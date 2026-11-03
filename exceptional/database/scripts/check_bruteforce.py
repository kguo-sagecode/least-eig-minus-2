"""Exact brute-force check for small n, with no floating point: run over all connected graphs on
n vertices (nauty geng -c), decide exactly whether M = 2I+A is positive semidefinite, and find its
rank, by symmetric fraction-free (Bareiss) elimination with diagonal pivoting in int64; keep those
with rank at most 8, canonically label them (labelg) and compare with the level file.

The entries after each step are minors of the permuted matrix (Bareiss), so every division is
exact (asserted), and for n <= 10 they are at most 13^(n/2) < 4e5 in absolute value (Hadamard),
far inside int64.  After k positive pivots the trailing block is a positive multiple of the Schur
complement, so M is positive semidefinite if and only if, at the first step where no diagonal
entry of the trailing block is positive, the whole trailing block is zero; the rank is then the
number of pivots.

Exact elimination avoids preselection by a floating-point least eigenvalue (LAPACK),
which would require a bound on numerical error. It also avoids relying on a search for an
e8common.certificate witness, which could miss a represented graph. For n <= 10 the exact
check and the floating-point/certificate check agree with the levels.

Usage: python check_bruteforce.py n LEVELFILE NWORKERS
"""
import sys, subprocess
import numpy as np
from multiprocessing import Pool

CHUNK = 50000   # graphs per batch; the int64 arrays of a batch take about 40 MB at n = 10


def decode_batch(lines, n):
    """graph6 strings of graphs on n >= 2 vertices -> adjacency matrices (b, n, n), int64."""
    m = n * (n - 1) // 2
    width = 1 + (m + 5) // 6
    arr = np.frombuffer(b"".join(lines), dtype=np.uint8).reshape(len(lines), width)
    assert (arr[:, 0] == n + 63).all()
    data = arr[:, 1:] - 63
    bits = np.unpackbits(data[:, :, None], axis=2)[:, :, 2:].reshape(len(lines), -1)[:, :m]
    I = [i for j in range(1, n) for i in range(j)]      # graph6 order: x(0,1), x(0,2), x(1,2), ...
    J = [j for j in range(1, n) for i in range(j)]
    A = np.zeros((len(lines), n, n), dtype=np.int64)
    A[:, I, J] = bits
    A[:, J, I] = bits
    return A


def psd_rank(M):
    """For each symmetric integer matrix of the batch: (positive semidefinite?, rank or -1)."""
    M = M.copy()
    B, n, _ = M.shape
    psd = np.zeros(B, dtype=bool)
    rank = np.full(B, -1, dtype=np.int64)
    prev = np.ones(B, dtype=np.int64)
    act = np.arange(B)
    ar = np.arange(n)
    for k in range(n):
        Mk = M[act]
        d = Mk[:, ar[k:], ar[k:]]
        p = d.argmax(axis=1)
        dmax = d[np.arange(act.size), p]
        stop = dmax <= 0
        if stop.any():
            zero = ~Mk[stop][:, k:, k:].reshape(int(stop.sum()), -1).any(axis=1)
            psd[act[stop]] = zero
            rank[act[stop]] = np.where(zero, k, -1)
            act, Mk, p = act[~stop], Mk[~stop], p[~stop]
            if act.size == 0:
                return psd, rank
        rb = np.arange(act.size)
        q = k + p
        rk, rq = Mk[rb, k, :].copy(), Mk[rb, q, :].copy()
        Mk[rb, k, :], Mk[rb, q, :] = rq, rk
        ck, cq = Mk[rb, :, k].copy(), Mk[rb, :, q].copy()
        Mk[rb, :, k], Mk[rb, :, q] = cq, ck
        piv = Mk[rb, k, k]
        assert np.abs(Mk[:, k:, k:]).max() < 2 ** 31, "entries too large for int64 products"
        c = Mk[:, k + 1:, k]
        T = piv[:, None, None] * Mk[:, k + 1:, k + 1:] - c[:, :, None] * c[:, None, :]
        pv = prev[act][:, None, None]
        assert not (T % pv).any(), "inexact division"
        Mk[:, k + 1:, k + 1:] = T // pv
        prev[act] = piv
        M[act] = Mk
    psd[act] = True
    rank[act] = n
    return psd, rank


def batches(n, res, mod):
    """The graph6 lines of part res/mod of geng's connected graphs on n vertices, in batches of
    CHUNK, read from its output as it runs rather than held in memory at once."""
    p = subprocess.Popen(["geng", "-cq", str(n), f"{res}/{mod}"], stdout=subprocess.PIPE)
    batch = []
    for line in p.stdout:
        line = line.strip()
        if line:
            batch.append(line)
        if len(batch) == CHUNK:
            yield batch
            batch = []
    if batch:
        yield batch
    p.stdout.close()
    if p.wait():
        raise RuntimeError(f"geng failed on part {res}/{mod}")


def job(args):
    n, res, mod = args
    total = npsd = nkeep = 0
    keep = []
    for chunk in batches(n, res, mod):
        A = decode_batch(chunk, n)
        M = 2 * np.eye(n, dtype=np.int64)[None, :, :] + A
        psd, rank = psd_rank(M)
        ok = psd & (rank <= 8)
        total += len(chunk)
        npsd += int(psd.sum())
        nkeep += int(ok.sum())
        keep.extend(s for s, o in zip(chunk, ok) if o)
    canon = []
    if keep:
        q = subprocess.run(["labelg", "-q"], input=b"\n".join(keep) + b"\n", capture_output=True,
                           check=True)
        canon = q.stdout.split()
        assert len(canon) == len(keep)
    return total, npsd, nkeep, canon


if __name__ == "__main__":
    n, level, nw = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
    ours = set(l.strip() for l in open(level, "rb") if l.strip())
    if n == 1:
        got, total, npsd, nkeep = {b"@"}, 1, 1, 1     # K_1: M = (2)
    else:
        mod = 4 * nw
        got, total, npsd, nkeep = set(), 0, 0, 0
        with Pool(nw) as pool:
            for t, s, k, c in pool.imap_unordered(job, [(n, i, mod) for i in range(mod)]):
                total += t; npsd += s; nkeep += k
                got.update(c)
    print(f"n={n}: connected {total}, 2I+A psd {npsd}, psd of rank <= 8 {nkeep} "
          f"({len(got)} classes), level {len(ours)}, equal: {got == ours}")
    sys.exit(0 if got == ours else 1)
