"""One level of the growth: from the connected graphs on n vertices represented in E8
(file of canonical graph6 strings) to all their one-vertex extensions represented in E8.

Usage: python grow.py LEVELFILE OUTDIR NWORKERS
Writes OUTDIR/children.NNN (canonical, sorted, unique per chunk) and OUTDIR/info.NNN,
one line per input graph: g6 rank latticedet nvalidextensions, where rank = rank(2I+A)
and latticedet = det of the Z-span of a representation (only computed when rank >= 6, else 0).

Environment (optional): LABELG, the labelg program (default labelg); SORTMEM, the memory budget
of all the sorts of the step together (default 6G), a number with an optional suffix K, M, G or T
(powers of 1024; K if there is none, as for sort -S). Each worker's sort runs single-threaded
with a share SORTMEM/NWORKERS, and beyond it spills to files in OUTDIR (the output is the same).
"""
import sys, os, re, shlex, subprocess
from itertools import islice
import numpy as np
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e8common import g6_decode, adjacency, certificate, nonzero01, g6_encode_rows, lattice_det_from_basis

LABELG = os.environ.get("LABELG", "labelg")
SORTMEM = os.environ.get("SORTMEM", "6G")

EXC = {(6, 3), (7, 2), (8, 1)}


def kib(size):
    """A size in the syntax of sort -S without %, in KiB."""
    m = re.fullmatch(r"(\d+)([KMGT]?)", size.strip().upper())
    assert m, ("SORTMEM is not a size such as 6G", size)
    return int(m.group(1)) << (10 * "KMGT".index(m.group(2) or "K"))


def extensions(s):
    n, bits = g6_decode(s)
    A = adjacency(n, bits)
    M = 2 * np.eye(n, dtype=np.int64) + A
    B, D, adj = certificate(M)
    r = len(B)
    C = adj @ M[B, :]
    S = nonzero01(r)
    P = S @ C
    ok = np.all((P == 0) | (P == D), axis=1)
    q = ((S @ adj) * S).sum(axis=1)
    if r == 8:
        ok &= (q == 2 * D)
    else:
        ok &= (q <= 2 * D)
    nb = (P[ok] == D).astype(np.uint8)
    det = lattice_det_from_basis(C, D) if r >= 6 else 0
    return n, bits, M, r, nb, det


def work(args):
    infile, start, lo, hi, outdir, idx, sortmem = args
    tmp = os.path.join(outdir, f"tmp{idx}")
    os.makedirs(tmp, exist_ok=True)
    out = os.path.join(outdir, f"children.{idx:03d}")
    # bash with pipefail: the exit status is nonzero if labelg fails as well as sort, so a
    # labelg failure after its input is closed cannot pass for a complete (truncated) child set.
    # GNU sort uses up to 8 threads by default, and then reserves more memory per line (about 125
    # bytes besides the text, against 48 with one thread); one thread is enough here.
    p = subprocess.Popen(["bash", "-o", "pipefail", "-c",
                          f"{LABELG} -q | LC_ALL=C sort --parallel=1 -u -S {sortmem} "
                          f"-T {shlex.quote(tmp)} > {shlex.quote(out)}"],
                         stdin=subprocess.PIPE)
    with open(os.path.join(outdir, f"info.{idx:03d}"), "w") as info, open(infile, "rb") as f:
        f.seek(start)                       # the first byte of line lo
        for line in islice(f, hi - lo):     # lines lo, ..., hi - 1
            s = line.strip().decode()
            n, bits, M, r, nb, det = extensions(s)
            if r >= 6:
                allowed = {r + 1, 4, 9 - r}
                assert det in allowed, (s, r, det)
            if len(nb):
                rows = np.concatenate([np.tile(bits, (len(nb), 1)), nb], axis=1)
                p.stdin.write(("\n".join(g6_encode_rows(n + 1, rows)) + "\n").encode())
            info.write(f"{s} {r} {det} {len(nb)}\n")
    p.stdin.close()
    p.wait()
    assert p.returncode == 0
    return idx


if __name__ == "__main__":
    infile, outdir, nw = sys.argv[1], sys.argv[2], int(sys.argv[3])
    os.makedirs(outdir, exist_ok=True)
    with open(infile, "rb") as f:
        N = sum(1 for _ in f)
    nchunks = min(max(1, N // 200), 4 * nw) if N > 0 else 1
    bounds = [N * k // nchunks for k in range(nchunks + 1)]
    # the byte offset of the first line of each chunk, so that a worker seeks to its chunk
    # instead of reading the file from the start
    starts = []
    with open(infile, "rb") as f:
        for k in range(nchunks):
            starts.append(f.tell())
            for _ in islice(f, bounds[k + 1] - bounds[k]):
                pass
    sortmem = f"{max(1, kib(SORTMEM) // nw)}K"
    jobs = [(infile, starts[k], bounds[k], bounds[k + 1], outdir, k, sortmem) for k in range(nchunks)]
    # ProcessPoolExecutor (unlike multiprocessing.Pool) raises if a worker dies abruptly,
    # so a crashed worker makes the step fail instead of silently losing graphs.
    with ProcessPoolExecutor(nw) as ex:
        done = sorted(ex.map(work, jobs))
    assert done == list(range(nchunks))
