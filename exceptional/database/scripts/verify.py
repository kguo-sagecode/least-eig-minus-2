"""Independent verification of the database files.

For every graph X in exceptional/database/{minus2,above-minus2}/nNN.g6[.gz] (or the two parts
nNN.edges_le_M.g6.gz, nNN.edges_ge_{M+1}.g6.gz of a list split by number of edges) we check:
 1. every file is sorted (C byte order) and without repetitions (the parts of a split list hold
    graphs with numbers of edges in their ranges, and their merge is the list), each line is a graph6 string
    on NN vertices, and it is its own canonical form (nauty labelg);
 2. X is connected;
 3. 2I+A is positive semidefinite of rank r <= 8, exactly (certificate of e8common):
    r < NN for minus2 (least eigenvalue -2), r = NN for above-minus2 (least eigenvalue > -2);
 4. the Z-span of a representation is E6, E7 or E8: the product of the nonzero elementary
    divisors of 2I+A (PARI matsnf) is 9-r, AND, independently, the lattice has 72, 126 or 240
    vectors of norm 2 (PARI qflllgram image basis, then qfminim).
Usage: python verify.py DBDIR NWORKERS [n ...]   (default: every n present in counts.json)
"""
import sys, os, gzip, json, subprocess
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e8common import g6_decode, adjacency, certificate, read_list

ROOTS = {6: 72, 7: 126, 8: 240}


def connected(A):
    n = len(A)
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in np.nonzero(A[v])[0]:
            w = int(w)
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == n


_PARI = None


def get_pari():
    """One PARI instance per worker process, with a fixed stack (size = sizemax), so that PARI
    never reallocates its stack under live objects. A first version created a new instance for
    every chunk and built each matrix with pari.matrix, and leaked about 3 GB per worker on the
    large files; under the job's memory limit it crashed inside qfminim. The matrices are now
    built from strings (see check_graph), which does not leak, so the workers are no longer
    recycled (maxtasksperchild): each is forked once, before any list is read."""
    global _PARI
    if _PARI is None:
        import cypari2
        _PARI = cypari2.Pari(size=2 ** 28, sizemax=2 ** 28)
    return _PARI


def check_graph(pari, s, n, kind):
    """The checks of one graph. They are in a function of their own so that its PARI objects are
    freed when it returns: cypari2 keeps every object on the PARI stack alive while a newer one
    is, so in a loop over a chunk they would all stay until the end of the chunk."""
    m, bits = g6_decode(s)
    assert m == n, s
    A = adjacency(n, bits)
    assert connected(A), s
    M = 2 * np.eye(n, dtype=np.int64) + A
    B, D, adj = certificate(M)
    r = len(B)
    assert r <= 8, s
    assert (r < n) if kind == "minus2" else (r == n), s
    # Built from a string: pari.matrix clones every nonzero entry onto the PARI heap and
    # never frees the clones (cypari2 2.2.4), about 20 KB per graph at n = 20.
    P = pari("[" + ";".join(",".join(map(str, row)) for row in M.tolist()) + "]")
    assert P.type() == "t_MAT" and P.nrows() == n and P.ncols() == n, s
    det = 1
    for x in pari.matsnf(P):
        if int(x):
            det *= int(x)
    assert r in ROOTS and det == 9 - r, (s, r, det)
    K, T = pari.qflllgram(P, 4)
    G = T.mattranspose() * P * T
    assert int(pari.matdet(G)) == det, s
    nroots = int(pari.qfminim(G, 2, 0)[0])
    assert nroots == ROOTS[r], (s, r, nroots)


def check_chunk(args):
    lines, n, kind = args
    pari = get_pari()
    for s in lines:
        check_graph(pari, s, n, kind)
    return len(lines)


def chunks(L, n, kind, size=2000):
    """The tasks for one list, made one at a time as the pool takes them."""
    for i in range(0, len(L), size):
        yield L[i:i + size], n, kind


def main():
    db, nw = sys.argv[1], int(sys.argv[2])
    with open(os.path.join(db, "counts.json")) as f:
        C = json.load(f)
    ns = [int(x) for x in sys.argv[3:]] or [int(k) for k in C["per_n"]]
    with Pool(nw) as pool:
        for n in ns:
            for kind, key in (("minus2", "minus2"), ("above-minus2", "above_minus2")):
                # sorted and without repetitions: checked by read_list, file by file and merged
                L = read_list(db, kind, n, check=True)
                assert len(L) == C["per_n"][str(n)][key], (n, kind)
                if not L:
                    continue
                out = subprocess.run(["labelg", "-q"], input=b"\n".join(L + [b""]),
                                     capture_output=True, check=True).stdout
                q = out.split()
                del out
                assert q == L, (n, kind, "not canonical")
                del q
                tot = sum(pool.imap_unordered(check_chunk, chunks(L, n, kind)))
                del L
                print(f"n={n} {kind}: {tot} graphs verified", flush=True)
    print("all checks passed")


if __name__ == "__main__":
    main()
