"""Common routines for the enumeration of the connected graphs represented in E8.

All tests are exact integer arithmetic.  Floating point is used only to *propose*
a basis; the proposal is then verified exactly (see `certificate`).
"""
import numpy as np
from scipy.linalg.lapack import dpstrf
from itertools import product

_tri_cache = {}


def tri_index(n):
    """Row and column indices of the graph6 bit order: for j=1..n-1, for i=0..j-1."""
    if n not in _tri_cache:
        I, J = [], []
        for j in range(1, n):
            for i in range(j):
                I.append(i)
                J.append(j)
        _tri_cache[n] = (np.array(I, dtype=np.int64), np.array(J, dtype=np.int64))
    return _tri_cache[n]


def g6_decode(s):
    """graph6 string (n <= 62) -> (n, bit vector of the upper triangle in graph6 order)."""
    b = s.encode() if isinstance(s, str) else s
    n = b[0] - 63
    m = n * (n - 1) // 2
    data = np.frombuffer(b[1:], dtype=np.uint8) - 63
    bits = np.unpackbits(data[:, None], axis=1)[:, 2:].reshape(-1)[:m]
    return n, bits


def adjacency(n, bits):
    A = np.zeros((n, n), dtype=np.int64)
    I, J = tri_index(n)
    A[I, J] = bits
    A[J, I] = bits
    return A


def g6_encode_rows(n, bitrows):
    """Encode many graphs on n vertices at once; bitrows is K x n(n-1)/2 (0/1)."""
    K, m = bitrows.shape
    pad = (-m) % 6
    if pad:
        bitrows = np.concatenate([bitrows, np.zeros((K, pad), dtype=bitrows.dtype)], axis=1)
    groups = bitrows.reshape(K, -1, 6).astype(np.uint8)
    w = np.array([32, 16, 8, 4, 2, 1], dtype=np.uint8)
    vals = (groups * w).sum(axis=2).astype(np.uint8) + 63
    head = chr(n + 63)
    return [head + r.tobytes().decode() for r in vals]


def bareiss_det_minors(G):
    """Exact leading principal minors of an integer matrix (fraction-free elimination).
    Returns the list [d_1, ..., d_k]; stops (returns what it has, with a 0) at a zero pivot."""
    M = [list(map(int, row)) for row in G]
    k = len(M)
    minors = []
    prev = 1
    for p in range(k):
        if M[p][p] == 0:
            minors.append(0)
            return minors
        minors.append(M[p][p])
        for i in range(p + 1, k):
            for j in range(p + 1, k):
                M[i][j] = (M[i][j] * M[p][p] - M[i][p] * M[p][j]) // prev
        prev = M[p][p]
    return minors


def adjugate_exact(G, D):
    """Exact adjugate of the nonsingular integer matrix G with determinant D > 0.
    Floating point only proposes: T = rint(D * inv(G)). The proposal is accepted when its entries
    are finite and at most 2^(k-1) in absolute value, the bound on the entries of adj(G) for a
    positive definite G with diagonal entries 2 (Hadamard's inequality), and G @ T == D * I in
    64-bit integers, which cannot overflow under that bound; then T = adj(G), since G is
    nonsingular. Otherwise adj(G) is computed exactly over the rationals (Gauss-Jordan)."""
    k = len(G)
    T = np.rint(np.linalg.inv(G.astype(float)) * D)
    if np.all(np.isfinite(T)) and np.all(np.abs(T) <= 2 ** (k - 1)):
        adj = T.astype(np.int64)
        if np.array_equal(G @ adj, D * np.eye(k, dtype=np.int64)):
            return adj
    from fractions import Fraction
    a = [[Fraction(int(G[i][j])) for j in range(k)] + [Fraction(int(i == j)) for j in range(k)]
         for i in range(k)]
    for c in range(k):
        p = next(r for r in range(c, k) if a[r][c] != 0)
        a[c], a[p] = a[p], a[c]
        pv = a[c][c]
        a[c] = [x / pv for x in a[c]]
        for r in range(k):
            if r != c and a[r][c] != 0:
                f = a[r][c]
                a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    adj = np.array([[int(a[i][k + j] * D) for j in range(k)] for i in range(k)], dtype=np.int64)
    assert np.array_equal(G @ adj, D * np.eye(k, dtype=np.int64))
    return adj


def certificate(M):
    """For M = 2I + A (integer, symmetric), find a set B of vertices with
       (i)  G = M[B,B] positive definite (all leading principal minors > 0, exact), and
       (ii) D*M == M[:,B] @ adj(G) @ M[B,:]  (exact), D = det G.
    Then M = M[:,B] G^{-1} M[B,:] is positive semidefinite of rank |B|.
    Returns (B, D, adj) or None if M is not positive semidefinite."""
    n = len(M)
    # propose a basis with LAPACK's pivoted Cholesky factorization (dpstrf); the proposal
    # is only a proposal: everything below is checked exactly, and on failure we fall back
    # to a greedy proposal.
    c, piv, rank, info = dpstrf(M.astype(float), tol=1e-8)
    B = sorted(int(p) - 1 for p in piv[:rank])
    try:
        return _check(M, B)
    except RuntimeError:
        pass
    B = []
    L = np.zeros((n, n))
    for v in range(n):
        if B:
            k = len(B)
            x = np.linalg.solve(L[:k, :k], M[B, v].astype(float))
            res = M[v, v] - x @ x
        else:
            x = np.zeros(0)
            res = float(M[v, v])
        if res < -1e-6:
            return None
        if res > 1e-6:
            k = len(B)
            L[k, :k] = x
            L[k, k] = np.sqrt(res)
            B.append(v)
    return _check(M, B)


def _check(M, B):
    G = M[np.ix_(B, B)]
    minors = bareiss_det_minors(G)
    if any(d <= 0 for d in minors):
        raise RuntimeError("basis proposal failed exact check")
    D = minors[-1]
    adj = adjugate_exact(G, D)
    MB = M[B, :]
    if not np.array_equal(D * M, MB.T @ adj @ MB):
        raise RuntimeError("basis proposal failed exact span check")
    return B, D, adj


_S_cache = {}


def nonzero01(r):
    if r not in _S_cache:
        S = np.array([s for s in product((0, 1), repeat=r) if any(s)], dtype=np.int64)
        _S_cache[r] = S
    return _S_cache[r]


def lattice_det_from_basis(C, D):
    """det of the Z-span L of a representation, from a certificate: in the coordinates of the
    basis B, L_B = Z^r and L = Z^r + sum_u Z (C[:,u]/D), where C = adj(G) M[B,:].
    So L/L_B is the subgroup of (Z/D)^r generated by the columns of C mod D, and
    det L = D / |L/L_B|^2 (exact)."""
    R = C % D
    nz = R.any(axis=0)
    if not nz.any():
        return D
    r = C.shape[0]
    gens = [tuple(int(x) for x in col) for col in set(map(tuple, R[:, nz].T.tolist()))]
    group = {tuple([0] * r)}
    changed = True
    while changed:
        changed = False
        for g in gens:
            new = {tuple((x + y) % D for x, y in zip(e, g)) for e in group}
            if not new <= group:
                group |= new
                changed = True
    idx = len(group)
    assert D % (idx * idx) == 0
    return D // (idx * idx)


# ----------------------------------------------------------------------------------------------
# Reading the lists. A list is one file nNN.g6 or nNN.g6.gz, or, when that would be over 100 MB
# gzipped, two parts split by number of edges (scripts/split_by_edges.py):
# nNN.edges_le_M.g6.gz (at most M edges) and nNN.edges_ge_{M+1}.g6.gz (at least M+1 edges).

import glob as _glob
import gzip as _gzip
import heapq as _heapq
import os as _os
import re as _re

_POP = bytes(bin(max(b - 63, 0)).count("1") for b in range(256))


def g6_edges(s):
    """The number of edges of a graph6 string (bytes) on at most 62 vertices: the number of 1 bits
    in its data bytes, each carrying 6 bits of the upper triangle offset by 63 (padding bits are 0)."""
    return sum(s[1:].translate(_POP))


def list_files(db, kind, n):
    """The files holding the list `kind` (minus2, above-minus2 or maximal) on n vertices, as a list
    of (path, lo, hi), where every graph in the file has between lo and hi edges (None: no bound).
    An absent list gives []."""
    base = _os.path.join(db, kind, "n%02d" % n)
    whole = [p for p in (base + ".g6", base + ".g6.gz") if _os.path.exists(p)]
    parts = sorted(_glob.glob(base + ".edges_*.g6.gz"))
    assert len(whole) <= 1 and not (whole and parts), ("ambiguous list files", base)
    if whole:
        return [(whole[0], None, None)]
    if not parts:
        return []
    le = [p for p in parts if _re.search(r"\.edges_le_\d+\.g6\.gz$", p)]
    ge = [p for p in parts if _re.search(r"\.edges_ge_\d+\.g6\.gz$", p)]
    assert len(parts) == 2 and len(le) == 1 and len(ge) == 1, ("unexpected parts", parts)
    m = int(_re.search(r"\.edges_le_(\d+)\.", le[0]).group(1))
    m1 = int(_re.search(r"\.edges_ge_(\d+)\.", ge[0]).group(1))
    assert m1 == m + 1, ("the parts' edge ranges do not meet", parts)
    return [(le[0], None, m), (ge[0], m + 1, None)]


def _file_strings(path, lo, hi, check):
    """The graph6 strings (bytes) of one list file, in its order, read as a stream. With check, they
    must be strictly increasing (sorted and without repetitions) and have between lo and hi edges
    (None: no bound)."""
    prev = None
    with (_gzip.open(path, "rb") if path.endswith(".gz") else open(path, "rb")) as f:
        for line in f:
            for s in line.split():
                if check:
                    assert prev is None or prev < s, (path, "not sorted and unique")
                    if lo is not None or hi is not None:
                        e = g6_edges(s)
                        assert (lo is None or e >= lo) and (hi is None or e <= hi), (path, s, e)
                prev = s
                yield s


def iter_list(db, kind, n, check=False):
    """The graph6 strings (bytes) of the list `kind` on n vertices, one at a time, in C byte order;
    the files are read as a stream, and the two parts of a split list are merged. With check, each
    file must be sorted and without repetitions, the graphs of each part must have their numbers of
    edges in the part's range, and the merged list must be sorted and without repetitions; a failed
    check raises AssertionError when the iteration reaches it."""
    runs = [_file_strings(path, lo, hi, check) for path, lo, hi in list_files(db, kind, n)]
    prev = None
    for s in runs[0] if len(runs) == 1 else _heapq.merge(*runs):
        if check:
            assert prev is None or prev < s, (db, kind, n, "the merged list is not sorted and unique")
            prev = s
        yield s


def read_list(db, kind, n, check=False):
    """All graph6 strings (bytes) of the list `kind` on n vertices, in C byte order, as a list (see
    iter_list, which reads the files as a stream, so that the list is the only copy in memory)."""
    return list(iter_list(db, kind, n, check))
