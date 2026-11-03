"""Exact Sage helpers. No imports or data loads from the project's scratch checks.

All root coordinates are row vectors. Lists use explicit structured Lean labels;
no assertion is made about Lean's internal Fintype enumeration order.
"""
from sage.all import *
from itertools import combinations, product
from collections import Counter
from pathlib import Path
import json
import time
import sage.version

HERE = Path(__file__).resolve().parent
CERT = HERE / "data"


def plain(x):
    if isinstance(x, dict):
        return {str(k): plain(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [plain(v) for v in x]
    if isinstance(x, (str, bool)) or x is None:
        return x
    if x in QQ:
        q = QQ(x)
        return int(q) if q.denominator() == 1 else {"num": int(q.numerator()), "den": int(q.denominator())}
    raise TypeError("Not an exact JSON value: %r" % (x,))


def rows(M):
    return [list(r) for r in M.rows()]


def save(name, computations, **data):
    CERT.mkdir(exist_ok=True)
    obj = dict(schema="linegraphs-sage-v1", computations=computations,
               sage_version=sage.version.version, **data)
    target = CERT / (name + ".json")
    target.write_text(json.dumps(plain(obj), indent=2, sort_keys=True) + "\n")
    print("certificate:", target.relative_to(HERE))


def begin(label):
    set_random_seed(0)
    print("SageMath", sage.version.version, "|", label, flush=True)


def unit(n, i):
    return vector(ZZ, [int(j == i) for j in range(n)])


def matrix_graph(M, value=1):
    G = Graph(M.nrows())
    G.add_edges((i, j) for i, j in combinations(range(M.nrows()), 2) if M[i, j] == value)
    return G


def adjacency(G):
    assert G.vertices(sort=True) == list(range(G.order()))
    return G.adjacency_matrix(vertices=list(range(G.order()))).change_ring(ZZ)


def integer_graph(G):
    return G.relabel({v: i for i, v in enumerate(G.vertices(sort=True))}, inplace=False)


def graph_data(G):
    return dict(order=G.order(), edges=[list(e) for e in G.edges(sort=True, labels=False)],
                adjacency=rows(adjacency(G)))


def root_graph(V, q=1):
    M = matrix(QQ, V)
    gram = M * M.transpose() / q
    assert set(gram.diagonal()) == {2}
    assert all(gram[i, j] in (0, 1) for i, j in combinations(range(len(V)), 2))
    return matrix_graph(gram)


def iso(G, H):
    ok, p = G.is_isomorphic(H, certificate=True)
    assert ok
    perm = [p[i] for i in range(G.order())]
    assert sorted(perm) == list(range(H.order()))
    A, B = adjacency(G), adjacency(H)
    assert all(A[i, j] == B[perm[i], perm[j]] for i in range(G.order()) for j in range(G.order()))
    return perm


def switching(G, subset):
    # Sage's own Seidel switching, followed by an exact sign identity.
    Y = set(subset)
    H = G.copy()
    H.seidel_switching(list(Y))
    n = G.order()
    D = diagonal_matrix(ZZ, [-1 if i in Y else 1 for i in range(n)])
    assert ones_matrix(ZZ, n) - identity_matrix(n) - 2 * adjacency(H) == D * (
        ones_matrix(ZZ, n) - identity_matrix(n) - 2 * adjacency(G)) * D
    return H


def switching_iso(G, H):
    """Find a switch and a permutation using the graphs with one isolated vertex."""
    n = G.order()
    X = switching(G, G.neighbors(0)).subgraph(range(1, n))
    for v in range(n):
        Y = switching(H, H.neighbors(v)).subgraph([w for w in range(n) if w != v])
        ok, p = X.is_isomorphic(Y, certificate=True)
        if not ok:
            continue
        p[0] = v
        A, B = adjacency(G), adjacency(H)
        signs = [1] + [int((1 - 2 * A[0, i]) * (1 - 2 * B[v, p[i]])) for i in range(1, n)]
        subset = [i for i in range(n) if signs[i] == -1]
        C = adjacency(switching(G, subset))
        assert all(C[i, j] == B[p[i], p[j]] for i in range(n) for j in range(n))
        return dict(subset=subset, signs=signs, permutation=[p[i] for i in range(n)])
    raise AssertionError("No switching isomorphism")


def spectral(M, spectrum):
    """Check charpoly independently; export small squarefree identity and traces."""
    M = matrix(ZZ, M)
    assert M == M.transpose()
    spectrum = sorted((ZZ(a), ZZ(m)) for a, m in spectrum if m)
    R = PolynomialRing(ZZ, "x")
    x = R.gen()
    cp = prod((x-a)**m for a, m in spectrum)
    assert M.charpoly("x") == cp
    annihilator = prod(x-a for a, m in spectrum)
    Z = zero_matrix(ZZ, M.nrows())
    I = identity_matrix(ZZ, M.nrows())
    for coefficient in reversed(annihilator.list()):
        Z = Z * M + coefficient * I
    assert Z.is_zero()
    traces = []
    power = I
    for j in range(len(spectrum)):
        traces.append(power.trace())
        assert traces[-1] == sum(m*a**j for a, m in spectrum)
        power *= M
    return dict(matrix=rows(M), eigenvalues=[a for a, m in spectrum],
                multiplicities=[m for a, m in spectrum],
                annihilator_coefficients=annihilator.list(), traces=traces,
                characteristic_polynomial_coefficients=cp.list())


def srg(G, expected=None):
    p = G.is_strongly_regular(parameters=True)
    assert p is not False
    if expected is not None:
        assert tuple(p) == tuple(expected), (p, expected)
    A = adjacency(G)
    n, k, a, c = p
    assert A*A == (k-c)*identity_matrix(n) + (a-c)*A + c*ones_matrix(n)
    return list(p)


def clique_count(G, k):
    # Explicit subsets keep the invariant suitable for a List/Bool Lean checker.
    nbr = {v: set(G.neighbors(v)) for v in G}
    return sum(all(v in nbr[u] for u, v in combinations(S, 2))
               for S in combinations(range(G.order()), k))


def local_clique_counts(G, k):
    counts = [0]*G.order()
    for S in combinations(range(G.order()), k):
        if all(G.has_edge(u,v) for u,v in combinations(S,2)):
            for v in S:
                counts[v] += 1
    assert sum(counts) == k*clique_count(G,k)
    return counts


def claws(G):
    result = []
    for v in G:
        for S in combinations(sorted(G.neighbors(v)), 3):
            if all(not G.has_edge(a, b) for a, b in combinations(S, 2)):
                result.append([v] + list(S))
    return result


def an(n):
    labels = [[i, j] for i in range(n+1) for j in range(n+1) if i != j]
    return labels, [unit(n+1, i)-unit(n+1, j) for i, j in labels]


def dn(n):
    labels = [[i, j, b, c] for i, j in combinations(range(n), 2) for b, c in product((0, 1), repeat=2)]
    return labels, [(-1)**b*unit(n, i)+(-1)**c*unit(n, j) for i, j, b, c in labels]


def e8d():
    dl, dv = dn(8)
    labels = [["D", p] for p in dl]
    V = [2*v for v in dv]
    for bits in product((0, 1), repeat=7):
        signs = [(-1)**b for b in bits]
        labels.append(["half", list(bits)])
        V.append(vector(ZZ, signs+[prod(signs)]))
    return labels, V


def exceptional(n):
    labels, V = e8d()
    use = [i for i, v in enumerate(V) if (n >= 7 or v[5] == v[6]) and (n >= 8 or v[6] == v[7])]
    return [labels[i] for i in use], [V[i] for i in use], use


def e8a():
    al, av = an(8)
    labels, V = [["A", p] for p in al], [3*v for v in av]
    for T in combinations(range(9), 3):
        for b in (0, 1):
            labels.append(["triple", list(T), b])
            V.append(vector(ZZ, [(-1)**b*(-2 if i in T else 1) for i in range(9)]))
    return labels, V


STEINER = [list(T) for T in combinations(range(8), 4) if
           int(T[0]) ^ int(T[1]) ^ int(T[2]) ^ int(T[3]) == 0]


def e8s():
    labels, V = [], []
    for i in range(8):
        for b in (0, 1):
            labels.append(["axis", i, b])
            V.append(2*(-1)**b*unit(8, i))
    for T in STEINER:
        for bits in product((0, 1), repeat=4):
            labels.append(["block", T, list(bits)])
            V.append(sum(((-1)**b*unit(8, i) for i, b in zip(T, bits)), vector(ZZ, 8)))
    return labels, V


def representatives(V):
    return [i for i, v in enumerate(V) if next(a for a in v if a) > 0]


def simple_roots(V):
    # A deterministic regular functional: base 10 prevents cancellation for our coordinates.
    h = vector(ZZ, [10**i for i in range(len(V[0]))])
    assert all(v*h != 0 for v in V)
    pos = [v for v in V if v*h > 0]
    lookup = {tuple(v) for v in pos}
    return [v for v in pos if not any(tuple(v-w) in lookup for w in pos)]


def ldl(M):
    M = matrix(QQ, M)
    n = M.nrows()
    L, d = identity_matrix(QQ, n), []
    for j in range(n):
        d.append(M[j, j] - sum(L[j, k]**2*d[k] for k in range(j)))
        assert d[-1] != 0
        for i in range(j+1, n):
            L[i, j] = (M[i, j]-sum(L[i, k]*L[j, k]*d[k] for k in range(j)))/d[j]
    assert M == L*diagonal_matrix(d)*L.transpose()
    return dict(matrix=rows(M), lower=rows(L), diagonal=d)


def flag_graph(v, blocks):
    flags = [[p, i] for i, B in enumerate(blocks) for p in sorted(B)]
    G = Graph(len(flags))
    G.add_edges((i, j) for i, j in combinations(range(len(flags)), 2)
                if flags[i][0] == flags[j][0] or flags[i][1] == flags[j][1])
    I = Graph(v+len(blocks))
    I.add_edges((p, v+i) for i, B in enumerate(blocks) for p in B)
    assert G.is_isomorphic(I.line_graph())
    return flags, G


def design_check(v, blocks, k, lam):
    from sage.combinat.designs.incidence_structures import IncidenceStructure
    assert all(len(B) == len(set(B)) == k for B in blocks)
    D = IncidenceStructure(v, blocks)
    assert D.is_t_design(2, v, k, lam)
    N = matrix(ZZ, v, len(blocks), lambda i, j: int(i in blocks[j]))
    r = len(blocks)*k//v
    assert N*N.transpose() == (r-lam)*identity_matrix(v) + lam*ones_matrix(v)
    return dict(parameters=[v, k, len(blocks), r, lam], blocks=blocks)


def design632():
    from sage.combinat.designs.bibd import balanced_incomplete_block_design
    D = balanced_incomplete_block_design(6, 3, 2)
    labels = {v:i for i,v in enumerate(sorted(D.ground_set()))}
    blocks = sorted(sorted(labels[v] for v in B) for B in D.blocks())
    design_check(6, blocks, 3, 2)
    return blocks


def chang_graphs():
    E = list(combinations(range(8), 2))
    T = Graph([E, lambda u, v: u != v and bool(set(u) & set(v))])
    T = T.relabel({e: i for i, e in enumerate(E)}, inplace=False)
    sets = [[(i, i+4) for i in range(4)],
            [(i, (i+1) % 8) for i in range(8)],
            [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (5, 6), (6, 7), (3, 7)]]
    ids = [[E.index(tuple(sorted(e))) for e in S] for S in sets]
    return E, T, [switching(T, S) for S in ids], ids
