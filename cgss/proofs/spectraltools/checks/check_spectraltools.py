#!/usr/bin/env python3
"""Exact small certificates and independent numerical sanity checks.

Run with python3; requires NumPy and SymPy. These checks are not Lean
proofs. All certificate arithmetic is integer arithmetic; numpy is used
only for independent comparisons of eigenvalues and Rayleigh bounds.
"""
from itertools import combinations
from pathlib import Path
import json

import numpy as np
import sympy as sp


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def mul(a, b):
    cols = transpose(b)
    return [[sum(x * y for x, y in zip(row, col)) for col in cols] for row in a]


def shift(a, b):
    return [[x + b * int(i == j) for j, x in enumerate(row)] for i, row in enumerate(a)]


def tr(a):
    return sum(a[i][i] for i in range(len(a)))


def moments(a, count):
    p = eye(len(a))
    out = []
    for _ in range(count):
        out.append(tr(p))
        p = mul(p, a)
    return out


def spectral_check(a, nodes, counts):
    n = len(a)
    if any(len(row) != n for row in a):
        return False
    if any(type(x) is not int for row in a for x in row):
        return False
    if a != transpose(a):
        return False
    if any(type(t) is not int for t in nodes):
        return False
    if len(set(nodes)) != len(nodes) or len(nodes) != len(counts):
        return False
    if any(type(m) is not int or m < 0 for m in counts):
        return False
    p = eye(n)
    for theta in nodes:
        p = mul(p, shift(a, -theta))
    if any(any(row) for row in p):
        return False
    return moments(a, len(nodes)) == [
        sum(m * theta**j for theta, m in zip(nodes, counts))
        for j in range(len(nodes))
    ]


def positive_check(a, x, b):
    n = len(a)
    return (
        n > 0
        and len(x) == n
        and all(len(row) == n for row in a)
        and all(type(t) is int for row in a for t in row)
        and all(type(t) is int for t in x)
        and type(b) is int
        and a == transpose(a)
        and all(t >= 0 for row in a for t in row)
        and all(t > 0 for t in x)
        and all(sum(a[i][j] * x[j] for j in range(n)) == b * x[i] for i in range(n))
    )


def adjacency(n, edges):
    a = [[0] * n for _ in range(n)]
    for i, j in edges:
        assert i != j
        a[i][j] = a[j][i] = 1
    return a


def edge_list(a):
    return [(i, j) for i, j in combinations(range(len(a)), 2) if a[i][j]]


def line_graph(a):
    e = [set(pair) for pair in edge_list(a)]
    return adjacency(len(e), [(i, j) for i, j in combinations(range(len(e)), 2) if e[i] & e[j]])


def eig(a):
    return np.linalg.eigvalsh(np.array(a, dtype=float))


def assert_spectrum(a, nodes, counts):
    assert spectral_check(a, nodes, counts)
    want = sorted(t for t, m in zip(nodes, counts) for _ in range(m))
    assert np.allclose(eig(a), want, atol=1e-10, rtol=0)


def cycle(n):
    return adjacency(n, [(i, (i + 1) % n) for i in range(n)])


def arm_tree(lengths, center_value):
    edges, weights = [], [center_value]
    for h in lengths:
        prev = 0
        for j in range(1, h + 1):
            u = len(weights)
            edges.append((prev, u))
            assert center_value * (h + 1 - j) % (h + 1) == 0
            weights.append(center_value * (h + 1 - j) // (h + 1))
            prev = u
    return adjacency(len(weights), edges), weights


def smith_d(ell):
    if ell == 4:
        return adjacency(5, [(0, i) for i in range(1, 5)]), [2, 1, 1, 1, 1]
    h = ell - 4
    edges = [(i, i + 1) for i in range(h)]
    weights = [2] * (h + 1)
    for endpoint in [0, h]:
        for _ in range(2):
            edges.append((endpoint, len(weights)))
            weights.append(1)
    return adjacency(len(weights), edges), weights


def c13_matrices():
    def vec(*terms):
        x = [0] * 8
        for i, value in terms:
            x[i - 1] = value
        return x

    perm = [1, 2, 3, 0, 7, 4, 5, 6]  # (1 2 3 4)(8 7 6 5)

    def rotate(x):
        y = [0] * 8
        for i, value in enumerate(x):
            y[perm[i]] = value
        return y

    out = []
    for third in [vec((1, 1), (2, 1), (5, -1), (6, 1)), vec((1, 1), (2, 1), (7, 1), (8, -1))]:
        rows = []
        for seed in [vec((1, 2)), vec((1, 1), (2, 1), (5, 1), (6, -1)), third]:
            x = seed
            for _ in range(4):
                rows.append(x)
                x = rotate(x)
        assert len({tuple(row) for row in rows}) == 12
        h = mul(rows, transpose(rows))
        assert all(h[i][i] == 4 for i in range(12))
        assert all(h[i][j] in (0, 2) for i, j in combinations(range(12), 2))
        a = [[0 if i == j else h[i][j] // 2 for j in range(12)] for i in range(12)]
        out.append(a)
    return out


def main():
    report = {"arithmetic": "Integer certificate operations; numpy only for independent spectral checks"}

    a = [[2, 1, 0], [1, 2, 0], [0, 0, 3]]
    assert_spectrum(a, [3, 1], [2, 1])
    assert 3 - (sp.Matrix(a) - 3 * sp.eye(3)).rank() == 2
    assert spectral_check([], [0], [0])
    assert not spectral_check(a, [3, 1], [1, 2])
    assert not spectral_check(a, [3, 3], [2, 1])
    assert not spectral_check([[0, 1], [0, 0]], [0], [2])
    assert not spectral_check([[0, 1]], [0], [1])
    assert not spectral_check([[0.0]], [0], [1])
    assert not spectral_check([[0]], [0.0], [1])
    assert not spectral_check([[0]], [0], [1.0])
    assert not positive_check([[0]], [0], 0)
    assert positive_check([[0]], [1], 0)
    assert not positive_check([], [], 0)
    bad_bound = sp.diag(-3, -2)
    assert (2 * sp.eye(2) + bad_bound).det() == 0
    assert not (2 * sp.eye(2) + bad_bound).is_positive_semidefinite
    report["basic"] = "Repeated multiplicity, empty spectrum, malformed/rejected certificates, and determinant versus least-bound distinction passed"

    c13 = []
    for a in c13_matrices():
        assert_spectrum(a, [4, 2, 0, -2], [1, 3, 3, 5])
        s = [[1 - int(i == j) - 2 * a[i][j] for j in range(12)] for i in range(12)]
        assert_spectrum(s, [-5, -1, 3], [3, 3, 6])
        assert_spectrum([[-x for x in row] for row in s], [5, 1, -3], [3, 3, 6])
        assert moments(s, 4)[3] == -216
        c13.append({"adjacency_moments": moments(a, 4), "Seidel_moments": moments(s, 3), "rank_2I_plus_A": int(sp.Matrix(shift(a, 2)).rank())})
    report["C13"] = c13

    pairs = list(combinations(range(5), 2))
    petersen = adjacency(10, [(i, j) for i, j in combinations(range(10), 2) if set(pairs[i]).isdisjoint(pairs[j])])
    mate = line_graph(line_graph(petersen))
    blocks = [{5, i, (i + 1) % 5} for i in range(5)] + [{i, (i + 2) % 5, (i + 3) % 5} for i in range(5)]
    assert all(sum({i, j} <= b for b in blocks) == 2 for i, j in combinations(range(6), 2))
    incidence_graph = adjacency(16, [(i, 6 + j) for i in range(6) for j, b in enumerate(blocks) if i in b])
    flag = line_graph(incidence_graph)
    for a in [mate, flag]:
        assert_spectrum(a, [6, 4, 1, 0, -2], [1, 5, 4, 5, 15])
        assert moments(a, 5) == [30, 0, 180, 420, 2820]
    report["C15"] = {"orders": [len(flag), len(mate)], "moments": moments(flag, 5), "nodes": [6, 4, 1, 0, -2], "multiplicities": [1, 5, 4, 5, 15]}
    design_b = sp.Matrix([[int(i in block) for block in blocks] for i in range(6)])
    assert design_b * design_b.T == 3 * sp.eye(6) + 2 * sp.ones(6)
    assert (design_b * design_b.T).det() == 15 * 3**5

    for p, q in [(1, 1), (1, 4), (2, 3), (3, 3)]:
        complete_bip = adjacency(p + q, [(i, p + j) for i in range(p) for j in range(q)])
        counts = {}
        for node, count in [(p + q - 2, 1), (p - 2, q - 1),
                            (q - 2, p - 1), (-2, (p - 1) * (q - 1))]:
            counts[node] = counts.get(node, 0) + count
        assert_spectrum(line_graph(complete_bip), list(counts), list(counts.values()))
    report['design_checks'] = 'Design Gram determinant and complete-bipartite line spectra, including collisions and singleton parts, passed'

    smiths = [(f"cycle_{n}", cycle(n), [1] * n) for n in range(3, 8)]
    smiths += [(f"Dtilde_{ell}", *smith_d(ell)) for ell in range(4, 9)]
    smiths += [(f"Etilde_{ell}", *arm_tree(arms, value)) for ell, arms, value in [(6, (2, 2, 2), 3), (7, (1, 3, 3), 4), (8, (1, 2, 5), 6)]]
    for name, a, x in smiths:
        assert positive_check(a, x, 2), name
        assert abs(eig(a)[-1] - 2) < 1e-10
        for deleted in range(len(a)):
            principal = [[a[i][j] for j in range(len(a)) if j != deleted] for i in range(len(a)) if i != deleted]
            assert eig(principal)[-1] < 2 - 1e-8
    report["C17"] = {name: x for name, _, x in smiths}

    b = sp.Matrix([[1, 1, 1], [1, 1, 1]])
    p, q, rank = b.rows, b.cols, b.rank()
    c = (3 * sp.eye(p)).row_join(b).col_join(b.T.row_join(2 * sp.eye(q)))
    assert c.eigenvals() == {5: 1, 3: 1, 2: 2, 0: 1}
    assert rank == 1
    bip_adjacency = sp.zeros(p).row_join(b).col_join(b.T.row_join(sp.zeros(q)))
    assert len(bip_adjacency.nullspace()) == p + q - 2 * rank
    report["rectangular_zero_modes"] = {"p": p, "q": q, "rank": int(rank), "zero_modes": int(p + q - 2 * rank), "q_minus_p": q - p}

    for a in [cycle(3), cycle(4), adjacency(4, [(0, 1), (1, 2), (2, 3)]), [[0]]]:
        n = len(a)
        aa = sp.Matrix(a)
        d = sp.diag(*(sum(row) for row in a))
        l, k = d - aa, d + aa
        assert len(l.nullspace()) == 1
        expected_bip = 0 if n == 3 else 1
        assert len(k.nullspace()) == expected_bip
        assert sum(v * v for v in eig(a)) <= n * eig(a)[-1] + 1e-9
        if n > 1:
            be = eig([row[:-1] for row in a[:-1]])
            ae = eig(a)
            assert np.all(ae[:-1] <= be + 1e-9) and np.all(be <= ae[1:] + 1e-9)
    report["graph_checks"] = "Laplacian/signless nullities, SP2 inequality and interlacing passed"

    for a, pars in [(petersen, (10, 3, 0, 1)), (cycle(4), (4, 2, 0, 2))]:
        n, degree, adjacent, nonadjacent = pars
        delta = (adjacent - nonadjacent)**2 + 4 * (degree - nonadjacent)
        theta1 = (sp.Integer(adjacent - nonadjacent) + sp.sqrt(delta)) / 2
        theta2 = (sp.Integer(adjacent - nonadjacent) - sp.sqrt(delta)) / 2
        m1 = sp.simplify((-degree - (n - 1) * theta2) / (theta1 - theta2))
        m2 = n - 1 - m1
        assert m1.is_integer and m2.is_integer
        assert sp.Matrix(a).eigenvals() == {degree: 1, theta1: m1, theta2: m2}
    report["SRG"] = "Petersen and C4 formulas and integral multiplicities passed"

    qmat = sp.Matrix([[1, 1], [1, -1]])
    a, bmat = sp.diag(0, 2), sp.Matrix([[1, -1], [-1, 1]])
    assert qmat * qmat == 2 * sp.eye(2) and qmat * a == bmat * qmat
    assert a.charpoly().as_expr() == bmat.charpoly().as_expr()

    h = sp.Matrix([[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]])
    pp = sp.Matrix([[h[i, u] * h[j, u] for u in range(4)] for i, j in combinations(range(4), 2)])
    assert pp.T * pp == 8 * sp.eye(4) - 2 * sp.ones(4)
    ch = (pp * pp.T - 4 * sp.eye(6)) / 4
    assert ch * sp.ones(6, 1) == sp.ones(6, 1)
    assert ch * sp.ones(6, 1) != -sp.ones(6, 1)
    assert ch.eigenvals() == {1: 3, -1: 3}
    report["Hadamard_row_sum_correction"] = {"n": 4, "x": 4, "actual_C_row_sum": 1, "printed_C_row_sum": -1, "P_gram_spectrum": {"8": 3, "0": 3}}

    # The empty Vandermonde system is valid only when the annihilator I is zero.
    assert spectral_check([], [], [])
    assert not spectral_check([[0]], [], [])
    assert not spectral_check([[1]], [], [])

    # Similarity alone permits a nonsymmetric zero-one matrix.
    directed = sp.Matrix([[0, 1], [0, 0]])
    ident = sp.eye(2)
    assert ident * directed == directed * ident and ident * ident == ident
    assert all(directed[i, i] == 0 for i in range(2))
    assert set(directed) <= {0, 1} and directed != directed.T
    assert not sp.Matrix([[-1]]).is_positive_semidefinite

    # Local, rather than only trace, triangle counts.
    for graph in [cycle(3), cycle(4), *c13_matrices()]:
        cube = mul(mul(graph, graph), graph)
        for u in range(len(graph)):
            triangles_at_u = sum(graph[u][v] * graph[u][w] * graph[v][w]
                                 for v, w in combinations(range(len(graph)), 2)
                                 if u not in (v, w))
            assert cube[u][u] == 2 * triangles_at_u

    # Both signs of the representation rank bound, and nonunit rank-one vectors.
    square = sp.Matrix(cycle(4))
    for sign, node in [(1, -2), (-1, 2)]:
        gram = 2 * sp.eye(4) + sign * square
        assert gram.is_positive_semidefinite and gram.rank() == 3
        assert square.eigenvals()[node] == 4 - gram.rank() == 1
    vectors = [sp.Matrix([2, 0]), sp.Matrix([1, 3]), sp.zeros(2, 1)]
    for u in vectors:
        for v in vectors:
            assert sp.trace((u * u.T) * (v * v.T)) == (u.dot(v))**2

    # Error 14: K_{6,10} and T(6) have cospectral line graphs.
    k610 = adjacency(16, [(i, 6 + j) for i in range(6) for j in range(10)])
    t6 = line_graph(adjacency(6, list(combinations(range(6), 2))))
    assert_spectrum(t6, [8, 2, -2], [1, 5, 9])
    for graph in [line_graph(k610), line_graph(t6)]:
        assert_spectrum(graph, [14, 8, 4, -2], [1, 5, 9, 45])
    assert 5 + 9 == 6 + 10 - 2 * 1 != 10 - 6
    assert 9 - 5 == 10 - 6

    # A sorted basis retains repeated eigenvalues and satisfies both Rayleigh gaps.
    matrix = np.array([[2., 1., 0.], [1., 2., 0.], [0., 0., 3.]])
    values, basis = np.linalg.eigh(matrix)
    order = np.argsort(values)[::-1]
    values, basis = values[order], basis[:, order]
    assert np.all(values[:-1] >= values[1:])
    assert np.allclose(matrix @ basis, basis * values)
    assert np.allclose(basis.T @ basis, np.eye(3))
    vector = np.array([2., -1., 4.]); coords = basis.T @ vector
    form, norm = vector @ matrix @ vector, vector @ vector
    assert np.isclose(form / norm, sum(values * coords**2) / sum(coords**2))
    assert np.isclose(values[0] * norm - form, sum((values[0] - values) * coords**2))
    assert np.isclose(form - values[-1] * norm, sum((values - values[-1]) * coords**2))
    report['review_regressions'] = {
        'empty_nodes': 'accepted exactly for empty order',
        'similarity_graph_guard': 'nonsymmetric counterexample rejected as adjacency',
        'coverage': 'local triangles, both Gram signs and arbitrary rank-one vectors passed',
        'error_14': {'kernel_multiplicities': [5, 9], 'sum': 14, 'difference': 4},
        'sorted_basis': 'repeated values, matrix action and both Rayleigh gaps passed',
    }

    path = Path(__file__).with_name("results.json")
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"All exact certificates and numerical sanity checks passed. Results: {path}")


if __name__ == "__main__":
    main()
