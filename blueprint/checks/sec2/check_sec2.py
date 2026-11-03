#!/usr/bin/env python3
"""Exact sanity checks for the Section 2 blueprint; these are not proofs.

Run with python3 blueprint/checks/sec2/check_sec2.py; requires NetworkX, NumPy and SymPy.
All inner products use integer coordinates divided by a fixed integer q.
No approximate eigenvalues, ranks, or graph invariants are used.
The checks of explicit graphs do not assert an exhaustive graph classification.
"""

from itertools import combinations, permutations, product
from math import comb

import networkx as nx
import numpy as np
import sympy as sp


def determinant_and_arithmetic():
    k = sp.symbols("k")
    B = sp.Matrix([
        [2, 1, 0, 0, k],
        [1, 2, 0, k, 0],
        [0, 0, k*k+k, k*k-k, k*k-k],
        [0, k, k*k-k, k*k+k, k],
        [k, 0, k*k-k, k, k*k+k],
    ])
    assert B == B.T and B[2, 0] == 0
    D = B[1:, 1:]
    assert sp.expand(D.det() - 2*k**5*(5-k)) == 0
    assert sp.expand(D.minor_submatrix(0, 0).det() - k**5*(7-k)) == 0
    assert sp.expand(D.minor_submatrix(0, 2).det() + 4*k**4) == 0
    cross = k*(2*k-4) + 2*k*(k-1)
    assert sp.expand(cross - (4*k*k-6*k)) == 0
    assert sp.expand(2*k*(3*k-5) - 2*k*(k-2) - cross) == 0
    assert sp.expand(2*k*(k-2) - (3*k-5)*(k-2) - (k-2)*(5-k)) == 0
    assert {6*i-3 for i in (2, 3, 5)} == {9, 15, 27}
    high = {i: (i-2)*(5-i)//2 for i in (2, 3, 4, 5)}
    assert high == {2: 0, 3: 1, 4: 1, 5: 0}
    assert 1 not in {4-2, 4}  # A neighbour of a high vertex would have d_K = 1.
    # 210combbound: for every k = 6+t with t >= 0 the high-vertex count is negative.
    t = sp.symbols("t", nonnegative=True)
    upper_count = sp.expand(((k-2)*(5-k)).subs(k, 6+t))
    assert upper_count == -t**2 - 5*t - 4
    assert upper_count.is_negative is True
    switching = {
        (0, 0): (1, (0, 0, 0)),
        (0, 1): (1, (0, 1, -1)),
        (0, -1): (-1, (0, 1, -1)),
        (1, 0): (-1, (-1, 0, 1)),
        (-1, 0): (1, (-1, 0, 1)),
        (1, -1): (1, (1, -1, 0)),
        (-1, 1): (-1, (1, -1, 0)),
    }
    for (a, b), (sign, expected) in switching.items():
        assert tuple(sign*x for x in (a, b, -a-b)) == expected
    assert set(product((-1, 0, 1), repeat=2)) - set(switching) == {(-1, -1), (1, 1)}
    print("C1: determinant, two cofactors, edge counts, high-vertex counts, switching table OK")
    print("210combbound: exact negativity of (k-2)(5-k) for every k = 6+t, t >= 0 OK")


def canonical_graph(k):
    """The complete labelled graphs constructed in Lemma 2.10."""
    X = nx.Graph()
    u, v = ("u",), ("v",)
    K = [("K", i) for i in range(k)]
    L = [("L", i) for i in range(k)]
    M = [("M", i) for i in range(k)]
    if k == 2:
        missed = {("single",): set(range(k))}
    elif k == 3:
        missed = {("centre",): set()}
        missed.update({("leaf", i): set(range(k)) - {i} for i in range(k)})
    elif k == 5:
        missed = {("pair", i, j): {i, j} for i, j in combinations(range(k), 2)}
    else:
        raise ValueError(k)
    X.add_nodes_from([u, v] + K + L + M + list(missed))
    for i in range(k):
        X.add_edges_from([(u, K[i]), (u, L[i]), (v, K[i]), (v, M[i]),
                          (K[i], L[i]), (K[i], M[i])])
        for j in range(k):
            if i != j:
                X.add_edge(L[i], M[j])
    for w, A in missed.items():
        for i in range(k):
            if i in A:
                X.add_edges_from([(w, L[i]), (w, M[i])])
            else:
                X.add_edge(w, K[i])
    if k == 3:
        X.add_edges_from([(("centre",), ("leaf", i)) for i in range(k)])
    if k == 5:
        X.add_edges_from((w, z) for w, z in combinations(missed, 2)
                         if missed[w].isdisjoint(missed[z]))
    return X


def independent_graph(k):
    """Grid, six-symbol duads, and the five-bit parity model."""
    if k == 2:
        return nx.cartesian_product(nx.complete_graph(3), nx.complete_graph(3))
    X = nx.Graph()
    if k == 3:
        pairs = list(combinations(range(6), 2))
        X.add_nodes_from(pairs)
        X.add_edges_from((a, b) for a, b in combinations(pairs, 2)
                         if set(a).isdisjoint(b))
        return X
    origin = ("origin",)
    points = [("point", i, bit) for i in range(5) for bit in (0, 1)]
    words = [w for w in product((0, 1), repeat=5) if sum(w) % 2 == 0]
    X.add_nodes_from([origin] + points + words)
    X.add_edges_from((origin, p) for p in points)
    X.add_edges_from((("point", i, 0), ("point", i, 1)) for i in range(5))
    for w in words:
        X.add_edges_from((w, ("point", i, w[i])) for i in range(5))
    X.add_edges_from((w, z) for w, z in combinations(words, 2)
                     if sum(a != b for a, b in zip(w, z)) == 4)
    return X


def has_triangle_property(X):
    """The single graph predicate in the blueprint, including its outside-vertex clause."""
    for u, v in X.edges():
        common = set(X[u]) & set(X[v])
        if len(common) != 1:
            return False
        w = next(iter(common))
        T = {u, v, w}
        if not all(len(set(X[z]) & T) == 1 for z in set(X) - T):
            return False
    return True


def triangle_property(X):
    assert has_triangle_property(X)


def small_graph_checks():
    """Exhaustive only through order seven; these do not prove the general classification."""
    count = 0
    for X in nx.graph_atlas_g():
        n = len(X)
        expected = X.number_of_edges() == 0
        if n >= 3 and n % 2 == 1:
            m = (n-1)//2
            Y = nx.complete_graph(3) if m == 1 else nx.windmill_graph(m, 3)
            expected |= nx.is_isomorphic(X, Y)
        assert has_triangle_property(X) == expected
        if has_triangle_property(X) and X.number_of_edges():
            assert any(d == n-1 for _, d in X.degree())
        count += 1
    # Unique common neighbours alone are insufficient: two disjoint triangles fail.
    assert not has_triangle_property(nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3)))
    assert not has_triangle_property(nx.complete_graph(2))
    assert not has_triangle_property(nx.complete_graph(4))
    print(f"Triangle predicate: all {count} atlas graphs through order seven and negative controls OK")


def check_pair_reconstruction(X, k, u, v):
    """Verify the proof's labelled isomorphism for a chosen nonadjacent pair."""
    assert u != v and not X.has_edge(u, v)
    K = sorted(set(X[u]) & set(X[v]), key=repr)
    L = set(X[u]) - set(X[v])
    M = set(X[v]) - set(X[u])
    N = set(X) - {u, v} - set(K) - L - M
    assert len(K) == len(L) == len(M) == k
    assert len(N) == 3*k-5
    phi = {u: ("u",), v: ("v",)}
    for i, x in enumerate(K):
        common_u = set(X[x]) & set(X[u])
        common_v = set(X[x]) & set(X[v])
        assert len(common_u) == len(common_v) == 1
        xp, xpp = next(iter(common_u)), next(iter(common_v))
        assert xp in L and xpp in M
        phi.update({x: ("K", i), xp: ("L", i), xpp: ("M", i)})
    degrees = {w: len(set(X[w]) & set(K)) for w in N}
    assert set(degrees.values()) <= {k-2, k}
    assert all(len(set(X[w]) & N) == degrees[w] for w in N)
    assert sum(degrees.values()) == k*(2*k-4)
    assert sum(d == k for d in degrees.values()) == (k-2)*(5-k)//2
    assert X.subgraph(N).number_of_edges() == k*(k-2)
    for w in N:
        A = {i for i, x in enumerate(K) if not X.has_edge(w, x)}
        for i, x in enumerate(K):
            xp = next(y for y in L if X.has_edge(x, y))
            xpp = next(y for y in M if X.has_edge(x, y))
            assert X.has_edge(w, xp) == X.has_edge(w, xpp) == (i in A)
        if k == 2:
            phi[w] = ("single",)
        elif k == 3:
            if not A:
                phi[w] = ("centre",)
            else:
                i, = set(range(k)) - A
                phi[w] = ("leaf", i)
        else:
            i, j = sorted(A)
            phi[w] = ("pair", i, j)
    Y = canonical_graph(k)
    assert set(phi) == set(X)
    assert len(set(phi.values())) == len(X) and set(phi.values()) == set(Y)
    assert all(X.has_edge(a, b) == Y.has_edge(phi[a], phi[b])
               for a, b in combinations(X, 2))
    return phi


def check_isomorphism_from_order(X, Y, k):
    """Apply the normal form to both graphs, then extend every bijection of their K labels."""
    def choose_pair(Z):
        return next((u, v) for u, v in combinations(Z, 2) if not Z.has_edge(u, v))

    labels_x = check_pair_reconstruction(X, k, *choose_pair(X))
    labels_y = check_pair_reconstruction(Y, k, *choose_pair(Y))
    inverse_y = {label: vertex for vertex, label in labels_y.items()}
    count = 0
    for beta in permutations(range(k)):
        def relabel(label):
            tag, *indices = label
            if tag in {"K", "L", "M", "leaf"}:
                return tag, beta[indices[0]]
            if tag == "pair":
                return (tag, *sorted(beta[i] for i in indices))
            return label

        psi = {x: inverse_y[relabel(label)] for x, label in labels_x.items()}
        assert set(psi.values()) == set(Y) and len(psi) == len(Y)
        assert all(X.has_edge(a, b) == Y.has_edge(psi[a], psi[b])
                   for a, b in combinations(X, 2))
        count += 1
    return count


def graph_checks():
    for k in (2, 3, 5):
        X, Y = canonical_graph(k), independent_graph(k)
        assert nx.is_isomorphic(X, Y)
        pair_count = 0
        for Z in (X, Y):
            triangle_property(Z)
            assert len(Z) == 6*k-3 and set(dict(Z.degree()).values()) == {2*k}
            for u, v in combinations(Z, 2):
                assert len(set(Z[u]) & set(Z[v])) == (1 if Z.has_edge(u, v) else k)
                if not Z.has_edge(u, v):
                    check_pair_reconstruction(Z, k, u, v)
                    pair_count += 1
        iso_count = check_isomorphism_from_order(X, Y, k)
        print(f"Graph order {len(X)}: canonical model, independent model, "
              f"triangle property, {pair_count} pair reconstructions and "
              f"all {iso_count} K-label bijections between the models OK")


def classical_roots(rank, kind, scale=2):
    dimension = rank+1 if kind == "A" else rank
    roots = []
    for i, j in combinations(range(dimension), 2):
        signs = [(1, -1), (-1, 1)] if kind == "A" else product((-1, 1), repeat=2)
        for a, b in signs:
            r = [0]*dimension
            r[i], r[j] = scale*a, scale*b
            roots.append(tuple(r))
    return roots


def e8_model_two():
    roots = classical_roots(8, "D")
    roots += [s for s in product((-1, 1), repeat=8) if sum(x == -1 for x in s) % 2 == 0]
    return roots, 4


def e8_model_one():
    roots = classical_roots(8, "A", scale=3)
    for triple in combinations(range(9), 3):
        r = tuple(-2 if i in triple else 1 for i in range(9))
        roots.extend([r, tuple(-x for x in r)])
    return roots, 9


def e8_model_three():
    # Affine planes of F_2^3: each nonzero linear functional has two fibres.
    points = list(product((0, 1), repeat=3))
    blocks = []
    for normal in points[1:]:
        for bit in (0, 1):
            blocks.append(tuple(i for i, p in enumerate(points)
                                if sum(a*b for a, b in zip(normal, p)) % 2 == bit))
    assert len(set(blocks)) == 14 and all(len(B) == 4 for B in blocks)
    assert all(sum(set(T) <= set(B) for B in blocks) == 1
               for T in combinations(range(8), 3))
    roots = []
    for i in range(8):
        for sign in (-1, 1):
            roots.append(tuple(2*sign if j == i else 0 for j in range(8)))
    for B in blocks:
        for signs in product((-1, 1), repeat=4):
            r = [0]*8
            for i, sign in zip(B, signs):
                r[i] = sign
            roots.append(tuple(r))
    return roots, 2


def root_graph(R, q, a, b):
    c = -a-b
    Ga = np.where((R @ a == 0) & (R @ b == q) & (R @ c == -q))[0]
    Delta = np.where((R @ a == 0) & (R @ b == 0))[0]
    X = nx.Graph()
    X.add_nodes_from(map(int, Ga))
    X.add_edges_from((int(i), int(j)) for i, j in combinations(Ga, 2) if R[i] @ R[j] == 0)
    return X, Ga, Delta


def verify_marked_roots(R, q, a, b):
    """Check every identity used in Lemmas 2.5--2.8 for this marked star."""
    roots = set(map(tuple, R))
    c = -a-b
    assert tuple(c) in roots
    X, Ga, Delta = root_graph(R, q, a, b)
    Gb = np.where((R @ b == 0) & (R @ c == q) & (R @ a == -q))[0]
    Gc = np.where((R @ c == 0) & (R @ a == q) & (R @ b == -q))[0]
    parts = [set(map(tuple, R[I])) for I in (Ga, Gb, Gc, Delta)]
    Sigma = {tuple(a), tuple(b), tuple(c)}.union(*parts)
    assert roots == Sigma | {tuple(-x for x in r) for r in Sigma}
    assert {tuple(R[i]+c) for i in Ga} == parts[1]
    assert {tuple(R[i]-b) for i in Ga} == parts[2]
    H = R[Ga] @ R[Ga].T
    assert np.array_equal((R[Ga]+c) @ (R[Ga]+c).T, H)
    assert set(H.ravel()) <= {0, q, 2*q}
    differences = {tuple(R[i]-R[j]) for i in Ga for j in Ga if R[i] @ R[j] == q}
    assert differences == parts[3]
    recovery = {tuple(a), tuple(b), tuple(c)} | parts[0]
    recovery |= {tuple(R[i]+c) for i in Ga} | {tuple(R[i]-b) for i in Ga} | differences
    assert recovery == Sigma  # Lemma 2.7 states this equality, not just determination.
    assert recovery | {tuple(-x for x in r) for r in recovery} == roots
    for i, j in X.edges():
        z = b-c-R[i]-R[j]
        assert tuple(z) in parts[0] and R[i] @ z == R[j] @ z == 0
        T = {tuple(R[i]), tuple(R[j]), tuple(z)}
        for w in parts[0] - T:
            products = [np.asarray(w) @ t for t in (R[i], R[j], z)]
            assert sorted(products) == [0, q, q]
    triangle_property(X)
    return X, len(Delta)//2


def model_check(name, roots, q, expected_rank, expected_lines, graph_kind=None,
                expected_delta=None, check_all_stars=False):
    assert len(roots) == len(set(roots)) == 2*expected_lines
    roots_set = set(roots)
    assert {tuple(-x for x in r) for r in roots} == roots_set
    R = np.asarray(roots, dtype=np.int64)
    H = R @ R.T
    assert np.all(np.diag(H) == 2*q)
    assert set(H.ravel()) <= {-2*q, -q, 0, q, 2*q}
    for i, j in zip(*np.where(H == -q)):
        assert tuple(R[i]+R[j]) in roots_set
    # Indecomposability of the signed root set is connectivity of nonzero products.
    Y = nx.from_numpy_array((H != 0).astype(int))
    assert nx.is_connected(Y)
    assert sp.Matrix(R.tolist()).rank() == expected_rank
    stars = list(zip(*np.where(H == -q)))
    if not stars:
        assert name == "A1" and expected_rank == expected_lines == 1
        print("A1: signed root set, rank and single-line case OK")
        return
    i, j = stars[0]
    X, delta = verify_marked_roots(R, q, R[i], R[j])
    if expected_delta is not None:
        assert delta == expected_delta
    if graph_kind[0] == "void":
        m = graph_kind[1]
        assert len(X) == m and X.number_of_edges() == 0
    elif graph_kind[0] == "friendship":
        m = graph_kind[1]
        assert len(X) == 2*m+1
        Y = nx.complete_graph(3) if m == 1 else nx.windmill_graph(m, 3)
        assert nx.is_isomorphic(X, Y)
    else:
        k = graph_kind[1]
        assert nx.is_isomorphic(X, independent_graph(k))
        for u, v in combinations(X, 2):
            if not X.has_edge(u, v):
                check_pair_reconstruction(X, k, u, v)
        # Check the actual block Gram matrix and its block-sum compression.
        u, v = next((u, v) for u, v in combinations(X, 2) if not X.has_edge(u, v))
        K = sorted(set(X[u]) & set(X[v]))
        L = [next(iter(set(X[u]) & set(X[x]))) for x in K]
        M = [next(iter(set(X[v]) & set(X[x]))) for x in K]
        vectors = np.array([R[u], R[v], R[K].sum(axis=0), R[L].sum(axis=0), R[M].sum(axis=0)])
        expected = np.array([[2, 1, 0, 0, k], [1, 2, 0, k, 0],
                             [0, 0, k*k+k, k*k-k, k*k-k],
                             [0, k, k*k-k, k*k+k, k], [k, 0, k*k-k, k, k*k+k]])
        assert np.array_equal(vectors @ vectors.T, q*expected)
    if check_all_stars:
        # Independently check the counts and local Gram graph for every ordered star.
        for i, j in stars:
            Ga = np.where((H[:, i] == 0) & (H[:, j] == q))[0]
            Delta = np.where((H[:, i] == 0) & (H[:, j] == 0))[0]
            assert len(Ga) == len(X) and len(Delta)//2 == delta
            A = H[np.ix_(Ga, Ga)] == 0
            if graph_kind[0] == "exceptional":
                k = graph_kind[1]
                assert np.all(A.sum(axis=1) == 2*k)
                common = A.astype(int) @ A.astype(int)
                expected = np.where(A, 1, k)
                np.fill_diagonal(expected, 2*k)
                assert np.array_equal(common, expected)
        all_text = f", all {len(stars)} ordered-star counts and parameters"
    else:
        all_text = ""
    print(f"{name}: {expected_lines} lines, exact rank {expected_rank}, "
          f"Gamma {len(X)}, Delta {delta} lines, Lemmas 2.5--2.8{all_text} OK")


def model_checks():
    for n in range(1, 11):
        model_check(f"A{n}", classical_roots(n, "A"), 4, n, n*(n+1)//2,
                    ("void", n-2) if n >= 2 else None)
    for n in range(4, 11):
        model_check(f"D{n}", classical_roots(n, "D"), 4, n, n*(n-1),
                    ("friendship", n-3))
    roots, q = e8_model_two()
    R = np.asarray(roots, dtype=np.int64)
    a = np.array([2, -2, 0, 0, 0, 0, 0, 0])
    b = np.array([0, 2, -2, 0, 0, 0, 0, 0])
    E7 = list(map(tuple, R[R @ a == 0]))
    E6 = list(map(tuple, R[(R @ a == 0) & (R @ b == 0)]))
    model_check("E6", E6, q, 6, 36, ("exceptional", 2), 6, True)
    model_check("E7", E7, q, 7, 63, ("exceptional", 3), 15, True)
    model_check("E8 model (ii)", roots, q, 8, 120, ("exceptional", 5), 36, True)
    for name, constructor in [("E8 model (i)", e8_model_one), ("E8 model (iii)", e8_model_three)]:
        roots, q = constructor()
        model_check(name, roots, q, 8, 120, ("exceptional", 5), 36, True)
    assert 36 + 84 == 56 + 64 == 8 + 8*14 == 120
    assert 7 + 8*7 == 63 and 4 + 8 + 4*6 == 36
    for gamma, delta, total in [(9, 6, 36), (15, 15, 63), (27, 36, 120)]:
        assert 3 + 3*gamma + delta == total
    assert comb(5, 2) == 10 and comb(3, 2) == 3
    print("C2/C4: all stated finite exceptional counts and sample classical parameters OK")


def isometry_checks():
    """Exact rational checks of 212relations--212onto, also in unequal ambient dimensions.

    We represent the quotient by a basis of the source range, then factor the target
    combinations through that range. The ambient matrix is used only on the root span.
    """
    exceptional, q = e8_model_two()
    E = np.asarray(exceptional, dtype=np.int64)
    a = np.array([2, -2, 0, 0, 0, 0, 0, 0])
    b = np.array([0, 2, -2, 0, 0, 0, 0, 0])
    models = [(f"A{n}", classical_roots(n, "A"), 4) for n in (2, 3, 5)]
    models += [(f"D{n}", classical_roots(n, "D"), 4) for n in (4, 6)]
    models += [
        ("E6", list(map(tuple, E[(E @ a == 0) & (E @ b == 0)])), q),
        ("E7", list(map(tuple, E[E @ a == 0])), q),
        ("E8", exceptional, q),
    ]
    for name, roots, q in models:
        root_array = np.asarray(roots, dtype=np.int64)
        gram = root_array @ root_array.T
        stars = list(zip(*np.where(gram == -q)))
        trials = 0
        # Deterministic different stars, including the empty and single-vertex Gamma cases.
        for source_index, target_index in ((0, len(stars)//3), (len(stars)//2, len(stars)-1)):
            i, j = stars[source_index]
            h, l = stars[target_index]
            a, b = root_array[i], root_array[j]
            a2, b2 = root_array[h], root_array[l]
            X, Ga, _ = root_graph(root_array, q, a, b)
            Y, _, _ = root_graph(root_array, q, a2, b2)
            psi = next(nx.algorithms.isomorphism.GraphMatcher(X, Y).isomorphisms_iter())
            source = np.vstack([a, b, -a-b, root_array[Ga]])
            target = np.vstack([a2, b2, -a2-b2, root_array[[psi[int(x)] for x in Ga]]])
            # The target lives in a strictly larger space. Neither system is assumed spanning.
            target = np.pad(target, ((0, 0), (0, 2)))
            R = sp.Matrix(source.tolist()).T
            T = sp.Matrix(target.tolist()).T
            assert R.T*R == T.T*T
            for relation in R.nullspace():
                assert T*relation == sp.zeros(T.rows, 1)
            # A negative control must fail the relation a+b+c=0.
            broken = T.copy()
            broken[:, 2] = 2*T[:, 2]
            relation = sp.Matrix([1, 1, 1] + [0]*len(Ga))
            assert R*relation == sp.zeros(R.rows, 1)
            assert broken*relation != sp.zeros(T.rows, 1)
            pivots = R.rref()[1]
            B, C = R[:, list(pivots)], T[:, list(pivots)]
            coordinates = (B.T*B).inv()*B.T
            F = C*coordinates
            assert F*R == T
            assert B.T*B == C.T*C and C.rank() == B.cols
            all_roots = sp.Matrix(root_array.tolist()).T
            assert B*coordinates*all_roots == all_roots  # The generators span every root.
            image = F*all_roots
            expected = {tuple(r) + (0, 0) for r in roots}
            assert {tuple(image[:, i]) for i in range(image.cols)} == expected
            assert image.T*image == all_roots.T*all_roots
            trials += 1
        print(f"{name}: {trials} exact kernel factorizations, span isometries and root-set bijections OK")


if __name__ == "__main__":
    determinant_and_arithmetic()
    small_graph_checks()
    graph_checks()
    model_checks()
    isometry_checks()
    print("All exact Section 2 sanity checks passed. These checks are not Lean proofs.")
