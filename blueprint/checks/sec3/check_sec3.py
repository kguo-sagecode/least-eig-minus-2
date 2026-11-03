#!/usr/bin/env python3
"""Exact arithmetic checks for C2--C6, not Lean proofs or a classification search.

All root tables use the existing Lean models' raw integer scales. Only the
classical checks use sample ranks; their blueprint proofs are parametric.
--write-certificates materializes the two C4 permutations for subsequent audits.
"""

from pathlib import Path
from itertools import combinations, product
import argparse
import json

import networkx as nx
import numpy as np
import sympy as sp

HERE = Path(__file__).resolve().parent
BLOCKS = ["1234", "1256", "1278", "1357", "1368", "1458", "1467",
          "2358", "2367", "2457", "2468", "3456", "3478", "5678"]


def classical(kind, rank, scale=1):
    d = rank + (kind == "A")
    rows = []
    for i, j in combinations(range(d), 2):
        signs = [(1, -1), (-1, 1)] if kind == "A" else product((-1, 1), repeat=2)
        for s, t in signs:
            row = [0] * d
            row[i], row[j] = scale * s, scale * t
            rows.append(row)
    return np.array(sorted(rows), dtype=np.int64)


def exceptional():
    two = classical("D", 8, 2).tolist()
    two += [list(s) for s in product((-1, 1), repeat=8) if np.prod(s) == 1]
    one = classical("A", 8, 3).tolist()
    for t in combinations(range(9), 3):
        r = [-2 if i in t else 1 for i in range(9)]
        one.extend([r, [-x for x in r]])
    three = []
    for i in range(8):
        for s in (-1, 1):
            three.append([2 * s if i == j else 0 for j in range(8)])
    for block in BLOCKS:
        for signs in product((-1, 1), repeat=4):
            r = [0] * 8
            for i, s in zip(block, signs):
                r[int(i) - 1] = s
            three.append(r)
    two = np.array(sorted(two), dtype=np.int64)
    return {
        "E8i": (np.array(sorted(one), dtype=np.int64), 9, 8, 120),
        "E8ii": (two, 4, 8, 120),
        "E8iii": (np.array(sorted(three), dtype=np.int64), 2, 8, 120),
        "E7": (two[two[:, 6] == two[:, 7]], 4, 7, 63),
        "E6": (two[(two[:, 5] == two[:, 6]) & (two[:, 6] == two[:, 7])], 4, 6, 36),
    }


def model(R, q, rank, count):
    roots = set(map(tuple, R.tolist()))
    assert len(R) == len(roots) == 2 * count
    assert {tuple(-x for x in r) for r in roots} == roots
    H = R @ R.T
    assert np.all(np.diag(H) == 2 * q)
    assert set(H.ravel()) <= {-2*q, -q, 0, q, 2*q}
    for a, b in zip(*np.where(H == -q)):
        assert tuple(R[a] + R[b]) in roots
    assert sp.Matrix(R.tolist()).rank() == rank
    adjacency = (H != 0).astype(int)
    np.fill_diagonal(adjacency, 0)
    assert nx.is_connected(nx.from_numpy_array(adjacency))
    return H


def marked(R, q):
    a, b = np.zeros(R.shape[1], dtype=np.int64), np.zeros(R.shape[1], dtype=np.int64)
    # All calls to this helper use q = scale^2.
    scale = {1: 1, 4: 2, 9: 3}[q]
    a[0], a[1], b[1], b[2] = scale, -scale, scale, -scale
    L = R[(R @ a == 0) & (R @ b == q)]
    A = (L @ L.T == 0).astype(np.int64)
    return L, A


def target_graph(name):
    vertices = list(product(range(3), repeat=2)) if name == "E6" else list(combinations(range(1, 7), 2))
    A = np.zeros((len(vertices), len(vertices)), dtype=np.int64)
    for i, u in enumerate(vertices):
        for j, v in enumerate(vertices):
            A[i, j] = i != j and ((u[0] == v[0] or u[1] == v[1]) if name == "E6"
                                  else set(u).isdisjoint(v))
    return vertices, A


def graph_certificates(models, write=False):
    if write:
        certificates = {"format": "source sorted raw Gamma index -> lexicographic target index",
                        "coordinates": "one-based in the blueprint; zero-based list positions"}
        for name in ("E6", "E7"):
            R, q, _, _ = models[name]
            L, A = marked(R, q)
            vertices, B = target_graph(name)
            matcher = nx.algorithms.isomorphism.GraphMatcher(nx.from_numpy_array(A), nx.from_numpy_array(B))
            mapping = next(matcher.isomorphisms_iter())
            certificates[name] = {"raw_gamma": L.tolist(), "target_vertices": vertices,
                                  "permutation": [mapping[i] for i in range(len(L))]}
        (HERE / "certificates.json").write_text(json.dumps(certificates, indent=2) + "\n")
    certificates = json.loads((HERE / "certificates.json").read_text())
    for name in ("E6", "E7"):
        R, q, _, _ = models[name]
        L, A = marked(R, q)
        vertices, B = target_graph(name)
        data = certificates[name]
        assert data["raw_gamma"] == L.tolist()
        assert data["target_vertices"] == [list(v) for v in vertices]
        p = data["permutation"]
        assert sorted(p) == list(range(len(L)))
        assert np.array_equal(A, B[np.ix_(p, p)])
    print("C4: exact grid and disjoint-pair permutation certificates OK")


LEAN = HERE.parents[2] / "LineGraphs/Computations"


def lean_table(name):
    """Read an integer adjacency table of the Lean C4 data files, without evaluating Lean."""
    number = name[1]
    text = (LEAN / f"C4E{number}Data.lean").read_text()
    body = text.split(f"def e{number}Adjacency : IntMatrix := [", 1)[1].split("]]", 1)[0] + "]"
    rows = [[int(x) for x in row.strip(" [],\n").split(",")]
            for row in body.split("],") if row.strip(" [],\n")]
    return np.array(rows, dtype=np.int64)


def lean_star_certificates(models, write=False):
    """The Lean isomorphisms are for the orthogonality graph of the star
    (e1+e2, -e1+e3); certify the lattice and disjointness labels of their tables."""
    for name in ("E6", "E7"):
        source = (LEAN / f"C4E{name[1]}.lean").read_text()
        assert "EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 1" in source
        assert "-EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 2 1" in source
        subscript = {"E6": "₆", "E7": "₇"}[name]
        assert f"theorem E{subscript}.orthGraph_isSRGWith" in source
        assert f"noncomputable def E{subscript}.orthGraphIso" in source
    # The signed permutation sigma of C4: e1 -> e2, e2 -> -e1, e3 -> -e3, in doubled coordinates.
    sigma = np.eye(8, dtype=np.int64)
    sigma[:, :3] = 0
    sigma[1, 0], sigma[0, 1], sigma[2, 2] = 1, -1, -1
    star = np.zeros(8, dtype=np.int64), np.zeros(8, dtype=np.int64)
    star[0][0], star[0][1], star[1][1], star[1][2] = 2, -2, 2, -2
    lean_star = sigma @ star[0], sigma @ star[1]
    assert lean_star[0].tolist() == [2, 2, 0, 0, 0, 0, 0, 0]
    assert lean_star[1].tolist() == [-2, 0, 2, 0, 0, 0, 0, 0]
    for name in ("E8ii", "E7", "E6"):
        R = models[name][0]
        assert set(map(tuple, R @ sigma.T)) == set(map(tuple, R)), ("sigma", name)
    for rank in range(4, 13):
        R = classical("D", rank)
        s = np.eye(rank, dtype=np.int64)
        s[:, :3] = 0
        s[1, 0], s[0, 1], s[2, 2] = 1, -1, -1
        assert set(map(tuple, R @ s.T)) == set(map(tuple, R)), ("sigma", rank)
    path = HERE / "certificates.json"
    certificates = json.loads(path.read_text())
    for name in ("E6", "E7"):
        R, q, _, _ = models[name]
        a, b = lean_star
        L = R[(R @ a == 0) & (R @ b == q)]
        orth = (L @ L.T == 0).astype(np.int64)
        table = lean_table(name)
        assert table.shape == orth.shape and np.array_equal(table, table.T)
        assert not np.diag(table).any() and set(table.ravel()) <= {0, 1}
        # The Lean table is the orthogonality graph (inner product 0) of this star, not the
        # represented graph at inner product 1.
        tbl, og = nx.from_numpy_array(table), nx.from_numpy_array(orth)
        assert nx.is_isomorphic(tbl, og)
        # Within Gamma_a the products are 0 or 1 (Lemma 2.6), so the represented graph is the
        # complement. The 3x3 lattice graph is self-complementary; for E7 the two differ.
        off = (L @ L.T)[~np.eye(len(L), dtype=bool)]
        assert set(off.tolist()) <= {0, q}
        rep = (L @ L.T == q).astype(np.int64)
        np.fill_diagonal(rep, 0)
        assert np.array_equal(rep, 1 - orth - np.eye(len(L), dtype=np.int64))
        if name == "E7":
            assert not nx.is_isomorphic(tbl, nx.from_numpy_array(rep))
        vertices, B = target_graph(name)
        key = name + "_lean"
        if write:
            mapping = next(nx.algorithms.isomorphism.GraphMatcher(tbl, nx.from_numpy_array(B))
                           .isomorphisms_iter())
            certificates[key] = {"source": f"LineGraphs/Computations/C4E{name[1]}Data.lean",
                                 "table": table.tolist(), "target_vertices": [list(v) for v in vertices],
                                 "permutation": [mapping[i] for i in range(len(table))]}
        data = certificates[key]
        assert data["table"] == table.tolist()
        assert data["target_vertices"] == [list(v) for v in vertices]
        p = data["permutation"]
        assert sorted(p) == list(range(len(table)))
        assert np.array_equal(table, B[np.ix_(p, p)])
    if write:
        path.write_text(json.dumps(certificates, indent=2) + "\n")
    print("C4: sigma carries our star to the Lean star; Lean E6/E7 orthogonality tables, "
          "lattice and disjointness permutations OK")


def exceptional_star_census(R, q, row):
    n, d, lam, mu, delta, pair_count = row
    H = R @ R.T
    pairs = list(zip(*np.where(H == -q)))
    assert len(pairs) == pair_count
    for i, j in pairs:
        indices = np.flatnonzero((H[:, i] == 0) & (H[:, j] == q))
        orth = np.flatnonzero((H[:, i] == 0) & (H[:, j] == 0))
        assert len(indices) == n and len(orth) == 2 * delta
        A = (H[np.ix_(indices, indices)] == 0).astype(np.int64)
        assert np.all(A.sum(axis=1) == d) and np.all(np.diag(A) == 0)
        common = np.where(A, lam, mu)
        np.fill_diagonal(common, d)
        assert np.array_equal(A @ A, common)


def isometries(models):
    one, two, three = (models[name][0] for name in ("E8i", "E8ii", "E8iii"))
    # Raw map: 3x -> 2 U(x). The last output coordinate is negated.
    numerators = 2 * one[:, :8] + one[:, 8, None]
    assert np.all(numerators % 3 == 0)
    images = numerators // 3
    images[:, 7] *= -1
    assert set(map(tuple, images)) == set(map(tuple, two))
    assert np.array_equal(4 * (one @ one.T), 9 * (images @ images.T))
    Q = np.kron(np.eye(4, dtype=np.int64), np.array([[1, 1], [1, -1]], dtype=np.int64))
    assert np.array_equal(Q.T @ Q, 2 * np.eye(8, dtype=np.int64))
    images = three @ Q.T
    assert set(map(tuple, images)) == set(map(tuple, two))
    assert np.array_equal(4 * (three @ three.T), 2 * (images @ images.T))
    print("C3: both explicit raw maps, all 240 images and scaled Gram products OK")


def blocks_and_cuts(models):
    blocks = [set(map(int, b)) for b in BLOCKS]
    assert len(blocks) == 14
    assert all(len(b & c) in (0, 2) for b, c in combinations(blocks, 2))
    assert all(sum(set(t) <= b for b in blocks) == 1 for t in combinations(range(1, 9), 3))
    R = models["E8iii"][0]
    T7 = R[R[:, 7] == 0]
    T6 = T7[T7[:, 4:8].sum(axis=1) == 0]
    model(T7, 2, 7, 63)
    model(T6, 2, 6, 36)
    # Axis / 1234 / each of the six other supports in the printed count.
    counts = {}
    for r in T6:
        support = tuple(np.flatnonzero(r))
        counts[support] = counts.get(support, 0) + 1
    assert sorted(counts.values()) == [2]*4 + [8]*6 + [16]
    print("C2: fixed Steiner blocks, all triples, T7=63 and T6=4+8+4*6=36 OK")


def inclusions(models):
    one, two = models["E8i"][0], models["E8ii"][0]
    assert set(map(tuple, classical("A", 8, 3))) < set(map(tuple, one))
    assert set(map(tuple, classical("D", 8, 2))) < set(map(tuple, two))
    # An explicit E8 automorphism implementing the root-transitivity argument for A7.
    # For doubled roots r, tau_r(v) = v - (v.r/4) r.
    h = np.ones(8, dtype=np.int64)
    u = h.copy(); u[0] -= 2; u[6] -= 2
    v = np.zeros(8, dtype=np.int64); v[0] = v[7] = 2
    def reflection(rows, r):
        products = rows @ r
        assert np.all(products % 4 == 0)
        return rows - (products // 4)[:, None] * r
    for r in (u, v):
        assert tuple(r) in set(map(tuple, two))
        assert set(map(tuple, reflection(two, r))) == set(map(tuple, two))
    image_h = reflection(reflection(h[None, :], u), v)[0]
    expected = np.zeros(8, dtype=np.int64); expected[6], expected[7] = 2, -2
    assert np.array_equal(image_h, expected)
    image_A7 = reflection(reflection(classical("A", 7, 2), u), v)
    assert set(map(tuple, image_A7)) < set(map(tuple, models["E7"][0]))
    assert sp.Matrix(image_A7.tolist()).rank() == 7
    _, grid = target_graph("E6")
    assert not any(not grid[np.ix_(t, t)].any() for t in combinations(range(9), 4))
    vertices, duads = target_graph("E7")
    pencil = [i for i, pair in enumerate(vertices) if 1 in pair]
    assert len(pencil) == 5 and not duads[np.ix_(pencil, pencil)].any()
    assert 2*(6-3) > 4 and 2*(7-3) > 6
    # Polynomial inequalities used to exhaust the equal-rank types.
    n = sp.symbols("n", integer=True, positive=True)
    assert sp.expand(n*(n-1)-n*(n+1)/2-n*(n-3)/2) == 0
    assert [(r*(r+1)//2, r*(r-1), models[f"E{r}" if r != 8 else "E8ii"][3])
            for r in (6, 7, 8)] == [(21, 30, 36), (28, 42, 63), (36, 56, 120)]
    print("C5: A8/D8 embeddings, explicit A7->E7 isometry, grid cocliques, pencil and degrees OK")


def frames(models):
    eye = lambda n: np.eye(n, dtype=np.int64)
    ones = lambda n: np.ones((n, n), dtype=np.int64)
    seven = np.zeros((8, 8), dtype=np.int64)
    seven[:6, :6], seven[6:, 6:] = 144*eye(6), 72*ones(2)
    six = np.zeros((8, 8), dtype=np.int64)
    six[:5, :5], six[5:, 5:] = 96*eye(5), 32*ones(3)
    expected = {"E8i": 540*eye(9)-60*ones(9), "E8ii": 240*eye(8),
                "E8iii": 120*eye(8), "E7": seven, "E6": six}
    for name, (R, q, rank, count) in models.items():
        K = R.T @ R
        assert np.array_equal(K, expected[name])
        assert np.array_equal(rank * (R @ K), 4 * count * q * R)
        # A deliberately arbitrary signing, then signs switched and order reversed.
        signing = np.array([r for r in R if next(x for x in r if x) > 0], dtype=np.int64)
        signing[::3] *= -1
        signing = signing[::-1]
        assert len(signing) == count
        assert np.array_equal(2 * signing.T @ signing, K)
        gram = signing @ signing.T
        assert np.array_equal(rank * (gram @ gram), 2 * count * q * gram)
        assert 2*count//rank-2 == {"E8i": 28, "E8ii": 28, "E8iii": 28, "E7": 16, "E6": 10}[name]
    # Regression: scalar identities in the oversized ambient space are false.
    assert not np.array_equal(seven, 144*eye(8))
    assert not np.array_equal(six, 96*eye(8))
    assert not np.array_equal(expected["E8i"], 540*eye(9))
    print("C6: all five exceptional coordinate matrices, span restriction, arbitrary signings and constants OK")


def run(write=False):
    models = exceptional()
    for name, (R, q, rank, count) in models.items():
        model(R, q, rank, count)
        print(f"C2/C4: {name}, {count} lines, exact rank {rank}, angles, closure, connectivity OK")
    blocks_and_cuts(models)
    isometries(models)
    rows = {"E6": (9, 4, 1, 2, 6, 1440), "E7": (15, 6, 1, 3, 15, 4032),
            "E8ii": (27, 10, 1, 5, 36, 13440)}
    for name, row in rows.items():
        R, q, _, _ = models[name]
        exceptional_star_census(R, q, row)
        print(f"C4: {name}, all {row[-1]} ordered-star rows OK")
    graph_certificates(models, write)
    lean_star_certificates(models, write)
    inclusions(models)
    frames(models)
    for kind, ranks in (("A", range(1, 13)), ("D", range(4, 13))):
        for rank in ranks:
            R = classical(kind, rank)
            count = rank*(rank+1)//2 if kind == "A" else rank*(rank-1)
            model(R, 1, rank, count)
            K = R.T @ R
            d = R.shape[1]
            expected = 2*(d*np.eye(d, dtype=np.int64)-np.ones((d, d), dtype=np.int64)) if kind == "A" else 4*(rank-1)*np.eye(d, dtype=np.int64)
            assert np.array_equal(K, expected)
            if rank >= 2:
                L, A = marked(R, 1)
                if kind == "A":
                    assert len(L) == rank-2 and not A.any()
                else:
                    assert len(L) == 2*rank-5
                    centre = next(i for i, r in enumerate(L) if r[0] == r[1] == 1)
                    assert A[centre].sum() == 2*(rank-3)
                    outer = np.delete(np.delete(A, centre, axis=0), centre, axis=1)
                    assert np.all(outer.sum(axis=1) == 1)
    print("Classical samples A1--A12 and D4--D12: counts, spans, closure, marked graphs, C6 OK")
    print("All Section 3 exact sanity checks passed. No spectral or classification oracle was used.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-certificates", action="store_true")
    run(parser.parse_args().write_certificates)
