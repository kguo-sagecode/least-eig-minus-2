#!/usr/bin/env python3
"""Exhaustive graph control for the local Hall–Connor argument on T(7).

Vertices are the two-subsets of a seven-set, adjacent when they intersect.
Every ordered adjacent pair is tested, without choosing a preferred labelling.
This checks a real graph model, not the hypothetical design or its incidence
matrix. Only j=0 occurs; the excluded j=1,2 certificates are in check_proof.py.
"""

from collections import Counter
from itertools import combinations

import sympy as sp


def check_triangular_graph():
    vertices = [frozenset(edge) for edge in combinations(range(7), 2)]
    labels = set(range(len(vertices)))
    neighbours = {
        i: {j for j in labels if i != j and vertices[i] & vertices[j]}
        for i in labels
    }

    def is_clique(subset):
        return all(j in neighbours[i] for i, j in combinations(sorted(subset), 2))

    adjacency = sp.Matrix(21, 21, lambda i, j: int(j in neighbours[i]))
    gram = 3*sp.eye(21) - adjacency + 2*sp.ones(21)
    connor = 35*sp.eye(21) - 7*gram + 10*sp.ones(21)
    assert gram == gram.T and connor == connor.T
    assert gram*gram == 5*gram + 50*sp.ones(21)
    assert gram*sp.ones(21) == sp.ones(21)*gram == 35*sp.ones(21)
    assert connor*connor == 35*connor and connor.rank() == 6
    for b1 in labels:
        assert len(neighbours[b1]) == 10
        # An induced claw would have three pairwise nonadjacent leaves.
        assert all(any(y in neighbours[x] for x, y in combinations(leaves, 2))
                   for leaves in combinations(sorted(neighbours[b1]), 3))
    for b1, b2 in combinations(sorted(labels), 2):
        counts = Counter((int(gram[b1, label]), int(gram[b2, label]))
                         for label in labels - {b1, b2})
        expected = ((5, 4, 4, 6) if b2 in neighbours[b1] else (4, 6, 6, 3))
        assert tuple(counts[pair] for pair in ((1, 1), (1, 2), (2, 1), (2, 2))) == expected
    print("PASS: T(7), both intersection tables, no claws, G^2=5G+50J, C^2=35C, rank C=6")

    # Independently enumerate all five-block hypotheses, not just the
    # instances used in the local split (where U_0 is empty in this control).
    five_patterns = 0
    ordered_pairs = [(b1, b2) for b1 in sorted(labels) for b2 in sorted(neighbours[b1])]
    assert len(ordered_pairs) == 210
    for b1, b2 in ordered_pairs:
        for b3 in neighbours[b1] & neighbours[b2]:
            ys = neighbours[b1] - (neighbours[b2] | neighbours[b3] | {b2, b3})
            ws = (neighbours[b2] & neighbours[b3]) - (neighbours[b1] | {b1, b2, b3})
            for y in ys:
                for w in ws:
                    assert len({b1, b2, b3, y, w}) == 5
                    assert w not in neighbours[y], (b1, b2, b3, y, w)
                    five_patterns += 1
    assert five_patterns > 0, "five-block control must not be vacuous"
    print(f"PASS: T(7), all {five_patterns} ordered five-block hypotheses satisfy the restriction")

    # Enumerate rather than assume that all six-cliques are stars.
    six_cliques = {frozenset(subset) for subset in combinations(range(21), 6)
                   if is_clique(subset)}
    stars = {frozenset(i for i, edge in enumerate(vertices) if point in edge)
             for point in range(7)}
    assert six_cliques == stars and len(six_cliques) == 7
    observed_j = Counter()
    for b1, b2 in ordered_pairs:
        common = neighbours[b1] & neighbours[b2]
        left = neighbours[b1] - (neighbours[b2] | {b2})
        right = neighbours[b2] - (neighbours[b1] | {b1})
        rest = labels - ({b1, b2} | common | left | right)
        parts = ({b1, b2}, common, left, right, rest)
        assert set.union(*parts) == labels
        assert all(not (part & other) for part, other in combinations(parts, 2))
        assert tuple(map(len, (common, left, right, rest))) == (5, 4, 4, 6)
        assert neighbours[b1] == {b2} | common | left
        assert neighbours[b2] == {b1} | common | right
        assert is_clique(left) and is_clique(right)
        assert all(len(neighbours[y] & common) == 2 for y in left)
        assert sum(len(neighbours[b] & left) for b in common) == 8
        candidates = {b for b in common if len(neighbours[b] & left) >= 2}
        assert len(candidates) == 1  # Stronger than the existence used in the proof.
        for b3 in candidates:
            j = len(left - neighbours[b3])
            h = len(neighbours[b3] & (common - {b3}))
            e = len(neighbours[b3] & right)
            ell = len(neighbours[b3] & rest)
            assert 0 <= j <= 2
            assert 1 + h + (4-j) == 5
            assert 1 + h + e == 5
            assert 2 + h + (4-j) + e + ell == 10
            assert (h, e, ell) == (j, 4-j, j)
            left_zero = left - neighbours[b3]
            right_one = right & neighbours[b3]
            assert (len(left_zero), len(right_one)) == (j, 4-j)
            assert is_clique(left_zero) and is_clique(right_one)
            assert all(w not in neighbours[y] for y in left_zero for w in right_one)
            assert len({b1, b2, b3} | left_zero | right_one) == 7
            observed_j[j] += 1
            assert j == 0
            assert not (neighbours[b3] & (common - {b3}))
            assert left <= neighbours[b3] and is_clique(common - {b3})
            first = frozenset({b1, b2} | (common - {b3}))
            second = frozenset({b1, b3} | left)
            assert len(first) == len(second) == 6
            assert is_clique(first) and is_clique(second)
            assert first & second == {b1}
            assert first | second == {b1} | neighbours[b1]
            assert {clique for clique in six_cliques if {b1, b2} <= clique} == {first}
            assert {clique for clique in six_cliques if b1 in clique} == {first, second}
    assert observed_j == {0: 210}
    print("PASS: T(7), all 210 ordered adjacent pairs: sizes 5,4,4,6; eight edges;")
    print("      unique eligible B3; (h,e,ell)=(j,4-j,j) with j=0;")
    print("      local six-cliques, intersection, union and uniqueness")

    assert all(len(first & second) == 1 for first, second in combinations(six_cliques, 2))
    family = sorted(six_cliques, key=lambda clique: tuple(sorted(clique)))
    incidence = sp.Matrix(21, 7, lambda i, j: int(i in family[j]))
    assert incidence*sp.ones(7, 1) == 2*sp.ones(21, 1)
    assert incidence.T*incidence == 5*sp.eye(7) + sp.ones(7)
    print("PASS: T(7), exactly seven six-cliques, two through each vertex, clique incidence identities")
    print("LIMIT: T(7) supplies no design incidence matrix; j=1,2 do not occur.")


if __name__ == "__main__":
    check_triangular_graph()
