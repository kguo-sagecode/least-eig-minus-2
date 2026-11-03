"""Exhaustive weighted-support sanity check through seven vertices.

NetworkX's graph atlas contains every simple graph up to seven vertices.
Every connected support is considered. Exact rational LDL elimination rejects
supports with 2I-A not positive definite. Entrywise monotonicity rejects every
weighted refinement of such a support. Every assignment of squared weights
1, 2, 3 on each remaining support is then checked by exact rational arithmetic.
Every orientation of every accepted multiple edge is compared to Mathlib's
named matrices, using directed graph isomorphism.
"""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
import networkx as nx
import numpy as np
from models import cartan


def positive_definite(a):
    h = [[Q(x) for x in row] for row in a]
    for k in range(len(h)):
        if h[k][k] <= 0:
            return False
        for i in range(k + 1, len(h)):
            for j in range(i, len(h)):
                h[j][i] = h[i][j] = h[i][j] - h[i][k]*h[k][j]/h[k][k]
    return True


def matrix_graph(a):
    g = nx.DiGraph()
    g.add_nodes_from(range(len(a)))
    for i in range(len(a)):
        for j in range(len(a)):
            if i != j and a[i][j]:
                g.add_edge(i, j, entry=int(a[i][j]))
    return g


def same(a, b):
    return nx.is_isomorphic(a, b, edge_match=nx.algorithms.isomorphism.categorical_edge_match("entry", 0))


if __name__ == "__main__":
    counts = Counter()
    types = Counter()
    for raw in nx.graph_atlas_g():
        if not raw or not nx.is_connected(raw):
            continue
        x = nx.convert_node_labels_to_integers(raw)
        n = len(x)
        counts["connected_supports"] += 1
        a = [[2 if i == j else -int(x.has_edge(i, j)) for j in range(n)] for i in range(n)]
        if not positive_definite(a):
            counts["supports_rejected_exactly"] += 1
            continue
        assert nx.is_tree(x)  # observed by enumeration, not assumed in generating supports
        counts["surviving_supports"] += 1
        edges = list(nx.bfs_edges(x, 0))
        for weights in product((1, 2, 3), repeat=len(edges)):
            counts["weighted_assignments"] += 1
            m = [[2 if i == j else 0 for j in range(n)] for i in range(n)]
            d = [1] * n
            b = np.zeros((n, n))
            for (i, j), p in zip(edges, weights):
                m[i][j], m[j][i] = -p, -1
                d[j] = d[i] * p
                b[i, j] = b[j, i] = np.sqrt(p)
            h = [[d[i]*m[i][j] for j in range(n)] for i in range(n)]
            assert h == list(map(list, zip(*h)))
            pd = positive_definite(h)
            top = np.linalg.eigvalsh(b)[-1]
            assert pd == (top < 2 - 1e-9), (n, edges, weights, top)
            if not pd:
                continue
            counts["accepted_weighted_assignments"] += 1
            candidates = [("A", n)]
            if n >= 2: candidates.append(("B", n))
            if n >= 3: candidates.append(("C", n))
            if n >= 4: candidates.append(("D", n))
            if n in (6, 7): candidates.append(("E", n))
            if n == 4: candidates.append(("F", n))
            if n == 2: candidates.append(("G", n))
            named = [(k, matrix_graph(cartan(k, r).tolist())) for k, r in candidates]
            multiple = [j for j, p in enumerate(weights) if p > 1]
            for flips in product((False, True), repeat=len(multiple)):
                oriented = [row[:] for row in m]
                for e, flip in zip(multiple, flips):
                    if flip:
                        i, j = edges[e]
                        oriented[i][j], oriented[j][i] = oriented[j][i], oriented[i][j]
                g = matrix_graph(oriented)
                matches = [k for k, target in named if same(g, target)]
                assert len(matches) == 1, (n, edges, weights, flips, matches)
                types[(matches[0], n)] += 1
                counts["accepted_orientations"] += 1
    expected = {(k, n) for k, ran in [("A", range(1, 8)), ("B", range(2, 8)),
                ("C", range(3, 8)), ("D", range(4, 8)), ("E", (6, 7)),
                ("F", (4,)), ("G", (2,))] for n in ran}
    assert set(types) == expected
    print(dict(counts))
    print("Observed types (multiplicities include different labellings and orientations):")
    print(dict(sorted(types.items())))
    print("Exhaustive check passed through seven vertices; all accept/reject decisions were exact.")
