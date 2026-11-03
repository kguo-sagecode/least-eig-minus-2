"""Independent extension of checks/enumerate_cartan.py to 8, 9 and 10 vertices.

Supports: all trees (networkx.nonisomorphic_trees). Non-tree supports contain a cycle, whose
largest eigenvalue is 2, so they are excluded by the monotonicity lemma; this script does not
re-test them.  For every tree and every assignment of products M(i,j)M(j,i) in {1,2,3} to its
edges, and for every orientation of the multiple edges, we build the integer matrix M and a
positive integer symmetrizer d, and decide positive definiteness of diag(d)M exactly by
Sylvester's criterion with fraction-free (Bareiss) determinants.  Every accepted matrix must
match exactly one of Mathlib's named matrices of that rank (literal transcription in
mathlib_literal.py), by directed graph isomorphism preserving entries.
"""
from itertools import product
from collections import Counter
import networkx as nx
from mathlib_literal import A, B, C, D, E, F4, G2


def bareiss_leading_minors(m):
    """Return all leading principal minors of the integer matrix m (list of lists)."""
    n = len(m)
    out = []
    for k in range(1, n + 1):
        a = [row[:k] for row in m[:k]]
        prev = 1
        sign = 1
        for p in range(k - 1):
            if a[p][p] == 0:
                # swap with a lower row having a nonzero pivot
                for r in range(p + 1, k):
                    if a[r][p] != 0:
                        a[p], a[r] = a[r], a[p]
                        sign = -sign
                        break
                else:
                    a = None
                    break
            for i in range(p + 1, k):
                for j in range(p + 1, k):
                    a[i][j] = (a[i][j] * a[p][p] - a[i][p] * a[p][j]) // prev
            prev = a[p][p]
        out.append(0 if a is None else sign * a[k - 1][k - 1])
    return out


def pos_def(h):
    return all(x > 0 for x in bareiss_leading_minors(h))


def digraph(m):
    g = nx.DiGraph()
    n = len(m)
    g.add_nodes_from(range(n))
    for i in range(n):
        for j in range(n):
            if i != j and m[i][j]:
                g.add_edge(i, j, entry=int(m[i][j]))
    return g


def named(n):
    out = [("A", A(n))]
    if n >= 2: out.append(("B", B(n)))
    if n >= 3: out.append(("C", C(n)))
    if n >= 4: out.append(("D", D(n)))
    if n in (6, 7, 8): out.append(("E", E(n)))
    if n == 4: out.append(("F", F4))
    if n == 2: out.append(("G", G2))
    return [(k, digraph(mat.tolist())) for k, mat in out]


em = nx.algorithms.isomorphism.categorical_edge_match("entry", 0)

if __name__ == "__main__":
    for n in range(8, 11):
        counts, types = Counter(), Counter()
        targets = named(n)
        for t in nx.nonisomorphic_trees(n):
            counts["trees"] += 1
            unit = [[2 if i == j else (-1 if t.has_edge(i, j) else 0) for j in range(n)] for i in range(n)]
            if not pos_def(unit):
                counts["trees_rejected_at_unit_weights"] += 1
                continue
            counts["surviving_trees"] += 1
            edges = list(nx.bfs_edges(t, 0))
            for w in product((1, 2, 3), repeat=len(edges)):
                m = [[2 if i == j else 0 for j in range(n)] for i in range(n)]
                d = [1] * n
                for (i, j), p in zip(edges, w):
                    m[i][j], m[j][i] = -p, -1
                    d[j] = d[i] * p
                h = [[d[i] * m[i][j] for j in range(n)] for i in range(n)]
                assert all(h[i][j] == h[j][i] for i in range(n) for j in range(n))
                counts["assignments"] += 1
                if not pos_def(h):
                    continue
                counts["accepted_assignments"] += 1
                mult = [k for k, p in enumerate(w) if p > 1]
                for flips in product((False, True), repeat=len(mult)):
                    o = [row[:] for row in m]
                    for k, f in zip(mult, flips):
                        if f:
                            i, j = edges[k]
                            o[i][j], o[j][i] = o[j][i], o[i][j]
                    g = digraph(o)
                    hits = [k for k, tg in targets if nx.is_isomorphic(g, tg, edge_match=em)]
                    assert len(hits) == 1, (n, edges, w, flips, hits)
                    types[(hits[0], n)] += 1
        expected = {("A", n), ("B", n), ("C", n), ("D", n)} | ({("E", 8)} if n == 8 else set())
        assert set(types) == expected, (n, types)
        print(n, dict(counts), dict(sorted(types.items())))
    print("Trees on 8, 9, 10 vertices: every finite-type orientation is exactly one listed type.")
