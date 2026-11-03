"""Sanity check of Lemmas 5.3-5.5 and Corollary D on trees with up to 14
vertices: the trees with largest eigenvalue < 2 are exactly the paths, T(1,1,c) and
T(1,2,2), T(1,2,3), T(1,2,4); those with largest eigenvalue exactly 2 are the tilde-D and
tilde-E trees. Strict inequality decisions are exact: leading minors of 2I-A by
Bareiss. The equality-to-2 test uses numerical tolerance 1e-9. We additionally
construct and check the path and arm bijections and Section 6 reindexings exactly.
Uses exact leading principal minors to test positive definiteness.
"""
import networkx as nx
import numpy as np
from trees_to_ten import bareiss_leading_minors
from mathlib_literal import D, E


def check_path_labelling(t, start=None):
    paths = [path for targets in dict(nx.all_pairs_shortest_path(t)).values()
             for path in targets.values()]
    phi = max(paths, key=len)
    if start is not None:
        assert t.degree(start) <= 1
        if phi[0] != start:
            phi = phi[::-1]
        assert phi[0] == start
    assert len(phi) == len(set(phi)) == len(t)
    assert set(phi) == set(t)
    for i in range(len(phi)):
        for j in range(len(phi)):
            assert t.has_edge(phi[i], phi[j]) == (abs(i-j) == 1)
    return phi


def check_arm_labelling(t, centre):
    paths = nx.single_source_shortest_path(t, centre)
    arms = []
    for neighbour in t[centre]:
        vertices = {u for u, path in paths.items() if len(path) > 1 and path[1] == neighbour}
        arm = check_path_labelling(t.subgraph(vertices), neighbour)
        arms.append(arm)
    arms.sort(key=lambda arm: (len(arm), arm))
    assert len(arms) == 3 and all(arms)
    phi = {(r, i+1): u for r, arm in enumerate(arms, 1) for i, u in enumerate(arm)}
    phi["centre"] = centre
    assert len(phi) == len(set(phi.values())) == len(t)
    assert set(phi.values()) == set(t)
    edges = {frozenset((centre, arm[0])) for arm in arms}
    edges |= {frozenset((arm[i], arm[i+1])) for arm in arms for i in range(len(arm)-1)}
    assert edges == {frozenset(edge) for edge in t.edges()}
    n = len(t)
    lengths = tuple(map(len, arms))
    if lengths[:2] == (1, 1):
        order = [phi[(3, n-3-i)] for i in range(n-3)]
        order += [centre, phi[(1, 1)], phi[(2, 1)]]
        target = D(n)
    elif lengths in ((1, 2, 2), (1, 2, 3), (1, 2, 4)):
        order = [phi[(2, 2)], phi[(1, 1)], phi[(2, 1)], centre]
        order += [phi[(3, i-3)] for i in range(4, n)]
        target = E(n)
    else:
        return
    assert len(set(order)) == n
    for i in range(n):
        for j in range(n):
            assert target[i, j] == (2 if i == j else -int(t.has_edge(order[i], order[j])))


def shape(t):
    degs = sorted(d for _, d in t.degree())
    n = t.number_of_nodes()
    if n == 1 or max(degs) <= 2:
        return ("path", n)
    branch = [v for v, d in t.degree() if d >= 3]
    if len(branch) == 1 and t.degree(branch[0]) == 3:
        v = branch[0]
        h = t.copy(); h.remove_node(v)
        arms = sorted(len(c) for c in nx.connected_components(h))
        return ("T", tuple(arms))
    return ("other", tuple(degs))


def dynkin(sh, n):
    if sh[0] == "path": return True
    if sh[0] == "T":
        a, b, c = sh[1]
        return (a, b) == (1, 1) or (a, b, c) in {(1, 2, 2), (1, 2, 3), (1, 2, 4)}
    return False


def affine(t, sh, n):
    if sh[0] == "T" and sh[1] in {(2, 2, 2), (1, 3, 3), (1, 2, 5)}: return True
    degs = sorted(d for _, d in t.degree())
    if n == 5 and degs == [1, 1, 1, 1, 4]: return True
    # tilde D_l, l >= 5: exactly two vertices of degree 3, four leaves, rest degree 2
    b3 = [v for v, d in t.degree() if d == 3]
    if (len(b3) == 2 and degs.count(1) == 4 and max(degs) == 3
            and all(sum(1 for w in t[v] if t.degree(w) == 1) == 2 for v in b3)):
        return True
    return False


if __name__ == "__main__":
    for n in range(1, 15):
        for t in nx.nonisomorphic_trees(n) if n > 1 else [nx.path_graph(1)]:
            t = nx.convert_node_labels_to_integers(t)
            if max(dict(t.degree()).values()) <= 2:
                check_path_labelling(t)
                for start in t:
                    if t.degree(start) <= 1:
                        check_path_labelling(t, start)
            branches = [u for u in t if t.degree(u) >= 3]
            if len(branches) == 1 and t.degree(branches[0]) == 3:
                check_arm_labelling(t, branches[0])
            a = [[2 if i == j else (-1 if t.has_edge(i, j) else 0) for j in range(n)] for i in range(n)]
            minors = bareiss_leading_minors(a)
            pd = all(m > 0 for m in minors)
            sh = shape(t)
            assert pd == dynkin(sh, n), (n, sh)
            # lambda = 2 exactly iff 2I - A is singular positive semidefinite; for trees that
            # are not PD, singular iff det = 0 and all proper leading minors > 0 is not a test
            # in general, so test the graph list instead via numpy eigenvalues.
            lam = max(np.linalg.eigvalsh(nx.to_numpy_array(t)))
            assert (abs(lam - 2) < 1e-9) == affine(t, sh, n), (n, sh, lam)
    print("Trees with <= 14 vertices: lambda < 2 exactly for the Dynkin shapes; lambda = 2")
    print("exactly for tilde-D and tilde-E (numerical tolerance 1e-9 for the equality test).")
    print("All applicable path/endpoint and three-arm bijections and D/E reindexings passed exactly.")
