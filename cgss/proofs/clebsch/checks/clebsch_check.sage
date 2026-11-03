# Independent check of SE2 and SE3 (cgss/proofs/clebsch/clebsch.tex): the folded 5-cube, the Clebsch
# graph, the graph gq24 on the 27 lines and the Schlaefli graph, and the structure used in the
# proofs.
from itertools import combinations

def srg(X):
    p = X.is_strongly_regular(parameters=True)
    return p

def compl_params(n, k, a, c):
    return (n, n - k - 1, n - 2 - 2*k + c, n - 2*k + a)

# == the folded 5-cube on the even subsets of {0,...,4} ==
E5 = [frozenset(s) for r in (0, 2, 4) for s in combinations(range(5), r)]
F = Graph([E5, lambda s, t: len(s.symmetric_difference(t)) == 4], loops=False)
C = F.complement()
print("folded 5-cube: vertices", F.order(), "parameters", srg(F))
print("Clebsch (complement): parameters", srg(C))
assert srg(F) == (16, 5, 0, 2) and srg(C) == (16, 10, 6, 6)
assert compl_params(16, 5, 0, 2) == (16, 10, 6, 6)
assert compl_params(16, 10, 6, 6) == (16, 5, 0, 2)
# among even subsets, distinct vertices have |s ^ t| in {2, 4}, so C is the halved 5-cube
assert all(len(s.symmetric_difference(t)) in (2, 4) for s, t in combinations(E5, 2))
assert all(C.has_edge(s, t) == (len(s.symmetric_difference(t)) == 2) for s, t in combinations(E5, 2))
print("folded 5-cube isomorphic to graphs.ClebschGraph():", F.is_isomorphic(graphs.ClebschGraph()))
assert F.is_isomorphic(graphs.ClebschGraph())
assert srg(graphs.ClebschGraph()) == (16, 5, 0, 2)
# it is the 5-cube with antipodes identified
Q5 = graphs.CubeGraph(5)
rep = lambda x: min(x, ''.join('1' if b == '0' else '0' for b in x))
Fq = Graph([(rep(x), rep(y)) for x, y in Q5.edges(labels=False)])
print("folded 5-cube equals the antipodal quotient of Q_5:", Fq.is_isomorphic(F))
assert Fq.order() == 16 and Fq.is_isomorphic(F)
H5 = Graph([[v for v in Q5.vertices() if v.count('1') % 2 == 0],
            lambda x, y: sum(p != q for p, q in zip(x, y)) == 2], loops=False)
print("Clebsch equals the halved 5-cube:", H5.is_isomorphic(C))
assert H5.is_isomorphic(C)

# == the structure of Theorem SE2, at every vertex of Sage's ClebschGraph ==
X = graphs.ClebschGraph()
count = 0
for u in X.vertices():
    N = X.neighbors(u)
    R = [w for w in X.vertices() if w != u and w not in N]
    assert len(N) == 5 and len(R) == 10
    assert all(not X.has_edge(x, y) for x, y in combinations(N, 2))          # N(u) independent
    phi = {w: frozenset(x for x in N if X.has_edge(w, x)) for w in R}
    assert all(len(phi[w]) == 2 for w in R)                                   # c = 2
    assert len(set(phi.values())) == 10                                       # injective
    assert all(len([v for v in X.neighbors(w) if v in R]) == 3 for w in R)   # 3 neighbours in R
    assert all(X.has_edge(w, v) == phi[w].isdisjoint(phi[v])                  # disjointness
               for w, v in combinations(R, 2))
    # the isomorphism of the proof onto the even-subset model, for a labelling beta of N(u)
    beta = {x: i for i, x in enumerate(N)}
    f = {u: frozenset()}
    for x in N:
        f[x] = frozenset(range(5)) - {beta[x]}
    for w in R:
        f[w] = frozenset(beta[x] for x in phi[w])
    assert len(set(f.values())) == 16
    assert all(X.has_edge(p, q) == F.has_edge(f[p], f[q]) for p, q in combinations(X.vertices(), 2))
    count += 1
print("SE2 structure (N(u) independent, pairs, injectivity, disjointness, the isomorphism) holds at",
      count, "vertices")

# == the graph gq24 on the 27 lines, and the Schlaefli graph ==
# vertices ('a',i), ('b',i) for i in {0,...,5} and the 2-subsets of {0,...,5}
V27 = [('a', i) for i in range(6)] + [('b', i) for i in range(6)] + \
      [frozenset(s) for s in combinations(range(6), 2)]
def meet(p, q):
    if isinstance(p, tuple) and isinstance(q, tuple):
        return p[0] != q[0] and p[1] != q[1]
    if isinstance(p, tuple):
        return p[1] in q
    if isinstance(q, tuple):
        return q[1] in p
    return p.isdisjoint(q)
def skew(p, q):
    if isinstance(p, tuple) and isinstance(q, tuple):
        return (p[0] == q[0]) != (p[1] == q[1])
    if isinstance(p, tuple):
        return p[1] not in q
    if isinstance(q, tuple):
        return q[1] not in p
    return len(p & q) == 1
GQ = Graph([V27, lambda p, q: meet(p, q)], loops=False)
S = Graph([V27, lambda p, q: skew(p, q)], loops=False)
print("gq24: vertices", GQ.order(), "parameters", srg(GQ))
print("schlafli: parameters", srg(S))
assert srg(GQ) == (27, 10, 1, 5) and srg(S) == (27, 16, 10, 8)
assert S == GQ.complement()          # the two case lists describe complementary graphs
assert compl_params(27, 16, 10, 8) == (27, 10, 1, 5)
assert compl_params(27, 10, 1, 5) == (27, 16, 10, 8)
print("schlafli isomorphic to graphs.SchlaefliGraph():", S.is_isomorphic(graphs.SchlaefliGraph()))
assert S.is_isomorphic(graphs.SchlaefliGraph())
assert srg(graphs.SchlaefliGraph()) == (27, 16, 10, 8)

# the E8 coordinates of [BCN] 3.11 (ii): e_i+e_7, e_i+e_8, c-e_i-e_j, adjacent at inner product 1
def e(i):
    v = [0]*8; v[i] = 1; return vector(QQ, v)
c8 = vector(QQ, [1/2]*8)
vec = {}
for i in range(6):
    vec[('a', i)] = e(i) + e(6)
    vec[('b', i)] = e(i) + e(7)
for s in combinations(range(6), 2):
    vec[frozenset(s)] = c8 - e(s[0]) - e(s[1])
assert all(vec[p]*vec[p] == 2 for p in V27)
assert all((vec[p]*vec[q] == 1) == S.has_edge(p, q) and vec[p]*vec[q] in (0, 1)
           for p, q in combinations(V27, 2))
print("schlafli equals the graph of the E8 vectors e_i+e_7, e_i+e_8, c-e_i-e_j at inner product 1")

# the vectors of [CGSS] Example 4.6 (with c for the misprinted 1/3, errata Error 2):
# x_ij = e_i+e_j (i<j<=6), y_i = c-e_i-e_7, z_i = c-e_i-e_8; the correspondence
# a_i -> y_i, b_i -> z_i, c_ij -> x_ij is an isomorphism from the complement of Q onto their graph
cg = {}
for i in range(6):
    cg[('a', i)] = c8 - e(i) - e(6)
    cg[('b', i)] = c8 - e(i) - e(7)
for s in combinations(range(6), 2):
    cg[frozenset(s)] = e(s[0]) + e(s[1])
assert len(set(tuple(v) for v in cg.values())) == 27 and all(cg[p]*cg[p] == 2 for p in V27)
assert all(cg[p]*cg[q] in (0, 1) and (cg[p]*cg[q] == 1) == S.has_edge(p, q)
           for p, q in combinations(V27, 2))
# the two vector families have the same Gram matrix under the two labellings
assert all(cg[p]*cg[q] == vec[p]*vec[q] for p in V27 for q in V27)
print("the complement of Q is the graph of the [CGSS] Example 4.6 vectors under",
      "a_i -> c-e_i-e_7, b_i -> c-e_i-e_8, c_ij -> e_i+e_j")

# == m7: Mathlib's truncated complement formula, the table and the automorphisms of Lemma 4.2 ==
def tsub(x, y):
    return max(x - y, 0)
def compl_mathlib(n, k, l, mu):
    # SimpleGraph.IsSRGWith.compl: n (n - k - 1) (n - (2 * k - mu) - 2) (n - (2 * k - l))
    return (n, tsub(tsub(n, k), 1), tsub(tsub(n, tsub(2*k, mu)), 2), tsub(n, tsub(2*k, l)))
def untruncated(n, k, l, mu):
    return all(v >= 0 for v in (n - k, n - k - 1, 2*k - mu, n - (2*k - mu), n - (2*k - mu) - 2,
                                2*k - l, n - (2*k - l)))
for P in [(16, 5, 0, 2), (16, 10, 6, 6), (27, 16, 10, 8), (27, 10, 1, 5)]:
    assert compl_mathlib(*P) == compl_params(*P) and untruncated(*P)
print("Mathlib's truncated complement formula agrees with the integer one, untruncated, for",
      "(16,5,0,2), (16,10,6,6), (27,16,10,8), (27,10,1,5)")
A = lambda i: ('a', i - 1)
B = lambda i: ('b', i - 1)
Cc = lambda i, j: frozenset((i - 1, j - 1))
table = [((A(1), B(2)), {Cc(1, 2)}),
         ((A(1), Cc(1, 2)), {B(2)}),
         ((Cc(1, 2), Cc(3, 4)), {Cc(5, 6)}),
         ((A(1), A(2)), {B(3), B(4), B(5), B(6), Cc(1, 2)}),
         ((A(1), B(1)), {Cc(1, j) for j in range(2, 7)}),
         ((A(1), Cc(2, 3)), {B(2), B(3), Cc(1, 4), Cc(1, 5), Cc(1, 6)}),
         ((Cc(1, 2), Cc(1, 3)), {A(1), B(1), Cc(4, 5), Cc(4, 6), Cc(5, 6)})]
for (p, q), common in table:
    assert set(GQ.neighbors(p)) & set(GQ.neighbors(q)) == common
    assert GQ.has_edge(p, q) == (len(common) == 1)
assert set(GQ.neighbors(A(1))) == {B(j) for j in range(2, 7)} | {Cc(1, j) for j in range(2, 7)}
assert set(GQ.neighbors(Cc(1, 2))) == {A(1), A(2), B(1), B(2)} | \
    {Cc(k, l) for k, l in combinations(range(3, 7), 2)}
print("the table of Lemma 4.2 holds pair by pair")
def act(g, sw, p):
    if isinstance(p, tuple):
        side = p[0] if not sw else ('b' if p[0] == 'a' else 'a')
        return (side, g[p[1]])
    return frozenset(g[i] for i in p)
from itertools import permutations
maps = [(g, sw) for g in permutations(range(6)) for sw in (False, True)]
assert len(maps) == 1440
for g, sw in maps:
    assert all(GQ.has_edge(act(g, sw, p), act(g, sw, q)) == GQ.has_edge(p, q)
               for p, q in combinations(V27, 2))
def orbit_of(obj):
    if isinstance(obj, tuple) and len(obj) == 2 and not isinstance(obj[0], str):
        return {frozenset((act(g, sw, obj[0]), act(g, sw, obj[1]))) for g, sw in maps}
    return {act(g, sw, obj) for g, sw in maps}
vorb = [orbit_of(A(1)), orbit_of(Cc(1, 2))]
assert sum(len(o) for o in vorb) == 27 and set().union(*vorb) == set(V27)
edges = {frozenset(e) for e in GQ.edges(labels=False)}
nonedges = {frozenset((p, q)) for p, q in combinations(V27, 2) if not GQ.has_edge(p, q)}
eorb = [orbit_of(pq) for pq, _ in table[:3]]
norb = [orbit_of(pq) for pq, _ in table[3:]]
assert sum(len(o) for o in eorb) == len(edges) == 135 and set().union(*eorb) == edges
assert sum(len(o) for o in norb) == len(nonedges) == 216 and set().union(*norb) == nonedges
print("Sym(6) and the exchange a <-> b are automorphisms of Q; vertices, edges and nonadjacent",
      "pairs fall into 2, 3 and 4 orbits with the representatives of Lemma 4.2")

# == [CGSS] Example 4.8: the Clebsch graph of C9, and its certificate isomorphism ==
# e_i+e_5, e_i+e_6, c-e_i-e_7, c-e_i-e_8 for 1 <= i <= 4 (0-based: e(i), e(4), ..., e(7))
cl = {}
for i in range(4):
    cl[('x5', i + 1)] = e(i) + e(4)
    cl[('x6', i + 1)] = e(i) + e(5)
    cl[('y', i + 1)] = c8 - e(i) - e(6)
    cl[('z', i + 1)] = c8 - e(i) - e(7)
h = e(4) + e(5)
assert {tuple(v) for v in cl.values()} == {tuple(cg[p]) for p in V27 if cg[p]*h == 1}
Vcl = sorted(cl)
Ccl = Graph([Vcl, lambda p, q: cl[p]*cl[q] == 1], loops=False)
assert all(cl[p]*cl[q] in (0, 1) for p, q in combinations(Vcl, 2))
assert srg(Ccl) == (16, 10, 6, 6)
ok, cert = Ccl.is_isomorphic(C, certificate=True)
assert ok
assert all(Ccl.has_edge(p, q) == C.has_edge(cert[p], cert[q]) for p, q in combinations(Vcl, 2))
assert len(set(cert.values())) == 16
print("the graph of the [CGSS] Example 4.8 vectors is (16,10,6,6), the neighbours of e_5+e_6 in",
      "Example 4.6, and isomorphic to the complement of the folded 5-cube; the certificate of the",
      "note (vector -> even subset of {1,...,5}), checked in closed form:")
# the same certificate in closed form, as stated in Section 6 of the note (1-based labels):
# s_1 = {}, s_2 = {3,4}, s_3 = {3,5}, s_4 = {4,5}; e_i+e_5 -> s_i, e_i+e_6 -> s_i ^ {1,2},
# c-e_i-e_7 -> s_i ^ {1,3,4,5}, c-e_i-e_8 -> s_i ^ {2,3,4,5}
s1 = {1: frozenset(), 2: frozenset({3, 4}), 3: frozenset({3, 5}), 4: frozenset({4, 5})}
shift = {'x5': frozenset(), 'x6': frozenset({1, 2}), 'y': frozenset({1, 3, 4, 5}),
         'z': frozenset({2, 3, 4, 5})}
closed = {p: frozenset(i - 1 for i in s1[p[1]].symmetric_difference(shift[p[0]])) for p in Vcl}
assert len(set(closed.values())) == 16
assert all(Ccl.has_edge(p, q) == C.has_edge(closed[p], closed[q]) for p, q in combinations(Vcl, 2))
names = {'x5': 'e_%d+e_5', 'x6': 'e_%d+e_6', 'y': 'c-e_%d-e_7', 'z': 'c-e_%d-e_8'}
for p in Vcl:
    print("   ", names[p[0]] % p[1], "->", sorted(i + 1 for i in closed[p]))

# == the triangle property of the complement (SE3), on Sage's own Schlaefli graph ==
def has_triangle_property(Y):
    for x, y in Y.edges(labels=False):
        cn = set(Y.neighbors(x)) & set(Y.neighbors(y))
        if len(cn) != 1:
            return False
        z = cn.pop()
        for w in Y.vertices():
            if w not in (x, y, z) and sum(Y.has_edge(w, t) for t in (x, y, z)) != 1:
                return False
    return True
Yc = graphs.SchlaefliGraph().complement()
assert srg(Yc) == (27, 10, 1, 5)
print("complement of graphs.SchlaefliGraph() has the triangle property:", has_triangle_property(Yc))
assert has_triangle_property(Yc) and has_triangle_property(GQ)
# the counting of the proof: 3(k-2) = n-3 edges leave each triangle, for the three GQ(2,t)
for (n, k) in [(9, 4), (15, 6), (27, 10)]:
    assert 3*(k - 2) == n - 3 and n == 3*k - 3
# the lines of the quadrangle: 45 triangles, each vertex on 5
T = [t for t in combinations(GQ.vertices(), 3) if all(GQ.has_edge(p, q) for p, q in combinations(t, 2))]
assert len(T) == 45 and all(sum(p in t for t in T) == 5 for p in GQ.vertices())
print("gq24 has 45 triangles, 5 through each vertex; its automorphism group has order",
      GQ.automorphism_group().order())
assert GQ.automorphism_group().order() == 51840
print("All checks pass.")
