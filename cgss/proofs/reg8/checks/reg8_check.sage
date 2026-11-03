# Independent check of SE4 (cgss/proofs/reg8/reg8.tex): the regular graphs of valency
# at most 3 on 8 vertices, their invariants, and the case analysis of the proof.
from itertools import combinations

def tri(X):
    return sum(1 for T in combinations(X.vertices(), 3)
               if X.has_edge(T[0],T[1]) and X.has_edge(T[0],T[2]) and X.has_edge(T[1],T[2]))

def quad(X):
    # number of 4-cycles = (1/2) sum over unordered pairs {u,w} of C(c(u,w),2),
    # where c(u,w) is the number of common neighbours
    s = sum(binomial(len(set(X.neighbors(u)) & set(X.neighbors(w))), 2)
            for u, w in combinations(X.vertices(), 2))
    assert s % 2 == 0
    return s // 2

def inv(X):
    return dict(triangles=tri(X), fourcycles=quad(X), connected=X.is_connected(),
                bipartite=X.is_bipartite(), girth=X.girth(), aut=X.automorphism_group().order(),
                diameter=X.diameter() if X.is_connected() else Infinity)

def eightcycle_plus(chords):
    # the 8-cycle 0-1-...-7-0 together with the given chords
    X = graphs.CycleGraph(8)
    X.add_edges(chords)
    return X

# ---- the named graphs, as defined in reg8.tex --------------------------------
named = {}
named['empty'] = Graph(8)
named['4K2'] = Graph([(0,1),(2,3),(4,5),(6,7)])
named['C8'] = graphs.CycleGraph(8)
named['C3+C5'] = Graph([(0,1),(1,2),(2,0),(3,4),(4,5),(5,6),(6,7),(7,3)])
named['2C4'] = Graph([(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7),(7,4)])
named['2K4'] = Graph([(i,j) for i,j in combinations(range(4),2)] + [(i,j) for i,j in combinations(range(4,8),2)])
# the uniform descriptions: C8 plus a perfect matching of chords
named['cube Q3'] = eightcycle_plus([(0,3),(1,6),(2,5),(4,7)])
named['Wagner M8'] = eightcycle_plus([(0,4),(1,5),(2,6),(3,7)])
named['truncated K33'] = eightcycle_plus([(0,2),(1,5),(3,6),(4,7)])
named['truncated K4 (two vertices)'] = eightcycle_plus([(0,2),(1,5),(3,7),(4,6)])
named['two diamonds'] = eightcycle_plus([(0,2),(1,3),(4,6),(5,7)])

# ---- the same graphs by their constructions ---------------------------------
Q3 = graphs.CubeGraph(3)
W8 = Graph([(i,(i+1)%8) for i in range(8)] + [(i,i+4) for i in range(4)])
def truncate(X, x):
    # replace the vertex x of a cubic graph X by a triangle
    Y = X.copy(); nb = X.neighbors(x); Y.delete_vertex(x)
    new = [(x,k) for k in range(3)]
    Y.add_edges([(new[0],new[1]),(new[1],new[2]),(new[0],new[2])])
    for k in range(3): Y.add_edge(new[k], nb[k])
    return Y
K33t = truncate(graphs.CompleteBipartiteGraph(3,3), 0)
K4tt = truncate(truncate(graphs.CompleteGraph(4), 0), 1)
D = Graph([('v','a'),('v','b'),('v','c'),('a','b'),('b','c'),
           ('w3','w1'),('w3','w2'),('w3','w4'),('w4','w1'),('w4','w2'),
           ('a','w1'),('c','w2')])
print("construction checks:",
      named['cube Q3'].is_isomorphic(Q3), named['Wagner M8'].is_isomorphic(W8),
      named['truncated K33'].is_isomorphic(K33t), named['truncated K4 (two vertices)'].is_isomorphic(K4tt),
      named['two diamonds'].is_isomorphic(D))

# ---- nauty_geng: all regular graphs of valency 0..3 on 8 vertices -----------
for k in range(4):
    L = list(graphs.nauty_geng("8 -d%d -D%d" % (k,k)))
    mine = [nm for nm,X in named.items() if all(X.degree(u)==k for u in X)]
    assert all(named[nm].order()==8 for nm in mine)
    matched = []
    for X in L:
        hits = [nm for nm in mine if X.is_isomorphic(named[nm])]
        assert len(hits) == 1, hits
        matched.append(hits[0])
    print("valency %d: geng gives %d graphs; named: %s; bijective: %s"
          % (k, len(L), mine, sorted(matched)==sorted(mine)))
    for nm in mine:
        print("   %-28s %s" % (nm, inv(named[nm])))
    pairs = [(inv(named[nm])['triangles'], inv(named[nm])['fourcycles']) for nm in mine]
    print("   (triangles, 4-cycles) pairwise distinct:", len(set(pairs)) == len(pairs))

# ---- the case analysis of Section 4 -----------------------------------------
# e(v) = number of edges in the neighbourhood of v; m = max_v e(v);
# for v with e(v)=m, the graph induced on the four non-neighbours R.
print("case analysis (m, shape of R for each v with e(v)=m):")
for X in graphs.nauty_geng("8 -d3 -D3"):
    nm = [n for n in named if X.is_isomorphic(named[n])][0]
    e = {v: X.subgraph(X.neighbors(v)).size() for v in X}
    m = max(e.values())
    shapes = set()
    for v in X:
        if e[v] == m:
            R = [u for u in X if u != v and not X.has_edge(u,v)]
            H = X.subgraph(R)
            for sh, S in [('K4',graphs.CompleteGraph(4)),('K4-e',graphs.CompleteGraph(4).copy()),
                          ('C4',graphs.CycleGraph(4)),('paw',Graph([(0,1),(1,2),(2,0),(2,3)])),
                          ('P4',graphs.PathGraph(4)),('K13',graphs.StarGraph(3))]:
                if sh == 'K4-e': S.delete_edge(0,1)
                if H.is_isomorphic(S): shapes.add(sh)
            # in case m=1, record also whether c's two R-neighbours are adjacent
            if m == 1 and H.is_isomorphic(graphs.CycleGraph(4)):
                N = X.neighbors(v)
                c = [x for x in N if all(not X.has_edge(x,y) for y in N)][0]
                cr = [u for u in X.neighbors(c) if u in R]
                shapes.add('C4, c-neighbours ' + ('adjacent' if X.has_edge(cr[0],cr[1]) else 'opposite'))
    print("   %-28s m=%d  %s" % (nm, m, sorted(shapes)))

# ---- the explicit isomorphisms of Section 4 ----------------------------------
# Each case of the proof produces a graph on v,a,b,c,w1,...,w4; the listed
# Hamiltonian cycle x0,...,x7 must map x_i to i and be an isomorphism onto the model.
base = [('v','a'),('v','b'),('v','c')]
cases = [
 ('two diamonds', 'm=2',
  base + [('a','b'),('b','c'),('w1','w3'),('w1','w4'),('w2','w3'),('w2','w4'),('w3','w4'),('a','w1'),('c','w2')],
  ['c','v','b','a','w1','w3','w4','w2']),
 ('truncated K4 (two vertices)', 'm=1, paw',
  base + [('a','b'),('w1','w2'),('w2','w3'),('w1','w3'),('w3','w4'),('c','w4'),('a','w4'),('b','w2'),('c','w1')],
  ['v','b','a','w4','w3','w2','w1','c']),
 ('truncated K4 (two vertices)', 'm=1, C4, adjacent',
  base + [('a','b'),('w1','w2'),('w2','w3'),('w3','w4'),('w4','w1'),('c','w1'),('c','w2'),('a','w4'),('b','w3')],
  ['b','v','a','w4','w1','c','w2','w3']),
 ('truncated K33', 'm=1, C4, opposite',
  base + [('a','b'),('w1','w2'),('w2','w3'),('w3','w4'),('w4','w1'),('c','w1'),('c','w3'),('a','w2'),('b','w4')],
  ['a','v','b','w4','w1','c','w3','w2']),
 ('cube Q3', 'm=0, K13',
  base + [('w4','w1'),('w4','w2'),('w4','w3'),('a','w2'),('a','w3'),('b','w1'),('b','w3'),('c','w1'),('c','w2')],
  ['v','a','w2','c','w1','w4','w3','b']),
 ('Wagner M8', 'm=0, P4',
  base + [('w1','w2'),('w2','w3'),('w3','w4'),('w1','a'),('w1','b'),('w2','c'),('w4','c'),('w4','a'),('w3','b')],
  ['v','c','w2','w1','a','w4','w3','b']),
]
print("explicit isomorphisms:")
for nm, case, E, order in cases:
    Y = Graph(E)
    pos = {x: i for i, x in enumerate(order)}
    img = Graph([(pos[x], pos[y]) for x, y in E])
    ok = (Y.order() == 8 and Y.size() == 12 and all(Y.degree(u) == 3 for u in Y)
          and len(pos) == 8 and set(img.edges(labels=False)) == set(named[nm].edges(labels=False)))
    print("   %-18s -> %-28s %s" % (case, nm, ok))
