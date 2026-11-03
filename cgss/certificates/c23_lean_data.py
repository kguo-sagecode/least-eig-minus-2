"""C23: explicit data for LineGraphs/Computations/C23.lean ([CGSS], Example 5.13).

Prints the Lean tables: the 1-factorization of K_6 (k = 2), the isomorphisms of its
graph H with the pair graph of the (6,3,10,5,2) design and with the line graph of
`SimpleGraph.petersen`, the hyperoval design 2-(28,4,1) with its resolution (k = 4),
and the residual of the (37,9,2) biplane of quartic residues mod 37.
Requires Python 3 with NetworkX; run with python3 -I cgss/certificates/c23_lean_data.py.
"""
from itertools import combinations, product
import networkx as nx


def resolution_graph(blocks):
    """H: blocks (class, index) adjacent when disjoint and in different classes."""
    H = nx.Graph()
    H.add_nodes_from(blocks)
    for a, b in combinations(blocks, 2):
        if a[0] != b[0] and not set(blocks[a]) & set(blocks[b]):
            H.add_edge(a, b)
    return H


def check_design(v, blocks, k, lam):
    for B in blocks:
        assert len(set(B)) == k
    for p, q in combinations(range(v), 2):
        assert sum(1 for B in blocks if p in B and q in B) == lam


# k = 2: the 1-factorization GK_6 of K_6 (infinity = 5, factors i, i+-1, i+-2 mod 5).
factors = [[sorted((i, 5)), sorted(((i + 1) % 5, (i - 1) % 5)), sorted(((i + 2) % 5, (i - 2) % 5))]
           for i in range(5)]
blocks2 = {(i, j): factors[i][j] for i in range(5) for j in range(3)}
check_design(6, list(blocks2.values()), 2, 1)
H2 = resolution_graph(blocks2)
assert all(d == 4 for _, d in H2.degree())

# The (6,3,10,5,2) design of C15.
d1 = [{0, 1, 2}, {0, 1, 4}, {0, 2, 3}, {0, 3, 5}, {0, 4, 5},
      {1, 2, 5}, {1, 3, 4}, {1, 3, 5}, {2, 3, 4}, {2, 4, 5}]
check_design(6, [sorted(B) for B in d1], 3, 2)
pairs = [frozenset(s) for s in combinations(range(6), 2)]
P2 = nx.Graph()
P2.add_nodes_from(pairs)
for s, t in combinations(pairs, 2):
    if (s | t) in [frozenset(B) for B in d1]:
        P2.add_edge(s, t)
iso = nx.vf2pp_isomorphism(H2, P2)
assert iso is not None
print("-- k = 2 pair labels, block (i, j) to pair")
print([[sorted(iso[(i, j)]) for j in range(3)] for i in range(5)])

# SimpleGraph.petersen: doubled vectors, adjacent when the integer product is 4.
roots = [[0, 0, 0, 2, 0, 0, 0, 2], [-1, 1, 1, 1, -1, 1, 1, 1], [2, 0, 0, 0, 0, 2, 0, 0],
         [2, 0, 0, 0, 0, 0, 2, 0], [0, 2, 0, 0, 2, 0, 0, 0], [1, -1, 1, 1, 1, -1, 1, 1],
         [0, 2, 0, 0, 0, 0, 2, 0], [0, 0, 2, 0, 2, 0, 0, 0], [0, 0, 2, 0, 0, 2, 0, 0],
         [1, 1, -1, 1, 1, 1, -1, 1]]
Pet = nx.Graph()
Pet.add_nodes_from(range(10))
for i, j in combinations(range(10), 2):
    if sum(a * b for a, b in zip(roots[i], roots[j])) == 4:
        Pet.add_edge(i, j)
assert all(d == 3 for _, d in Pet.degree()) and Pet.number_of_edges() == 15
LPet = nx.line_graph(Pet)
iso = nx.vf2pp_isomorphism(H2, LPet)
assert iso is not None
print("-- k = 2 Petersen edge labels, block (i, j) to edge")
print([[tuple(sorted(iso[(i, j)])) for j in range(3)] for i in range(5)])

# k = 4: the dual of a hyperoval in PG(2,8); GF(8) = GF(2)[x]/(x^3+x+1).
def gmul(a, b):
    r = 0
    for i in range(3):
        if b >> i & 1:
            r ^= a << i
    for i in (4, 3):
        if r >> i & 1:
            r ^= 0b1011 << (i - 3)
    return r


def ginv(a):
    return next(x for x in range(1, 8) if gmul(a, x) == 1)


def canonical(p):
    a = next(x for x in p if x)
    ai = ginv(a)
    return tuple(gmul(x, ai) for x in p)


coords = sorted({canonical(p) for p in product(range(8), repeat=3) if any(p)})
assert len(coords) == 73


def incident(p, l):
    s = 0
    for a, b in zip(p, l):
        s ^= gmul(a, b)
    return s == 0


O = {canonical((1, t, gmul(t, t))) for t in range(8)} | {(0, 0, 1), (0, 1, 0)}
assert len(O) == 10
assert all(sum(incident(p, l) for p in O) in (0, 2) for l in coords)
external = [l for l in coords if not any(incident(p, l) for p in O)]
assert len(external) == 28
base = (0, 0, 1)
pencil = [l for l in coords if incident(base, l)]
assert len(pencil) == 9
classes = [[p for p in coords if p not in O and incident(p, l)] for l in pencil]
assert all(len(c) == 7 for c in classes)
blocks4 = {(i, j): [x for x, l in enumerate(external) if incident(classes[i][j], l)]
           for i in range(9) for j in range(7)}
check_design(28, list(blocks4.values()), 4, 1)
for i in range(9):
    assert sorted(x for j in range(7) for x in blocks4[(i, j)]) == list(range(28))
print("-- k = 4 resolution table, class i, block j")
print([[blocks4[(i, j)] for j in range(7)] for i in range(9)])

# The (37,9,2) biplane of quartic residues and its residual 2-(28,7,2) design.
D = sorted({pow(t, 4, 37) for t in range(1, 37)})
assert D == [1, 7, 9, 10, 12, 16, 26, 33, 34]
biplane = [sorted((a + t) % 37 for a in D) for t in range(37)]
removed = set(biplane[0])
remaining = sorted(set(range(37)) - removed)
residual = [[remaining.index(x) for x in B if x not in removed] for B in biplane[1:]]
check_design(28, residual, 7, 2)
print("-- residual blocks")
print(residual)
