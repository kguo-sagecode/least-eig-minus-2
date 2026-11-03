from common import *
begin("C2, C3: root counts and explicit model maps")

models = dict(E8_D=(*e8d(), 4), E8_A=(*e8a(), 9), E8_S=(*e8s(), 2))
for name, (labels, V, q) in models.items():
    assert len(V) == len(set(tuple(v) for v in V)) == 240
    assert len(representatives(V)) == 120
    assert all(v*v == 2*q for v in V)
    assert {tuple(-v) for v in V} == {tuple(v) for v in V}
    print("C2", name, ": 240 roots, 120 lines, rank", matrix(V).rank())

# Independent root-system construction, without a change of coordinate convention.
SageE8 = RootSystem(["E",8]).ambient_space()
sage_roots = [vector(QQ, r.to_vector()) for r in SageE8.roots()]
assert {tuple(2*v) for v in sage_roots} == {tuple(v) for v in models["E8_D"][1]}
counts = []
for typ, low in (("A",1),("D",3)):
    for rank in range(low,10):
        labels, V = an(rank) if typ == "A" else dn(rank)
        ambient = RootSystem([typ,rank]).ambient_space()
        roots = [vector(QQ,r.to_vector()) for r in ambient.roots()]
        assert {tuple(v) for v in V} == {tuple(v) for v in roots}
        expected = rank*(rank+1)//2 if typ == "A" else rank*(rank-1)
        assert len(V) == 2*expected
        counts.append([typ,rank,expected])
for rank, count in ((6,36),(7,63)):
    labels, V, parent = exceptional(rank)
    assert len(V) == 2*count and matrix(V).rank() == rank
    assert len(RootSystem(["E",rank]).ambient_space().roots()) == len(V)
    models["E%d" % rank] = (labels,V,4)
    print("C2 E%d: %d roots, %d lines" % (rank,len(V),count))

# The exact fixed Steiner labelling in Models.lean is the binary affine geometry.
fixed_blocks = [[0,1,2,3],[0,1,4,5],[0,1,6,7],[0,2,4,6],[0,2,5,7],[0,3,4,7],[0,3,5,6],
                [1,2,4,7],[1,2,5,6],[1,3,4,6],[1,3,5,7],[2,3,4,5],[2,3,6,7],[4,5,6,7]]
assert STEINER == fixed_blocks
from sage.combinat.designs.incidence_structures import IncidenceStructure
D = IncidenceStructure(8, STEINER)
AG = designs.AffineGeometryDesign(3,2,2,point_coordinates=False)
assert D.is_t_design(3,8,4,1) and D.is_isomorphic(AG)
SV = models["E8_S"][1]
S7 = [v for v in SV if v[7] == 0]
S6 = [v for v in S7 if sum(v[4:8]) == 0]
assert len(S7) == 126 and len(S6) == 72
assert sum(sum(a != 0 for a in v) == 1 for v in S7)//2 == 7
assert sum(sum(a != 0 for a in v) == 1 for v in S6)//2 == 4
parts6 = Counter(tuple(i for i,a in enumerate(v) if a) for v in S6 if sum(a != 0 for a in v) == 4)
assert sorted(parts6.values()) == [8]*6+[16]
print("C2 PASS: 36+84 = 56+64 = 8+8*14 = 120; Steiner cuts 7+8*7=63, 4+8+4*6=36; A1..A9, D3..D9 agree with Sage RootSystem")

# Similarities between *integer encodings*. They preserve normalized Gram matrices.
labelsD, VD, qD = models["E8_D"]
lookup = {tuple(v): i for i,v in enumerate(VD)}
T_SD = block_diagonal_matrix([matrix(QQ, [[1,1],[1,-1]])]*4)
assert T_SD*T_SD.transpose() == 2*identity_matrix(8)
pSD = [lookup[tuple(v*T_SD)] for v in SV]
assert sorted(pSD) == list(range(240))

VA = models["E8_A"][1]
BA = matrix(QQ, simple_roots(VA))
BD = matrix(QQ, [2*vector(QQ,r.to_vector()) for r in SageE8.simple_roots()])
GA, GD = BA*BA.transpose()/9, BD*BD.transpose()/4
ga, gd = matrix_graph(GA,-1), matrix_graph(GD,-1)
p = iso(ga,gd)
BD = matrix(QQ, [BD[p[i]] for i in range(8)])
assert BA*BA.transpose()/9 == BD*BD.transpose()/4
T_AD = BA.transpose()*(BA*BA.transpose()).inverse()*BD
assert T_AD*T_AD.transpose() == QQ(4)/9*(identity_matrix(9)-ones_matrix(9)/9)
pAD = [lookup[tuple(v*T_AD)] for v in VA]
assert sorted(pAD) == list(range(240))
assert matrix(VA)*T_AD == matrix([VD[i] for i in pAD])
assert matrix(SV)*T_SD == matrix([VD[i] for i in pSD])
print("C3 PASS: rational maps of all 240 encoded roots; A->D norm factor 4/9, Steiner->D norm factor 2")
print("C3 convention: on norm-sqrt(2) roots the Steiner isometry is T_SD/sqrt(2); the rational certificate uses the integer encodings.")

save("c02_models", ["C2"], models={name:dict(labels=labels,roots=rows(matrix(V)),q=q,
     line_representative_indices=representatives(V)) for name,(labels,V,q) in models.items()},
     classical_checked_counts=counts, classical_formulas=dict(A="n*(n+1)/2",D="n*(n-1)"),
     steiner_blocks=STEINER, steiner_E7_roots=rows(matrix(S7)), steiner_E6_roots=rows(matrix(S6)))
save("c03_maps", ["C3"], convention="row vectors: source * map = target[permutation]; source/target data in c02_models.json",
     maps=[dict(source="E8_A",target="E8_D",matrix=rows(T_AD),permutation=pAD,norm_factor=QQ(4)/9),
           dict(source="E8_S",target="E8_D",matrix=rows(T_SD),permutation=pSD,norm_factor=2)])
