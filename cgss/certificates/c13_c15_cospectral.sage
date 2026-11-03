from common import *
begin("C13, C15: exact spectra, switching, isomorphism and non-isomorphism certificates")
u = [unit(8,i) for i in range(8)]
pi = [1,2,3,0,7,4,5,6]
def orbit(v):
    out = []
    for z in range(4):
        out.append(v)
        v = vector(ZZ,[v[pi.index(i)] for i in range(8)])
    return out
V1 = sum([orbit(v) for v in [2*u[0],u[0]+u[1]+u[4]-u[5],u[0]+u[1]-u[4]+u[5]]],[])
V2 = sum([orbit(v) for v in [2*u[0],u[0]+u[1]+u[4]-u[5],u[0]+u[1]+u[6]-u[7]]],[])
steiner = {tuple(v):i for i,v in enumerate(e8s()[1])}
assert all(tuple(v) in steiner and sum(v[4:8]) == 0 for v in V1+V2)
# Carry the paper's E7 section of the Steiner model into the fixed Lean E7.
T_SD = block_diagonal_matrix([matrix(QQ,[[1,1],[1,-1]])]*4)
coordinate_permutation = [0,1,2,3,6,4,7,5]
Q = matrix(QQ,8,8,lambda i,j: (-1 if j in (0,7) else 1) if j == coordinate_permutation[i] else 0)
T = T_SD*Q
leanE7 = {tuple(v):i for i,v in enumerate(exceptional(7)[1])}
lean_indices = [[leanE7[tuple(v*T)] for v in V] for V in (V1,V2)]
assert T*T.transpose() == 2*identity_matrix(8)
G1,G2 = root_graph(V1,2),root_graph(V2,2)
flags,F432 = flag_graph(4,list(combinations(range(4),3)))
p = iso(G1,F432)
assert not G1.is_isomorphic(G2)
sw = switching_iso(G1,G2)
specs = []
for G in (G1,G2):
    A = adjacency(G)
    S = 2*A-ones_matrix(12)+identity_matrix(12) # paper's sign, opposite common Sage convention
    specs.append(dict(adjacency=spectral(A,[(4,1),(2,3),(0,3),(-2,5)]),
                      paper_Seidel=spectral(S,[(5,3),(1,3),(-3,6)])))
invariants = [dict(four_cliques=clique_count(G,4),claws=claws(G)) for G in (G1,G2)]
assert [(z["four_cliques"],len(z["claws"])) for z in invariants][0] != [(z["four_cliques"],len(z["claws"])) for z in invariants][1]
print("C13 PASS: adjacency spectra 4^1,2^3,0^3,(-2)^5; paper Seidel spectra 5^3,1^3,(-3)^6; switching equivalence; non-isomorphism")
print("C13 invariants (4-cliques, induced claws):",[(z["four_cliques"],len(z["claws"])) for z in invariants])
save("c13",["C13"],roots=[rows(matrix(V1)),rows(matrix(V2))],q=2,
    steiner_indices=[[steiner[tuple(v)] for v in V] for V in (V1,V2)],graphs=[graph_data(G1),graph_data(G2)],
    spectra=specs,switching_isomorphism=sw,nonisomorphism_invariants=invariants,
    design_blocks=list(combinations(range(4),3)),flag_labels=flags,flag_graph=graph_data(F432),flag_isomorphism=p,
    Seidel_convention="2A-J+I",map_to_Lean_E7=rows(T),Lean_E7_indices=lean_indices)

blocks = design632()
flags,F632 = flag_graph(6,blocks)
LLP = integer_graph(graphs.PetersenGraph().line_graph().line_graph())
A1,A2 = adjacency(F632),adjacency(LLP)
assert A1.charpoly() == A2.charpoly()
assert not F632.is_isomorphic(LLP)
spectrum = [(6,1),(4,5),(1,4),(0,5),(-2,15)]
certs = [spectral(A,spectrum) for A in (A1,A2)]
counts = [clique_count(G,4) for G in (F632,LLP)]
assert counts == [30,15]
assert certs[0]["traces"] == certs[1]["traces"]
print("C15 PASS: both spectra 6^1,4^5,1^4,0^5,(-2)^15; 4-clique counts 30 versus 15 distinguish the graphs")
save("c15",["C15"],design=design_check(6,blocks,3,2),flag_labels=flags,
    graphs=[graph_data(F632),graph_data(LLP)],spectra=certs,four_clique_counts=counts)
