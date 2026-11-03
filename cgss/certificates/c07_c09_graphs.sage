from common import *
begin("C7, C9: the 36-vector example and the seven sporadic graphs")

u = [unit(9,i) for i in range(9)]
V36 = [3*(u[i]-u[8]) for i in range(8)] + [vector(ZZ,[1]*9)-3*(u[8]+u[i]+u[j]) for i,j in combinations(range(8),2)]
G36 = root_graph(V36,9)
assert G36.order() == 36 and G36.subgraph(range(8)).is_clique()
T8 = integer_graph(graphs.CompleteGraph(8).line_graph())
part28 = G36.subgraph(range(8,36)).relabel({i:i-8 for i in range(8,36)},inplace=False)
p28 = iso(part28,T8)
degrees = Counter(G36.degree())
assert degrees == {28:8,18:28}
print("C7 PASS: K8 and T(8) induced subgraphs; degree distribution",dict(degrees))
save("c07",["C7"],roots=rows(matrix(V36)),q=9,graph=graph_data(G36),T8_target=graph_data(T8),
     T8_permutation=p28,degrees=G36.degree(),spectrum=spectral(adjacency(G36),[(21,1),(5,7),(-2,28)]))

u = [unit(8,i) for i in range(8)]
c = vector(ZZ,[1]*8)  # doubled apex
E,T,chang,sets = chang_graphs()
root_index = {tuple(v):i for i,v in enumerate(e8d()[1])}
data = {}
for z,H in enumerate(chang):
    V = [c-2*(u[i]+u[j]) if h in sets[z] else 2*(u[i]+u[j]) for h,(i,j) in enumerate(E)]
    assert adjacency(root_graph(V,4)) == adjacency(H)
    name = ["Chang I","Chang II","Chang III"][z]
    data[name] = dict(graph=graph_data(H),parameters=srg(H,[28,12,6,4]),
        roots=rows(matrix(V)),E8_indices=[root_index[tuple(v)] for v in V],switch_subset=sets[z],
        spectrum=spectral(adjacency(H),[(12,1),(4,7),(-2,20)]),
        four_cliques=clique_count(H,4),five_cliques=clique_count(H,5),claw_count=len(claws(H)))
    print("C9",name,"parameters",data[name]["parameters"],"4/5-cliques",data[name]["four_cliques"],data[name]["five_cliques"])
assert all(not chang[i].is_isomorphic(chang[j]) for i,j in combinations(range(3),2))

VS = [2*(u[i]+u[j]) for i,j in combinations(range(6),2)]
VS += [c-2*(u[i]+u[j]) for j in (6,7) for i in range(6)]
VC = [2*(u[i]+u[j]) for j in (4,5) for i in range(4)]
VC += [c-2*(u[i]+u[j]) for j in (6,7) for i in range(4)]
cross = [(i,j) for i in range(4) for j in range(4,8)]
VR = [c-2*(u[i]+u[j]) if j == i+4 else 2*(u[i]+u[j]) for i,j in cross]
pairsP = [(3,7)]+[(i,j) for i in range(3) for j in range(4,7)]
VP = [c-2*(u[i]+u[j]) if j == i+4 and i < 3 else 2*(u[i]+u[j]) for i,j in pairsP]
S,R,C,P = [root_graph(V,4) for V in (VS,VR,VC,VP)]
for name,V,G,target,params in [
    ("Schlaefli",VS,S,graphs.SchlaefliGraph(),[27,16,10,8]),
    ("Shrikhande",VR,R,graphs.ShrikhandeGraph(),[16,6,2,2]),
    ("Clebsch",VC,C,graphs.ClebschGraph().complement(),[16,10,6,6]),
    ("Petersen",VP,P,graphs.PetersenGraph(),[10,3,0,1])]:
    target = integer_graph(target)
    params = srg(G,params)
    theta = params[2]-params[3]+2
    mult = (2*params[0]-params[1]-2)//(theta+2)
    data[name] = dict(roots=rows(matrix(V)),E8_indices=[root_index[tuple(v)] for v in V],
        graph=graph_data(G),parameters=params,target=graph_data(target),isomorphism=iso(G,target),
        spectrum=spectral(adjacency(G),[(params[1],1),(theta,mult),(-2,params[0]-mult-1)]))
    print("C9",name,"PASS:",params,"and Sage named-graph isomorphism")

shr_in_chang = [E.index(pair) for pair in cross]
assert adjacency(R) == adjacency(chang[0].subgraph(shr_in_chang).relabel({v:i for i,v in enumerate(shr_in_chang)},inplace=False))
cleb_in_schl = [next(i for i,w in enumerate(VS) if w == v) for v in VC]
centre = next(i for i,w in enumerate(VS) if w == 2*(u[4]+u[5]))
assert set(cleb_in_schl) == set(S.neighbors(centre))
assert all(S.has_edge(cleb_in_schl[i],cleb_in_schl[j]) == C.has_edge(i,j) for i,j in combinations(range(16),2))
L44 = integer_graph(graphs.CompleteBipartiteGraph(4,4).line_graph())
relations = dict(Shrikhande_in_ChangI=shr_in_chang,Clebsch_in_Schlaefli=cleb_in_schl,
    Schlaefli_neighbourhood_centre=centre,L44=graph_data(L44),
    Clebsch_to_L44=switching_iso(C,L44),Clebsch_to_Shrikhande=switching_iso(C,R))
bad = vector(QQ,[QQ(1)/3]*8)-u[0]-u[6]
assert bad*bad == QQ(14)/9
print("C9 PASS: subgraph and switching relations; printed Schlaefli 1/3 gives norm^2=14/9, corrected 1/2 gives norm^2=2")
save("c09",["C9"],graphs=data,triangular_base=graph_data(T),relations=relations,
    printed_Schlaefli_norm_squared=bad*bad)
