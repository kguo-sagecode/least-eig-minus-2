from common import *
begin("C10: generalized line graph valencies")

def check_graph(Y, weights):
    m = Y.order()
    edges = sorted(tuple(sorted(e)) for e in Y.edges(labels=False))
    labels = [["edge",i,j] for i,j in edges]
    dim = m+sum(weights)
    V = [unit(dim,i)+unit(dim,j) for i,j in edges]
    H = Graph(len(edges))
    H.add_edges((i,j) for i,j in combinations(range(len(edges)),2) if set(edges[i]) & set(edges[j]))
    assert H.is_isomorphic(Y.line_graph())
    offset = m
    for i,a in enumerate(weights):
        start = len(V)
        for j in range(a):
            for sign in (1,-1):
                labels.append(["cocktail",i,j,sign])
                V.append(unit(dim,i)+sign*unit(dim,offset+j))
        H.add_vertices(range(start,len(V)))
        CP = Graph(0) if a == 0 else integer_graph(graphs.CompleteMultipartiteGraph([2]*a))
        H.add_edges((start+p,start+q) for p,q in CP.edges(labels=False))
        H.add_edges((h,z) for h,e in enumerate(edges) if i in e for z in range(start,len(V)))
        offset += a
    if V:
        assert adjacency(H) == adjacency(root_graph(V))
    for z,label in enumerate(labels):
        if label[0] == "edge":
            i,j = label[1:]
            expected = 2*(weights[i]+weights[j])+Y.degree(i)+Y.degree(j)-2
        else:
            i = label[1]
            expected = 2*(weights[i]-1)+Y.degree(i)
        assert H.degree(z) == expected
    return dict(base=graph_data(Y),weights=weights,labels=labels,graph=graph_data(H),
                roots=rows(matrix(ZZ,V)) if V else [],degrees=H.degree())

count = 0
for m in range(1,5):
    for Y in graphs.nauty_geng(str(m)):
        Y = integer_graph(Y)
        for weights in product(range(3),repeat=m):
            check_graph(Y,list(weights))
            count += 1
sample = check_graph(integer_graph(graphs.PathGraph(4)),[0,1,2,1])
# Symbolic disjoint-neighbour counts, including the possibility a_i=0.
R = PolynomialRing(ZZ,names=("ai","aj","vi","vj"))
ai,aj,vi,vj = R.gens()
edge_degree = (vi-1)+(vj-1)+2*ai+2*aj
cp_degree = (2*ai-2)+vi
assert edge_degree == 2*(ai+aj)+vi+vj-2
assert cp_degree == 2*(ai-1)+vi
print("C10 PASS: symbolic counts and",count,"base-graph/weight cases, all unlabelled graphs on 1..4 vertices, weights 0..2")
save("c10",["C10"],exhaustive_cases=count,scope=dict(base_vertices=[1,4],weights=[0,2]),
    formula_variables=list(R.variable_names()),edge_degree_terms=[[list(e),a] for e,a in edge_degree.dict().items()],
    cocktail_degree_terms=[[list(e),a] for e,a in cp_degree.dict().items()],sample=sample)
