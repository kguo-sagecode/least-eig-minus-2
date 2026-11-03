from common import *
begin("C22: complete finite regular-switching checks")

E8,T8,CG,Y8 = chang_graphs()
targets = [("T8",T8),("Chang I",CG[0]),("Chang II",CG[1]),("Chang III",CG[2])]
invariants = {}
for name,G in targets:
    local4 = local_clique_counts(G,4)
    cp = G.clique_polynomial()
    invariants[name] = dict(four_cliques=clique_count(G,4),five_cliques=clique_count(G,5),claws=len(claws(G)),
        four_cliques_through_vertex=local4,local_four_clique_histogram=sorted(Counter(local4).items()),
        clique_polynomial_coefficients=cp.list())
    assert cp[4] == invariants[name]["four_cliques"] and cp[5] == invariants[name]["five_cliques"]
assert invariants["Chang II"]["four_cliques"] == invariants["Chang III"]["four_cliques"] == 240
assert invariants["Chang II"]["five_cliques"] == invariants["Chang III"]["five_cliques"] == 48
assert len({tuple(sorted(z["four_cliques_through_vertex"])) for z in invariants.values()}) == 4
cases8 = []
for d in range(4):
    for H in graphs.nauty_geng("8 -d%d -D%d" % (d,d)):
        H = integer_graph(H)
        subset = [E8.index(tuple(sorted(e))) for e in H.edges(labels=False)]
        G = switching(T8,subset)
        assert srg(G) == [28,12,6,4]
        matches = [(name,target) for name,target in targets if G.is_isomorphic(target)]
        assert len(matches) == 1
        name,target = matches[0]
        cases8.append(dict(switch_graph=graph_data(H),degree=d,switch_subset=subset,
            switched=graph_data(G),target=name,permutation=iso(G,target)))
assert len(cases8) == 11
assert Counter(z["target"] for z in cases8) == {"T8":2,"Chang I":4,"Chang II":3,"Chang III":2}
print("C22 E8 PASS: 11 unlabelled regular graphs of degree 0..3; output class counts",dict(Counter(z["target"] for z in cases8)))
print("C22 target (4-cliques,5-cliques,claws):",{name:[z[key] for key in ("four_cliques","five_cliques","claws")] for name,z in invariants.items()})
print("C22 DISAGREEMENT: global 4/5-clique totals coincide for Chang II and III (240,48).")
print("C22 replacement invariant, counts of 4-cliques through each vertex:",{name:z["local_four_clique_histogram"] for name,z in invariants.items()})

def low_rank_case(n,isolated,target_degree):
    E = list(combinations(range(n),2))
    size = len(E)+int(isolated)
    base = Graph(size)
    base.add_edges((i,j) for i,j in combinations(range(len(E)),2) if set(E[i]) & set(E[j]))
    survivors = []
    examined = 0
    for mask in range(2**len(E)):
        subset = [i for i in range(len(E)) if int(mask) & (1 << int(i))]
        m = len(subset)
        hd = [0]*n
        for i in subset:
            for v in E[i]:
                hd[v] += 1
        degrees = []
        for i,(u,v) in enumerate(E):
            degree0 = 2*(n-2)
            if int(mask) & (1 << int(i)):
                local = hd[u]+hd[v]-2
                degrees.append(degree0-2*(degree0-local)+size-m)
            else:
                degrees.append(degree0-2*(hd[u]+hd[v])+m)
        if isolated:
            degrees.append(m)
        regular = all(d == target_degree for d in degrees)
        # Finite verification of the hand reduction to a cycle or 2-regular H.
        criterion = all(d == 2 for d in hd)
        assert regular == criterion
        examined += 1
        if regular:
            G = switching(base,subset)
            assert set(G.degree()) == {target_degree}
            survivors.append((subset,G))
    return base,survivors,examined

T5,cases5,count5 = low_rank_case(5,False,3)
assert len(cases5) == 12
P = integer_graph(graphs.PetersenGraph())
out5 = [dict(subset=S,permutation=iso(G,P)) for S,G in cases5]
T6iso,cases6,count6 = low_rank_case(6,True,6)
assert len(cases6) == 70
Shr = integer_graph(graphs.ShrikhandeGraph())
L44 = integer_graph(graphs.CompleteBipartiteGraph(4,4).line_graph())
out6 = []
for S,G in cases6:
    name,target = ("Shrikhande",Shr) if G.is_isomorphic(Shr) else ("L44",L44)
    out6.append(dict(subset=S,target=name,permutation=iso(G,target)))
assert Counter(z["target"] for z in out6) == {"Shrikhande":60,"L44":10}
assert len(claws(Shr)) > 0 and len(claws(L44)) == 0
print("C22 E6 PASS:",count5,"switches, 12 regular, all Petersen")
print("C22 E7 PASS:",count6,"switches fixing isolated vertex, 70 regular: 60 Shrikhande and 10 L(K4,4)")
save("c22",["C22"],E8=dict(edge_labels=E8,base=graph_data(T8),cases=cases8,
    targets={name:graph_data(G) for name,G in targets},invariants=invariants,
    scope="All unlabelled regular H on 8 vertices of degree <=3 from nauty geng; complements cover degree >=4"),
    E6=dict(base=graph_data(T5),examined=count5,regular_switches=out5,target=graph_data(P)),
    E7=dict(base=graph_data(T6iso),examined=count6,regular_switches=out6,
            targets=dict(Shrikhande=graph_data(Shr),L44=graph_data(L44)),
            Shrikhande_claw_witness=claws(Shr)[0],L44_claw_count=0))
