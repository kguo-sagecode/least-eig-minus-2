from common import *
begin("C4, C5, C6: closure, Gamma graphs, embeddings, tight frames")

systems = [("E%d" % n,exceptional(n)[1],4,n) for n in (6,7,8)]
systems += [("E8_A",e8a()[1],9,8),("E8_S",e8s()[1],2,8)]
systems += [("A%d" % n,an(n)[1],1,n) for n in range(1,10)]
systems += [("D%d" % n,dn(n)[1],1,n) for n in range(3,10)]
structure, frames = {}, {}
for name,V,q,rank in systems:
    mat = matrix(ZZ,V)
    G = mat*mat.transpose()
    assert set(G.list()) <= {-2*q,-q,0,q,2*q}
    lookup = {tuple(v):i for i,v in enumerate(V)}
    closure = []
    for i,j in combinations(range(len(V)),2):
        if G[i,j] == -q:
            assert tuple(V[i]+V[j]) in lookup
            closure.append([i,j,lookup[tuple(V[i]+V[j])]])
    ids = representatives(V)
    line_graph = Graph(len(ids))
    line_graph.add_edges((i,j) for i,j in combinations(range(len(ids)),2) if G[ids[i],ids[j]] != 0)
    assert line_graph.is_connected()
    data = dict(root_count=len(V),line_count=len(ids),q=q,
                nonorthogonality_spanning_tree=[list(e) for e in line_graph.min_spanning_tree()],
                line_representative_indices=ids,star_sum_indices=closure)
    if rank >= 2:
        i,j = next((i,j) for i,j in combinations(range(len(V)),2) if G[i,j] == -q)
        gamma = [t for t in range(len(V)) if G[t,i] == 0 and G[t,j] == q]
        delta = [t for t in range(len(V)) if G[t,i] == 0 and G[t,j] == 0]
        H = matrix_graph(G.matrix_from_rows_and_columns(gamma,gamma),0)
        assert len(ids) == 3+3*len(gamma)+len(delta)//2
        data.update(star=[i,j,lookup[tuple(-V[i]-V[j])]],gamma=gamma,delta=delta,
                    gamma_graph=graph_data(H),delta_lines=len(delta)//2)
        if name in ("E6","E7","E8","E8_A","E8_S"):
            kind = "E%d" % rank
            expected = {"E6":(9,6),"E7":(15,15),"E8":(27,36)}[kind]
            assert (len(gamma),len(delta)//2) == expected
            target = {"E6":lambda: graphs.CompleteBipartiteGraph(3,3).line_graph(),
                      "E7":lambda: graphs.CompleteGraph(6).line_graph().complement(),
                      "E8":lambda: graphs.SchlaefliGraph().complement()}[kind]()
            target = integer_graph(target)
            data.update(target=graph_data(target),isomorphism=iso(H,target),parameters=srg(H))
            print("C4",name,"Gamma/Delta-lines",expected,"Gamma parameters",srg(H))
        elif name.startswith("A"):
            assert H.order() == rank-2 and H.size() == 0
        elif name.startswith("D"):
            assert H.order() == 2*(rank-3)+1
            assert H.is_isomorphic(graphs.FriendshipGraph(rank-3)) if rank > 3 else H.order() == 1
    structure[name] = data

    # The ambient-coordinate identity is F=(2N/rank)*P_span, not a full identity
    # matrix when the roots lie in a proper subspace (A_n, E6, E7, E8_A).
    W = matrix(QQ,[V[i] for i in ids])
    B = W.row_space().basis_matrix()
    P = B.transpose()*(B*B.transpose()).inverse()*B
    factor = QQ(2*len(ids))/rank
    frame = W.transpose()*W/q
    assert P*P == P and P.rank() == rank
    assert frame == factor*P
    theta = factor-2
    C = W*W.transpose()/q - 2*identity_matrix(len(ids))
    spec = spectral(C,[(theta,rank),(-2,len(ids)-rank)])
    frames[name] = dict(q=q,rank=rank,roots=rows(mat),line_representative_indices=ids,
        projector=rows(P),frame=rows(frame),frame_factor=factor,theta=theta,spectrum=spec)
print("C4 PASS: all three E8 models and E6/E7 star-closed and indecomposable; A1..A9 and D3..D9 checked")

# C5: A8 and D8 are literal subfamilies of their defining E8 models.
LD,VD = e8d()
LA,VA = e8a()
assert [3*v for v in an(8)[1]] == VA[:72]
assert [2*v for v in dn(8)[1]] == VD[:112]

# Weyl reflections move the normal c to e6-e7, sending the A7 subsystem to E7.
c = vector(QQ,[QQ(1)/2]*8)
t = unit(8,0)+unit(8,6)
normal = unit(8,6)-unit(8,7)
def reflection(r):
    return identity_matrix(QQ,8)-2*matrix(QQ,8,1,r)*matrix(QQ,1,8,r)/(r*r)
T = reflection(c-t)*reflection(t-normal)
assert T*T.transpose() == identity_matrix(8) and c*T == normal
AV = matrix(QQ,an(7)[1])
images = 2*AV*T
E7 = exceptional(7)[1]
lookup7 = {tuple(v):i for i,v in enumerate(E7)}
embedding = [lookup7[tuple(v)] for v in images.rows()]
assert len(set(embedding)) == 56
L33 = integer_graph(graphs.CompleteBipartiteGraph(3,3).line_graph())
T6 = integer_graph(graphs.CompleteGraph(6).line_graph())
assert len(L33.independent_set()) == 3
assert clique_count(L33.complement(),4) == 0
assert len(T6.independent_set()) == 3 and T6.clique_number() == 5
valencies = []
for n in (6,7):
    DG = structure["D%d" % n]["gamma_graph"]["adjacency"]
    EG = structure["E%d" % n]["gamma_graph"]["adjacency"]
    md,me = max(sum(r) for r in DG),max(sum(r) for r in EG)
    assert md > me
    valencies.append([n,md,me])
classical_obstructions = []
for n in range(4,10):
    DG = matrix_graph(matrix(ZZ,structure["D%d" % n]["gamma_graph"]["adjacency"]))
    independent = sorted(DG.independent_set())
    assert len(independent) == n-3
    assert clique_count(DG.complement(),n-2) == 0
    classical_obstructions.append(dict(rank=n,D_Gamma_independent_set=independent,
        D_Gamma_independence=n-3,A_Gamma_order=n-2))
print("C5 PASS: A8, D8 embeddings; explicit A7->E7; L2(3) independence=3; D6/D7 Gamma maximum degrees exceed E6/E7:",valencies)
print("C5 errata Gap 13 PASS: A_n cannot embed in D_n for n=4..9; Gamma independence numbers n-2 versus n-3")
print("C6 PASS: exact projector/frame identities and charpolys; theta(A_n)=n-1, theta(D_n)=2(n-2), theta(E6,E7,E8)=10,16,28")
print("C6 convention: I means identity on the span; ambient coordinates require the exported orthogonal projector.")
save("c04",["C4"],systems=structure,classical_scope="A1..A9, D3..D9; finite samples, not a proof for arbitrary rank")
save("c05",["C5"],A8_in_E8A=list(range(72)),D8_in_E8D=list(range(112)),
    A7_to_E7=dict(source_labels=an(7)[0],matrix=rows(T),output_scale=2,permutation_into_E7=embedding),
    L33=graph_data(L33),independence_number=3,T6=graph_data(T6),T6_clique_number=5,T6_independence_number=3,
    valency_obstructions=valencies,classical_nonembeddings=classical_obstructions,
    classical_argument="For n>=4 the D_n Gamma graph is n-3 triangles with one common centre, independence n-3; A_n Gamma is independent of order n-2.")
save("c06",["C6"],systems=frames)
