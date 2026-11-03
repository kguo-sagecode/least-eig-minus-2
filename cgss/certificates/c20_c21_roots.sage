from common import *
begin("C20, C21: every root neighbourhood, apex pairs, simple bases")
neighbourhoods,bases = {},{}
systems = [("A9",an(9)[1],1,16),("D9",dn(9)[1],1,28)]
systems += [("E%d" % n,exceptional(n)[1],4,cnt) for n,cnt in [(6,20),(7,32),(8,56)]]
for name,V,q,cnt in systems:
    M = matrix(ZZ,V)
    G = M*M.transpose()
    neighbours = [[j for j in range(len(V)) if G[i,j] == q] for i in range(len(V))]
    assert set(map(len,neighbours)) == {cnt}
    item = dict(roots=rows(M),q=q,neighbour_indices=neighbours,counts=[len(z) for z in neighbours])
    if name.startswith("E"):
        rank = int(name[1:])
        lookup = {tuple(v):i for i,v in enumerate(V)}
        c = vector(ZZ,[1]*8)
        apex = lookup[tuple(c)]
        edges = list(combinations(range({6:5,7:6,8:8}[rank]),2))
        if rank == 7:
            edges.append((6,7))
        pairs = []
        for a,b in edges:
            v = 2*(unit(8,a)+unit(8,b))
            pairs.append([lookup[tuple(v)],lookup[tuple(c-v)]])
        assert sorted(sum(pairs,[])) == sorted(neighbours[apex])
        assert all(G[i,j] == -q for i,j in pairs)
        item.update(apex_index=apex,edge_labels=edges,apex_pairs=pairs)

        simple = simple_roots(V)
        B = matrix(QQ,simple)
        gram = B*B.transpose()/q
        assert B.rank() == len(simple) == rank
        assert gram.det() == 9-rank
        cartan = matrix(ZZ,CartanMatrix(["E",rank]))
        permutation = iso(matrix_graph(gram,-1),matrix_graph(cartan,-1))
        assert all(gram[i,j] == cartan[permutation[i],permutation[j]] for i in range(rank) for j in range(rank))
        # Every root has integral coefficients, all nonnegative or all nonpositive.
        coordinates = M*B.transpose()*(B*B.transpose()).inverse()
        assert coordinates*B == M
        assert all(a in ZZ for a in coordinates.list())
        assert all(all(a >= 0 for a in row) or all(a <= 0 for a in row) for row in coordinates.rows())
        sageE = RootSystem(["E",rank]).ambient_space()
        sage_simple = [vector(QQ,v.to_vector()) for v in sageE.simple_roots()]
        target_basis = matrix(QQ,[sage_simple[permutation[i]] for i in range(rank)])
        image = coordinates*target_basis
        assert {tuple(row) for row in image.rows()} == {tuple(v.to_vector()) for v in sageE.roots()}
        bases[name] = dict(q=q,simple_indices=[lookup[tuple(v)] for v in simple],
            simple_roots=rows(B),gram=rows(gram),determinant=gram.det(),
            gram_inverse=rows(gram.inverse()),root_coefficients=rows(coordinates),
            sage_cartan=rows(cartan),permutation_to_sage_cartan=permutation,
            sage_normalized_target_basis=rows(target_basis),LDL=ldl(gram))
        print("C21",name,"PASS: simple-root Gram determinant",gram.det(),"and integral coefficients for every root")
    neighbourhoods[name] = item
    print("C20",name,"PASS:",len(V),"roots,",cnt,"neighbours per root")
save("c20",["C20"],systems=neighbourhoods,classical_formulas=dict(A="2*(rank-1)",D="4*(rank-2)"))
save("c21",["C21"],systems=bases)
