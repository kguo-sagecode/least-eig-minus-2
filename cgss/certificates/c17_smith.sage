from common import *
begin("C17: Smith graphs, positive eigenvectors, and deleted-vertex bases")

cases = []
for typ,ranks in [("A",range(2,13)),("D",range(4,13)),("E",(6,7,8))]:
    for rank in ranks:
        C = matrix(ZZ,CartanMatrix([typ,rank,1]))
        A = 2*identity_matrix(rank+1)-C
        assert A == A.transpose() and set(A.list()) <= {0,1}
        G = matrix_graph(A)
        assert G.is_connected()
        null = C.right_kernel().basis()[0]
        null *= lcm(a.denominator() for a in null)
        null = vector(ZZ,null)
        if null[0] < 0:
            null = -null
        assert all(a > 0 for a in null) and gcd(null) == 1
        assert A*null == 2*null
        ambient = RootSystem([typ,rank]).ambient_space()
        simple = [vector(QQ,v.to_vector()) for v in ambient.simple_roots()]
        highest = vector(QQ,ambient.highest_root().to_vector())
        V = matrix(QQ,[-highest]+simple)
        assert V*V.transpose() == C
        assert V.rank() == rank and matrix(simple).rank() == rank
        finite = C[1:,1:]
        factor = {"A":rank+1,"D":4,"E":9-rank}[typ]
        assert finite.det() == factor
        deleted_determinants = [C.matrix_from_rows_and_columns([j for j in range(rank+1) if j != i],
            [j for j in range(rank+1) if j != i]).det() for i in range(rank+1)]
        assert deleted_determinants == [factor*a*a for a in null]
        decomposition = ldl(finite)
        assert all(d > 0 for d in decomposition["diagonal"])
        # Check the entire Gram is PSD by exact Sage algebraic-real eigenvalues.
        assert min(C.change_ring(AA).eigenvalues()) == 0
        if typ == "A":
            assert G.is_isomorphic(graphs.CycleGraph(rank+1))
            assert list(null) == [1]*(rank+1)
        if typ == "D":
            assert Counter(null) == {1:4,2:rank-3}
        cases.append(dict(type=typ,rank=rank,vertices=list(range(rank+1)),marked_vertex=0,
            graph=graph_data(G),positive_eigenvector=list(null),affine_roots=rows(V),gram=rows(C),
            remaining_basis=rows(matrix(simple)),remaining_determinant=factor,remaining_LDL=decomposition,
            all_vertex_deletion_determinants=deleted_determinants))
        if typ == "E":
            print("C17 E%d affine: positive vector" % rank,list(null),"deleted determinant",factor)
print("C17 PASS: A2..A12 cycles, D4..D12 forks, E6/E7/E8 affine diagrams; marked affine node 0 deleted; every single-vertex deletion gives independent roots")
print("C17 scope: finite checks plus displayed family vectors; the inference 'positive eigenvector => largest eigenvalue' uses SM1 in Lean.")
save("c17",["C17"],cases=cases,family_rules=dict(A="cycle: every coordinate 1",D="four leaves 1; fork-to-fork path 2"))
