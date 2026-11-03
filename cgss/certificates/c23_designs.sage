from common import *
from sage.combinat.designs.incidence_structures import IncidenceStructure
from sage.combinat.designs.resolvable_bibd import kirkman_triple_system
begin("C23: hyperoval designs, Kirkman triples, and the 37-point biplane")

def resolution_check(v,blocks,classes):
    assert sorted(sum(classes,[])) == list(range(len(blocks)))
    for cls in classes:
        assert sorted(p for i in cls for p in blocks[i]) == list(range(v))

def block_graph(k,blocks,classes):
    v = k*(2*k-1)
    resolution_check(v,blocks,classes)
    membership = {i:c for c,cls in enumerate(classes) for i in cls}
    H = Graph(len(blocks))
    H.add_edges((i,j) for i,j in combinations(range(len(blocks)),2)
                if membership[i] != membership[j] and not set(blocks[i]) & set(blocks[j]))
    s,t = 2*k-1,k-1
    degree = (s+1)*t
    sq = QQ(t*(s+1)*(s-t))/(s-1)
    root = ZZ(sq.sqrt())
    mu = (s-1)*(s+2)//2
    spec = spectral(adjacency(H),[(degree,1),(-t,s+1),(root,mu),(-root,mu)])
    return dict(graph=graph_data(H),s=s,t=t,spectrum=spec)

def hyperoval_design(d):
    k = 2**d
    q = 2*k
    field = GF(q,"z")
    elts = sorted(field,key=lambda x:x.to_integer())
    def canonical(p):
        a = next(x for x in p if x)
        return tuple(x/a for x in p)
    coords = sorted({canonical(p) for p in product(elts,repeat=3) if any(p)},
                    key=lambda p:tuple(x.to_integer() for x in p))
    index = {p:i for i,p in enumerate(coords)}
    def incident(p,l):
        return sum(a*b for a,b in zip(p,l)) == 0
    pg_blocks = [[i for i,p in enumerate(coords) if incident(p,l)] for l in coords]
    PG = IncidenceStructure(len(coords),pg_blocks)
    # Independently constructed Sage projective plane.
    assert PG.is_isomorphic(designs.ProjectiveGeometryDesign(2,1,field))
    O = {canonical((field(1),t,t*t)) for t in elts}
    O |= {(field(0),field(0),field(1)),(field(0),field(1),field(0))}
    assert len(O) == q+2
    assert all(sum(incident(p,l) for p in O) in (0,2) for l in coords)
    external = [l for l in coords if not any(incident(p,l) for p in O)]
    off_points = [p for p in coords if p not in O]
    blocks = [[j for j,l in enumerate(external) if incident(p,l)] for p in off_points]
    design = design_check(len(external),blocks,k,1)
    assert design["parameters"] == [k*(2*k-1),k,4*k*k-1,2*k+1,1]
    base = (field(0),field(0),field(1))
    pencils = [l for l in coords if incident(base,l)]
    classes = [[i for i,p in enumerate(off_points) if incident(p,l)] for l in pencils]
    resolution_check(len(external),blocks,classes)
    design.update(d=d,q=q,field_modulus=[int(c) for c in field.modulus().list()],
        projective_coordinates=[[x.to_integer() for x in p] for p in coords],
        hyperoval_indices=sorted(index[p] for p in O),
        external_line_indices=[index[p] for p in external],block_point_indices=[index[p] for p in off_points],
        classes=classes,block_graph=block_graph(k,blocks,classes))
    print("C23 hyperoval d=%d PASS:" % d,design["parameters"],"parallel classes",len(classes))
    return design

hyperovals = [hyperoval_design(d) for d in (1,2)]
KTS = kirkman_triple_system(15)
blocks = sorted(sorted(B) for B in KTS.blocks())
ok,classes_as_blocks = KTS.is_resolvable(certificate=True)
assert ok
lookup = {tuple(B):i for i,B in enumerate(blocks)}
classes = sorted(sorted(lookup[tuple(sorted(B))] for B in cls) for cls in classes_as_blocks)
resolution_check(15,blocks,classes)
kts = design_check(15,blocks,3,1)
kts.update(classes=classes,block_graph=block_graph(3,blocks,classes))
print("C23 Kirkman PASS:",kts["parameters"],"with 7 parallel classes")

field = GF(37)
difference_set = sorted({int(t**4) for t in field if t})
assert difference_set == [1,7,9,10,12,16,26,33,34]
diff_counts = Counter((a-b)%37 for a in difference_set for b in difference_set if a != b)
assert set(diff_counts) == set(range(1,37)) and set(diff_counts.values()) == {2}
biplane_blocks = [sorted((a+t)%37 for a in difference_set) for t in range(37)]
biplane = design_check(37,biplane_blocks,9,2)
removed = set(biplane_blocks[0])
remaining = sorted(set(range(37))-removed)
residual_blocks = [[remaining.index(x) for x in B if x not in removed] for B in biplane_blocks[1:]]
residual = design_check(28,residual_blocks,7,2)
complement_blocks = [sorted(set(range(28))-set(B)) for B in residual_blocks]
complement = design_check(28,complement_blocks,21,20)
assert complement["parameters"] == [28,21,36,27,20]
derived_blocks = [[difference_set.index(x) for x in B if x in removed] for B in biplane_blocks[1:]]
derived = design_check(9,derived_blocks,2,1)
small = design_check(6,design632(),3,2)
print("C23 biplane PASS: (37,9,37,9,2); residual",residual["parameters"],"complement",complement["parameters"])
print("C23 small design PASS:",small["parameters"])
save("c23",["C23"],hyperoval_designs=hyperovals,kirkman=kts,design632=small,
    fourth_power_difference_set=difference_set,difference_multiplicities=sorted(diff_counts.items()),
    biplane=biplane,deleted_block_index=0,residual_point_labels=remaining,residual=residual,
    complement_residual=complement,derived=derived)
