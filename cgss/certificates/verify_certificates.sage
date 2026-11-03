"""Reload the emitted JSON: validate exact data, witnesses and cross-file indices.

This is an independent serialization audit, not a Lean proof or trust-base component.
"""
from common import *
import hashlib
begin("JSON certificate round-trip audit")

def decode(x):
    if isinstance(x,float):
        raise AssertionError("Floating-point JSON entry")
    if isinstance(x,list):
        return [decode(y) for y in x]
    if isinstance(x,dict):
        if set(x) == {"num","den"}:
            assert isinstance(x["num"],int) and isinstance(x["den"],int)
            assert x["den"] > 1 and gcd(x["num"],x["den"]) == 1
            return QQ(x["num"])/x["den"]
        return {k:decode(v) for k,v in x.items()}
    return x

filenames = ["c02_models" if n == 2 else "c03_maps" if n == 3 else "c%02d" % n for n in range(1,25)] + ["remark311_ldl"]
data = {name:decode(json.loads((CERT/(name+".json")).read_text())) for name in filenames}
counters = Counter()
for z in data.values():
    assert z["schema"] == "linegraphs-sage-v1" and z["sage_version"] == "10.9"
assert set("C%d" % i for i in range(1,25)) <= {c for z in data.values() for c in z["computations"]}

def audit(z):
    if isinstance(z,list):
        for item in z:
            audit(item)
    if not isinstance(z,dict):
        return
    if {"matrix","eigenvalues","multiplicities","annihilator_coefficients","traces"} <= set(z):
        M = matrix(ZZ,z["matrix"])
        n = M.nrows()
        assert M == M.transpose()
        es,ms = z["eigenvalues"],z["multiplicities"]
        assert sorted(set(es)) == es and all(m > 0 for m in ms) and sum(ms) == n
        I = identity_matrix(ZZ,n)
        zero = zero_matrix(ZZ,n)
        for c in reversed(z["annihilator_coefficients"]):
            zero = zero*M+c*I
        assert zero.is_zero()
        R = PolynomialRing(ZZ,"x")
        x = R.gen()
        assert R(z["annihilator_coefficients"]) == prod(x-a for a in es)
        assert R(z["characteristic_polynomial_coefficients"]) == prod((x-a)**m for a,m in zip(es,ms))
        powers = I
        assert len(z["traces"]) == len(es)
        for j,tr in enumerate(z["traces"]):
            assert powers.trace() == tr == sum(m*a**j for a,m in zip(es,ms))
            powers *= M
        counters["spectral certificates"] += 1
    if {"matrix","lower","diagonal"} <= set(z):
        M,L,D = matrix(QQ,z["matrix"]),matrix(QQ,z["lower"]),diagonal_matrix(QQ,z["diagonal"])
        assert L*D*L.transpose() == M and all(a > 0 for a in D.diagonal())
        assert all(L[i,i] == 1 for i in range(L.nrows()))
        assert all(L[i,j] == 0 for i in range(L.nrows()) for j in range(i+1,L.ncols()))
        counters["positive LDL certificates"] += 1
    if {"order","edges","adjacency"} <= set(z):
        n = z["order"]
        A = matrix(ZZ,z["adjacency"]) if n else matrix(ZZ,0)
        assert A.nrows() == A.ncols() == n
        assert A == A.transpose() and set(A.list()) <= {0,1} and all(a == 0 for a in A.diagonal())
        assert sorted(tuple(e) for e in z["edges"]) == [(i,j) for i,j in combinations(range(n),2) if A[i,j]]
        counters["graph packets"] += 1
    if {"parameters","blocks"} <= set(z) and len(z["parameters"]) == 5:
        v,k,b,r,lam = z["parameters"]
        blocks = z["blocks"]
        assert len(blocks) == b and all(len(B) == len(set(B)) == k for B in blocks)
        assert all(0 <= p < v for B in blocks for p in B)
        N = matrix(ZZ,v,b,lambda i,j:int(i in blocks[j]))
        assert N*N.transpose() == (r-lam)*identity_matrix(v)+lam*ones_matrix(v)
        if "classes" in z:
            assert sorted(sum(z["classes"],[])) == list(range(b))
            assert all(sorted(p for i in cls for p in blocks[i]) == list(range(v)) for cls in z["classes"])
        counters["design packets"] += 1
    for value in z.values():
        audit(value)
for z in data.values():
    audit(z)

def check_iso(A,B,p):
    assert sorted(p) == list(range(B.nrows()))
    assert A == B.matrix_from_rows_and_columns(p,p)
    counters["isomorphism/switching witnesses"] += 1

def switched(A,S):
    S = set(S)
    return matrix(ZZ,A.nrows(),A.ncols(),lambda i,j:1-A[i,j] if (i in S) != (j in S) else A[i,j])

models = data["c02_models"]["models"]
for item in data["c03_maps"]["maps"]:
    V,W = [matrix(QQ,models[name]["roots"]) for name in (item["source"],item["target"])]
    T,p = matrix(QQ,item["matrix"]),item["permutation"]
    assert sorted(p) == list(range(240)) and V*T == W.matrix_from_rows(p)
    assert V*V.transpose()*item["norm_factor"] == (V*T)*(V*T).transpose()
    counters["root model maps"] += 1

for name,z in data["c06"]["systems"].items():
    V = matrix(QQ,z["roots"])
    W = V.matrix_from_rows(z["line_representative_indices"])
    P = matrix(QQ,z["projector"])
    assert P == P.transpose() and P*P == P and P.rank() == z["rank"]
    assert W.transpose()*W/z["q"] == matrix(QQ,z["frame"]) == z["frame_factor"]*P
    assert W*W.transpose()/z["q"]-2*identity_matrix(W.nrows()) == matrix(QQ,z["spectrum"]["matrix"])
    c4 = data["c04"]["systems"][name]
    assert len(c4["star_sum_indices"]) == sum(1 for a in (V*V.transpose()).list() if a == -z["q"])//2
    for i,j,k in c4["star_sum_indices"]:
        assert V[i]+V[j] == V[k] and V[i]*V[j] == -z["q"]
    counters["frames and closure witnesses"] += 1

z = data["c13"]
A,B = [matrix(ZZ,g["adjacency"]) for g in z["graphs"]]
sw = z["switching_isomorphism"]
check_iso(switched(A,sw["subset"]),B,sw["permutation"])
check_iso(A,matrix(ZZ,z["flag_graph"]["adjacency"]),z["flag_isomorphism"])
T = matrix(QQ,z["map_to_Lean_E7"])
E7 = matrix(QQ,models["E7"]["roots"])
for roots,indices in zip(z["roots"],z["Lean_E7_indices"]):
    assert matrix(QQ,roots)*T == E7.matrix_from_rows(indices)
for G,inv in zip(z["graphs"],z["nonisomorphism_invariants"]):
    graph = matrix_graph(matrix(ZZ,G["adjacency"]))
    assert claws(graph) == inv["claws"]
for G,n in zip(data["c15"]["graphs"],data["c15"]["four_clique_counts"]):
    assert clique_count(matrix_graph(matrix(ZZ,G["adjacency"])),4) == n

for name,z in data["c09"]["graphs"].items():
    V = matrix(QQ,z["roots"])
    assert V == matrix(QQ,models["E8_D"]["roots"]).matrix_from_rows(z["E8_indices"])
    assert V*V.transpose()/4-2*identity_matrix(V.nrows()) == matrix(ZZ,z["graph"]["adjacency"])
    if "target" in z:
        check_iso(matrix(ZZ,z["graph"]["adjacency"]),matrix(ZZ,z["target"]["adjacency"]),z["isomorphism"])

for name,z in data["c20"]["systems"].items():
    V = matrix(QQ,z["roots"])
    G = V*V.transpose()
    assert [[j for j in range(V.nrows()) if G[i,j] == z["q"]] for i in range(V.nrows())] == z["neighbour_indices"]
    if "apex_pairs" in z:
        c = V[z["apex_index"]]
        assert all(V[i]+V[j] == c for i,j in z["apex_pairs"])
for name,z in data["c21"]["systems"].items():
    B = matrix(QQ,z["simple_roots"])
    G = matrix(QQ,z["gram"])
    assert B*B.transpose()/z["q"] == G and G.det() == z["determinant"]
    assert G*matrix(QQ,z["gram_inverse"]) == identity_matrix(G.nrows())
    assert matrix(QQ,z["root_coefficients"])*B == matrix(QQ,data["c20"]["systems"][name]["roots"])

# Re-enumerate Lemma P by deriving n from (k,c), a different search order.
feasible = []
for k in range(1,35):
    for c in range(1,k+1):
        if (k-c)%2:
            continue
        theta = (k-c)//2
        a = c+theta-2
        n = QQ(k+1)+QQ(k*(k-a-1))/c
        if n not in ZZ or not 4 <= n <= 36 or not 0 <= a < k or not k < n-1:
            continue
        n = ZZ(n)
        m1 = QQ(2*n-k-2)/(theta+2)
        if m1 not in ZZ or m1 <= 0 or n-1-m1 <= 0 or n-2*k+c-2 < 0 or n-2*k+a < 0:
            continue
        feasible.append([n,k,a,c,theta,m1,n-1-m1,1+m1])
assert sorted(feasible) == data["c18"]["arithmetic_feasible"]

for key in ("E6","E7","E8"):
    z = data["c22"][key]
    A = matrix(ZZ,z["base"]["adjacency"])
    for case in z.get("cases",z.get("regular_switches",[])):
        S = case.get("switch_subset",case.get("subset"))
        target = z["target"] if key == "E6" else z["targets"][case["target"]]
        check_iso(switched(A,S),matrix(ZZ,target["adjacency"]),case["permutation"])
for name,inv in data["c22"]["E8"]["invariants"].items():
    G = matrix_graph(matrix(ZZ,data["c22"]["E8"]["targets"][name]["adjacency"]))
    assert local_clique_counts(G,4) == inv["four_cliques_through_vertex"]
for z in data["c19"]["negative_forms"]:
    M,x = matrix(ZZ,z["matrix"]),vector(ZZ,z["vector"])
    assert x*M*x == z["quadratic_value"] < 0
for z in data["c19"]["seven_by_seven"]:
    if z["j"]:
        assert matrix(ZZ,z["matrix"])*matrix(ZZ,z["inverse_numerator"]) == z["inverse_denominator"]*identity_matrix(7)

source_paths = [HERE.parents[1] / p for p in ["cgss/errata.md",
    "cgss/prerequisites.md","cgss/proofs/remark311/remark311.tex","LineGraphs/LineSystem/Models.lean"]]
source_paths += sorted(p for p in HERE.glob("*.sage") if p.is_file())
source_paths += [HERE/"common.py", HERE/"c23_lean_data.py", HERE/"run_all.sh"]
manifest = dict(schema="linegraphs-sage-manifest-v1",sage_version=sage.version.version,
    checked_packets=plain(dict(counters)),
    sources={str(p.relative_to(HERE.parents[1])):hashlib.sha256(p.read_bytes()).hexdigest() for p in source_paths},
    certificates={name+".json":dict(sha256=hashlib.sha256((CERT/(name+".json")).read_bytes()).hexdigest(),
        bytes=(CERT/(name+".json")).stat().st_size) for name in filenames})
(CERT/"manifest.json").write_text(json.dumps(manifest,indent=2,sort_keys=True)+"\n")
print("PASS: 25 exact JSON certificate files cover C1-C24 and Remark 3.11")
for key,count in sorted(counters.items()):
    print(key+":",count)
print("PASS: cross-file root indices, frames, maps, switches, designs, Connor witnesses and independent Lemma P enumeration")
print("manifest: data/manifest.json")
