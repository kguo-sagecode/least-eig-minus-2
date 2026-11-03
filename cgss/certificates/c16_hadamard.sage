from common import *
from sage.combinat.matrices.hadamard_matrix import hadamard_matrix_paleyI, hadamard_matrix
begin("C16: Hadamard row products and exact line angles")

results = []
examples = [("Paley12",hadamard_matrix_paleyI(12,normalize=False),4)]
examples += [("Sylvester%d" % n,hadamard_matrix(n),n) for n in (2,4,8,16)]
for name,H,x in examples:
    n = H.nrows()
    assert set(H.list()) == {-1,1} and H*H.transpose() == n*identity_matrix(n)
    pairs = list(combinations(range(n),2))
    P = matrix(ZZ,[[H[i,k]*H[j,k] for k in range(n)] for i,j in pairs])
    assert 2*P.transpose()*P == n*n*identity_matrix(n)-n*ones_matrix(n)
    assert P.rank() == n-1 and P*vector(ZZ,[1]*n) == 0
    agreements = Counter(sum(len({H[i,k] for i in inds}) == 1 for k in range(n)) for inds in combinations(range(n),4))
    assert all(8*a in (n,n-x,n+x) for a in agreements)
    G = P*P.transpose()
    A = (G-n*identity_matrix(len(pairs)))/x
    assert set(A.list()) <= {-1,0,1}
    assert (x*A+n*identity_matrix(len(pairs)))*(x*A-n*(n-2)/2*identity_matrix(len(pairs))) == 0
    reps = Counter(tuple(v if next(a for a in v if a)>0 else -v) for v in P.rows())
    if n == 12:
        assert len(reps) == 66
        assert {abs(G[i,j]) for i,j in combinations(range(66),2)} == {0,4}
        assert set(sum(row) for row in (x*A).rows()) == {-60,36}
    else:
        assert len(reps) == n-1 and set(reps.values()) == {n//2}
    # Hypothesis 6.1's fourth-row count, for every fixed triple.
    fourth_counts = []
    for triple in combinations(range(n),3):
        exceptional = 0
        for j in range(n):
            if j in triple:
                continue
            a = sum(len({H[i,k] for i in triple+(j,)}) == 1 for k in range(n))
            exceptional += 8*a in (n-x,n+x)
        fourth_counts.append(exceptional)
    # For distinct fourth rows the count is d^2 (unless n=2, with no triples).
    if fourth_counts:
        assert set(fourth_counts) == {(n//x)**2}
    spectral_certificate = spectral(G,[(n*n//2,n-1),(0,len(pairs)-n+1)])
    results.append(dict(name=name,n=n,x=x,H=rows(H),pairs=pairs,P=rows(P),
        agreement_histogram=[[a,c] for a,c in sorted(agreements.items())],distinct_lines=len(reps),
        line_multiplicities=sorted(reps.values()),xA_row_sums=sorted(set(sum(row) for row in (x*A).rows())),
        fourth_row_counts=fourth_counts,gram_spectrum=spectral_certificate))
    print("C16",name,"PASS: rank",n-1,"distinct lines",len(reps),"agreement histogram",dict(agreements),
          "xA row sums",results[-1]["xA_row_sums"])
print("C16 confirms errata Error 9: xAJ=-nJ is false; the quadratic identities hold.")
save("c16",["C16"],examples=results,general_entry_identity="sum_(i<j) h_ic*h_jc*h_id*h_jd = ((sum_i h_ic*h_id)^2-n)/2")
