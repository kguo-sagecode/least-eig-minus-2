from common import *
begin("C1, C8, C24: determinants, parameter inequalities, rank obstruction")

R = PolynomialRing(QQ, names=("k", "n", "d", "alpha", "m"))
k, n, d, alpha, m = R.gens()
M = matrix(R, [[2,1,0,0,k], [1,2,0,k,0],
    [0,0,k*k+k,k*k-k,k*k-k], [0,k,k*k-k,k*k+k,k], [k,0,k*k-k,k,k*k+k]])
assert M[1:,1:].det() == 2*k**5*(5-k)
assert 2*k*(3*k-5) == 2*k*(k-2)+4*k*k-6*k
assert 2+3*k+(3*k-5) == 6*k-3
print("C1 PASS: corrected symmetric block sums; minor determinant = 2*k^5*(5-k); N=3*k-5, Gamma=6*k-3")

F = R.fraction_field()
b = F(d+2)/(2*n)
psd = (1-b)**2 + (F(1)/2-b)**2*alpha + b*b*(-1-alpha)
linear = alpha*(n-2*d-4)+2*(2*n-2*d-4)
assert 4*n*psd == linear
quadratic = (d-2*n+16)*(2*d+4-n)+14*(2*n-2*d-4)
assert quadratic == 2*d*d-5*d*n+8*d+2*n*n+4*n+8
survivors, excluded = [], []
for nn in range(1,29):
    for dd in range(nn):
        if nn >= 2*dd+4:
            continue
        value = quadratic(n=nn, d=dd)
        row = [nn, dd, value]
        (survivors if value >= 0 else excluded).append(row)
assert max(dd for nn, dd, z in survivors if nn == 28) == 17
assert max(dd for nn, dd, z in survivors if nn <= 27) == 16
assert all(dd <= (17 if nn == 28 else 16) for nn, dd, z in survivors)
print("C8 PASS: exact PSD reduction; under n<2d+4, n=28 gives d<=17 and n<=27 gives d<=16")

gap = (2*m-16)**2-(27-m)*(192-4*m)
assert gap == 236*m-4928
rank_rows = [[mm, (2*mm-16)**2, (27-mm)*(192-4*mm), gap(m=mm)] for mm in range(21,28)]
assert all(row[-1] > 0 for row in rank_rows)
print("C24 PASS: gaps for m=21..27:", [z[-1] for z in rank_rows])

# The rank-transfer error in [CGSS], Theorem 4.4, p. 318 (cgss/errata.md, Error 15),
# is independently visible on T(8).
T8 = integer_graph(graphs.CompleteGraph(8).line_graph())
A = adjacency(T8)
E = (4*identity_matrix(28)+2*A-ones_matrix(28))/3
assert E*vector(QQ, [1]*28) == 0
assert E.rank() == 7 and (2*identity_matrix(28)+A).rank() == 8
review = spectral(3*E, [(12,7),(0,21)])
print("C8 WARNING: T(8) has equiangular Gram rank 7, original Gram rank 8, and all-ones eigenvalue 0; the positivity/rank-transfer sentence needs d>12 ([CGSS], Theorem 4.4, p. 318; cgss/errata.md, Error 15).")

def polynomial_data(p):
    return [[list(e), c] for e,c in sorted(R(p).dict().items())]

save("c01", ["C1"], variables=R.variable_names(), block_sum_matrix=[[polynomial_data(a) for a in r] for r in M.rows()],
     determinant=polynomial_data(M[1:,1:].det()), N=polynomial_data(3*k-5), Gamma=polynomial_data(6*k-3))
save("c08", ["C8"], variables=R.variable_names(), psd_linear_numerator=polynomial_data(linear),
     quadratic=polynomial_data(quadratic), bounds=dict(n=[1,28], d="0 <= d < n", condition="n < 2*d+4"),
     survivors=survivors, excluded=excluded, review_counterexample=dict(graph=graph_data(T8), triple_equiangular_gram=review))
save("c24", ["C24"], rows=rank_rows, columns=["m","left","right","gap"], gap_linear_coefficients=[-4928,236])
