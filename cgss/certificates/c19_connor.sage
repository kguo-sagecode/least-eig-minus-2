from common import *
begin("C19: Hall-Connor finite certificates")

# Moment equations for intersections with a fixed block; they also rule out
# a second labelled block with the same underlying 5-set.
solutions = [list(z) for z in IntegerVectors(20,6)
             if sum(i*z[i] for i in range(6)) == 30 and sum(i*i*z[i] for i in range(6)) == 50]
assert solutions == [[0,10,10,0,0,0]]
assert [i*i-3*i+2 for i in range(6)] == [2,0,0,2,6,12]

R = PolynomialRing(QQ,names=("S","J"))
S,J = R.gens()
ideal = R.ideal([S*S-5*S-50*J,S*J-35*J,J*J-21*J])
C = 35-7*S+10*J
assert ideal.reduce(C*C-35*C) == 0
assert ideal.reduce(C*J) == 0
# For C*N^T, use S*N^T = N^T*(5I+2J_15) = 5N^T+10J_21,15
# and J_21*N^T = 7J_21,15, from block size 5 and replication 7.
assert 35-7*5 == 0 and -7*10+10*7 == 0

claw = matrix(ZZ,[[10,3,3,3],[3,10,-4,-4],[3,-4,10,-4],[3,-4,-4,10]])
x4 = vector(ZZ,[-1,1,1,1])
bad5 = matrix(ZZ,[[10,3,3,3,-4],[3,10,3,-4,3],[3,3,10,-4,3],[3,-4,-4,10,3],[-4,3,3,3,10]])
x5 = vector(ZZ,[-1,1,1,1,-1])
assert x4*claw*x4 == -2 and x5*bad5*x5 == -4
negative = [dict(matrix=rows(M),vector=list(x),quadratic_value=x*M*x,determinant=M.det()) for M,x in [(claw,x4),(bad5,x5)]]
print("C19 negative quadratic forms:",[z["quadratic_value"] for z in negative])

seven = []
for j in (0,1,2):
    U,V = list(range(3,3+j)),list(range(3+j,7))
    first_pairs = {(0,1),(0,2),(1,2)}
    first_pairs |= {(0,u) for u in U} | {(a,v) for a in (1,2) for v in V}
    first_pairs |= set(combinations(U,2)) | set(combinations(V,2))
    M = matrix(ZZ,7,7,lambda a,b: 10 if a == b else (3 if tuple(sorted((a,b))) in first_pairs else -4))
    assert M.det() == j*(3-j)*7**6
    item = dict(j=j,matrix=rows(M),determinant=M.det(),rank=M.rank())
    if j:
        inverse14 = (14*M.inverse()).change_ring(ZZ)
        assert M*inverse14 == 14*identity_matrix(7)
        item.update(inverse_numerator=rows(inverse14),inverse_denominator=14,LDL=ldl(M))
        assert all(d > 0 for d in item["LDL"]["diagonal"])
    else:
        null = M.right_kernel().basis()[0]
        null *= lcm(a.denominator() for a in null)
        item["null_vector"] = list(null)
        assert M*null == 0
    seven.append(item)
value = (5*identity_matrix(ZZ,22)+2*ones_matrix(ZZ,22)).det()
assert value == 5**21*49 and value.valuation(5) == 21 and not value.is_square()
print("C19 PASS: intersections 1 or 2 (ten each); C^2=35C, CN^T=0; seven-by-seven determinants",[z["determinant"] for z in seven])
print("C19 PASS: 5^21*49 =",value,"has odd 5-adic valuation 21; nonsingularity, not failure of PSD, excludes the two 7x7 cases.")
save("c19",["C19"],intersection_moment_solutions=solutions,moment_columns=list(range(6)),
    negative_forms=negative,seven_by_seven=seven,determinant_square_obstruction=dict(value=value,prime=5,valuation=21),
    Connor_relations=["S^2=5S+50J","SJ=JS=35J","J^2=21J","C=35I-7S+10J","C^2=35C","CN^T=0"],
    rank_bound=6)
