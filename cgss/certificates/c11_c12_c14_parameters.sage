from common import *
begin("C11, C12, C14: design parameter algebra, H spectra, Hadamard border")
R = PolynomialRing(QQ,names=("s","t","k","r","v"))
s,t,k,r,v = R.gens()
F = R.fraction_field()
bb = F(v*r)/k
edge_equation = 2*v*r-(r+k)*(bb+v-1)/2
assert edge_equation == (k*(r+k)-v*(r-k)**2)/(2*k)
vv = F(k*(r+k))/(r-k)**2
assert vv(r=k+2*t) == F(k*(k+t))/(2*t*t)
vs = s*(s+1)/2
bs = (s+1)*(s+2)/2
ks,rs = s*t,(s+2)*t
lam = F(2*t*(s*t-1))/(s-1)
assert vs*rs == bs*ks
assert lam*(vs-1) == rs*(ks-1)
assert lam == 2*t*t+F(2*t*(t-1))/(s-1)
assert vs-ks == s*(s+1-2*t)/2
assert bs-vs == s+1

N = s*(s+2)
degree = (s+1)*t
B = F(t*(s+1)*(s-t))/(s-1)
g = F(t*t*(s+1)*(s*t-1))/(s-1)
mu = (s-1)*(s+2)/2
assert 1+(s+1)+2*mu == N
assert degree-(s+1)*t == 0
assert degree**2+(s+1)*t*t+2*mu*B == N*degree
assert degree**3-(s+1)*t**3 == N*t**3*(s+1)
assert (degree+t)*(degree*degree-B) == g*N
assert g-t*degree+t*B == t**3*(s+1)
print("C11 PASS: parameter identities, divisibility remainder 2*t*(t-1), spectral multiplicities, H polynomial identity and triangle parity")
print("C11 confirms the errata: k<=v requires s>=2*t-1.")

instances = []
for ss,tt,H in [(3,1,integer_graph(graphs.PetersenGraph().line_graph())),
                 (3,2,integer_graph(graphs.CompleteGraph(6).line_graph()))]:
    A = adjacency(H)
    nv,dv,bv,gv = [ZZ(z(s=ss,t=tt)) for z in (N,degree,B,g)]
    I,J = identity_matrix(nv),ones_matrix(nv)
    assert (A+tt*I)*(A*A-bv*I) == gv*J
    assert A*J == dv*J
    sp = Counter()
    sp[dv] += 1
    sp[-tt] += ss+1
    root = ZZ(bv.sqrt())
    sp[root] += (ss-1)*(ss+2)//2
    sp[-root] += (ss-1)*(ss+2)//2
    instances.append(dict(s=ss,t=tt,graph=graph_data(H),B=bv,g=gv,spectrum=spectral(A,list(sp.items()))))

# Formal border multiplication reduces to these scalar relations:
# Q=2A-J, Q*j=j, Q^2=4*t^2*I-J, N=4*t^2-1.
Nborder = 4*t*t-1
assert 2*(2*t*t)-Nborder == 1
assert 4*t*t-4*(2*t*t)+Nborder == -1
border_examples = []
for tt,H in [(1,graphs.CompleteGraph(3)),(2,integer_graph(graphs.CompleteGraph(6).line_graph()))]:
    A = adjacency(H)
    nv = H.order()
    assert nv == 4*tt*tt-1
    I,J = identity_matrix(nv),ones_matrix(nv)
    assert A*A == tt*tt*(I+J) and A*J == 2*tt*tt*J
    Q = 2*A-J
    K = block_matrix(QQ,[[matrix([[-1]]),-ones_matrix(1,nv)],[-ones_matrix(nv,1),Q]])
    assert K == K.transpose() and set(K.list()) == {-1,1}
    assert K*K.transpose() == 4*tt*tt*identity_matrix(nv+1)
    assert set(K.diagonal()) == {-1}
    border_examples.append(dict(t=tt,A=rows(A),hadamard=rows(K),positive_diagonal_hadamard=rows(-K)))
print("C12 PASS: symbolic block multiplication; explicit orders 4 and 16. The literal border has diagonal -1; negate it for diagonal +1.")

allowed = []
for tt in range(2,21):
    for divisor in divisors(2*tt*(tt-1)):
        ss = divisor+1
        if ss >= 2*tt-1 and tt*(ss+1) % 2 == 0:
            ll = ZZ(lam(s=ss,t=tt))
            allowed.append([ss,tt,ll])
assert sorted(ss for ss,tt,ll in allowed if tt == 2) == [3,5]
assert all(ll >= 19 for ss,tt,ll in allowed if tt >= 3)
assert lam(s=13,t=3) == 19
# General bound: lambda=2*t^2+positive_integer; t>=3 gives lambda>=19.
assert (2*t*t-18) == 2*(t-3)*(t+3)
print("C14 PASS: t=2 gives s=3,5; t>=3 gives lambda>=2*t^2+1>=19, attained at (s,t)=(13,3)")

def rational_function(z):
    z = F(z)
    return dict(numerator=[[list(e),c] for e,c in sorted(z.numerator().dict().items())],
                denominator=[[list(e),c] for e,c in sorted(z.denominator().dict().items())])

save("c11",["C11"],variables=list(R.variable_names()),parameter_functions={key:rational_function(z) for key,z in
    dict(v=vs,b=bs,k=ks,r=rs,lambda_value=lam,N=N,degree=degree,nonprincipal_square=B,identity_rhs=g,
         equal_multiplicity=mu,triangle_diagonal=t**3*(s+1)).items()},
    identities="(A+tI)(A^2-BI)=gJ; AJ=degree*J; triangle_diagonal is even",instances=instances)
save("c12",["C12"],convention="H=[[-1,-j^T],[-j,2A-J]]; -H has positive diagonal",examples=border_examples,
     general_assumptions="A symmetric 0/1 with zero diagonal, order 4t^2-1, A^2=t^2(I+J), Aj=2t^2j")
save("c14",["C14"],t2_survivors=[row for row in allowed if row[1] == 2],bounded_crosscheck=allowed,
    bounded_t_range=[2,20],general_bound="lambda=2t^2+2t(t-1)/(s-1)>=2t^2+1 for integer lambda,t>=3,s>1",
    sharp_parameters=[13,3,19])
