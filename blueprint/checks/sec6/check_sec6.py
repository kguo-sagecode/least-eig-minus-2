import numpy as np, itertools as it
def syl(k):
    H=np.array([[1]])
    for _ in range(k): H=np.block([[H,H],[H,-H]])
    return H
# Paley H12
q=11; sq={(x*x)%q for x in range(1,q)}
chi=lambda a: 0 if a%q==0 else (1 if a%q in sq else -1)
Q=np.array([[chi(j-i) for j in range(q)] for i in range(q)])
S=np.zeros((12,12),int); S[0,1:]=1; S[1:,0]=-1; S[1:,1:]=Q
H12=S+np.eye(12,dtype=int)
for H in [syl(3),syl(4),H12]:
    n=len(H); assert (H@H.T==n*np.eye(n)).all()
    pairs=list(it.combinations(range(n),2)); P=np.array([H[i]*H[j] for i,j in pairs])
    assert (P.T@P==n*n/2*np.eye(n)-n/2).all()
    assert (P@np.ones(n)==0).all()
    for i,j,k,l in it.combinations(range(n),4):
        a=sum(1 for c in range(n) if H[i,c]==H[j,c]==H[k,c]==H[l,c])
        assert 8*a==n+P[pairs.index((i,j))]@P[pairs.index((k,l))]
    G=P@P.T; assert (G@G==n*n/2*G).all()
    vals=set(np.unique(G-n*np.eye(len(pairs))).astype(int)); print(n,vals)
    # fourth-row count for rows 0,1,2
    x=max(abs(v) for v in vals)
    m=sum(1 for j in range(3,n) if P[pairs.index((0,j))]@P[pairs.index((1,2))]!=0)
    print(' fourth rows',m,'(n/x)^2=',(n/x)**2)
# E7 in model (ii) doubled coordinates
E8=[]
for i,j in it.combinations(range(8),2):
    for s,t in it.product([2,-2],repeat=2):
        v=[0]*8; v[i]=s; v[j]=t; E8.append(tuple(v))
for eps in it.product([1,-1],repeat=8):
    if np.prod(eps)==1: E8.append(eps)
E8=np.array(E8); E7=E8[E8[:,6]==E8[:,7]]
print(len(E8),len(E7))
ip=E7@E7.T//4
print(set((ip==1).sum(1)))
# n-1 orthogonal lines in D_l only for l even: brute check small l
def maxorth(roots):
    best=0
    lines=[r for r in roots if tuple(-np.array(r))>tuple(r)]
    def rec(ch,start):
        nonlocal best; best=max(best,len(ch))
        for a in range(start,len(lines)):
            if all(np.dot(lines[a],lines[b])==0 for b in ch): rec(ch+[a],a+1)
    rec([],0); return best
for l in range(2,8):
    D=[tuple(v) for i,j in it.combinations(range(l),2) for s,t in it.product([1,-1],repeat=2) for v in [[s if c==i else t if c==j else 0 for c in range(l)]]]
    A=[tuple(v) for i in range(l+1) for j in range(l+1) if i!=j for v in [[1 if c==i else -1 if c==j else 0 for c in range(l+1)]]]
    print(l,'A',maxorth(A),'D',maxorth(D))
