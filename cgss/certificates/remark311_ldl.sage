from common import *
begin("Remark 3.11: exact rational LDL^T certificates in Mathlib indexing")

data = []
for name,n,d in [("E6",6,[1]*6),("E7",7,[1]*7),("E8",8,[1]*8),
                 ("F4",4,[1,1,2,2]),("G2",2,[1,3])]:
    M = 2*identity_matrix(ZZ,n)
    if name.startswith("E"):
        for i,j in [(0,2),(1,3),(2,3)]+[(i,i+1) for i in range(3,n-1)]:
            M[i,j] = M[j,i] = -1
    elif name == "F4":
        for i in range(3):
            M[i,i+1] = M[i+1,i] = -1
        M[1,2] = -2
    else:
        M[0,1],M[1,0] = -3,-1
    H = diagonal_matrix(d)*M
    cert = ldl(H)
    assert all(q > 0 for q in cert["diagonal"])
    expected_q = {"E6":[2,2,QQ(3)/2,QQ(5)/6,QQ(4)/5,QQ(3)/4],
                  "E7":[2,2,QQ(3)/2,QQ(5)/6,QQ(4)/5,QQ(3)/4,QQ(2)/3],
                  "E8":[2,2,QQ(3)/2,QQ(5)/6,QQ(4)/5,QQ(3)/4,QQ(2)/3,QQ(1)/2],
                  "F4":[2,QQ(3)/2,QQ(4)/3,1],"G2":[2,QQ(3)/2]}[name]
    assert cert["diagonal"] == expected_q
    # The paper's ordering for E equals Sage's ordering minus one. F/G may be transposed.
    sageC = matrix(ZZ,CartanMatrix([name[0],n]))
    assert M == sageC or M == sageC.transpose()
    minors = [M[:i,:i].det() for i in range(1,n+1)]
    expected = {"E6":[2,4,6,5,4,3],"E7":[2,4,6,5,4,3,2],"E8":[2,4,6,5,4,3,2,1],
                "F4":[2,3,2,1],"G2":[2,1]}[name]
    assert minors == expected
    data.append(dict(type=name,cartan=rows(M),symmetrizer=d,leading_cartan_minors=minors,LDL=cert))
    print(name,"PASS: leading minors",minors,"LDL pivots",cert["diagonal"])
save("remark311_ldl",["C17","C21","Remark 3.11"],cases=data,
     convention="H=diag(d)*M=L*diag(q)*L^T; row/column order is the Mathlib order in remark311.tex")
