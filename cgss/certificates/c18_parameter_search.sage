from common import *
begin("C18: exhaustive exact parameter search for Lemma P")

raw_feasible = []
tested = 0
for n in range(4,37):
    for k in range(1,n-1):
        for a in range(k):
            for c in range(1,k+1):
                tested += 1
                theta = a-c+2
                if theta < 0 or k != c+2*theta or k*(k-a-1) != c*(n-k-1):
                    continue
                num,den = 2*n-k-2,theta+2
                if num % den:
                    continue
                m1 = num//den
                m2 = n-1-m1
                if m1 <= 0 or m2 <= 0:
                    continue
                raw_feasible.append([n,k,a,c,theta,m1,m2,1+m1])
# Nonnegative complement common-neighbour counts are necessary too (SR2).
all_feasible = [p for p in raw_feasible if p[0]-2*p[1]+p[3]-2 >= 0 and p[0]-2*p[1]+p[2] >= 0]
complement_rejected = [p for p in raw_feasible if p not in all_feasible]
assert len(raw_feasible) == 34 and len(complement_rejected) == 4
rank8 = [p for p in all_feasible if p[7] <= 8]
lemmaP = [p for p in rank8 if p[1] <= 16]
expected = [[2*m,2*m-2,2*m-4,2*m-2] for m in range(2,8)] + [
    [9,4,1,2],[16,6,2,2],[10,6,3,4],[15,8,4,4],[21,10,5,4],[28,12,6,4],
    [10,3,0,1],[16,10,6,6],[27,16,10,8]]
assert sorted(p[:4] for p in lemmaP) == sorted(expected)
assert [len(all_feasible),len(rank8),len(lemmaP)] == [30,16,15]
assert [p[:4] for p in rank8 if p not in lemmaP] == [[28,18,12,10]]
for n,k,a,c,theta,m1,m2,rank in all_feasible:
    assert 1+m1+m2 == n and k+m1*theta-2*m2 == 0
    assert k*k+m1*theta*theta+4*m2 == n*k
print("C18 PASS:",tested,"tuples tested; 30 arithmetic-feasible sets, 16 with rank<=8, 15 with k<=16")
print("C18 qualification: SR4 and multiplicity integrality alone leave 34 sets; nonnegative complement parameters remove",[p[:4] for p in complement_rejected])
print("C18 sets:",[p[:4] for p in lemmaP])
# The two later integrality obstructions in Remark 4.14.
obstructions = [[15,8,6,QQ(3)*15/10],[21,10,7,QQ(2)*21/12]]
assert all(z[-1].denominator() != 1 for z in obstructions)
save("c18",["C18"],bounds=dict(n=[4,36],k="1..n-2",a="0..k-1",c="1..k"),tested=tested,
    predicates=["theta=a-c+2 >= 0","k=c+2*theta","k*(k-a-1)=c*(n-k-1)",
    "theta+2 divides 2*n-k-2","m1=(2*n-k-2)/(theta+2)>0","m2=n-1-m1>0",
    "n-2*k+c-2 >= 0","n-2*k+a >= 0"],
    columns=["n","k","a","c","theta","m1","m2","rank_2I_plus_A"],
    SR4_and_integrality_only=raw_feasible,complement_rejected=complement_rejected,
    arithmetic_feasible=all_feasible,rank_at_most_8=rank8,lemma_P=lemmaP,later_integrality_obstructions=obstructions)
