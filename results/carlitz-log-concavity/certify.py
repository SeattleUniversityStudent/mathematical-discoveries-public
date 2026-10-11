"""Verify the saved rational identities without importing the construction program."""
import json
from pathlib import Path
from math import comb
from fractions import Fraction
P=Path(__file__).resolve().parent
data=json.loads((P/"algebra.json").read_text())
def plus(*ps):
    d={}
    for p in ps:
        for i,v in p.items():d[i]=d.get(i,0)+v
    return {i:v for i,v in d.items() if v}
def times(p,q):
    d={}
    for i,a in p.items():
        for j,b in q.items():d[i+j]=d.get(i+j,0)+a*b
    return {i:v for i,v in d.items() if v}
def scl(p,c):return {i:c*v for i,v in p.items() if c*v}
def one_minus_y(k):
    return {i:(-1)**i*comb(k,i) for i in range(k+1)}
def dp(p):return {i:v for i,v in enumerate(p) if v}
def coeff(num,s,m):return sum(c*comb(m-j+s,s) for j,c in enumerate(num) if m>=j)
N=[[dp(p) for p in row] for row in data["state_numerators"]]
T=[[[0]*7 for _ in range(7)] for _ in range(5)]
for u in range(1,7):
    for v in range(1,7):
        r=u+v-3
        if u==v or r<0 or r>4:continue
        for prev in range(7):
            if prev==0 or prev!=u:T[r][prev][v]+=1
assert T==data["transition_matrices"]
residuals=0
for s in range(5):
    for j in range(7):
        rhs=one_minus_y(s+1) if (s==0 and j==0) else {}
        for r in range(s+1):
            for i in range(7):
                if T[r][i][j]:
                    rhs=plus(rhs,times({1:T[r][i][j]},times(N[s-r][i],one_minus_y(r))))
        assert N[s][j]==rhs,(s,j,N[s][j],rhs)
        residuals+=1
for s in range(5):
    assert plus(*N[s])==dp(data["even_numerators"][s])
    rhs={}
    for r in range(s+1):
        rhs=plus(rhs,times(plus(*(N[s-r][j] for j in range(7) if j!=r+1)),one_minus_y(r)))
    assert rhs==dp(data["odd_numerators"][s])
def polynomial_binomial_s(m_offset,s):
    p={0:Fraction(1)}
    for q in range(1,s+1):p=times(p,{0:Fraction(m_offset+q,q),1:Fraction(1,q)})
    return p
def coefficient_poly(num,s,shift=0):
    return plus(*(scl(polynomial_binomial_s(shift-j,s),v) for j,v in enumerate(num)))
A=coefficient_poly(data["odd_numerators"][1],1)
B=coefficient_poly(data["even_numerators"][2],2)
C=coefficient_poly(data["odd_numerators"][4],4,-1)
assert A=={0:1,1:1};assert B=={1:1,2:3}
assert scl(C,24)=={0:-312,1:426,2:-277,3:114,4:1}
M=plus(times(A,C),scl(times(B,B),-1))
P24=scl(M,24)
assert P24=={0:-312,1:114,2:125,3:-307,4:-101,5:1}
shift={}
for i,c in P24.items():
    shift=plus(shift,{j:c*comb(i,j)*104**(i-j) for j in range(i+1)})
assert shift=={0:6987864,1:120548802,2:4598485,3:65837,4:419,5:1}
assert all(v>0 for v in shift.values())
for m in range(1,104):
    a=coeff(data["odd_numerators"][1],1,m)
    b=coeff(data["even_numerators"][2],2,m)
    c=coeff(data["odd_numerators"][4],4,m-1)
    assert b*b>=a*c
direct=json.loads((P/"counterexample.json").read_text())
assert {k:int(v) for k,v in direct["counts"].items()}=={"207":coeff(data["odd_numerators"][4],4,103),"208":coeff(data["even_numerators"][2],2,104),"209":coeff(data["odd_numerators"][1],1,104)}
result={"status":"PASS","polynomial_state_residuals":residuals,"even_and_odd_projection_identities":10,"transition_entries_compared":245,"closed_form_polynomial_identities":"PASS","positive_integer_shift_certificate":[int(shift[i]) for i in range(6)],"nonfailure_m_1_through_103_in_this_family":"PASS","independent_last_part_counts":"MATCH","global_minimality":"NOT CHECKED"}
(P/"certificate_verification.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))

