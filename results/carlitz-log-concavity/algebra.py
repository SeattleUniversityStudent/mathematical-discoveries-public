"""Exact finite excess transfer calculation; all operations are integer polynomials."""
from math import comb
from fractions import Fraction
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent
def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b):
    out=[0]*max(len(a),len(b))
    for i,x in enumerate(a):out[i]+=x
    for i,x in enumerate(b):out[i]+=x
    return trim(out)
def scale(a,c):return trim([c*x for x in a])
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return trim(out)
def power(a,k):
    out=[1]
    for _ in range(k):out=mul(out,a)
    return out
def numerator_coeff(num,s,m):
    return sum(c*comb(m-j+s,s) for j,c in enumerate(num) if m>=j)
def coefficient_polynomial(num,s,shift=0):
    out=[Fraction(0)]
    for j,c in enumerate(num):
        p=[Fraction(c)]
        for t in range(1,s+1):p=mul(p,[Fraction(shift-j+t,t),Fraction(1,t)])
        out=add(out,p)
    return out
def translate(p,b):
    out=[Fraction(0)]
    for i,c in enumerate(p):
        out=add(out,[c*comb(i,j)*b**(i-j) for j in range(i+1)])
    return out
H=4;V=H+3
T=[]
for r in range(H+1):
    matrix=[[0]*V for _ in range(V)]
    for prev in range(V):
        for v in range(1,V):
            u=r+3-v
            if u>=1 and u!=v and (prev==0 or u!=prev):matrix[prev][v]+=1
    T.append(matrix)
assert all(sum(T[0][i][k]*T[0][k][j] for k in range(V))==T[0][i][j] for i in range(V) for j in range(V))
N=[[[0] for _ in range(V)] for _ in range(H+1)]
for j in range(V):
    N[0][j]=add([1,-1] if j==0 else [0],[0,T[0][0][j]])
for s in range(1,H+1):
    for r in range(1,s+1):
        w=[[0] for _ in range(V)]
        for i in range(V):
            for j in range(V):
                if T[r][i][j]:w[j]=add(w[j],scale(N[s-r][i],T[r][i][j]))
        z=[mul(w[j],[1,-1]) for j in range(V)]
        for i in range(V):
            for j in range(V):
                if T[0][i][j]:z[j]=add(z[j],mul(w[i],[0,T[0][i][j]]))
        factor=mul([0,1],power([1,-1],r-1))
        for j in range(V):N[s][j]=add(N[s][j],mul(z[j],factor))
E=[];O=[]
for s in range(H+1):
    e=[0];o=[0]
    for j in range(V):e=add(e,N[s][j])
    for r in range(s+1):
        term=[0]
        for j in range(V):
            if j!=r+1:term=add(term,N[s-r][j])
        o=add(o,mul(term,power([1,-1],r)))
    E.append(e);O.append(o)
# Numerators are over (1-y)^(s+1); polynomial formulas hold once m is >= numerator degree.
out={"excess_limit":H,"even_numerators":E,"odd_numerators":O,"denominator_rule":"(1-y)^(s+1)","transition_matrices":T,"state_numerators":N}
for kind,nums in [("E",E),("O",O)]:
    for s,num in enumerate(nums):
        print(kind,s,"numerator",num,"eventual polynomial in m",[str(x) for x in coefficient_polynomial(num,s)],flush=True)
# Last three coefficients n=3m+2: a(n,2m+1), a(n,2m), a(n,2m-1).
A=coefficient_polynomial(O[1],1)
B=coefficient_polynomial(E[2],2)
C=coefficient_polynomial(O[4],4,shift=-1)
margin=add(mul(B,B),scale(mul(A,C),-1))
out["n_3m_plus_2"]={"A":[str(x) for x in A],"B":[str(x) for x in B],"C":[str(x) for x in C],"B_squared_minus_AC":[str(x) for x in margin]}
first=None
for m in range(1,10001):
    av=numerator_coeff(O[1],1,m);bv=numerator_coeff(E[2],2,m);cv=numerator_coeff(O[4],4,m-1)
    if bv*bv<av*cv:
        first={"m":m,"n":3*m+2,"middle_k":2*m,"A":str(av),"B":str(bv),"C":str(cv),"margin":str(bv*bv-av*cv)}
        break
out["first_failure_in_this_tail_family"]=first
if first:
    out["negative_margin_shifted_at_first"]=[str(x) for x in translate(scale(margin,-1),first["m"])]
# Reuse previously computed rows. No extension of the full census.
source=P/"reference_coefficients.json"
data=json.loads(source.read_text());checks=0
for row in data["rows"]:
    n=row["n"];counts=[0]+[int(x) for x in row["counts"]]
    for s in range(H+1):
        if (n-s)%3==0:
            m=(n-s)//3
            if m>=1 and 2*m<len(counts):
                assert numerator_coeff(E[s],s,m)==counts[2*m],("E",n,m,s);checks+=1
        if (n-1-s)%3==0:
            m=(n-1-s)//3
            if m>=0 and 2*m+1<len(counts):
                assert numerator_coeff(O[s],s,m)==counts[2*m+1],("O",n,m,s);checks+=1
out["existing_coefficient_comparisons"]=checks
out["input_sha256"]=hashlib.sha256(source.read_bytes()).hexdigest()
out["input_bytes"]=source.stat().st_size
(P/"algebra.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({k:v for k,v in out.items() if k not in ("transition_matrices","state_numerators")},indent=2),flush=True)

