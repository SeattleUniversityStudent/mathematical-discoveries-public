from functools import lru_cache
from fractions import Fraction as Fr
import itertools, json
# F(k,n,p): Carlitz compositions of n with k parts, first part != p (p=0: no restriction)
@lru_cache(None)
def F(k,n,p):
    if k==0: return 1 if n==0 else 0
    return sum(F(k-1,n-q,q) for q in range(1,n+1) if q!=p)
def minsum(k,p):
    if k==0: return 0
    if k%2==0: return 3*k//2
    return (3*k+1)//2 if p==1 else (3*k-1)//2
# brute check vs literal
def comps(k,n):
    if k==0: return [[]] if n==0 else []
    return [[i]+l for i in range(1,n+1) for l in comps(k-1,n-i)]
lit=lambda n,k: sum(all(a!=b for a,b in zip(l,l[1:])) for l in comps(k,n))
for n in range(0,11):
    for k in range(0,8): assert lit(n,k)==F(k,n,0)
# slack values: base for parity uses unrestricted min (3k-1)//2 odd, 3k//2 even
def base(k): return 3*k//2 if k%2==0 else (3*k-1)//2
S=4; P=8
def interp(xs,ys):
    # Lagrange -> coefficients (Fractions), degree<=len-1
    n=len(xs); coef=[Fr(0)]*n
    for i in range(n):
        num=[Fr(1)]; den=Fr(1)
        for j in range(n):
            if j==i: continue
            num=[ (num[t-1] if t>0 else 0) - xs[j]*(num[t] if t<len(num) else 0) for t in range(len(num)+1)]
            den*= (xs[i]-xs[j])
        for t in range(len(num)): coef[t]+= ys[i]*num[t]/den
    return coef
res={}
for par in (0,1):
  for s in range(S+1):
    for p in range(P):
      ks=[k for k in range(2,60) if k%2==par]
      vals=[F(k,base(k)+s,p) for k in ks]
      # fit using j=k//2 index, degree<=6, from k>=K0; find smallest K0 s.t. poly fits all
      for K0i in range(0,8):
        xs=[k//2 for k in ks[K0i:K0i+8]]; ys=vals[K0i:K0i+8]
        c=interp(xs,ys)
        while len(c)>1 and c[-1]==0: c.pop()
        ok=all(sum(cc*(k//2)**t for t,cc in enumerate(c))==v for k,v in zip(ks[K0i:],vals[K0i:]))
        if ok and len(c)<=6: res[(par,s,p)]=(ks[K0i],[str(x) for x in c]); break
      else: res[(par,s,p)]=None
for key,v in res.items(): print(key,v)
