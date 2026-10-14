import json
from fractions import Fraction as Fr
exec(open('table.py').read().split('# slack values')[0])
def base(k): return 3*k//2 if k%2==0 else (3*k-1)//2
# need(par_next, s, p) -> list of (par_prev, s', q); par_next parity of k+1; d = base(k+1)-base(k)
def deps(par_next,s,p):
    d = 1 if par_next==1 else 2
    return [ (1-par_next, d+s-q, q) for q in range(1,d+s+1) if q!=p ]
targets=[(1,1,0),(0,2,0),(1,4,0)]
seen=set(); todo=list(targets)
while todo:
    st=todo.pop()
    if st in seen: continue
    seen.add(st); todo+= deps(*st)
print(len(seen),'states; max s',max(s for _,s,_ in seen),'max p',max(p for *_,p in seen))
def interp(xs,ys):
    n=len(xs); coef=[Fr(0)]*n
    for i in range(n):
        num=[Fr(1)]; den=Fr(1)
        for j in range(n):
            if j==i: continue
            num=[ (num[t-1] if t>0 else 0) - xs[j]*(num[t] if t<len(num) else 0) for t in range(len(num)+1)]
            den*= (xs[i]-xs[j])
        for t in range(len(num)): coef[t]+= ys[i]*num[t]/den
    return coef
polys={}
for (par,s,p) in sorted(seen):
    # k = 2j+par, require validity for all j>=2 (k>=4 or 5)
    js=list(range(2,40)); vals=[F(2*j+par, base(2*j+par)+s, p) for j in js]
    c=interp(js[:9],vals[:9])
    while len(c)>1 and c[-1]==0: c.pop()
    assert all(sum(cc*j**t for t,cc in enumerate(c))==v for j,v in zip(js,vals)), (par,s,p)
    c24=[x*24 for x in c]; assert all(x.denominator==1 for x in c24)
    polys[f"{par},{s},{p}"]=[int(x) for x in c24]
json.dump(polys,open('polys.json','w'),indent=0)
print('all states fit for j>=2 (checked to j=39)')
