"""Exact last-part count at the specified counterexample."""
from pathlib import Path
from time import perf_counter
import json
P=Path(__file__).resolve().parent;start=perf_counter()
N=314;K=209
tot=[0]*(N+1);tot[0]=1
end=[[0]*(N+1) for _ in range(N+1)]
target={}
for k in range(1,K+1):
    newtot=[0]*(N+1);newend=[[0]*(N+1) for _ in range(N+1)]
    lower_prev=0 if k==1 else (3*(k-1))//2
    for n in range((3*k)//2,N+1):
        for j in range(1,n-lower_prev+1):
            v=tot[n-j]-end[n-j][j]
            assert v>=0
            newend[n][j]=v;newtot[n]+=v
    tot,end=newtot,newend
    if k in (207,208,209):target[k]=tot[N]
a,b,c=target[207],target[208],target[209]
assert (a,b,c)==(10094513,32552,105)
assert b*b<a*c
out={"n":N,"counts":{str(k):str(v) for k,v in target.items()},"middle_square":str(b*b),"neighbor_product":str(a*c),"difference":str(b*b-a*c),"method":"last-part recurrence, exact arbitrary-precision integers","global_minimality":"NOT CHECKED","elapsed_seconds":perf_counter()-start}
(P/"counterexample.json").write_text(json.dumps(out,indent=2)+"\n");print(json.dumps(out,indent=2),flush=True)

