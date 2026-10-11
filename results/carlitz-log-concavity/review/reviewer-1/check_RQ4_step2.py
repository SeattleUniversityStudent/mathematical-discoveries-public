#!/usr/bin/env python3
"""Step-2 supplementary checks (REV-A-RQ4-a). Standard library only."""
from fractions import Fraction
from math import comb
import os
out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)

NMAX = 320
def carlitz_table(NMAX):
    a = [[0]*(NMAX+2) for _ in range(NMAX+1)]; a[0][0] = 1
    prev = [[0]*(NMAX+1) for _ in range(NMAX+1)]
    for n in range(1, NMAX+1): prev[n][n] = 1; a[n][1] = 1
    k = 1
    while True:
        k += 1
        Tp = [sum(r) for r in prev]
        cur = [[0]*(NMAX+1) for _ in range(NMAX+1)]; nz = False
        for n in range(1, NMAX+1):
            s = 0
            for j in range(1, n):
                v = Tp[n-j] - prev[n-j][j]
                if v: cur[n][j] = v; s += v
            if s: a[n][k] = s; nz = True
        prev = cur
        if not nz: return a
a = carlitz_table(NMAX)
def get(n, k): return a[n][k] if 0 <= n <= NMAX and 0 <= k <= NMAX+1 else None

# 1. numerators from DP: E_s(m)=a(3m+s,2m), O_s(m)=a(3m+1+s,2m+1); numerator=(1-y)^{s+1}*series
table_E = {0:[1,1],1:[0,2,2],2:[0,4,2],3:[0,4,8,4,-6,-2],4:[0,6,16,-2,4,-4,-10]}
table_O = {0:[1],1:[1],2:[1,4,-3,-1],3:[1,5,0,-1,-4],4:[1,10,3,-12,2,-3]}
def numer(series, s):
    M = len(series); res = []
    for j in range(M):
        res.append(sum((-1)**i*comb(s+1, i)*series[j-i] for i in range(min(s+1, j)+1)))
    while res and res[-1] == 0: res.pop()
    return res
allok = True
for s in range(5):
    E = [a[3*m+s][2*m] for m in range((NMAX-s)//3+1)]
    O = [a[3*m+1+s][2*m+1] for m in range((NMAX-1-s)//3+1)]
    nE, nO = numer(E, s), numer(O, s)
    okE, okO = nE == table_E[s], nO == table_O[s]
    allok &= okE and okO
    P("s=%d even numerator from DP (%d terms):" % (s, len(E)), nE, okE, "| odd:", nO, okO)
P("All 10 table numerators reproduced from DP (trailing coefficients vanish to m~105):", allok)

# 2. the n=3m+1 family at k=2m: A'=a(3m+1,2m+1)=O_0(m)=1, B'=E_1(m)=4m-2, C'=O_3(m-1)
def Cprime(m):  # valid m>=2
    return comb(m+2,3) + 5*comb(m+1,3) - comb(m-1,3) - 4*comb(m-2,3)
ok = all(a[3*m+1][2*m+1] == 1 and a[3*m+1][2*m] == 4*m-2 and a[3*m+1][2*m-1] == Cprime(m) for m in range(2, (NMAX-1)//3+1))
P("n=3m+1 endpoint values A'=1, B'=4m-2, C'=binomial formula match DP for 2<=m<=%d:" % ((NMAX-1)//3), ok)
# C' as polynomial: compute exact coefficients by interpolation (cubic)
def interp(f, deg, xs):
    # Lagrange -> coefficient list via solving Vandermonde with Fractions
    n = deg+1; A = [[Fraction(x)**j for j in range(n)] + [Fraction(f(x))] for x in xs[:n]]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0); A[c], A[p] = A[p], A[c]
        A[c] = [v / A[c][c] for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f_ = A[r][c]; A[r] = [x - f_*y for x, y in zip(A[r], A[c])]
    return [A[i][n] for i in range(n)]
Cp = interp(Cprime, 3, list(range(10, 20)))
P("C'(m) polynomial coeffs (low->high):", [str(c) for c in Cp])
assert all(sum(c*m**i for i, c in enumerate(Cp)) == Cprime(m) for m in range(2, 500))
# margin M(m) = 6*(A'C' - B'^2) = 6C' - 6(4m-2)^2
Mp = [6*c for c in Cp]; Mp[0] -= 24; Mp[1] += 96; Mp[2] -= 96
Mp = [int(c) for c in Mp]
P("6(A'C'-B'^2) coeffs (low->high):", Mp)
def shift(p, s):
    r = [0]
    for c in reversed(p):
        nr = [0]*(len(r)+1)
        for i, x in enumerate(r): nr[i] += s*x; nr[i+1] += x
        nr[0] += c; r = nr
    while len(r) > 1 and r[-1] == 0: r.pop()
    return r
P("shift m=52+t:", shift(Mp, 52), "all>0:", all(c > 0 for c in shift(Mp, 52)))
P("values m=50..53:", [sum(c*m**i for i, c in enumerate(Mp)) for m in (50, 51, 52, 53)])
P("m in 2..51 with failure (should be none):", [m for m in range(2, 52) if sum(c*m**i for i, c in enumerate(Mp)) > 0])
P("first n in 3m+1 family: n=%d, k=%d, values %d,%d,%d" % (157, 104, a[157][103], a[157][104], a[157][105]))

# 3. Bender-Canfield Example 2: radius of convergence of Carlitz GF
def h(x, J=2000): return sum(x**j/(1+x**j) for j in range(1, J))
def g(x, K=4000): return sum((-1)**(k-1)*x**k/(1-x**k) for k in range(1, K))
def bis(F, lo, hi):
    for _ in range(100):
        mid = (lo+hi)/2
        if (F(lo)-1)*(F(mid)-1) <= 0: hi = mid
        else: lo = mid
    return lo
r1 = bis(h, 0.3, 0.9); r2 = bis(g, 0.3, 0.9)
P("root of sum_j x^j/(1+x^j)=1 : %.10f ; root of paper's g(x,1)=1 : %.10f ; 1/r=%.8f" % (r1, r2, 1/r1))
c = [sum(a[n][k] for k in range(1, NMAX+2)) for n in range(NMAX+1)]
P("DP growth c(n-1)/c(n) at n=320 (estimates r): %.10f" % (c[319]/c[320]))
P("g(0.78397,1) = %.6f (should be 1 if r=0.78397)" % g(0.78397))
# candidate explanations
import math
P("candidates: sqrt(r)=%.6f, r^(1/3)=%.6f, -ln r=%.6f, 1/(1+r)=%.6f, exp(-r)=%.6f, 1-r^2=%.6f, ln(1/r)/ln2... =%.6f" %
  (math.sqrt(r1), r1**(1/3), -math.log(r1), 1/(1+r1), math.exp(-r1), 1-r1*r1, -math.log(r1)/math.log(2)))
# D={+1,-1}, L=R=N : radius via transfer DP
N3 = 200
cnt = [[0]*(N3+2) for _ in range(N3+1)]  # cnt[n][last]
for j in range(1, N3+1): cnt[j][j] += 1
for n in range(1, N3+1):
    for last in range(1, n+1):
        v = cnt[n][last]
        if not v: continue
        for nxt in (last-1, last+1):
            if nxt >= 1 and n+nxt <= N3: cnt[n+nxt][nxt] += v
tot = [sum(r) for r in cnt]
P("D={+-1}, L=R=N growth estimate c(199)/c(200) = %.6f" % (tot[199]/tot[200]))

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "check_RQ4_step2_output.txt"), "w") as fh:
    fh.write("\n".join(out)+"\n")

# 4. constant A in c(n) ~ A r^-n (BC table 0.4563634741 vs KP 0.456387)
P("c(320)*r^320 = %.10f" % (c[320]*r1**320))
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "check_RQ4_step2_output.txt"), "w") as fh:
    fh.write("\n".join(out)+"\n")
