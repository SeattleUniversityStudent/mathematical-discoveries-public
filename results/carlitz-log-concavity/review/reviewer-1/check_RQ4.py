#!/usr/bin/env python3
"""Independent check of RQ4 (Carlitz compositions, log-concavity failure at n=3m+2, k=2m).
Standard library only, exact integers/Fractions."""
import itertools, sys
from fractions import Fraction

NMAX = 320
out = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); out.append(s)

# ---------- DP layered by length k: f[n][j] = # Carlitz comps of n with k parts ending in j ----------
# f_k(n,j) = T_{k-1}(n-j) - f_{k-1}(n-j, j)
a = [[0]*(NMAX+2) for _ in range(NMAX+1)]   # a[n][k]
a[0][0] = 1
prev = [[0]*(NMAX+1) for _ in range(NMAX+1)]  # k=1
for n in range(1, NMAX+1):
    prev[n][n] = 1
    a[n][1] = 1
k = 1
while True:
    k += 1
    Tprev = [sum(row) for row in prev]
    cur = [[0]*(NMAX+1) for _ in range(NMAX+1)]
    any_nz = False
    for n in range(1, NMAX+1):
        row = cur[n]; s = 0
        for j in range(1, n):
            r = n - j
            v = Tprev[r] - prev[r][j]
            if v:
                row[j] = v; s += v
        if s:
            a[n][k] = s; any_nz = True
    prev = cur
    if not any_nz:
        break
KMAX = k
P("DP done, max k with any nonzero up to n=%d: %d" % (NMAX, KMAX-1))

# ---------- independent method 2 (block inclusion-exclusion GF), for n<=60 ----------
# sum a(n,k) x^n y^k = 1/(1 - sum_{i,j>=1} (-1)^{j-1} y^j x^{ij})
N2 = 60
b = [[0]*(N2+2) for _ in range(N2+1)]
b[0][0] = 1
for n in range(1, N2+1):
    for kk in range(1, n+1):
        s = 0
        for i in range(1, n+1):
            for j in range(1, min(kk, n//i)+1):
                s += (-1)**(j-1) * b[n-i*j][kk-j]
        b[n][kk] = s
ok2 = all(b[n][kk] == a[n][kk] for n in range(N2+1) for kk in range(N2+1))
P("GF block-method cross-check n<=%d:" % N2, ok2)

# ---------- brute force n<=14 ----------
okb = True
for n in range(1, 15):
    cnt = [0]*(n+1)
    for mask in range(1 << (n-1)):
        parts = []; last = 0
        for i in range(1, n):
            if mask >> (i-1) & 1:
                parts.append(i-last); last = i
        parts.append(n-last)
        if all(parts[t] != parts[t+1] for t in range(len(parts)-1)):
            cnt[len(parts)] += 1
    for kk in range(n+1):
        if cnt[kk] != a[n][kk]:
            okb = False; P("BRUTE MISMATCH", n, kk, cnt[kk], a[n][kk])
P("Brute-force cross-check n<=14:", okb)
# total Carlitz numbers sanity (OEIS A003242: 1,1,1,3,4,7,14,23,39,71,124)
P("row totals n=0..10:", [sum(a[n]) for n in range(11)])

# ---------- specific values ----------
x207, x208, x209 = a[314][207], a[314][208], a[314][209]
P("a(314,207)=%d a(314,208)=%d a(314,209)=%d" % (x207, x208, x209))
P("matches stated:", (x207, x208, x209) == (10094513, 32552, 105))
P("32552^2 =", x208**2, " a207*a209 =", x207*x209, " diff =", x208**2 - x207*x209)
P("stated diff -291161 ok:", x208**2 - x207*x209 == -291161)
P("a(314,k)>0 for k>209?", any(a[314][kk] for kk in range(210, NMAX+2)))

# ---------- endpoint formulas ----------
def Cf(m): return Fraction(m**4 + 114*m**3 - 277*m**2 + 426*m - 312, 24)
bad = []
mmax = (NMAX-2)//3
for m in range(1, mmax+1):
    n = 3*m+2
    A, B, C = a[n][2*m+1], a[n][2*m], a[n][2*m-1]
    largest = max(kk for kk in range(NMAX+2) if a[n][kk])
    good = (A == m+1, B == m*(3*m+1), C == Cf(m), largest == 2*m+1)
    if not all(good):
        bad.append((m, good, A, B, C, Cf(m), largest))
P("endpoint formulas: m=2..%d failures:" % mmax, [t for t in bad if t[0] >= 2])
P("m=1 status (outside lemma):", [t for t in bad if t[0] == 1] or "holds")
P("C integrality for m in 1..2000:", all((m**4 + 114*m**3 - 277*m**2 + 426*m - 312) % 24 == 0 for m in range(1, 2001)))

# ---------- polynomial algebra ----------
def pmul(p, q):
    r = [0]*(len(p)+len(q)-1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i+j] += x*y
    return r
def padd(p, q):
    n = max(len(p), len(q)); return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]
def pscale(p, c): return [c*x for x in p]
def ptrim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0: p.pop()
    return p
# coefficient lists low->high
Ap = [1, 1]
Bp = [0, 1, 3]
C24 = [-312, 426, -277, 114, 1]
lhs = ptrim(padd(pmul(Ap, C24), pscale(pmul(Bp, Bp), -24)))  # 24(AC - B^2)
Q = [-312, 114, 125, -307, -101, 1]
P("24(AC-B^2) coeffs (low->high):", lhs, " equals stated quintic:", lhs == Q)

def peval(p, x): return sum(c*x**i for i, c in enumerate(p))
def shift(p, s):  # p(x+s)
    r = [0]
    for c in reversed(p):
        r = padd(pmul(r, [s, 1]), [c])
    return ptrim(r)
Qs = shift(Q, 104)
P("Q(104+t) coeffs (low->high):", Qs, " all >0:", all(c > 0 for c in Qs))
Qs103 = shift(Q, 103)
P("Q(103+t) coeffs:", Qs103)
signs = {m: peval(Q, m) for m in range(-5, 111)}
neg_pos = [m for m in range(1, 104) if peval(Q, m) > 0]
P("m in 1..103 with Q(m)>0:", neg_pos)
P("Q(102),Q(103),Q(104):", peval(Q, 102), peval(Q, 103), peval(Q, 104))
P("m in 0..103 with Q(m)==0:", [m for m in range(0, 104) if peval(Q, m) == 0])
# real roots location by sign changes on a grid (Fractions)
sc = []
prevv = None
for t in range(-400, 4001):
    x = Fraction(t, 20); v = peval(Q, x)
    if prevv is not None and (v == 0 or (v > 0) != (prevv > 0)):
        sc.append(float(x))
    prevv = v
P("approx sign changes of Q on [-20,200] (step .05):", sc)

# ---------- all log-concavity failures within range ----------
fails = []
for n in range(1, NMAX+1):
    ks = [kk for kk in range(NMAX+2) if a[n][kk]]
    lo, hi = min(ks), max(ks)
    for kk in range(lo, hi+1):
        if a[n][kk]**2 < a[n][kk-1]*a[n][kk+1]:
            fails.append((n, kk))
P("number of LC failures n<=%d:" % NMAX, len(fails))
P("smallest n with failure:", fails[0] if fails else None)
P("all failures:", fails)
P("failures not of form (3m+2,2m):", [(n, kk) for n, kk in fails if not (n % 3 == 2 and kk == 2*((n-2)//3))])
for n, kk in fails:
    P("  n=%d k=%d: a(k-1),a(k),a(k+1)=%d,%d,%d; max k=%d" % (n, kk, a[n][kk-1], a[n][kk], a[n][kk+1], max(t for t in range(NMAX+2) if a[n][t])))
# Also check at k = lower boundary internal zeros (a(n,k)=0 between positives?) -> internal zeros
iz = [n for n in range(1, NMAX+1) if any(a[n][kk] == 0 for kk in range(1, max(t for t in range(NMAX+2) if a[n][t])))]
P("rows with internal zeros:", iz)
# check: does row 3m+2 for m in 104..106 fail at k=2m (direct)
P("direct check m=104..106:", [(m, a[3*m+2][2*m]**2 < a[3*m+2][2*m-1]*a[3*m+2][2*m+1]) for m in range(104, mmax+1)])

with open(__file__.replace("check_RQ4.py", "check_RQ4_output.txt"), "w") as fh:
    fh.write("\n".join(out) + "\n")
