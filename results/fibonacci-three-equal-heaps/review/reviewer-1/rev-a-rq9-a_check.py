#!/usr/bin/env python3
"""Independent check of RQ9 claims C1-C7 (reviewer REV-A-RQ9-a, step 1).
Standard library only. Game: position (h;r), a move removes t from one heap
with 1<=t<=r and t<=heap; next bound 2t. Empty position loses (normal play).
Grundy values computed by literal mex over legal moves, bound carried
explicitly. A 'capped' variant memoizes r as min(r, max heap) (identical move
set); it is cross-checked against the uncapped literal one."""
import sys, time
from functools import lru_cache
from itertools import combinations_with_replacement
sys.setrecursionlimit(100000)
INF = float('inf')
OUT = []
def log(*a):
    s = ' '.join(str(x) for x in a); print(s); OUT.append(s)

def moves(h, r):
    """All legal moves as (i, t, child_sorted, next_bound); i = heap index."""
    for i, x in enumerate(h):
        for t in range(1, min(r, x) + 1):
            c = list(h); c[i] -= t
            yield i, t, tuple(sorted(c)), 2 * t

def mex(s):
    m = 0
    while m in s: m += 1
    return m

@lru_cache(maxsize=None)
def g_lit(h, r):  # h sorted tuple, r uncapped
    return mex({g_lit(c, nr) for _, _, c, nr in moves(h, r)})

@lru_cache(maxsize=None)
def g_cap(h, r):
    r = min(r, max(h)) if h and max(h) > 0 else 1
    return _g_cap(h, r)
@lru_cache(maxsize=None)
def _g_cap(h, r):
    return mex({g_cap(c, nr) for _, _, c, nr in moves(h, r)})

@lru_cache(maxsize=None)
def win(h, r):  # outcome only, capped r (exact), literal "exists move to P"
    m = max(h) if h else 0
    if m == 0: return False
    r = min(r, m)
    return _win(h, r)
@lru_cache(maxsize=None)
def _win(h, r):
    return any(not win(c, nr) for _, _, c, nr in moves(h, r))

def T_lit(h):
    """Least positive r with (h;r) N, by literal outcome; INF if none.
    For r >= max(h) the move set is constant, so scanning 1..max(h) suffices."""
    m = max(h) if h else 0
    for r in range(1, m + 1):
        if win(h, r): return r
    return INF

@lru_cache(maxsize=None)
def T_rec(h):
    """Claimed recurrence C1, computed purely from itself."""
    best = INF
    for i, x in enumerate(h):
        for t in range(1, x + 1):
            if t >= best: break
            c = list(h); c[i] -= t
            if T_rec(tuple(sorted(c))) > 2 * t:
                best = t; break
    return best

def zeck_smallest(n):
    f = [1, 2]
    while f[-1] <= n: f.append(f[-1] + f[-2])
    last = None
    for x in reversed(f):
        if x <= n: n -= x; last = x
    return last

def sorted_tuples(k, N):
    return list(combinations_with_replacement(range(N + 1), k))

t0 = time.time()
ok_all = {}

# ---- sanity: capped vs literal Grundy on heaps <= 12, r <= 30
bad = 0
for h in sorted_tuples(3, 12):
    for r in range(1, 31):
        if g_lit(h, r) != g_cap(h, r): bad += 1
        if (g_lit(h, r) != 0) != win(h, r): bad += 1
log(f"[sanity] capped vs uncapped Grundy & outcome, 3 heaps <=12, r<=30: mismatches={bad}")

# ---- C1: recurrence vs literal thresholds, and P iff r<T (monotonicity)
for N in (45,):
    bad_T = bad_mono = 0; ex = []
    for k in (1, 2, 3):
        for h in sorted_tuples(k, N):
            if k == 3 and False: pass
            tl = T_lit(h); tr = T_rec(h)
            if tl != tr:
                bad_T += 1
                if len(ex) < 5: ex.append((h, tl, tr))
            m = max(h)
            for r in range(1, m + 3):
                if win(h, r) != (r >= tl): bad_mono += 1
    log(f"[C1] k=1,2,3 heaps, entries<={N}: T_rec!=T_lit count={bad_T}, "
        f"'P iff r<T' violations (r=1..max+2)={bad_mono}; examples={ex}")
    log(f"[C1] T_rec(0,0,0)={T_rec((0,0,0))}")
    ok_all['C1'] = bad_T == 0 and bad_mono == 0 and T_rec((0,0,0)) == INF
log(f"  time {time.time()-t0:.1f}s")

# ---- C2: (n,n;r) P for all r; T(n,n,n)<=n
bad2 = []
for n in range(0, 61):
    for r in range(1, max(n, 1) + 3):
        if win((n, n), r): bad2.append((n, r))
        if win((0, n, n), r): bad2.append(('3heap', n, r))
bad2b = [n for n in range(1, 46) if not T_lit((n, n, n)) <= n]
bad2c = [n for n in range(46, 101) if not T_rec((n, n, n)) <= n]
log(f"[C2] (n,n;r) and (0,n,n;r) N-instances for n<=60, r<=n+2: {bad2[:10]} (count {len(bad2)})")
log(f"[C2] n<=45 with T_lit(n,n,n)>n: {bad2b}; n in 46..100 with T_rec(n,n,n)>n: {bad2c}")
ok_all['C2'] = not bad2 and not bad2b and not bad2c

# ---- C3: Grundy values (literal, uncapped)
c3 = [((6,6,6),1,0), ((0,0,6),1,1), ((5,6,6),2,1), ((4,6,6),2,0),
      ((20,20,20),1,1), ((0,0,20),1,0), ((19,20,20),2,0)]
ok3 = True
for h, r, claim in c3:
    v = g_lit(h, r)
    log(f"[C3] G{h};{r} = {v} ({'P' if v==0 else 'N'}), claimed {claim}: {'ok' if v==claim else 'MISMATCH'}")
    ok3 &= v == claim
ok_all['C3'] = ok3

# ---- C4
def move_list(h, r):
    return [(i, t, c, nr, g_lit(c, nr)) for i, t, c, nr in moves(h, r)]
fm6 = move_list((6,6,6), 1)
log(f"[C4] first moves from (6,6,6;1): {sorted(set((c,nr) for _,_,c,nr,_ in fm6))}")
resp = move_list((5,6,6), 2)
winning = [(i, t, c, nr) for i, t, c, nr, v in resp if v == 0]
log(f"[C4] winning responses from (5,6,6;2) [(heap index in sorted (5,6,6), t, child, bound)]: {winning}")
fm20 = move_list((20,20,20), 1)
kids20 = sorted(set((c, nr, v) for _,_,c,nr,v in fm20))
log(f"[C4] first moves from (20,20,20;1) up to symmetry: {kids20}")
ok4 = (set((c,nr) for _,_,c,nr,_ in fm6) == {((5,6,6),2)}
       and winning and all(i == 0 and t == 1 for i,t,_,_ in winning)
       and len(kids20) == 1 and kids20[0][2] == 0
       and g_lit((6,6,6),1) == 0 and g_lit((0,0,6),1) != 0
       and g_lit((20,20,20),1) != 0 and g_lit((0,0,20),1) == 0)
log(f"[C4] winning response unique and equal to 'one more from smallest heap': "
    f"{len(winning)==1 and winning[0][:2]==(0,1)}")
ok_all['C4'] = ok4

# ---- C5
Tt = [T_lit((n,n,n)) for n in range(1, 9)]
Z = [zeck_smallest(n) for n in range(1, 9)]
T1 = [T_lit((n,)) for n in range(1, 9)]
first_diff = next((n for n in range(1, 200) if T_rec((n,n,n)) != zeck_smallest(n)), None)
log(f"[C5] T(n,n,n), n=1..8: {Tt}")
log(f"[C5] Zeckendorf smallest summand 1..8: {Z}; literal one-heap thresholds: {T1}")
one_heap_bad = [n for n in range(1, 301) if T_rec((n,)) != zeck_smallest(n)]
one_heap_bad_lit = [n for n in range(1, 61) if T_lit((n,)) != zeck_smallest(n)]
log(f"[C5] one-heap T vs Zeckendorf mismatches: literal n<=60 {one_heap_bad_lit}, recurrence n<=300 {one_heap_bad}")
log(f"[C5] first n with T(n,n,n) != Zeckendorf smallest: {first_diff}")
ok_all['C5'] = (Tt == [1,2,3,1,5,6,7,8] and Z == [1,2,3,1,5,1,2,8]
                and T1 == Z and first_diff == 6)
log(f"[C5] extra: T(n,n,n) n=1..40 (recurrence): {[T_rec((n,n,n)) for n in range(1,41)]}")

# ---- C6
cnt6 = sum(1 for _ in combinations_with_replacement(range(81), 3))
log(f"[C6] sorted tuples 0<=a<=b<=c<=80: {cnt6}")
ok_all['C6'] = cnt6 == 91881

# ---- C7
states = inst = inst_distinct = 0; bad7 = 0
for h in sorted_tuples(3, 20):
    for r in range(1, 41):
        states += 1
        mv = list(moves(h, r))
        inst += len(mv)
        inst_distinct += len(set((c, nr) for _, _, c, nr in mv))
        v = g_lit(h, r)
        if (v != 0) != (r >= T_lit(h)): bad7 += 1
        if (v != 0) != (r >= T_rec(h)): bad7 += 1
log(f"[C7] states={states}, legal removal instances (heap index, t)={inst}, "
    f"distinct child positions={inst_distinct}, threshold disagreements={bad7}")
ok_all['C7'] = states == 70840 and inst == 1788710 and bad7 == 0

log("SUMMARY: " + ", ".join(f"{k}={'held' if v else 'FAILED'}" for k, v in ok_all.items()))
log(f"total time {time.time()-t0:.1f}s")
with open('/tmp/rv/rev/RQ9/step1/check_RQ9_output.txt', 'w') as f:
    f.write('\n'.join(OUT) + '\n')
