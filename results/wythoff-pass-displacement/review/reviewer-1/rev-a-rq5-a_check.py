#!/usr/bin/env python3
"""
rev-a-rq5-a_check.py  --  independent finite check by reviewer REV-A-RQ5-a.

Written from the definitions in STATEMENT.md only.

Game: two heaps (a,b) plus a flag f (f=1: the single shared pass is still available).
Moves: reduce one heap by k>0; reduce both heaps by the same k>0; if f=1 and (a,b)!=(0,0),
pass: (a,b,1) -> (a,b,0).  Normal play.  P position = loss for the player to move.

  P0 = P positions with f=0 (ordinary Wythoff Nim).
  P1 = P positions with f=1 (the object of the main statement).

Recursion: (a,b,1) is P  <=>  no Wythoff move from (a,b) reaches a P1 position, and
           either (a,b)=(0,0) or (a,b) is not in P0 (the pass option leads to (a,b,0)).

Everything is exact integer arithmetic.  floor(phi*n) = (n + isqrt(5 n^2)) // 2 (proof printed below).

Usage: timeout 120 python3 -I rev-a-rq5-a_check.py M N2 N3
  M  : rows 0..M of the pass game are computed exactly (all b), so every P1 position with
       min(a,b) <= M is found; in particular every P1 position in the square [0..M]^2.
  N2 : side of the square for the independent O(N2^2) row/column/diagonal scan (cross-check).
  N3 : side of the square for the literal move-by-move computation (cross-check).
"""
import sys
import time
from math import isqrt
from array import array
import numpy as np

T0 = time.time()


def log(*a):
    print(*a, flush=True)


def el():
    return "%.1fs" % (time.time() - T0)


# ----------------------------------------------------------------------------- exact floor(phi*n)
def fphi(n):
    """floor(phi*n), exact, for any integer n (negative allowed)."""
    if n >= 0:
        return (n + isqrt(5 * n * n)) // 2
    m = -n  # phi*n = -phi*m, which is irrational for m>0, so floor = -floor(phi*m) - 1
    return -((m + isqrt(5 * m * m)) // 2) - 1


def fphi_vec(n):
    """Vectorized exact floor(phi*n) for an int64 array 0 <= n < 1e9.
    A float64 sqrt is used only as a first guess; the integer square root s is then corrected
    and *verified* in exact int64 arithmetic (s^2 <= 5n^2 < (s+1)^2; no overflow below 1e9)."""
    n = np.asarray(n, dtype=np.int64)
    assert n.size == 0 or (n.min() >= 0 and n.max() < 10**9)
    t = 5 * n * n
    s = np.floor(np.sqrt(t.astype(np.float64))).astype(np.int64)
    for _ in range(4):
        s = np.where(s * s > t, s - 1, s)
        s = np.where((s + 1) * (s + 1) <= t, s + 1, s)
    assert np.all(s * s <= t) and np.all((s + 1) * (s + 1) > t), "isqrt verification failed"
    return (n + s) // 2


# ----------------------------------------------------------------------------- ordinary Wythoff table
def wythoff_table(L):
    """A[n] = floor(phi n) for n = 0..nmax (with A[nmax] > L), and w[x] = the unique y with
    (x,y) in P0, for x = 0..L.  Uses the stated formula (floor(phi n), floor(phi n)+n) and mirrors."""
    nmax = (2 * L) // 3 + 10            # 1/phi < 2/3, so A[nmax] > L
    n = np.arange(nmax + 1, dtype=np.int64)
    A = fphi_vec(n)
    # spot-check the vectorized values against math.isqrt on a prefix and the tail
    for i in list(range(0, min(nmax + 1, 200001))) + list(range(max(0, nmax - 200000), nmax + 1)):
        assert int(A[i]) == fphi(i), ("fphi mismatch", i)
    assert int(A[-1]) > L
    B = A + n
    w = np.full(L + 1, -1, dtype=np.int64)
    mA = A <= L
    w[A[mA]] = B[mA]
    mB = B <= L
    w[B[mB]] = A[mB]
    # Beatty complementarity on 1..L: every x>=1 is exactly one A_n or B_n (n>=1)
    vals = np.concatenate([A[1:][A[1:] <= L], B[1:][B[1:] <= L]])
    cnt = np.bincount(vals, minlength=L + 1)
    assert cnt[0] == 0 and np.all(cnt[1:] == 1), "Beatty complementarity check failed"
    assert np.all(w >= 0)
    return A, w


# ----------------------------------------------------------------------------- method 1: exact row greedy
def row_greedy(M, wl, use_pass):
    """Exact P set (f=1 if use_pass, else f=0) for rows a = 0..M, all b >= 0.
    Returns array p with (a, p[a]) the unique P position of row a.

    Facts used (all elementary):
      * each row/column/diagonal contains at most one P position (two would be joined by a move);
      * the P set is symmetric under (a,b)->(b,a) (the rules and the pass-forbidden set P0 are);
      * so if some earlier row a'<a has its P at column a, row a's P is (a,a');
        otherwise row a's P has b >= a and is the least b >= a whose column has no P in rows < a,
        whose diagonal b-a has no P below it, and (pass game, a>0) with (a,b) not in P0.
      * at most a columns + a diagonals + 1 forbidden cell are blocked, so b <= 3a+1: the search ends.
    """
    size = 3 * M + 8
    owner = array('i', [-1]) * size       # owner[c] = row a' whose P (a',c) has c >= a'
    dused = bytearray(size)               # diagonal d = b-a >= 0 already holds a P
    p = array('q', [0]) * (M + 1)
    d0 = 0                                # least unused diagonal
    for a in range(M + 1):
        o = owner[a]
        if o >= 0:
            p[a] = o
            continue
        forb = wl[a] if (use_pass and a > 0) else -1
        d = d0
        while True:
            if dused[d]:
                d += 1
                continue
            b = a + d
            if owner[b] >= 0 or b == forb:
                d += 1
                continue
            break
        p[a] = b
        owner[b] = a
        dused[d] = 1
        while dused[d0]:
            d0 += 1
    return np.frombuffer(p, dtype=np.int64).copy()


# ----------------------------------------------------------------------------- method 2: O(N^2) square scan
def square_scan(N, wl, use_pass):
    """Independent scan of the square [0..N]^2 in lexicographic order with row/column/diagonal flags.
    Does NOT assume symmetry.  Returns prow[a] = b of the P position in row a inside the square, or -1."""
    col = bytearray(N + 1)
    diag = bytearray(2 * N + 1)
    prow = [-1] * (N + 1)
    for a in range(N + 1):
        forb = wl[a] if (use_pass and a > 0) else -1
        for b in range(N + 1):            # row flag: after the first P in the row, the rest are N
            if col[b] or diag[b - a + N] or b == forb:
                continue
            prow[a] = b
            col[b] = 1
            diag[b - a + N] = 1
            break
    return prow


# ----------------------------------------------------------------------------- method 3: literal move-by-move
def literal(N):
    """Literal evaluation of every state (a,b,f), 0<=a,b<=N, f in {0,1}, enumerating every move
    exactly as defined.  Returns isP[f][a][b]."""
    isP = [[[False] * (N + 1) for _ in range(N + 1)] for _ in range(2)]
    for f in (0, 1):
        for a in range(N + 1):
            for b in range(N + 1):
                opts = []
                opts += [(f, a - k, b) for k in range(1, a + 1)]
                opts += [(f, a, b - k) for k in range(1, b + 1)]
                opts += [(f, a - k, b - k) for k in range(1, min(a, b) + 1)]
                if f == 1 and (a, b) != (0, 0):
                    opts.append((0, a, b))
                isP[f][a][b] = not any(isP[g][x][y] for (g, x, y) in opts)
    return isP


# ----------------------------------------------------------------------------- nearest P0 distance
def nearest_p0_d2(a, b, w, L):
    """Exact min over all P0 points (x, w[x]) of (x-a)^2 + (w[x]-b)^2.
    Every row x>=0 holds exactly one P0 point, so P0 = {(x, w[x])}.  Scan rows |x-a|<=k; if the
    best value found is <= (k+1)^2, rows further away cannot do better, so it is exact; else double k."""
    big = np.int64(1) << 62
    res = np.empty(len(a), dtype=np.int64)
    pend = np.arange(len(a))
    k = 4
    while len(pend):
        aa = a[pend]
        bb = b[pend]
        best = np.full(len(pend), big, dtype=np.int64)
        for dx in range(-k, k + 1):
            x = aa + dx
            ok = x >= 0
            assert np.all(x[ok] <= L)
            xs = np.where(ok, x, 0)
            d2 = dx * dx + (w[xs] - bb) ** 2
            best = np.minimum(best, np.where(ok, d2, big))
        done = best <= (k + 1) ** 2
        res[pend[done]] = best[done]
        pend = pend[~done]
        k *= 2
    return res


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    N2 = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    N3 = int(sys.argv[3]) if len(sys.argv) > 3 else 80
    assert N3 <= N2 <= M
    log("REV-A-RQ5-a check: Wythoff Nim with one shared pass")
    log("parameters: M=%d (rows 0..M exact, all b), N2=%d (square scan), N3=%d (literal)" % (M, N2, N3))
    log("python", sys.version.split()[0], "numpy", np.__version__)
    log("")
    log("Exactness of floor(phi*n): s = isqrt(5n^2) satisfies s < n*sqrt5 < s+1 for n>0 (sqrt5 irrational),")
    log("  so (n+s)/2 < phi*n < (n+s+1)/2, an open interval of length 1/2 containing no integer in its")
    log("  interior other than possibly (n+s+1)/2 itself (excluded) -> floor(phi n) = (n+s)//2.")
    log("Exactness of the computed region: every move strictly decreases a+b or removes the pass, so the")
    log("  status of (a,b,f) depends only on states with smaller coordinates; rows 0..M are computed in full")
    log("  (no truncation in b), hence every P1 position with min(a,b) <= M is found exactly, which includes")
    log("  every P1 position in the square [0..M]^2.  No floating point enters any decision.")
    log("")

    L = 3 * M + 40
    A, w = wythoff_table(L)
    wl = array('q', w.tobytes())
    log("[%s] ordinary Wythoff table built for x <= L=%d (Beatty complementarity verified)" % (el(), L))

    # --- method 1
    p0 = row_greedy(M, wl, use_pass=False)
    log("[%s] row greedy, no pass, rows 0..%d done" % (el(), M))
    assert np.array_equal(p0, w[:M + 1]), "no-pass greedy disagrees with the Wythoff formula"
    log("  check: no-pass greedy == formula pairs (floor(phi n), floor(phi n)+n) and mirrors, rows 0..M: OK")
    p1 = row_greedy(M, wl, use_pass=True)
    log("[%s] row greedy, pass unused, rows 0..%d done" % (el(), M))

    # internal consistency of p1: involution where defined, one P per column / diagonal
    idx = np.arange(M + 1, dtype=np.int64)
    inr = p1 <= M
    assert np.all(p1[p1[inr]] == idx[inr]), "pass-game P set not symmetric"
    up = p1 >= idx
    assert len(np.unique(p1[up])) == int(up.sum()) and len(np.unique((p1 - idx)[up])) == int(up.sum())
    assert np.all(p1 <= 3 * idx + 1)
    inter = np.nonzero(p1 == w[:M + 1])[0]
    log("  checks: symmetry, one P per column/diagonal, b <= 3a+1: OK;  P1 ∩ P0 within rows 0..M =",
        [(int(a), int(p1[a])) for a in inter])

    # --- method 2 and 3 cross-checks
    s0 = square_scan(N2, wl, False)
    s1 = square_scan(N2, wl, True)
    for a in range(N2 + 1):
        g0 = int(p0[a]) if p0[a] <= N2 else -1
        g1 = int(p1[a]) if p1[a] <= N2 else -1
        assert s0[a] == g0, ("square scan (no pass) != greedy", a)
        assert s1[a] == g1, ("square scan (pass) != greedy", a)
    log("[%s] O(N^2) square scan on [0..%d]^2 (no symmetry assumed) == row greedy, both games: OK" % (el(), N2))
    lit = literal(N3)
    for a in range(N3 + 1):
        for b in range(N3 + 1):
            assert lit[0][a][b] == (int(w[a]) == b), ("literal f=0 != formula", a, b)
            assert lit[1][a][b] == (s1[a] == b), ("literal f=1 != square scan", a, b)
            assert lit[1][a][b] == (int(p1[a]) == b), ("literal f=1 != greedy", a, b)
    nlit = sum(lit[1][a][b] for a in range(N3 + 1) for b in range(N3 + 1))
    log("[%s] literal move-by-move on [0..%d]^2 x {pass, no pass} == scan == greedy == formula: OK (%d P1 cells)"
        % (el(), N3, nlit))
    log("")

    # --- list of small P1 positions
    small = [(int(a), int(p1[a])) for a in range(min(M, 60) + 1) if p1[a] >= a]
    log("first P1 positions (pass unused, a<=b):", small[:30])
    log("")

    # --- main statement
    a_up = idx[up]
    b_up = p1[up]
    d_up = b_up - a_up
    assert d_up.max() < len(A)
    F = A[d_up]                                   # floor(phi d), exact
    disp = a_up - F
    adisp = np.abs(disp)
    sq = b_up <= M
    mx = int(adisp.max())
    where = np.nonzero(adisp == mx)[0]
    log("MAIN STATEMENT  |a - floor(phi d)| <= 17,  d = b-a,  over P1 positions with a <= b:")
    log("  positions checked: %d with a <= b and a <= M (of which %d lie in the square b <= M)"
        % (len(a_up), int(sq.sum())))
    log("  signed a - floor(phi d): min %d, max %d;  max |.| = %d" % (int(disp.min()), int(disp.max()), mx))
    log("  attained at %d positions; first ones:" % len(where),
        [(int(a_up[i]), int(b_up[i]), int(d_up[i]), int(disp[i])) for i in where[:12]], "(a,b,d,a-floor(phi d))")
    log("  max |.| inside the square [0..M]^2: %d" % int(adisp[sq].max()))
    viol = np.nonzero(adisp > 17)[0]
    log("  violations of the bound 17: %d" % len(viol),
        [(int(a_up[i]), int(b_up[i])) for i in viol[:10]])
    vals, cnts = np.unique(disp, return_counts=True)
    log("  histogram of a - floor(phi d):", dict(zip([int(v) for v in vals], [int(c) for c in cnts])))
    log("  max |a - floor(phi d)| by block of a:")
    lo = 0
    hi = 10
    while lo <= M:
        m = (a_up >= lo) & (a_up < hi)
        if m.any():
            j = np.nonzero(m)[0][np.argmax(adisp[m])]
            log("    a in [%d,%d): %d positions, max %d at (%d,%d)"
                % (lo, hi, int(m.sum()), int(adisp[j]), int(a_up[j]), int(b_up[j])))
        lo, hi = hi, hi * 10
    log("  mirror images: for a P1 position (a,b) with a > b the statement is applied to (b,a), which is")
    log("    itself a P1 position (symmetry verified above), so the a <= b list above covers them.")
    log("  edge cases: (0,0) is P1 (no move: the pass is not allowed at (0,0)); d=0, value 0.")
    log("    Row a=0 contains no other P1 position ((0,b,1)->(0,0,1)).  Diagonal a=b>0 contains none.")
    log("")

    # --- W1
    a_all = idx
    b_all = p1
    d2 = nearest_p0_d2(a_all, b_all, w, L)
    m2 = int(d2.max())
    wh = np.nonzero(d2 == m2)[0]
    log("W1  every P1 position is within squared Euclidean distance 20 of some P0 position:")
    log("  positions checked: all %d rows a = 0..M (both orientations; P1 position (a, p1[a]))" % (M + 1))
    log("  max squared distance to nearest P0 point: %d, attained %d times; first:" % (m2, len(wh)),
        [(int(a_all[i]), int(b_all[i])) for i in wh[:12]])
    log("  max inside the square [0..M]^2: %d" % int(d2[b_all <= M].max()))
    vv, cc = np.unique(d2, return_counts=True)
    log("  histogram of squared distance:", dict(zip([int(v) for v in vv], [int(c) for c in cc])))
    v20 = np.nonzero(d2 > 20)[0]
    log("  violations of W1 (d^2 > 20): %d" % len(v20), [(int(a_all[i]), int(b_all[i])) for i in v20[:10]])
    lo = 0
    hi = 10
    log("  max squared distance by block of a:")
    while lo <= M:
        m = (a_all >= lo) & (a_all < hi)
        if m.any():
            j = np.nonzero(m)[0][np.argmax(d2[m])]
            log("    a in [%d,%d): max %d at (%d,%d)" % (lo, hi, int(d2[j]), int(a_all[j]), int(b_all[j])))
        lo, hi = hi, hi * 10
    log("")

    # --- auxiliary: what W1 would imply for the main statement (exact integer bookkeeping)
    offs = [(dx, dy) for dx in range(-4, 5) for dy in range(-4, 5) if dx * dx + dy * dy <= 20]
    # case (i): near (A_n, A_n+n), a = A_n+dx, d = n+e with e = dy-dx;
    #   floor(phi d) - A_n = floor({phi n} + phi e) in {floor(phi e), floor(phi e)+1}
    bound_i = 0
    arg_i = None
    for dx, dy in offs:
        e = dy - dx
        fe = fphi(e)
        for v in (dx - fe, dx - fe - 1):
            if abs(v) > bound_i:
                bound_i, arg_i = abs(v), (dx, dy)
    # case (ii): near the mirror (A_n+n, A_n) with a <= b forces n <= dy-dx <= 6: enumerate
    bound_ii = 0
    arg_ii = None
    for n in range(0, 12):
        An = fphi(n)
        for dx, dy in offs:
            a_, b_ = An + n + dx, An + dy
            if a_ < 0 or b_ < 0 or a_ > b_:
                continue
            v = abs(a_ - fphi(b_ - a_))
            if v > bound_ii:
                bound_ii, arg_ii = v, (a_, b_, n)
    log("AUXILIARY (W1 => main?): if every P1 point is within d^2<=20 of a P0 point, then")
    log("  near (A_n, A_n+n): |a - floor(phi d)| <= %d (worst offset %s, exact integer case analysis)"
        % (bound_i, arg_i))
    log("  near a mirror (A_n+n, A_n) with a<=b (forces n<=6): <= %d (worst (a,b,n)=%s)" % (bound_ii, arg_ii))
    log("  so W1 would give the main statement with constant %d <= 17." % max(bound_i, bound_ii))
    log("")

    ok_main = len(viol) == 0
    ok_w1 = len(v20) == 0
    import resource
    log("[%s] done; peak RSS %.0f MB" % (el(), resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024))
    log("SUMMARY REV-A-RQ5-a: rows 0..%d exact (all P1 with min(a,b)<=%d; square [0..%d]^2 included); "
        "cross-checks scan[0..%d]^2 + literal[0..%d]^2 OK; main: max|a-floor(phi d)|=%d at (a,b)=(%d,%d) -> bound 17 %s; "
        "W1: max d^2=%d at (%d,%d) -> bound 20 %s"
        % (M, M, M, N2, N3, mx, int(a_up[where[0]]), int(b_up[where[0]]),
           "HOLDS in range" if ok_main else "FAILS",
           m2, int(a_all[wh[0]]), int(b_all[wh[0]]), "HOLDS in range" if ok_w1 else "FAILS"))


if __name__ == "__main__":
    main()
