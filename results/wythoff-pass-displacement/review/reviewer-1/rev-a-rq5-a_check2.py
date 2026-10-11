#!/usr/bin/env python3
"""
rev-a-rq5-a_check2.py -- step-2 supplement by REV-A-RQ5-a.
Checks, in a finite range, the two ingredients behind the cited Theorem 5 (Miyadera-Manabe-Fukui):
  (T4/Cor2)  for x>=9 or y>=9:  G1(x,y,1)=0  <=>  G(x,y)=1   (G = ordinary Wythoff Grundy value)
  (T3, Blass-Fraenkel Cor 5.14 as quoted): G=1 positions (a_n,b_n), a_n increasing (a_n<=b_n):
            |b_n - (floor(n phi)+n)| <= 4  and  floor(n phi)-1 <= a_n <= floor(n phi)+2.
G=1 set: (x,y) has G=1 iff (x,y) is not P0 and no option has G=1 (mex=1 <=> 0 in options, 1 not;
a non-P0 position always has a P0 option).  So the G=1 set is the row greedy with P0 forbidden
everywhere, including (0,0); the pass-game P set is the same greedy with (0,0) allowed.
Exact integers only.  Cross-checked against a literal mex computation on a small square.
Usage: timeout 120 python3 -I rev-a-rq5-a_check2.py M NLIT
"""
import sys
import time
from math import isqrt
from array import array

T0 = time.time()


def fphi(n):
    return (n + isqrt(5 * n * n)) // 2


def p0_row(L):
    w = array('q', [-1]) * (L + 1)
    n = 0
    while True:
        A = fphi(n)
        if A > L:
            break
        w[A] = A + n
        if A + n <= L:
            w[A + n] = A
        n += 1
    assert all(v >= 0 for v in w)
    return w


def greedy(M, w, allow00):
    size = 3 * M + 8
    owner = array('i', [-1]) * size
    dused = bytearray(size)
    p = array('q', [0]) * (M + 1)
    d0 = 0
    for a in range(M + 1):
        o = owner[a]
        if o >= 0:
            p[a] = o
            continue
        forb = -1 if (allow00 and a == 0) else w[a]
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
    return p


def literal_grundy(N):
    G = [[0] * (N + 1) for _ in range(N + 1)]
    for a in range(N + 1):
        for b in range(N + 1):
            s = set(G[a - k][b] for k in range(1, a + 1))
            s |= set(G[a][b - k] for k in range(1, b + 1))
            s |= set(G[a - k][b - k] for k in range(1, min(a, b) + 1))
            g = 0
            while g in s:
                g += 1
            G[a][b] = g
    return G


def main():
    M = int(sys.argv[1])
    NL = int(sys.argv[2])
    w = p0_row(3 * M + 40)
    p1 = greedy(M, w, allow00=True)      # pass game, pass unused
    g1 = greedy(M, w, allow00=False)     # Wythoff Grundy value 1
    print("[%.1fs] greedy sets built for rows 0..%d" % (time.time() - T0, M), flush=True)
    G = literal_grundy(NL)
    for a in range(NL + 1):
        for b in range(NL + 1):
            assert (G[a][b] == 1) == (g1[a] == b), ("literal G=1 != greedy", a, b)
            assert (G[a][b] == 0) == (w[a] == b)
    print("[%.1fs] literal mex Grundy on [0..%d]^2: G=0 and G=1 sets == formula / greedy: OK" % (time.time() - T0, NL))
    # Theorem 4 / Corollary 2 of the source, finite check
    bad = []
    small_diff = []
    for a in range(M + 1):
        x, y1, y2 = a, p1[a], g1[a]
        if y1 != y2:
            # the two sets differ in row a; the source's claim needs both positions to be small
            if not (x <= 8 and y1 <= 8 and y2 <= 8):
                bad.append((a, y1, y2))
            else:
                small_diff.append((a, y1, y2))
    print("T4/Cor2 (rows 0..%d): rows where P1 and G=1 differ: small (x,y<=8) %s ; with x>=9 or y>=9: %d %s"
          % (M, small_diff, len(bad), bad[:10]))
    # Theorem 3 (Blass-Fraenkel bounds as quoted), finite check on G=1 positions with a<=b, a increasing
    seq = [(a, g1[a]) for a in range(M + 1) if g1[a] >= a]
    worst_b = (0, None)
    worst_a = (0, None)
    viol = []
    for n, (an, bn) in enumerate(seq):
        A = fphi(n)
        eb = bn - (A + n)
        ea = an - A
        if abs(eb) > worst_b[0]:
            worst_b = (abs(eb), (n, an, bn))
        if ea < -1 or ea > 2:
            viol.append((n, an, bn, ea, eb))
        if abs(eb) > 4:
            viol.append((n, an, bn, ea, eb))
        worst_a = (max(worst_a[0], ea), worst_a[1]) if ea <= worst_a[0] else (ea, (n, an, bn))
    print("first G=1 positions (a<=b):", seq[:12])
    mn = min(an - fphi(n) for n, (an, bn) in enumerate(seq))
    mxa = max(an - fphi(n) for n, (an, bn) in enumerate(seq))
    print("T3 (Blass-Fraenkel bounds as quoted), %d G=1 positions with a<=b, a<=%d: a_n-floor(n phi) in [%d,%d]; "
          "max |b_n-(floor(n phi)+n)| = %d at (n,a,b)=%s; violations: %d %s"
          % (len(seq), M, mn, mxa, worst_b[0], worst_b[1], len(viol), viol[:5]))
    print("[%.1fs] SUMMARY check2: T4/Cor2 exceptions with x>=9 or y>=9: %d; T3 violations: %d (rows 0..%d)"
          % (time.time() - T0, len(bad), len(viol), M))


if __name__ == "__main__":
    main()
