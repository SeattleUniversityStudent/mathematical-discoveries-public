#!/usr/bin/env python3
"""Independent check for RQ1 (cofactor inequality c(A) >= 2D/(n+1)), stdlib only, exact arithmetic."""
import itertools, random, sys, time
from fractions import Fraction as F

T0 = time.time()
random.seed(12345)

def det(M):
    """Bareiss, exact integer determinant."""
    n = len(M)
    if n == 0:
        return 1
    A = [list(r) for r in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for i in range(k + 1, n):
                if A[i][k] != 0:
                    A[k], A[i] = A[i], A[k]; sign = -sign; break
            else:
                return 0
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]

def minor(M, i, j):
    return [r[:j] + r[j + 1:] for k, r in enumerate(M) if k != i]

def analyse(M):
    """Return dict with D, c, inverse (Fractions) or None if singular."""
    n = len(M)
    d = det(M)
    if d == 0:
        return None
    cof = [[(-1) ** (i + j) * det(minor(M, i, j)) for j in range(n)] for i in range(n)]
    inv = [[F(cof[j][i], d) for j in range(n)] for i in range(n)]  # adj/det
    c = max(abs(cof[i][j]) for i in range(n) for j in range(n))
    return dict(D=abs(d), c=c, inv=inv, det=d)

def matmul(X, Y):
    return [[sum(X[i][k] * Y[k][j] for k in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]

def transpose(X):
    return [list(r) for r in zip(*X)]

def is_S(M):
    n = len(M)
    StS = matmul(transpose(M), M)
    for i in range(n):
        for j in range(n):
            target = F(n + 1, 4) * (2 if i == j else 1)
            if StS[i][j] != target:
                return False
    return True

fails = []
def check(cond, msg):
    if not cond:
        fails.append(msg)
        if len(fails) < 20:
            print("FAIL:", msg)

def check_matrix(M, stats):
    n = len(M)
    r = analyse(M)
    if r is None:
        return
    stats['nonsing'] += 1
    D, c, inv = r['D'], r['c'], r['inv']
    # identity check: inv * M == I
    if stats.get('verify_inv', True):
        P = matmul(inv, M)
        check(all(P[i][j] == (1 if i == j else 0) for i in range(n) for j in range(n)), f"inverse wrong {M}")
    maxn = max(abs(x) for row in inv for x in row)
    F2 = sum(x * x for row in inv for x in row)
    bound = F(2 * D, n + 1)
    # main inequality
    check(c >= bound, f"c>=2D/(n+1) fails {M} c={c} D={D}")
    # (i)
    check(F(c, D) == maxn, f"(i) c/D != maxnorm {M}")
    # (ii) maxnorm >= Fnorm/n  <=> n^2 maxn^2 >= F2
    check(n * n * maxn * maxn >= F2, f"(ii) fails {M}")
    # cited Frobenius bound squared
    check(F2 >= F(2 * n, n + 1) ** 2, f"Frobenius bound fails {M} F2={F2}")
    eq = (c == bound)
    S = is_S(M)
    feq = (F2 == F(2 * n, n + 1) ** 2)
    check(eq == S, f"equality <-> S-matrix fails {M} eq={eq} S={S}")
    check(feq == S, f"Frobenius equality <-> S fails {M} feq={feq} S={S}")
    if eq: stats['eq'] += 1
    if S:
        stats['S'] += 1
        # (iii)
        J = [[1] * n for _ in range(n)]
        pred = [[F(2 * (2 * M[j][i] - 1), n + 1) for j in range(n)] for i in range(n)]
        check(pred == inv, f"(iii) fails {M}")
    # min ratio c(n+1)/(2D) tracking
    ratio = F(c * (n + 1), 2 * D)
    if stats['minratio'] is None or ratio < stats['minratio']:
        stats['minratio'] = ratio
    # second smallest (non-equality) ratio
    if not eq and (stats['min_noneq'] is None or ratio < stats['min_noneq']):
        stats['min_noneq'] = ratio

def newstats():
    return dict(nonsing=0, eq=0, S=0, minratio=None, min_noneq=None)

def report(label, st):
    print(f"{label}: nonsingular={st['nonsing']} equality_cases={st['eq']} S_matrices={st['S']} "
          f"min c(n+1)/(2D)={st['minratio']} min_nonequality_ratio={st['min_noneq']}  [{time.time()-T0:.1f}s]")

# also verify: count of S-matrices among ALL binary matrices (incl. singular) equals equality count
for n in (1, 2, 3, 4):
    st = newstats()
    if n == 4:
        st['verify_inv'] = False  # speed; inverse correctness verified at n<=3 and on samples
    S_all = 0
    for bits in itertools.product((0, 1), repeat=n * n):
        M = [list(bits[i * n:(i + 1) * n]) for i in range(n)]
        if is_S(M):
            S_all += 1
        check_matrix(M, st)
    report(f"n={n} exhaustive", st)
    print(f"   S-matrices among all 2^{n*n} binary matrices: {S_all}")
    check(S_all == st['S'], f"singular S-matrix found n={n}")

# random sampling n=5,6 plus biased sampling (dense / sparse)
for n, N in ((5, 15000), (6, 8000), (7, 3000)):
    st = newstats()
    for t in range(N):
        p = random.choice((0.3, 0.5, 0.6, 0.75))
        M = [[1 if random.random() < p else 0 for _ in range(n)] for _ in range(n)]
        check_matrix(M, st)
    report(f"n={n} random({N})", st)

# Hill-climb attack: try to minimise c(n+1)/(2D) over binary matrices
def ratio_of(M):
    r = analyse(M)
    if r is None:
        return None
    return F(r['c'] * (len(M) + 1), 2 * r['D'])

for n in (5, 6, 7, 8):
    best_overall = None
    for restart in range(6 if n < 8 else 3):
        M = [[random.randint(0, 1) for _ in range(n)] for _ in range(n)]
        while ratio_of(M) is None:
            M = [[random.randint(0, 1) for _ in range(n)] for _ in range(n)]
        cur = ratio_of(M)
        for step in range(250):
            i, j = random.randrange(n), random.randrange(n)
            M[i][j] ^= 1
            r = ratio_of(M)
            if r is not None and r <= cur:
                cur = r
            else:
                M[i][j] ^= 1
        st = newstats(); st['verify_inv'] = True
        check_matrix(M, st)
        if best_overall is None or cur < best_overall[0]:
            best_overall = (cur, [row[:] for row in M], is_S(M))
    print(f"n={n} hill-climb min ratio={best_overall[0]} (as float {float(best_overall[0]):.4f}) S-matrix={best_overall[2]}  [{time.time()-T0:.1f}s]")

# S-matrix constructions from Sylvester Hadamard matrices
def sylvester(k):
    H = [[1]]
    for _ in range(k):
        H = [r + r for r in H] + [r + [-x for x in r] for r in H]
    return H

def S_from_H(H):
    # normalize: first row & column all +1 (Sylvester already normalized); delete them; map +1->0, -1->1
    m = len(H)
    return [[1 if H[i][j] == -1 else 0 for j in range(1, m)] for i in range(1, m)]

for k in (1, 2, 3, 4):
    H = sylvester(k)
    S = S_from_H(H)
    n = len(S)
    st = newstats()
    check(is_S(S), f"Sylvester core not S n={n}")
    check_matrix(S, st)
    r = analyse(S)
    print(f"Sylvester order {2**k}: n={n} isS={is_S(S)} D={r['D']} c={r['c']} 2D/(n+1)={F(2*r['D'], n+1)} eq={st['eq']}  [{time.time()-T0:.1f}s]")
    # perturb: permutations of rows/cols remain S; a single flipped entry should break equality
    P = list(range(n)); random.shuffle(P)
    Q = list(range(n)); random.shuffle(Q)
    S2 = [[S[P[i]][Q[j]] for j in range(n)] for i in range(n)]
    st2 = newstats(); check_matrix(S2, st2)
    check(st2['S'] == 1 and st2['eq'] == 1, f"permuted S fails n={n}")
    S3 = [row[:] for row in S]; S3[0][0] ^= 1
    st3 = newstats(); check_matrix(S3, st3)
    print(f"   permuted S: eq={st2['eq']}; one-flip perturbation: nonsing={st3['nonsing']} eq={st3['eq']}")

# Paley-type order 12 Hadamard -> n=11 S-matrix (quadratic residues mod 11)
q = 11
QR = {(x * x) % q for x in range(1, q)}
S11 = [[1 if ((j - i) % q) in QR or False else 0 for j in range(q)] for i in range(q)]
# complement-of-QR-circulant (including diagonal?) try both variants and keep the S one
cands = []
for diag in (0, 1):
    for use_qr in (True, False):
        M = [[(diag if i == j else (1 if (((j - i) % q) in QR) == use_qr else 0)) for j in range(q)] for i in range(q)]
        cands.append(M)
found = [M for M in cands if is_S(M)]
print(f"n=11 QR circulant candidates that are S-matrices: {len(found)}")
for M in found[:1]:
    st = newstats(); check_matrix(M, st)
    print(f"   n=11 S: eq={st['eq']} S={st['S']}")

# n=1 sanity
r = analyse([[1]])
print(f"n=1: A=[1], D={r['D']}, c={r['c']} (empty det), 2D/(n+1)={F(2,2)}, isS={is_S([[1]])}")

# Is the bound c >= 2D/(n+1) also tight / compare with n=2 (no S-matrix): min ratio from exhaustive above
print()
print("TOTAL FAILURES:", len(fails))
print(f"elapsed {time.time()-T0:.1f}s")
