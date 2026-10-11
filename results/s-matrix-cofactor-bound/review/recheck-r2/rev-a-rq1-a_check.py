#!/usr/bin/env python3
"""REV-A-RQ1-a  --  computational check, step 1 (statement only).

Statements under test (from STATEMENT.md in this folder):
  MAIN : A nonsingular binary n x n, D=|det A|, c(A)=max |(n-1)-minor| (c=1 for n=1):
         c(A) >= 2D/(n+1), equality iff A is an S-matrix.
  L1   : A nonsingular real n x n, entries in [0,1]:  Fnorm(A^-1) >= 2n/(n+1),
         equality iff A is an S-matrix.
  L2   : S an S-matrix of order n  =>  S^-1 = 2(2 S^T - J)/(n+1).

Arithmetic policy.  Every verdict (inequality holds / fails / equality) is decided in exact
arithmetic (Python int, fractions.Fraction, or numpy int64 on small bounded integers where
overflow is impossible).  numpy (installed, v2.x) float64 is used ONLY to *propose* an
adjugate that is then certified exactly by the integer identity A*B == D*I, and as a
heuristic guide inside searches whose outputs are re-checked exactly.

Identity used throughout: adj(A) = det(A) A^-1 and |adj(A)_ji| = |minor_ij|, hence
  c(A) = max|adj(A)|,   MAIN  <=>  (n+1) * max|adj| >= 2|det|  <=>  maxnorm(A^-1) >= 2/(n+1).
  L1   <=>  (n+1)^2 * sum(adj^2) >= 4 n^2 det^2.
This identity is cross-checked against literal minors for every binary matrix with n <= 4.
Ratios reported:  R = (n+1) c / (2D)  (MAIN holds iff R >= 1),
                  Q = (n+1)^2 Fnorm(A^-1)^2 / (4 n^2)  (L1 holds iff Q >= 1).
"""
import sys, time, itertools, random, math
from fractions import Fraction
import numpy as np

T0 = time.time()
DEADLINE = 106.0   # self-imposed wall-clock budget (s); sections shrink or skip, and say so


def left():
    return DEADLINE - (time.time() - T0)


SKIPPED = []
RNG = random.Random(20261010)
NPR = np.random.default_rng(20261010)
ANOM = []
TESTED = {}


def say(*a):
    print(*a, flush=True)


def el():
    return "%.1fs" % (time.time() - T0)


def anomaly(msg):
    ANOM.append(msg)
    say("  !! ANOMALY:", msg)


def fmtM(A):
    return "[" + ",".join("".join(str(int(x)) for x in r) for r in A) + "]"


# ----------------------------------------------------------------- exact helpers
def det_bareiss(M):
    n = len(M)
    if n == 0:
        return 1
    A = [list(r) for r in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    A[k], A[r] = A[r], A[k]
                    sign = -sign
                    break
            else:
                return 0
        akk, Ak = A[k][k], A[k]
        for i in range(k + 1, n):
            Ai = A[i]
            aik = Ai[k]
            for j in range(k + 1, n):
                Ai[j] = (Ai[j] * akk - aik * Ak[j]) // prev
        prev = akk
    return sign * A[n - 1][n - 1]


def det_small(M):
    n = len(M)
    if n == 0:
        return 1
    if n == 1:
        return M[0][0]
    if n == 2:
        return M[0][0] * M[1][1] - M[0][1] * M[1][0]
    if n == 3:
        a, b, c = M[0]; d, e, f = M[1]; g, h, i = M[2]
        return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
    return det_bareiss(M)


def inv_frac(M):
    n = len(M)
    A = [[Fraction(x) for x in M[i]] + [Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return None
        if p != c:
            A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        if piv != 1:
            A[c] = [x / piv for x in A[c]]
        rc = A[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * y for x, y in zip(A[r], rc)]
    return [row[n:] for row in A]


def matmul(A, B):
    Bt = list(zip(*B))
    return [[sum(a * b for a, b in zip(r, col)) for col in Bt] for r in A]


def T(A):
    return [list(r) for r in zip(*A)]


def ident(n, d=1):
    return [[d if i == j else 0 for j in range(n)] for i in range(n)]


def is_S(A):
    n = len(A)
    if any(x not in (0, 1) for r in A for x in r):
        return False
    G = matmul(T(A), A)
    return all(4 * G[i][j] == (n + 1) * (2 if i == j else 1) for i in range(n) for j in range(n))


def adj_det(A):
    """(B, D): D = det A exactly (signed), B = adj A exactly, certified A*B == D*I."""
    n = len(A)
    D = det_bareiss(A)
    if D == 0:
        return None, 0
    if n == 1:
        return [[1]], D
    want = ident(n, D)
    try:
        X = np.linalg.inv(np.array(A, dtype=float))
        B = [[int(round(D * X[i][j])) for j in range(n)] for i in range(n)]
        if matmul(A, B) == want:
            return B, D
    except Exception:
        pass
    Xf = inv_frac(A)
    B = [[D * x for x in row] for row in Xf]
    assert all(x.denominator == 1 for row in B for x in row)
    B = [[int(x) for x in row] for row in B]
    assert matmul(A, B) == want
    return B, D


def RQ(A):
    """exact (R, Q, c, D) for a square integer matrix; None if singular."""
    n = len(A)
    B, D = adj_det(A)
    if B is None:
        return None
    c = max(abs(x) for r in B for x in r)
    s2 = sum(x * x for r in B for x in r)
    aD = abs(D)
    return Fraction((n + 1) * c, 2 * aD), Fraction((n + 1) ** 2 * s2, 4 * n * n * D * D), c, aD


def Q_real(A):
    """exact Q for a real (Fraction) matrix; None if singular."""
    n = len(A)
    X = inv_frac(A)
    if X is None:
        return None
    s2 = sum(x * x for r in X for x in r)
    return s2 * Fraction((n + 1) ** 2, 4 * n * n)


# ----------------------------------------------------------------- vectorised exact helpers
def batch_det(M):
    """exact det of each matrix in int64 batch M (B,n,n) by Laplace DP over column subsets."""
    Bn, n, _ = M.shape
    prev = {0: np.ones(Bn, dtype=np.int64)}
    for k in range(n):
        cur = {}
        rowk = M[:, k, :]
        for S, val in prev.items():
            for c in range(n):
                if (S >> c) & 1:
                    continue
                Tm = S | (1 << c)
                pos = bin(S & ((1 << c) - 1)).count("1")
                term = rowk[:, c] * val
                if (k + pos) & 1:
                    term = -term
                if Tm in cur:
                    cur[Tm] += term
                else:
                    cur[Tm] = term
        prev = cur
    return prev[(1 << n) - 1]


def batch_adj(M, D):
    """certified adjugates for nonsingular batch M with exact dets D."""
    n = M.shape[1]
    X = np.linalg.inv(M.astype(np.float64))
    Bm = np.rint(X * D[:, None, None].astype(np.float64)).astype(np.int64)
    P = np.einsum("bij,bjk->bik", M, Bm)
    ok = np.all(P == D[:, None, None] * np.eye(n, dtype=np.int64)[None], axis=(1, 2))
    bad = np.nonzero(~ok)[0]
    for b in bad:
        Bx, Dx = adj_det(M[b].tolist())
        assert Dx == int(D[b])
        Bm[b] = np.array(Bx, dtype=np.int64)
    return Bm, len(bad)


def batch_certified(M):
    """For arbitrary int64 batch: returns (sing, Bm, Dm) with Bm, Dm int64 and M*Bm == Dm*I
    exactly for every nonsingular one (so Bm/Dm == M^-1 exactly); sing = exactly singular."""
    Bn, n, _ = M.shape
    I = np.eye(n, dtype=np.int64)[None]
    Mf = M.astype(np.float64)
    d = np.linalg.det(Mf)
    sing = np.zeros(Bn, dtype=bool)
    Bm = np.zeros_like(M)
    LIM = float(2 ** 50) / max(n, 1)
    good = (np.abs(d) >= 0.5) & (np.abs(d) < LIM)
    Dr = np.where(good, np.rint(np.where(good, d, 0.0)), 0.0).astype(np.int64)
    idx = np.nonzero(good)[0]
    todo = list(np.nonzero(~good)[0])
    if len(idx):
        X = np.linalg.inv(Mf[idx])
        XD = X * Dr[idx][:, None, None].astype(np.float64)
        small = np.abs(XD).max(axis=(1, 2)) < LIM
        Bc = np.rint(np.where(small[:, None, None], XD, 0.0)).astype(np.int64)
        P = np.einsum("bij,bjk->bik", M[idx], Bc)
        ok = small & np.all(P == Dr[idx][:, None, None] * I, axis=(1, 2))
        Bm[idx[ok]] = Bc[ok]
        todo += list(idx[~ok])
    nfb = len(todo)
    fb = []
    for b in todo:
        Bx, Dx = adj_det(M[b].tolist())
        fb.append((b, Bx, Dx))
    big = any(Bx is not None and max(abs(Dx), max(abs(x) for r in Bx for x in r)) >= 2 ** 40 for b, Bx, Dx in fb)
    if big:
        Bm = Bm.astype(object)
        Dr = Dr.astype(object)
    for b, Bx, Dx in fb:
        if Bx is None:
            sing[b] = True
            Dr[b] = 0
        else:
            Bm[b] = np.array(Bx, dtype=object if big else np.int64)
            Dr[b] = Dx
    return sing, Bm, Dr, nfb


def batch_S(M):
    n = M.shape[1]
    G = np.einsum("bki,bkj->bij", M, M)
    target = (n + 1) * (np.eye(n, dtype=np.int64) + 1)
    return np.all(4 * G == target[None], axis=(1, 2))


class Stats:
    def __init__(self, n):
        self.n = n
        self.nonsing = 0
        self.viol = 0
        self.eq = 0
        self.eq_nonS = 0
        self.S = 0
        self.S_noneq = 0
        self.minR = None
        self.argR = None
        self.minRnonS = None
        self.argRnonS = None
        self.violQ = 0
        self.eqQ = 0
        self.eqQ_nonS = 0
        self.minQ = None
        self.argQ = None
        self.minQnonS = None
        self.fallback = 0

    def add_batch(self, M, Bm, Dm):
        """M (B,n,n) binary int64, Bm certified with M*Bm == Dm*I, Dm != 0."""
        n = self.n
        if len(M) == 0:
            return
        mx = max(int(np.abs(Bm).max()), int(np.abs(Dm).max()))
        if Bm.dtype != object and 4 * (mx * (n + 1) * n) ** 2 * 2 >= 2 ** 62:
            Bm = Bm.astype(object)
            Dm = Dm.astype(object)
        c = np.abs(Bm).max(axis=(1, 2))
        aD = np.abs(Dm)
        gap = (n + 1) * c - 2 * aD
        s2 = (Bm * Bm).sum(axis=(1, 2))
        gapQ = (n + 1) ** 2 * s2 - 4 * n * n * aD * aD
        Sm = batch_S(M)
        self.nonsing += len(M)
        self.viol += int((gap < 0).sum())
        eq = gap == 0
        self.eq += int(eq.sum())
        self.eq_nonS += int((eq & ~Sm).sum())
        self.S += int(Sm.sum())
        self.S_noneq += int((Sm & ~eq).sum())
        self.violQ += int((gapQ < 0).sum())
        eqQ = gapQ == 0
        self.eqQ += int(eqQ.sum())
        self.eqQ_nonS += int((eqQ & ~Sm).sum())
        for b in np.nonzero((gap < 0) | (eq & ~Sm) | (gapQ < 0) | (eqQ & ~Sm) | (Sm & ~eq) | (Sm & ~eqQ))[0][:5]:
            anomaly("n=%d matrix %s gap=%d gapQ=%d S=%s" % (n, fmtM(M[b]), gap[b], gapQ[b], Sm[b]))
        rf = ((n + 1) * c).astype(np.float64) / (2.0 * aD.astype(np.float64))
        qf = ((n + 1) ** 2 * s2).astype(np.float64) / (4.0 * n * n * aD.astype(np.float64) ** 2)
        for (vals, mask, attr) in ((rf, None, "R"), (rf, ~Sm, "RnonS"), (qf, None, "Q"), (qf, ~Sm, "QnonS")):
            v = vals if mask is None else np.where(mask, vals, np.inf)
            m = v.min()
            if not np.isfinite(m):
                continue
            cand = np.nonzero(v <= m * (1 + 1e-12))[0]
            best, arg = None, None
            for b in cand[:50]:
                if attr.startswith("R"):
                    fr = Fraction(int((n + 1) * c[b]), int(2 * aD[b]))
                else:
                    fr = Fraction(int((n + 1) ** 2 * s2[b]), int(4 * n * n * aD[b] * aD[b]))
                if best is None or fr < best:
                    best, arg = fr, M[b].copy()
            name = "min" + attr
            old = getattr(self, name)
            if old is None or best < old:
                setattr(self, name, best)
                if attr in ("R", "RnonS", "Q"):
                    setattr(self, "arg" + attr, arg)

    def report(self, label):
        n = self.n
        say("  [%s] n=%d nonsingular processed=%d" % (label, n, self.nonsing))
        say("     MAIN: violations=%d equality=%d (non-S among them=%d) S-matrices=%d (S without equality=%d)"
            % (self.viol, self.eq, self.eq_nonS, self.S, self.S_noneq))
        say("     MAIN: min R=%s (%.6f) at %s ; min R over non-S=%s (%.6f) at %s"
            % (self.minR, float(self.minR), fmtM(self.argR),
               self.minRnonS, float(self.minRnonS) if self.minRnonS is not None else float("nan"),
               fmtM(self.argRnonS) if self.argRnonS is not None else "-"))
        say("     L1(binary): violations=%d equality=%d (non-S=%d) min Q=%s (%.6f) at %s ; min Q non-S=%s"
            % (self.violQ, self.eqQ, self.eqQ_nonS, self.minQ, float(self.minQ), fmtM(self.argQ),
               ("%.6f" % float(self.minQnonS)) if self.minQnonS is not None else "-"))


# ================================================================= SECTION 1: n = 1
say("=" * 78)
say("REV-A-RQ1-a check program; python", sys.version.split()[0], "numpy", np.__version__)
say("SECTION 1  n = 1 edge case")
for a in (0, 1):
    A = [[a]]
    if det_bareiss(A) == 0:
        say("  A=[[0]] singular (excluded by hypothesis)")
        continue
    D = 1
    c = 1  # empty determinant
    say("  A=[[1]]: D=%d c=%d bound 2D/(n+1)=%s  equality=%s  is_S=%s  L2: 2(2*S^T-J)/(n+1)=%s, S^-1=%s"
        % (D, c, Fraction(2 * D, 2), c * 2 == 2 * D, is_S(A), Fraction(2 * (2 * 1 - 1), 2), Fraction(1, 1)))
    if not (c * 2 >= 2 * D and is_S(A)):
        anomaly("n=1 [[1]]")
# L1 at n=1: A=[a], a in (0,1]: Fnorm(A^-1)=1/a, bound 2n/(n+1)=1
bad = 0
for k in range(1, 1001):
    a = Fraction(k, 1000)
    q = Q_real([[a]])
    if q < 1 or (q == 1 and a != 1):
        bad += 1
say("  L1 n=1: 1000 exact values a=k/1000: Q=1/a^2 >=1 always, equality only a=1 -> anomalies:", bad)
TESTED["n1"] = True

# ================================================================= SECTION 2: literal n<=4
say("SECTION 2  exhaustive over ALL 2^(n^2) binary matrices, n=2,3,4, c(A) from literal minors " + el())
SEC2 = {}
SEC3MIN = {}
for n in (2, 3, 4):
    st = dict(nonsing=0, viol=0, eq=0, eq_nonS=0, S=0, S_noneq=0, violQ=0, eqQ=0, eqQ_nonS=0)
    minR = minRn = minQ = None
    argR = argRn = argQ = None
    idmismatch = 0
    for m in range(1 << (n * n)):
        A = [[(m >> (i * n + j)) & 1 for j in range(n)] for i in range(n)]
        D = det_small(A)
        if D == 0:
            continue
        st["nonsing"] += 1
        Mn = [[det_small([row[:j] + row[j + 1:] for k, row in enumerate(A) if k != i]) for j in range(n)]
              for i in range(n)]
        c = max(abs(x) for r in Mn for x in r)
        s2 = sum(x * x for r in Mn for x in r)
        aD = abs(D)
        S = is_S(A)
        R = Fraction((n + 1) * c, 2 * aD)
        Q = Fraction((n + 1) ** 2 * s2, 4 * n * n * aD * aD)
        # cross-check identity c = max|adj| via exact inverse for a subsample
        if m % 7 == 0:
            X = inv_frac(A)
            if max(abs(x) for r in X for x in r) * aD != c:
                idmismatch += 1
        st["S"] += S
        if R < 1:
            st["viol"] += 1
            anomaly("n=%d MAIN violated by %s" % (n, fmtM(A)))
        if R == 1:
            st["eq"] += 1
            if not S:
                st["eq_nonS"] += 1
                anomaly("n=%d MAIN equality at non-S %s" % (n, fmtM(A)))
        elif S:
            st["S_noneq"] += 1
            anomaly("n=%d S-matrix without equality %s" % (n, fmtM(A)))
        if Q < 1:
            st["violQ"] += 1
            anomaly("n=%d L1 violated by %s" % (n, fmtM(A)))
        if Q == 1:
            st["eqQ"] += 1
            if not S:
                st["eqQ_nonS"] += 1
        if minR is None or R < minR:
            minR, argR = R, A
        if not S and (minRn is None or R < minRn):
            minRn, argRn = R, A
        if minQ is None or Q < minQ:
            minQ, argQ = Q, A
    SEC2[n] = st["nonsing"]
    say("  n=%d: %d matrices, nonsingular=%d  %s" % (n, 1 << (n * n), st["nonsing"],
                                                     {k: v for k, v in st.items() if k != "nonsing"}))
    say("     min R=%s at %s ; min R non-S=%s at %s ; min Q=%s at %s ; identity mismatches=%d"
        % (minR, fmtM(argR), minRn, fmtM(argRn), minQ, fmtM(argQ), idmismatch))
say("  (nonsingular counts for comparison with OEIS A046747 as recalled, not looked up: 6, 174, 22560)")

# ================================================================= SECTION 3: vectorised n<=6
say("SECTION 3  exhaustive up to row/column permutation, exact int64 det DP + certified adjugates " + el())
# self-test of batch_det / adj_det against Bareiss and Fractions
mism = 0
for n in range(1, 8):
    M = (NPR.random((300, n, n)) < 0.5).astype(np.int64)
    d = batch_det(M)
    for b in range(300):
        if int(d[b]) != det_bareiss(M[b].tolist()):
            mism += 1
for n in (5, 6, 7):
    for _ in range(40):
        A = [[RNG.randint(0, 1) for _ in range(n)] for _ in range(n)]
        r = adj_det(A)
        X = inv_frac(A)
        if (r[0] is None) != (X is None):
            mism += 1
        elif X is not None and any(Fraction(r[0][i][j], r[1]) != X[i][j] for i in range(n) for j in range(n)):
            mism += 1
say("  self-test batch_det vs Bareiss (2100 matrices) and adj_det vs Fraction inverse (120): mismatches=%d" % mism)
if mism:
    anomaly("self-test mismatch")

for n in (3, 4, 5):
    ROWS = np.array([[(v >> (n - 1 - c)) & 1 for c in range(n)] for v in range(1 << n)], dtype=np.int64)
    Rset = np.array(list(itertools.combinations(range(1, 1 << n), n)), dtype=np.int64)
    M = ROWS[Rset]
    D = batch_det(M)
    nz = D != 0
    M, D = M[nz], D[nz]
    Bm, nfb = batch_adj(M, D)
    st = Stats(n)
    st.add_batch(M, Bm, D)
    SEC3MIN[n] = st.minR
    if n in SEC2 and SEC2[n] != len(M) * math.factorial(n):
        anomaly("n=%d count mismatch between SECTION 2 and SECTION 3" % n)
    say("  n=%d: all %d sets of n distinct nonzero rows (complete up to row order); nonsingular sets=%d -> x n! = %d"
        % (n, len(Rset), len(M), len(M) * math.factorial(n)))
    st.report("rowsets")
say("  (A046747 as recalled: n=5 -> 12514320)")

# n = 6: rows strictly increasing + column weights nondecreasing (complete up to row/col permutation)
n = 6
t6 = time.time()
ROWS = np.array([[(v >> (n - 1 - c)) & 1 for c in range(n)] for v in range(1 << n)], dtype=np.int64)
c4 = np.array(list(itertools.combinations(range(61), 4)), dtype=np.int64)
c4 = c4[np.lexsort((c4[:, 0], c4[:, 1], c4[:, 2], c4[:, 3]))]
Pk = np.array([sum(((v >> (n - 1 - c)) & 1) << (3 * c) for c in range(n)) for v in range(64)], dtype=np.int64)
vals = np.arange(1 << 18)
fld = [(vals >> (3 * c)) & 7 for c in range(n)]
LUT = np.ones(1 << 18, dtype=bool)
for c in range(n - 1):
    LUT &= fld[c] <= fld[c + 1]
kept, total = [], 0
for r0 in range(1, 64):
    for r1 in range(r0 + 1, 64):
        m = 63 - r1
        if m < 4:
            continue
        k = math.comb(m, 4)
        Tl = c4[:k] + (r1 + 1)
        s = Pk[r0] + Pk[r1] + Pk[Tl[:, 0]] + Pk[Tl[:, 1]] + Pk[Tl[:, 2]] + Pk[Tl[:, 3]]
        ok = LUT[s]
        total += k
        if ok.any():
            sel = Tl[ok]
            Rr = np.empty((len(sel), 6), dtype=np.int64)
            Rr[:, 0] = r0
            Rr[:, 1] = r1
            Rr[:, 2:] = sel
            kept.append(Rr)
Rall = np.concatenate(kept)
say("  n=6: row sets enumerated=%d (=C(63,6)=%d), kept with nondecreasing column weights=%d  (%.1fs)"
    % (total, math.comb(63, 6), len(Rall), time.time() - t6))
st6 = Stats(6)
nfb_tot = 0
nonsing6 = 0
for i in range(0, len(Rall), 250000):
    M = ROWS[Rall[i:i + 250000]]
    D = batch_det(M)
    nz = D != 0
    M, D = M[nz], D[nz]
    nonsing6 += len(M)
    Bm, nfb = batch_adj(M, D)
    nfb_tot += nfb
    st6.add_batch(M, Bm, D)
say("  n=6: nonsingular canonical representatives=%d, exact-fallback adjugates=%d  (%.1fs)"
    % (nonsing6, nfb_tot, time.time() - t6))
st6.report("canonical")
SEC3MIN[6] = st6.minR
# distribution of D at n=6 among representatives that attain min R
say("  completeness argument for n=6: every nonsingular A becomes, after sorting columns by weight and then rows")
say("  as binary words, a member of the enumerated family; c, D, maxnorm, Fnorm, S-property are permutation invariant.")
# spot check: random 6x6 binary matrices (not canonicalised) must have R >= reported min
worst = None
for _ in range(400):
    A = [[RNG.randint(0, 1) for _ in range(6)] for _ in range(6)]
    r = RQ(A)
    if r and (worst is None or r[0] < worst):
        worst = r[0]
say("  n=6 spot check, 400 random uncanonicalised matrices: min R=%s (must be >= %s): %s"
    % (worst, st6.minR, worst >= st6.minR))
if worst < st6.minR:
    anomaly("n=6 canonical enumeration incomplete")


# ================================================================= SECTION 4: Plotkin-necessary search
def code_search(n, s, budget):
    """All doubly-lexical (rows strictly increasing as words with column 0 most significant,
    columns strictly increasing with row 0 most significant) binary n x n matrices whose rows
    and columns all have weight >= s and pairwise Hamming distance >= s.
    Returns (leaves, complete, nodes)."""
    top = n - 1
    W = np.array([v for v in range(1, 1 << n) if bin(v).count("1") >= s], dtype=np.int64)
    N = len(W)
    if N < n:
        return [], True, 0
    pc8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)

    def popc(x):
        r = np.zeros_like(x)
        for sh in range(0, n, 8):
            r += pc8[(x >> sh) & 255]
        return r

    compat = [0] * N
    for i in range(N - 1):
        ok = popc(W[i + 1:] ^ W[i]) >= s
        if ok.any():
            bits = np.zeros(N, dtype=bool)
            bits[i + 1:] = ok
            compat[i] = int.from_bytes(np.packbits(bits, bitorder="little").tobytes(), "little")
    Wl = W.tolist()
    leaves, chosen = [], []
    st = {"nodes": 0, "abort": False}
    t0 = time.time()
    Tinit = 0
    for j in range(n - 1):
        Tinit |= 1 << (top - j)

    def rec(k, cand, Tm, cols):
        st["nodes"] += 1
        if (st["nodes"] & 511) == 0 and time.time() - t0 > budget:
            st["abort"] = True
            return
        if k == n:
            if Tm == 0:
                leaves.append(list(chosen))
            return
        rem = n - k - 1
        need = s - rem
        c = cand
        while c:
            low = c & -c
            idx = low.bit_length() - 1
            c ^= low
            v = Wl[idx]
            if (v & ~(v << 1)) & Tm:
                continue
            nc = cand & compat[idx]
            if bin(nc).count("1") < rem:
                continue
            ncols = [cols[j] | (((v >> (top - j)) & 1) << k) for j in range(n)]
            if need > 0:
                if min(x.bit_count() for x in ncols) < need:
                    continue
                okd = True
                for a in range(n):
                    ca = ncols[a]
                    for b in range(a + 1, n):
                        if (ca ^ ncols[b]).bit_count() < need:
                            okd = False
                            break
                    if not okd:
                        break
                if not okd:
                    continue
            nT = Tm & ~(v ^ (v << 1))
            chosen.append(v)
            rec(k + 1, nc, nT, ncols)
            chosen.pop()
            if st["abort"]:
                return

    rec(0, (1 << N) - 1, Tinit, [0] * n)
    return leaves, not st["abort"], st["nodes"]


def leaf_to_mat(rows, n):
    return [[(r >> (n - 1 - j)) & 1 for j in range(n)] for r in rows]


say("SECTION 4  complete search of the only region where MAIN can fail or be tight " + el())
say("  Necessary condition (exact, derived from A X = X A = I with |X_ij| <= 2/(n+1)): every row and column")
say("  of A has weight >= t and every two rows (columns) differ in >= t places, t = ceil((n+1)/2).")
say("  The search below is complete up to row/column permutation (doubly lexical normal form).")
plotkin_ok = True
all_S_leaves = {}
for n in list(range(2, 15)) + [16, 15]:
    t = (n + 2) // 2
    budget = 9.0 if n == 15 else 20.0
    budget = min(budget, max(0.5, left() - 75))
    ts = time.time()
    leaves, complete, nodes = code_search(n, t, budget)
    nS = nEq = nbad = nsing = nnonS = 0
    minnon = None
    for L in leaves:
        A = leaf_to_mat(L, n)
        r = RQ(A)
        S = is_S(A)
        if r is None:
            nsing += 1
            continue
        nS += S
        nEq += (r[0] == 1)
        if not S:
            nnonS += 1
            if minnon is None or r[0] < minnon:
                minnon = r[0]
        if r[0] < 1 or (r[0] == 1) != S:
            nbad += 1
            anomaly("n=%d search leaf R=%s S=%s %s" % (n, r[0], S, fmtM(A)))
    all_S_leaves[n] = [leaf_to_mat(L, n) for L in leaves[:40]]
    say("  n=%2d t=%d: complete=%s nodes=%d leaves=%d (singular %d, S %d, non-S nonsingular %d, min R non-S %s)"
        " R<1: none=%s, R==1 exactly at the S leaves: %s  (%.1fs)"
        % (n, t, complete, nodes, len(leaves), nsing, nS, nnonS,
           ("%.5f" % float(minnon)) if minnon is not None else "-", nbad == 0, nEq == nS, time.time() - ts))
    if not complete and n != 15:
        plotkin_ok = False
TESTED["plotkin_complete_n"] = "2..14,16 (15 partial)"

# relaxed thresholds: complete enumeration of all matrices with maxnorm(A^-1) <= 1/s, i.e. R <= (n+1)/(2s)
say("SECTION 4b relaxed searches: all matrices with R <= (n+1)/(2s) (gap to the nearest non-S matrix) " + el())
for (n, s, bud) in ((5, 2, 3.0), (6, 3, 3.0), (7, 3, 6.0), (8, 4, 4.0), (9, 4, 5.0), (11, 5, 5.0)):
    if left() < 62:
        SKIPPED.append("4b n=%d s=%d" % (n, s))
        say("  n=%2d s=%d SKIPPED (time budget)" % (n, s))
        continue
    bud = min(bud, left() - 60)
    ts = time.time()
    leaves, complete, nodes = code_search(n, s, bud)
    lim = Fraction(n + 1, 2 * s)
    if not leaves:
        say("  n=%2d s=%d (covers R<=%s): complete=%s nodes=%d leaves=0" % (n, s, lim, complete, nodes))
        continue
    Mall = np.array([leaf_to_mat(L, n) for L in leaves], dtype=np.int64)
    sing, Bm, Dm, nfb = batch_certified(Mall)
    st = Stats(n)
    st.add_batch(Mall[~sing], Bm[~sing], Dm[~sing])
    if complete and n in SEC3MIN:
        exp_ = SEC3MIN[n] if SEC3MIN[n] <= lim else None
        got_ = st.minR if (st.minR is not None and st.minR <= lim) else None
        say("  cross-check vs exhaustive SECTION 3 at n=%d: min R with R<=%s  search=%s exhaustive=%s  agree=%s"
            % (n, lim, got_, exp_, got_ == exp_))
        if got_ != exp_:
            anomaly("search/exhaustive disagreement at n=%d" % n)
    say("  n=%2d s=%d (covers all A with R<=%s): complete=%s nodes=%d leaves=%d singular=%d S=%d viol=%d eq(non-S)=%d"
        " min R over non-S=%s %s  (%.1fs)"
        % (n, s, lim, complete, nodes, len(leaves), int(sing.sum()), st.S, st.viol, st.eq_nonS,
           ("%s=%.5f" % (st.minRnonS, float(st.minRnonS))) if st.minRnonS is not None else "none",
           fmtM(st.argRnonS) if st.argRnonS is not None else "", time.time() - ts))


# SECTION 4c: completeness test of code_search against independent enumeration
say("SECTION 4c completeness test of the SECTION 4 search code against independent enumeration " + el())


def alt_canon(rows, n, maxit=200):
    """alternate: sort rows ascending (col 0 most significant), sort columns ascending (row 0 most
    significant); return the fixed point (doubly lexical) or None."""
    for it in range(maxit):
        rows = sorted(rows)
        cols = [sum(((rows[i] >> (n - 1 - j)) & 1) << (n - 1 - i) for i in range(n)) for j in range(n)]
        order = sorted(range(n), key=lambda j: cols[j])
        if order == list(range(n)):
            return tuple(rows), it
        rows = [sum(((r >> (n - 1 - order[jj])) & 1) << (n - 1 - jj) for jj in range(n)) for r in rows]
    return None, maxit


def constraint_filter(M, s):
    """M (B,n,n) binary; keep rows/cols weight >= s and pairwise distances >= s."""
    n = M.shape[1]
    ok = (M.sum(axis=2) >= s).all(axis=1) & (M.sum(axis=1) >= s).all(axis=1)
    for a in range(n):
        for b in range(a + 1, n):
            ok &= (M[:, a, :] != M[:, b, :]).sum(axis=1) >= s
            ok &= (M[:, :, a] != M[:, :, b]).sum(axis=1) >= s
    return ok


for (n, s) in ((4, 1), (5, 2), (5, 3), (6, 3), (6, 4)):
    ts = time.time()
    ROWSn = np.array([[(v >> (n - 1 - c)) & 1 for c in range(n)] for v in range(1 << n)], dtype=np.int64)
    if n <= 5:
        Rset = np.array(list(itertools.combinations(range(1, 1 << n), n)), dtype=np.int64)
    else:
        Rset = Rall  # rows strictly increasing, column weights nondecreasing: one per permutation class
    Mx = ROWSn[Rset]
    keep = constraint_filter(Mx, s)
    Mx = Mx[keep]
    canon = set()
    maxit = 0
    nonconv = 0
    for A in Mx:
        rows = [int(sum(int(A[i][j]) << (n - 1 - j) for j in range(n))) for i in range(n)]
        c_, it = alt_canon(rows, n)
        if c_ is None:
            nonconv += 1
            continue
        maxit = max(maxit, it)
        canon.add(c_)
    leaves, complete, nodes = code_search(n, s, 20.0)
    L = set(tuple(x) for x in leaves)
    missing = len(canon - L)
    if missing or nonconv:
        anomaly("code_search incomplete n=%d s=%d missing=%d nonconv=%d" % (n, s, missing, nonconv))
    say("  n=%d s=%d: independent matrices meeting constraints=%d -> distinct doubly-lexical forms=%d (max sort rounds %d,"
        " non-converged %d); search leaves=%d complete=%s; forms missing from search=%d  (%.1fs)"
        % (n, s, len(Mx), len(canon), maxit, nonconv, len(L), complete, missing, time.time() - ts))

# ================================================================= SECTION 5: S-matrices, L2
say("SECTION 5  S-matrices from Hadamard matrices; L2 and MAIN/L1 equality, exact " + el())


def sylvester(m):
    H = [[1]]
    for _ in range(m):
        H = [r + r for r in H] + [r + [-x for x in r] for r in H]
    return H


def paley_prime(q):
    QR = {(x * x) % q for x in range(1, q)}

    def chi(a):
        a %= q
        return 0 if a == 0 else (1 if a in QR else -1)

    m = q + 1
    Sk = [[0] * m for _ in range(m)]
    for j in range(1, m):
        Sk[0][j] = 1
        Sk[j][0] = -1
    for i in range(q):
        for j in range(q):
            Sk[i + 1][j + 1] = chi(j - i)
    return [[Sk[i][j] + (1 if i == j else 0) for j in range(m)] for i in range(m)]


def paley_gf27():
    # GF(27) = GF(3)[x]/(x^3 + 2x + 1); elements as (a0,a1,a2)
    els = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]

    def mul(u, v):
        p = [0] * 5
        for i in range(3):
            for j in range(3):
                p[i + j] += u[i] * v[j]
        # x^3 = -2x - 1 = x + 2 ; x^4 = x^2 + 2x
        for d in (4, 3):
            co = p[d]
            p[d] = 0
            p[d - 3] += 2 * co
            p[d - 2] += 1 * co
        return tuple(x % 3 for x in p[:3])

    def sub(u, v):
        return tuple((a - b) % 3 for a, b in zip(u, v))

    zero = (0, 0, 0)
    sq = {mul(e, e) for e in els if e != zero}
    assert len(sq) == 13

    def chi(a):
        return 0 if a == zero else (1 if a in sq else -1)

    q = 27
    m = 28
    Sk = [[0] * m for _ in range(m)]
    for j in range(1, m):
        Sk[0][j] = 1
        Sk[j][0] = -1
    for i in range(q):
        for j in range(q):
            Sk[i + 1][j + 1] = chi(sub(els[j], els[i]))
    return [[Sk[i][j] + (1 if i == j else 0) for j in range(m)] for i in range(m)]


def kron(A, B):
    return [[a * b for a in ra for b in rb] for ra in A for rb in B]


def is_hadamard(H):
    m = len(H)
    return all(x in (1, -1) for r in H for x in r) and matmul(H, T(H)) == ident(m, m)


def S_from_H(H, r=0, c=0):
    m = len(H)
    H1 = [[H[i][j] * H[r][j] for j in range(m)] for i in range(m)]
    H2 = [[H1[i][j] * H1[i][c] for j in range(m)] for i in range(m)]
    assert all(H2[r][j] == 1 for j in range(m)) and all(H2[i][c] == 1 for i in range(m))
    return [[1 if H2[i][j] == -1 else 0 for j in range(m) if j != c] for i in range(m) if i != r]


def H_from_S(S):
    n = len(S)
    return [[1] * (n + 1)] + [[1] + [1 - 2 * x for x in S[i]] for i in range(n)]


def L2_check(S):
    n = len(S)
    J = [[1] * n for _ in range(n)]
    M = [[2 * S[j][i] - 1 for j in range(n)] for i in range(n)]  # 2 S^T - J
    k = (n + 1)
    # S^-1 == 2M/(n+1)  <=>  S*M == ((n+1)/2) I  and  M*S == ((n+1)/2) I  (n+1 even)
    a = matmul(S, M) == ident(n, k // 2) if k % 2 == 0 else False
    b = matmul(M, S) == ident(n, k // 2) if k % 2 == 0 else False
    return a and b


Hlist = [("Sylvester", sylvester(m)) for m in (1, 2, 3, 4, 5)]
Hlist += [("Paley q=%d" % q, paley_prime(q)) for q in (3, 7, 11, 19, 23, 31, 43, 47)]
Hlist += [("Paley GF(27)", paley_gf27()), ("H2 x Paley12", kron(sylvester(1), paley_prime(11))),
          ("H2 x Paley20", kron(sylvester(1), paley_prime(19)))]
nS_tested = 0
L2_fail = 0
for name, H in Hlist:
    m = len(H)
    if not is_hadamard(H):
        anomaly("construction %s not Hadamard" % name)
        continue
    n = m - 1
    picks = [(0, 0)] + [(RNG.randrange(m), RNG.randrange(m)) for _ in range(2)]
    res = []
    for (r, c) in picks:
        S = S_from_H(H, r, c)
        variants = [S, T(S)]
        pr = list(range(n)); pc = list(range(n))
        RNG.shuffle(pr); RNG.shuffle(pc)
        variants.append([[S[pr[i]][pc[j]] for j in range(n)] for i in range(n)])
        for V in variants:
            nS_tested += 1
            okS = is_S(V)
            okH = is_hadamard(H_from_S(V))
            okL2 = L2_check(V)
            if not okL2:
                L2_fail += 1
            if n <= 31 and V is S:
                X = inv_frac(V)
                okL2b = all(X[i][j] == Fraction(2 * (2 * V[j][i] - 1), n + 1) for i in range(n) for j in range(n))
            else:
                okL2b = True
            D = det_bareiss(V)
            okD = abs(D) * 2 ** n == (n + 1) ** ((n + 1) // 2) if n > 1 else abs(D) == 1
            if V is S and n <= 31:
                rq = RQ(V)
                okR = rq[0] == 1 and rq[1] == 1
            else:
                okR = True
            res.append(okS and okH and okL2 and okL2b and okD and okR)
            if not (okS and okH and okL2 and okL2b and okD and okR):
                anomaly("%s n=%d: S=%s H=%s L2=%s L2frac=%s D=%s R,Q=%s"
                        % (name, n, okS, okH, okL2, okL2b, okD, okR))
    say("  %-14s order %2d -> S-matrices of order n=%2d: %d variants, all pass (Gram def, Hadamard-def"
        " equivalence, L2 exact, |det|=(n+1)^((n+1)/2)/2^n, R=Q=1): %s" % (name, m, n, len(res), all(res)))
# search-found S-matrices (from SECTION 4) also through L2
cnt = 0
for n, Ls in all_S_leaves.items():
    for A in Ls:
        if is_S(A):
            cnt += 1
            if not (L2_check(A) and is_hadamard(H_from_S(A))):
                anomaly("search S-matrix fails L2 %s" % fmtM(A))
                L2_fail += 1
say("  search-found S-matrices (n=3,7,11,15 partial) passed through L2 and Hadamard reconstruction: %d" % cnt)
nS_tested += cnt
# power check: L2 formula must FAIL for perturbed S
pw = 0
for name, H in Hlist[1:6]:
    S = S_from_H(H)
    n = len(S)
    for _ in range(5):
        i, j = RNG.randrange(n), RNG.randrange(n)
        V = [r[:] for r in S]
        V[i][j] ^= 1
        if L2_check(V) or is_S(V):
            anomaly("power check: perturbed S passes L2")
        r = RQ(V)
        if r is not None and not (r[0] > 1 and r[1] > 1):
            anomaly("one-flip perturbation of S has R or Q <= 1: %s" % fmtM(V))
        pw += 1
say("  power check: %d one-entry perturbations of S-matrices all fail L2 and have R>1, Q>1" % pw)


# ================================================================= SECTION 6: L1 exact targeted tests
say("SECTION 6  L1 on real matrices with entries in [0,1], exact targeted tests " + el())
# (a) rational grids
for n, grid in ((2, [Fraction(k, 4) for k in range(5)]), (3, [Fraction(0), Fraction(1, 2), Fraction(1)])):
    cnt = viol = eq = eqnonS = 0
    minQ, argQ = None, None
    minQnb = None
    for vals in itertools.product(grid, repeat=n * n):
        A = [list(vals[i * n:(i + 1) * n]) for i in range(n)]
        q = Q_real(A)
        if q is None:
            continue
        cnt += 1
        binA = all(x in (0, 1) for x in vals)
        S = binA and is_S([[int(x) for x in r] for r in A])
        if q < 1:
            viol += 1
            anomaly("L1 violated n=%d %s" % (n, A))
        if q == 1:
            eq += 1
            if not S:
                eqnonS += 1
                anomaly("L1 equality at non-S n=%d %s" % (n, A))
        if minQ is None or q < minQ:
            minQ, argQ = q, A
        if not binA and (minQnb is None or q < minQnb):
            minQnb = q
    say("  grid n=%d values %s: nonsingular=%d violations=%d equality=%d (non-S=%d) min Q=%s; min Q non-binary=%s (%.5f)"
        % (n, [str(g) for g in grid], cnt, viol, eq, eqnonS, minQ, minQnb, float(minQnb)))
# (b) exact first-order (KKT) test at S-matrices: gradient of f(A)=||A^-1||_F^2 is G = -2 A^-T A^-1 A^-T;
#     S is a strict local minimiser on [0,1]^(n x n) if G_ij < 0 where S_ij = 1 and G_ij > 0 where S_ij = 0.
for name, H in (("H4", sylvester(2)), ("H8", sylvester(3)), ("P12", paley_prime(11)), ("H16", sylvester(4))):
    S = S_from_H(H)
    n = len(S)
    X = inv_frac(S)
    Xt = T(X)
    G = [[-2 * x for x in r] for r in matmul(matmul(Xt, X), Xt)]
    k = n + 1
    ok = all((G[i][j] < 0) if S[i][j] == 1 else (G[i][j] > 0) for i in range(n) for j in range(n))
    vals1 = sorted({G[i][j] for i in range(n) for j in range(n) if S[i][j] == 1})
    vals0 = sorted({G[i][j] for i in range(n) for j in range(n) if S[i][j] == 0})
    say("  KKT at S (n=%d): strict sign pattern=%s; G on S=1 entries %s (expected -16n/k^3=%s), on S=0 entries %s (expected 16(k+1)/k^3=%s)"
        % (n, ok, [str(v) for v in vals1], Fraction(-16 * n, k ** 3), [str(v) for v in vals0], Fraction(16 * (k + 1), k ** 3)))
    if not ok:
        anomaly("KKT sign pattern fails at S n=%d" % n)
    # (c) random feasible perturbations, exact
    worst = None
    for trial in range(12):
        E = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if RNG.random() < 0.4:
                    u = Fraction(RNG.randint(1, 9), 9)
                    E[i][j] = -u if S[i][j] == 1 else u
        for eps in (Fraction(1, 2), Fraction(1, 10), Fraction(1, 1000), Fraction(1, 10 ** 6)):
            A = [[S[i][j] + eps * E[i][j] for j in range(n)] for i in range(n)]
            q = Q_real(A)
            if q is None:
                continue
            if q <= 1:
                anomaly("L1 perturbation of S n=%d eps=%s Q=%s" % (n, eps, q))
            if worst is None or q < worst:
                worst = q
    say("     12 random feasible directions x eps in {1/2,1/10,1/1000,1e-6}: min Q=%s (>1: %s)"
        % (float(worst), worst > 1))
# (d) two-level family alpha*S + beta*(J-S)
for H in (sylvester(2), sylvester(3), paley_prime(11)):
    S = S_from_H(H)
    n = len(S)
    worst = None
    eqs = []
    for al in (Fraction(1), Fraction(999, 1000), Fraction(9, 10), Fraction(1, 2), Fraction(0)):
        for be in (Fraction(0), Fraction(1, 1000), Fraction(1, 100), Fraction(1, 10), Fraction(1, 3), Fraction(3, 5), Fraction(1)):
            A = [[al if S[i][j] else be for j in range(n)] for i in range(n)]
            q = Q_real(A)
            if q is None:
                continue
            if q < 1:
                anomaly("L1 two-level violation n=%d al=%s be=%s" % (n, al, be))
            if q == 1:
                eqs.append((al, be))
            if (al, be) != (1, 0) and (worst is None or q < worst):
                worst = q
    say("  two-level alpha*S+beta*(J-S), n=%d, 35 (alpha,beta) pairs incl. J-S: equality only at %s; min Q otherwise=%.6f"
        % (n, [(str(a), str(b)) for a, b in eqs], float(worst)))


# (e) convex combinations of row/column-permuted copies of one S-matrix and of its transpose
for H in (sylvester(2), sylvester(3), paley_prime(11)):
    S = S_from_H(H)
    n = len(S)
    worst = None
    cnt = 0
    for trial in range(40):
        mats = []
        for _ in range(RNG.choice((2, 3))):
            pr = list(range(n)); pc = list(range(n))
            RNG.shuffle(pr); RNG.shuffle(pc)
            B = S if RNG.random() < 0.5 else T(S)
            mats.append([[B[pr[i]][pc[j]] for j in range(n)] for i in range(n)])
        w = [Fraction(RNG.randint(1, 9)) for _ in mats]
        tot = sum(w)
        A = [[sum(wk * Mk[i][j] for wk, Mk in zip(w, mats)) / tot for j in range(n)] for i in range(n)]
        if all(x in (0, 1) for r in A for x in r):
            continue
        q = Q_real(A)
        if q is None:
            continue
        cnt += 1
        if q <= 1:
            anomaly("L1 convex combination of S-matrices n=%d Q=%s" % (n, q))
        if worst is None or q < worst:
            worst = q
    say("  convex combinations of 2-3 permuted copies of S / S^T, n=%d: %d non-binary nonsingular cases, min Q=%.6f (>1: %s)"
        % (n, cnt, float(worst), worst > 1))

# ================================================================= SECTION 7: L1 numeric optimisation
say("SECTION 7  L1 heuristic minimisation over [0,1]^(n x n) (projected gradient, float), exact re-check " + el())


def l1_opt(n, starts, iters):
    best = None
    for s in range(starts):
        if s % 2 == 0:
            A = NPR.random((n, n))
        else:
            A = (NPR.random((n, n)) < 0.5) * 0.8 + 0.1 + 0.05 * NPR.random((n, n))
        try:
            X = np.linalg.inv(A)
        except np.linalg.LinAlgError:
            continue
        f = (X * X).sum()
        eta = 0.05
        for it in range(iters):
            G = -2 * X.T @ X @ X.T
            A2 = np.clip(A - eta * G, 0.0, 1.0)
            try:
                X2 = np.linalg.inv(A2)
            except np.linalg.LinAlgError:
                eta *= 0.5
                continue
            f2 = (X2 * X2).sum()
            if f2 < f:
                A, X, f = A2, X2, f2
                eta *= 1.5
            else:
                eta *= 0.4
            if eta < 1e-14:
                break
        if best is None or f < best[0]:
            best = (f, A.copy())
    return best


tl1 = time.time()
for n in range(2, 13):
    if left() < 35:
        SKIPPED.append("7 n>=%d" % n)
        say("  SKIPPED n>=%d (time budget)" % n)
        break
    starts = 16 if n <= 8 else 8
    f, A = l1_opt(n, starts, 600)
    bound2 = (2 * n / (n + 1)) ** 2
    # exact re-check of the rationalised minimiser (snap within 1e-7 of 0/1)
    Af = []
    for i in range(n):
        row = []
        for j in range(n):
            x = float(A[i][j])
            if x < 1e-7:
                row.append(Fraction(0))
            elif x > 1 - 1e-7:
                row.append(Fraction(1))
            else:
                row.append(Fraction(x).limit_denominator(10 ** 7))
        Af.append(row)
    q = Q_real(Af)
    nonbin = sum(1 for r in Af for x in r if x not in (0, 1))
    binA = nonbin == 0
    S = binA and is_S([[int(x) for x in r] for r in Af])
    if q is not None and q < 1:
        anomaly("L1 numeric candidate below bound n=%d Q=%s" % (n, q))
    if q == 1 and not S:
        anomaly("L1 equality at non-S n=%d" % n)
    say("  n=%2d: float min f/bound=%.6f ; exact Q of rationalised minimiser=%.8f ; non-binary entries=%d ; is S=%s"
        % (n, f / bound2, float(q) if q is not None else float("nan"), nonbin, S))
    if time.time() - tl1 > 12:
        say("  (time budget for SECTION 7 reached after n=%d)" % n)
        break


# ================================================================= SECTION 8: MAIN at larger orders
say("SECTION 8  MAIN at larger orders: circulants, neighbourhoods of S, random, hill-climb (exact certification) " + el())


def analyse(M, n, label, verbose=True):
    sing, Bm, Dm, nfb = batch_certified(M)
    keep = ~sing
    st = Stats(n)
    st.add_batch(M[keep], Bm[keep], Dm[keep])
    if verbose:
        say("  %s n=%d: matrices=%d nonsingular=%d viol=%d eq=%d (non-S %d) S=%d minR=%s minR(non-S)=%s L1viol=%d minQ(non-S)=%s fallbacks=%d"
            % (label, n, len(M), st.nonsing, st.viol, st.eq, st.eq_nonS, st.S,
               ("%.5f" % float(st.minR)) if st.minR is not None else "-",
               ("%s=%.5f" % (st.minRnonS, float(st.minRnonS))) if st.minRnonS is not None else "-",
               st.violQ, ("%.5f" % float(st.minQnonS)) if st.minQnonS is not None else "-", nfb))
    return st


# (a) all circulants
for n in range(2, 14):
    rows = np.arange(1 << n)
    first = ((rows[:, None] >> np.arange(n)[None, :]) & 1).astype(np.int64)
    M = np.stack([np.roll(first, i, axis=1) for i in range(n)], axis=1)
    analyse(M, n, "all circulants      ")
# (b) exhaustive single- and double-flip neighbourhoods of S-matrices
for name, H in (("H8", sylvester(3)), ("P12", paley_prime(11)), ("H16", sylvester(4)), ("P20", paley_prime(19)),
                ("P24", paley_prime(23))):
    S = np.array(S_from_H(H), dtype=np.int64)
    n = len(S)
    idx = np.arange(n * n)
    M = np.repeat(S[None], n * n, axis=0)
    M[idx, idx // n, idx % n] ^= 1
    analyse(M, n, "S single flips (%s)" % name)
    if n <= 11:
        pairs = np.array(list(itertools.combinations(range(n * n), 2)), dtype=np.int64)
        M = np.repeat(S[None], len(pairs), axis=0)
        ar = np.arange(len(pairs))
        M[ar, pairs[:, 0] // n, pairs[:, 0] % n] ^= 1
        M[ar, pairs[:, 1] // n, pairs[:, 1] % n] ^= 1
        analyse(M, n, "S double flips (%s)" % name)
# (c) random binary matrices
for n in (7, 8, 9, 10, 11, 12, 15, 16, 19, 20, 24, 31):
    if left() < 14:
        SKIPPED.append("8c n>=%d" % n)
        say("  random n>=%d SKIPPED (time budget)" % n)
        break
    allst = []
    for p in (0.3, 0.5, 0.7):
        M = (NPR.random((150, n, n)) < p).astype(np.int64)
        allst.append(analyse(M, n, "", verbose=False))
    viol = sum(s.viol for s in allst)
    eqn = sum(s.eq_nonS for s in allst)
    mins = [s.minR for s in allst if s.minR is not None]
    say("  random n=%2d (450 matrices, densities .3/.5/.7): nonsingular=%d violations=%d non-S equalities=%d min R=%.5f L1 viol=%d"
        % (n, sum(s.nonsing for s in allst), viol, eqn, float(min(mins)), sum(s.violQ for s in allst)))


# (d) hill-climb minimising maxnorm(A^-1) by single flips (float guide), exact check of endpoints
def obj_batch(Ms):
    d = np.linalg.det(Ms)
    good = np.abs(d) > 0.5
    out = np.full(len(Ms), np.inf)
    if good.any():
        X = np.linalg.inv(Ms[good])
        out[good] = np.abs(X).max(axis=(1, 2))
    return out


def hill(A, max_steps=200):
    n = A.shape[0]
    cur = obj_batch(A[None].astype(float))[0]
    idx = np.arange(n * n)
    plateau = 0
    for _ in range(max_steps):
        Ms = np.repeat(A[None], n * n, axis=0)
        Ms[idx, idx // n, idx % n] ^= 1
        v = obj_batch(Ms.astype(float))
        m = v.min()
        if m < cur - 1e-12:
            j = RNG.choice(list(np.nonzero(v <= m + 1e-12)[0]))
            A, cur = Ms[j], m
            plateau = 0
        elif m <= cur + 1e-12 and plateau < 15:
            j = RNG.choice(list(np.nonzero(v <= cur + 1e-12)[0]))
            A = Ms[j]
            plateau += 1
        else:
            break
    return A, cur


th = time.time()
for n in (7, 8, 9, 10, 11, 12, 13, 14, 15, 16):
    if left() < 2:
        SKIPPED.append("8d n>=%d" % n)
        say("  hill-climb n>=%d SKIPPED (time budget)" % n)
        break
    ends = []
    starts = 6 if n <= 11 else 3
    for s in range(starts):
        A0 = (NPR.random((n, n)) < 0.6).astype(np.int64)
        A, v = hill(A0)
        ends.append(A)
    if n in (7, 11, 15):
        S = np.array(S_from_H(sylvester(3) if n == 7 else (paley_prime(11) if n == 11 else sylvester(4))), dtype=np.int64)
        for s in range(3):
            A0 = S.copy()
            for _ in range(3):
                A0[RNG.randrange(n), RNG.randrange(n)] ^= 1
            A, v = hill(A0)
            ends.append(A)
    st = analyse(np.array(ends), n, "hill-climb endpoints", verbose=False)
    say("  hill-climb n=%2d: endpoints=%d (S-matrices reached=%d) violations=%d non-S equalities=%d min R non-S=%s"
        % (n, len(ends), st.S, st.viol, st.eq_nonS,
           ("%s=%.5f" % (st.minRnonS, float(st.minRnonS))) if st.minRnonS is not None else "-"))
    if time.time() - th > 10:
        say("  (time budget for hill-climb reached after n=%d)" % n)
        break

# ================================================================= SECTION 9: literal minors at n>=5
say("SECTION 9  c(A) from literal (n-1)-minors (Bareiss) vs adjugate route, n=5..12 " + el())
mm = 0
cases = 0
lit_list = [S_from_H(sylvester(3)), S_from_H(paley_prime(11))]
for n in range(5, 13):
    for _ in range(6):
        lit_list.append([[RNG.randint(0, 1) for _ in range(n)] for _ in range(n)])
for A in lit_list:
    n = len(A)
    D = det_bareiss(A)
    if D == 0:
        continue
    minors = [abs(det_bareiss([row[:j] + row[j + 1:] for k, row in enumerate(A) if k != i])) for i in range(n) for j in range(n)]
    r = RQ(A)
    cases += 1
    if max(minors) != r[2] or abs(D) != r[3]:
        mm += 1
        anomaly("literal minor mismatch %s" % fmtM(A))
    if is_S(A) and Fraction((n + 1) * max(minors), 2 * abs(D)) != 1:
        anomaly("literal minors: S-matrix without equality")
say("  %d nonsingular matrices (incl. S-matrices of orders 7 and 11): mismatches=%d" % (cases, mm))

# ================================================================= SECTION 10: counting table
say("SECTION 10 analytic cross-check (not part of the search): Plotkin-type counting on the region of SECTION 4")
say("  rows of A plus the zero word = m=n+1 words of length n, pairwise distance >= t=ceil((n+1)/2).")
say("  Sum of pairwise distances <= n*floor(m/2)*ceil(m/2) (column count); needs >= C(m,2)*t.")
imp, tight = [], []
for n in range(1, 65):
    m = n + 1
    t = (n + 2) // 2
    cap = n * (m // 2) * ((m + 1) // 2)
    need = m * (m - 1) // 2 * t
    if cap < need:
        imp.append(n)
    elif cap == need:
        tight.append(n)
    else:
        anomaly("counting slack at n=%d" % n)
say("  n in 1..64 where region is empty by counting: %s" % ("all even n" if imp == list(range(2, 65, 2)) else imp))
say("  n where counting is exactly tight (forces equidistance, column sums (n+1)/2): %s" % ("all odd n" if tight == list(range(1, 65, 2)) else tight))
say("  in the tight case A A^T has diagonal (n+1)/2 and off-diagonal (n+1)/4, so integrality forces n=1 or n = 3 mod 4")
say("  and then A A^T = (n+1)(I+J)/4. This is consistent with every search leaf in SECTION 4 being an S-matrix.")

# ================================================================= SUMMARY
say("=" * 78)
say("anomalies: %d" % len(ANOM))
for a in ANOM[:20]:
    say("  ", a)
say("S-matrix variants tested for L2: %d, L2 failures: %d" % (nS_tested, L2_fail))
say("skipped for time: %s" % (SKIPPED if SKIPPED else "nothing"))
say("total runtime %s" % el())
verdict = "NO counterexample found" if not ANOM else "ANOMALIES FOUND (%d)" % len(ANOM)
say("SUMMARY: %s | MAIN: exhaustive n<=6 (all classes), all A with R<=1 enumerated completely for n<=14 and 16"
    " (n=15 partial) and all are S-matrices with R=1, sampled to n=31 | L1: binary exhaustive n<=6, real [0,1] grids n<=3,"
    " KKT/perturbation/convex tests at S n=3..15, heuristic optimisation n<=12, no violation, equality only at S |"
    " L2: exact on %d S-matrix variants n=1..47, failures=%d | runtime %s"
    % (verdict, nS_tested, L2_fail, el()))
