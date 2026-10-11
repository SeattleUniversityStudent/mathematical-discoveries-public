# A failure of log-concavity for Carlitz composition lengths

Contribution PRT-CAR-001, revision r1, released 2026-10-11.

**Proof status:** unreviewed draft.
**Result status:** new claim not cleared.

This work is AI-assisted: AI systems produced the argument, the programs and the runs described below. Two AI reviewers, from two different vendors, checked it (see REVIEW.md). No human has reviewed or endorsed it. No proof assistant was used. No claim of priority is made.

## Statement

Let a(n,k) be the number of ordered lists of k positive integers with sum n and unequal adjacent entries (Carlitz compositions of n with k parts). For every integer m ≥ 104, the row n = 3m+2 fails log-concavity at k = 2m:

a(n,2m)² < a(n,2m−1) · a(n,2m+1).

At m = 104 (n = 314): a(314,207) = 10094513, a(314,208) = 32552, a(314,209) = 105, and 32552² = 1059632704 < 1059923865 = 10094513 · 105.

Global least size is not claimed. Unimodality, which is weaker than log-concavity, is not settled. The full statement, proof and limitations are in PROOF.md.

## Status

| Item | Status |
| --- | --- |
| Endpoint formulas A, B, C and the infinite family m ≥ 104 | Written proof with an exact finite certificate; unreviewed by humans; prior-art status undetermined (new claim not cleared). |
| Definitions, last-part recurrence, generating function | Known (Knopfmacher and Prodinger 1998). |

## Files

| Path | Content |
| --- | --- |
| PROOF.md | Statement, definitions, proof, computations, sources, limitations |
| algebra.py, algebra.json, algebra.log | Transfer matrices, state polynomials, comparison with the reference table |
| verify_counterexample.py, counterexample.json, counterexample.log | Separate last-part dynamic program for the n = 314 values |
| certify.py, certificate_verification.json, certificate.log | Exact check of all state and projection identities and of the closed forms |
| reference_coefficients.json | Frozen auxiliary table of a(n,k), n ≤ 150 |
| RERUN.json | Commands that produce each log |
| EXECUTION.json | Record of the reruns made when this release was prepared |
| REVIEW.md | Record of the two AI reviews |
| review/reviewer-1/, review/reviewer-2/ | Each reviewer's own check programs and outputs |
| RIGHTS.md | Rights and licensing status |
| MANIFEST.json | SHA-256 and size of every other file |

## What was actually run

Requirements: Python 3, standard library only. No network access.

All three supplied commands in RERUN.json were rerun when this release was prepared (Python 3.13.16, x86-64 Linux, each under a 120-second limit). Every log and output matched the supplied file byte for byte, except the elapsed-time field in counterexample.json and counterexample.log. Both reviewers' independent programs were also rerun; see EXECUTION.json.

## Observations from review (not part of the claim)

- One reviewer found a second failing family by exhaustive computation: (n, k) = (3m+1, 2m) for every m ≥ 52, first at n = 157 (triple 42709, 206, 1), and n = 157 is the smallest failing row for n ≤ 320. The result above is therefore not the first failure; PROOF.md does not claim it is.
- Bender and Canfield, *Locally Restricted Compositions I*, Electron. J. Combin. 12 (2005) R57, DOI 10.37236/1954, prints r ≈ 0.78397 in Example 2 (p. 3) as the radius of convergence for Carlitz compositions. Both reviewers' exact computations, and the same paper's later table, give 0.5713497932, in agreement with Knopfmacher and Prodinger. This background value is not used in the proof.

## Limitations

- No human review and no formal proof-assistant check.
- Prior-art search was bounded (web, OEIS, the cited papers); MathSciNet and zbMATH were not searched. Search absence is not clearance.
- The reference table is an auxiliary finite check only; the proof does not depend on it.

## Rights

No licence is granted. See RIGHTS.md.

## Revision history

r1: first public release.
