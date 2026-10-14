# A failure of log-concavity for Carlitz composition lengths

Contribution PRT-CAR-001, revision r2 (formal-verification revision), publicly released 2026-10-14; first released 2026-10-11 as r1.

**Proof status:** unreviewed draft.
**Result status:** new claim not cleared.
**Formal verification:** Lean kernel-checked (core Lean 4.34.0) for the five statements listed in FORMAL/coverage.json: the main inequality for every m ≥ 104, the closed forms A, B and C for m ≥ 2, and the three values at n = 314. The check covers those statements only. The Lean proof follows a different route from PROOF.md, and the Python programs and certificates are not formally checked.

This work is AI-assisted: AI systems produced the argument, the programs, the Lean formalization and the runs described below. Two AI reviewers, from two different vendors, checked the written proof (see REVIEW.md). A separate AI verifier built and replayed the Lean formalization, and a separate AI reviewer checked that its statements match this page (see FORMAL/). No human has reviewed or endorsed it. No claim of priority is made.

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

## Review provenance

REVIEW.md preserves the two written-proof reviews of r1. Its statement about files being byte-identical to the reviewed delivery applies to the r1 source material; FORMAL/ was added in r2 and has its own verification and correspondence records. Later documentation corrections are listed below and do not extend either review’s scope.

## Files

| Path | Content |
| --- | --- |
| PROOF.md | Statement, definitions, proof, computations, sources, limitations |
| algebra.py, algebra.json, algebra.log | Transfer matrices, state polynomials, comparison with the reference table |
| verify_counterexample.py, counterexample.json, counterexample.log | Separate last-part dynamic program for the n = 314 values |
| certify.py, certificate_verification.json, certificate.log | Exact check of all state and projection identities and of the closed forms |
| reference_coefficients.json | Frozen auxiliary table of a(n,k), n ≤ 150 |
| RERUN.json | Commands that produce each log |
| FORMAL/ | Lean sources, verifier receipt and logs, statement coverage and the correspondence review |
| EXECUTION.json | Record of the reruns made when this release was prepared |
| REVIEW.md | Record of the two AI reviews |
| review/reviewer-1/, review/reviewer-2/ | Each reviewer's own check programs and outputs |
| RIGHTS.md | Rights and licensing status |
| MANIFEST.json | SHA-256 and size of every other file |

## What was actually run

Requirements: Python 3, standard library only. No network access.

All three supplied commands in RERUN.json were rerun when this release was prepared (Python 3.13.16, x86-64 Linux, each under a 120-second limit). Every log and output matched the supplied file byte for byte, except the elapsed-time field in counterexample.json and counterexample.log. Both reviewers' independent programs were also rerun; see EXECUTION.json.

## Observations from review (not part of the claim)

- One reviewer's exhaustive computation for n ≤ 320 found failures at (n, k) = (3m+1, 2m) for every m with 52 ≤ m ≤ 106, the first at n = 157 (triple 42709, 206, 1); n = 157 is the smallest failing row for n ≤ 320. No general proof of this family is given here, and it is not part of the formally checked statements. The result above is therefore not the first failure; PROOF.md does not claim it is.
- Bender and Canfield, *Locally Restricted Compositions I*, Electron. J. Combin. 12 (2005) R57, DOI 10.37236/1954, prints r ≈ 0.78397 in Example 2 (p. 3) as the radius of convergence for Carlitz compositions. Both reviewers' exact computations, and the same paper's later table, give 0.5713497932, in agreement with Knopfmacher and Prodinger. This background value is not used in the proof.

## Limitations

- No human review. The formal check covers only the five statements in FORMAL/coverage.json, not the computations or the observations above.
- Prior-art search was bounded (web, OEIS, the cited papers); MathSciNet and zbMATH were not searched. Search absence is not clearance.
- The reference table is an auxiliary finite check only; the proof does not depend on it.

## Rights

No licence is granted. See RIGHTS.md.

## Revision history

- r1: first public release.
- r1, documentation update of 2026-10-11: a formal-verification status line was added (then: none, pending). Only README.md and MANIFEST.json changed.
- r2, publicly released 2026-10-14: added FORMAL/ (Lean source revision RQ4-lean-r2, verifier receipt and replay, coverage, correspondence review) and updated this README. PROOF.md is unchanged from r1; its closing sentence that no proof-assistant compilation is supplied describes the note as written for r1.
- r2, documentation correction of 2026-10-14: corrected the public release date (previously shown as 2026-10-11) and clarified the r1 review inventory. Only README.md, FORMAL/CORRESPONDENCE.md and MANIFEST.json changed; the mathematical claim, proof, programs and formal sources are unchanged, and the prior correspondence is preserved as labelled history.
