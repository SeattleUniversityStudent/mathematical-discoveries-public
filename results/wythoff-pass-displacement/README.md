# Wythoff Nim with one pass: bounded displacement of P-positions

Contribution GAM-WYP-001, revision r1, released 2026-10-11.

**Proof status:** unreviewed draft.
**Result status:** known result.
**Formal verification:** none. No Lean or other proof-assistant check has been run on this result. Formal verification is pending; this is an AI-reviewed draft, not part of a formally verified collection.

This work is AI-assisted: AI systems produced the note and the check programs described below. One AI reviewer checked it (see REVIEW.md). No human has reviewed or endorsed it. No proof assistant was used. No new result is claimed: the statement is a short corollary of a published theorem.

## Statement

Two heaps; a move reduces one heap, or both heaps by the same amount; normal play. Either player may instead use one shared pass, once in the whole game, except at the empty position. For every P-position (a, b) with the pass unused and a ≤ b, with d = b − a and φ = (1+√5)/2:

|a − ⌊φd⌋| ≤ 17.

The constant is deliberately loose. The reviewer's exact computation over all P-positions with min(a, b) ≤ 2·10⁷ found a maximum of 8, first at (93, 146); the same argument, done more carefully, gives 14. Sharpness is not claimed.

## Source

R. Miyadera, H. Manabe, M. Fukui, *Wythoff's Game with a Pass*, Integers 25 (2025), #G4, Theorems 2 and 5. DOI 10.5281/zenodo.17535339 (the DOI is not printed in PROOF.md). Theorem numbers refer to the Integers version; arXiv:1711.04960v2 numbers them differently.

## Files

| Path | Content |
| --- | --- |
| PROOF.md | Statement and the short derivation from the source theorem |
| RERUN.json | Records that the note has no programs or logs of its own |
| REVIEW.md | Record of the AI review |
| review/reviewer-1/verdict.md | The reviewer's complete verdict, verbatim |
| review/reviewer-1/rev-a-rq5-a_check.py, …_output.txt | Exact computation of all P-positions with min(a, b) ≤ 2·10⁷ |
| review/reviewer-1/rev-a-rq5-a_check2.py, …_output.txt | Finite checks of the source's Theorem 4 / Corollary 2 and of the quoted Blass–Fraenkel bounds (rows ≤ 10⁶) |
| EXECUTION.json | Record of the reruns made when this release was prepared |
| RIGHTS.md | Rights and licensing status |
| MANIFEST.json | SHA-256 and size of every other file |

PROOF.md and RERUN.json are byte-identical to the reviewed revision (archive SHA-256 a460b07e50d5a478d7b2486330ac0a3e7600111ff2f2c11083aee8b11b16b486). That archive's own short README.md and REVIEW.md, written before any review returned, are replaced by this README and REVIEW.md. PROOF.md is retained as the original pre-review note: its closing statement that no separate review is supplied describes that original delivery. The later AI review and its finite checks are supplied in REVIEW.md and review/.

## What was actually run

Both reviewer programs were rerun when this release was prepared (Python 3.13.16, NumPy 2.5.3, x86-64 Linux): `python3 rev-a-rq5-a_check.py 20000000 5000 150` (about 55 s) and `python3 rev-a-rq5-a_check2.py 1000000 60`. Both outputs matched the supplied outputs apart from elapsed-time stamps.

## Points noted in review (not changing the result)

- The source proves its Theorem 5 from Corollaries 1 and 2, which cover x ≥ 9 or y ≥ 9 only. The reviewer closed the finite remaining cases x, y ≤ 8 from the source's Lemma 1 and exact data.
- The source's Theorem 3 (Blass and Fraenkel 1990, Corollary 5.14, DOI 10.1016/0304-3975(90)90098-3) was checked only finitely, up to a ≤ 10⁶; the original paper was not read.

## Limitations

- No human review and no formal proof-assistant check.
- The bound for all a rests on the cited theorem chain; the computations are finite.

## Rights

No licence is granted. See RIGHTS.md.

## Revision history

- r1: first public release.
- r1, documentation update of 2026-10-11: the formal-verification status above was added. Only README.md and MANIFEST.json changed; the mathematics, programs, logs and reviews are unchanged.
- r1, documentation correction of 2026-10-14: clarified that PROOF.md’s pre-review closing sentence describes the original delivery. Only README.md and MANIFEST.json changed; the mathematics and review evidence are unchanged.
