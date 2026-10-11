# A cofactor bound from the S-matrix theorem

Contribution MAT-SCF-001, revision r2, released 2026-10-11.

**Proof status:** unreviewed draft.
**Result status:** reconstruction.

This work is AI-assisted: AI systems wrote the note and the check programs described below. An AI reviewer checked it, and the same reviewer rechecked the revised lines (see REVIEW.md). No human has reviewed or endorsed it. No proof assistant was used. No new result is claimed: the bound is a two-step consequence of a published theorem.

## Statement

Let A be a nonsingular n×n binary matrix, n ≥ 1. Put D = |det A|, and let c(A) be the largest absolute value of a determinant obtained by deleting one row and one column (with the empty determinant equal to 1). Then

c(A) ≥ 2D/(n+1),

with equality exactly when A is an S-matrix (a binary matrix with SᵀS = (n+1)(I+J)/4).

Proof in one line: c(A)/D = maxnorm(A⁻¹) ≥ ‖A⁻¹‖_F / n ≥ 2/(n+1), using the S-matrix theorem ‖A⁻¹‖_F ≥ 2n/(n+1) for nonsingular A with entries in [0,1]. Details are in PROOF.md.

## Dependence on recent work

The S-matrix theorem in all orders rests on recent preprints that have not been audited here:

- Odd orders: Cheng (1987); Drnovšek, Linear Algebra Appl. 439(11) (2013) 3555–3560, arXiv:1306.6786.
- Even orders: Frankel and Urschel, Linear Algebra Appl. 708 (2025) 193–203, DOI 10.1016/j.laa.2024.11.030, for n ≥ 1000. Zhang, arXiv:2609.20306, and Li, arXiv:2608.29750v2, for all n.

The note is only as strong as that theorem.

## Citation checks made at release

- Li, arXiv:2608.29750: version v2 (7 October 2026) exists and is titled "An independent proof of the even-dimensional S-matrix inequality", as PROOF.md states.
- Li's Theorem 1.1 is the S-matrix theorem in every dimension: ‖A⁻¹‖_F ≥ (2n/(n+1))‖A‖_max⁻¹ for nonsingular nonnegative A, with equality iff A is a positive multiple of an S-matrix. Li proves the even part and imports the odd part from Cheng. For a binary A the [0,1] form used here follows directly.
- Li's introduction states that "Zhang has given a complete proof of the conjecture in all dimensions" and cites Zhang, arXiv:2609.20306. This supports PROOF.md's statement that Li cites Zhang's complete proof.
- Frankel–Urschel: title, authors, volume 708 and pages 193–203 confirmed via Crossref for DOI 10.1016/j.laa.2024.11.030.
- Drnovšek: journal reference Linear Algebra Appl. 439(11) (2013) 3555–3560 confirmed on the arXiv record.

## Files

| Path | Content |
| --- | --- |
| PROOF.md | Statement, derivation, sources and limitations (revision r2) |
| RERUN.json | Records that the note has no programs or logs of its own |
| REVIEW.md | Record of the review and the recheck |
| review/review-r1/ | The reviewer's statement-only check program and output for revision r1 |
| review/recheck-r2/ | The recheck verdict for revision r2, and the check program and output it refers to |
| EXECUTION.json | Record of the reruns made when this release was prepared |
| RIGHTS.md | Rights and licensing status |
| MANIFEST.json | SHA-256 and size of every other file |

PROOF.md has SHA-256 99e1d6558099efd0423df9f76d7fb307afd77e15a5494c735200d7e326e65700, which is the revision the recheck covered. Revision r1 differed only in lines 4, 8, 10 and 19: the result label, the wording "follows directly from", an explicit statement of dependence on the recent preprint, and a statement of reading scope.

## What was actually run

The note has no programs. Both reviewer check programs were rerun when this release was prepared (Python 3.13.16, NumPy 2.5.3, x86-64 Linux). See EXECUTION.json for how the outputs compared.

## Limitations

- No human review and no formal proof-assistant check.
- The even-order proofs in the 2026 preprints were not audited by anyone in this review chain.
- Editorial points the reviewer raised but did not require are not applied: missing spaces such as "determinant1", and a two-line proof of S⁻¹ = 2(2Sᵀ − J)/(n+1).

## Rights

No licence is granted. See RIGHTS.md.

## Revision history

- r1: first version; the review found one wording GAP.
- r2: wording revision of lines 4, 8, 10 and 19; first public release.
