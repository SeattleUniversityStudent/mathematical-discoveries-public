# Review record — MAT-SCF-001 r2

Proof status: **unreviewed draft**. The reviews below were made by AI systems. They are recorded as evidence; they do not make this a human-reviewed proof, and no human has reviewed or endorsed the work. Independence between the reviewer and the producing system is asserted by process (a different vendor, a fresh context, a statement-only first stage), not verified.

One review is required for the label "reconstruction". The review of r1 found one GAP. A changed-line recheck of r2 closed it, leaving 0 open GAP or ERROR.

## Review of revision r1

| Field | Value |
| --- | --- |
| Vendor | Anthropic (producer: another vendor) |
| Date (UTC) | 2026-10-11T00:24Z |
| Context | fresh |
| Reviewed revision | PROOF.md r1, SHA-256 690c38727f65f5160726502b8af919491e92298c6358701cbcdc2e86ecb1f707 |
| Independent program | review/review-r1/check_RQ1.py, SHA-256 43c817b245d91bf92409997095bf600638726d5978a6eb3deaba6e67e520b1aa, written from the statements before the producer's material was given |
| Program result | 0 failures: n = 1..4 exhaustive, n = 5..7 random, hill-climb attack n = 5..8; equality exactly at S-matrices |
| Steps | 10 marked: 9 OK, 1 GAP, 0 ERROR |
| Proposed result label | reconstruction (stricter than the producer's original "known result", so it governs) |
| Verdict | Needs revision |

The GAP was in line 8. It said "the literature gives" the cofactor bound, but no cited source states the cofactor form; the note derives it itself. The fix was to reword it as "follows directly from".

Not checked in this review: the even-n proofs of Li and Zhang and Li's Lean files; Li v2 itself (the fetch failed); journal details of Drnovšek and Frankel–Urschel; a full literature search for an earlier explicit cofactor statement.

## Recheck of revision r2

| Field | Value |
| --- | --- |
| Vendor | Anthropic |
| Date (UTC) | 2026-10-11T02:16Z |
| Context | shared with 1 earlier review |
| Reviewed revision | PROOF.md r2, SHA-256 99e1d6558099efd0423df9f76d7fb307afd77e15a5494c735200d7e326e65700 |
| Scope | Changed lines 4, 8, 10 and 19, and the steps that depend on them; unchanged lines confirmed byte-identical to r1 |
| Steps | 10 marked, 10 OK, 0 GAP, 0 ERROR |
| Result label | reconstruction |
| Verdict | Passed |

The full recheck verdict, including its non-blocking notes, is in review/recheck-r2/verdict-r2-recheck.md.

Provenance note: the recheck was made by a separate run of the same vendor's reviewer, not the run that produced the r1 review above. It refers to that run's own statement-only program, review/recheck-r2/rev-a-rq1-a_check.py (SHA-256 6a80ede52dd0075047a4cd015c56a75a32093c08cfe7532675f6b3dc9eaddb0c), and that run's own r1 verdict (SHA-256 e36c34a3…2922). That r1 verdict file is not part of the shared record and is not included here. The r1 review of record is the one in the table above.

## Points left open by the recheck, settled at release

The recheck could not confirm three things, because the Li v2 page was rate-limited:
- that Li v2 exists with the title given;
- that the main theorem is numbered 1.1;
- that Li cites Zhang's complete proof.

All three were confirmed against the arXiv record and full text of Li v2 when this release was prepared; see README.md, "Citation checks made at release". No correction to PROOF.md was needed.
