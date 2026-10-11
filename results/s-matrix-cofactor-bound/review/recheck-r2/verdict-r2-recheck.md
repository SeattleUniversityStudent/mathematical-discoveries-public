# Verdict REV-A-RQ1-a — Cofactor inequality from the S-matrix theorem (revision r2 recheck)
Reviewer ID: REV-A-RQ1-a
Vendor: Anthropic
Date (UTC): 2026-10-11T02:16Z
Context: shared with 1 earlier reviews
Sources consulted: /tmp/reva/rq1a/producer_r2/PROOF.md (sha256 99e1d655…5700, matches the coordinator's value); /tmp/reva/rq1a/producer_r2/r1_to_r2.diff (sha256 9751c95e…75e4); /tmp/reva/rq1a/producer/PROOF.md (r1, for comparison; all unchanged lines confirmed byte-identical); /tmp/reva/rq1a/producer/RERUN.json (sha256 b3c94171…c29c, unchanged); my own rev-a-rq1-a_check.py (6a80ede5…db0c), rev-a-rq1-a_check_output.txt (c1c6527f…7e47) and rev-a-rq1-a_verdict.md (r1, e36c34a3…2922); web: 1 generic search; arxiv.org/abs/2608.29750 (Li abstract page, read via fetch summary). FAILED: arxiv.org/abs/2608.29750v2 (HTTP 429 rate limit, not retried).
Independent program: rev-a-rq1-a_check.py; written before reading producer code: yes
Independent program result: no counterexample or anomaly; MAIN exhaustive n<=6, complete search of the extremal region for n<=14 and n=16, sampled to n=31; L1 and L2 consistent; the mathematics is unchanged in r2, so not re-run; agrees with producer logs: no producer logs exist
## Steps
| # | Statement or step | Mark | Note |
|---|---|---|---|
| 1 | r2 L4: "Proposed result status: reconstruction." | OK | Consistent with L8 ("follows directly"), L10 (cited source theorem) and L19 (no claim of independent discovery). Matches my own label. |
| 2 | r2 L8: the bound and its equality case "follow directly from the cited inverse-Frobenius theorem" | OK | Closes the governing GAP. The note no longer attributes the cofactor form to the literature; the sources state only the Frobenius form. The derivation it points to (L11–L12) is the producer's own two-step implication. |
| 3 | r2 L10: all-order source theorem cited from Li's preprint, Thm 1.1; source proof "not independently audited for this note" | OK | Supported in substance. Li's abstract (arxiv.org/abs/2608.29750, Yinjie Li, v1 dated 2026-08-30) claims that with Cheng's odd case it settles the Harwit–Sloane/S-matrix conjecture in every dimension, with equality for positive multiples of S-matrices. Li states the max-normalised non-negative form; the [0,1] form at L10 follows immediately (maxnorm<=1, and equality forces A=S). The "not audited" clause is accurate. Not confirmed: the theorem number "1.1" and version v2 (see note b). |
| 4 | r2 L19: Zhang's body "was not read for this note"; Li's dependence on Frankel–Urschel Lemma 2.1; Lean formalisation | OK | The self-report cannot be checked externally and is consistent with RERUN.json. Li's abstract confirms both claims: Frankel–Urschel Lemma 2.1 is the sole external mathematical input, and the proof is formalised in Lean 4. Dates are consistent with "earlier": Zhang v1 2026-07-30, before Li v1 2026-08-30. Li's abstract does not name Zhang, so "cited by Li" is not confirmed (note c). |
| 5 | Dependent: inequality chain at L11 with r2 L10 | OK | L11 is unchanged. c/D = maxnorm(A^-1) >= Fnorm(A^-1)/n >= 2/(n+1) is valid given the source theorem; r2 changes only its attribution. |
| 6 | Dependent: equality argument and S-matrix inverse at L12, n=1 | OK | L12 is unchanged. Equality in the cofactor bound forces equality in the source theorem, hence A=S. The converse via S^-1 = 2(2S^T-J)/(n+1) and the n=1 case were confirmed exactly in step 1. |
| 7 | My r1 GAP "known result / literature gives" (r1 row 3, at L4 and L8) | OK | Closed by r2 (L4 and L8 rewritten). |
| 8 | My r1 GAP "L1 for even 4<=n<=998 rests on unaudited preprints" (r1 row 6) | OK | Non-blocking. r2 L10 now discloses the dependency explicitly, so the note states nothing false. The mathematical dependency remains, and Li's abstract confirms that Li claims this range. |
| 9 | My r1 GAP "L2 identity given without proof or citation" (r1 row 10) | OK | Non-blocking (editorial). The identity is true, as checked exactly in step 1, and follows in two lines from S^T S=(n+1)(I+J)/4. |
| 10 | My r1 GAP "Li citation unverified" (r1 row 14) | OK | Non-blocking (citation). The preprint exists and claims the all-dimension result. The title at L17 and the version "v2" do not match what I could see (note b). I could not establish that either is false, because the v2 page was rate-limited. |
Open GAP/ERROR count: 0
## Not checked
- The body and proof of Li arXiv:2608.29750 (abstract only, via fetch summary); whether a v2 exists, its title, and whether its main theorem is numbered 1.1; whether Li cites Zhang.
- The body of Zhang arXiv:2609.20306 (abstract only, in step 2). Proofs in Drnovšek and Frankel–Urschel (statements only).
- No re-run of the step-1 program: the mathematics is unchanged, and the program and output hashes match step 1.
- "Passed" applies the coordinator's blocking rule. It does not mean that anyone in this review chain has audited the all-dimension proof of L1 for even n with 4<=n<=998.
## Citations
- Y. Li, The S-matrix conjecture (preprint; v1 2026-08-30 seen on the abstract page; PROOF.md L17 gives title "An independent proof of the even-dimensional S-matrix inequality", v2 — unconfirmed) — arXiv:2608.29750
- T. Zhang, The A-optimal design problem and the S-matrix conjecture (preprint, v1 2026-07-30) — arXiv:2609.20306
- E. Frankel, J. Urschel, On the Frobenius norm of the inverse of a non-negative matrix, Linear Algebra Appl. 708 (2025) 193–203 — DOI 10.1016/j.laa.2024.11.030; arXiv:2409.04354
- R. Drnovšek, On the S-matrix conjecture, Linear Algebra Appl. 439(11) (2013) 3555–3560 — DOI 10.1016/j.laa.2013.09.012; arXiv:1306.6786
- C.-S. Cheng, An application of the Kiefer–Wolfowitz equivalence theorem to a problem in Hadamard transform optics, Ann. Statist. 15(4) (1987) — DOI 10.1214/aos/1176350612
Reviewer result label: reconstruction
Verdict: Passed

## Non-blocking notes for the producer
a. L10: say in one clause that the cited sources state the max-normalised non-negative form, ‖A^-1‖_F >= (2n/(n+1))‖A‖_max^-1 with equality iff A is a positive multiple of S, and that the [0,1] form follows (‖A‖_max <= 1, and equality forces A = S). Also say that the all-order statement is Li (even n) combined with Cheng/Drnovšek (odd n), as Li's abstract itself states.
b. L17: the arXiv abstract page I could read lists the title "The S-matrix conjecture" and only v1 (2026-08-30). Check whether v2 exists, whether it carries the title given at L17, and whether "Theorem 1.1" is right; correct the line otherwise. Add the Drnovšek DOI 10.1016/j.laa.2013.09.012 at L15.
c. L19: "cited by Li as an earlier complete proof" is not visible in Li's abstract. Give the location in Li, or say that the Zhang reference was found independently.
d. L12: add a two-line proof of S^-1 = 2(2S^T-J)/(n+1): from S^T S=(n+1)(I+J)/4, the column sums are (n+1)/2, so SS^T=(n+1)(I+J)/4 and SJ=((n+1)/2)J, hence S(2S^T-J)=((n+1)/2)I.
e. Typos: "determinant1", "all1", "value2", "printedp2", "Theorem1.1", "LAA439" are missing spaces.
