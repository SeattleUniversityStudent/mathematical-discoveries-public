# Verdict REV-A-RQ5-a — Wythoff Nim with one pass — bounded displacement is known
Reviewer ID: REV-A-RQ5-a
Vendor: Anthropic
Date (UTC): 2026-10-11T02:03Z
Context: fresh
Sources consulted: /tmp/reva/rq5a/STATEMENT.md; /tmp/reva/rq5a/producer/PROOF.md (sha256 f7714b42…ba66217), README.md (a10c925c…ec0c5), RERUN.json (46f9f55e…e3e2), REVIEW.md (a2fa4a34…d6b3), manifest.json (ada919e1…535f0; the four listed hashes match the files); my own files rev-a-rq5-a_check.py, rev-a-rq5-a_check_output.txt, rev-a-rq5-a_check2.py, rev-a-rq5-a_check2_output.txt, rev-a-rq5-a_notes.txt; external, read through the WebFetch tool, which returns model-extracted text and quotes, not the raw file: https://math.colgate.edu/~integers/zg4/zg4.pdf (three reads), https://arxiv.org/abs/1711.04960, https://arxiv.org/html/1711.04960v2, https://arxiv.org/pdf/1711.04960v2, https://zenodo.org/records/17535339 (via doi.org redirect), https://ftp.math.utah.edu/pub/tex/bib/idx/tcs1990/75/3/311_333.html, Crossref API bibliographic query for the Blass–Fraenkel title, https://portal.mardi4nfdi.de/entity/Q914374, Cambridge Core page of Nivasch's chapter; two web searches: "Wythoff's game with a pass Miyadera Manabe Fukui arXiv" and "\"10.1016/0304-3975(90)\" Sprague-Grundy function Wythoff's game Blass Fraenkel" (result lists only, except the pages named above)
Independent program: rev-a-rq5-a_check.py; written before reading producer code: yes (no producer code exists)
Independent program result: exact computation of every P position (pass unused) with min(a,b) <= 2*10^7 (12,360,681 with a <= b): max |a - floor(phi d)| = 8, first at (93,146); W1 max squared distance = 9; 0 violations of 17 or of 20; supplement rev-a-rq5-a_check2.py (rows 0..10^6) found 0 exceptions to source Theorem 4/Corollary 2 for x>=9 or y>=9 and 0 violations of the quoted Blass–Fraenkel bounds; agrees with producer logs: no producer logs exist (RERUN.json: runs = []); consistent with the producer's claimed bound 17
## Steps
| # | Statement or step | Mark | Note |
|---|---|---|---|
| 1 | PROOF.md L3: game definition (one shared pass, either player, not allowed at the empty position, normal play) | OK | Matches STATEMENT.md and the Integers version, Def. 8/11: pass allowed iff p = 1 and x + y > 0, so allowed on the axes. The arXiv v2 text reportedly has an inconsistent remark that disallows the pass on the axes; the Integers version is the one cited. |
| 2 | PROOF.md L5: main statement | OK | Identical to STATEMENT.md. |
| 3 | PROOF.md L7, L9: "Theorem 5 of the source gives an ordinary Wythoff P position within Euclidean distance sqrt(20)" | OK | Theorem 5 exists in Integers 25 (2025) #G4: for every (x,y,1) with G1(x,y,1)=0 there is (v,w,0) with G1(v,w,0)=0 at distance <= sqrt(20). Here p=1 means the pass is unused, and G1(v,w,0)=0 means an ordinary Wythoff P position. The variant is exactly the one under review. |
| 4 | Scope of the source's proof of Theorem 5 | OK (closed by reviewer) | The source proves Theorem 5 "directly from Corollaries 1 and 2". Corollary 2 (via Theorem 4) holds only for x >= 9 or y >= 9, and no sentence in the source covers x, y <= 8. The gap is finite. Lemma 1(ii) lists those P positions as (0,0), (1,3), (2,5), (4,8), (6,7) and their mirrors, matching my program's list. Their maximum squared distance to an ordinary P position is 4, at (6,7). My exact enumeration up to 2*10^7 found max squared distance 9 and no violation. The producer did not mention this. |
| 5 | PROOF.md L9: Theorem 2 of the source (Wythoff's formula) | OK | Exists as cited: {(floor(n phi), floor(n phi)+n)} together with mirrors. It justifies the form (v,w) in L7. |
| 6 | Dependency inside Theorem 5: source Theorem 3 = Blass–Fraenkel Cor. 5.14 (G=1 positions near (floor(n phi), floor(n phi)+n)) | OK (finite check only) | Cited, not reproved, in the source. Published in TCS 75 (1990). I did not read Blass–Fraenkel itself. My exact check of the quoted bounds over 618,035 G=1 positions (a <= 10^6) found a_n - floor(n phi) in [-1,2] and max |b_n - (floor(n phi)+n)| = 4, with no violations. |
| 7 | PROOF.md L7: "Sorting its coordinates preserves that bound" | OK | For a <= b: (a-v)^2 + (b-w)^2 - [(a-w)^2 + (b-v)^2] = 2(w-v)(a-b), which is >= 0 when v > w. So sorting does not increase the distance, and a mirror of an ordinary P position is an ordinary P position. |
| 8 | PROOF.md L7: "Integer coordinate differences have absolute value at most four, so |d-n| <= 8" | OK | dx^2 + dy^2 <= 20 gives |dx|, |dy| <= 4, and d - n = dy - dx. The bound is valid but loose: the true maximum of |dy - dx| is 6. |
| 9 | PROOF.md L7: "|floor(phi d) - floor(phi n)| <= ceil(8 phi) = 13" | OK | 8 phi = 12.944..., so the ceiling is 13. The step uses the unstated standard fact |floor x - floor y| <= ceil|x - y|, which is true. |
| 10 | PROOF.md L7: "giving the stated bound" (final sum) | OK | |a - floor(phi d)| <= |a - v| + |floor(phi n) - floor(phi d)| <= 4 + 13 = 17. The sum is implicit, not written out. My exact case analysis gives 14 from the same input; the observed maximum in range is 8. |
| 11 | PROOF.md L9: citation details | OK (editorial) | Volume, article and theorem numbers are correct for the Integers version. The DOI is missing (10.5281/zenodo.17535339). The "associated arXiv:1711.04960v2" uses different numbering (Lemma 1.x / Theorem 2.x) and has no "Theorem 5", so the theorem numbers should be tied to the Integers version only. |
| 12 | README.md, PROOF.md L7/L9: status "known result", no novelty asserted | OK | Consistent with what I found: the main statement is a few-line corollary of a published theorem. |
Open GAP/ERROR count: 0
## Not checked
- Blass and Fraenkel (1990), Corollary 5.14, read directly. Behind a paywall and not read; only its statement as quoted in the Integers paper was checked, and only finitely (a <= 10^6).
- The source PDF read word for word by a human. My reading went through a fetch tool that returns model-extracted text. Theorem numbers and statements were consistent across three separate reads, but a direct reading is advisable.
- The source's computer-assisted Lemma 1 (Grundy tables for x, y <= 8) and Theorem 4 beyond my finite range: rows <= 10^6 for Theorem 4/Corollary 2, rows <= 2*10^7 for the P positions.
- Any bound for all a by my own independent argument. The finite computation cannot show this; the all-a claim rests entirely on the cited theorem chain.
- Sharpness of 17 or of 14. Not asked, and no optimality is claimed.
- The 2026 arXiv paper "A duality of misère games and play with a pass" (arXiv:2607.18682), which appeared in search results. Not read.
## Citations
- R. Miyadera, H. Manabe, M. Fukui, "Wythoff's Game with a Pass", Integers 25 (2025), #G4 — DOI 10.5281/zenodo.17535339; arXiv:1711.04960 (v2, 2025-07-04; different theorem numbering)
- U. Blass, A. S. Fraenkel, "The Sprague-Grundy function for Wythoff's game", Theoretical Computer Science 75(3) (1990) 311–333 — DOI 10.1016/0304-3975(90)90098-3 (from Crossref; article not read)
- W. A. Wythoff, "A modification of the game of Nim", Nieuw Archief voor Wiskunde 7 (1907) 199–202 — unverified (no DOI/ISBN found; cited only as the source's Theorem 2)
- G. Nivasch, "More on the Sprague–Grundy function for Wythoff's game", in Games of No Chance 3 (MSRI Publ. 56, Cambridge Univ. Press, 2009) 377–410 — DOI 10.1017/CBO9780511807251.019 (background only; chapter not read)
Reviewer result label: known result
Verdict: Passed
