# Statement-correspondence binding renewal for PRT-CAR-001 r2

Reviewer ID: independent-codex-doc-correspondence-reviewer-20261014
Reviewed receipt SHA-256: cea4888f385ee3d0df918c0eb2e01896ae4b51d5c2b7a3367a26d82ab577b0e4
Reviewed coverage SHA-256: 3f484740e907b5b5a02aeb2260921766bab3ed5b27925dbab4583efe30b690e5
Reviewed README SHA-256: 1debc0634015479c859a1ed133d02b4a3690b1a01f5165459d2036bb62601030
Reviewed PROOF SHA-256: c867b6f57e4aba4e7da4cacc50e2e12dc6e8f58c79ee9c4f5436482d78985940
Open issues: 0
Verdict: Passed
Reviewer type: AI (OpenAI Codex)
Review date (UTC): 2026-10-14T20:53:09Z
Result: PRT-CAR-001
Package revision: r2
Lean source revision: RQ4-lean-r2

The Passed verdict and zero open issues apply only to renewed statement correspondence for the four exact files below.

This is a new review by an AI reviewer separate from the documentation author and from the role identities in the historical receipt and correspondence. It is not human review, an independently implemented kernel check, a novelty finding or permission to publish. The reviewer inspected the supplied public snapshot and the proposed documentation; it did not access private source records.

## Exact binding

| Bound file, relative to this result | Bytes | SHA-256 |
| --- | ---: | --- |
| README.md | 6054 | 1debc0634015479c859a1ed133d02b4a3690b1a01f5165459d2036bb62601030 |
| FORMAL/receipt.json | 11144 | cea4888f385ee3d0df918c0eb2e01896ae4b51d5c2b7a3367a26d82ab577b0e4 |
| FORMAL/coverage.json | 1263 | 3f484740e907b5b5a02aeb2260921766bab3ed5b27925dbab4583efe30b690e5 |
| PROOF.md | 7065 | c867b6f57e4aba4e7da4cacc50e2e12dc6e8f58c79ee9c4f5436482d78985940 |

The historical correspondence bound README SHA-256 46f2f5b6caa720e500fa446e2b8995c886bfdae14a3c9daef5fe01da2a24fce0. This renewal binds the new README above. The receipt, coverage and PROOF bytes are unchanged. Any further change to a bound file requires renewed binding review.

## Material inspected and work performed

The reviewer read the complete old and new README, PROOF.md, REVIEW.md, FORMAL/CORRESPONDENCE.md, FORMAL/coverage.json, FORMAL/receipt.json and FORMAL/README.txt. It read the literal definitions in CarlitzSpec.lean, the F_literal and carlitz_eq_F bridge in CarlitzCore.lean, and the five release theorem declarations and their surrounding proofs in CarlitzMain.lean. It compared the receipt signatures and axiom lists with verification/axioms_stdout.txt, and read the saved build summary, replay summaries and dependency-closure summary.

Local SHA-256 comparisons matched all 14 Lean source files and all 18 published evidence files listed in the unchanged receipt. All five signature/axiom-list pairs matched the saved printed report. Hashing generated induction sources and individual logs confirms their byte identity with the receipt; it is not a new semantic audit of every generated step or log. The source archive identity remains the one recorded by that receipt, 2bb7171400588f7bb1bc1b43e3d1db53ccb7ac00829e341f06f4bcce1d142c30; this review did not reconstruct the archive.

The new work consists of source/document reading, exact byte bindings and statement comparisons. No Lean command, compiler, proof checker, mathematical program or finite mathematical test was run. The original build, second compilation and stored-declaration replay are reused as historical evidence. Their recorded toolchain is Lean 4.34.0 and their printed dependencies are propext, Classical.choice and Quot.sound. All these executions use the same kernel implementation; this renewal does not add another execution or another kernel.

## Five statement comparisons

The literal count remains the same object: comps enumerates ordered lists by selecting one positive first part from 1 through n, then a tail of the remaining length and total; adjDistinct filters precisely unequal adjacent entries; carlitz takes the length of that filtered enumeration. The first-part choice and tail determine each list uniquely. F_literal and carlitz_eq_F connect the recurrence used by the formal proof to that count. This is the same interpretation as a(n,k) in README.md and PROOF.md.

| Coverage assertion | Formal declaration | Renewed comparison |
| --- | --- | --- |
| A1 | carlitz_logconcavity_fails | Every integer m >= 104 is represented by the natural-number quantifier. Total 3m+2, middle length 2m, neighboring lengths 2m-1 and 2m+1, and the strict inequality direction agree. Multiplication of the middle count by itself is its square. |
| A2a | carlitz_A | For m >= 2, a(3m+2,2m+1) = m+1; same endpoint, domain and value. |
| A2b | carlitz_B | For m >= 2, a(3m+2,2m) = m(3m+1); same endpoint, domain and value. |
| A2c | carlitz_C | For m >= 2, the natural-number identity 24C + 277m^2 + 312 = m^4 + 114m^3 + 426m is equivalent over the integers to C = (m^4+114m^3-277m^2+426m-312)/24. Division is exact, the denominator is positive, and the domain excludes m=1. |
| A3 | carlitz_n314 | The conjunction states a(314,207)=10094513, a(314,208)=32552 and a(314,209)=105, in the same order and with the same values as the public claim. |

No admissible integer m is lost by the natural-number domains, and all neighboring lengths are nonnegative on those domains. The documentation edits change chronology and provenance wording; they do not alter these five statements or the counting definitions.

## Coverage and provenance limits retained

The formal proof takes a first-part recursion route. This review does not claim formal coverage of every transfer-matrix or generating-function step in PROOF.md. The Python programs, certificates and logs, the finite observation about (3m+1,2m), and the Bender–Canfield background note remain outside the five-statement formal coverage.

The observed family is still limited to 52 <= m <= 106 within totals at most 320. There is no general theorem for that family, no claim of a globally least counterexample, no unimodality conclusion, no priority clearance and no human endorsement. The README still explains that PROOF.md's closing proof-assistant disclaimer is historical r1 wording. Its new provenance paragraph correctly limits the written-proof review inventory to r1 and distinguishes the later FORMAL records.

The README's revised public release date is a release-history assertion, outside the theorem comparison. The release reviewer supplied a release-date record for public commit c33ff560630bc04c9e774432ffeb884f31c5ad1e: author and committer timestamps are 2026-10-14T19:07:58Z; the record separately attributes the Publisher push observation at 19:39:30–19:39:52Z and the anonymous public readback at 19:40:17–19:40:18Z to the release reviewer. That record supports the corrected calendar date while distinguishing commit timestamps from actual publication observations. This reviewer read the supplied record (1022 bytes, SHA-256 1494b1c50044f1200cfe954b10223cacaacb8fbdc3bbd9cf55766794a83019ae); it did not independently observe those earlier events or contact GitHub. The repository owner and Publisher must update the manifest for this replacement correspondence and perform final package-integrity and publication checks. This review does not grant release acceptance.

## Historical correspondence — preserved by reversible indentation

The complete previous FORMAL/CORRESPONDENCE.md follows as historical literal text, including its original reviewer identity, date, bindings and limits. Each original line, including every blank line, is prefixed by exactly four ASCII spaces so its metadata cannot be parsed as active fields. To recover the exact original bytes, take only the content between the BEGIN and END markers, remove exactly the first four ASCII spaces from each line, and retain all original line endings, including the final newline. Recovery was verified against the original: 5546 bytes, SHA-256 96ca13073a253cf866f47997bbf54b46b9cc17e447e7420468445114a15279d0. The old README binding inside it is superseded only by the exact renewed binding above; no original content is omitted or altered after reversing the indentation.

<!-- BEGIN INDENTED HISTORICAL CORRESPONDENCE -->
    # Statement-correspondence review for PRT-CAR-001 r2
    
    Reviewer ID: statement-correspondence-reviewer-1
    Reviewed receipt SHA-256: cea4888f385ee3d0df918c0eb2e01896ae4b51d5c2b7a3367a26d82ab577b0e4
    Reviewed coverage SHA-256: 3f484740e907b5b5a02aeb2260921766bab3ed5b27925dbab4583efe30b690e5
    Reviewed README SHA-256: 46f2f5b6caa720e500fa446e2b8995c886bfdae14a3c9daef5fe01da2a24fce0
    Reviewed PROOF SHA-256: c867b6f57e4aba4e7da4cacc50e2e12dc6e8f58c79ee9c4f5436482d78985940
    Open issues: 0
    Verdict: Passed
    
    Date: 2026-10-11
    Result: PRT-CAR-001
    Package revision: r2
    Lean source revision: RQ4-lean-r2
    Lean source archive SHA-256: 2bb7171400588f7bb1bc1b43e3d1db53ccb7ac00829e341f06f4bcce1d142c30
    
    ## Decision and scope
    
    The five assertions A1, A2a, A2b, A2c and A3 in the bound coverage file match the five named formal theorems in the bound receipt. The reviewed definitions count exactly the objects specified in the bound README and PROOF. The relation is exact in each case. This is a statement-correspondence decision, not a new execution of Lean, human endorsement, a priority determination or permission to release a package that fails another required check.
    
    ## Counting definition and semantic bridge
    
    For natural k and n, comps k n enumerates each ordered list of k positive integers summing to n exactly once. Induction on k establishes this: at k=0 there is one empty list precisely when n=0; at k+1 the index i in List.range n selects the first part i+1 exactly once from 1 through n, followed by an enumerated tail of length k and total n-(i+1). The first part determines its branch uniquely and the tail is unique by induction. No truncated subtraction changes a valid branch because i+1 is at most n. The definition also returns no nonempty list at total zero.
    
    adjDistinct checks each adjacent pair recursively, with the empty and singleton cases vacuously true. Consequently carlitz n k, the length of the filtered list, is the public count a(n,k), without a multiplicity or ordering change. The inspected core lemmas F_literal and carlitz_eq_F link the recursion used by the formal argument to this literal enumeration; the formal argument is not merely a theorem about an unrelated recurrence.
    
    ## Assertion correspondence
    
    A1 -> carlitz_logconcavity_fails. The domain m >= 104, n=3*m+2, middle index 2*m and neighboring indices 2*m-1 and 2*m+1 agree. Multiplication of the middle count by itself equals its square. The comparison is strict in the same direction. Every integer in this domain is a natural number, so the formal quantifier drops no admissible case.
    
    A2a -> carlitz_A. For every m >= 2, the upper endpoint count is m+1.
    
    A2b -> carlitz_B. For every m >= 2, the middle count is m*(3*m+1).
    
    A2c -> carlitz_C. For every m >= 2, the natural-number equality 24*C + 277*m^2 + 312 = m^4 + 114*m^3 + 426*m is equivalent over the integers to the stated quartic numerator divided by 24. Division by the positive integer 24 introduces no rounding or new premise. The domain excludes m=1, as the written proof requires. All neighboring lengths are nonnegative on the asserted domains.
    
    A3 -> carlitz_n314. The conjunction gives a(314,207)=10094513, a(314,208)=32552 and a(314,209)=105, in the same order as the public statement.
    
    ## Execution evidence inspected
    
    The separate formal verifier's original V2 record identifies the exact r2 source, successful compilation of the 13 theorem modules, separate execution of Axioms.lean, a fresh second compilation and stored-declaration replay including the entire import closure. The printed output for the five statements and their axiom dependencies was reconstructed and matched to SHA-256 ec001ee8bceaadd6c87dc870b95418d8b2bf78197f28d6808b8f3852921a3407. Each assertion has the reported dependency set propext, Classical.choice and Quot.sound. The public receipt's source identity, target signatures and stated checking scope agree with that original record.
    
    All those executions use the same Lean 4.34.0 kernel implementation; the second compilation and replay are not a separately implemented kernel. This reviewer did not execute Lean or independently download every underlying log file. The final package integrity check must still match all included sources and referenced evidence to their recorded hashes. Fourteen Lean source files include the reporting file Axioms.lean; the theorem import closure contains the 13 compiled result modules.
    
    ## Limits preserved in the public wording
    
    The Lean proof uses a first-part recursion. This review does not claim that each transfer-matrix or generating-function step of PROOF.md was formalized. The Python programs, certificates, finite observations and background source note remain outside formal coverage, as the bound coverage file states.
    
    The additional family at (3*m+1,2*m) is explicitly presented only for the observed finite range 52 <= m <= 106 within totals at most 320; it is not promoted to an all-m formal theorem. No least counterexample over an unbounded domain or unimodality theorem is claimed. The README identifies the closing proof-assistant disclaimer in the unchanged PROOF.md as historical r1 wording, not as the status of r2.
    
    The zero-open-issues field above refers only to this exact statement-correspondence scope. Final release integrity, confidentiality, publication-control checks and correct destination readback remain separate requirements. Any change to one of the four bound files requires renewed binding review; an unrelated implementation change does not itself alter this mathematical decision.
<!-- END INDENTED HISTORICAL CORRESPONDENCE -->
