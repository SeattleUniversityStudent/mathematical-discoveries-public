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
