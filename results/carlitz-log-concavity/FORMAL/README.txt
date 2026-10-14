PRT-CAR-001 Lean formalization, source revision r2 (2026-10-11).
Toolchain: Lean 4.34.0 official release (commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b), core library only; no Mathlib, no Lake.
Build: put the Lean 4.34.0 `bin` directory first on PATH, then run ./build.sh (sequential `lean -o build/<M>.olean <M>.lean`, LEAN_PATH=build).
Axiom report: LEAN_PATH=build lean Axioms.lean   (prints #print axioms and the release-theorem signatures).
Release theorems (CarlitzMain.lean): carlitz_logconcavity_fails, carlitz_A, carlitz_B, carlitz_C, carlitz_n314.
Definitions (CarlitzSpec.lean): comps (literal enumeration), adjDistinct, carlitz.
Proof route: a first-part recursion F proved equal to the literal count (F_literal, carlitz_eq_F), a minimum-sum
vanishing lemma, and generated induction steps for the closed forms at slack <= 4; this is an alternative route to
the transfer-matrix argument in PROOF.md, not a line-by-line formalization of it.
gen/: Python scripts that computed the state closure and polynomials and generated CarlitzStates/CarlitzSteps*.lean.
They are provenance only; Lean checks the generated proofs independently of them.
Revision r2 differs from r1 only in comments, this README and build.sh (no hard-coded toolchain path); the
r1 author-side outputs axioms_report.txt and build_all.log are not included.
