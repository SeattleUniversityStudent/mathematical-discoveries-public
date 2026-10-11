# mathematical-discoveries-public

Mathematical contributions with explicit claims, proofs, prior-work references and reproducibility records. Each result has its own folder under `results/` with a README, the full proof, the programs and logs, a review record and a manifest of file hashes.

All results here are AI-assisted. Every result states three separate things:

- **Proof status:** "unreviewed draft" means no human expert has reviewed the proof. AI reviews, where present, are recorded in the result's REVIEW.md and do not change this label.
- **Result status:** "known result", "reconstruction", "new claim not cleared" (no prior statement found in a bounded search; priority not established) or "conjecture".
- **Formal verification:** whether the exact published claim has been checked in the Lean proof assistant. A result's formal status covers only the theorems and assumptions its FORMAL/ record lists.

No result here has been reviewed or endorsed by a human expert. Formal verification, where present, does not establish novelty, attribution or human endorsement.

## Release standard

From 2026-10-11, a new result is released only after its exact published claim has passed a Lean formal-verification gate, in addition to AI review, reproducibility, citation and confidentiality checks. The gate requires:

- a clean build;
- a separate replay of the same source;
- printed theorem statements and their transitive axioms, limited to propext, Classical.choice and Quot.sound, with no sorry, no project axioms and no native-evaluation trust;
- a separate review that the formal statements match the published claim.

The three results below were published before this standard was adopted. They have **not** been formally verified, and their formal verification is pending.

## Results

| Result | Proof status | Result status | AI reviews | Formal verification |
| --- | --- | --- | --- | --- |
| [A failure of log-concavity for Carlitz composition lengths](results/carlitz-log-concavity/) | unreviewed draft | new claim not cleared | 2 (two vendors), both passed | none (pending) |
| [Wythoff Nim with one pass: bounded displacement of P-positions](results/wythoff-pass-displacement/) | unreviewed draft | known result | 1, passed | none (pending) |
| [A cofactor bound from the S-matrix theorem](results/s-matrix-cofactor-bound/) | unreviewed draft | reconstruction | 1 review plus recheck of the revision, passed | none (pending) |

## Rights

No licence is granted for the contents of this repository unless a result says otherwise. See each result's RIGHTS.md.
