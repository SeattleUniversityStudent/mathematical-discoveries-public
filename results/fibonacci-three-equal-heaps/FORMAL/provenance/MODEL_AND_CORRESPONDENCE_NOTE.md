# Model and statement-correspondence note for the Lean formalization

Extracted by the publisher from the formalization author's pre-build note (original sha256 f34e3e256a35dcbfa6b9f1e05e2abc3329553a79eb86484b406a31cd3ea25542; the original is kept privately). Only the task statement, the rule correspondence, the strategy-derivation argument and the coverage section are reproduced, with internal labels reworded. Sections on status at the time of writing, input custody, author test runs, the proposed toolchain pin and unrelated pending work are omitted; the toolchain actually used and the build and replay results are in ../verification/ and ../receipt.json.

## Task and boundary

The four normal global Fibonacci Nim claims are (6,6,6;1) P, (0,0,6;1) N, (20,20,20;1) N and (0,0,20;1) P. P means losing for the next player; N means winning. No all-n classification, exact nonzero Grundy value, minimal counterexample or new discovery is claimed.

## Rule and source correspondence

A labelled position is (a,b,c,r), with nonnegative integer heap sizes and positive bound r. In one move choose one coordinate i and remove t with 1<=t<=min(h_i,r), leaving all other heaps unchanged and setting the global next bound to 2t. Zero heaps have no available removal. An empty position has no move and is P.

Primary rule source: Urban Larsson and Simon Rubinstein-Salzedo, Global Fibonacci Nim, arXiv:1509.08527v1, https://arxiv.org/html/1509.08527v1, sections 1 and 2, especially the global-bound rule and P/N recursion. Those passages were read in this batch; the original role had inspected the full manuscript. The journal metadata and abstract were also checked: Global Fibonacci nim, International Journal of Game Theory 47, 595-611 (2018), DOI 10.1007/s00182-017-0574-x, https://link.springer.com/article/10.1007/s00182-017-0574-x . Online publication is 13 March 2017 and issue date May 2018. The journal full subscription body was not read here. This adds the requested bibliographic locator without asserting a new theorem from an unread article.

Model.lean retains three labelled heaps and their multiplicity. The union of its three List.range/map lists contains exactly the legal moves, in heap-index order and increasing removal size. k ranges from zero through min(h_i,r)-1 and t=k+1, so no illegal zero removal, truncated subtraction or lost bound is introduced. Equal heap sizes do not license pair deletion. The definition extends to r=0 as an immobile state, but every root and every reachable nonterminal certificate state has r>0; no claim relies on the extension.

Every move decreases a+b+c by the strictly positive t. Thus play is finite, of length at most the initial total. The source's ordinary backward-induction P/N semantics is well-defined on every state used here.

## Explicit strategy derivations, not a trusted truth table

Outcome p true is generated only by a legal follower q with a derivation of Outcome q false. Outcome p false is generated only by AllWinning (moves p). AllWinning is a mutually defined finite list of winning derivations, with nil and cons constructors. It contains no axiom asserting an outcome, table lookup or untrusted oracle result.

These constructors agree with normal-play semantics. Prove the equivalence by induction on the total counters of p. All legal followers have smaller total. A true derivation gives a legal false follower; by induction that follower is P, so p is N. A false derivation supplies a true derivation for every entry of the complete move list; by induction all followers are N, so p is P, including the empty-list case. Conversely, if p is N, its winning legal move leads to a P follower whose derivation exists by induction, and the win constructor applies. If p is P, all followers are N and their induction-derived proofs assemble into AllWinning, giving the lose constructor. This establishes both directions, exclusivity and the terminal convention. This correspondence argument is written mathematics; its interpretation by the separate statement reviewer and compilation of the inductive definitions remain mandatory.

The Python search oracle is untrusted source-generation assistance. It sorts heap coordinates internally to find useful candidate choices, but all saved strategy states and every emitted formal statement retain labelled heaps. No Lean theorem assumes that the oracle is correct or uses a symmetry theorem. A losing node includes every legal response, including any repeated entries; a winning node keeps only one legal losing follower. Discarding other moves at a winning node is sound for the existential winning condition, not a general state-space equivalence.

Node indices strictly follow decreasing-counter dependencies. Each generated theorem either applies Outcome.win with a local finite-list membership proof by decide, or Outcome.lose with an explicit AllWinning constructor chain for the complete reduced move list. No native_decide, sorry, new axiom or externally trusted computation is present. `by decide` is used for concrete local move membership, not evaluation of the entire game tree. Without compilation this remains a candidate, not a verified statement about what the Lean kernel accepts.

## Exact final candidate and coverage

The submitted Lean sources are 127 files (Model, 125 chunks, Claims); together they contain 6819917 UTF-8 bytes. Its 26041 node derivations retain 77233 complete losing-node response edges and 19846 winning witnesses. The declared root witnesses are:

- RQ9F1.triple_six_is_P: Outcome <6,6,6,1> false, node_5702.
- RQ9F1.single_six_is_N: Outcome <0,0,6,1> true, node_324.
- RQ9F1.triple_twenty_is_N: Outcome <20,20,20,1> true, node_26040.
- RQ9F1.single_twenty_is_P: Outcome <0,0,20,1> false, node_6944.

This covers the four outcome claims and hence both directions of failure of equal-pair deletion. It does not formally establish the predecessor's full 70840-entry Grundy table, threshold recurrence, exact SG=1 claims, least discrepant n, or original binary hashes. Those are deliberately outside this finite-outcome formal target.

