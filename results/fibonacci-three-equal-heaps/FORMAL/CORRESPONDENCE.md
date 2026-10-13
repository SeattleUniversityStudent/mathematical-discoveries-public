# Final statement-correspondence review — four finite outcomes

Reviewer ID: package-correspondent-1
Reviewed receipt SHA-256: b98019d45b244340c2a22fc83182c8b935f311847bd1ed4ab8200cb2ff41cf51
Reviewed coverage SHA-256: c6c5f6c0ab0eefdf175539c50c0027c399ccbb4e1248147de6d566c743dcbddf
Reviewed README SHA-256: c569aa6e11fc707797715a5b3419bc679abb9bf26b805ffcca43fa6c249de2d3
Reviewed PROOF SHA-256: 458b26d99821f94b3c2783ecbc028f4edc9ed8d4b20c6d254bc5101860795c3e
Open issues: 0
Verdict: Passed

## Independence and actual scope

This AI reviewer is distinct from the producer, formalization author, formal verifier and publisher. The reviewer performed independent read-only source, statement and final-package correspondence inspection and wrote this report. This is not human review or endorsement. Earlier accepted mathematical review, clean build, axiom audit and stored-declaration replay were reused; none was repeated by this reviewer. Their execution remains attributed to their recorded authors and verifier.

The exact final files named above were inspected. The package archive and every payload path, size and hash were checked against its manifest. All 127 submitted Lean sources are unchanged from the previously accepted source. The final revision corrects the written-bridge locator and adds a publisher rerun record for the unchanged independent review program, with the historical binary-comparison limitation stated explicitly. The receipt's proof hash matches the inspected written note. This review does not issue a release-tool verdict, exact commit-patch approval or public-delivery receipt.

## Four assertions and formal meanings

The coverage entries match the following declarations in namespace RQ9F1:

| Public assertion, first bound 1 | Formal declaration | Formal conclusion |
| --- | --- | --- |
| Three heaps of 6 form a P-position | triple_six_is_P | Outcome ⟨6,6,6,1⟩ false |
| One heap of 6 forms an N-position | single_six_is_N | Outcome ⟨0,0,6,1⟩ true |
| Three heaps of 20 form an N-position | triple_twenty_is_N | Outcome ⟨20,20,20,1⟩ true |
| One heap of 20 forms a P-position | single_twenty_is_P | Outcome ⟨0,0,20,1⟩ false |

These are the four bounded formal assertions stated in the README and coverage record. Together they demonstrate outcome changes in both directions after deleting two equal heaps in these examples. The single-heap notation is represented by two zero heaps, with no legal moves from those zero heaps. Reconstruction and unreviewed-draft labels remain appropriate; formal checking does not establish priority.

## Model-to-game correspondence

Model.lean enumerates a removal from exactly one of three labelled heaps. For a heap of size h and current bound r, its list ranges over k from zero to min(h,r)-1 and removes t=k+1. Thus it contains exactly the moves with 1≤t≤min(h,r), leaves other heaps unchanged, and sets the shared next bound to 2t. No zero removal, truncated subtraction, lost heap multiplicity or pair-deletion assumption is introduced. Every move strictly decreases the total counter count.

The written argument in FORMAL/provenance/MODEL_AND_CORRESPONDENCE_NOTE.md applies induction on that total. Outcome.win supplies a legal follower with a false derivation; Outcome.lose supplies true derivations for every entry in the complete move list. The empty move list gives the normal-play losing terminal case. By induction these constructors have the intended N/P meaning; conversely, normal-play winning and losing classifications assemble the respective finite derivations. The fixed first bound is positive and every successor bound is positive, so the model's immobile bound-zero extension does not affect these claims. Labels are retained in the formal state; sorting used by source-generation assistance supplies no trusted symmetry premise.

This establishes the required written semantic bridge for the four formal conclusions. The generic equivalence itself is written mathematics, not a Lean theorem. The accepted formal receipt reports a clean build and separate fresh stored-declaration replay for the exact source, with only propext in each of the four transitive axiom footprints. Replay coverage is supported by the recorded checker/import closure; no individual-declaration verbose replay log or second compilation is claimed.

## Limits and reused evidence

No Sprague–Grundy value, full finite census, threshold recurrence, first-discrepancy minimality, all-n classification, infinite family or novelty statement is formally accepted by this report. Those historical computations in the written note remain expressly outside the four-declaration formal scope. The original mathematical AI review and its retained independent program/output are separate evidence.

The publisher's new independent-program rerun receipt and actual supplied output were inspected; the output matches the retained reviewer output apart from two elapsed-time lines. This reviewer did not execute that program. The retained program implements its stated finite checks and does not read or hash producer binary certificates. The additional historical comparison helper is not retained, and its binary-reproduction claims remain attributed to the historical verdict. The publisher's producer-program reruns and the accepted Lean chain remain separately recorded evidence.

No universal literature search, copyright-ownership determination, human endorsement or release-tool acceptance is represented here. No open statement-correspondence issue remains for the exact four bound files and four finite assertions above. Changes to those files or assertion scope require focused reinspection and new bindings.
