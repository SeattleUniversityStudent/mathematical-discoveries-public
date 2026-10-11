# A cofactor bound from the S-matrix theorem

Proposed proof status: unreviewed draft.
Proposed result status: reconstruction.

Let A be a nonsingular n-by-n binary real matrix, n>=1. Put D=abs(det A) and c(A)=max absolute determinant obtained by deleting one row and one column, with empty determinant1. Let maxnorm denote the largest absolute entry and Fnorm the Frobenius norm.

The bound c(A)>=2D/(n+1), with equality precisely for S-matrices, follows directly from the cited inverse-Frobenius theorem. Here S is binary and S^T S=(n+1)(I+J)/4, where J is the all1 matrix. Equivalently S is the binary complement-core of a normalized Hadamard matrix of order n+1.

The source theorem is Fnorm(A^-1)>=2n/(n+1) for nonsingular A with entries in [0,1], with equality precisely for S-matrices. Its all-order form is cited here from Li's recent preprint, Theorem1.1; the complete source proof has not been independently audited for this note. Hence
c(A)/D=maxnorm(A^-1)>=Fnorm(A^-1)/n>=2/(n+1).
Equality in the cofactor inequality implies equality in the source theorem. Conversely, for an S-matrix, A^-1=2(2A^T-J)/(n+1), so every inverse entry has absolute value2/(n+1). This also covers n=1.

Sources:
- Roman Drnovsek, On the S-matrix Conjecture, LAA439(11)(2013),3555–3560, arXiv:1306.6786v2, Theorem printedp2 and odd-order equality argument p4. https://arxiv.org/pdf/1306.6786
- Elsa Frankel and John Urschel, On the Frobenius Norm of the Inverse of a Non-Negative Matrix, LAA708(2025),193–203, DOI10.1016/j.laa.2024.11.030, Theorem1.2: all n>=1000. https://math.mit.edu/~urschel/preprints/frobenius.pdf
- Yinjie Li, An independent proof of the even-dimensional S-matrix inequality, arXiv:2608.29750v2, Theorem1.1: every n; Sections7–8 delimit formal verification and combine cases. https://arxiv.org/html/2608.29750v2

Limitations: this note checks the direct implication, not the complete recent even-dimensional proof. Li reports a formal argument conditional on Frankel–Urschel Lemma2.1, with native evaluation for finite checks; no formal artifacts were executed here. Teng Zhang's arXiv:2609.20306v1 is cited by Li as an earlier complete proof; that body was not read for this note. No computations, programs or mathematical run logs accompany this note. There is no assertion of an independent discovery, full literature clearance, or human review.
