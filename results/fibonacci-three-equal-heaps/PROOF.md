# Three equal heaps in global Fibonacci Nim

Proof status: unreviewed draft.

## Question and definitions

A position is (a,b,c;r), with nonnegative integer heap sizes and a positive integer bound r. A move removes t counters from one heap, where 1 <= t <= r and that heap contains at least t counters. The next bound is 2t. The empty position loses. A P-position loses for the player to move; an N-position has a move to a P-position. Permuting heaps does not change the game.

The question is to describe all positive n for which (n,n,n;1) is P. No all-n classification is obtained here. The finite results below rule out replacing three equal heaps by a single heap.

## A threshold recurrence

For a heap tuple h, let T(h) be the least positive bound for which (h;r) is N, or infinity when no such bound exists. Then

T(h) = min { t : some heap of h is at least t and T(sort(h - t e_i)) > 2t },

where the minimum of an empty set is infinity. In particular T(0,0,0) is infinity.

This follows by induction on the total number of counters. The followers after a removal of size t have bound 2t, independently of the previous bound r. By the induction hypothesis, that follower is P precisely when its threshold exceeds 2t. Therefore a winning removal is available exactly when r is at least the minimum displayed above. This also establishes that (h;r) is P exactly when r < T(h). The recurrence is a routine exact evaluation procedure, not the requested structural classification.

Two equal heaps form a P-position at every positive bound: after a removal of t from one heap, the opponent can remove t from the other, since t <= 2t. Repeating this response ensures the responding player makes the last move. Consequently T(n,n,n) <= n for n > 0: removing one entire heap leaves two equal heaps. This argument does not permit deleting equal heaps from a larger position, because their moves change the shared bound.

## Finite counterexamples to equal-pair deletion

The direct legal-move calculation gives:

| Position | Sprague-Grundy value | Outcome |
| --- | --- | --- |
| (6,6,6;1) | 0 | P |
| (0,0,6;1) | 1 | N |
| (5,6,6;2) | 1 | N |
| (4,6,6;2) | 0 | P |
| (20,20,20;1) | 1 | N |
| (0,0,20;1) | 0 | P |
| (19,20,20;2) | 0 | P |

Thus deleting two equal heaps can change the outcome in either direction. Every first move from (6,6,6;1) gives (5,6,6;2), whose winning response removes one more counter from its smallest heap. At n=20 the unique first move up to symmetry is winning.

For n=1,...,8 the calculated equal-triple thresholds are 1,2,3,1,5,6,7,8. The smallest Fibonacci summands in the corresponding Zeckendorf representations are 1,2,3,1,5,1,2,8. In particular n=6 is the first discrepancy with the one-heap threshold among positive integers. The finite table establishes this minimality only because every smaller integer is included.

## Reproducible finite evidence

The threshold program evaluates every sorted tuple 0 <= a <= b <= c <= 80, in lexicographic order. Every follower occurs earlier. Its 91,881 thresholds are saved as unsigned 16-bit little-endian integers, with 65,535 representing infinity. All tested finite bounds are below this sentinel. The program examined 730,751 removal instances before the first winning one at each position or exhaustion. This is not a count of all edges.

A separately written program retains r explicitly and computes the mex of all legal follower values. It reads neither the threshold program's functions nor its recurrence. It evaluates every sorted tuple bounded by 20, for every r=1,...,40: 70,840 states and 1,788,710 legal removal instances. All outcomes agree with the threshold data. Its certificate stores the resulting Grundy values as bytes in the order a=0,...,20; b=a,...,20; c=b,...,20; r=1,...,40.

This domain is closed under moves: no heap increases and each successor bound is 2t <= 40. The total number of counters strictly decreases, so the ordinary mex induction terminates. Together with the complete inventory and legal-move definition, the attached program and certificate give a finite, reproducible calculation of the displayed values.

> Publisher delivery note (not part of the original note; original PROOF.md sha256 c367476ab246ae7203d2c73112edf98c13125e4b868ccfe6ba81000db8a641fc): this package contains the programs, their logs and receipts, but not the two binary files named in this note, the threshold data (sha256 eee40b74dd77099183c5c64ce3c26f9a79cace7dd89a1bf62132fbee7e8341ef) and the literal certificate (sha256 8bc6a2357846f88c6e693a6f3fa86f20da60de195bd2b8aa3919c255dd2969c7). Running the commands in RERUN.json regenerates both files; the publisher's rerun reproduced both with the hashes stated here, and the review verdict (review/reviewer-1/verdict.md, step 14) records that the reviewer's rerun of those commands did so as well. The words "attached program and certificate" refer to the original delivery, which included the binaries. The two implementations are from the same producer and do not constitute separate review.

The threshold binary has SHA256 eee40b74dd77099183c5c64ce3c26f9a79cace7dd89a1bf62132fbee7e8341ef. The literal certificate has SHA256 8bc6a2357846f88c6e693a6f3fa86f20da60de195bd2b8aa3919c255dd2969c7. Exact commands and log names are in RERUN.json. No larger domain was independently checked.

## Prior work and limitations

Urban Larsson and Simon Rubinstein-Salzedo, Global Fibonacci Nim, arXiv:1509.08527v1 (2015), https://arxiv.org/html/1509.08527v1: §1 defines the shared bound; §5 gives the one-heap criterion; §6 treats two heaps and §7 gives some multipile results. Its full mathematical text was inspected. No all-n equal-three-heap classification was located there.

The finite counterexamples are useful diagnostics, with priority undetermined. They are not presented as a distinct discovery. The general classification, any asymptotic description, and any infinite family beyond routine consequences remain unresolved. Enlarging the finite table alone would not settle those questions.
