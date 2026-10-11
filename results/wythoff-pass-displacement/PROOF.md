# A bounded displacement for Wythoff Nim with one pass

Two nonnegative heaps permit arbitrary reduction of one heap or equal reduction of both. Normal play applies. Either player may instead consume one shared pass, except at the empty position. A P position is losing for the next player.

For every P position with the pass unused and heaps a <= b, set d=b-a and phi=(1+sqrt(5))/2. Then |a-floor(phi*d)| <= 17.

Theorem 5 of the source below gives an ordinary Wythoff P position within Euclidean distance sqrt(20). Sorting its coordinates preserves that bound. Write it as (v,w)=(floor(phi*n),floor(phi*n)+n). Integer coordinate differences have absolute value at most four, so |d-n|<=8. Consequently |floor(phi*d)-floor(phi*n)|<=ceil(8*phi)=13, giving the stated bound. This loose constant only translates an established theorem.

Source: Miyadera, Manabe and Fukui, *Wythoff's Game with a Pass*, Integers 25 (2025), G4, Theorems 2 and 5; https://math.colgate.edu/~integers/zg4/zg4.pdf ; associated arXiv:1711.04960v2. The relevant text was read. No game computation, optimality argument, formal verification or separate review is supplied.
