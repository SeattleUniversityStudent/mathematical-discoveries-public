/-
  PRT-CAR-001 — definitions. Main theorems are stated and proved in CarlitzMain.lean.
  Core Lean 4.34.0 only (no Mathlib).

  Published claim (README / PROOF.md):
    a(n,k) = number of ordered lists of k positive integers with sum n and unequal adjacent entries.
    For every integer m ≥ 104, with n = 3m+2:  a(n,2m)^2 < a(n,2m-1) * a(n,2m+1).
    At m = 104: a(314,207)=10094513, a(314,208)=32552, a(314,209)=105.
  Supporting closed forms (m ≥ 2): A=a(n,2m+1)=m+1, B=a(n,2m)=m(3m+1),
    C=a(n,2m-1)=(m^4+114m^3-277m^2+426m-312)/24.
-/

/-- Every list of positive integers of length `k` summing to `n` (literal enumeration).
    Structural recursion on the length `k`, so the kernel can evaluate it. -/
def comps : Nat → Nat → List (List Nat)
  | 0, n => if n = 0 then [[]] else []
  | k+1, n => (List.range n).flatMap fun i =>      -- first part p = i+1, 1 ≤ p ≤ n
      (comps k (n - (i+1))).map fun l => (i+1) :: l

/-- Unequal adjacent entries. -/
def adjDistinct : List Nat → Bool
  | a :: b :: t => a != b && adjDistinct (b :: t)
  | _ => true

/-- a(n,k): the number of Carlitz compositions of n with k parts (literal definition). -/
def carlitz (n k : Nat) : Nat := ((comps k n).filter adjDistinct).length

-- Sanity checks of the literal definition against hand counts (kernel-evaluated):
theorem sanity_5_2 : carlitz 5 2 = 4 := by decide          -- (1,4),(4,1),(2,3),(3,2)
theorem sanity_4_3 : carlitz 4 3 = 1 := by decide          -- (1,2,1)
theorem sanity_8_5 : carlitz 8 5 = 3 := by decide          -- m=2: A = m+1 = 3
