import CarlitzSpec

/-! Core lemmas for PRT-CAR-001. Core Lean 4.34.0 only. -/

/-- F k n p: Carlitz compositions of n with k parts whose first part is not p (p = 0: no restriction). -/
def F : Nat → Nat → Nat → Nat
  | 0, n, _ => if n = 0 then 1 else 0
  | k+1, n, p => ((List.range n).map fun i => if i + 1 = p then 0 else F k (n - (i+1)) (i+1)).sum

/-- "First part differs from p" (p = 0 means no restriction). -/
def headNe (p : Nat) : List Nat → Bool
  | a :: _ => p == 0 || a != p
  | [] => true

theorem count_flatMap {α β} (L : List α) (g : α → List β) (P : β → Bool) :
    ((L.flatMap g).filter P).length = (L.map fun a => ((g a).filter P).length).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.filter_append, ih]

theorem F_literal (k : Nat) : ∀ n p,
    ((comps k n).filter (fun l => adjDistinct l && headNe p l)).length = F k n p := by
  induction k with
  | zero => intro n p; by_cases h : n = 0 <;> simp [comps, F, h, adjDistinct, headNe]
  | succ k ih =>
    intro n p
    simp only [comps, F]
    rw [count_flatMap]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [List.filter_map, List.length_map]
    by_cases hp : i + 1 = p
    · simp only [hp, ite_true]
      apply List.length_eq_zero_iff.mpr
      apply List.filter_eq_nil_iff.mpr
      intro l _
      cases l with
      | nil => simp [Function.comp, adjDistinct, headNe]; omega
      | cons b t => simp [Function.comp, adjDistinct, headNe]; omega
    · simp only [hp, ite_false]
      rw [← ih (n - (i+1)) (i+1)]
      congr 1
      apply List.filter_congr
      intro l _
      cases l with
      | nil => simp [Function.comp, adjDistinct, headNe]; omega
      | cons b t =>
        simp only [Function.comp, adjDistinct, headNe]
        cases t with
        | nil =>
          by_cases hb : b = i + 1
          · subst hb; simp [adjDistinct]
          · have h1 : (i + 1 != p) = true := by simpa [bne_iff_ne] using hp
            have h2 : (i + 1 != b) = true := by simpa [bne_iff_ne] using (Ne.symm hb)
            have h3 : (b != i + 1) = true := by simpa [bne_iff_ne] using hb
            simp [adjDistinct, h1, h2, h3]
        | cons c u =>
          by_cases hb : b = i + 1
          · subst hb; simp [adjDistinct]
          · have h1 : (i + 1 != p) = true := by simpa [bne_iff_ne] using hp
            have h2 : (i + 1 != b) = true := by simpa [bne_iff_ne] using (Ne.symm hb)
            have h3 : (b != i + 1) = true := by simpa [bne_iff_ne] using hb
            simp [adjDistinct, h1, h2, h3]

theorem carlitz_eq_F (n k : Nat) : carlitz n k = F k n 0 := by
  rw [← F_literal k n 0, carlitz]
  congr 1
  apply List.filter_congr
  intro l _
  cases l <;> simp [headNe]

/-- Minimum sum of a Carlitz composition with k parts whose first part is not p. -/
def minsum (k p : Nat) : Nat :=
  if k = 0 then 0 else if k % 2 = 0 then 3 * k / 2 else if p = 1 then (3 * k + 1) / 2 else (3 * k - 1) / 2

theorem minsum_step (k p q : Nat) (hq : 1 ≤ q) (hpq : q ≠ p) :
    minsum (k+1) p ≤ q + minsum k q := by
  unfold minsum
  repeat' split
  all_goals omega

theorem F_vanish (k : Nat) : ∀ n p, n < minsum k p → F k n p = 0 := by
  induction k with
  | zero => intro n p h; simp [minsum] at h
  | succ k ih =>
    intro n p h
    simp only [F]
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    split
    · rfl
    · rename_i hip
      apply ih
      have := minsum_step k p (i+1) (by omega) hip
      omega

theorem sum_range_trunc (t : Nat → Nat) (L n : Nat) (hL : L ≤ n)
    (h : ∀ i, L ≤ i → i < n → t i = 0) :
    ((List.range n).map t).sum = ((List.range L).map t).sum := by
  induction n with
  | zero => have : L = 0 := by omega
            subst this; rfl
  | succ n ih =>
    by_cases hLn : L = n + 1
    · subst hLn; rfl
    · rw [List.range_succ, List.map_append, List.sum_append]
      rw [ih (by omega) (fun i h1 h2 => h i h1 (by omega))]
      simp [h n (by omega) (by omega)]
