import CarlitzSteps

/-! PRT-CAR-001 — main theorems. Core Lean 4.34.0 only. -/

theorem evenOK_two : EvenOK 2 := by unfold EvenOK; decide

theorem oddOK_of_evenOK (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : OddOK j :=
  ⟨st_o0_2 j hj h, st_o0_3 j hj h, st_o0_4 j hj h, st_o0_5 j hj h, st_o0_6 j hj h, st_o1_0 j hj h, st_o1_1 j hj h, st_o1_2 j hj h, st_o1_3 j hj h, st_o1_4 j hj h, st_o1_5 j hj h, st_o2_1 j hj h, st_o2_2 j hj h, st_o2_3 j hj h, st_o2_4 j hj h, st_o3_1 j hj h, st_o3_2 j hj h, st_o3_3 j hj h, st_o4_0 j hj h, st_o4_1 j hj h, st_o4_2 j hj h⟩

theorem evenOK_succ (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : EvenOK (j+1) := by
  unfold EvenOK
  exact ⟨st_e0_1 j hj h, st_e0_2 j hj h, st_e0_3 j hj h, st_e0_4 j hj h, st_e0_5 j hj h, st_e1_1 j hj h, st_e1_2 j hj h, st_e1_3 j hj h, st_e1_4 j hj h, st_e2_0 j hj h, st_e2_1 j hj h, st_e2_2 j hj h, st_e2_3 j hj h, st_e3_1 j hj h, st_e3_2 j hj h, st_e4_1 j hj h⟩

theorem allOK_aux (d : Nat) : EvenOK (2+d) ∧ OddOK (2+d) := by
  induction d with
  | zero => exact ⟨evenOK_two, oddOK_of_evenOK 2 (Nat.le_refl 2) evenOK_two⟩
  | succ d ih =>
    have he := evenOK_succ (2+d) (by omega) ih.2
    exact ⟨he, oddOK_of_evenOK (2+d+1) (by omega) he⟩

theorem allOK (j : Nat) (hj : 2 ≤ j) : EvenOK j ∧ OddOK j := by
  have := allOK_aux (j - 2)
  rwa [show 2 + (j - 2) = j by omega] at this

/-- Assertion A2, closed form A (m ≥ 2). -/
theorem carlitz_A (m : Nat) (hm : 2 ≤ m) : carlitz (3*m+2) (2*m+1) = m + 1 := by
  have h := (allOK m hm).2
  unfold OddOK at h
  obtain ⟨-, -, -, -, -, hA, -, -, -, -, -, -, -, -, -, -, -, -, hC, -, -⟩ := h
  rw [carlitz_eq_F, show 3*m+2 = 3*m+1+1 by omega]
  omega

/-- Assertion A2, closed form B (m ≥ 2). -/
theorem carlitz_B (m : Nat) (hm : 2 ≤ m) : carlitz (3*m+2) (2*m) = m * (3*m+1) := by
  have h := (allOK m hm).1
  unfold EvenOK at h
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, -, -, -, -, -⟩ := h
  rw [carlitz_eq_F]
  have : (F (2*m) (3*m+2) 0 : Int) = (m : Int) * (3*m+1) := by grind
  exact_mod_cast this

/-- Assertion A2, closed form C (m ≥ 2), stated multiplied by 24 to stay in ℕ. -/
theorem carlitz_C (m : Nat) (hm : 2 ≤ m) :
    24 * carlitz (3*m+2) (2*m-1) + 277*m^2 + 312 = m^4 + 114*m^3 + 426*m := by
  by_cases h2 : m = 2
  · subst h2; decide
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h := (allOK j (by omega)).2
  unfold OddOK at h
  obtain ⟨-, -, -, -, -, hA, -, -, -, -, -, -, -, -, -, -, -, -, hC, -, -⟩ := h
  rw [carlitz_eq_F, show 2*(j+1)-1 = 2*j+1 by omega, show 3*(j+1)+2 = 3*j+1+4 by omega]
  grind

/-- Main assertion A1 (the published claim). -/
theorem carlitz_logconcavity_fails (m : Nat) (hm : 104 ≤ m) :
    carlitz (3*m+2) (2*m) * carlitz (3*m+2) (2*m) <
      carlitz (3*m+2) (2*m-1) * carlitz (3*m+2) (2*m+1) := by
  rw [carlitz_A m (by omega), carlitz_B m (by omega)]
  have hC := carlitz_C m (by omega)
  obtain ⟨t, rfl⟩ : ∃ t, m = 104 + t := ⟨m - 104, by omega⟩
  generalize carlitz (3*(104+t)+2) (2*(104+t)-1) = c at hC ⊢
  have key : 24 * (c * (104 + t + 1)) = 24 * ((104+t) * (3*(104+t)+1) * ((104+t) * (3*(104+t)+1)))
      + ((t^5 + 419*t^4 + 65837*t^3 + 4598485*t^2 + 120548802*t) + 6987864) := by grind
  generalize c * (104 + t + 1) = Z at key ⊢
  generalize (104+t) * (3*(104+t)+1) * ((104+t) * (3*(104+t)+1)) = X at key ⊢
  generalize t^5 + 419*t^4 + 65837*t^3 + 4598485*t^2 + 120548802*t = Y at key
  omega

/-- Assertion A3 (explicit values at m = 104). -/
theorem carlitz_n314 :
    carlitz 314 207 = 10094513 ∧ carlitz 314 208 = 32552 ∧ carlitz 314 209 = 105 := by
  have hA := carlitz_A 104 (by omega)
  have hB := carlitz_B 104 (by omega)
  have hC := carlitz_C 104 (by omega)
  rw [show 3*104+2 = 314 from rfl, show 2*104+1 = 209 from rfl] at hA
  rw [show 3*104+2 = 314 from rfl, show 2*104 = 208 from rfl, show 104*(3*104+1) = 32552 from rfl] at hB
  rw [show 3*104+2 = 314 from rfl, show 2*104-1 = 207 from rfl, show (104:Nat)^2 = 10816 from rfl,
    show (104:Nat)^3 = 1124864 from rfl, show (104:Nat)^4 = 116985856 from rfl] at hC
  generalize carlitz 314 207 = c207 at hC ⊢
  generalize carlitz 314 208 = c208 at hB ⊢
  generalize carlitz 314 209 = c209 at hA ⊢
  omega
