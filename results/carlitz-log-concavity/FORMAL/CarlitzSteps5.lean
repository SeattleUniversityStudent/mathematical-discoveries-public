import CarlitzStates

theorem st_e0_5 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)) 5 : Nat) : Int) = (48:Int)*1 := by
  unfold OddOK at h
  obtain ⟨h_st_o0_2, -, -, -, -, -, h_st_o1_1, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1) = 3*j+3 by omega]
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3 - (0 + 1) = 3*j+1+1 by omega, show 3*j+3 - (1 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e1_1 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+1) 1 : Nat) : Int) = (24:Int)*((j+1):Int) := by
  unfold OddOK at h
  obtain ⟨-, h_st_o0_3, -, -, -, -, -, h_st_o1_2, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+1 = 3*j+3+1 by omega]
  rw [F]
  rw [sum_range_trunc _ 3 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+1 - (1 + 1) = 3*j+1+1 by omega, show 3*j+3+1 - (2 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e1_2 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+1) 2 : Nat) : Int) = (-24:Int)*1 + (72:Int)*((j+1):Int) := by
  unfold OddOK at h
  obtain ⟨-, h_st_o0_3, -, -, -, -, -, -, -, -, -, h_st_o2_1, -, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+1 = 3*j+3+1 by omega]
  rw [F]
  rw [sum_range_trunc _ 3 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+1 - (0 + 1) = 3*j+1+2 by omega, show 3*j+3+1 - (2 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e1_3 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+1) 3 : Nat) : Int) = (-72:Int)*1 + (96:Int)*((j+1):Int) := by
  unfold OddOK at h
  obtain ⟨-, -, -, -, -, -, -, h_st_o1_2, -, -, -, h_st_o2_1, -, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+1 = 3*j+3+1 by omega]
  rw [F]
  rw [sum_range_trunc _ 3 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+1 - (0 + 1) = 3*j+1+2 by omega, show 3*j+3+1 - (1 + 1) = 3*j+1+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e1_4 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+1) 4 : Nat) : Int) = (-48:Int)*1 + (96:Int)*((j+1):Int) := by
  unfold OddOK at h
  obtain ⟨-, h_st_o0_3, -, -, -, -, -, h_st_o1_2, -, -, -, h_st_o2_1, -, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+1 = 3*j+3+1 by omega]
  rw [F]
  rw [sum_range_trunc _ 3 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+1 - (0 + 1) = 3*j+1+2 by omega, show 3*j+3+1 - (1 + 1) = 3*j+1+1 by omega, show 3*j+3+1 - (2 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind
