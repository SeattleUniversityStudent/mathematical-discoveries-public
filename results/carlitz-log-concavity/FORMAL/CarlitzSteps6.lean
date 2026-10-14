import CarlitzStates

theorem st_e2_0 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+2) 0 : Nat) : Int) = (24:Int)*((j+1):Int) + (72:Int)*((j+1):Int)^2 := by
  unfold OddOK at h
  obtain ⟨-, -, h_st_o0_4, -, -, -, -, -, h_st_o1_3, -, -, -, h_st_o2_2, -, -, h_st_o3_1, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+2 = 3*j+3+2 by omega]
  rw [F]
  rw [sum_range_trunc _ 4 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+2 - (0 + 1) = 3*j+1+3 by omega, show 3*j+3+2 - (1 + 1) = 3*j+1+2 by omega, show 3*j+3+2 - (2 + 1) = 3*j+1+1 by omega, show 3*j+3+2 - (3 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e2_1 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+2) 1 : Nat) : Int) = (-24:Int)*1 + (84:Int)*((j+1):Int) + (12:Int)*((j+1):Int)^2 := by
  unfold OddOK at h
  obtain ⟨-, -, h_st_o0_4, -, -, -, -, -, h_st_o1_3, -, -, -, h_st_o2_2, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+2 = 3*j+3+2 by omega]
  rw [F]
  rw [sum_range_trunc _ 4 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+2 - (1 + 1) = 3*j+1+2 by omega, show 3*j+3+2 - (2 + 1) = 3*j+1+1 by omega, show 3*j+3+2 - (3 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e2_2 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+2) 2 : Nat) : Int) = (48:Int)*1 + (-36:Int)*((j+1):Int) + (60:Int)*((j+1):Int)^2 := by
  unfold OddOK at h
  obtain ⟨-, -, h_st_o0_4, -, -, -, -, -, h_st_o1_3, -, -, -, -, -, -, h_st_o3_1, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+2 = 3*j+3+2 by omega]
  rw [F]
  rw [sum_range_trunc _ 4 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+2 - (0 + 1) = 3*j+1+3 by omega, show 3*j+3+2 - (2 + 1) = 3*j+1+1 by omega, show 3*j+3+2 - (3 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e2_3 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+2) 3 : Nat) : Int) = (72:Int)*((j+1):Int)^2 := by
  unfold OddOK at h
  obtain ⟨-, -, h_st_o0_4, -, -, -, -, -, -, -, -, -, h_st_o2_2, -, -, h_st_o3_1, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+2 = 3*j+3+2 by omega]
  rw [F]
  rw [sum_range_trunc _ 4 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+2 - (0 + 1) = 3*j+1+3 by omega, show 3*j+3+2 - (1 + 1) = 3*j+1+2 by omega, show 3*j+3+2 - (3 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e3_1 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+3) 1 : Nat) : Int) = (96:Int)*1 + (-160:Int)*((j+1):Int) + (132:Int)*((j+1):Int)^2 + (4:Int)*((j+1):Int)^3 := by
  unfold OddOK at h
  obtain ⟨-, -, -, h_st_o0_5, -, -, -, -, -, h_st_o1_4, -, -, -, h_st_o2_3, -, -, h_st_o3_2, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+3 = 3*j+3+3 by omega]
  rw [F]
  rw [sum_range_trunc _ 5 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+3 - (1 + 1) = 3*j+1+3 by omega, show 3*j+3+3 - (2 + 1) = 3*j+1+2 by omega, show 3*j+3+3 - (3 + 1) = 3*j+1+1 by omega, show 3*j+3+3 - (4 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind
