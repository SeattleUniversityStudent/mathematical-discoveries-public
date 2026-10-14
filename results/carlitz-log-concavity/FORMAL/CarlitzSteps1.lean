import CarlitzStates

theorem st_o1_0 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1+1) 0 : Nat) : Int) = (24:Int)*1 + (24:Int)*(j:Int) := by
  unfold EvenOK at h
  obtain ⟨-, h_st_e0_2, -, -, -, h_st_e1_1, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1+1 - (0 + 1) = 3*j+1 by omega, show 3*j+1+1 - (1 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o1_1 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1+1) 1 : Nat) : Int) = (24:Int)*1 := by
  unfold EvenOK at h
  obtain ⟨-, h_st_e0_2, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1+1 - (1 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o1_2 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1+1) 2 : Nat) : Int) = (24:Int)*(j:Int) := by
  unfold EvenOK at h
  obtain ⟨-, -, -, -, -, h_st_e1_1, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1+1 - (0 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o1_3 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1+1) 3 : Nat) : Int) = (24:Int)*1 + (24:Int)*(j:Int) := by
  unfold EvenOK at h
  obtain ⟨-, h_st_e0_2, -, -, -, h_st_e1_1, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1+1 - (0 + 1) = 3*j+1 by omega, show 3*j+1+1 - (1 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o1_4 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1+1) 4 : Nat) : Int) = (24:Int)*1 + (24:Int)*(j:Int) := by
  unfold EvenOK at h
  obtain ⟨-, h_st_e0_2, -, -, -, h_st_e1_1, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1+1 - (0 + 1) = 3*j+1 by omega, show 3*j+1+1 - (1 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind
