import CarlitzStates

theorem st_o0_2 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1) 2 : Nat) : Int) = (24:Int)*1 := by
  unfold EvenOK at h
  obtain ⟨h_st_e0_1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 1 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1 - (0 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o0_3 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1) 3 : Nat) : Int) = (24:Int)*1 := by
  unfold EvenOK at h
  obtain ⟨h_st_e0_1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 1 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1 - (0 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o0_4 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1) 4 : Nat) : Int) = (24:Int)*1 := by
  unfold EvenOK at h
  obtain ⟨h_st_e0_1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 1 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1 - (0 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o0_5 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1) 5 : Nat) : Int) = (24:Int)*1 := by
  unfold EvenOK at h
  obtain ⟨h_st_e0_1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 1 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1 - (0 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_o0_6 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1) 6 : Nat) : Int) = (24:Int)*1 := by
  unfold EvenOK at h
  obtain ⟨h_st_e0_1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [F]
  rw [sum_range_trunc _ 1 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1 - (0 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind
