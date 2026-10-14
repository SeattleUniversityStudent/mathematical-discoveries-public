import CarlitzStates

theorem st_o4_2 (j : Nat) (hj : 2 ≤ j) (h : EvenOK j) : (24 * (F (2*j+1) (3*j+1+4) 2 : Nat) : Int) = (-120:Int)*1 + (342:Int)*(j:Int) + (-25:Int)*(j:Int)^2 + (90:Int)*(j:Int)^3 + (1:Int)*(j:Int)^4 := by
  unfold EvenOK at h
  obtain ⟨-, -, -, -, h_st_e0_5, -, -, -, h_st_e1_4, -, -, -, h_st_e2_3, -, -, h_st_e4_1⟩ := h
  rw [F]
  rw [sum_range_trunc _ 5 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+1+4 - (0 + 1) = 3*j+4 by omega, show 3*j+1+4 - (2 + 1) = 3*j+2 by omega, show 3*j+1+4 - (3 + 1) = 3*j+1 by omega, show 3*j+1+4 - (4 + 1) = 3*j by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e0_1 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)) 1 : Nat) : Int) = (24:Int)*1 := by
  unfold OddOK at h
  obtain ⟨h_st_o0_2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1) = 3*j+3 by omega]
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3 - (1 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e0_2 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)) 2 : Nat) : Int) = (24:Int)*1 := by
  unfold OddOK at h
  obtain ⟨-, -, -, -, -, -, h_st_o1_1, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1) = 3*j+3 by omega]
  rw [F]
  rw [sum_range_trunc _ 2 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3 - (0 + 1) = 3*j+1+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e0_3 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)) 3 : Nat) : Int) = (48:Int)*1 := by
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

theorem st_e0_4 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)) 4 : Nat) : Int) = (48:Int)*1 := by
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
