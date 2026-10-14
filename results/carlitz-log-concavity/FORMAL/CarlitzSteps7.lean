import CarlitzStates

theorem st_e3_2 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+3) 2 : Nat) : Int) = (72:Int)*1 + (-124:Int)*((j+1):Int) + (96:Int)*((j+1):Int)^2 + (28:Int)*((j+1):Int)^3 := by
  unfold OddOK at h
  obtain ⟨-, -, -, h_st_o0_5, -, -, -, -, -, h_st_o1_4, -, -, -, h_st_o2_3, -, -, -, -, -, h_st_o4_1, -⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+3 = 3*j+3+3 by omega]
  rw [F]
  rw [sum_range_trunc _ 5 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+3 - (0 + 1) = 3*j+1+4 by omega, show 3*j+3+3 - (2 + 1) = 3*j+1+2 by omega, show 3*j+3+3 - (3 + 1) = 3*j+1+1 by omega, show 3*j+3+3 - (4 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind

theorem st_e4_1 (j : Nat) (hj : 2 ≤ j) (h : OddOK j) : (24 * (F (2*(j+1)) (3*(j+1)+4) 1 : Nat) : Int) = (-120:Int)*1 + (246:Int)*((j+1):Int) + (-97:Int)*((j+1):Int)^2 + (90:Int)*((j+1):Int)^3 + (1:Int)*((j+1):Int)^4 := by
  unfold OddOK at h
  obtain ⟨-, -, -, -, h_st_o0_6, -, -, -, -, -, h_st_o1_5, -, -, -, h_st_o2_4, -, -, h_st_o3_3, -, -, h_st_o4_2⟩ := h
  rw [show 2*(j+1) = (2*j+1)+1 by omega, show 3*(j+1)+4 = 3*j+3+4 by omega]
  rw [F]
  rw [sum_range_trunc _ 6 _ (by omega) (fun i h1 h2 => by
    split
    · rfl
    · refine F_vanish _ _ _ ?_
      unfold minsum; (repeat' split) <;> omega)]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  simp only [show 3*j+3+4 - (1 + 1) = 3*j+1+4 by omega, show 3*j+3+4 - (2 + 1) = 3*j+1+3 by omega, show 3*j+3+4 - (3 + 1) = 3*j+1+2 by omega, show 3*j+3+4 - (4 + 1) = 3*j+1+1 by omega, show 3*j+3+4 - (5 + 1) = 3*j+1 by omega]
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, Nat.add_zero, Nat.zero_add, reduceIte]
  push_cast
  grind
