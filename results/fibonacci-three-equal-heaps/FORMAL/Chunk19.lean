import Chunk18
set_option autoImplicit false
namespace RQ9F1

theorem node_4733 : Outcome ⟨2, 2, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 13, 2⟩, ⟨0, 2, 13, 4⟩, ⟨2, 1, 13, 2⟩, ⟨2, 0, 13, 4⟩, ⟨2, 2, 12, 2⟩, ⟨2, 2, 11, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 2, 9, 8⟩, ⟨2, 2, 8, 10⟩, ⟨2, 2, 7, 12⟩, ⟨2, 2, 6, 14⟩, ⟨2, 2, 5, 16⟩]
  exact AllWinning.cons node_4007 (AllWinning.cons node_3329 (AllWinning.cons node_4055 (AllWinning.cons node_3478 (AllWinning.cons node_4058 (AllWinning.cons node_3487 (AllWinning.cons node_2948 (AllWinning.cons node_2489 (AllWinning.cons node_1994 (AllWinning.cons node_1645 (AllWinning.cons node_1287 (AllWinning.cons node_1006 (AllWinning.nil))))))))))))

theorem node_4734 : Outcome ⟨2, 2, 13, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 13, 2⟩, ⟨0, 2, 13, 4⟩, ⟨2, 1, 13, 2⟩, ⟨2, 0, 13, 4⟩, ⟨2, 2, 12, 2⟩, ⟨2, 2, 11, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 2, 9, 8⟩, ⟨2, 2, 8, 10⟩, ⟨2, 2, 7, 12⟩, ⟨2, 2, 6, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 2, 4, 18⟩, ⟨2, 2, 3, 20⟩]
  exact AllWinning.cons node_4007 (AllWinning.cons node_3329 (AllWinning.cons node_4055 (AllWinning.cons node_3478 (AllWinning.cons node_4058 (AllWinning.cons node_3487 (AllWinning.cons node_2948 (AllWinning.cons node_2489 (AllWinning.cons node_1994 (AllWinning.cons node_1645 (AllWinning.cons node_1287 (AllWinning.cons node_1006 (AllWinning.cons node_776 (AllWinning.cons node_574 (AllWinning.nil))))))))))))))

theorem node_4735 : Outcome ⟨2, 2, 13, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 13, 2⟩, ⟨0, 2, 13, 4⟩, ⟨2, 1, 13, 2⟩, ⟨2, 0, 13, 4⟩, ⟨2, 2, 12, 2⟩, ⟨2, 2, 11, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 2, 9, 8⟩, ⟨2, 2, 8, 10⟩, ⟨2, 2, 7, 12⟩, ⟨2, 2, 6, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 2, 4, 18⟩, ⟨2, 2, 3, 20⟩, ⟨2, 2, 2, 22⟩, ⟨2, 2, 1, 24⟩]
  exact AllWinning.cons node_4007 (AllWinning.cons node_3329 (AllWinning.cons node_4055 (AllWinning.cons node_3478 (AllWinning.cons node_4058 (AllWinning.cons node_3487 (AllWinning.cons node_2948 (AllWinning.cons node_2489 (AllWinning.cons node_1994 (AllWinning.cons node_1645 (AllWinning.cons node_1287 (AllWinning.cons node_1006 (AllWinning.cons node_776 (AllWinning.cons node_574 (AllWinning.cons node_394 (AllWinning.cons node_290 (AllWinning.nil))))))))))))))))

theorem node_4736 : Outcome ⟨2, 3, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 4⟩) (by decide) node_3482

theorem node_4737 : Outcome ⟨2, 3, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 10⟩) (by decide) node_1998

theorem node_4738 : Outcome ⟨2, 3, 12, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 10⟩) (by decide) node_1998

theorem node_4739 : Outcome ⟨2, 3, 12, 16⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 10⟩) (by decide) node_1998

theorem node_4740 : Outcome ⟨2, 3, 12, 22⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 10⟩) (by decide) node_1998

theorem node_4741 : Outcome ⟨2, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 4⟩) (by decide) node_3494

theorem node_4742 : Outcome ⟨2, 4, 11, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 4⟩) (by decide) node_3494

theorem node_4743 : Outcome ⟨2, 5, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.nil))))))

theorem node_4744 : Outcome ⟨2, 5, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.nil))))))))))

theorem node_4745 : Outcome ⟨2, 5, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.nil)))))))))))))

theorem node_4746 : Outcome ⟨2, 5, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.nil)))))))))))))))

theorem node_4747 : Outcome ⟨2, 5, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4748 : Outcome ⟨2, 5, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4749 : Outcome ⟨2, 5, 10, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4750 : Outcome ⟨2, 5, 10, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4751 : Outcome ⟨2, 5, 10, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4752 : Outcome ⟨2, 5, 10, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4753 : Outcome ⟨2, 5, 10, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4754 : Outcome ⟨2, 5, 10, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4755 : Outcome ⟨2, 5, 10, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 10, 2⟩, ⟨0, 5, 10, 4⟩, ⟨2, 4, 10, 2⟩, ⟨2, 3, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨2, 1, 10, 8⟩, ⟨2, 0, 10, 10⟩, ⟨2, 5, 9, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 5, 6, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 5, 4, 12⟩, ⟨2, 5, 3, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 5, 1, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4015 (AllWinning.cons node_3340 (AllWinning.cons node_4064 (AllWinning.cons node_3489 (AllWinning.cons node_2948 (AllWinning.cons node_2485 (AllWinning.cons node_1985 (AllWinning.cons node_4066 (AllWinning.cons node_3499 (AllWinning.cons node_2959 (AllWinning.cons node_2502 (AllWinning.cons node_2016 (AllWinning.cons node_1659 (AllWinning.cons node_1301 (AllWinning.cons node_1018 (AllWinning.cons node_790 (AllWinning.cons node_597 (AllWinning.nil)))))))))))))))))

theorem node_4756 : Outcome ⟨2, 6, 9, 2⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 4⟩) (by decide) node_3494

theorem node_4757 : Outcome ⟨2, 6, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 4⟩) (by decide) node_3494

theorem node_4758 : Outcome ⟨2, 6, 9, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 4⟩) (by decide) node_3494

theorem node_4759 : Outcome ⟨2, 7, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 8, 2⟩, ⟨0, 7, 8, 4⟩, ⟨2, 6, 8, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 7, 7, 2⟩, ⟨2, 7, 6, 4⟩]
  exact AllWinning.cons node_4022 (AllWinning.cons node_3349 (AllWinning.cons node_4069 (AllWinning.cons node_3499 (AllWinning.cons node_4073 (AllWinning.cons node_3507 (AllWinning.nil))))))

theorem node_4760 : Outcome ⟨2, 7, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 8, 2⟩, ⟨0, 7, 8, 4⟩, ⟨2, 6, 8, 2⟩, ⟨2, 5, 8, 4⟩, ⟨2, 4, 8, 6⟩, ⟨2, 3, 8, 8⟩, ⟨2, 7, 7, 2⟩, ⟨2, 7, 6, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 7, 4, 8⟩]
  exact AllWinning.cons node_4022 (AllWinning.cons node_3349 (AllWinning.cons node_4069 (AllWinning.cons node_3499 (AllWinning.cons node_2956 (AllWinning.cons node_2492 (AllWinning.cons node_4073 (AllWinning.cons node_3507 (AllWinning.cons node_2967 (AllWinning.cons node_2509 (AllWinning.nil))))))))))

theorem node_4761 : Outcome ⟨2, 7, 8, 8⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 10⟩) (by decide) node_2028

theorem node_4762 : Outcome ⟨2, 7, 8, 20⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 10⟩) (by decide) node_2028

theorem node_4763 : Outcome ⟨2, 7, 8, 24⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 10⟩) (by decide) node_2028

theorem node_4764 : Outcome ⟨2, 8, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 7, 2⟩, ⟨0, 8, 7, 4⟩, ⟨2, 7, 7, 2⟩, ⟨2, 6, 7, 4⟩, ⟨2, 8, 6, 2⟩, ⟨2, 8, 5, 4⟩]
  exact AllWinning.cons node_4026 (AllWinning.cons node_3352 (AllWinning.cons node_4073 (AllWinning.cons node_3503 (AllWinning.cons node_4077 (AllWinning.cons node_3511 (AllWinning.nil))))))

theorem node_4765 : Outcome ⟨2, 8, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 7, 2⟩, ⟨0, 8, 7, 4⟩, ⟨2, 7, 7, 2⟩, ⟨2, 6, 7, 4⟩, ⟨2, 5, 7, 6⟩, ⟨2, 4, 7, 8⟩, ⟨2, 8, 6, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 8, 4, 6⟩, ⟨2, 8, 3, 8⟩]
  exact AllWinning.cons node_4026 (AllWinning.cons node_3352 (AllWinning.cons node_4073 (AllWinning.cons node_3503 (AllWinning.cons node_2959 (AllWinning.cons node_2497 (AllWinning.cons node_4077 (AllWinning.cons node_3511 (AllWinning.cons node_2972 (AllWinning.cons node_2514 (AllWinning.nil))))))))))

theorem node_4766 : Outcome ⟨2, 8, 7, 8⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 10⟩) (by decide) node_1998

theorem node_4767 : Outcome ⟨2, 8, 7, 20⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 10⟩) (by decide) node_1998

theorem node_4768 : Outcome ⟨2, 8, 7, 24⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 10⟩) (by decide) node_1998

theorem node_4769 : Outcome ⟨2, 9, 6, 2⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 4⟩) (by decide) node_3516

theorem node_4770 : Outcome ⟨2, 9, 6, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 4⟩) (by decide) node_3516

theorem node_4771 : Outcome ⟨2, 9, 6, 18⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 4⟩) (by decide) node_3516

theorem node_4772 : Outcome ⟨2, 10, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.nil))))))

theorem node_4773 : Outcome ⟨2, 10, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.nil))))))))))

theorem node_4774 : Outcome ⟨2, 10, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))

theorem node_4775 : Outcome ⟨2, 10, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))

theorem node_4776 : Outcome ⟨2, 10, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4777 : Outcome ⟨2, 10, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4778 : Outcome ⟨2, 10, 5, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4779 : Outcome ⟨2, 10, 5, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4780 : Outcome ⟨2, 10, 5, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4781 : Outcome ⟨2, 10, 5, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4782 : Outcome ⟨2, 10, 5, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4783 : Outcome ⟨2, 10, 5, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4784 : Outcome ⟨2, 10, 5, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 5, 2⟩, ⟨0, 10, 5, 4⟩, ⟨2, 9, 5, 2⟩, ⟨2, 8, 5, 4⟩, ⟨2, 7, 5, 6⟩, ⟨2, 6, 5, 8⟩, ⟨2, 5, 5, 10⟩, ⟨2, 4, 5, 12⟩, ⟨2, 3, 5, 14⟩, ⟨2, 2, 5, 16⟩, ⟨2, 1, 5, 18⟩, ⟨2, 0, 5, 20⟩, ⟨2, 10, 4, 2⟩, ⟨2, 10, 3, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 10, 1, 8⟩, ⟨2, 10, 0, 10⟩]
  exact AllWinning.cons node_4033 (AllWinning.cons node_3359 (AllWinning.cons node_4081 (AllWinning.cons node_3511 (AllWinning.cons node_2967 (AllWinning.cons node_2505 (AllWinning.cons node_2016 (AllWinning.cons node_1653 (AllWinning.cons node_1291 (AllWinning.cons node_1006 (AllWinning.cons node_772 (AllWinning.cons node_555 (AllWinning.cons node_4084 (AllWinning.cons node_3521 (AllWinning.cons node_2981 (AllWinning.cons node_2522 (AllWinning.cons node_2052 (AllWinning.nil)))))))))))))))))

theorem node_4785 : Outcome ⟨2, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 4⟩) (by decide) node_3516

theorem node_4786 : Outcome ⟨2, 11, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 4⟩) (by decide) node_3516

theorem node_4787 : Outcome ⟨2, 12, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 4⟩) (by decide) node_3528

theorem node_4788 : Outcome ⟨2, 12, 3, 8⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 10⟩) (by decide) node_2028

theorem node_4789 : Outcome ⟨2, 12, 3, 14⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 10⟩) (by decide) node_2028

theorem node_4790 : Outcome ⟨2, 12, 3, 16⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 10⟩) (by decide) node_2028

theorem node_4791 : Outcome ⟨2, 12, 3, 22⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 10⟩) (by decide) node_2028

theorem node_4792 : Outcome ⟨2, 13, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 2, 2⟩, ⟨0, 13, 2, 4⟩, ⟨2, 12, 2, 2⟩, ⟨2, 11, 2, 4⟩, ⟨2, 13, 1, 2⟩, ⟨2, 13, 0, 4⟩]
  exact AllWinning.cons node_4044 (AllWinning.cons node_3370 (AllWinning.cons node_4089 (AllWinning.cons node_3525 (AllWinning.cons node_4092 (AllWinning.cons node_3533 (AllWinning.nil))))))

theorem node_4793 : Outcome ⟨2, 13, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 2, 2⟩, ⟨0, 13, 2, 4⟩, ⟨2, 12, 2, 2⟩, ⟨2, 11, 2, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 9, 2, 8⟩, ⟨2, 13, 1, 2⟩, ⟨2, 13, 0, 4⟩]
  exact AllWinning.cons node_4044 (AllWinning.cons node_3370 (AllWinning.cons node_4089 (AllWinning.cons node_3525 (AllWinning.cons node_2981 (AllWinning.cons node_2519 (AllWinning.cons node_4092 (AllWinning.cons node_3533 (AllWinning.nil))))))))

theorem node_4794 : Outcome ⟨2, 13, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 2, 2⟩, ⟨0, 13, 2, 4⟩, ⟨2, 12, 2, 2⟩, ⟨2, 11, 2, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 9, 2, 8⟩, ⟨2, 8, 2, 10⟩, ⟨2, 7, 2, 12⟩, ⟨2, 13, 1, 2⟩, ⟨2, 13, 0, 4⟩]
  exact AllWinning.cons node_4044 (AllWinning.cons node_3370 (AllWinning.cons node_4089 (AllWinning.cons node_3525 (AllWinning.cons node_2981 (AllWinning.cons node_2519 (AllWinning.cons node_2043 (AllWinning.cons node_1665 (AllWinning.cons node_4092 (AllWinning.cons node_3533 (AllWinning.nil))))))))))

theorem node_4795 : Outcome ⟨2, 13, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 2, 2⟩, ⟨0, 13, 2, 4⟩, ⟨2, 12, 2, 2⟩, ⟨2, 11, 2, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 9, 2, 8⟩, ⟨2, 8, 2, 10⟩, ⟨2, 7, 2, 12⟩, ⟨2, 6, 2, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 13, 1, 2⟩, ⟨2, 13, 0, 4⟩]
  exact AllWinning.cons node_4044 (AllWinning.cons node_3370 (AllWinning.cons node_4089 (AllWinning.cons node_3525 (AllWinning.cons node_2981 (AllWinning.cons node_2519 (AllWinning.cons node_2043 (AllWinning.cons node_1665 (AllWinning.cons node_1304 (AllWinning.cons node_1018 (AllWinning.cons node_4092 (AllWinning.cons node_3533 (AllWinning.nil))))))))))))

theorem node_4796 : Outcome ⟨2, 13, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 2, 2⟩, ⟨0, 13, 2, 4⟩, ⟨2, 12, 2, 2⟩, ⟨2, 11, 2, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 9, 2, 8⟩, ⟨2, 8, 2, 10⟩, ⟨2, 7, 2, 12⟩, ⟨2, 6, 2, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 4, 2, 18⟩, ⟨2, 3, 2, 20⟩, ⟨2, 13, 1, 2⟩, ⟨2, 13, 0, 4⟩]
  exact AllWinning.cons node_4044 (AllWinning.cons node_3370 (AllWinning.cons node_4089 (AllWinning.cons node_3525 (AllWinning.cons node_2981 (AllWinning.cons node_2519 (AllWinning.cons node_2043 (AllWinning.cons node_1665 (AllWinning.cons node_1304 (AllWinning.cons node_1018 (AllWinning.cons node_785 (AllWinning.cons node_577 (AllWinning.cons node_4092 (AllWinning.cons node_3533 (AllWinning.nil))))))))))))))

theorem node_4797 : Outcome ⟨2, 13, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 2, 2⟩, ⟨0, 13, 2, 4⟩, ⟨2, 12, 2, 2⟩, ⟨2, 11, 2, 4⟩, ⟨2, 10, 2, 6⟩, ⟨2, 9, 2, 8⟩, ⟨2, 8, 2, 10⟩, ⟨2, 7, 2, 12⟩, ⟨2, 6, 2, 14⟩, ⟨2, 5, 2, 16⟩, ⟨2, 4, 2, 18⟩, ⟨2, 3, 2, 20⟩, ⟨2, 2, 2, 22⟩, ⟨2, 1, 2, 24⟩, ⟨2, 13, 1, 2⟩, ⟨2, 13, 0, 4⟩]
  exact AllWinning.cons node_4044 (AllWinning.cons node_3370 (AllWinning.cons node_4089 (AllWinning.cons node_3525 (AllWinning.cons node_2981 (AllWinning.cons node_2519 (AllWinning.cons node_2043 (AllWinning.cons node_1665 (AllWinning.cons node_1304 (AllWinning.cons node_1018 (AllWinning.cons node_785 (AllWinning.cons node_577 (AllWinning.cons node_394 (AllWinning.cons node_287 (AllWinning.cons node_4092 (AllWinning.cons node_3533 (AllWinning.nil))))))))))))))))

theorem node_4798 : Outcome ⟨2, 14, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 4⟩) (by decide) node_3374

theorem node_4799 : Outcome ⟨2, 14, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 4⟩) (by decide) node_3374

theorem node_4800 : Outcome ⟨2, 14, 1, 16⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 20⟩) (by decide) node_586

theorem node_4801 : Outcome ⟨2, 14, 1, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 20⟩) (by decide) node_586

theorem node_4802 : Outcome ⟨2, 15, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 0, 2⟩, ⟨0, 15, 0, 4⟩, ⟨2, 14, 0, 2⟩, ⟨2, 13, 0, 4⟩]
  exact AllWinning.cons node_4050 (AllWinning.cons node_3382 (AllWinning.cons node_4095 (AllWinning.cons node_3533 (AllWinning.nil))))

theorem node_4803 : Outcome ⟨2, 15, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 0, 2⟩, ⟨0, 15, 0, 4⟩, ⟨2, 14, 0, 2⟩, ⟨2, 13, 0, 4⟩, ⟨2, 12, 0, 6⟩, ⟨2, 11, 0, 8⟩]
  exact AllWinning.cons node_4050 (AllWinning.cons node_3382 (AllWinning.cons node_4095 (AllWinning.cons node_3533 (AllWinning.cons node_2987 (AllWinning.cons node_2526 (AllWinning.nil))))))

theorem node_4804 : Outcome ⟨2, 15, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 0, 2⟩, ⟨0, 15, 0, 4⟩, ⟨2, 14, 0, 2⟩, ⟨2, 13, 0, 4⟩, ⟨2, 12, 0, 6⟩, ⟨2, 11, 0, 8⟩, ⟨2, 10, 0, 10⟩, ⟨2, 9, 0, 12⟩]
  exact AllWinning.cons node_4050 (AllWinning.cons node_3382 (AllWinning.cons node_4095 (AllWinning.cons node_3533 (AllWinning.cons node_2987 (AllWinning.cons node_2526 (AllWinning.cons node_2052 (AllWinning.cons node_1674 (AllWinning.nil))))))))

theorem node_4805 : Outcome ⟨2, 15, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 0, 2⟩, ⟨0, 15, 0, 4⟩, ⟨2, 14, 0, 2⟩, ⟨2, 13, 0, 4⟩, ⟨2, 12, 0, 6⟩, ⟨2, 11, 0, 8⟩, ⟨2, 10, 0, 10⟩, ⟨2, 9, 0, 12⟩, ⟨2, 8, 0, 14⟩, ⟨2, 7, 0, 16⟩]
  exact AllWinning.cons node_4050 (AllWinning.cons node_3382 (AllWinning.cons node_4095 (AllWinning.cons node_3533 (AllWinning.cons node_2987 (AllWinning.cons node_2526 (AllWinning.cons node_2052 (AllWinning.cons node_1674 (AllWinning.cons node_1313 (AllWinning.cons node_1028 (AllWinning.nil))))))))))

theorem node_4806 : Outcome ⟨2, 15, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 0, 2⟩, ⟨0, 15, 0, 4⟩, ⟨2, 14, 0, 2⟩, ⟨2, 13, 0, 4⟩, ⟨2, 12, 0, 6⟩, ⟨2, 11, 0, 8⟩, ⟨2, 10, 0, 10⟩, ⟨2, 9, 0, 12⟩, ⟨2, 8, 0, 14⟩, ⟨2, 7, 0, 16⟩, ⟨2, 6, 0, 18⟩, ⟨2, 5, 0, 20⟩]
  exact AllWinning.cons node_4050 (AllWinning.cons node_3382 (AllWinning.cons node_4095 (AllWinning.cons node_3533 (AllWinning.cons node_2987 (AllWinning.cons node_2526 (AllWinning.cons node_2052 (AllWinning.cons node_1674 (AllWinning.cons node_1313 (AllWinning.cons node_1028 (AllWinning.cons node_794 (AllWinning.cons node_597 (AllWinning.nil))))))))))))

theorem node_4807 : Outcome ⟨2, 15, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 0, 2⟩, ⟨0, 15, 0, 4⟩, ⟨2, 14, 0, 2⟩, ⟨2, 13, 0, 4⟩, ⟨2, 12, 0, 6⟩, ⟨2, 11, 0, 8⟩, ⟨2, 10, 0, 10⟩, ⟨2, 9, 0, 12⟩, ⟨2, 8, 0, 14⟩, ⟨2, 7, 0, 16⟩, ⟨2, 6, 0, 18⟩, ⟨2, 5, 0, 20⟩, ⟨2, 4, 0, 22⟩, ⟨2, 3, 0, 24⟩]
  exact AllWinning.cons node_4050 (AllWinning.cons node_3382 (AllWinning.cons node_4095 (AllWinning.cons node_3533 (AllWinning.cons node_2987 (AllWinning.cons node_2526 (AllWinning.cons node_2052 (AllWinning.cons node_1674 (AllWinning.cons node_1313 (AllWinning.cons node_1028 (AllWinning.cons node_794 (AllWinning.cons node_597 (AllWinning.cons node_402 (AllWinning.cons node_294 (AllWinning.nil))))))))))))))

theorem node_4808 : Outcome ⟨2, 15, 0, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 26⟩) (by decide) node_216

theorem node_4809 : Outcome ⟨3, 0, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 4⟩) (by decide) node_3385

theorem node_4810 : Outcome ⟨3, 0, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 6⟩) (by decide) node_2993

theorem node_4811 : Outcome ⟨3, 0, 14, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 6⟩) (by decide) node_2993

theorem node_4812 : Outcome ⟨3, 0, 14, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 22⟩) (by decide) node_413

theorem node_4813 : Outcome ⟨3, 0, 14, 22⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 22⟩) (by decide) node_413

theorem node_4814 : Outcome ⟨3, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 4⟩) (by decide) node_3393

theorem node_4815 : Outcome ⟨3, 1, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 4⟩) (by decide) node_3393

theorem node_4816 : Outcome ⟨3, 1, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 4⟩) (by decide) node_3393

theorem node_4817 : Outcome ⟨3, 1, 13, 12⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 14⟩) (by decide) node_1325

theorem node_4818 : Outcome ⟨3, 1, 13, 18⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 14⟩) (by decide) node_1325

theorem node_4819 : Outcome ⟨3, 1, 13, 28⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 14⟩) (by decide) node_1325

theorem node_4820 : Outcome ⟨3, 2, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 4⟩) (by decide) node_3399

theorem node_4821 : Outcome ⟨3, 2, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4822 : Outcome ⟨3, 2, 12, 14⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4823 : Outcome ⟨3, 2, 12, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4824 : Outcome ⟨3, 2, 12, 22⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4825 : Outcome ⟨3, 3, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 3, 11, 2⟩, ⟨1, 3, 11, 4⟩, ⟨3, 2, 11, 2⟩, ⟨3, 1, 11, 4⟩, ⟨3, 3, 10, 2⟩, ⟨3, 3, 9, 4⟩]
  exact AllWinning.cons node_4061 (AllWinning.cons node_3404 (AllWinning.cons node_4105 (AllWinning.cons node_3539 (AllWinning.cons node_4108 (AllWinning.cons node_3547 (AllWinning.nil))))))

theorem node_4826 : Outcome ⟨3, 3, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 11, 6⟩) (by decide) node_2836

theorem node_4827 : Outcome ⟨3, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 4⟩) (by decide) node_3408

theorem node_4828 : Outcome ⟨3, 4, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 4⟩) (by decide) node_3408

theorem node_4829 : Outcome ⟨3, 4, 10, 18⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 4⟩) (by decide) node_3408

theorem node_4830 : Outcome ⟨3, 5, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 4⟩) (by decide) node_3413

theorem node_4831 : Outcome ⟨3, 5, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 4⟩) (by decide) node_3413

theorem node_4832 : Outcome ⟨3, 5, 9, 14⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 4⟩) (by decide) node_3413

theorem node_4833 : Outcome ⟨3, 5, 9, 22⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 4⟩) (by decide) node_3413

theorem node_4834 : Outcome ⟨3, 6, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 4⟩) (by decide) node_3427

theorem node_4835 : Outcome ⟨3, 6, 8, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 6⟩) (by decide) node_3008

theorem node_4836 : Outcome ⟨3, 6, 8, 8⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 14⟩) (by decide) node_1356

theorem node_4837 : Outcome ⟨3, 6, 8, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 14⟩) (by decide) node_1356

theorem node_4838 : Outcome ⟨3, 6, 8, 20⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 14⟩) (by decide) node_1356

theorem node_4839 : Outcome ⟨3, 7, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 6⟩) (by decide) node_2851

theorem node_4840 : Outcome ⟨3, 7, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4841 : Outcome ⟨3, 7, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4842 : Outcome ⟨3, 7, 7, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4843 : Outcome ⟨3, 7, 7, 18⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 10⟩) (by decide) node_2069

theorem node_4844 : Outcome ⟨3, 8, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 4⟩) (by decide) node_3433

theorem node_4845 : Outcome ⟨3, 8, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 6⟩) (by decide) node_3027

theorem node_4846 : Outcome ⟨3, 8, 6, 8⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 14⟩) (by decide) node_1325

theorem node_4847 : Outcome ⟨3, 8, 6, 12⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 14⟩) (by decide) node_1325

theorem node_4848 : Outcome ⟨3, 8, 6, 20⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 14⟩) (by decide) node_1325

theorem node_4849 : Outcome ⟨3, 9, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 4⟩) (by decide) node_3437

theorem node_4850 : Outcome ⟨3, 9, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 4⟩) (by decide) node_3437

theorem node_4851 : Outcome ⟨3, 9, 5, 14⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 4⟩) (by decide) node_3437

theorem node_4852 : Outcome ⟨3, 9, 5, 22⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 4⟩) (by decide) node_3437

theorem node_4853 : Outcome ⟨3, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 4⟩) (by decide) node_3451

theorem node_4854 : Outcome ⟨3, 10, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 4⟩) (by decide) node_3451

theorem node_4855 : Outcome ⟨3, 10, 4, 18⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 4⟩) (by decide) node_3451

theorem node_4856 : Outcome ⟨3, 11, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 3, 2⟩, ⟨1, 11, 3, 4⟩, ⟨3, 10, 3, 2⟩, ⟨3, 9, 3, 4⟩, ⟨3, 11, 2, 2⟩, ⟨3, 11, 1, 4⟩]
  exact AllWinning.cons node_4086 (AllWinning.cons node_3455 (AllWinning.cons node_4136 (AllWinning.cons node_3568 (AllWinning.cons node_4140 (AllWinning.cons node_3577 (AllWinning.nil))))))

theorem node_4857 : Outcome ⟨3, 11, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 3, 6⟩) (by decide) node_2874

theorem node_4858 : Outcome ⟨3, 12, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 4⟩) (by decide) node_3459

theorem node_4859 : Outcome ⟨3, 12, 2, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 10⟩) (by decide) node_2100

theorem node_4860 : Outcome ⟨3, 12, 2, 14⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 10⟩) (by decide) node_2100

theorem node_4861 : Outcome ⟨3, 12, 2, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 10⟩) (by decide) node_2100

theorem node_4862 : Outcome ⟨3, 12, 2, 22⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 10⟩) (by decide) node_2100

theorem node_4863 : Outcome ⟨3, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 4⟩) (by decide) node_3465

theorem node_4864 : Outcome ⟨3, 13, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 4⟩) (by decide) node_3465

theorem node_4865 : Outcome ⟨3, 13, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 4⟩) (by decide) node_3465

theorem node_4866 : Outcome ⟨3, 13, 1, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 14⟩) (by decide) node_1356

theorem node_4867 : Outcome ⟨3, 13, 1, 18⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 14⟩) (by decide) node_1356

theorem node_4868 : Outcome ⟨3, 13, 1, 28⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 14⟩) (by decide) node_1356

theorem node_4869 : Outcome ⟨3, 14, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 4⟩) (by decide) node_3471

theorem node_4870 : Outcome ⟨3, 14, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 0, 6⟩) (by decide) node_3042

theorem node_4871 : Outcome ⟨3, 14, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 0, 6⟩) (by decide) node_3042

theorem node_4872 : Outcome ⟨3, 14, 0, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 22⟩) (by decide) node_436

theorem node_4873 : Outcome ⟨3, 14, 0, 22⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 22⟩) (by decide) node_436

theorem node_4874 : Outcome ⟨4, 0, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 2⟩) (by decide) node_4150

theorem node_4875 : Outcome ⟨4, 0, 13, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 8⟩) (by decide) node_2363

theorem node_4876 : Outcome ⟨4, 0, 13, 18⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 18⟩) (by decide) node_828

theorem node_4877 : Outcome ⟨4, 0, 13, 24⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 18⟩) (by decide) node_828

theorem node_4878 : Outcome ⟨4, 1, 12, 2⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 4⟩) (by decide) node_3482

theorem node_4879 : Outcome ⟨4, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 4⟩) (by decide) node_3482

theorem node_4880 : Outcome ⟨4, 1, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 4⟩) (by decide) node_3482

theorem node_4881 : Outcome ⟨4, 1, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 4⟩) (by decide) node_3482

theorem node_4882 : Outcome ⟨4, 1, 12, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 20⟩) (by decide) node_625

theorem node_4883 : Outcome ⟨4, 2, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 9, 4⟩) (by decide) node_3594

theorem node_4884 : Outcome ⟨4, 2, 11, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 9, 4⟩) (by decide) node_3594

theorem node_4885 : Outcome ⟨4, 2, 11, 32⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 20⟩) (by decide) node_643

theorem node_4886 : Outcome ⟨4, 3, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 10, 4⟩) (by decide) node_3589

theorem node_4887 : Outcome ⟨4, 3, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 10, 4⟩) (by decide) node_3589

theorem node_4888 : Outcome ⟨4, 3, 10, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 10, 4⟩) (by decide) node_3589

theorem node_4889 : Outcome ⟨4, 4, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 4⟩) (by decide) node_3494

theorem node_4890 : Outcome ⟨4, 4, 9, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 4⟩) (by decide) node_3494

theorem node_4891 : Outcome ⟨4, 4, 9, 24⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 18⟩) (by decide) node_854

theorem node_4892 : Outcome ⟨4, 5, 8, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 2⟩) (by decide) node_4165

theorem node_4893 : Outcome ⟨4, 5, 8, 8⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 2⟩) (by decide) node_4165

theorem node_4894 : Outcome ⟨4, 5, 8, 22⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 2⟩) (by decide) node_4165

theorem node_4895 : Outcome ⟨4, 5, 8, 24⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 2⟩) (by decide) node_4165

theorem node_4896 : Outcome ⟨4, 6, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 2⟩) (by decide) node_4170

theorem node_4897 : Outcome ⟨4, 6, 7, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 2⟩) (by decide) node_4170

theorem node_4898 : Outcome ⟨4, 7, 6, 6⟩ true :=
  Outcome.win (q := ⟨4, 6, 6, 2⟩) (by decide) node_4183

theorem node_4899 : Outcome ⟨4, 7, 6, 8⟩ true :=
  Outcome.win (q := ⟨4, 6, 6, 2⟩) (by decide) node_4183

theorem node_4900 : Outcome ⟨4, 8, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 2⟩) (by decide) node_4187

theorem node_4901 : Outcome ⟨4, 8, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 2⟩) (by decide) node_4187

theorem node_4902 : Outcome ⟨4, 8, 5, 22⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 2⟩) (by decide) node_4187

theorem node_4903 : Outcome ⟨4, 8, 5, 24⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 2⟩) (by decide) node_4187

theorem node_4904 : Outcome ⟨4, 9, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 4⟩) (by decide) node_3516

theorem node_4905 : Outcome ⟨4, 9, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 4⟩) (by decide) node_3516

theorem node_4906 : Outcome ⟨4, 9, 4, 24⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 18⟩) (by decide) node_828

theorem node_4907 : Outcome ⟨4, 10, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 1, 4⟩) (by decide) node_3620

theorem node_4908 : Outcome ⟨4, 10, 3, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 1, 4⟩) (by decide) node_3620

theorem node_4909 : Outcome ⟨4, 10, 3, 18⟩ true :=
  Outcome.win (q := ⟨4, 10, 1, 4⟩) (by decide) node_3620

theorem node_4910 : Outcome ⟨4, 11, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 2, 4⟩) (by decide) node_3614

theorem node_4911 : Outcome ⟨4, 11, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 9, 2, 4⟩) (by decide) node_3614

theorem node_4912 : Outcome ⟨4, 11, 2, 32⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 20⟩) (by decide) node_625

theorem node_4913 : Outcome ⟨4, 12, 1, 2⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 4⟩) (by decide) node_3528

theorem node_4914 : Outcome ⟨4, 12, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 4⟩) (by decide) node_3528

theorem node_4915 : Outcome ⟨4, 12, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 4⟩) (by decide) node_3528

theorem node_4916 : Outcome ⟨4, 12, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 4⟩) (by decide) node_3528

theorem node_4917 : Outcome ⟨4, 12, 1, 24⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 20⟩) (by decide) node_643

theorem node_4918 : Outcome ⟨4, 13, 0, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 2⟩) (by decide) node_4214

theorem node_4919 : Outcome ⟨4, 13, 0, 8⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 8⟩) (by decide) node_2427

theorem node_4920 : Outcome ⟨4, 13, 0, 18⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 18⟩) (by decide) node_854

theorem node_4921 : Outcome ⟨4, 13, 0, 24⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 18⟩) (by decide) node_854

theorem node_4922 : Outcome ⟨5, 0, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 2⟩) (by decide) node_4150

theorem node_4923 : Outcome ⟨5, 0, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 2⟩) (by decide) node_4150

theorem node_4924 : Outcome ⟨5, 0, 12, 8⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 14⟩) (by decide) node_1410

theorem node_4925 : Outcome ⟨5, 0, 12, 12⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 14⟩) (by decide) node_1410

theorem node_4926 : Outcome ⟨5, 0, 12, 14⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 14⟩) (by decide) node_1410

theorem node_4927 : Outcome ⟨5, 1, 11, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 4⟩) (by decide) node_3635

theorem node_4928 : Outcome ⟨5, 1, 11, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 4⟩) (by decide) node_3635

theorem node_4929 : Outcome ⟨5, 1, 11, 6⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 4⟩) (by decide) node_3635

theorem node_4930 : Outcome ⟨5, 2, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 10, 2⟩, ⟨3, 2, 10, 4⟩, ⟨5, 1, 10, 2⟩, ⟨5, 0, 10, 4⟩, ⟨5, 2, 9, 2⟩, ⟨5, 2, 8, 4⟩]
  exact AllWinning.cons node_4160 (AllWinning.cons node_3543 (AllWinning.cons node_4225 (AllWinning.cons node_3630 (AllWinning.cons node_4229 (AllWinning.cons node_3646 (AllWinning.nil))))))

theorem node_4931 : Outcome ⟨5, 2, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 10, 2⟩, ⟨3, 2, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨1, 2, 10, 8⟩, ⟨5, 1, 10, 2⟩, ⟨5, 0, 10, 4⟩, ⟨5, 2, 9, 2⟩, ⟨5, 2, 8, 4⟩, ⟨5, 2, 7, 6⟩, ⟨5, 2, 6, 8⟩]
  exact AllWinning.cons node_4160 (AllWinning.cons node_3543 (AllWinning.cons node_2948 (AllWinning.cons node_2439 (AllWinning.cons node_4225 (AllWinning.cons node_3630 (AllWinning.cons node_4229 (AllWinning.cons node_3646 (AllWinning.cons node_3093 (AllWinning.cons node_2639 (AllWinning.nil))))))))))

theorem node_4932 : Outcome ⟨5, 2, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 10, 2⟩, ⟨3, 2, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨1, 2, 10, 8⟩, ⟨0, 2, 10, 10⟩, ⟨5, 1, 10, 2⟩, ⟨5, 0, 10, 4⟩, ⟨5, 2, 9, 2⟩, ⟨5, 2, 8, 4⟩, ⟨5, 2, 7, 6⟩, ⟨5, 2, 6, 8⟩, ⟨5, 2, 5, 10⟩, ⟨5, 2, 4, 12⟩]
  exact AllWinning.cons node_4160 (AllWinning.cons node_3543 (AllWinning.cons node_2948 (AllWinning.cons node_2439 (AllWinning.cons node_1875 (AllWinning.cons node_4225 (AllWinning.cons node_3630 (AllWinning.cons node_4229 (AllWinning.cons node_3646 (AllWinning.cons node_3093 (AllWinning.cons node_2639 (AllWinning.cons node_2169 (AllWinning.cons node_1762 (AllWinning.nil)))))))))))))

theorem node_4933 : Outcome ⟨5, 2, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 10, 2⟩, ⟨3, 2, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨1, 2, 10, 8⟩, ⟨0, 2, 10, 10⟩, ⟨5, 1, 10, 2⟩, ⟨5, 0, 10, 4⟩, ⟨5, 2, 9, 2⟩, ⟨5, 2, 8, 4⟩, ⟨5, 2, 7, 6⟩, ⟨5, 2, 6, 8⟩, ⟨5, 2, 5, 10⟩, ⟨5, 2, 4, 12⟩, ⟨5, 2, 3, 14⟩, ⟨5, 2, 2, 16⟩]
  exact AllWinning.cons node_4160 (AllWinning.cons node_3543 (AllWinning.cons node_2948 (AllWinning.cons node_2439 (AllWinning.cons node_1875 (AllWinning.cons node_4225 (AllWinning.cons node_3630 (AllWinning.cons node_4229 (AllWinning.cons node_3646 (AllWinning.cons node_3093 (AllWinning.cons node_2639 (AllWinning.cons node_2169 (AllWinning.cons node_1762 (AllWinning.cons node_1426 (AllWinning.cons node_1095 (AllWinning.nil)))))))))))))))

theorem node_4934 : Outcome ⟨5, 2, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 10, 2⟩, ⟨3, 2, 10, 4⟩, ⟨2, 2, 10, 6⟩, ⟨1, 2, 10, 8⟩, ⟨0, 2, 10, 10⟩, ⟨5, 1, 10, 2⟩, ⟨5, 0, 10, 4⟩, ⟨5, 2, 9, 2⟩, ⟨5, 2, 8, 4⟩, ⟨5, 2, 7, 6⟩, ⟨5, 2, 6, 8⟩, ⟨5, 2, 5, 10⟩, ⟨5, 2, 4, 12⟩, ⟨5, 2, 3, 14⟩, ⟨5, 2, 2, 16⟩, ⟨5, 2, 1, 18⟩, ⟨5, 2, 0, 20⟩]
  exact AllWinning.cons node_4160 (AllWinning.cons node_3543 (AllWinning.cons node_2948 (AllWinning.cons node_2439 (AllWinning.cons node_1875 (AllWinning.cons node_4225 (AllWinning.cons node_3630 (AllWinning.cons node_4229 (AllWinning.cons node_3646 (AllWinning.cons node_3093 (AllWinning.cons node_2639 (AllWinning.cons node_2169 (AllWinning.cons node_1762 (AllWinning.cons node_1426 (AllWinning.cons node_1095 (AllWinning.cons node_874 (AllWinning.cons node_665 (AllWinning.nil)))))))))))))))))

end RQ9F1
