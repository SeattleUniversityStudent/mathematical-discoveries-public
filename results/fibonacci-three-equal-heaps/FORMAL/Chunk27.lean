import Chunk26
set_option autoImplicit false
namespace RQ9F1

theorem node_6544 : Outcome ⟨6, 13, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 13, 0, 2⟩) (by decide) node_5676

theorem node_6545 : Outcome ⟨6, 13, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 0, 2⟩) (by decide) node_5676

theorem node_6546 : Outcome ⟨6, 13, 0, 12⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 14⟩) (by decide) node_2231

theorem node_6547 : Outcome ⟨6, 13, 0, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 14⟩) (by decide) node_2231

theorem node_6548 : Outcome ⟨6, 13, 0, 28⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 14⟩) (by decide) node_2231

theorem node_6549 : Outcome ⟨7, 0, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 12, 2⟩, ⟨5, 0, 12, 4⟩, ⟨7, 0, 11, 2⟩, ⟨7, 0, 10, 4⟩]
  exact AllWinning.cons node_5681 (AllWinning.cons node_4923 (AllWinning.cons node_5729 (AllWinning.cons node_5031 (AllWinning.nil))))

theorem node_6550 : Outcome ⟨7, 0, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 6⟩) (by decide) node_4152

theorem node_6551 : Outcome ⟨7, 0, 12, 6⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 10⟩) (by decide) node_3165

theorem node_6552 : Outcome ⟨7, 0, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 10⟩) (by decide) node_3165

theorem node_6553 : Outcome ⟨7, 0, 12, 14⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 10⟩) (by decide) node_3165

theorem node_6554 : Outcome ⟨7, 0, 12, 16⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 10⟩) (by decide) node_3165

theorem node_6555 : Outcome ⟨7, 0, 12, 30⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 10⟩) (by decide) node_3165

theorem node_6556 : Outcome ⟨7, 1, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.nil)))))

theorem node_6557 : Outcome ⟨7, 1, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.nil)))))))))

theorem node_6558 : Outcome ⟨7, 1, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.nil)))))))))))))

theorem node_6559 : Outcome ⟨7, 1, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.nil))))))))))))))))

theorem node_6560 : Outcome ⟨7, 1, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.nil))))))))))))))))))

theorem node_6561 : Outcome ⟨7, 1, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6562 : Outcome ⟨7, 1, 11, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6563 : Outcome ⟨7, 1, 11, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6564 : Outcome ⟨7, 1, 11, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6565 : Outcome ⟨7, 1, 11, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6566 : Outcome ⟨7, 1, 11, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6567 : Outcome ⟨7, 1, 11, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6568 : Outcome ⟨7, 1, 11, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨4, 1, 11, 6⟩, ⟨3, 1, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨0, 1, 11, 14⟩, ⟨7, 0, 11, 2⟩, ⟨7, 1, 10, 2⟩, ⟨7, 1, 9, 4⟩, ⟨7, 1, 8, 6⟩, ⟨7, 1, 7, 8⟩, ⟨7, 1, 6, 10⟩, ⟨7, 1, 5, 12⟩, ⟨7, 1, 4, 14⟩, ⟨7, 1, 3, 16⟩, ⟨7, 1, 2, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 1, 0, 22⟩]
  exact AllWinning.cons node_5686 (AllWinning.cons node_4928 (AllWinning.cons node_4157 (AllWinning.cons node_3540 (AllWinning.cons node_2945 (AllWinning.cons node_2437 (AllWinning.cons node_1870 (AllWinning.cons node_5729 (AllWinning.cons node_5732 (AllWinning.cons node_5035 (AllWinning.cons node_4331 (AllWinning.cons node_3730 (AllWinning.cons node_3175 (AllWinning.cons node_2698 (AllWinning.cons node_2247 (AllWinning.cons node_1804 (AllWinning.cons node_1501 (AllWinning.cons node_1131 (AllWinning.cons node_901 (AllWinning.nil)))))))))))))))))))

theorem node_6569 : Outcome ⟨7, 2, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6570 : Outcome ⟨7, 2, 10, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6571 : Outcome ⟨7, 2, 10, 16⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 14⟩) (by decide) node_2255

theorem node_6572 : Outcome ⟨7, 2, 10, 18⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 14⟩) (by decide) node_2255

theorem node_6573 : Outcome ⟨7, 3, 9, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 9, 2⟩) (by decide) node_5692

theorem node_6574 : Outcome ⟨7, 3, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 3, 9, 2⟩) (by decide) node_5692

theorem node_6575 : Outcome ⟨7, 3, 9, 10⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 14⟩) (by decide) node_2271

theorem node_6576 : Outcome ⟨7, 3, 9, 12⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 14⟩) (by decide) node_2271

theorem node_6577 : Outcome ⟨7, 3, 9, 20⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 14⟩) (by decide) node_2271

theorem node_6578 : Outcome ⟨7, 4, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 8, 4⟩) (by decide) node_5040

theorem node_6579 : Outcome ⟨7, 4, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 6⟩) (by decide) node_4167

theorem node_6580 : Outcome ⟨7, 4, 8, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 6⟩) (by decide) node_4167

theorem node_6581 : Outcome ⟨7, 5, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 5, 7, 2⟩, ⟨5, 5, 7, 4⟩, ⟨7, 4, 7, 2⟩, ⟨7, 3, 7, 4⟩, ⟨7, 5, 6, 2⟩, ⟨7, 5, 5, 4⟩]
  exact AllWinning.cons node_5699 (AllWinning.cons node_4951 (AllWinning.cons node_5745 (AllWinning.cons node_5045 (AllWinning.cons node_5749 (AllWinning.cons node_5053 (AllWinning.nil))))))

theorem node_6582 : Outcome ⟨7, 5, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 6⟩) (by decide) node_4172

theorem node_6583 : Outcome ⟨7, 5, 7, 14⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 10⟩) (by decide) node_3165

theorem node_6584 : Outcome ⟨7, 5, 7, 20⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 10⟩) (by decide) node_3165

theorem node_6585 : Outcome ⟨7, 6, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 6, 2⟩) (by decide) node_5703

theorem node_6586 : Outcome ⟨7, 6, 6, 10⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 14⟩) (by decide) node_1895

theorem node_6587 : Outcome ⟨7, 7, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 7, 5, 2⟩, ⟨5, 7, 5, 4⟩, ⟨7, 6, 5, 2⟩, ⟨7, 5, 5, 4⟩, ⟨7, 7, 4, 2⟩, ⟨7, 7, 3, 4⟩]
  exact AllWinning.cons node_5707 (AllWinning.cons node_4957 (AllWinning.cons node_5752 (AllWinning.cons node_5053 (AllWinning.cons node_5755 (AllWinning.cons node_5059 (AllWinning.nil))))))

theorem node_6588 : Outcome ⟨7, 7, 5, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 6⟩) (by decide) node_4189

theorem node_6589 : Outcome ⟨7, 7, 5, 14⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 10⟩) (by decide) node_3202

theorem node_6590 : Outcome ⟨7, 7, 5, 20⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 10⟩) (by decide) node_3202

theorem node_6591 : Outcome ⟨7, 8, 4, 2⟩ true :=
  Outcome.win (q := ⟨7, 8, 2, 4⟩) (by decide) node_5064

theorem node_6592 : Outcome ⟨7, 8, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 6⟩) (by decide) node_4202

theorem node_6593 : Outcome ⟨7, 8, 4, 20⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 6⟩) (by decide) node_4202

theorem node_6594 : Outcome ⟨7, 9, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 9, 3, 2⟩) (by decide) node_5713

theorem node_6595 : Outcome ⟨7, 9, 3, 4⟩ true :=
  Outcome.win (q := ⟨6, 9, 3, 2⟩) (by decide) node_5713

theorem node_6596 : Outcome ⟨7, 9, 3, 10⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 14⟩) (by decide) node_2255

theorem node_6597 : Outcome ⟨7, 9, 3, 12⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 14⟩) (by decide) node_2255

theorem node_6598 : Outcome ⟨7, 9, 3, 20⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 14⟩) (by decide) node_2255

theorem node_6599 : Outcome ⟨7, 10, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6600 : Outcome ⟨7, 10, 2, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6601 : Outcome ⟨7, 10, 2, 16⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 14⟩) (by decide) node_2271

theorem node_6602 : Outcome ⟨7, 10, 2, 18⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 14⟩) (by decide) node_2271

theorem node_6603 : Outcome ⟨7, 11, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_5772 (AllWinning.nil)))))

theorem node_6604 : Outcome ⟨7, 11, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_5772 (AllWinning.nil)))))))))

theorem node_6605 : Outcome ⟨7, 11, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_5772 (AllWinning.nil)))))))))))))

theorem node_6606 : Outcome ⟨7, 11, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_5772 (AllWinning.nil))))))))))))))))

theorem node_6607 : Outcome ⟨7, 11, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 2, 1, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_1505 (AllWinning.cons node_1131 (AllWinning.cons node_5772 (AllWinning.nil))))))))))))))))))

theorem node_6608 : Outcome ⟨7, 11, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 2, 1, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 0, 1, 22⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_1505 (AllWinning.cons node_1131 (AllWinning.cons node_895 (AllWinning.cons node_5772 (AllWinning.nil)))))))))))))))))))

theorem node_6609 : Outcome ⟨7, 11, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 2, 1, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 0, 1, 22⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_1505 (AllWinning.cons node_1131 (AllWinning.cons node_895 (AllWinning.cons node_5772 (AllWinning.nil)))))))))))))))))))

theorem node_6610 : Outcome ⟨7, 11, 1, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 2, 1, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 0, 1, 22⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_1505 (AllWinning.cons node_1131 (AllWinning.cons node_895 (AllWinning.cons node_5772 (AllWinning.nil)))))))))))))))))))

theorem node_6611 : Outcome ⟨7, 11, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 2, 1, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 0, 1, 22⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_1505 (AllWinning.cons node_1131 (AllWinning.cons node_895 (AllWinning.cons node_5772 (AllWinning.nil)))))))))))))))))))

theorem node_6612 : Outcome ⟨7, 11, 1, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 2, 1, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 0, 1, 22⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_1505 (AllWinning.cons node_1131 (AllWinning.cons node_895 (AllWinning.cons node_5772 (AllWinning.nil)))))))))))))))))))

theorem node_6613 : Outcome ⟨7, 11, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 1, 2⟩, ⟨5, 11, 1, 4⟩, ⟨4, 11, 1, 6⟩, ⟨3, 11, 1, 8⟩, ⟨2, 11, 1, 10⟩, ⟨1, 11, 1, 12⟩, ⟨0, 11, 1, 14⟩, ⟨7, 10, 1, 2⟩, ⟨7, 9, 1, 4⟩, ⟨7, 8, 1, 6⟩, ⟨7, 7, 1, 8⟩, ⟨7, 6, 1, 10⟩, ⟨7, 5, 1, 12⟩, ⟨7, 4, 1, 14⟩, ⟨7, 3, 1, 16⟩, ⟨7, 2, 1, 18⟩, ⟨7, 1, 1, 20⟩, ⟨7, 0, 1, 22⟩, ⟨7, 11, 0, 2⟩]
  exact AllWinning.cons node_5721 (AllWinning.cons node_4981 (AllWinning.cons node_4211 (AllWinning.cons node_3578 (AllWinning.cons node_2983 (AllWinning.cons node_2475 (AllWinning.cons node_1923 (AllWinning.cons node_5769 (AllWinning.cons node_5069 (AllWinning.cons node_4385 (AllWinning.cons node_3755 (AllWinning.cons node_3195 (AllWinning.cons node_2716 (AllWinning.cons node_2285 (AllWinning.cons node_1810 (AllWinning.cons node_1505 (AllWinning.cons node_1131 (AllWinning.cons node_895 (AllWinning.cons node_5772 (AllWinning.nil)))))))))))))))))))

theorem node_6614 : Outcome ⟨7, 12, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 0, 2⟩, ⟨5, 12, 0, 4⟩, ⟨7, 11, 0, 2⟩, ⟨7, 10, 0, 4⟩]
  exact AllWinning.cons node_5724 (AllWinning.cons node_4984 (AllWinning.cons node_5772 (AllWinning.cons node_5074 (AllWinning.nil))))

theorem node_6615 : Outcome ⟨7, 12, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 6⟩) (by decide) node_4216

theorem node_6616 : Outcome ⟨7, 12, 0, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 10⟩) (by decide) node_3202

theorem node_6617 : Outcome ⟨7, 12, 0, 10⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 10⟩) (by decide) node_3202

theorem node_6618 : Outcome ⟨7, 12, 0, 14⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 10⟩) (by decide) node_3202

theorem node_6619 : Outcome ⟨7, 12, 0, 16⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 10⟩) (by decide) node_3202

theorem node_6620 : Outcome ⟨7, 12, 0, 30⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 10⟩) (by decide) node_3202

theorem node_6621 : Outcome ⟨8, 0, 11, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6622 : Outcome ⟨8, 0, 11, 6⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6623 : Outcome ⟨8, 0, 11, 20⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6624 : Outcome ⟨8, 1, 10, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 9, 2⟩) (by decide) node_5778

theorem node_6625 : Outcome ⟨8, 1, 10, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 9, 2⟩) (by decide) node_5778

theorem node_6626 : Outcome ⟨8, 1, 10, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 9, 2⟩) (by decide) node_5778

theorem node_6627 : Outcome ⟨8, 1, 10, 12⟩ true :=
  Outcome.win (q := ⟨8, 1, 9, 2⟩) (by decide) node_5778

theorem node_6628 : Outcome ⟨8, 1, 10, 20⟩ true :=
  Outcome.win (q := ⟨8, 1, 9, 2⟩) (by decide) node_5778

theorem node_6629 : Outcome ⟨8, 2, 9, 2⟩ true :=
  Outcome.win (q := ⟨8, 2, 7, 4⟩) (by decide) node_5082

theorem node_6630 : Outcome ⟨8, 2, 9, 14⟩ true :=
  Outcome.win (q := ⟨8, 2, 7, 4⟩) (by decide) node_5082

theorem node_6631 : Outcome ⟨8, 2, 9, 20⟩ true :=
  Outcome.win (q := ⟨8, 2, 7, 4⟩) (by decide) node_5082

theorem node_6632 : Outcome ⟨8, 3, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 8, 2⟩, ⟨6, 3, 8, 4⟩, ⟨8, 2, 8, 2⟩, ⟨8, 1, 8, 4⟩, ⟨8, 3, 7, 2⟩, ⟨8, 3, 6, 4⟩]
  exact AllWinning.cons node_5740 (AllWinning.cons node_5000 (AllWinning.cons node_5782 (AllWinning.cons node_5080 (AllWinning.cons node_5787 (AllWinning.cons node_5087 (AllWinning.nil))))))

theorem node_6633 : Outcome ⟨8, 3, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6634 : Outcome ⟨8, 3, 8, 10⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6635 : Outcome ⟨8, 3, 8, 16⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6636 : Outcome ⟨8, 3, 8, 30⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6637 : Outcome ⟨8, 4, 7, 2⟩ true :=
  Outcome.win (q := ⟨8, 2, 7, 4⟩) (by decide) node_5082

theorem node_6638 : Outcome ⟨8, 4, 7, 4⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 6⟩) (by decide) node_4238

theorem node_6639 : Outcome ⟨8, 4, 7, 20⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 6⟩) (by decide) node_4238

theorem node_6640 : Outcome ⟨8, 5, 6, 4⟩ true :=
  Outcome.win (q := ⟨8, 5, 5, 2⟩) (by decide) node_5795

theorem node_6641 : Outcome ⟨8, 5, 6, 8⟩ true :=
  Outcome.win (q := ⟨8, 5, 5, 2⟩) (by decide) node_5795

theorem node_6642 : Outcome ⟨8, 5, 6, 18⟩ true :=
  Outcome.win (q := ⟨8, 5, 5, 2⟩) (by decide) node_5795

theorem node_6643 : Outcome ⟨8, 6, 5, 4⟩ true :=
  Outcome.win (q := ⟨8, 5, 5, 2⟩) (by decide) node_5795

theorem node_6644 : Outcome ⟨8, 6, 5, 8⟩ true :=
  Outcome.win (q := ⟨8, 5, 5, 2⟩) (by decide) node_5795

theorem node_6645 : Outcome ⟨8, 6, 5, 18⟩ true :=
  Outcome.win (q := ⟨8, 5, 5, 2⟩) (by decide) node_5795

theorem node_6646 : Outcome ⟨8, 7, 4, 2⟩ true :=
  Outcome.win (q := ⟨8, 7, 2, 4⟩) (by decide) node_5104

theorem node_6647 : Outcome ⟨8, 7, 4, 4⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 6⟩) (by decide) node_4255

theorem node_6648 : Outcome ⟨8, 7, 4, 20⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 6⟩) (by decide) node_4255

theorem node_6649 : Outcome ⟨8, 8, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 3, 2⟩, ⟨6, 8, 3, 4⟩, ⟨8, 7, 3, 2⟩, ⟨8, 6, 3, 4⟩, ⟨8, 8, 2, 2⟩, ⟨8, 8, 1, 4⟩]
  exact AllWinning.cons node_5759 (AllWinning.cons node_5015 (AllWinning.cons node_5803 (AllWinning.cons node_5100 (AllWinning.cons node_5808 (AllWinning.cons node_5109 (AllWinning.nil))))))

theorem node_6650 : Outcome ⟨8, 8, 3, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 6⟩) (by decide) node_4433

theorem node_6651 : Outcome ⟨8, 8, 3, 10⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 6⟩) (by decide) node_4433

theorem node_6652 : Outcome ⟨8, 8, 3, 16⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 6⟩) (by decide) node_4433

theorem node_6653 : Outcome ⟨8, 8, 3, 30⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 6⟩) (by decide) node_4433

theorem node_6654 : Outcome ⟨8, 9, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 7, 2, 4⟩) (by decide) node_5104

theorem node_6655 : Outcome ⟨8, 9, 2, 14⟩ true :=
  Outcome.win (q := ⟨8, 7, 2, 4⟩) (by decide) node_5104

theorem node_6656 : Outcome ⟨8, 9, 2, 20⟩ true :=
  Outcome.win (q := ⟨8, 7, 2, 4⟩) (by decide) node_5104

theorem node_6657 : Outcome ⟨8, 10, 1, 2⟩ true :=
  Outcome.win (q := ⟨8, 9, 1, 2⟩) (by decide) node_5813

theorem node_6658 : Outcome ⟨8, 10, 1, 4⟩ true :=
  Outcome.win (q := ⟨8, 9, 1, 2⟩) (by decide) node_5813

theorem node_6659 : Outcome ⟨8, 10, 1, 8⟩ true :=
  Outcome.win (q := ⟨8, 9, 1, 2⟩) (by decide) node_5813

theorem node_6660 : Outcome ⟨8, 10, 1, 12⟩ true :=
  Outcome.win (q := ⟨8, 9, 1, 2⟩) (by decide) node_5813

theorem node_6661 : Outcome ⟨8, 10, 1, 20⟩ true :=
  Outcome.win (q := ⟨8, 9, 1, 2⟩) (by decide) node_5813

theorem node_6662 : Outcome ⟨8, 11, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 6⟩) (by decide) node_4433

theorem node_6663 : Outcome ⟨8, 11, 0, 6⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 6⟩) (by decide) node_4433

theorem node_6664 : Outcome ⟨8, 11, 0, 20⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 6⟩) (by decide) node_4433

theorem node_6665 : Outcome ⟨9, 0, 10, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 2⟩) (by decide) node_5820

theorem node_6666 : Outcome ⟨9, 0, 10, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 2⟩) (by decide) node_5820

theorem node_6667 : Outcome ⟨9, 1, 9, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 9, 2⟩) (by decide) node_5778

theorem node_6668 : Outcome ⟨9, 1, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 8⟩) (by decide) node_3637

theorem node_6669 : Outcome ⟨9, 1, 9, 8⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 8⟩) (by decide) node_3637

theorem node_6670 : Outcome ⟨9, 2, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 8, 4⟩) (by decide) node_5040

theorem node_6671 : Outcome ⟨9, 2, 8, 14⟩ true :=
  Outcome.win (q := ⟨7, 2, 8, 4⟩) (by decide) node_5040

theorem node_6672 : Outcome ⟨9, 2, 8, 20⟩ true :=
  Outcome.win (q := ⟨7, 2, 8, 4⟩) (by decide) node_5040

theorem node_6673 : Outcome ⟨9, 3, 7, 2⟩ true :=
  Outcome.win (q := ⟨9, 3, 6, 2⟩) (by decide) node_5842

theorem node_6674 : Outcome ⟨9, 3, 7, 4⟩ true :=
  Outcome.win (q := ⟨9, 3, 6, 2⟩) (by decide) node_5842

theorem node_6675 : Outcome ⟨9, 3, 7, 10⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 14⟩) (by decide) node_2000

theorem node_6676 : Outcome ⟨9, 3, 7, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 14⟩) (by decide) node_2000

theorem node_6677 : Outcome ⟨9, 3, 7, 20⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 14⟩) (by decide) node_2000

theorem node_6678 : Outcome ⟨9, 4, 6, 2⟩ true :=
  Outcome.win (q := ⟨9, 3, 6, 2⟩) (by decide) node_5842

theorem node_6679 : Outcome ⟨9, 4, 6, 20⟩ true :=
  Outcome.win (q := ⟨9, 3, 6, 2⟩) (by decide) node_5842

theorem node_6680 : Outcome ⟨9, 4, 6, 26⟩ true :=
  Outcome.win (q := ⟨9, 3, 6, 2⟩) (by decide) node_5842

theorem node_6681 : Outcome ⟨9, 5, 5, 8⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 8⟩) (by decide) node_3798

theorem node_6682 : Outcome ⟨9, 5, 5, 18⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 18⟩) (by decide) node_1179

theorem node_6683 : Outcome ⟨9, 6, 4, 2⟩ true :=
  Outcome.win (q := ⟨9, 6, 3, 2⟩) (by decide) node_5856

theorem node_6684 : Outcome ⟨9, 6, 4, 20⟩ true :=
  Outcome.win (q := ⟨9, 6, 3, 2⟩) (by decide) node_5856

theorem node_6685 : Outcome ⟨9, 6, 4, 26⟩ true :=
  Outcome.win (q := ⟨9, 6, 3, 2⟩) (by decide) node_5856

theorem node_6686 : Outcome ⟨9, 7, 3, 2⟩ true :=
  Outcome.win (q := ⟨9, 6, 3, 2⟩) (by decide) node_5856

theorem node_6687 : Outcome ⟨9, 7, 3, 4⟩ true :=
  Outcome.win (q := ⟨9, 6, 3, 2⟩) (by decide) node_5856

theorem node_6688 : Outcome ⟨9, 7, 3, 10⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 14⟩) (by decide) node_2030

theorem node_6689 : Outcome ⟨9, 7, 3, 12⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 14⟩) (by decide) node_2030

theorem node_6690 : Outcome ⟨9, 7, 3, 20⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 14⟩) (by decide) node_2030

theorem node_6691 : Outcome ⟨9, 8, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 8, 2, 4⟩) (by decide) node_5064

theorem node_6692 : Outcome ⟨9, 8, 2, 14⟩ true :=
  Outcome.win (q := ⟨7, 8, 2, 4⟩) (by decide) node_5064

theorem node_6693 : Outcome ⟨9, 8, 2, 20⟩ true :=
  Outcome.win (q := ⟨7, 8, 2, 4⟩) (by decide) node_5064

theorem node_6694 : Outcome ⟨9, 9, 1, 2⟩ true :=
  Outcome.win (q := ⟨8, 9, 1, 2⟩) (by decide) node_5813

theorem node_6695 : Outcome ⟨9, 9, 1, 4⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 8⟩) (by decide) node_3675

theorem node_6696 : Outcome ⟨9, 9, 1, 8⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 8⟩) (by decide) node_3675

theorem node_6697 : Outcome ⟨9, 10, 0, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 2⟩) (by decide) node_5870

theorem node_6698 : Outcome ⟨9, 10, 0, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 2⟩) (by decide) node_5870

theorem node_6699 : Outcome ⟨10, 0, 9, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 2⟩) (by decide) node_5820

theorem node_6700 : Outcome ⟨10, 0, 9, 4⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 2⟩) (by decide) node_5820

theorem node_6701 : Outcome ⟨10, 0, 9, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 2⟩) (by decide) node_5820

theorem node_6702 : Outcome ⟨10, 1, 8, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 8, 2⟩) (by decide) node_5833

theorem node_6703 : Outcome ⟨10, 1, 8, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 8, 2⟩) (by decide) node_5833

theorem node_6704 : Outcome ⟨10, 1, 8, 8⟩ true :=
  Outcome.win (q := ⟨9, 1, 8, 2⟩) (by decide) node_5833

theorem node_6705 : Outcome ⟨10, 1, 8, 12⟩ true :=
  Outcome.win (q := ⟨9, 1, 8, 2⟩) (by decide) node_5833

theorem node_6706 : Outcome ⟨10, 1, 8, 20⟩ true :=
  Outcome.win (q := ⟨9, 1, 8, 2⟩) (by decide) node_5833

theorem node_6707 : Outcome ⟨10, 2, 7, 2⟩ true :=
  Outcome.win (q := ⟨8, 2, 7, 4⟩) (by decide) node_5082

theorem node_6708 : Outcome ⟨10, 2, 7, 4⟩ true :=
  Outcome.win (q := ⟨8, 2, 7, 4⟩) (by decide) node_5082

theorem node_6709 : Outcome ⟨10, 2, 7, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 14⟩) (by decide) node_2071

theorem node_6710 : Outcome ⟨10, 2, 7, 18⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 14⟩) (by decide) node_2071

theorem node_6711 : Outcome ⟨10, 3, 6, 2⟩ true :=
  Outcome.win (q := ⟨9, 3, 6, 2⟩) (by decide) node_5842

theorem node_6712 : Outcome ⟨10, 3, 6, 8⟩ true :=
  Outcome.win (q := ⟨9, 3, 6, 2⟩) (by decide) node_5842

theorem node_6713 : Outcome ⟨10, 3, 6, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 18⟩) (by decide) node_1227

theorem node_6714 : Outcome ⟨10, 4, 5, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 4⟩) (by decide) node_5153

theorem node_6715 : Outcome ⟨10, 4, 5, 4⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 6⟩) (by decide) node_4345

theorem node_6716 : Outcome ⟨10, 4, 5, 8⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 6⟩) (by decide) node_4345

theorem node_6717 : Outcome ⟨10, 4, 5, 16⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 6⟩) (by decide) node_4345

theorem node_6718 : Outcome ⟨10, 5, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 4⟩) (by decide) node_5172

theorem node_6719 : Outcome ⟨10, 5, 4, 4⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 6⟩) (by decide) node_4360

theorem node_6720 : Outcome ⟨10, 5, 4, 8⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 6⟩) (by decide) node_4360

theorem node_6721 : Outcome ⟨10, 5, 4, 16⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 6⟩) (by decide) node_4360

theorem node_6722 : Outcome ⟨10, 6, 3, 2⟩ true :=
  Outcome.win (q := ⟨9, 6, 3, 2⟩) (by decide) node_5856

theorem node_6723 : Outcome ⟨10, 6, 3, 8⟩ true :=
  Outcome.win (q := ⟨9, 6, 3, 2⟩) (by decide) node_5856

theorem node_6724 : Outcome ⟨10, 6, 3, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 18⟩) (by decide) node_1255

theorem node_6725 : Outcome ⟨10, 7, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 7, 2, 4⟩) (by decide) node_5104

theorem node_6726 : Outcome ⟨10, 7, 2, 4⟩ true :=
  Outcome.win (q := ⟨8, 7, 2, 4⟩) (by decide) node_5104

theorem node_6727 : Outcome ⟨10, 7, 2, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 14⟩) (by decide) node_2102

theorem node_6728 : Outcome ⟨10, 7, 2, 18⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 14⟩) (by decide) node_2102

theorem node_6729 : Outcome ⟨10, 8, 1, 2⟩ true :=
  Outcome.win (q := ⟨9, 8, 1, 2⟩) (by decide) node_5867

theorem node_6730 : Outcome ⟨10, 8, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 8, 1, 2⟩) (by decide) node_5867

theorem node_6731 : Outcome ⟨10, 8, 1, 8⟩ true :=
  Outcome.win (q := ⟨9, 8, 1, 2⟩) (by decide) node_5867

theorem node_6732 : Outcome ⟨10, 8, 1, 12⟩ true :=
  Outcome.win (q := ⟨9, 8, 1, 2⟩) (by decide) node_5867

theorem node_6733 : Outcome ⟨10, 8, 1, 20⟩ true :=
  Outcome.win (q := ⟨9, 8, 1, 2⟩) (by decide) node_5867

theorem node_6734 : Outcome ⟨10, 9, 0, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 2⟩) (by decide) node_5870

theorem node_6735 : Outcome ⟨10, 9, 0, 4⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 2⟩) (by decide) node_5870

theorem node_6736 : Outcome ⟨10, 9, 0, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 2⟩) (by decide) node_5870

theorem node_6737 : Outcome ⟨11, 0, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 8, 2⟩, ⟨9, 0, 8, 4⟩, ⟨11, 0, 7, 2⟩, ⟨11, 0, 6, 4⟩]
  exact AllWinning.cons node_5883 (AllWinning.cons node_5114 (AllWinning.cons node_5912 (AllWinning.cons node_5190 (AllWinning.nil))))

theorem node_6738 : Outcome ⟨11, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6739 : Outcome ⟨11, 0, 8, 6⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6740 : Outcome ⟨11, 0, 8, 20⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 6⟩) (by decide) node_4392

theorem node_6741 : Outcome ⟨11, 1, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.nil)))))

theorem node_6742 : Outcome ⟨11, 1, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.nil)))))))))

theorem node_6743 : Outcome ⟨11, 1, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.nil)))))))))))))

theorem node_6744 : Outcome ⟨11, 1, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨4, 1, 7, 14⟩, ⟨3, 1, 7, 16⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩, ⟨11, 1, 0, 14⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_2129 (AllWinning.cons node_1685 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.cons node_2355 (AllWinning.nil))))))))))))))))

theorem node_6745 : Outcome ⟨11, 1, 7, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨4, 1, 7, 14⟩, ⟨3, 1, 7, 16⟩, ⟨2, 1, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩, ⟨11, 1, 0, 14⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_2129 (AllWinning.cons node_1685 (AllWinning.cons node_1284 (AllWinning.cons node_959 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.cons node_2355 (AllWinning.nil))))))))))))))))))

theorem node_6746 : Outcome ⟨11, 1, 7, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨4, 1, 7, 14⟩, ⟨3, 1, 7, 16⟩, ⟨2, 1, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨0, 1, 7, 22⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩, ⟨11, 1, 0, 14⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_2129 (AllWinning.cons node_1685 (AllWinning.cons node_1284 (AllWinning.cons node_959 (AllWinning.cons node_690 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.cons node_2355 (AllWinning.nil)))))))))))))))))))

theorem node_6747 : Outcome ⟨11, 1, 7, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨4, 1, 7, 14⟩, ⟨3, 1, 7, 16⟩, ⟨2, 1, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨0, 1, 7, 22⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩, ⟨11, 1, 0, 14⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_2129 (AllWinning.cons node_1685 (AllWinning.cons node_1284 (AllWinning.cons node_959 (AllWinning.cons node_690 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.cons node_2355 (AllWinning.nil)))))))))))))))))))

theorem node_6748 : Outcome ⟨11, 1, 7, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨4, 1, 7, 14⟩, ⟨3, 1, 7, 16⟩, ⟨2, 1, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨0, 1, 7, 22⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩, ⟨11, 1, 0, 14⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_2129 (AllWinning.cons node_1685 (AllWinning.cons node_1284 (AllWinning.cons node_959 (AllWinning.cons node_690 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.cons node_2355 (AllWinning.nil)))))))))))))))))))

theorem node_6749 : Outcome ⟨11, 1, 7, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨4, 1, 7, 14⟩, ⟨3, 1, 7, 16⟩, ⟨2, 1, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨0, 1, 7, 22⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩, ⟨11, 1, 0, 14⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_2129 (AllWinning.cons node_1685 (AllWinning.cons node_1284 (AllWinning.cons node_959 (AllWinning.cons node_690 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.cons node_2355 (AllWinning.nil)))))))))))))))))))

theorem node_6750 : Outcome ⟨11, 1, 7, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 7, 2⟩, ⟨9, 1, 7, 4⟩, ⟨8, 1, 7, 6⟩, ⟨7, 1, 7, 8⟩, ⟨6, 1, 7, 10⟩, ⟨5, 1, 7, 12⟩, ⟨4, 1, 7, 14⟩, ⟨3, 1, 7, 16⟩, ⟨2, 1, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨0, 1, 7, 22⟩, ⟨11, 0, 7, 2⟩, ⟨11, 1, 6, 2⟩, ⟨11, 1, 5, 4⟩, ⟨11, 1, 4, 6⟩, ⟨11, 1, 3, 8⟩, ⟨11, 1, 2, 10⟩, ⟨11, 1, 1, 12⟩, ⟨11, 1, 0, 14⟩]
  exact AllWinning.cons node_5887 (AllWinning.cons node_5117 (AllWinning.cons node_4405 (AllWinning.cons node_3730 (AllWinning.cons node_3128 (AllWinning.cons node_2636 (AllWinning.cons node_2129 (AllWinning.cons node_1685 (AllWinning.cons node_1284 (AllWinning.cons node_959 (AllWinning.cons node_690 (AllWinning.cons node_5912 (AllWinning.cons node_5914 (AllWinning.cons node_5195 (AllWinning.cons node_4498 (AllWinning.cons node_3868 (AllWinning.cons node_3285 (AllWinning.cons node_2798 (AllWinning.cons node_2355 (AllWinning.nil)))))))))))))))))))

theorem node_6751 : Outcome ⟨11, 2, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 6, 2⟩, ⟨9, 2, 6, 4⟩, ⟨11, 1, 6, 2⟩, ⟨11, 0, 6, 4⟩, ⟨11, 2, 5, 2⟩, ⟨11, 2, 4, 4⟩]
  exact AllWinning.cons node_5890 (AllWinning.cons node_5122 (AllWinning.cons node_5914 (AllWinning.cons node_5190 (AllWinning.cons node_5917 (AllWinning.cons node_5197 (AllWinning.nil))))))

theorem node_6752 : Outcome ⟨11, 2, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 6, 2⟩, ⟨9, 2, 6, 4⟩, ⟨8, 2, 6, 6⟩, ⟨7, 2, 6, 8⟩, ⟨11, 1, 6, 2⟩, ⟨11, 0, 6, 4⟩, ⟨11, 2, 5, 2⟩, ⟨11, 2, 4, 4⟩, ⟨11, 2, 3, 6⟩, ⟨11, 2, 2, 8⟩]
  exact AllWinning.cons node_5890 (AllWinning.cons node_5122 (AllWinning.cons node_4408 (AllWinning.cons node_3734 (AllWinning.cons node_5914 (AllWinning.cons node_5190 (AllWinning.cons node_5917 (AllWinning.cons node_5197 (AllWinning.cons node_4501 (AllWinning.cons node_3872 (AllWinning.nil))))))))))

theorem node_6753 : Outcome ⟨11, 2, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 6, 2⟩, ⟨9, 2, 6, 4⟩, ⟨8, 2, 6, 6⟩, ⟨7, 2, 6, 8⟩, ⟨6, 2, 6, 10⟩, ⟨5, 2, 6, 12⟩, ⟨11, 1, 6, 2⟩, ⟨11, 0, 6, 4⟩, ⟨11, 2, 5, 2⟩, ⟨11, 2, 4, 4⟩, ⟨11, 2, 3, 6⟩, ⟨11, 2, 2, 8⟩, ⟨11, 2, 1, 10⟩, ⟨11, 2, 0, 12⟩]
  exact AllWinning.cons node_5890 (AllWinning.cons node_5122 (AllWinning.cons node_4408 (AllWinning.cons node_3734 (AllWinning.cons node_3134 (AllWinning.cons node_2640 (AllWinning.cons node_5914 (AllWinning.cons node_5190 (AllWinning.cons node_5917 (AllWinning.cons node_5197 (AllWinning.cons node_4501 (AllWinning.cons node_3872 (AllWinning.cons node_3288 (AllWinning.cons node_2802 (AllWinning.nil))))))))))))))

theorem node_6754 : Outcome ⟨11, 2, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 6, 2⟩, ⟨9, 2, 6, 4⟩, ⟨8, 2, 6, 6⟩, ⟨7, 2, 6, 8⟩, ⟨6, 2, 6, 10⟩, ⟨5, 2, 6, 12⟩, ⟨4, 2, 6, 14⟩, ⟨3, 2, 6, 16⟩, ⟨11, 1, 6, 2⟩, ⟨11, 0, 6, 4⟩, ⟨11, 2, 5, 2⟩, ⟨11, 2, 4, 4⟩, ⟨11, 2, 3, 6⟩, ⟨11, 2, 2, 8⟩, ⟨11, 2, 1, 10⟩, ⟨11, 2, 0, 12⟩]
  exact AllWinning.cons node_5890 (AllWinning.cons node_5122 (AllWinning.cons node_4408 (AllWinning.cons node_3734 (AllWinning.cons node_3134 (AllWinning.cons node_2640 (AllWinning.cons node_2134 (AllWinning.cons node_1688 (AllWinning.cons node_5914 (AllWinning.cons node_5190 (AllWinning.cons node_5917 (AllWinning.cons node_5197 (AllWinning.cons node_4501 (AllWinning.cons node_3872 (AllWinning.cons node_3288 (AllWinning.cons node_2802 (AllWinning.nil))))))))))))))))

theorem node_6755 : Outcome ⟨11, 2, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 6, 2⟩, ⟨9, 2, 6, 4⟩, ⟨8, 2, 6, 6⟩, ⟨7, 2, 6, 8⟩, ⟨6, 2, 6, 10⟩, ⟨5, 2, 6, 12⟩, ⟨4, 2, 6, 14⟩, ⟨3, 2, 6, 16⟩, ⟨2, 2, 6, 18⟩, ⟨1, 2, 6, 20⟩, ⟨11, 1, 6, 2⟩, ⟨11, 0, 6, 4⟩, ⟨11, 2, 5, 2⟩, ⟨11, 2, 4, 4⟩, ⟨11, 2, 3, 6⟩, ⟨11, 2, 2, 8⟩, ⟨11, 2, 1, 10⟩, ⟨11, 2, 0, 12⟩]
  exact AllWinning.cons node_5890 (AllWinning.cons node_5122 (AllWinning.cons node_4408 (AllWinning.cons node_3734 (AllWinning.cons node_3134 (AllWinning.cons node_2640 (AllWinning.cons node_2134 (AllWinning.cons node_1688 (AllWinning.cons node_1288 (AllWinning.cons node_963 (AllWinning.cons node_5914 (AllWinning.cons node_5190 (AllWinning.cons node_5917 (AllWinning.cons node_5197 (AllWinning.cons node_4501 (AllWinning.cons node_3872 (AllWinning.cons node_3288 (AllWinning.cons node_2802 (AllWinning.nil))))))))))))))))))

end RQ9F1
