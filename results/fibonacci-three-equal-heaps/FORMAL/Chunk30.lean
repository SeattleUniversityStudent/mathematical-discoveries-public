import Chunk29
set_option autoImplicit false
namespace RQ9F1

theorem node_7102 : Outcome ⟨1, 17, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 2, 2⟩, ⟨1, 16, 2, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 14, 2, 6⟩, ⟨1, 13, 2, 8⟩, ⟨1, 12, 2, 10⟩, ⟨1, 11, 2, 12⟩, ⟨1, 10, 2, 14⟩, ⟨1, 9, 2, 16⟩, ⟨1, 17, 1, 2⟩, ⟨1, 17, 0, 4⟩]
  exact AllWinning.cons node_6108 (AllWinning.cons node_6188 (AllWinning.cons node_5445 (AllWinning.cons node_4708 (AllWinning.cons node_4046 (AllWinning.cons node_3461 (AllWinning.cons node_2932 (AllWinning.cons node_2471 (AllWinning.cons node_1972 (AllWinning.cons node_6192 (AllWinning.cons node_5453 (AllWinning.nil)))))))))))

theorem node_7103 : Outcome ⟨1, 17, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 2, 2⟩, ⟨1, 16, 2, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 14, 2, 6⟩, ⟨1, 13, 2, 8⟩, ⟨1, 12, 2, 10⟩, ⟨1, 11, 2, 12⟩, ⟨1, 10, 2, 14⟩, ⟨1, 9, 2, 16⟩, ⟨1, 8, 2, 18⟩, ⟨1, 7, 2, 20⟩, ⟨1, 6, 2, 22⟩, ⟨1, 5, 2, 24⟩, ⟨1, 17, 1, 2⟩, ⟨1, 17, 0, 4⟩]
  exact AllWinning.cons node_6108 (AllWinning.cons node_6188 (AllWinning.cons node_5445 (AllWinning.cons node_4708 (AllWinning.cons node_4046 (AllWinning.cons node_3461 (AllWinning.cons node_2932 (AllWinning.cons node_2471 (AllWinning.cons node_1972 (AllWinning.cons node_1626 (AllWinning.cons node_1267 (AllWinning.cons node_983 (AllWinning.cons node_756 (AllWinning.cons node_6192 (AllWinning.cons node_5453 (AllWinning.nil)))))))))))))))

theorem node_7104 : Outcome ⟨1, 17, 2, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 26⟩) (by decide) node_537

theorem node_7105 : Outcome ⟨1, 17, 2, 22⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 26⟩) (by decide) node_537

theorem node_7106 : Outcome ⟨1, 18, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 1, 2⟩, ⟨1, 17, 1, 2⟩, ⟨1, 16, 1, 4⟩, ⟨1, 18, 0, 2⟩]
  exact AllWinning.cons node_6111 (AllWinning.cons node_6192 (AllWinning.cons node_5450 (AllWinning.cons node_6194 (AllWinning.nil))))

theorem node_7107 : Outcome ⟨1, 18, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 1, 2⟩, ⟨1, 17, 1, 2⟩, ⟨1, 16, 1, 4⟩, ⟨1, 15, 1, 6⟩, ⟨1, 14, 1, 8⟩, ⟨1, 18, 0, 2⟩]
  exact AllWinning.cons node_6111 (AllWinning.cons node_6192 (AllWinning.cons node_5450 (AllWinning.cons node_4712 (AllWinning.cons node_4048 (AllWinning.cons node_6194 (AllWinning.nil))))))

theorem node_7108 : Outcome ⟨1, 19, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 0, 2⟩, ⟨1, 18, 0, 2⟩, ⟨1, 17, 0, 4⟩]
  exact AllWinning.cons node_6113 (AllWinning.cons node_6194 (AllWinning.cons node_5453 (AllWinning.nil)))

theorem node_7109 : Outcome ⟨1, 19, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 0, 2⟩, ⟨1, 18, 0, 2⟩, ⟨1, 17, 0, 4⟩, ⟨1, 16, 0, 6⟩, ⟨1, 15, 0, 8⟩]
  exact AllWinning.cons node_6113 (AllWinning.cons node_6194 (AllWinning.cons node_5453 (AllWinning.cons node_4716 (AllWinning.cons node_4051 (AllWinning.nil)))))

theorem node_7110 : Outcome ⟨1, 19, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 10⟩) (by decide) node_3474

theorem node_7111 : Outcome ⟨1, 19, 0, 10⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 10⟩) (by decide) node_3474

theorem node_7112 : Outcome ⟨2, 0, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 6⟩) (by decide) node_4721

theorem node_7113 : Outcome ⟨2, 0, 18, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 6⟩) (by decide) node_4721

theorem node_7114 : Outcome ⟨2, 0, 18, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 6⟩) (by decide) node_4721

theorem node_7115 : Outcome ⟨2, 0, 18, 32⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 32⟩) (by decide) node_197

theorem node_7116 : Outcome ⟨2, 1, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 17, 2⟩, ⟨0, 1, 17, 4⟩, ⟨2, 0, 17, 2⟩, ⟨2, 1, 16, 2⟩, ⟨2, 1, 15, 4⟩]
  exact AllWinning.cons node_6117 (AllWinning.cons node_5314 (AllWinning.cons node_6196 (AllWinning.cons node_6199 (AllWinning.cons node_5460 (AllWinning.nil)))))

theorem node_7117 : Outcome ⟨2, 1, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 17, 2⟩, ⟨0, 1, 17, 4⟩, ⟨2, 0, 17, 2⟩, ⟨2, 1, 16, 2⟩, ⟨2, 1, 15, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 1, 13, 8⟩]
  exact AllWinning.cons node_6117 (AllWinning.cons node_5314 (AllWinning.cons node_6196 (AllWinning.cons node_6199 (AllWinning.cons node_5460 (AllWinning.cons node_4727 (AllWinning.cons node_4057 (AllWinning.nil)))))))

theorem node_7118 : Outcome ⟨2, 1, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 17, 2⟩, ⟨0, 1, 17, 4⟩, ⟨2, 0, 17, 2⟩, ⟨2, 1, 16, 2⟩, ⟨2, 1, 15, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 1, 13, 8⟩, ⟨2, 1, 12, 10⟩, ⟨2, 1, 11, 12⟩]
  exact AllWinning.cons node_6117 (AllWinning.cons node_5314 (AllWinning.cons node_6196 (AllWinning.cons node_6199 (AllWinning.cons node_5460 (AllWinning.cons node_4727 (AllWinning.cons node_4057 (AllWinning.cons node_3484 (AllWinning.cons node_2946 (AllWinning.nil)))))))))

theorem node_7119 : Outcome ⟨2, 1, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 17, 2⟩, ⟨0, 1, 17, 4⟩, ⟨2, 0, 17, 2⟩, ⟨2, 1, 16, 2⟩, ⟨2, 1, 15, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 1, 13, 8⟩, ⟨2, 1, 12, 10⟩, ⟨2, 1, 11, 12⟩, ⟨2, 1, 10, 14⟩, ⟨2, 1, 9, 16⟩]
  exact AllWinning.cons node_6117 (AllWinning.cons node_5314 (AllWinning.cons node_6196 (AllWinning.cons node_6199 (AllWinning.cons node_5460 (AllWinning.cons node_4727 (AllWinning.cons node_4057 (AllWinning.cons node_3484 (AllWinning.cons node_2946 (AllWinning.cons node_2486 (AllWinning.cons node_1989 (AllWinning.nil)))))))))))

theorem node_7120 : Outcome ⟨2, 1, 17, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 17, 2⟩, ⟨0, 1, 17, 4⟩, ⟨2, 0, 17, 2⟩, ⟨2, 1, 16, 2⟩, ⟨2, 1, 15, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 1, 13, 8⟩, ⟨2, 1, 12, 10⟩, ⟨2, 1, 11, 12⟩, ⟨2, 1, 10, 14⟩, ⟨2, 1, 9, 16⟩, ⟨2, 1, 8, 18⟩, ⟨2, 1, 7, 20⟩, ⟨2, 1, 6, 22⟩, ⟨2, 1, 5, 24⟩]
  exact AllWinning.cons node_6117 (AllWinning.cons node_5314 (AllWinning.cons node_6196 (AllWinning.cons node_6199 (AllWinning.cons node_5460 (AllWinning.cons node_4727 (AllWinning.cons node_4057 (AllWinning.cons node_3484 (AllWinning.cons node_2946 (AllWinning.cons node_2486 (AllWinning.cons node_1989 (AllWinning.cons node_1642 (AllWinning.cons node_1285 (AllWinning.cons node_1002 (AllWinning.cons node_773 (AllWinning.nil)))))))))))))))

theorem node_7121 : Outcome ⟨2, 1, 17, 20⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 26⟩) (by decide) node_567

theorem node_7122 : Outcome ⟨2, 1, 17, 22⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 26⟩) (by decide) node_567

theorem node_7123 : Outcome ⟨2, 2, 16, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 6⟩) (by decide) node_4732

theorem node_7124 : Outcome ⟨2, 2, 16, 16⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 32⟩) (by decide) node_218

theorem node_7125 : Outcome ⟨2, 2, 16, 32⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 32⟩) (by decide) node_218

theorem node_7126 : Outcome ⟨2, 3, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 6⟩) (by decide) node_4721

theorem node_7127 : Outcome ⟨2, 3, 15, 10⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 16⟩) (by decide) node_2001

theorem node_7128 : Outcome ⟨2, 3, 15, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 16⟩) (by decide) node_2001

theorem node_7129 : Outcome ⟨2, 4, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨2, 3, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨2, 4, 13, 2⟩, ⟨2, 4, 12, 4⟩]
  exact AllWinning.cons node_6127 (AllWinning.cons node_5325 (AllWinning.cons node_6206 (AllWinning.cons node_5464 (AllWinning.cons node_6210 (AllWinning.cons node_5471 (AllWinning.nil))))))

theorem node_7130 : Outcome ⟨2, 4, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨2, 3, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 0, 14, 8⟩, ⟨2, 4, 13, 2⟩, ⟨2, 4, 12, 4⟩, ⟨2, 4, 11, 6⟩, ⟨2, 4, 10, 8⟩]
  exact AllWinning.cons node_6127 (AllWinning.cons node_5325 (AllWinning.cons node_6206 (AllWinning.cons node_5464 (AllWinning.cons node_4727 (AllWinning.cons node_4053 (AllWinning.cons node_6210 (AllWinning.cons node_5471 (AllWinning.cons node_4742 (AllWinning.cons node_4065 (AllWinning.nil))))))))))

theorem node_7131 : Outcome ⟨2, 4, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨2, 3, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 0, 14, 8⟩, ⟨2, 4, 13, 2⟩, ⟨2, 4, 12, 4⟩, ⟨2, 4, 11, 6⟩, ⟨2, 4, 10, 8⟩, ⟨2, 4, 9, 10⟩, ⟨2, 4, 8, 12⟩]
  exact AllWinning.cons node_6127 (AllWinning.cons node_5325 (AllWinning.cons node_6206 (AllWinning.cons node_5464 (AllWinning.cons node_4727 (AllWinning.cons node_4053 (AllWinning.cons node_6210 (AllWinning.cons node_5471 (AllWinning.cons node_4742 (AllWinning.cons node_4065 (AllWinning.cons node_3496 (AllWinning.cons node_2957 (AllWinning.nil))))))))))))

theorem node_7132 : Outcome ⟨2, 4, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨2, 3, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 0, 14, 8⟩, ⟨2, 4, 13, 2⟩, ⟨2, 4, 12, 4⟩, ⟨2, 4, 11, 6⟩, ⟨2, 4, 10, 8⟩, ⟨2, 4, 9, 10⟩, ⟨2, 4, 8, 12⟩, ⟨2, 4, 7, 14⟩, ⟨2, 4, 6, 16⟩]
  exact AllWinning.cons node_6127 (AllWinning.cons node_5325 (AllWinning.cons node_6206 (AllWinning.cons node_5464 (AllWinning.cons node_4727 (AllWinning.cons node_4053 (AllWinning.cons node_6210 (AllWinning.cons node_5471 (AllWinning.cons node_4742 (AllWinning.cons node_4065 (AllWinning.cons node_3496 (AllWinning.cons node_2957 (AllWinning.cons node_2498 (AllWinning.cons node_2014 (AllWinning.nil))))))))))))))

theorem node_7133 : Outcome ⟨2, 4, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨2, 3, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 0, 14, 8⟩, ⟨2, 4, 13, 2⟩, ⟨2, 4, 12, 4⟩, ⟨2, 4, 11, 6⟩, ⟨2, 4, 10, 8⟩, ⟨2, 4, 9, 10⟩, ⟨2, 4, 8, 12⟩, ⟨2, 4, 7, 14⟩, ⟨2, 4, 6, 16⟩, ⟨2, 4, 5, 18⟩, ⟨2, 4, 4, 20⟩]
  exact AllWinning.cons node_6127 (AllWinning.cons node_5325 (AllWinning.cons node_6206 (AllWinning.cons node_5464 (AllWinning.cons node_4727 (AllWinning.cons node_4053 (AllWinning.cons node_6210 (AllWinning.cons node_5471 (AllWinning.cons node_4742 (AllWinning.cons node_4065 (AllWinning.cons node_3496 (AllWinning.cons node_2957 (AllWinning.cons node_2498 (AllWinning.cons node_2014 (AllWinning.cons node_1654 (AllWinning.cons node_1298 (AllWinning.nil))))))))))))))))

theorem node_7134 : Outcome ⟨2, 4, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨2, 3, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨2, 1, 14, 6⟩, ⟨2, 0, 14, 8⟩, ⟨2, 4, 13, 2⟩, ⟨2, 4, 12, 4⟩, ⟨2, 4, 11, 6⟩, ⟨2, 4, 10, 8⟩, ⟨2, 4, 9, 10⟩, ⟨2, 4, 8, 12⟩, ⟨2, 4, 7, 14⟩, ⟨2, 4, 6, 16⟩, ⟨2, 4, 5, 18⟩, ⟨2, 4, 4, 20⟩, ⟨2, 4, 3, 22⟩, ⟨2, 4, 2, 24⟩]
  exact AllWinning.cons node_6127 (AllWinning.cons node_5325 (AllWinning.cons node_6206 (AllWinning.cons node_5464 (AllWinning.cons node_4727 (AllWinning.cons node_4053 (AllWinning.cons node_6210 (AllWinning.cons node_5471 (AllWinning.cons node_4742 (AllWinning.cons node_4065 (AllWinning.cons node_3496 (AllWinning.cons node_2957 (AllWinning.cons node_2498 (AllWinning.cons node_2014 (AllWinning.cons node_1654 (AllWinning.cons node_1298 (AllWinning.cons node_1014 (AllWinning.cons node_786 (AllWinning.nil))))))))))))))))))

theorem node_7135 : Outcome ⟨2, 4, 14, 16⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 26⟩) (by decide) node_589

theorem node_7136 : Outcome ⟨2, 4, 14, 34⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 26⟩) (by decide) node_589

theorem node_7137 : Outcome ⟨2, 5, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 6⟩) (by decide) node_4732

theorem node_7138 : Outcome ⟨2, 5, 13, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 6⟩) (by decide) node_4732

theorem node_7139 : Outcome ⟨2, 5, 13, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 6⟩) (by decide) node_4732

theorem node_7140 : Outcome ⟨2, 6, 12, 2⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 2⟩) (by decide) node_6217

theorem node_7141 : Outcome ⟨2, 6, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 2⟩) (by decide) node_6217

theorem node_7142 : Outcome ⟨2, 6, 12, 16⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 2⟩) (by decide) node_6217

theorem node_7143 : Outcome ⟨2, 6, 12, 28⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 2⟩) (by decide) node_6217

theorem node_7144 : Outcome ⟨2, 7, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 2⟩) (by decide) node_6137

theorem node_7145 : Outcome ⟨2, 7, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 2⟩) (by decide) node_6137

theorem node_7146 : Outcome ⟨2, 7, 11, 12⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 16⟩) (by decide) node_2031

theorem node_7147 : Outcome ⟨2, 7, 11, 14⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 16⟩) (by decide) node_2031

theorem node_7148 : Outcome ⟨2, 7, 11, 20⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 16⟩) (by decide) node_2031

theorem node_7149 : Outcome ⟨2, 7, 11, 28⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 16⟩) (by decide) node_2031

theorem node_7150 : Outcome ⟨2, 8, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨2, 7, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨2, 8, 9, 2⟩, ⟨2, 8, 8, 4⟩]
  exact AllWinning.cons node_6149 (AllWinning.cons node_5341 (AllWinning.cons node_6227 (AllWinning.cons node_5478 (AllWinning.cons node_6231 (AllWinning.cons node_5486 (AllWinning.nil))))))

theorem node_7151 : Outcome ⟨2, 8, 10, 6⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 6⟩) (by decide) node_4745

theorem node_7152 : Outcome ⟨2, 8, 10, 16⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 6⟩) (by decide) node_4745

theorem node_7153 : Outcome ⟨2, 8, 10, 18⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 6⟩) (by decide) node_4745

theorem node_7154 : Outcome ⟨2, 9, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_7155 : Outcome ⟨2, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_7156 : Outcome ⟨2, 9, 9, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_7157 : Outcome ⟨2, 9, 9, 12⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_7158 : Outcome ⟨2, 10, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 8, 2⟩, ⟨0, 10, 8, 4⟩, ⟨2, 9, 8, 2⟩, ⟨2, 8, 8, 4⟩, ⟨2, 10, 7, 2⟩, ⟨2, 10, 6, 4⟩]
  exact AllWinning.cons node_6157 (AllWinning.cons node_5356 (AllWinning.cons node_6234 (AllWinning.cons node_5486 (AllWinning.cons node_6237 (AllWinning.cons node_5495 (AllWinning.nil))))))

theorem node_7159 : Outcome ⟨2, 10, 8, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 6⟩) (by decide) node_4774

theorem node_7160 : Outcome ⟨2, 10, 8, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 6⟩) (by decide) node_4774

theorem node_7161 : Outcome ⟨2, 10, 8, 18⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 6⟩) (by decide) node_4774

theorem node_7162 : Outcome ⟨2, 11, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 2⟩) (by decide) node_6162

theorem node_7163 : Outcome ⟨2, 11, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 2⟩) (by decide) node_6162

theorem node_7164 : Outcome ⟨2, 11, 7, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 16⟩) (by decide) node_2001

theorem node_7165 : Outcome ⟨2, 11, 7, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 16⟩) (by decide) node_2001

theorem node_7166 : Outcome ⟨2, 11, 7, 20⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 16⟩) (by decide) node_2001

theorem node_7167 : Outcome ⟨2, 11, 7, 28⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 16⟩) (by decide) node_2001

theorem node_7168 : Outcome ⟨2, 12, 6, 2⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 2⟩) (by decide) node_6241

theorem node_7169 : Outcome ⟨2, 12, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 2⟩) (by decide) node_6241

theorem node_7170 : Outcome ⟨2, 12, 6, 16⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 2⟩) (by decide) node_6241

theorem node_7171 : Outcome ⟨2, 12, 6, 28⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 2⟩) (by decide) node_6241

theorem node_7172 : Outcome ⟨2, 13, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 6⟩) (by decide) node_4774

theorem node_7173 : Outcome ⟨2, 13, 5, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 6⟩) (by decide) node_4774

theorem node_7174 : Outcome ⟨2, 13, 5, 12⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 6⟩) (by decide) node_4774

theorem node_7175 : Outcome ⟨2, 14, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 4, 2⟩, ⟨0, 14, 4, 4⟩, ⟨2, 13, 4, 2⟩, ⟨2, 12, 4, 4⟩, ⟨2, 14, 3, 2⟩, ⟨2, 14, 2, 4⟩]
  exact AllWinning.cons node_6181 (AllWinning.cons node_5371 (AllWinning.cons node_6255 (AllWinning.cons node_5500 (AllWinning.cons node_6258 (AllWinning.cons node_5507 (AllWinning.nil))))))

theorem node_7176 : Outcome ⟨2, 14, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 4, 2⟩, ⟨0, 14, 4, 4⟩, ⟨2, 13, 4, 2⟩, ⟨2, 12, 4, 4⟩, ⟨2, 11, 4, 6⟩, ⟨2, 10, 4, 8⟩, ⟨2, 14, 3, 2⟩, ⟨2, 14, 2, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 14, 0, 8⟩]
  exact AllWinning.cons node_6181 (AllWinning.cons node_5371 (AllWinning.cons node_6255 (AllWinning.cons node_5500 (AllWinning.cons node_4786 (AllWinning.cons node_4085 (AllWinning.cons node_6258 (AllWinning.cons node_5507 (AllWinning.cons node_4799 (AllWinning.cons node_4096 (AllWinning.nil))))))))))

theorem node_7177 : Outcome ⟨2, 14, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 4, 2⟩, ⟨0, 14, 4, 4⟩, ⟨2, 13, 4, 2⟩, ⟨2, 12, 4, 4⟩, ⟨2, 11, 4, 6⟩, ⟨2, 10, 4, 8⟩, ⟨2, 9, 4, 10⟩, ⟨2, 8, 4, 12⟩, ⟨2, 14, 3, 2⟩, ⟨2, 14, 2, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 14, 0, 8⟩]
  exact AllWinning.cons node_6181 (AllWinning.cons node_5371 (AllWinning.cons node_6255 (AllWinning.cons node_5500 (AllWinning.cons node_4786 (AllWinning.cons node_4085 (AllWinning.cons node_3518 (AllWinning.cons node_2973 (AllWinning.cons node_6258 (AllWinning.cons node_5507 (AllWinning.cons node_4799 (AllWinning.cons node_4096 (AllWinning.nil))))))))))))

theorem node_7178 : Outcome ⟨2, 14, 4, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 4, 2⟩, ⟨0, 14, 4, 4⟩, ⟨2, 13, 4, 2⟩, ⟨2, 12, 4, 4⟩, ⟨2, 11, 4, 6⟩, ⟨2, 10, 4, 8⟩, ⟨2, 9, 4, 10⟩, ⟨2, 8, 4, 12⟩, ⟨2, 7, 4, 14⟩, ⟨2, 6, 4, 16⟩, ⟨2, 14, 3, 2⟩, ⟨2, 14, 2, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 14, 0, 8⟩]
  exact AllWinning.cons node_6181 (AllWinning.cons node_5371 (AllWinning.cons node_6255 (AllWinning.cons node_5500 (AllWinning.cons node_4786 (AllWinning.cons node_4085 (AllWinning.cons node_3518 (AllWinning.cons node_2973 (AllWinning.cons node_2510 (AllWinning.cons node_2023 (AllWinning.cons node_6258 (AllWinning.cons node_5507 (AllWinning.cons node_4799 (AllWinning.cons node_4096 (AllWinning.nil))))))))))))))

theorem node_7179 : Outcome ⟨2, 14, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 4, 2⟩, ⟨0, 14, 4, 4⟩, ⟨2, 13, 4, 2⟩, ⟨2, 12, 4, 4⟩, ⟨2, 11, 4, 6⟩, ⟨2, 10, 4, 8⟩, ⟨2, 9, 4, 10⟩, ⟨2, 8, 4, 12⟩, ⟨2, 7, 4, 14⟩, ⟨2, 6, 4, 16⟩, ⟨2, 5, 4, 18⟩, ⟨2, 4, 4, 20⟩, ⟨2, 14, 3, 2⟩, ⟨2, 14, 2, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 14, 0, 8⟩]
  exact AllWinning.cons node_6181 (AllWinning.cons node_5371 (AllWinning.cons node_6255 (AllWinning.cons node_5500 (AllWinning.cons node_4786 (AllWinning.cons node_4085 (AllWinning.cons node_3518 (AllWinning.cons node_2973 (AllWinning.cons node_2510 (AllWinning.cons node_2023 (AllWinning.cons node_1660 (AllWinning.cons node_1298 (AllWinning.cons node_6258 (AllWinning.cons node_5507 (AllWinning.cons node_4799 (AllWinning.cons node_4096 (AllWinning.nil))))))))))))))))

theorem node_7180 : Outcome ⟨2, 14, 4, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 4, 2⟩, ⟨0, 14, 4, 4⟩, ⟨2, 13, 4, 2⟩, ⟨2, 12, 4, 4⟩, ⟨2, 11, 4, 6⟩, ⟨2, 10, 4, 8⟩, ⟨2, 9, 4, 10⟩, ⟨2, 8, 4, 12⟩, ⟨2, 7, 4, 14⟩, ⟨2, 6, 4, 16⟩, ⟨2, 5, 4, 18⟩, ⟨2, 4, 4, 20⟩, ⟨2, 3, 4, 22⟩, ⟨2, 2, 4, 24⟩, ⟨2, 14, 3, 2⟩, ⟨2, 14, 2, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 14, 0, 8⟩]
  exact AllWinning.cons node_6181 (AllWinning.cons node_5371 (AllWinning.cons node_6255 (AllWinning.cons node_5500 (AllWinning.cons node_4786 (AllWinning.cons node_4085 (AllWinning.cons node_3518 (AllWinning.cons node_2973 (AllWinning.cons node_2510 (AllWinning.cons node_2023 (AllWinning.cons node_1660 (AllWinning.cons node_1298 (AllWinning.cons node_1010 (AllWinning.cons node_777 (AllWinning.cons node_6258 (AllWinning.cons node_5507 (AllWinning.cons node_4799 (AllWinning.cons node_4096 (AllWinning.nil))))))))))))))))))

theorem node_7181 : Outcome ⟨2, 14, 4, 16⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 26⟩) (by decide) node_567

theorem node_7182 : Outcome ⟨2, 14, 4, 34⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 26⟩) (by decide) node_567

theorem node_7183 : Outcome ⟨2, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 6⟩) (by decide) node_4804

theorem node_7184 : Outcome ⟨2, 15, 3, 10⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 16⟩) (by decide) node_2031

theorem node_7185 : Outcome ⟨2, 15, 3, 12⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 16⟩) (by decide) node_2031

theorem node_7186 : Outcome ⟨2, 16, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 6⟩) (by decide) node_4794

theorem node_7187 : Outcome ⟨2, 16, 2, 16⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 32⟩) (by decide) node_197

theorem node_7188 : Outcome ⟨2, 16, 2, 32⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 32⟩) (by decide) node_197

theorem node_7189 : Outcome ⟨2, 17, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 1, 2⟩, ⟨0, 17, 1, 4⟩, ⟨2, 16, 1, 2⟩, ⟨2, 15, 1, 4⟩, ⟨2, 17, 0, 2⟩]
  exact AllWinning.cons node_6192 (AllWinning.cons node_5383 (AllWinning.cons node_6265 (AllWinning.cons node_5510 (AllWinning.cons node_6269 (AllWinning.nil)))))

theorem node_7190 : Outcome ⟨2, 17, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 1, 2⟩, ⟨0, 17, 1, 4⟩, ⟨2, 16, 1, 2⟩, ⟨2, 15, 1, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 13, 1, 8⟩, ⟨2, 17, 0, 2⟩]
  exact AllWinning.cons node_6192 (AllWinning.cons node_5383 (AllWinning.cons node_6265 (AllWinning.cons node_5510 (AllWinning.cons node_4799 (AllWinning.cons node_4094 (AllWinning.cons node_6269 (AllWinning.nil)))))))

theorem node_7191 : Outcome ⟨2, 17, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 1, 2⟩, ⟨0, 17, 1, 4⟩, ⟨2, 16, 1, 2⟩, ⟨2, 15, 1, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 13, 1, 8⟩, ⟨2, 12, 1, 10⟩, ⟨2, 11, 1, 12⟩, ⟨2, 17, 0, 2⟩]
  exact AllWinning.cons node_6192 (AllWinning.cons node_5383 (AllWinning.cons node_6265 (AllWinning.cons node_5510 (AllWinning.cons node_4799 (AllWinning.cons node_4094 (AllWinning.cons node_3530 (AllWinning.cons node_2984 (AllWinning.cons node_6269 (AllWinning.nil)))))))))

theorem node_7192 : Outcome ⟨2, 17, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 1, 2⟩, ⟨0, 17, 1, 4⟩, ⟨2, 16, 1, 2⟩, ⟨2, 15, 1, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 13, 1, 8⟩, ⟨2, 12, 1, 10⟩, ⟨2, 11, 1, 12⟩, ⟨2, 10, 1, 14⟩, ⟨2, 9, 1, 16⟩, ⟨2, 17, 0, 2⟩]
  exact AllWinning.cons node_6192 (AllWinning.cons node_5383 (AllWinning.cons node_6265 (AllWinning.cons node_5510 (AllWinning.cons node_4799 (AllWinning.cons node_4094 (AllWinning.cons node_3530 (AllWinning.cons node_2984 (AllWinning.cons node_2523 (AllWinning.cons node_2047 (AllWinning.cons node_6269 (AllWinning.nil)))))))))))

theorem node_7193 : Outcome ⟨2, 17, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 1, 2⟩, ⟨0, 17, 1, 4⟩, ⟨2, 16, 1, 2⟩, ⟨2, 15, 1, 4⟩, ⟨2, 14, 1, 6⟩, ⟨2, 13, 1, 8⟩, ⟨2, 12, 1, 10⟩, ⟨2, 11, 1, 12⟩, ⟨2, 10, 1, 14⟩, ⟨2, 9, 1, 16⟩, ⟨2, 8, 1, 18⟩, ⟨2, 7, 1, 20⟩, ⟨2, 6, 1, 22⟩, ⟨2, 5, 1, 24⟩, ⟨2, 17, 0, 2⟩]
  exact AllWinning.cons node_6192 (AllWinning.cons node_5383 (AllWinning.cons node_6265 (AllWinning.cons node_5510 (AllWinning.cons node_4799 (AllWinning.cons node_4094 (AllWinning.cons node_3530 (AllWinning.cons node_2984 (AllWinning.cons node_2523 (AllWinning.cons node_2047 (AllWinning.cons node_1668 (AllWinning.cons node_1309 (AllWinning.cons node_1023 (AllWinning.cons node_791 (AllWinning.cons node_6269 (AllWinning.nil)))))))))))))))

theorem node_7194 : Outcome ⟨2, 17, 1, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 26⟩) (by decide) node_589

theorem node_7195 : Outcome ⟨2, 17, 1, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 26⟩) (by decide) node_589

theorem node_7196 : Outcome ⟨2, 18, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 6⟩) (by decide) node_4804

theorem node_7197 : Outcome ⟨2, 18, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 6⟩) (by decide) node_4804

theorem node_7198 : Outcome ⟨2, 18, 0, 14⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 6⟩) (by decide) node_4804

theorem node_7199 : Outcome ⟨2, 18, 0, 32⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 32⟩) (by decide) node_218

theorem node_7200 : Outcome ⟨3, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 2⟩) (by decide) node_6272

theorem node_7201 : Outcome ⟨3, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 2⟩) (by decide) node_6272

theorem node_7202 : Outcome ⟨3, 1, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 2⟩) (by decide) node_6272

theorem node_7203 : Outcome ⟨3, 1, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 2⟩) (by decide) node_6272

theorem node_7204 : Outcome ⟨3, 1, 16, 14⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 20⟩) (by decide) node_1328

theorem node_7205 : Outcome ⟨3, 1, 16, 24⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 20⟩) (by decide) node_1328

theorem node_7206 : Outcome ⟨3, 2, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 15, 2⟩, ⟨1, 2, 15, 4⟩, ⟨3, 1, 15, 2⟩, ⟨3, 0, 15, 4⟩, ⟨3, 2, 14, 2⟩, ⟨3, 2, 13, 4⟩]
  exact AllWinning.cons node_6203 (AllWinning.cons node_5396 (AllWinning.cons node_6280 (AllWinning.cons node_5519 (AllWinning.cons node_6284 (AllWinning.cons node_5528 (AllWinning.nil))))))

theorem node_7207 : Outcome ⟨3, 2, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 6⟩) (by decide) node_4577

theorem node_7208 : Outcome ⟨3, 2, 15, 10⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 16⟩) (by decide) node_2072

theorem node_7209 : Outcome ⟨3, 2, 15, 12⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 16⟩) (by decide) node_2072

theorem node_7210 : Outcome ⟨3, 2, 15, 32⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 16⟩) (by decide) node_2072

theorem node_7211 : Outcome ⟨3, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7212 : Outcome ⟨3, 3, 14, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7213 : Outcome ⟨3, 3, 14, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7214 : Outcome ⟨3, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7215 : Outcome ⟨3, 4, 13, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7216 : Outcome ⟨3, 4, 13, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7217 : Outcome ⟨3, 5, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 4, 12, 2⟩) (by decide) node_6295

theorem node_7218 : Outcome ⟨3, 5, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 4, 12, 2⟩) (by decide) node_6295

theorem node_7219 : Outcome ⟨3, 5, 12, 14⟩ true :=
  Outcome.win (q := ⟨3, 4, 12, 2⟩) (by decide) node_6295

theorem node_7220 : Outcome ⟨3, 6, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 4⟩) (by decide) node_5538

theorem node_7221 : Outcome ⟨3, 6, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 4⟩) (by decide) node_5538

theorem node_7222 : Outcome ⟨3, 6, 11, 24⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 20⟩) (by decide) node_1359

theorem node_7223 : Outcome ⟨3, 7, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 10, 2⟩, ⟨1, 7, 10, 4⟩, ⟨3, 6, 10, 2⟩, ⟨3, 5, 10, 4⟩, ⟨3, 7, 9, 2⟩, ⟨3, 7, 8, 4⟩]
  exact AllWinning.cons node_6227 (AllWinning.cons node_5416 (AllWinning.cons node_6310 (AllWinning.cons node_5535 (AllWinning.cons node_6313 (AllWinning.cons node_5543 (AllWinning.nil))))))

theorem node_7224 : Outcome ⟨3, 7, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 10, 2⟩, ⟨1, 7, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨3, 6, 10, 2⟩, ⟨3, 5, 10, 4⟩, ⟨3, 4, 10, 6⟩, ⟨3, 3, 10, 8⟩, ⟨3, 7, 9, 2⟩, ⟨3, 7, 8, 4⟩, ⟨3, 7, 7, 6⟩, ⟨3, 7, 6, 8⟩]
  exact AllWinning.cons node_6227 (AllWinning.cons node_5416 (AllWinning.cons node_4603 (AllWinning.cons node_6310 (AllWinning.cons node_5535 (AllWinning.cons node_4828 (AllWinning.cons node_4110 (AllWinning.cons node_6313 (AllWinning.cons node_5543 (AllWinning.cons node_4840 (AllWinning.cons node_4125 (AllWinning.nil)))))))))))

theorem node_7225 : Outcome ⟨3, 7, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 10, 2⟩, ⟨1, 7, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨3, 6, 10, 2⟩, ⟨3, 5, 10, 4⟩, ⟨3, 4, 10, 6⟩, ⟨3, 3, 10, 8⟩, ⟨3, 2, 10, 10⟩, ⟨3, 1, 10, 12⟩, ⟨3, 7, 9, 2⟩, ⟨3, 7, 8, 4⟩, ⟨3, 7, 7, 6⟩, ⟨3, 7, 6, 8⟩, ⟨3, 7, 5, 10⟩, ⟨3, 7, 4, 12⟩]
  exact AllWinning.cons node_6227 (AllWinning.cons node_5416 (AllWinning.cons node_4603 (AllWinning.cons node_6310 (AllWinning.cons node_5535 (AllWinning.cons node_4828 (AllWinning.cons node_4110 (AllWinning.cons node_3544 (AllWinning.cons node_2997 (AllWinning.cons node_6313 (AllWinning.cons node_5543 (AllWinning.cons node_4840 (AllWinning.cons node_4125 (AllWinning.cons node_3563 (AllWinning.cons node_3023 (AllWinning.nil)))))))))))))))

theorem node_7226 : Outcome ⟨3, 7, 10, 10⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 16⟩) (by decide) node_2103

theorem node_7227 : Outcome ⟨3, 7, 10, 12⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 16⟩) (by decide) node_2103

theorem node_7228 : Outcome ⟨3, 8, 9, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 4⟩) (by decide) node_5538

theorem node_7229 : Outcome ⟨3, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 4⟩) (by decide) node_5538

theorem node_7230 : Outcome ⟨3, 8, 9, 8⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 4⟩) (by decide) node_5538

theorem node_7231 : Outcome ⟨3, 8, 9, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 4⟩) (by decide) node_5538

theorem node_7232 : Outcome ⟨3, 8, 9, 14⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 4⟩) (by decide) node_5538

theorem node_7233 : Outcome ⟨3, 9, 8, 2⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 4⟩) (by decide) node_5553

theorem node_7234 : Outcome ⟨3, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 4⟩) (by decide) node_5553

theorem node_7235 : Outcome ⟨3, 9, 8, 8⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 4⟩) (by decide) node_5553

theorem node_7236 : Outcome ⟨3, 9, 8, 12⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 4⟩) (by decide) node_5553

theorem node_7237 : Outcome ⟨3, 9, 8, 14⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 4⟩) (by decide) node_5553

theorem node_7238 : Outcome ⟨3, 10, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 7, 2⟩, ⟨1, 10, 7, 4⟩, ⟨3, 9, 7, 2⟩, ⟨3, 8, 7, 4⟩, ⟨3, 10, 6, 2⟩, ⟨3, 10, 5, 4⟩]
  exact AllWinning.cons node_6237 (AllWinning.cons node_5427 (AllWinning.cons node_6322 (AllWinning.cons node_5548 (AllWinning.cons node_6327 (AllWinning.cons node_5558 (AllWinning.nil))))))

theorem node_7239 : Outcome ⟨3, 10, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 7, 2⟩, ⟨1, 10, 7, 4⟩, ⟨0, 10, 7, 6⟩, ⟨3, 9, 7, 2⟩, ⟨3, 8, 7, 4⟩, ⟨3, 7, 7, 6⟩, ⟨3, 6, 7, 8⟩, ⟨3, 10, 6, 2⟩, ⟨3, 10, 5, 4⟩, ⟨3, 10, 4, 6⟩, ⟨3, 10, 3, 8⟩]
  exact AllWinning.cons node_6237 (AllWinning.cons node_5427 (AllWinning.cons node_4613 (AllWinning.cons node_6322 (AllWinning.cons node_5548 (AllWinning.cons node_4840 (AllWinning.cons node_4120 (AllWinning.cons node_6327 (AllWinning.cons node_5558 (AllWinning.cons node_4854 (AllWinning.cons node_4138 (AllWinning.nil)))))))))))

theorem node_7240 : Outcome ⟨3, 10, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 7, 2⟩, ⟨1, 10, 7, 4⟩, ⟨0, 10, 7, 6⟩, ⟨3, 9, 7, 2⟩, ⟨3, 8, 7, 4⟩, ⟨3, 7, 7, 6⟩, ⟨3, 6, 7, 8⟩, ⟨3, 5, 7, 10⟩, ⟨3, 4, 7, 12⟩, ⟨3, 10, 6, 2⟩, ⟨3, 10, 5, 4⟩, ⟨3, 10, 4, 6⟩, ⟨3, 10, 3, 8⟩, ⟨3, 10, 2, 10⟩, ⟨3, 10, 1, 12⟩]
  exact AllWinning.cons node_6237 (AllWinning.cons node_5427 (AllWinning.cons node_4613 (AllWinning.cons node_6322 (AllWinning.cons node_5548 (AllWinning.cons node_4840 (AllWinning.cons node_4120 (AllWinning.cons node_3555 (AllWinning.cons node_3012 (AllWinning.cons node_6327 (AllWinning.cons node_5558 (AllWinning.cons node_4854 (AllWinning.cons node_4138 (AllWinning.cons node_3574 (AllWinning.cons node_3036 (AllWinning.nil)))))))))))))))

theorem node_7241 : Outcome ⟨3, 10, 7, 10⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 16⟩) (by decide) node_2072

theorem node_7242 : Outcome ⟨3, 10, 7, 12⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 16⟩) (by decide) node_2072

theorem node_7243 : Outcome ⟨3, 11, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 4⟩) (by decide) node_5553

theorem node_7244 : Outcome ⟨3, 11, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 4⟩) (by decide) node_5553

theorem node_7245 : Outcome ⟨3, 11, 6, 24⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 20⟩) (by decide) node_1328

theorem node_7246 : Outcome ⟨3, 12, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 2⟩) (by decide) node_6330

theorem node_7247 : Outcome ⟨3, 12, 5, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 2⟩) (by decide) node_6330

theorem node_7248 : Outcome ⟨3, 12, 5, 14⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 2⟩) (by decide) node_6330

theorem node_7249 : Outcome ⟨3, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨3, 12, 4, 2⟩) (by decide) node_6341

theorem node_7250 : Outcome ⟨3, 13, 4, 12⟩ true :=
  Outcome.win (q := ⟨3, 12, 4, 2⟩) (by decide) node_6341

theorem node_7251 : Outcome ⟨3, 13, 4, 18⟩ true :=
  Outcome.win (q := ⟨3, 12, 4, 2⟩) (by decide) node_6341

theorem node_7252 : Outcome ⟨3, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 2⟩) (by decide) node_6345

theorem node_7253 : Outcome ⟨3, 14, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 2⟩) (by decide) node_6345

theorem node_7254 : Outcome ⟨3, 14, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 2⟩) (by decide) node_6345

theorem node_7255 : Outcome ⟨3, 15, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 15, 2, 2⟩, ⟨1, 15, 2, 4⟩, ⟨3, 14, 2, 2⟩, ⟨3, 13, 2, 4⟩, ⟨3, 15, 1, 2⟩, ⟨3, 15, 0, 4⟩]
  exact AllWinning.cons node_6262 (AllWinning.cons node_5445 (AllWinning.cons node_6352 (AllWinning.cons node_5564 (AllWinning.cons node_6356 (AllWinning.cons node_5572 (AllWinning.nil))))))

theorem node_7256 : Outcome ⟨3, 15, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 6⟩) (by decide) node_4636

theorem node_7257 : Outcome ⟨3, 15, 2, 10⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 16⟩) (by decide) node_2103

theorem node_7258 : Outcome ⟨3, 15, 2, 12⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 16⟩) (by decide) node_2103

theorem node_7259 : Outcome ⟨3, 15, 2, 32⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 16⟩) (by decide) node_2103

theorem node_7260 : Outcome ⟨3, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 2⟩) (by decide) node_6360

theorem node_7261 : Outcome ⟨3, 16, 1, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 2⟩) (by decide) node_6360

theorem node_7262 : Outcome ⟨3, 16, 1, 8⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 2⟩) (by decide) node_6360

theorem node_7263 : Outcome ⟨3, 16, 1, 14⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 20⟩) (by decide) node_1359

theorem node_7264 : Outcome ⟨3, 16, 1, 24⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 20⟩) (by decide) node_1359

theorem node_7265 : Outcome ⟨3, 17, 0, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 2⟩) (by decide) node_6360

theorem node_7266 : Outcome ⟨4, 0, 16, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 2⟩) (by decide) node_6272

theorem node_7267 : Outcome ⟨4, 0, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 2⟩) (by decide) node_6272

theorem node_7268 : Outcome ⟨4, 0, 16, 18⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 24⟩) (by decide) node_831

theorem node_7269 : Outcome ⟨4, 0, 16, 24⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 24⟩) (by decide) node_831

theorem node_7270 : Outcome ⟨4, 1, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 15, 2⟩, ⟨2, 1, 15, 4⟩, ⟨4, 0, 15, 2⟩, ⟨4, 1, 14, 2⟩, ⟨4, 1, 13, 4⟩]
  exact AllWinning.cons node_6280 (AllWinning.cons node_5460 (AllWinning.cons node_6368 (AllWinning.cons node_6372 (AllWinning.cons node_5580 (AllWinning.nil)))))

theorem node_7271 : Outcome ⟨4, 1, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 15, 2⟩, ⟨2, 1, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨0, 1, 15, 8⟩, ⟨4, 0, 15, 2⟩, ⟨4, 1, 14, 2⟩, ⟨4, 1, 13, 4⟩, ⟨4, 1, 12, 6⟩, ⟨4, 1, 11, 8⟩]
  exact AllWinning.cons node_6280 (AllWinning.cons node_5460 (AllWinning.cons node_4654 (AllWinning.cons node_3933 (AllWinning.cons node_6368 (AllWinning.cons node_6372 (AllWinning.cons node_5580 (AllWinning.cons node_4880 (AllWinning.cons node_4158 (AllWinning.nil)))))))))

theorem node_7272 : Outcome ⟨4, 1, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 15, 2⟩, ⟨2, 1, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨0, 1, 15, 8⟩, ⟨4, 0, 15, 2⟩, ⟨4, 1, 14, 2⟩, ⟨4, 1, 13, 4⟩, ⟨4, 1, 12, 6⟩, ⟨4, 1, 11, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 1, 9, 12⟩]
  exact AllWinning.cons node_6280 (AllWinning.cons node_5460 (AllWinning.cons node_4654 (AllWinning.cons node_3933 (AllWinning.cons node_6368 (AllWinning.cons node_6372 (AllWinning.cons node_5580 (AllWinning.cons node_4880 (AllWinning.cons node_4158 (AllWinning.cons node_3591 (AllWinning.cons node_3050 (AllWinning.nil)))))))))))

theorem node_7273 : Outcome ⟨4, 1, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 15, 2⟩, ⟨2, 1, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨0, 1, 15, 8⟩, ⟨4, 0, 15, 2⟩, ⟨4, 1, 14, 2⟩, ⟨4, 1, 13, 4⟩, ⟨4, 1, 12, 6⟩, ⟨4, 1, 11, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 1, 9, 12⟩, ⟨4, 1, 8, 14⟩, ⟨4, 1, 7, 16⟩]
  exact AllWinning.cons node_6280 (AllWinning.cons node_5460 (AllWinning.cons node_4654 (AllWinning.cons node_3933 (AllWinning.cons node_6368 (AllWinning.cons node_6372 (AllWinning.cons node_5580 (AllWinning.cons node_4880 (AllWinning.cons node_4158 (AllWinning.cons node_3591 (AllWinning.cons node_3050 (AllWinning.cons node_2586 (AllWinning.cons node_2130 (AllWinning.nil)))))))))))))

theorem node_7274 : Outcome ⟨4, 1, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 15, 2⟩, ⟨2, 1, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨0, 1, 15, 8⟩, ⟨4, 0, 15, 2⟩, ⟨4, 1, 14, 2⟩, ⟨4, 1, 13, 4⟩, ⟨4, 1, 12, 6⟩, ⟨4, 1, 11, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 1, 9, 12⟩, ⟨4, 1, 8, 14⟩, ⟨4, 1, 7, 16⟩, ⟨4, 1, 6, 18⟩, ⟨4, 1, 5, 20⟩]
  exact AllWinning.cons node_6280 (AllWinning.cons node_5460 (AllWinning.cons node_4654 (AllWinning.cons node_3933 (AllWinning.cons node_6368 (AllWinning.cons node_6372 (AllWinning.cons node_5580 (AllWinning.cons node_4880 (AllWinning.cons node_4158 (AllWinning.cons node_3591 (AllWinning.cons node_3050 (AllWinning.cons node_2586 (AllWinning.cons node_2130 (AllWinning.cons node_1722 (AllWinning.cons node_1379 (AllWinning.nil)))))))))))))))

theorem node_7275 : Outcome ⟨4, 1, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 15, 2⟩, ⟨2, 1, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨0, 1, 15, 8⟩, ⟨4, 0, 15, 2⟩, ⟨4, 1, 14, 2⟩, ⟨4, 1, 13, 4⟩, ⟨4, 1, 12, 6⟩, ⟨4, 1, 11, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 1, 9, 12⟩, ⟨4, 1, 8, 14⟩, ⟨4, 1, 7, 16⟩, ⟨4, 1, 6, 18⟩, ⟨4, 1, 5, 20⟩, ⟨4, 1, 4, 22⟩, ⟨4, 1, 3, 24⟩]
  exact AllWinning.cons node_6280 (AllWinning.cons node_5460 (AllWinning.cons node_4654 (AllWinning.cons node_3933 (AllWinning.cons node_6368 (AllWinning.cons node_6372 (AllWinning.cons node_5580 (AllWinning.cons node_4880 (AllWinning.cons node_4158 (AllWinning.cons node_3591 (AllWinning.cons node_3050 (AllWinning.cons node_2586 (AllWinning.cons node_2130 (AllWinning.cons node_1722 (AllWinning.cons node_1379 (AllWinning.cons node_1067 (AllWinning.cons node_838 (AllWinning.nil)))))))))))))))))

theorem node_7276 : Outcome ⟨4, 1, 15, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 26⟩) (by decide) node_628

theorem node_7277 : Outcome ⟨4, 2, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨4, 1, 14, 2⟩, ⟨4, 0, 14, 4⟩, ⟨4, 2, 13, 2⟩, ⟨4, 2, 12, 4⟩]
  exact AllWinning.cons node_6284 (AllWinning.cons node_5464 (AllWinning.cons node_6372 (AllWinning.cons node_5576 (AllWinning.cons node_6374 (AllWinning.cons node_5586 (AllWinning.nil))))))

theorem node_7278 : Outcome ⟨4, 2, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨1, 2, 14, 6⟩, ⟨0, 2, 14, 8⟩, ⟨4, 1, 14, 2⟩, ⟨4, 0, 14, 4⟩, ⟨4, 2, 13, 2⟩, ⟨4, 2, 12, 4⟩, ⟨4, 2, 11, 6⟩, ⟨4, 2, 10, 8⟩]
  exact AllWinning.cons node_6284 (AllWinning.cons node_5464 (AllWinning.cons node_4657 (AllWinning.cons node_3936 (AllWinning.cons node_6372 (AllWinning.cons node_5576 (AllWinning.cons node_6374 (AllWinning.cons node_5586 (AllWinning.cons node_4884 (AllWinning.cons node_4161 (AllWinning.nil))))))))))

theorem node_7279 : Outcome ⟨4, 2, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨1, 2, 14, 6⟩, ⟨0, 2, 14, 8⟩, ⟨4, 1, 14, 2⟩, ⟨4, 0, 14, 4⟩, ⟨4, 2, 13, 2⟩, ⟨4, 2, 12, 4⟩, ⟨4, 2, 11, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 2, 9, 10⟩, ⟨4, 2, 8, 12⟩]
  exact AllWinning.cons node_6284 (AllWinning.cons node_5464 (AllWinning.cons node_4657 (AllWinning.cons node_3936 (AllWinning.cons node_6372 (AllWinning.cons node_5576 (AllWinning.cons node_6374 (AllWinning.cons node_5586 (AllWinning.cons node_4884 (AllWinning.cons node_4161 (AllWinning.cons node_3596 (AllWinning.cons node_3055 (AllWinning.nil))))))))))))

theorem node_7280 : Outcome ⟨4, 2, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨1, 2, 14, 6⟩, ⟨0, 2, 14, 8⟩, ⟨4, 1, 14, 2⟩, ⟨4, 0, 14, 4⟩, ⟨4, 2, 13, 2⟩, ⟨4, 2, 12, 4⟩, ⟨4, 2, 11, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 2, 9, 10⟩, ⟨4, 2, 8, 12⟩, ⟨4, 2, 7, 14⟩, ⟨4, 2, 6, 16⟩]
  exact AllWinning.cons node_6284 (AllWinning.cons node_5464 (AllWinning.cons node_4657 (AllWinning.cons node_3936 (AllWinning.cons node_6372 (AllWinning.cons node_5576 (AllWinning.cons node_6374 (AllWinning.cons node_5586 (AllWinning.cons node_4884 (AllWinning.cons node_4161 (AllWinning.cons node_3596 (AllWinning.cons node_3055 (AllWinning.cons node_2592 (AllWinning.cons node_2135 (AllWinning.nil))))))))))))))

theorem node_7281 : Outcome ⟨4, 2, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨1, 2, 14, 6⟩, ⟨0, 2, 14, 8⟩, ⟨4, 1, 14, 2⟩, ⟨4, 0, 14, 4⟩, ⟨4, 2, 13, 2⟩, ⟨4, 2, 12, 4⟩, ⟨4, 2, 11, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 2, 9, 10⟩, ⟨4, 2, 8, 12⟩, ⟨4, 2, 7, 14⟩, ⟨4, 2, 6, 16⟩, ⟨4, 2, 5, 18⟩, ⟨4, 2, 4, 20⟩]
  exact AllWinning.cons node_6284 (AllWinning.cons node_5464 (AllWinning.cons node_4657 (AllWinning.cons node_3936 (AllWinning.cons node_6372 (AllWinning.cons node_5576 (AllWinning.cons node_6374 (AllWinning.cons node_5586 (AllWinning.cons node_4884 (AllWinning.cons node_4161 (AllWinning.cons node_3596 (AllWinning.cons node_3055 (AllWinning.cons node_2592 (AllWinning.cons node_2135 (AllWinning.cons node_1729 (AllWinning.cons node_1385 (AllWinning.nil))))))))))))))))

theorem node_7282 : Outcome ⟨4, 2, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 14, 2⟩, ⟨2, 2, 14, 4⟩, ⟨1, 2, 14, 6⟩, ⟨0, 2, 14, 8⟩, ⟨4, 1, 14, 2⟩, ⟨4, 0, 14, 4⟩, ⟨4, 2, 13, 2⟩, ⟨4, 2, 12, 4⟩, ⟨4, 2, 11, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 2, 9, 10⟩, ⟨4, 2, 8, 12⟩, ⟨4, 2, 7, 14⟩, ⟨4, 2, 6, 16⟩, ⟨4, 2, 5, 18⟩, ⟨4, 2, 4, 20⟩, ⟨4, 2, 3, 22⟩, ⟨4, 2, 2, 24⟩]
  exact AllWinning.cons node_6284 (AllWinning.cons node_5464 (AllWinning.cons node_4657 (AllWinning.cons node_3936 (AllWinning.cons node_6372 (AllWinning.cons node_5576 (AllWinning.cons node_6374 (AllWinning.cons node_5586 (AllWinning.cons node_4884 (AllWinning.cons node_4161 (AllWinning.cons node_3596 (AllWinning.cons node_3055 (AllWinning.cons node_2592 (AllWinning.cons node_2135 (AllWinning.cons node_1729 (AllWinning.cons node_1385 (AllWinning.cons node_1071 (AllWinning.cons node_842 (AllWinning.nil))))))))))))))))))

theorem node_7283 : Outcome ⟨4, 2, 14, 16⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 26⟩) (by decide) node_646

theorem node_7284 : Outcome ⟨4, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7285 : Outcome ⟨4, 3, 13, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7286 : Outcome ⟨4, 3, 13, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 2⟩) (by decide) node_6288

theorem node_7287 : Outcome ⟨4, 4, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 4, 12, 2⟩) (by decide) node_6295

theorem node_7288 : Outcome ⟨4, 4, 12, 18⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 24⟩) (by decide) node_857

theorem node_7289 : Outcome ⟨4, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 2⟩) (by decide) node_6299

theorem node_7290 : Outcome ⟨4, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 8⟩) (by decide) node_4173

theorem node_7291 : Outcome ⟨4, 5, 11, 18⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 8⟩) (by decide) node_4173

theorem node_7292 : Outcome ⟨4, 5, 11, 26⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 8⟩) (by decide) node_4173

theorem node_7293 : Outcome ⟨4, 6, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.nil))))))

theorem node_7294 : Outcome ⟨4, 6, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 3, 10, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩, ⟨4, 6, 7, 6⟩, ⟨4, 6, 6, 8⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_4674 (AllWinning.cons node_3953 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_4887 (AllWinning.cons node_4161 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.cons node_4896 (AllWinning.cons node_4185 (AllWinning.nil))))))))))))

theorem node_7295 : Outcome ⟨4, 6, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 3, 10, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 0, 10, 12⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩, ⟨4, 6, 7, 6⟩, ⟨4, 6, 6, 8⟩, ⟨4, 6, 5, 10⟩, ⟨4, 6, 4, 12⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_4674 (AllWinning.cons node_3953 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_4887 (AllWinning.cons node_4161 (AllWinning.cons node_3591 (AllWinning.cons node_3047 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.cons node_4896 (AllWinning.cons node_4185 (AllWinning.cons node_3607 (AllWinning.cons node_3068 (AllWinning.nil))))))))))))))))

theorem node_7296 : Outcome ⟨4, 6, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 3, 10, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 0, 10, 12⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩, ⟨4, 6, 7, 6⟩, ⟨4, 6, 6, 8⟩, ⟨4, 6, 5, 10⟩, ⟨4, 6, 4, 12⟩, ⟨4, 6, 3, 14⟩, ⟨4, 6, 2, 16⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_4674 (AllWinning.cons node_3953 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_4887 (AllWinning.cons node_4161 (AllWinning.cons node_3591 (AllWinning.cons node_3047 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.cons node_4896 (AllWinning.cons node_4185 (AllWinning.cons node_3607 (AllWinning.cons node_3068 (AllWinning.cons node_2609 (AllWinning.cons node_2151 (AllWinning.nil))))))))))))))))))

theorem node_7297 : Outcome ⟨4, 6, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 3, 10, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 0, 10, 12⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩, ⟨4, 6, 7, 6⟩, ⟨4, 6, 6, 8⟩, ⟨4, 6, 5, 10⟩, ⟨4, 6, 4, 12⟩, ⟨4, 6, 3, 14⟩, ⟨4, 6, 2, 16⟩, ⟨4, 6, 1, 18⟩, ⟨4, 6, 0, 20⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_4674 (AllWinning.cons node_3953 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_4887 (AllWinning.cons node_4161 (AllWinning.cons node_3591 (AllWinning.cons node_3047 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.cons node_4896 (AllWinning.cons node_4185 (AllWinning.cons node_3607 (AllWinning.cons node_3068 (AllWinning.cons node_2609 (AllWinning.cons node_2151 (AllWinning.cons node_1746 (AllWinning.cons node_1403 (AllWinning.nil))))))))))))))))))))

theorem node_7298 : Outcome ⟨4, 6, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 3, 10, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 0, 10, 12⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩, ⟨4, 6, 7, 6⟩, ⟨4, 6, 6, 8⟩, ⟨4, 6, 5, 10⟩, ⟨4, 6, 4, 12⟩, ⟨4, 6, 3, 14⟩, ⟨4, 6, 2, 16⟩, ⟨4, 6, 1, 18⟩, ⟨4, 6, 0, 20⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_4674 (AllWinning.cons node_3953 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_4887 (AllWinning.cons node_4161 (AllWinning.cons node_3591 (AllWinning.cons node_3047 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.cons node_4896 (AllWinning.cons node_4185 (AllWinning.cons node_3607 (AllWinning.cons node_3068 (AllWinning.cons node_2609 (AllWinning.cons node_2151 (AllWinning.cons node_1746 (AllWinning.cons node_1403 (AllWinning.nil))))))))))))))))))))

theorem node_7299 : Outcome ⟨4, 6, 10, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 3, 10, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 0, 10, 12⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩, ⟨4, 6, 7, 6⟩, ⟨4, 6, 6, 8⟩, ⟨4, 6, 5, 10⟩, ⟨4, 6, 4, 12⟩, ⟨4, 6, 3, 14⟩, ⟨4, 6, 2, 16⟩, ⟨4, 6, 1, 18⟩, ⟨4, 6, 0, 20⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_4674 (AllWinning.cons node_3953 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_4887 (AllWinning.cons node_4161 (AllWinning.cons node_3591 (AllWinning.cons node_3047 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.cons node_4896 (AllWinning.cons node_4185 (AllWinning.cons node_3607 (AllWinning.cons node_3068 (AllWinning.cons node_2609 (AllWinning.cons node_2151 (AllWinning.cons node_1746 (AllWinning.cons node_1403 (AllWinning.nil))))))))))))))))))))

theorem node_7300 : Outcome ⟨4, 6, 10, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 10, 2⟩, ⟨2, 6, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨4, 5, 10, 2⟩, ⟨4, 4, 10, 4⟩, ⟨4, 3, 10, 6⟩, ⟨4, 2, 10, 8⟩, ⟨4, 1, 10, 10⟩, ⟨4, 0, 10, 12⟩, ⟨4, 6, 9, 2⟩, ⟨4, 6, 8, 4⟩, ⟨4, 6, 7, 6⟩, ⟨4, 6, 6, 8⟩, ⟨4, 6, 5, 10⟩, ⟨4, 6, 4, 12⟩, ⟨4, 6, 3, 14⟩, ⟨4, 6, 2, 16⟩, ⟨4, 6, 1, 18⟩, ⟨4, 6, 0, 20⟩]
  exact AllWinning.cons node_6310 (AllWinning.cons node_5478 (AllWinning.cons node_4674 (AllWinning.cons node_3953 (AllWinning.cons node_6384 (AllWinning.cons node_5593 (AllWinning.cons node_4887 (AllWinning.cons node_4161 (AllWinning.cons node_3591 (AllWinning.cons node_3047 (AllWinning.cons node_6389 (AllWinning.cons node_5599 (AllWinning.cons node_4896 (AllWinning.cons node_4185 (AllWinning.cons node_3607 (AllWinning.cons node_3068 (AllWinning.cons node_2609 (AllWinning.cons node_2151 (AllWinning.cons node_1746 (AllWinning.cons node_1403 (AllWinning.nil))))))))))))))))))))

end RQ9F1
