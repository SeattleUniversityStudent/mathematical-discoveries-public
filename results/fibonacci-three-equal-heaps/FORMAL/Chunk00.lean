import Model
set_option autoImplicit false
namespace RQ9F1

theorem node_0 : Outcome ⟨0, 0, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_1 : Outcome ⟨0, 0, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_2 : Outcome ⟨0, 0, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_3 : Outcome ⟨0, 0, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_4 : Outcome ⟨0, 0, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_5 : Outcome ⟨0, 0, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_6 : Outcome ⟨0, 0, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_7 : Outcome ⟨0, 0, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_8 : Outcome ⟨0, 0, 0, 18⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_9 : Outcome ⟨0, 0, 0, 20⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_10 : Outcome ⟨0, 0, 0, 22⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_11 : Outcome ⟨0, 0, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_12 : Outcome ⟨0, 0, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_13 : Outcome ⟨0, 0, 0, 28⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_14 : Outcome ⟨0, 0, 0, 32⟩ false := by
  apply Outcome.lose
  change AllWinning []
  exact AllWinning.nil

theorem node_15 : Outcome ⟨0, 0, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_16 : Outcome ⟨0, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_17 : Outcome ⟨0, 0, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_18 : Outcome ⟨0, 0, 1, 24⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_19 : Outcome ⟨0, 1, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_20 : Outcome ⟨0, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_21 : Outcome ⟨0, 1, 0, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_22 : Outcome ⟨0, 1, 0, 24⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_23 : Outcome ⟨1, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_24 : Outcome ⟨1, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_25 : Outcome ⟨1, 0, 0, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_26 : Outcome ⟨1, 0, 0, 24⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 2⟩) (by decide) node_0

theorem node_27 : Outcome ⟨0, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_28 : Outcome ⟨0, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_29 : Outcome ⟨0, 0, 2, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_30 : Outcome ⟨0, 0, 2, 12⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_31 : Outcome ⟨0, 0, 2, 22⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_32 : Outcome ⟨0, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_33 : Outcome ⟨0, 1, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_34 : Outcome ⟨0, 1, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_35 : Outcome ⟨0, 1, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_36 : Outcome ⟨0, 1, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_37 : Outcome ⟨0, 1, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_38 : Outcome ⟨0, 1, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_39 : Outcome ⟨0, 1, 1, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_40 : Outcome ⟨0, 1, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_41 : Outcome ⟨0, 1, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_42 : Outcome ⟨0, 1, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_43 : Outcome ⟨0, 1, 1, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_44 : Outcome ⟨0, 1, 1, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_45 : Outcome ⟨0, 1, 1, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_46 : Outcome ⟨0, 1, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_47 : Outcome ⟨0, 1, 1, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_48 : Outcome ⟨0, 1, 1, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨0, 1, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_19 (AllWinning.nil))

theorem node_49 : Outcome ⟨0, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_50 : Outcome ⟨0, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_51 : Outcome ⟨0, 2, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_52 : Outcome ⟨0, 2, 0, 12⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_53 : Outcome ⟨0, 2, 0, 22⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_54 : Outcome ⟨1, 0, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_55 : Outcome ⟨1, 0, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_56 : Outcome ⟨1, 0, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_57 : Outcome ⟨1, 0, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_58 : Outcome ⟨1, 0, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_59 : Outcome ⟨1, 0, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_60 : Outcome ⟨1, 0, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_61 : Outcome ⟨1, 0, 1, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_62 : Outcome ⟨1, 0, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_63 : Outcome ⟨1, 0, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_64 : Outcome ⟨1, 0, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_65 : Outcome ⟨1, 0, 1, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_66 : Outcome ⟨1, 0, 1, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_67 : Outcome ⟨1, 0, 1, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_68 : Outcome ⟨1, 0, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_69 : Outcome ⟨1, 0, 1, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_70 : Outcome ⟨1, 0, 1, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 1, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_15 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_71 : Outcome ⟨1, 1, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_72 : Outcome ⟨1, 1, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_73 : Outcome ⟨1, 1, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_74 : Outcome ⟨1, 1, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_75 : Outcome ⟨1, 1, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_76 : Outcome ⟨1, 1, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_77 : Outcome ⟨1, 1, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_78 : Outcome ⟨1, 1, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_79 : Outcome ⟨1, 1, 0, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_80 : Outcome ⟨1, 1, 0, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_81 : Outcome ⟨1, 1, 0, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_82 : Outcome ⟨1, 1, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_83 : Outcome ⟨1, 1, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_84 : Outcome ⟨1, 1, 0, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_85 : Outcome ⟨1, 1, 0, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_86 : Outcome ⟨1, 1, 0, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_87 : Outcome ⟨1, 1, 0, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 0, 2⟩, ⟨1, 0, 0, 2⟩]
  exact AllWinning.cons node_19 (AllWinning.cons node_23 (AllWinning.nil))

theorem node_88 : Outcome ⟨2, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_89 : Outcome ⟨2, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_90 : Outcome ⟨2, 0, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_91 : Outcome ⟨2, 0, 0, 12⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_92 : Outcome ⟨2, 0, 0, 22⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 4⟩) (by decide) node_1

theorem node_93 : Outcome ⟨0, 0, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 2, 2⟩, ⟨0, 0, 1, 4⟩]
  exact AllWinning.cons node_27 (AllWinning.cons node_16 (AllWinning.nil))

theorem node_94 : Outcome ⟨0, 0, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_95 : Outcome ⟨0, 0, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_96 : Outcome ⟨0, 0, 3, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_97 : Outcome ⟨0, 0, 3, 20⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_98 : Outcome ⟨0, 1, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_99 : Outcome ⟨0, 1, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_100 : Outcome ⟨0, 1, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_101 : Outcome ⟨0, 1, 2, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_102 : Outcome ⟨0, 2, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_103 : Outcome ⟨0, 2, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_104 : Outcome ⟨0, 2, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_105 : Outcome ⟨0, 2, 1, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_106 : Outcome ⟨0, 3, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 0, 2⟩, ⟨0, 1, 0, 4⟩]
  exact AllWinning.cons node_49 (AllWinning.cons node_20 (AllWinning.nil))

theorem node_107 : Outcome ⟨0, 3, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_108 : Outcome ⟨0, 3, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_109 : Outcome ⟨0, 3, 0, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_110 : Outcome ⟨0, 3, 0, 20⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_111 : Outcome ⟨1, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 2⟩) (by decide) node_54

theorem node_112 : Outcome ⟨1, 0, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 2⟩) (by decide) node_54

theorem node_113 : Outcome ⟨1, 0, 2, 24⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 2⟩) (by decide) node_54

theorem node_114 : Outcome ⟨1, 1, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_115 : Outcome ⟨1, 1, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_116 : Outcome ⟨1, 1, 1, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 2⟩) (by decide) node_32

theorem node_117 : Outcome ⟨1, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 2⟩) (by decide) node_71

theorem node_118 : Outcome ⟨1, 2, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 2⟩) (by decide) node_71

theorem node_119 : Outcome ⟨1, 2, 0, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 2⟩) (by decide) node_71

theorem node_120 : Outcome ⟨2, 0, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 2⟩) (by decide) node_54

theorem node_121 : Outcome ⟨2, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 2⟩) (by decide) node_54

theorem node_122 : Outcome ⟨2, 0, 1, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 2⟩) (by decide) node_54

theorem node_123 : Outcome ⟨2, 0, 1, 24⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 2⟩) (by decide) node_54

theorem node_124 : Outcome ⟨2, 1, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 2⟩) (by decide) node_71

theorem node_125 : Outcome ⟨2, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 2⟩) (by decide) node_71

theorem node_126 : Outcome ⟨2, 1, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 2⟩) (by decide) node_71

theorem node_127 : Outcome ⟨2, 1, 0, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 2⟩) (by decide) node_71

theorem node_128 : Outcome ⟨3, 0, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 0, 0, 2⟩, ⟨1, 0, 0, 4⟩]
  exact AllWinning.cons node_88 (AllWinning.cons node_24 (AllWinning.nil))

theorem node_129 : Outcome ⟨3, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_130 : Outcome ⟨3, 0, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_131 : Outcome ⟨3, 0, 0, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_132 : Outcome ⟨3, 0, 0, 20⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 6⟩) (by decide) node_2

theorem node_133 : Outcome ⟨0, 0, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 3, 2⟩) (by decide) node_93

theorem node_134 : Outcome ⟨0, 0, 4, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 8⟩) (by decide) node_3

theorem node_135 : Outcome ⟨0, 0, 4, 18⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 8⟩) (by decide) node_3

theorem node_136 : Outcome ⟨0, 1, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_137 : Outcome ⟨0, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_138 : Outcome ⟨0, 1, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_139 : Outcome ⟨0, 1, 3, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_140 : Outcome ⟨0, 1, 3, 22⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_141 : Outcome ⟨0, 2, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_142 : Outcome ⟨0, 2, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_143 : Outcome ⟨0, 2, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_144 : Outcome ⟨0, 2, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_145 : Outcome ⟨0, 2, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_146 : Outcome ⟨0, 2, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_147 : Outcome ⟨0, 2, 2, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_148 : Outcome ⟨0, 2, 2, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_149 : Outcome ⟨0, 2, 2, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_150 : Outcome ⟨0, 2, 2, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_151 : Outcome ⟨0, 2, 2, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_152 : Outcome ⟨0, 2, 2, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_153 : Outcome ⟨0, 2, 2, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_154 : Outcome ⟨0, 2, 2, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_155 : Outcome ⟨0, 2, 2, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_156 : Outcome ⟨0, 2, 2, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨0, 2, 1, 2⟩, ⟨0, 2, 0, 4⟩]
  exact AllWinning.cons node_98 (AllWinning.cons node_28 (AllWinning.cons node_102 (AllWinning.cons node_50 (AllWinning.nil))))

theorem node_157 : Outcome ⟨0, 3, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_158 : Outcome ⟨0, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_159 : Outcome ⟨0, 3, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_160 : Outcome ⟨0, 3, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_161 : Outcome ⟨0, 3, 1, 22⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_162 : Outcome ⟨0, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 0, 2⟩) (by decide) node_106

theorem node_163 : Outcome ⟨0, 4, 0, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 8⟩) (by decide) node_3

theorem node_164 : Outcome ⟨0, 4, 0, 18⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 8⟩) (by decide) node_3

theorem node_165 : Outcome ⟨1, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_166 : Outcome ⟨1, 0, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_167 : Outcome ⟨1, 0, 3, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_168 : Outcome ⟨1, 0, 3, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_169 : Outcome ⟨1, 0, 3, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_170 : Outcome ⟨1, 1, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_171 : Outcome ⟨1, 1, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_172 : Outcome ⟨1, 1, 2, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_173 : Outcome ⟨1, 1, 2, 22⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_174 : Outcome ⟨1, 2, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_175 : Outcome ⟨1, 2, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_176 : Outcome ⟨1, 2, 1, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_177 : Outcome ⟨1, 2, 1, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_178 : Outcome ⟨1, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_179 : Outcome ⟨1, 3, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_180 : Outcome ⟨1, 3, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_181 : Outcome ⟨1, 3, 0, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_182 : Outcome ⟨1, 3, 0, 22⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_183 : Outcome ⟨2, 0, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_184 : Outcome ⟨2, 0, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_185 : Outcome ⟨2, 0, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_186 : Outcome ⟨2, 0, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_187 : Outcome ⟨2, 0, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_188 : Outcome ⟨2, 0, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_189 : Outcome ⟨2, 0, 2, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_190 : Outcome ⟨2, 0, 2, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_191 : Outcome ⟨2, 0, 2, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_192 : Outcome ⟨2, 0, 2, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_193 : Outcome ⟨2, 0, 2, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_194 : Outcome ⟨2, 0, 2, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_195 : Outcome ⟨2, 0, 2, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_196 : Outcome ⟨2, 0, 2, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_197 : Outcome ⟨2, 0, 2, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_198 : Outcome ⟨2, 0, 2, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_199 : Outcome ⟨2, 0, 2, 36⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 2, 2⟩, ⟨0, 0, 2, 4⟩, ⟨2, 0, 1, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_111 (AllWinning.cons node_28 (AllWinning.cons node_120 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_200 : Outcome ⟨2, 1, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_201 : Outcome ⟨2, 1, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_202 : Outcome ⟨2, 1, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_203 : Outcome ⟨2, 1, 1, 22⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 4⟩) (by decide) node_33

theorem node_204 : Outcome ⟨2, 2, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_205 : Outcome ⟨2, 2, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_206 : Outcome ⟨2, 2, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_207 : Outcome ⟨2, 2, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_208 : Outcome ⟨2, 2, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_209 : Outcome ⟨2, 2, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_210 : Outcome ⟨2, 2, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_211 : Outcome ⟨2, 2, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_212 : Outcome ⟨2, 2, 0, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_213 : Outcome ⟨2, 2, 0, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_214 : Outcome ⟨2, 2, 0, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_215 : Outcome ⟨2, 2, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_216 : Outcome ⟨2, 2, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_217 : Outcome ⟨2, 2, 0, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_218 : Outcome ⟨2, 2, 0, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_219 : Outcome ⟨2, 2, 0, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_220 : Outcome ⟨2, 2, 0, 36⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 0, 2⟩, ⟨0, 2, 0, 4⟩, ⟨2, 1, 0, 2⟩, ⟨2, 0, 0, 4⟩]
  exact AllWinning.cons node_117 (AllWinning.cons node_50 (AllWinning.cons node_124 (AllWinning.cons node_89 (AllWinning.nil))))

theorem node_221 : Outcome ⟨3, 0, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_222 : Outcome ⟨3, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_223 : Outcome ⟨3, 0, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_224 : Outcome ⟨3, 0, 1, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_225 : Outcome ⟨3, 0, 1, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 4⟩) (by decide) node_55

theorem node_226 : Outcome ⟨3, 1, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_227 : Outcome ⟨3, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_228 : Outcome ⟨3, 1, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_229 : Outcome ⟨3, 1, 0, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_230 : Outcome ⟨3, 1, 0, 22⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 4⟩) (by decide) node_72

theorem node_231 : Outcome ⟨4, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 0, 2⟩) (by decide) node_128

theorem node_232 : Outcome ⟨4, 0, 0, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 8⟩) (by decide) node_3

theorem node_233 : Outcome ⟨4, 0, 0, 18⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 8⟩) (by decide) node_3

theorem node_234 : Outcome ⟨0, 0, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 4, 2⟩, ⟨0, 0, 3, 4⟩]
  exact AllWinning.cons node_133 (AllWinning.cons node_94 (AllWinning.nil))

theorem node_235 : Outcome ⟨0, 0, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 4, 2⟩, ⟨0, 0, 3, 4⟩, ⟨0, 0, 2, 6⟩, ⟨0, 0, 1, 8⟩]
  exact AllWinning.cons node_133 (AllWinning.cons node_94 (AllWinning.cons node_29 (AllWinning.cons node_17 (AllWinning.nil))))

theorem node_236 : Outcome ⟨0, 0, 5, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_237 : Outcome ⟨0, 0, 5, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_238 : Outcome ⟨0, 0, 5, 16⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_239 : Outcome ⟨0, 1, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 4, 2⟩, ⟨0, 1, 3, 2⟩, ⟨0, 1, 2, 4⟩]
  exact AllWinning.cons node_133 (AllWinning.cons node_136 (AllWinning.cons node_99 (AllWinning.nil)))

theorem node_240 : Outcome ⟨0, 1, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_241 : Outcome ⟨0, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_242 : Outcome ⟨0, 1, 4, 10⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_243 : Outcome ⟨0, 1, 4, 20⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_244 : Outcome ⟨0, 2, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_245 : Outcome ⟨0, 2, 3, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_246 : Outcome ⟨0, 2, 3, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_247 : Outcome ⟨0, 2, 3, 24⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_248 : Outcome ⟨0, 3, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_249 : Outcome ⟨0, 3, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_250 : Outcome ⟨0, 3, 2, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_251 : Outcome ⟨0, 3, 2, 24⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_252 : Outcome ⟨0, 4, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 1, 2⟩, ⟨0, 2, 1, 4⟩, ⟨0, 4, 0, 2⟩]
  exact AllWinning.cons node_157 (AllWinning.cons node_103 (AllWinning.cons node_162 (AllWinning.nil)))

theorem node_253 : Outcome ⟨0, 4, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_254 : Outcome ⟨0, 4, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_255 : Outcome ⟨0, 4, 1, 10⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_256 : Outcome ⟨0, 4, 1, 20⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_257 : Outcome ⟨0, 5, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 0, 2⟩, ⟨0, 3, 0, 4⟩]
  exact AllWinning.cons node_162 (AllWinning.cons node_107 (AllWinning.nil))

theorem node_258 : Outcome ⟨0, 5, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 0, 2⟩, ⟨0, 3, 0, 4⟩, ⟨0, 2, 0, 6⟩, ⟨0, 1, 0, 8⟩]
  exact AllWinning.cons node_162 (AllWinning.cons node_107 (AllWinning.cons node_51 (AllWinning.cons node_21 (AllWinning.nil))))

theorem node_259 : Outcome ⟨0, 5, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_260 : Outcome ⟨0, 5, 0, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_261 : Outcome ⟨0, 5, 0, 16⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_262 : Outcome ⟨1, 0, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_263 : Outcome ⟨1, 0, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_264 : Outcome ⟨1, 0, 4, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_265 : Outcome ⟨1, 0, 4, 20⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_266 : Outcome ⟨1, 1, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 3, 2⟩, ⟨1, 0, 3, 2⟩, ⟨1, 1, 2, 2⟩, ⟨1, 1, 1, 4⟩]
  exact AllWinning.cons node_136 (AllWinning.cons node_165 (AllWinning.cons node_170 (AllWinning.cons node_114 (AllWinning.nil))))

theorem node_267 : Outcome ⟨1, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_268 : Outcome ⟨1, 1, 3, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_269 : Outcome ⟨1, 1, 3, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_270 : Outcome ⟨1, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_271 : Outcome ⟨1, 2, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_272 : Outcome ⟨1, 2, 2, 24⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 2⟩) (by decide) node_141

theorem node_273 : Outcome ⟨1, 3, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 1, 2⟩, ⟨1, 2, 1, 2⟩, ⟨1, 1, 1, 4⟩, ⟨1, 3, 0, 2⟩]
  exact AllWinning.cons node_157 (AllWinning.cons node_174 (AllWinning.cons node_114 (AllWinning.cons node_178 (AllWinning.nil))))

theorem node_274 : Outcome ⟨1, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_275 : Outcome ⟨1, 3, 1, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_276 : Outcome ⟨1, 3, 1, 20⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_277 : Outcome ⟨1, 4, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_278 : Outcome ⟨1, 4, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_279 : Outcome ⟨1, 4, 0, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_280 : Outcome ⟨1, 4, 0, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_281 : Outcome ⟨2, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_282 : Outcome ⟨2, 0, 3, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_283 : Outcome ⟨2, 0, 3, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_284 : Outcome ⟨2, 0, 3, 24⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_285 : Outcome ⟨2, 1, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_286 : Outcome ⟨2, 1, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_287 : Outcome ⟨2, 1, 2, 24⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_288 : Outcome ⟨2, 2, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_289 : Outcome ⟨2, 2, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_290 : Outcome ⟨2, 2, 1, 24⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_291 : Outcome ⟨2, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_292 : Outcome ⟨2, 3, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_293 : Outcome ⟨2, 3, 0, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_294 : Outcome ⟨2, 3, 0, 24⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_295 : Outcome ⟨3, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_296 : Outcome ⟨3, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_297 : Outcome ⟨3, 0, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_298 : Outcome ⟨3, 0, 2, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_299 : Outcome ⟨3, 0, 2, 24⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 2⟩) (by decide) node_183

theorem node_300 : Outcome ⟨3, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 1, 2⟩, ⟨1, 1, 1, 4⟩, ⟨3, 0, 1, 2⟩, ⟨3, 1, 0, 2⟩]
  exact AllWinning.cons node_200 (AllWinning.cons node_114 (AllWinning.cons node_221 (AllWinning.cons node_226 (AllWinning.nil))))

theorem node_301 : Outcome ⟨3, 1, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_302 : Outcome ⟨3, 1, 1, 10⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_303 : Outcome ⟨3, 1, 1, 20⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 6⟩) (by decide) node_34

theorem node_304 : Outcome ⟨3, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_305 : Outcome ⟨3, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_306 : Outcome ⟨3, 2, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_307 : Outcome ⟨3, 2, 0, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_308 : Outcome ⟨3, 2, 0, 24⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 2⟩) (by decide) node_204

theorem node_309 : Outcome ⟨4, 0, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 1, 2⟩, ⟨2, 0, 1, 4⟩, ⟨4, 0, 0, 2⟩]
  exact AllWinning.cons node_221 (AllWinning.cons node_121 (AllWinning.cons node_231 (AllWinning.nil)))

theorem node_310 : Outcome ⟨4, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_311 : Outcome ⟨4, 0, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_312 : Outcome ⟨4, 0, 1, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_313 : Outcome ⟨4, 0, 1, 20⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 6⟩) (by decide) node_56

theorem node_314 : Outcome ⟨4, 1, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 0, 2⟩, ⟨2, 1, 0, 4⟩, ⟨4, 0, 0, 2⟩]
  exact AllWinning.cons node_226 (AllWinning.cons node_125 (AllWinning.cons node_231 (AllWinning.nil)))

theorem node_315 : Outcome ⟨4, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_316 : Outcome ⟨4, 1, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_317 : Outcome ⟨4, 1, 0, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_318 : Outcome ⟨4, 1, 0, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 6⟩) (by decide) node_73

theorem node_319 : Outcome ⟨5, 0, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 0, 2⟩, ⟨3, 0, 0, 4⟩]
  exact AllWinning.cons node_231 (AllWinning.cons node_129 (AllWinning.nil))

theorem node_320 : Outcome ⟨5, 0, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 0, 2⟩, ⟨3, 0, 0, 4⟩, ⟨2, 0, 0, 6⟩, ⟨1, 0, 0, 8⟩]
  exact AllWinning.cons node_231 (AllWinning.cons node_129 (AllWinning.cons node_90 (AllWinning.cons node_25 (AllWinning.nil))))

theorem node_321 : Outcome ⟨5, 0, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_322 : Outcome ⟨5, 0, 0, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_323 : Outcome ⟨5, 0, 0, 16⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 10⟩) (by decide) node_4

theorem node_324 : Outcome ⟨0, 0, 6, 1⟩ true :=
  Outcome.win (q := ⟨0, 0, 5, 2⟩) (by decide) node_234

theorem node_325 : Outcome ⟨0, 0, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 5, 2⟩) (by decide) node_234

theorem node_326 : Outcome ⟨0, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 5, 2⟩) (by decide) node_234

theorem node_327 : Outcome ⟨0, 0, 6, 12⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 12⟩) (by decide) node_5

theorem node_328 : Outcome ⟨0, 0, 6, 14⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 12⟩) (by decide) node_5

theorem node_329 : Outcome ⟨0, 1, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 5, 2⟩) (by decide) node_234

theorem node_330 : Outcome ⟨0, 1, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 8⟩) (by decide) node_35

theorem node_331 : Outcome ⟨0, 1, 5, 18⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 8⟩) (by decide) node_35

theorem node_332 : Outcome ⟨0, 2, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 4⟩) (by decide) node_142

theorem node_333 : Outcome ⟨0, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 4⟩) (by decide) node_142

theorem node_334 : Outcome ⟨0, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 4⟩) (by decide) node_142

theorem node_335 : Outcome ⟨0, 2, 4, 12⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 4⟩) (by decide) node_142

theorem node_336 : Outcome ⟨0, 2, 4, 22⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 4⟩) (by decide) node_142

theorem node_337 : Outcome ⟨0, 3, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 3, 2⟩, ⟨0, 1, 3, 4⟩, ⟨0, 3, 2, 2⟩, ⟨0, 3, 1, 4⟩]
  exact AllWinning.cons node_244 (AllWinning.cons node_137 (AllWinning.cons node_248 (AllWinning.cons node_158 (AllWinning.nil))))

theorem node_338 : Outcome ⟨0, 3, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 3, 2⟩, ⟨0, 1, 3, 4⟩, ⟨0, 0, 3, 6⟩, ⟨0, 3, 2, 2⟩, ⟨0, 3, 1, 4⟩, ⟨0, 3, 0, 6⟩]
  exact AllWinning.cons node_244 (AllWinning.cons node_137 (AllWinning.cons node_95 (AllWinning.cons node_248 (AllWinning.cons node_158 (AllWinning.cons node_108 (AllWinning.nil))))))

end RQ9F1
