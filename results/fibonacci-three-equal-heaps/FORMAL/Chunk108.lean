import Chunk107
set_option autoImplicit false
namespace RQ9F1

theorem node_22683 : Outcome ⟨12, 16, 9, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 9, 4⟩) (by decide) node_21446

theorem node_22684 : Outcome ⟨12, 16, 9, 6⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 6⟩) (by decide) node_20866

theorem node_22685 : Outcome ⟨12, 16, 9, 12⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 16⟩) (by decide) node_16131

theorem node_22686 : Outcome ⟨12, 17, 8, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 8, 2⟩) (by decide) node_22076

theorem node_22687 : Outcome ⟨12, 17, 8, 10⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 16⟩) (by decide) node_16139

theorem node_22688 : Outcome ⟨12, 18, 7, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 4⟩) (by decide) node_21527

theorem node_22689 : Outcome ⟨12, 18, 7, 6⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 6⟩) (by decide) node_20861

theorem node_22690 : Outcome ⟨12, 19, 6, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 6, 2⟩) (by decide) node_22080

theorem node_22691 : Outcome ⟨12, 19, 6, 12⟩ true :=
  Outcome.win (q := ⟨7, 19, 6, 10⟩) (by decide) node_19094

theorem node_22692 : Outcome ⟨12, 20, 5, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 4⟩) (by decide) node_21527

theorem node_22693 : Outcome ⟨13, 4, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 4, 20, 2⟩, ⟨11, 4, 20, 4⟩, ⟨13, 3, 20, 2⟩, ⟨13, 2, 20, 4⟩, ⟨13, 4, 19, 2⟩, ⟨13, 4, 18, 4⟩]
  exact AllWinning.cons node_22084 (AllWinning.cons node_21452 (AllWinning.cons node_22131 (AllWinning.cons node_21536 (AllWinning.cons node_22132 (AllWinning.cons node_21540 (AllWinning.nil))))))

theorem node_22694 : Outcome ⟨13, 4, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 4, 20, 2⟩, ⟨11, 4, 20, 4⟩, ⟨10, 4, 20, 6⟩, ⟨9, 4, 20, 8⟩, ⟨13, 3, 20, 2⟩, ⟨13, 2, 20, 4⟩, ⟨13, 1, 20, 6⟩, ⟨13, 0, 20, 8⟩, ⟨13, 4, 19, 2⟩, ⟨13, 4, 18, 4⟩, ⟨13, 4, 17, 6⟩, ⟨13, 4, 16, 8⟩]
  exact AllWinning.cons node_22084 (AllWinning.cons node_21452 (AllWinning.cons node_20730 (AllWinning.cons node_19949 (AllWinning.cons node_22131 (AllWinning.cons node_21536 (AllWinning.cons node_20879 (AllWinning.cons node_20127 (AllWinning.cons node_22132 (AllWinning.cons node_21540 (AllWinning.cons node_20887 (AllWinning.cons node_20136 (AllWinning.nil))))))))))))

theorem node_22695 : Outcome ⟨13, 4, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 4, 20, 2⟩, ⟨11, 4, 20, 4⟩, ⟨10, 4, 20, 6⟩, ⟨9, 4, 20, 8⟩, ⟨8, 4, 20, 10⟩, ⟨7, 4, 20, 12⟩, ⟨13, 3, 20, 2⟩, ⟨13, 2, 20, 4⟩, ⟨13, 1, 20, 6⟩, ⟨13, 0, 20, 8⟩, ⟨13, 4, 19, 2⟩, ⟨13, 4, 18, 4⟩, ⟨13, 4, 17, 6⟩, ⟨13, 4, 16, 8⟩, ⟨13, 4, 15, 10⟩, ⟨13, 4, 14, 12⟩]
  exact AllWinning.cons node_22084 (AllWinning.cons node_21452 (AllWinning.cons node_20730 (AllWinning.cons node_19949 (AllWinning.cons node_19101 (AllWinning.cons node_18136 (AllWinning.cons node_22131 (AllWinning.cons node_21536 (AllWinning.cons node_20879 (AllWinning.cons node_20127 (AllWinning.cons node_22132 (AllWinning.cons node_21540 (AllWinning.cons node_20887 (AllWinning.cons node_20136 (AllWinning.cons node_19366 (AllWinning.cons node_18496 (AllWinning.nil))))))))))))))))

theorem node_22696 : Outcome ⟨13, 5, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 19, 2⟩, ⟨11, 5, 19, 4⟩, ⟨13, 4, 19, 2⟩, ⟨13, 3, 19, 4⟩, ⟨13, 5, 18, 2⟩, ⟨13, 5, 17, 4⟩]
  exact AllWinning.cons node_22086 (AllWinning.cons node_21455 (AllWinning.cons node_22132 (AllWinning.cons node_21537 (AllWinning.cons node_22134 (AllWinning.cons node_21543 (AllWinning.nil))))))

theorem node_22697 : Outcome ⟨13, 5, 19, 4⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 6⟩) (by decide) node_20733

theorem node_22698 : Outcome ⟨13, 5, 19, 6⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 6⟩) (by decide) node_20733

theorem node_22699 : Outcome ⟨13, 6, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 6, 17, 2⟩) (by decide) node_22136

theorem node_22700 : Outcome ⟨13, 7, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 6, 17, 2⟩) (by decide) node_22136

theorem node_22701 : Outcome ⟨13, 7, 17, 4⟩ true :=
  Outcome.win (q := ⟨13, 6, 17, 2⟩) (by decide) node_22136

theorem node_22702 : Outcome ⟨13, 7, 17, 10⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 16⟩) (by decide) node_16693

theorem node_22703 : Outcome ⟨13, 8, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 8, 16, 2⟩, ⟨11, 8, 16, 4⟩, ⟨13, 7, 16, 2⟩, ⟨13, 6, 16, 4⟩, ⟨13, 8, 15, 2⟩, ⟨13, 8, 14, 4⟩]
  exact AllWinning.cons node_22094 (AllWinning.cons node_21460 (AllWinning.cons node_22139 (AllWinning.cons node_21546 (AllWinning.cons node_22142 (AllWinning.cons node_21551 (AllWinning.nil))))))

theorem node_22704 : Outcome ⟨13, 8, 16, 6⟩ true :=
  Outcome.win (q := ⟨13, 8, 13, 6⟩) (by decide) node_20895

theorem node_22705 : Outcome ⟨13, 8, 16, 16⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 20⟩) (by decide) node_14117

theorem node_22706 : Outcome ⟨13, 9, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 9, 15, 2⟩, ⟨11, 9, 15, 4⟩, ⟨13, 8, 15, 2⟩, ⟨13, 7, 15, 4⟩, ⟨13, 9, 14, 2⟩, ⟨13, 9, 13, 4⟩]
  exact AllWinning.cons node_22098 (AllWinning.cons node_21463 (AllWinning.cons node_22142 (AllWinning.cons node_21548 (AllWinning.cons node_22145 (AllWinning.cons node_21554 (AllWinning.nil))))))

theorem node_22707 : Outcome ⟨13, 9, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 9, 15, 2⟩, ⟨11, 9, 15, 4⟩, ⟨10, 9, 15, 6⟩, ⟨9, 9, 15, 8⟩, ⟨13, 8, 15, 2⟩, ⟨13, 7, 15, 4⟩, ⟨13, 6, 15, 6⟩, ⟨13, 5, 15, 8⟩, ⟨13, 9, 14, 2⟩, ⟨13, 9, 13, 4⟩, ⟨13, 9, 12, 6⟩, ⟨13, 9, 11, 8⟩]
  exact AllWinning.cons node_22098 (AllWinning.cons node_21463 (AllWinning.cons node_20750 (AllWinning.cons node_19958 (AllWinning.cons node_22142 (AllWinning.cons node_21548 (AllWinning.cons node_20890 (AllWinning.cons node_20138 (AllWinning.cons node_22145 (AllWinning.cons node_21554 (AllWinning.cons node_20900 (AllWinning.cons node_20152 (AllWinning.nil))))))))))))

theorem node_22708 : Outcome ⟨13, 9, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 9, 15, 2⟩, ⟨11, 9, 15, 4⟩, ⟨10, 9, 15, 6⟩, ⟨9, 9, 15, 8⟩, ⟨8, 9, 15, 10⟩, ⟨7, 9, 15, 12⟩, ⟨13, 8, 15, 2⟩, ⟨13, 7, 15, 4⟩, ⟨13, 6, 15, 6⟩, ⟨13, 5, 15, 8⟩, ⟨13, 4, 15, 10⟩, ⟨13, 3, 15, 12⟩, ⟨13, 9, 14, 2⟩, ⟨13, 9, 13, 4⟩, ⟨13, 9, 12, 6⟩, ⟨13, 9, 11, 8⟩, ⟨13, 9, 10, 10⟩, ⟨13, 9, 9, 12⟩]
  exact AllWinning.cons node_22098 (AllWinning.cons node_21463 (AllWinning.cons node_20750 (AllWinning.cons node_19958 (AllWinning.cons node_19111 (AllWinning.cons node_18151 (AllWinning.cons node_22142 (AllWinning.cons node_21548 (AllWinning.cons node_20890 (AllWinning.cons node_20138 (AllWinning.cons node_19366 (AllWinning.cons node_18492 (AllWinning.cons node_22145 (AllWinning.cons node_21554 (AllWinning.cons node_20900 (AllWinning.cons node_20152 (AllWinning.cons node_19380 (AllWinning.cons node_18511 (AllWinning.nil))))))))))))))))))

theorem node_22709 : Outcome ⟨13, 9, 15, 10⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 16⟩) (by decide) node_16704

theorem node_22710 : Outcome ⟨13, 10, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 10, 14, 2⟩, ⟨11, 10, 14, 4⟩, ⟨13, 9, 14, 2⟩, ⟨13, 8, 14, 4⟩, ⟨13, 10, 13, 2⟩, ⟨13, 10, 12, 4⟩]
  exact AllWinning.cons node_22101 (AllWinning.cons node_21465 (AllWinning.cons node_22145 (AllWinning.cons node_21551 (AllWinning.cons node_22147 (AllWinning.cons node_21556 (AllWinning.nil))))))

theorem node_22711 : Outcome ⟨13, 10, 14, 6⟩ true :=
  Outcome.win (q := ⟨13, 6, 14, 8⟩) (by decide) node_20141

theorem node_22712 : Outcome ⟨13, 10, 14, 10⟩ true :=
  Outcome.win (q := ⟨13, 6, 14, 8⟩) (by decide) node_20141

theorem node_22713 : Outcome ⟨13, 11, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 11, 13, 2⟩, ⟨11, 11, 13, 4⟩, ⟨13, 10, 13, 2⟩, ⟨13, 9, 13, 4⟩, ⟨13, 11, 12, 2⟩, ⟨13, 11, 11, 4⟩]
  exact AllWinning.cons node_22104 (AllWinning.cons node_21468 (AllWinning.cons node_22147 (AllWinning.cons node_21554 (AllWinning.cons node_22149 (AllWinning.cons node_21558 (AllWinning.nil))))))

theorem node_22714 : Outcome ⟨13, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 8, 13, 6⟩) (by decide) node_20895

theorem node_22715 : Outcome ⟨13, 11, 13, 6⟩ true :=
  Outcome.win (q := ⟨13, 8, 13, 6⟩) (by decide) node_20895

theorem node_22716 : Outcome ⟨13, 12, 12, 2⟩ true :=
  Outcome.win (q := ⟨11, 12, 12, 4⟩) (by decide) node_21471

theorem node_22717 : Outcome ⟨13, 12, 12, 6⟩ true :=
  Outcome.win (q := ⟨11, 12, 12, 4⟩) (by decide) node_21471

theorem node_22718 : Outcome ⟨13, 12, 12, 10⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 16⟩) (by decide) node_16679

theorem node_22719 : Outcome ⟨13, 13, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 11, 2⟩, ⟨11, 13, 11, 4⟩, ⟨13, 12, 11, 2⟩, ⟨13, 11, 11, 4⟩, ⟨13, 13, 10, 2⟩, ⟨13, 13, 9, 4⟩]
  exact AllWinning.cons node_22110 (AllWinning.cons node_21474 (AllWinning.cons node_22153 (AllWinning.cons node_21558 (AllWinning.cons node_22157 (AllWinning.cons node_21560 (AllWinning.nil))))))

theorem node_22720 : Outcome ⟨13, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 8, 6⟩) (by decide) node_20911

theorem node_22721 : Outcome ⟨13, 13, 11, 6⟩ true :=
  Outcome.win (q := ⟨13, 13, 8, 6⟩) (by decide) node_20911

theorem node_22722 : Outcome ⟨13, 14, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 14, 10, 2⟩, ⟨11, 14, 10, 4⟩, ⟨13, 13, 10, 2⟩, ⟨13, 12, 10, 4⟩, ⟨13, 14, 9, 2⟩, ⟨13, 14, 8, 4⟩]
  exact AllWinning.cons node_22113 (AllWinning.cons node_21477 (AllWinning.cons node_22157 (AllWinning.cons node_21559 (AllWinning.cons node_22159 (AllWinning.cons node_21562 (AllWinning.nil))))))

theorem node_22723 : Outcome ⟨13, 14, 10, 6⟩ true :=
  Outcome.win (q := ⟨13, 14, 6, 8⟩) (by decide) node_20167

theorem node_22724 : Outcome ⟨13, 14, 10, 10⟩ true :=
  Outcome.win (q := ⟨13, 14, 6, 8⟩) (by decide) node_20167

theorem node_22725 : Outcome ⟨13, 15, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 9, 2⟩, ⟨11, 15, 9, 4⟩, ⟨13, 14, 9, 2⟩, ⟨13, 13, 9, 4⟩, ⟨13, 15, 8, 2⟩, ⟨13, 15, 7, 4⟩]
  exact AllWinning.cons node_22116 (AllWinning.cons node_21480 (AllWinning.cons node_22159 (AllWinning.cons node_21560 (AllWinning.cons node_22161 (AllWinning.cons node_21565 (AllWinning.nil))))))

theorem node_22726 : Outcome ⟨13, 15, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 9, 2⟩, ⟨11, 15, 9, 4⟩, ⟨10, 15, 9, 6⟩, ⟨9, 15, 9, 8⟩, ⟨13, 14, 9, 2⟩, ⟨13, 13, 9, 4⟩, ⟨13, 12, 9, 6⟩, ⟨13, 11, 9, 8⟩, ⟨13, 15, 8, 2⟩, ⟨13, 15, 7, 4⟩, ⟨13, 15, 6, 6⟩, ⟨13, 15, 5, 8⟩]
  exact AllWinning.cons node_22116 (AllWinning.cons node_21480 (AllWinning.cons node_20763 (AllWinning.cons node_19979 (AllWinning.cons node_22159 (AllWinning.cons node_21560 (AllWinning.cons node_20908 (AllWinning.cons node_20159 (AllWinning.cons node_22161 (AllWinning.cons node_21565 (AllWinning.cons node_20917 (AllWinning.cons node_20172 (AllWinning.nil))))))))))))

theorem node_22727 : Outcome ⟨13, 15, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 9, 2⟩, ⟨11, 15, 9, 4⟩, ⟨10, 15, 9, 6⟩, ⟨9, 15, 9, 8⟩, ⟨8, 15, 9, 10⟩, ⟨7, 15, 9, 12⟩, ⟨13, 14, 9, 2⟩, ⟨13, 13, 9, 4⟩, ⟨13, 12, 9, 6⟩, ⟨13, 11, 9, 8⟩, ⟨13, 10, 9, 10⟩, ⟨13, 9, 9, 12⟩, ⟨13, 15, 8, 2⟩, ⟨13, 15, 7, 4⟩, ⟨13, 15, 6, 6⟩, ⟨13, 15, 5, 8⟩, ⟨13, 15, 4, 10⟩, ⟨13, 15, 3, 12⟩]
  exact AllWinning.cons node_22116 (AllWinning.cons node_21480 (AllWinning.cons node_20763 (AllWinning.cons node_19979 (AllWinning.cons node_19131 (AllWinning.cons node_18172 (AllWinning.cons node_22159 (AllWinning.cons node_21560 (AllWinning.cons node_20908 (AllWinning.cons node_20159 (AllWinning.cons node_19384 (AllWinning.cons node_18511 (AllWinning.cons node_22161 (AllWinning.cons node_21565 (AllWinning.cons node_20917 (AllWinning.cons node_20172 (AllWinning.cons node_19398 (AllWinning.cons node_18531 (AllWinning.nil))))))))))))))))))

theorem node_22728 : Outcome ⟨13, 15, 9, 10⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 16⟩) (by decide) node_16693

theorem node_22729 : Outcome ⟨13, 16, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 8, 2⟩, ⟨11, 16, 8, 4⟩, ⟨13, 15, 8, 2⟩, ⟨13, 14, 8, 4⟩, ⟨13, 16, 7, 2⟩, ⟨13, 16, 6, 4⟩]
  exact AllWinning.cons node_22119 (AllWinning.cons node_21482 (AllWinning.cons node_22161 (AllWinning.cons node_21562 (AllWinning.cons node_22164 (AllWinning.cons node_21569 (AllWinning.nil))))))

theorem node_22730 : Outcome ⟨13, 16, 8, 6⟩ true :=
  Outcome.win (q := ⟨13, 13, 8, 6⟩) (by decide) node_20911

theorem node_22731 : Outcome ⟨13, 16, 8, 16⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 20⟩) (by decide) node_14150

theorem node_22732 : Outcome ⟨13, 17, 7, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 6, 2⟩) (by decide) node_22167

theorem node_22733 : Outcome ⟨13, 17, 7, 4⟩ true :=
  Outcome.win (q := ⟨13, 17, 6, 2⟩) (by decide) node_22167

theorem node_22734 : Outcome ⟨13, 17, 7, 10⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 16⟩) (by decide) node_16704

theorem node_22735 : Outcome ⟨13, 18, 6, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 6, 2⟩) (by decide) node_22167

theorem node_22736 : Outcome ⟨13, 19, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 19, 5, 2⟩, ⟨11, 19, 5, 4⟩, ⟨13, 18, 5, 2⟩, ⟨13, 17, 5, 4⟩, ⟨13, 19, 4, 2⟩, ⟨13, 19, 3, 4⟩]
  exact AllWinning.cons node_22127 (AllWinning.cons node_21487 (AllWinning.cons node_22170 (AllWinning.cons node_21572 (AllWinning.cons node_22172 (AllWinning.cons node_21576 (AllWinning.nil))))))

theorem node_22737 : Outcome ⟨13, 19, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 6⟩) (by decide) node_20776

theorem node_22738 : Outcome ⟨13, 19, 5, 6⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 6⟩) (by decide) node_20776

theorem node_22739 : Outcome ⟨13, 20, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 20, 4, 2⟩, ⟨11, 20, 4, 4⟩, ⟨10, 20, 4, 6⟩, ⟨9, 20, 4, 8⟩, ⟨13, 19, 4, 2⟩, ⟨13, 18, 4, 4⟩, ⟨13, 17, 4, 6⟩, ⟨13, 16, 4, 8⟩, ⟨13, 20, 3, 2⟩, ⟨13, 20, 2, 4⟩, ⟨13, 20, 1, 6⟩, ⟨13, 20, 0, 8⟩]
  exact AllWinning.cons node_22130 (AllWinning.cons node_21488 (AllWinning.cons node_20781 (AllWinning.cons node_19986 (AllWinning.cons node_22172 (AllWinning.cons node_21574 (AllWinning.cons node_20922 (AllWinning.cons node_20174 (AllWinning.cons node_22174 (AllWinning.cons node_21580 (AllWinning.cons node_20929 (AllWinning.cons node_20182 (AllWinning.nil))))))))))))

theorem node_22740 : Outcome ⟨13, 20, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 20, 4, 2⟩, ⟨11, 20, 4, 4⟩, ⟨10, 20, 4, 6⟩, ⟨9, 20, 4, 8⟩, ⟨8, 20, 4, 10⟩, ⟨7, 20, 4, 12⟩, ⟨13, 19, 4, 2⟩, ⟨13, 18, 4, 4⟩, ⟨13, 17, 4, 6⟩, ⟨13, 16, 4, 8⟩, ⟨13, 15, 4, 10⟩, ⟨13, 14, 4, 12⟩, ⟨13, 20, 3, 2⟩, ⟨13, 20, 2, 4⟩, ⟨13, 20, 1, 6⟩, ⟨13, 20, 0, 8⟩]
  exact AllWinning.cons node_22130 (AllWinning.cons node_21488 (AllWinning.cons node_20781 (AllWinning.cons node_19986 (AllWinning.cons node_19142 (AllWinning.cons node_18187 (AllWinning.cons node_22172 (AllWinning.cons node_21574 (AllWinning.cons node_20922 (AllWinning.cons node_20174 (AllWinning.cons node_19398 (AllWinning.cons node_18527 (AllWinning.cons node_22174 (AllWinning.cons node_21580 (AllWinning.cons node_20929 (AllWinning.cons node_20182 (AllWinning.nil))))))))))))))))

theorem node_22741 : Outcome ⟨14, 3, 20, 4⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 6⟩) (by decide) node_20937

theorem node_22742 : Outcome ⟨14, 4, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 4, 19, 2⟩, ⟨12, 4, 19, 4⟩, ⟨11, 4, 19, 6⟩, ⟨10, 4, 19, 8⟩, ⟨14, 3, 19, 2⟩, ⟨14, 2, 19, 4⟩, ⟨14, 1, 19, 6⟩, ⟨14, 0, 19, 8⟩, ⟨14, 4, 18, 2⟩, ⟨14, 4, 17, 4⟩, ⟨14, 4, 16, 6⟩, ⟨14, 4, 15, 8⟩]
  exact AllWinning.cons node_22132 (AllWinning.cons node_21493 (AllWinning.cons node_20785 (AllWinning.cons node_19991 (AllWinning.cons node_22176 (AllWinning.cons node_21583 (AllWinning.cons node_20932 (AllWinning.cons node_20185 (AllWinning.cons node_22178 (AllWinning.cons node_21587 (AllWinning.cons node_20944 (AllWinning.cons node_20195 (AllWinning.nil))))))))))))

theorem node_22743 : Outcome ⟨14, 4, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 4, 19, 2⟩, ⟨12, 4, 19, 4⟩, ⟨11, 4, 19, 6⟩, ⟨10, 4, 19, 8⟩, ⟨9, 4, 19, 10⟩, ⟨8, 4, 19, 12⟩, ⟨14, 3, 19, 2⟩, ⟨14, 2, 19, 4⟩, ⟨14, 1, 19, 6⟩, ⟨14, 0, 19, 8⟩, ⟨14, 4, 18, 2⟩, ⟨14, 4, 17, 4⟩, ⟨14, 4, 16, 6⟩, ⟨14, 4, 15, 8⟩, ⟨14, 4, 14, 10⟩, ⟨14, 4, 13, 12⟩]
  exact AllWinning.cons node_22132 (AllWinning.cons node_21493 (AllWinning.cons node_20785 (AllWinning.cons node_19991 (AllWinning.cons node_19147 (AllWinning.cons node_18192 (AllWinning.cons node_22176 (AllWinning.cons node_21583 (AllWinning.cons node_20932 (AllWinning.cons node_20185 (AllWinning.cons node_22178 (AllWinning.cons node_21587 (AllWinning.cons node_20944 (AllWinning.cons node_20195 (AllWinning.cons node_19421 (AllWinning.cons node_18559 (AllWinning.nil))))))))))))))))

theorem node_22744 : Outcome ⟨14, 4, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 4, 19, 2⟩, ⟨12, 4, 19, 4⟩, ⟨11, 4, 19, 6⟩, ⟨10, 4, 19, 8⟩, ⟨9, 4, 19, 10⟩, ⟨8, 4, 19, 12⟩, ⟨7, 4, 19, 14⟩, ⟨6, 4, 19, 16⟩, ⟨5, 4, 19, 18⟩, ⟨4, 4, 19, 20⟩, ⟨14, 3, 19, 2⟩, ⟨14, 2, 19, 4⟩, ⟨14, 1, 19, 6⟩, ⟨14, 0, 19, 8⟩, ⟨14, 4, 18, 2⟩, ⟨14, 4, 17, 4⟩, ⟨14, 4, 16, 6⟩, ⟨14, 4, 15, 8⟩, ⟨14, 4, 14, 10⟩, ⟨14, 4, 13, 12⟩, ⟨14, 4, 12, 14⟩, ⟨14, 4, 11, 16⟩, ⟨14, 4, 10, 18⟩, ⟨14, 4, 9, 20⟩]
  exact AllWinning.cons node_22132 (AllWinning.cons node_21493 (AllWinning.cons node_20785 (AllWinning.cons node_19991 (AllWinning.cons node_19147 (AllWinning.cons node_18192 (AllWinning.cons node_17252 (AllWinning.cons node_16203 (AllWinning.cons node_15154 (AllWinning.cons node_14165 (AllWinning.cons node_22176 (AllWinning.cons node_21583 (AllWinning.cons node_20932 (AllWinning.cons node_20185 (AllWinning.cons node_22178 (AllWinning.cons node_21587 (AllWinning.cons node_20944 (AllWinning.cons node_20195 (AllWinning.cons node_19421 (AllWinning.cons node_18559 (AllWinning.cons node_17649 (AllWinning.cons node_16742 (AllWinning.cons node_15688 (AllWinning.cons node_14723 (AllWinning.nil))))))))))))))))))))))))

theorem node_22745 : Outcome ⟨14, 4, 19, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 4, 19, 2⟩, ⟨12, 4, 19, 4⟩, ⟨11, 4, 19, 6⟩, ⟨10, 4, 19, 8⟩, ⟨9, 4, 19, 10⟩, ⟨8, 4, 19, 12⟩, ⟨7, 4, 19, 14⟩, ⟨6, 4, 19, 16⟩, ⟨5, 4, 19, 18⟩, ⟨4, 4, 19, 20⟩, ⟨3, 4, 19, 22⟩, ⟨2, 4, 19, 24⟩, ⟨1, 4, 19, 26⟩, ⟨0, 4, 19, 28⟩, ⟨14, 3, 19, 2⟩, ⟨14, 2, 19, 4⟩, ⟨14, 1, 19, 6⟩, ⟨14, 0, 19, 8⟩, ⟨14, 4, 18, 2⟩, ⟨14, 4, 17, 4⟩, ⟨14, 4, 16, 6⟩, ⟨14, 4, 15, 8⟩, ⟨14, 4, 14, 10⟩, ⟨14, 4, 13, 12⟩, ⟨14, 4, 12, 14⟩, ⟨14, 4, 11, 16⟩, ⟨14, 4, 10, 18⟩, ⟨14, 4, 9, 20⟩, ⟨14, 4, 8, 22⟩, ⟨14, 4, 7, 24⟩, ⟨14, 4, 6, 26⟩, ⟨14, 4, 5, 28⟩, ⟨14, 4, 4, 30⟩, ⟨14, 4, 3, 32⟩, ⟨14, 4, 2, 34⟩, ⟨14, 4, 1, 36⟩]
  exact AllWinning.cons node_22132 (AllWinning.cons node_21493 (AllWinning.cons node_20785 (AllWinning.cons node_19991 (AllWinning.cons node_19147 (AllWinning.cons node_18192 (AllWinning.cons node_17252 (AllWinning.cons node_16203 (AllWinning.cons node_15154 (AllWinning.cons node_14165 (AllWinning.cons node_13133 (AllWinning.cons node_12091 (AllWinning.cons node_11036 (AllWinning.cons node_9874 (AllWinning.cons node_22176 (AllWinning.cons node_21583 (AllWinning.cons node_20932 (AllWinning.cons node_20185 (AllWinning.cons node_22178 (AllWinning.cons node_21587 (AllWinning.cons node_20944 (AllWinning.cons node_20195 (AllWinning.cons node_19421 (AllWinning.cons node_18559 (AllWinning.cons node_17649 (AllWinning.cons node_16742 (AllWinning.cons node_15688 (AllWinning.cons node_14723 (AllWinning.cons node_13779 (AllWinning.cons node_12794 (AllWinning.cons node_11820 (AllWinning.cons node_10813 (AllWinning.cons node_9753 (AllWinning.cons node_8812 (AllWinning.cons node_7815 (AllWinning.cons node_6885 (AllWinning.nil))))))))))))))))))))))))))))))))))))

theorem node_22746 : Outcome ⟨14, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 4⟩) (by decide) node_21496

theorem node_22747 : Outcome ⟨14, 5, 18, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 4⟩) (by decide) node_21496

theorem node_22748 : Outcome ⟨14, 5, 18, 14⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 4⟩) (by decide) node_21496

theorem node_22749 : Outcome ⟨14, 6, 17, 4⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 8⟩) (by decide) node_20202

theorem node_22750 : Outcome ⟨14, 6, 17, 10⟩ true :=
  Outcome.win (q := ⟨9, 6, 17, 10⟩) (by decide) node_19154

theorem node_22751 : Outcome ⟨14, 7, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 7, 16, 2⟩, ⟨12, 7, 16, 4⟩, ⟨14, 6, 16, 2⟩, ⟨14, 5, 16, 4⟩, ⟨14, 7, 15, 2⟩, ⟨14, 7, 14, 4⟩]
  exact AllWinning.cons node_22139 (AllWinning.cons node_21503 (AllWinning.cons node_22182 (AllWinning.cons node_21588 (AllWinning.cons node_22185 (AllWinning.cons node_21591 (AllWinning.nil))))))

theorem node_22752 : Outcome ⟨14, 7, 16, 6⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 6⟩) (by decide) node_20790

theorem node_22753 : Outcome ⟨14, 8, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 8, 15, 2⟩, ⟨12, 8, 15, 4⟩, ⟨14, 7, 15, 2⟩, ⟨14, 6, 15, 4⟩, ⟨14, 8, 14, 2⟩, ⟨14, 8, 13, 4⟩]
  exact AllWinning.cons node_22142 (AllWinning.cons node_21505 (AllWinning.cons node_22185 (AllWinning.cons node_21590 (AllWinning.cons node_22187 (AllWinning.cons node_21593 (AllWinning.nil))))))

theorem node_22754 : Outcome ⟨14, 8, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 8, 15, 2⟩, ⟨12, 8, 15, 4⟩, ⟨11, 8, 15, 6⟩, ⟨10, 8, 15, 8⟩, ⟨14, 7, 15, 2⟩, ⟨14, 6, 15, 4⟩, ⟨14, 5, 15, 6⟩, ⟨14, 4, 15, 8⟩, ⟨14, 8, 14, 2⟩, ⟨14, 8, 13, 4⟩, ⟨14, 8, 12, 6⟩, ⟨14, 8, 11, 8⟩]
  exact AllWinning.cons node_22142 (AllWinning.cons node_21505 (AllWinning.cons node_20795 (AllWinning.cons node_20000 (AllWinning.cons node_22185 (AllWinning.cons node_21590 (AllWinning.cons node_20947 (AllWinning.cons node_20195 (AllWinning.cons node_22187 (AllWinning.cons node_21593 (AllWinning.cons node_20953 (AllWinning.cons node_20209 (AllWinning.nil))))))))))))

theorem node_22755 : Outcome ⟨14, 8, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 8, 15, 2⟩, ⟨12, 8, 15, 4⟩, ⟨11, 8, 15, 6⟩, ⟨10, 8, 15, 8⟩, ⟨9, 8, 15, 10⟩, ⟨8, 8, 15, 12⟩, ⟨14, 7, 15, 2⟩, ⟨14, 6, 15, 4⟩, ⟨14, 5, 15, 6⟩, ⟨14, 4, 15, 8⟩, ⟨14, 3, 15, 10⟩, ⟨14, 2, 15, 12⟩, ⟨14, 8, 14, 2⟩, ⟨14, 8, 13, 4⟩, ⟨14, 8, 12, 6⟩, ⟨14, 8, 11, 8⟩, ⟨14, 8, 10, 10⟩, ⟨14, 8, 9, 12⟩]
  exact AllWinning.cons node_22142 (AllWinning.cons node_21505 (AllWinning.cons node_20795 (AllWinning.cons node_20000 (AllWinning.cons node_19160 (AllWinning.cons node_18204 (AllWinning.cons node_22185 (AllWinning.cons node_21590 (AllWinning.cons node_20947 (AllWinning.cons node_20195 (AllWinning.cons node_19418 (AllWinning.cons node_18550 (AllWinning.cons node_22187 (AllWinning.cons node_21593 (AllWinning.cons node_20953 (AllWinning.cons node_20209 (AllWinning.cons node_19429 (AllWinning.cons node_18571 (AllWinning.nil))))))))))))))))))

theorem node_22756 : Outcome ⟨14, 8, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 8, 15, 2⟩, ⟨12, 8, 15, 4⟩, ⟨11, 8, 15, 6⟩, ⟨10, 8, 15, 8⟩, ⟨9, 8, 15, 10⟩, ⟨8, 8, 15, 12⟩, ⟨7, 8, 15, 14⟩, ⟨6, 8, 15, 16⟩, ⟨14, 7, 15, 2⟩, ⟨14, 6, 15, 4⟩, ⟨14, 5, 15, 6⟩, ⟨14, 4, 15, 8⟩, ⟨14, 3, 15, 10⟩, ⟨14, 2, 15, 12⟩, ⟨14, 1, 15, 14⟩, ⟨14, 0, 15, 16⟩, ⟨14, 8, 14, 2⟩, ⟨14, 8, 13, 4⟩, ⟨14, 8, 12, 6⟩, ⟨14, 8, 11, 8⟩, ⟨14, 8, 10, 10⟩, ⟨14, 8, 9, 12⟩, ⟨14, 8, 8, 14⟩, ⟨14, 8, 7, 16⟩]
  exact AllWinning.cons node_22142 (AllWinning.cons node_21505 (AllWinning.cons node_20795 (AllWinning.cons node_20000 (AllWinning.cons node_19160 (AllWinning.cons node_18204 (AllWinning.cons node_17265 (AllWinning.cons node_16216 (AllWinning.cons node_22185 (AllWinning.cons node_21590 (AllWinning.cons node_20947 (AllWinning.cons node_20195 (AllWinning.cons node_19418 (AllWinning.cons node_18550 (AllWinning.cons node_17636 (AllWinning.cons node_16730 (AllWinning.cons node_22187 (AllWinning.cons node_21593 (AllWinning.cons node_20953 (AllWinning.cons node_20209 (AllWinning.cons node_19429 (AllWinning.cons node_18571 (AllWinning.cons node_17660 (AllWinning.cons node_16754 (AllWinning.nil))))))))))))))))))))))))

theorem node_22757 : Outcome ⟨14, 8, 15, 10⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 18⟩) (by decide) node_15170

theorem node_22758 : Outcome ⟨14, 9, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 14, 2⟩, ⟨12, 9, 14, 4⟩, ⟨14, 8, 14, 2⟩, ⟨14, 7, 14, 4⟩, ⟨14, 9, 13, 2⟩, ⟨14, 9, 12, 4⟩]
  exact AllWinning.cons node_22145 (AllWinning.cons node_21507 (AllWinning.cons node_22187 (AllWinning.cons node_21591 (AllWinning.cons node_22189 (AllWinning.cons node_21595 (AllWinning.nil))))))

theorem node_22759 : Outcome ⟨14, 9, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 14, 2⟩, ⟨12, 9, 14, 4⟩, ⟨11, 9, 14, 6⟩, ⟨10, 9, 14, 8⟩, ⟨14, 8, 14, 2⟩, ⟨14, 7, 14, 4⟩, ⟨14, 6, 14, 6⟩, ⟨14, 5, 14, 8⟩, ⟨14, 9, 13, 2⟩, ⟨14, 9, 12, 4⟩, ⟨14, 9, 11, 6⟩, ⟨14, 9, 10, 8⟩]
  exact AllWinning.cons node_22145 (AllWinning.cons node_21507 (AllWinning.cons node_20797 (AllWinning.cons node_20004 (AllWinning.cons node_22187 (AllWinning.cons node_21591 (AllWinning.cons node_20948 (AllWinning.cons node_20198 (AllWinning.cons node_22189 (AllWinning.cons node_21595 (AllWinning.cons node_20955 (AllWinning.cons node_20212 (AllWinning.nil))))))))))))

theorem node_22760 : Outcome ⟨14, 9, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 14, 2⟩, ⟨12, 9, 14, 4⟩, ⟨11, 9, 14, 6⟩, ⟨10, 9, 14, 8⟩, ⟨9, 9, 14, 10⟩, ⟨8, 9, 14, 12⟩, ⟨14, 8, 14, 2⟩, ⟨14, 7, 14, 4⟩, ⟨14, 6, 14, 6⟩, ⟨14, 5, 14, 8⟩, ⟨14, 4, 14, 10⟩, ⟨14, 3, 14, 12⟩, ⟨14, 9, 13, 2⟩, ⟨14, 9, 12, 4⟩, ⟨14, 9, 11, 6⟩, ⟨14, 9, 10, 8⟩, ⟨14, 9, 9, 10⟩, ⟨14, 9, 8, 12⟩]
  exact AllWinning.cons node_22145 (AllWinning.cons node_21507 (AllWinning.cons node_20797 (AllWinning.cons node_20004 (AllWinning.cons node_19163 (AllWinning.cons node_18207 (AllWinning.cons node_22187 (AllWinning.cons node_21591 (AllWinning.cons node_20948 (AllWinning.cons node_20198 (AllWinning.cons node_19421 (AllWinning.cons node_18554 (AllWinning.cons node_22189 (AllWinning.cons node_21595 (AllWinning.cons node_20955 (AllWinning.cons node_20212 (AllWinning.cons node_19432 (AllWinning.cons node_18574 (AllWinning.nil))))))))))))))))))

theorem node_22761 : Outcome ⟨14, 9, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 14, 2⟩, ⟨12, 9, 14, 4⟩, ⟨11, 9, 14, 6⟩, ⟨10, 9, 14, 8⟩, ⟨9, 9, 14, 10⟩, ⟨8, 9, 14, 12⟩, ⟨7, 9, 14, 14⟩, ⟨6, 9, 14, 16⟩, ⟨14, 8, 14, 2⟩, ⟨14, 7, 14, 4⟩, ⟨14, 6, 14, 6⟩, ⟨14, 5, 14, 8⟩, ⟨14, 4, 14, 10⟩, ⟨14, 3, 14, 12⟩, ⟨14, 2, 14, 14⟩, ⟨14, 1, 14, 16⟩, ⟨14, 9, 13, 2⟩, ⟨14, 9, 12, 4⟩, ⟨14, 9, 11, 6⟩, ⟨14, 9, 10, 8⟩, ⟨14, 9, 9, 10⟩, ⟨14, 9, 8, 12⟩, ⟨14, 9, 7, 14⟩, ⟨14, 9, 6, 16⟩]
  exact AllWinning.cons node_22145 (AllWinning.cons node_21507 (AllWinning.cons node_20797 (AllWinning.cons node_20004 (AllWinning.cons node_19163 (AllWinning.cons node_18207 (AllWinning.cons node_17267 (AllWinning.cons node_16221 (AllWinning.cons node_22187 (AllWinning.cons node_21591 (AllWinning.cons node_20948 (AllWinning.cons node_20198 (AllWinning.cons node_19421 (AllWinning.cons node_18554 (AllWinning.cons node_17640 (AllWinning.cons node_16734 (AllWinning.cons node_22189 (AllWinning.cons node_21595 (AllWinning.cons node_20955 (AllWinning.cons node_20212 (AllWinning.cons node_19432 (AllWinning.cons node_18574 (AllWinning.cons node_17663 (AllWinning.cons node_16759 (AllWinning.nil))))))))))))))))))))))))

theorem node_22762 : Outcome ⟨14, 9, 14, 10⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 18⟩) (by decide) node_15670

theorem node_22763 : Outcome ⟨14, 10, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 10, 13, 2⟩, ⟨12, 10, 13, 4⟩, ⟨14, 9, 13, 2⟩, ⟨14, 8, 13, 4⟩, ⟨14, 10, 12, 2⟩, ⟨14, 10, 11, 4⟩]
  exact AllWinning.cons node_22147 (AllWinning.cons node_21509 (AllWinning.cons node_22189 (AllWinning.cons node_21593 (AllWinning.cons node_22191 (AllWinning.cons node_21598 (AllWinning.nil))))))

theorem node_22764 : Outcome ⟨14, 10, 13, 6⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 8⟩) (by decide) node_20202

theorem node_22765 : Outcome ⟨14, 10, 13, 10⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 8⟩) (by decide) node_20202

theorem node_22766 : Outcome ⟨14, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨12, 11, 12, 4⟩) (by decide) node_21510

theorem node_22767 : Outcome ⟨14, 11, 12, 10⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 18⟩) (by decide) node_15681

theorem node_22768 : Outcome ⟨14, 11, 12, 14⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 18⟩) (by decide) node_15681

theorem node_22769 : Outcome ⟨14, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨12, 12, 11, 4⟩) (by decide) node_21513

theorem node_22770 : Outcome ⟨14, 12, 11, 10⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 18⟩) (by decide) node_15718

theorem node_22771 : Outcome ⟨14, 12, 11, 14⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 18⟩) (by decide) node_15718

theorem node_22772 : Outcome ⟨14, 13, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 13, 10, 2⟩, ⟨12, 13, 10, 4⟩, ⟨14, 12, 10, 2⟩, ⟨14, 11, 10, 4⟩, ⟨14, 13, 9, 2⟩, ⟨14, 13, 8, 4⟩]
  exact AllWinning.cons node_22157 (AllWinning.cons node_21516 (AllWinning.cons node_22196 (AllWinning.cons node_21601 (AllWinning.cons node_22200 (AllWinning.cons node_21605 (AllWinning.nil))))))

theorem node_22773 : Outcome ⟨14, 13, 10, 6⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 8⟩) (by decide) node_20222

theorem node_22774 : Outcome ⟨14, 13, 10, 10⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 8⟩) (by decide) node_20222

theorem node_22775 : Outcome ⟨14, 14, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 9, 2⟩, ⟨12, 14, 9, 4⟩, ⟨14, 13, 9, 2⟩, ⟨14, 12, 9, 4⟩, ⟨14, 14, 8, 2⟩, ⟨14, 14, 7, 4⟩]
  exact AllWinning.cons node_22159 (AllWinning.cons node_21517 (AllWinning.cons node_22200 (AllWinning.cons node_21603 (AllWinning.cons node_22202 (AllWinning.cons node_21607 (AllWinning.nil))))))

theorem node_22776 : Outcome ⟨14, 14, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 9, 2⟩, ⟨12, 14, 9, 4⟩, ⟨11, 14, 9, 6⟩, ⟨10, 14, 9, 8⟩, ⟨14, 13, 9, 2⟩, ⟨14, 12, 9, 4⟩, ⟨14, 11, 9, 6⟩, ⟨14, 10, 9, 8⟩, ⟨14, 14, 8, 2⟩, ⟨14, 14, 7, 4⟩, ⟨14, 14, 6, 6⟩, ⟨14, 14, 5, 8⟩]
  exact AllWinning.cons node_22159 (AllWinning.cons node_21517 (AllWinning.cons node_20807 (AllWinning.cons node_20020 (AllWinning.cons node_22200 (AllWinning.cons node_21603 (AllWinning.cons node_20959 (AllWinning.cons node_20215 (AllWinning.cons node_22202 (AllWinning.cons node_21607 (AllWinning.cons node_20964 (AllWinning.cons node_20227 (AllWinning.nil))))))))))))

theorem node_22777 : Outcome ⟨14, 14, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 9, 2⟩, ⟨12, 14, 9, 4⟩, ⟨11, 14, 9, 6⟩, ⟨10, 14, 9, 8⟩, ⟨9, 14, 9, 10⟩, ⟨8, 14, 9, 12⟩, ⟨14, 13, 9, 2⟩, ⟨14, 12, 9, 4⟩, ⟨14, 11, 9, 6⟩, ⟨14, 10, 9, 8⟩, ⟨14, 9, 9, 10⟩, ⟨14, 8, 9, 12⟩, ⟨14, 14, 8, 2⟩, ⟨14, 14, 7, 4⟩, ⟨14, 14, 6, 6⟩, ⟨14, 14, 5, 8⟩, ⟨14, 14, 4, 10⟩, ⟨14, 14, 3, 12⟩]
  exact AllWinning.cons node_22159 (AllWinning.cons node_21517 (AllWinning.cons node_20807 (AllWinning.cons node_20020 (AllWinning.cons node_19181 (AllWinning.cons node_18226 (AllWinning.cons node_22200 (AllWinning.cons node_21603 (AllWinning.cons node_20959 (AllWinning.cons node_20215 (AllWinning.cons node_19432 (AllWinning.cons node_18571 (AllWinning.cons node_22202 (AllWinning.cons node_21607 (AllWinning.cons node_20964 (AllWinning.cons node_20227 (AllWinning.cons node_19442 (AllWinning.cons node_18591 (AllWinning.nil))))))))))))))))))

theorem node_22778 : Outcome ⟨14, 14, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 9, 2⟩, ⟨12, 14, 9, 4⟩, ⟨11, 14, 9, 6⟩, ⟨10, 14, 9, 8⟩, ⟨9, 14, 9, 10⟩, ⟨8, 14, 9, 12⟩, ⟨7, 14, 9, 14⟩, ⟨6, 14, 9, 16⟩, ⟨14, 13, 9, 2⟩, ⟨14, 12, 9, 4⟩, ⟨14, 11, 9, 6⟩, ⟨14, 10, 9, 8⟩, ⟨14, 9, 9, 10⟩, ⟨14, 8, 9, 12⟩, ⟨14, 7, 9, 14⟩, ⟨14, 6, 9, 16⟩, ⟨14, 14, 8, 2⟩, ⟨14, 14, 7, 4⟩, ⟨14, 14, 6, 6⟩, ⟨14, 14, 5, 8⟩, ⟨14, 14, 4, 10⟩, ⟨14, 14, 3, 12⟩, ⟨14, 14, 2, 14⟩, ⟨14, 14, 1, 16⟩]
  exact AllWinning.cons node_22159 (AllWinning.cons node_21517 (AllWinning.cons node_20807 (AllWinning.cons node_20020 (AllWinning.cons node_19181 (AllWinning.cons node_18226 (AllWinning.cons node_17283 (AllWinning.cons node_16242 (AllWinning.cons node_22200 (AllWinning.cons node_21603 (AllWinning.cons node_20959 (AllWinning.cons node_20215 (AllWinning.cons node_19432 (AllWinning.cons node_18571 (AllWinning.cons node_17657 (AllWinning.cons node_16750 (AllWinning.cons node_22202 (AllWinning.cons node_21607 (AllWinning.cons node_20964 (AllWinning.cons node_20227 (AllWinning.cons node_19442 (AllWinning.cons node_18591 (AllWinning.cons node_17680 (AllWinning.cons node_16774 (AllWinning.nil))))))))))))))))))))))))

theorem node_22779 : Outcome ⟨14, 14, 9, 10⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 18⟩) (by decide) node_15730

theorem node_22780 : Outcome ⟨14, 15, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 8, 2⟩, ⟨12, 15, 8, 4⟩, ⟨14, 14, 8, 2⟩, ⟨14, 13, 8, 4⟩, ⟨14, 15, 7, 2⟩, ⟨14, 15, 6, 4⟩]
  exact AllWinning.cons node_22161 (AllWinning.cons node_21519 (AllWinning.cons node_22202 (AllWinning.cons node_21605 (AllWinning.cons node_22204 (AllWinning.cons node_21609 (AllWinning.nil))))))

theorem node_22781 : Outcome ⟨14, 15, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 8, 2⟩, ⟨12, 15, 8, 4⟩, ⟨11, 15, 8, 6⟩, ⟨10, 15, 8, 8⟩, ⟨14, 14, 8, 2⟩, ⟨14, 13, 8, 4⟩, ⟨14, 12, 8, 6⟩, ⟨14, 11, 8, 8⟩, ⟨14, 15, 7, 2⟩, ⟨14, 15, 6, 4⟩, ⟨14, 15, 5, 6⟩, ⟨14, 15, 4, 8⟩]
  exact AllWinning.cons node_22161 (AllWinning.cons node_21519 (AllWinning.cons node_20809 (AllWinning.cons node_20023 (AllWinning.cons node_22202 (AllWinning.cons node_21605 (AllWinning.cons node_20962 (AllWinning.cons node_20218 (AllWinning.cons node_22204 (AllWinning.cons node_21609 (AllWinning.cons node_20967 (AllWinning.cons node_20231 (AllWinning.nil))))))))))))

theorem node_22782 : Outcome ⟨14, 15, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 8, 2⟩, ⟨12, 15, 8, 4⟩, ⟨11, 15, 8, 6⟩, ⟨10, 15, 8, 8⟩, ⟨9, 15, 8, 10⟩, ⟨8, 15, 8, 12⟩, ⟨14, 14, 8, 2⟩, ⟨14, 13, 8, 4⟩, ⟨14, 12, 8, 6⟩, ⟨14, 11, 8, 8⟩, ⟨14, 10, 8, 10⟩, ⟨14, 9, 8, 12⟩, ⟨14, 15, 7, 2⟩, ⟨14, 15, 6, 4⟩, ⟨14, 15, 5, 6⟩, ⟨14, 15, 4, 8⟩, ⟨14, 15, 3, 10⟩, ⟨14, 15, 2, 12⟩]
  exact AllWinning.cons node_22161 (AllWinning.cons node_21519 (AllWinning.cons node_20809 (AllWinning.cons node_20023 (AllWinning.cons node_19184 (AllWinning.cons node_18230 (AllWinning.cons node_22202 (AllWinning.cons node_21605 (AllWinning.cons node_20962 (AllWinning.cons node_20218 (AllWinning.cons node_19435 (AllWinning.cons node_18574 (AllWinning.cons node_22204 (AllWinning.cons node_21609 (AllWinning.cons node_20967 (AllWinning.cons node_20231 (AllWinning.cons node_19447 (AllWinning.cons node_18594 (AllWinning.nil))))))))))))))))))

theorem node_22783 : Outcome ⟨14, 15, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 8, 2⟩, ⟨12, 15, 8, 4⟩, ⟨11, 15, 8, 6⟩, ⟨10, 15, 8, 8⟩, ⟨9, 15, 8, 10⟩, ⟨8, 15, 8, 12⟩, ⟨7, 15, 8, 14⟩, ⟨6, 15, 8, 16⟩, ⟨14, 14, 8, 2⟩, ⟨14, 13, 8, 4⟩, ⟨14, 12, 8, 6⟩, ⟨14, 11, 8, 8⟩, ⟨14, 10, 8, 10⟩, ⟨14, 9, 8, 12⟩, ⟨14, 8, 8, 14⟩, ⟨14, 7, 8, 16⟩, ⟨14, 15, 7, 2⟩, ⟨14, 15, 6, 4⟩, ⟨14, 15, 5, 6⟩, ⟨14, 15, 4, 8⟩, ⟨14, 15, 3, 10⟩, ⟨14, 15, 2, 12⟩, ⟨14, 15, 1, 14⟩, ⟨14, 15, 0, 16⟩]
  exact AllWinning.cons node_22161 (AllWinning.cons node_21519 (AllWinning.cons node_20809 (AllWinning.cons node_20023 (AllWinning.cons node_19184 (AllWinning.cons node_18230 (AllWinning.cons node_17288 (AllWinning.cons node_16246 (AllWinning.cons node_22202 (AllWinning.cons node_21605 (AllWinning.cons node_20962 (AllWinning.cons node_20218 (AllWinning.cons node_19435 (AllWinning.cons node_18574 (AllWinning.cons node_17660 (AllWinning.cons node_16752 (AllWinning.cons node_22204 (AllWinning.cons node_21609 (AllWinning.cons node_20967 (AllWinning.cons node_20231 (AllWinning.cons node_19447 (AllWinning.cons node_18594 (AllWinning.cons node_17685 (AllWinning.cons node_16777 (AllWinning.nil))))))))))))))))))))))))

theorem node_22784 : Outcome ⟨14, 15, 8, 10⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 18⟩) (by decide) node_15201

theorem node_22785 : Outcome ⟨14, 16, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 7, 2⟩, ⟨12, 16, 7, 4⟩, ⟨14, 15, 7, 2⟩, ⟨14, 14, 7, 4⟩, ⟨14, 16, 6, 2⟩, ⟨14, 16, 5, 4⟩]
  exact AllWinning.cons node_22164 (AllWinning.cons node_21521 (AllWinning.cons node_22204 (AllWinning.cons node_21607 (AllWinning.cons node_22206 (AllWinning.cons node_21610 (AllWinning.nil))))))

theorem node_22786 : Outcome ⟨14, 16, 7, 6⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 6⟩) (by decide) node_20812

theorem node_22787 : Outcome ⟨14, 17, 6, 4⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 8⟩) (by decide) node_20222

theorem node_22788 : Outcome ⟨14, 17, 6, 10⟩ true :=
  Outcome.win (q := ⟨9, 17, 6, 10⟩) (by decide) node_19191

theorem node_22789 : Outcome ⟨14, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 4⟩) (by decide) node_21527

theorem node_22790 : Outcome ⟨14, 18, 5, 8⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 4⟩) (by decide) node_21527

theorem node_22791 : Outcome ⟨14, 18, 5, 14⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 4⟩) (by decide) node_21527

theorem node_22792 : Outcome ⟨14, 19, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 4, 2⟩, ⟨12, 19, 4, 4⟩, ⟨11, 19, 4, 6⟩, ⟨10, 19, 4, 8⟩, ⟨14, 18, 4, 2⟩, ⟨14, 17, 4, 4⟩, ⟨14, 16, 4, 6⟩, ⟨14, 15, 4, 8⟩, ⟨14, 19, 3, 2⟩, ⟨14, 19, 2, 4⟩, ⟨14, 19, 1, 6⟩, ⟨14, 19, 0, 8⟩]
  exact AllWinning.cons node_22172 (AllWinning.cons node_21531 (AllWinning.cons node_20819 (AllWinning.cons node_20033 (AllWinning.cons node_22211 (AllWinning.cons node_21613 (AllWinning.cons node_20970 (AllWinning.cons node_20231 (AllWinning.cons node_22213 (AllWinning.cons node_21616 (AllWinning.cons node_20980 (AllWinning.cons node_20240 (AllWinning.nil))))))))))))

theorem node_22793 : Outcome ⟨14, 19, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 4, 2⟩, ⟨12, 19, 4, 4⟩, ⟨11, 19, 4, 6⟩, ⟨10, 19, 4, 8⟩, ⟨9, 19, 4, 10⟩, ⟨8, 19, 4, 12⟩, ⟨14, 18, 4, 2⟩, ⟨14, 17, 4, 4⟩, ⟨14, 16, 4, 6⟩, ⟨14, 15, 4, 8⟩, ⟨14, 14, 4, 10⟩, ⟨14, 13, 4, 12⟩, ⟨14, 19, 3, 2⟩, ⟨14, 19, 2, 4⟩, ⟨14, 19, 1, 6⟩, ⟨14, 19, 0, 8⟩]
  exact AllWinning.cons node_22172 (AllWinning.cons node_21531 (AllWinning.cons node_20819 (AllWinning.cons node_20033 (AllWinning.cons node_19197 (AllWinning.cons node_18240 (AllWinning.cons node_22211 (AllWinning.cons node_21613 (AllWinning.cons node_20970 (AllWinning.cons node_20231 (AllWinning.cons node_19442 (AllWinning.cons node_18587 (AllWinning.cons node_22213 (AllWinning.cons node_21616 (AllWinning.cons node_20980 (AllWinning.cons node_20240 (AllWinning.nil))))))))))))))))

theorem node_22794 : Outcome ⟨14, 19, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 4, 2⟩, ⟨12, 19, 4, 4⟩, ⟨11, 19, 4, 6⟩, ⟨10, 19, 4, 8⟩, ⟨9, 19, 4, 10⟩, ⟨8, 19, 4, 12⟩, ⟨7, 19, 4, 14⟩, ⟨6, 19, 4, 16⟩, ⟨5, 19, 4, 18⟩, ⟨4, 19, 4, 20⟩, ⟨14, 18, 4, 2⟩, ⟨14, 17, 4, 4⟩, ⟨14, 16, 4, 6⟩, ⟨14, 15, 4, 8⟩, ⟨14, 14, 4, 10⟩, ⟨14, 13, 4, 12⟩, ⟨14, 12, 4, 14⟩, ⟨14, 11, 4, 16⟩, ⟨14, 10, 4, 18⟩, ⟨14, 9, 4, 20⟩, ⟨14, 19, 3, 2⟩, ⟨14, 19, 2, 4⟩, ⟨14, 19, 1, 6⟩, ⟨14, 19, 0, 8⟩]
  exact AllWinning.cons node_22172 (AllWinning.cons node_21531 (AllWinning.cons node_20819 (AllWinning.cons node_20033 (AllWinning.cons node_19197 (AllWinning.cons node_18240 (AllWinning.cons node_17298 (AllWinning.cons node_16258 (AllWinning.cons node_15212 (AllWinning.cons node_14203 (AllWinning.cons node_22211 (AllWinning.cons node_21613 (AllWinning.cons node_20970 (AllWinning.cons node_20231 (AllWinning.cons node_19442 (AllWinning.cons node_18587 (AllWinning.cons node_17672 (AllWinning.cons node_16765 (AllWinning.cons node_15708 (AllWinning.cons node_14738 (AllWinning.cons node_22213 (AllWinning.cons node_21616 (AllWinning.cons node_20980 (AllWinning.cons node_20240 (AllWinning.nil))))))))))))))))))))))))

theorem node_22795 : Outcome ⟨14, 19, 4, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 4, 2⟩, ⟨12, 19, 4, 4⟩, ⟨11, 19, 4, 6⟩, ⟨10, 19, 4, 8⟩, ⟨9, 19, 4, 10⟩, ⟨8, 19, 4, 12⟩, ⟨7, 19, 4, 14⟩, ⟨6, 19, 4, 16⟩, ⟨5, 19, 4, 18⟩, ⟨4, 19, 4, 20⟩, ⟨3, 19, 4, 22⟩, ⟨2, 19, 4, 24⟩, ⟨1, 19, 4, 26⟩, ⟨0, 19, 4, 28⟩, ⟨14, 18, 4, 2⟩, ⟨14, 17, 4, 4⟩, ⟨14, 16, 4, 6⟩, ⟨14, 15, 4, 8⟩, ⟨14, 14, 4, 10⟩, ⟨14, 13, 4, 12⟩, ⟨14, 12, 4, 14⟩, ⟨14, 11, 4, 16⟩, ⟨14, 10, 4, 18⟩, ⟨14, 9, 4, 20⟩, ⟨14, 8, 4, 22⟩, ⟨14, 7, 4, 24⟩, ⟨14, 6, 4, 26⟩, ⟨14, 5, 4, 28⟩, ⟨14, 4, 4, 30⟩, ⟨14, 3, 4, 32⟩, ⟨14, 2, 4, 34⟩, ⟨14, 1, 4, 36⟩, ⟨14, 19, 3, 2⟩, ⟨14, 19, 2, 4⟩, ⟨14, 19, 1, 6⟩, ⟨14, 19, 0, 8⟩]
  exact AllWinning.cons node_22172 (AllWinning.cons node_21531 (AllWinning.cons node_20819 (AllWinning.cons node_20033 (AllWinning.cons node_19197 (AllWinning.cons node_18240 (AllWinning.cons node_17298 (AllWinning.cons node_16258 (AllWinning.cons node_15212 (AllWinning.cons node_14203 (AllWinning.cons node_13197 (AllWinning.cons node_12145 (AllWinning.cons node_11087 (AllWinning.cons node_9930 (AllWinning.cons node_22211 (AllWinning.cons node_21613 (AllWinning.cons node_20970 (AllWinning.cons node_20231 (AllWinning.cons node_19442 (AllWinning.cons node_18587 (AllWinning.cons node_17672 (AllWinning.cons node_16765 (AllWinning.cons node_15708 (AllWinning.cons node_14738 (AllWinning.cons node_13789 (AllWinning.cons node_12803 (AllWinning.cons node_11825 (AllWinning.cons node_10817 (AllWinning.cons node_9753 (AllWinning.cons node_8808 (AllWinning.cons node_7804 (AllWinning.cons node_6874 (AllWinning.cons node_22213 (AllWinning.cons node_21616 (AllWinning.cons node_20980 (AllWinning.cons node_20240 (AllWinning.nil))))))))))))))))))))))))))))))))))))

theorem node_22796 : Outcome ⟨14, 20, 3, 4⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 6⟩) (by decide) node_20974

theorem node_22797 : Outcome ⟨15, 2, 20, 8⟩ true :=
  Outcome.win (q := ⟨15, 0, 20, 4⟩) (by decide) node_21619

theorem node_22798 : Outcome ⟨15, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 2⟩) (by decide) node_22219

theorem node_22799 : Outcome ⟨15, 3, 19, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 19, 8⟩) (by decide) node_20040

theorem node_22800 : Outcome ⟨15, 4, 18, 4⟩ true :=
  Outcome.win (q := ⟨11, 4, 18, 8⟩) (by decide) node_20045

theorem node_22801 : Outcome ⟨15, 5, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 15, 4⟩) (by decide) node_21629

theorem node_22802 : Outcome ⟨15, 6, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 6, 16, 2⟩, ⟨13, 6, 16, 4⟩, ⟨15, 5, 16, 2⟩, ⟨15, 4, 16, 4⟩, ⟨15, 6, 15, 2⟩, ⟨15, 6, 14, 4⟩]
  exact AllWinning.cons node_22182 (AllWinning.cons node_21546 (AllWinning.cons node_22230 (AllWinning.cons node_21626 (AllWinning.cons node_22233 (AllWinning.cons node_21632 (AllWinning.nil))))))

theorem node_22803 : Outcome ⟨15, 6, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 6⟩) (by decide) node_20832

theorem node_22804 : Outcome ⟨15, 6, 16, 8⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 10⟩) (by decide) node_19461

theorem node_22805 : Outcome ⟨15, 6, 16, 12⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 10⟩) (by decide) node_19461

theorem node_22806 : Outcome ⟨15, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 6⟩) (by decide) node_20838

theorem node_22807 : Outcome ⟨15, 7, 15, 6⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 6⟩) (by decide) node_20838

theorem node_22808 : Outcome ⟨15, 8, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 8, 14, 2⟩, ⟨13, 8, 14, 4⟩, ⟨15, 7, 14, 2⟩, ⟨15, 6, 14, 4⟩, ⟨15, 8, 13, 2⟩, ⟨15, 8, 12, 4⟩]
  exact AllWinning.cons node_22187 (AllWinning.cons node_21551 (AllWinning.cons node_22236 (AllWinning.cons node_21632 (AllWinning.cons node_22238 (AllWinning.cons node_21638 (AllWinning.nil))))))

theorem node_22809 : Outcome ⟨15, 8, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 8, 14, 2⟩, ⟨13, 8, 14, 4⟩, ⟨12, 8, 14, 6⟩, ⟨11, 8, 14, 8⟩, ⟨15, 7, 14, 2⟩, ⟨15, 6, 14, 4⟩, ⟨15, 5, 14, 6⟩, ⟨15, 4, 14, 8⟩, ⟨15, 8, 13, 2⟩, ⟨15, 8, 12, 4⟩, ⟨15, 8, 11, 6⟩, ⟨15, 8, 10, 8⟩]
  exact AllWinning.cons node_22187 (AllWinning.cons node_21551 (AllWinning.cons node_20842 (AllWinning.cons node_20054 (AllWinning.cons node_22236 (AllWinning.cons node_21632 (AllWinning.cons node_20994 (AllWinning.cons node_20254 (AllWinning.cons node_22238 (AllWinning.cons node_21638 (AllWinning.cons node_21008 (AllWinning.cons node_20261 (AllWinning.nil))))))))))))

theorem node_22810 : Outcome ⟨15, 8, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 8, 14, 2⟩, ⟨13, 8, 14, 4⟩, ⟨12, 8, 14, 6⟩, ⟨11, 8, 14, 8⟩, ⟨10, 8, 14, 10⟩, ⟨9, 8, 14, 12⟩, ⟨15, 7, 14, 2⟩, ⟨15, 6, 14, 4⟩, ⟨15, 5, 14, 6⟩, ⟨15, 4, 14, 8⟩, ⟨15, 3, 14, 10⟩, ⟨15, 2, 14, 12⟩, ⟨15, 8, 13, 2⟩, ⟨15, 8, 12, 4⟩, ⟨15, 8, 11, 6⟩, ⟨15, 8, 10, 8⟩, ⟨15, 8, 9, 10⟩, ⟨15, 8, 8, 12⟩]
  exact AllWinning.cons node_22187 (AllWinning.cons node_21551 (AllWinning.cons node_20842 (AllWinning.cons node_20054 (AllWinning.cons node_19218 (AllWinning.cons node_18261 (AllWinning.cons node_22236 (AllWinning.cons node_21632 (AllWinning.cons node_20994 (AllWinning.cons node_20254 (AllWinning.cons node_19474 (AllWinning.cons node_18606 (AllWinning.cons node_22238 (AllWinning.cons node_21638 (AllWinning.cons node_21008 (AllWinning.cons node_20261 (AllWinning.cons node_19490 (AllWinning.cons node_18627 (AllWinning.nil))))))))))))))))))

theorem node_22811 : Outcome ⟨15, 8, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 8, 14, 2⟩, ⟨13, 8, 14, 4⟩, ⟨12, 8, 14, 6⟩, ⟨11, 8, 14, 8⟩, ⟨10, 8, 14, 10⟩, ⟨9, 8, 14, 12⟩, ⟨8, 8, 14, 14⟩, ⟨7, 8, 14, 16⟩, ⟨15, 7, 14, 2⟩, ⟨15, 6, 14, 4⟩, ⟨15, 5, 14, 6⟩, ⟨15, 4, 14, 8⟩, ⟨15, 3, 14, 10⟩, ⟨15, 2, 14, 12⟩, ⟨15, 1, 14, 14⟩, ⟨15, 0, 14, 16⟩, ⟨15, 8, 13, 2⟩, ⟨15, 8, 12, 4⟩, ⟨15, 8, 11, 6⟩, ⟨15, 8, 10, 8⟩, ⟨15, 8, 9, 10⟩, ⟨15, 8, 8, 12⟩, ⟨15, 8, 7, 14⟩, ⟨15, 8, 6, 16⟩]
  exact AllWinning.cons node_22187 (AllWinning.cons node_21551 (AllWinning.cons node_20842 (AllWinning.cons node_20054 (AllWinning.cons node_19218 (AllWinning.cons node_18261 (AllWinning.cons node_17320 (AllWinning.cons node_16281 (AllWinning.cons node_22236 (AllWinning.cons node_21632 (AllWinning.cons node_20994 (AllWinning.cons node_20254 (AllWinning.cons node_19474 (AllWinning.cons node_18606 (AllWinning.cons node_17698 (AllWinning.cons node_16780 (AllWinning.cons node_22238 (AllWinning.cons node_21638 (AllWinning.cons node_21008 (AllWinning.cons node_20261 (AllWinning.cons node_19490 (AllWinning.cons node_18627 (AllWinning.cons node_17721 (AllWinning.cons node_16801 (AllWinning.nil))))))))))))))))))))))))

theorem node_22812 : Outcome ⟨15, 8, 14, 10⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 18⟩) (by decide) node_15768

theorem node_22813 : Outcome ⟨15, 9, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 13, 2⟩, ⟨13, 9, 13, 4⟩, ⟨15, 8, 13, 2⟩, ⟨15, 7, 13, 4⟩, ⟨15, 9, 12, 2⟩, ⟨15, 9, 11, 4⟩]
  exact AllWinning.cons node_22189 (AllWinning.cons node_21554 (AllWinning.cons node_22238 (AllWinning.cons node_21635 (AllWinning.cons node_22241 (AllWinning.cons node_21641 (AllWinning.nil))))))

theorem node_22814 : Outcome ⟨15, 9, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 13, 2⟩, ⟨13, 9, 13, 4⟩, ⟨12, 9, 13, 6⟩, ⟨11, 9, 13, 8⟩, ⟨15, 8, 13, 2⟩, ⟨15, 7, 13, 4⟩, ⟨15, 6, 13, 6⟩, ⟨15, 5, 13, 8⟩, ⟨15, 9, 12, 2⟩, ⟨15, 9, 11, 4⟩, ⟨15, 9, 10, 6⟩, ⟨15, 9, 9, 8⟩]
  exact AllWinning.cons node_22189 (AllWinning.cons node_21554 (AllWinning.cons node_20845 (AllWinning.cons node_20057 (AllWinning.cons node_22238 (AllWinning.cons node_21635 (AllWinning.cons node_20997 (AllWinning.cons node_20256 (AllWinning.cons node_22241 (AllWinning.cons node_21641 (AllWinning.cons node_21011 (AllWinning.cons node_20266 (AllWinning.nil))))))))))))

theorem node_22815 : Outcome ⟨15, 9, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 13, 2⟩, ⟨13, 9, 13, 4⟩, ⟨12, 9, 13, 6⟩, ⟨11, 9, 13, 8⟩, ⟨10, 9, 13, 10⟩, ⟨9, 9, 13, 12⟩, ⟨15, 8, 13, 2⟩, ⟨15, 7, 13, 4⟩, ⟨15, 6, 13, 6⟩, ⟨15, 5, 13, 8⟩, ⟨15, 4, 13, 10⟩, ⟨15, 3, 13, 12⟩, ⟨15, 9, 12, 2⟩, ⟨15, 9, 11, 4⟩, ⟨15, 9, 10, 6⟩, ⟨15, 9, 9, 8⟩, ⟨15, 9, 8, 10⟩, ⟨15, 9, 7, 12⟩]
  exact AllWinning.cons node_22189 (AllWinning.cons node_21554 (AllWinning.cons node_20845 (AllWinning.cons node_20057 (AllWinning.cons node_19223 (AllWinning.cons node_18264 (AllWinning.cons node_22238 (AllWinning.cons node_21635 (AllWinning.cons node_20997 (AllWinning.cons node_20256 (AllWinning.cons node_19478 (AllWinning.cons node_18610 (AllWinning.cons node_22241 (AllWinning.cons node_21641 (AllWinning.cons node_21011 (AllWinning.cons node_20266 (AllWinning.cons node_19492 (AllWinning.cons node_18631 (AllWinning.nil))))))))))))))))))

theorem node_22816 : Outcome ⟨15, 9, 13, 10⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 16⟩) (by decide) node_16289

theorem node_22817 : Outcome ⟨15, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨15, 10, 11, 2⟩) (by decide) node_22244

theorem node_22818 : Outcome ⟨15, 10, 12, 6⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 6⟩) (by decide) node_21002

theorem node_22819 : Outcome ⟨15, 10, 12, 12⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 6⟩) (by decide) node_21002

theorem node_22820 : Outcome ⟨15, 11, 11, 2⟩ true :=
  Outcome.win (q := ⟨15, 10, 11, 2⟩) (by decide) node_22244

theorem node_22821 : Outcome ⟨15, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨15, 11, 10, 2⟩) (by decide) node_22247

theorem node_22822 : Outcome ⟨15, 12, 10, 6⟩ true :=
  Outcome.win (q := ⟨15, 12, 7, 6⟩) (by decide) node_21021

theorem node_22823 : Outcome ⟨15, 12, 10, 12⟩ true :=
  Outcome.win (q := ⟨15, 12, 7, 6⟩) (by decide) node_21021

theorem node_22824 : Outcome ⟨15, 13, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 9, 2⟩, ⟨13, 13, 9, 4⟩, ⟨15, 12, 9, 2⟩, ⟨15, 11, 9, 4⟩, ⟨15, 13, 8, 2⟩, ⟨15, 13, 7, 4⟩]
  exact AllWinning.cons node_22200 (AllWinning.cons node_21560 (AllWinning.cons node_22250 (AllWinning.cons node_21646 (AllWinning.cons node_22253 (AllWinning.cons node_21649 (AllWinning.nil))))))

theorem node_22825 : Outcome ⟨15, 13, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 9, 2⟩, ⟨13, 13, 9, 4⟩, ⟨12, 13, 9, 6⟩, ⟨11, 13, 9, 8⟩, ⟨15, 12, 9, 2⟩, ⟨15, 11, 9, 4⟩, ⟨15, 10, 9, 6⟩, ⟨15, 9, 9, 8⟩, ⟨15, 13, 8, 2⟩, ⟨15, 13, 7, 4⟩, ⟨15, 13, 6, 6⟩, ⟨15, 13, 5, 8⟩]
  exact AllWinning.cons node_22200 (AllWinning.cons node_21560 (AllWinning.cons node_20854 (AllWinning.cons node_20065 (AllWinning.cons node_22250 (AllWinning.cons node_21646 (AllWinning.cons node_21015 (AllWinning.cons node_20266 (AllWinning.cons node_22253 (AllWinning.cons node_21649 (AllWinning.cons node_21026 (AllWinning.cons node_20274 (AllWinning.nil))))))))))))

theorem node_22826 : Outcome ⟨15, 13, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 9, 2⟩, ⟨13, 13, 9, 4⟩, ⟨12, 13, 9, 6⟩, ⟨11, 13, 9, 8⟩, ⟨10, 13, 9, 10⟩, ⟨9, 13, 9, 12⟩, ⟨15, 12, 9, 2⟩, ⟨15, 11, 9, 4⟩, ⟨15, 10, 9, 6⟩, ⟨15, 9, 9, 8⟩, ⟨15, 8, 9, 10⟩, ⟨15, 7, 9, 12⟩, ⟨15, 13, 8, 2⟩, ⟨15, 13, 7, 4⟩, ⟨15, 13, 6, 6⟩, ⟨15, 13, 5, 8⟩, ⟨15, 13, 4, 10⟩, ⟨15, 13, 3, 12⟩]
  exact AllWinning.cons node_22200 (AllWinning.cons node_21560 (AllWinning.cons node_20854 (AllWinning.cons node_20065 (AllWinning.cons node_19232 (AllWinning.cons node_18279 (AllWinning.cons node_22250 (AllWinning.cons node_21646 (AllWinning.cons node_21015 (AllWinning.cons node_20266 (AllWinning.cons node_19490 (AllWinning.cons node_18623 (AllWinning.cons node_22253 (AllWinning.cons node_21649 (AllWinning.cons node_21026 (AllWinning.cons node_20274 (AllWinning.cons node_19507 (AllWinning.cons node_18644 (AllWinning.nil))))))))))))))))))

end RQ9F1
