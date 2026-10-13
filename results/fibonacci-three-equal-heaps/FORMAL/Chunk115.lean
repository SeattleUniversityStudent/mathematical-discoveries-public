import Chunk114
set_option autoImplicit false
namespace RQ9F1

theorem node_24116 : Outcome ⟨16, 5, 19, 6⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 12⟩) (by decide) node_20736

theorem node_24117 : Outcome ⟨16, 5, 19, 12⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 12⟩) (by decide) node_20736

theorem node_24118 : Outcome ⟨16, 6, 18, 2⟩ true :=
  Outcome.win (q := ⟨16, 6, 17, 2⟩) (by decide) node_23718

theorem node_24119 : Outcome ⟨16, 7, 17, 2⟩ true :=
  Outcome.win (q := ⟨15, 7, 17, 2⟩) (by decide) node_23693

theorem node_24120 : Outcome ⟨16, 7, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 7, 17, 2⟩) (by decide) node_23693

theorem node_24121 : Outcome ⟨16, 8, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 8, 16, 2⟩, ⟨14, 8, 16, 4⟩, ⟨13, 8, 16, 6⟩, ⟨12, 8, 16, 8⟩, ⟨16, 7, 16, 2⟩, ⟨16, 6, 16, 4⟩, ⟨16, 5, 16, 6⟩, ⟨16, 4, 16, 8⟩, ⟨16, 8, 15, 2⟩, ⟨16, 8, 14, 4⟩, ⟨16, 8, 13, 6⟩, ⟨16, 8, 12, 8⟩]
  exact AllWinning.cons node_23694 (AllWinning.cons node_23254 (AllWinning.cons node_22704 (AllWinning.cons node_22096 (AllWinning.cons node_23720 (AllWinning.cons node_23317 (AllWinning.cons node_22849 (AllWinning.cons node_22284 (AllWinning.cons node_23723 (AllWinning.cons node_23321 (AllWinning.cons node_22854 (AllWinning.cons node_22292 (AllWinning.nil))))))))))))

theorem node_24122 : Outcome ⟨16, 8, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 8, 16, 2⟩, ⟨14, 8, 16, 4⟩, ⟨13, 8, 16, 6⟩, ⟨12, 8, 16, 8⟩, ⟨11, 8, 16, 10⟩, ⟨10, 8, 16, 12⟩, ⟨16, 7, 16, 2⟩, ⟨16, 6, 16, 4⟩, ⟨16, 5, 16, 6⟩, ⟨16, 4, 16, 8⟩, ⟨16, 3, 16, 10⟩, ⟨16, 2, 16, 12⟩, ⟨16, 8, 15, 2⟩, ⟨16, 8, 14, 4⟩, ⟨16, 8, 13, 6⟩, ⟨16, 8, 12, 8⟩, ⟨16, 8, 11, 10⟩, ⟨16, 8, 10, 12⟩]
  exact AllWinning.cons node_23694 (AllWinning.cons node_23254 (AllWinning.cons node_22704 (AllWinning.cons node_22096 (AllWinning.cons node_21461 (AllWinning.cons node_20747 (AllWinning.cons node_23720 (AllWinning.cons node_23317 (AllWinning.cons node_22849 (AllWinning.cons node_22284 (AllWinning.cons node_21672 (AllWinning.cons node_21046 (AllWinning.cons node_23723 (AllWinning.cons node_23321 (AllWinning.cons node_22854 (AllWinning.cons node_22292 (AllWinning.cons node_21679 (AllWinning.cons node_21069 (AllWinning.nil))))))))))))))))))

theorem node_24123 : Outcome ⟨16, 8, 16, 10⟩ true :=
  Outcome.win (q := ⟨16, 0, 16, 16⟩) (by decide) node_19534

theorem node_24124 : Outcome ⟨16, 9, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 9, 15, 2⟩, ⟨14, 9, 15, 4⟩, ⟨16, 8, 15, 2⟩, ⟨16, 7, 15, 4⟩, ⟨16, 9, 14, 2⟩, ⟨16, 9, 13, 4⟩]
  exact AllWinning.cons node_23696 (AllWinning.cons node_23255 (AllWinning.cons node_23723 (AllWinning.cons node_23319 (AllWinning.cons node_23725 (AllWinning.cons node_23322 (AllWinning.nil))))))

theorem node_24125 : Outcome ⟨16, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 6⟩) (by decide) node_22708

theorem node_24126 : Outcome ⟨16, 9, 15, 6⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 6⟩) (by decide) node_22708

theorem node_24127 : Outcome ⟨16, 10, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 10, 14, 2⟩, ⟨14, 10, 14, 4⟩, ⟨16, 9, 14, 2⟩, ⟨16, 8, 14, 4⟩, ⟨16, 10, 13, 2⟩, ⟨16, 10, 12, 4⟩]
  exact AllWinning.cons node_23698 (AllWinning.cons node_23257 (AllWinning.cons node_23725 (AllWinning.cons node_23321 (AllWinning.cons node_23726 (AllWinning.cons node_23325 (AllWinning.nil))))))

theorem node_24128 : Outcome ⟨16, 10, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 10, 14, 2⟩, ⟨14, 10, 14, 4⟩, ⟨13, 10, 14, 6⟩, ⟨12, 10, 14, 8⟩, ⟨16, 9, 14, 2⟩, ⟨16, 8, 14, 4⟩, ⟨16, 7, 14, 6⟩, ⟨16, 6, 14, 8⟩, ⟨16, 10, 13, 2⟩, ⟨16, 10, 12, 4⟩, ⟨16, 10, 11, 6⟩, ⟨16, 10, 10, 8⟩]
  exact AllWinning.cons node_23698 (AllWinning.cons node_23257 (AllWinning.cons node_22711 (AllWinning.cons node_22103 (AllWinning.cons node_23725 (AllWinning.cons node_23321 (AllWinning.cons node_22853 (AllWinning.cons node_22288 (AllWinning.cons node_23726 (AllWinning.cons node_23325 (AllWinning.cons node_22860 (AllWinning.cons node_22297 (AllWinning.nil))))))))))))

theorem node_24129 : Outcome ⟨16, 10, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 10, 14, 2⟩, ⟨14, 10, 14, 4⟩, ⟨13, 10, 14, 6⟩, ⟨12, 10, 14, 8⟩, ⟨11, 10, 14, 10⟩, ⟨10, 10, 14, 12⟩, ⟨16, 9, 14, 2⟩, ⟨16, 8, 14, 4⟩, ⟨16, 7, 14, 6⟩, ⟨16, 6, 14, 8⟩, ⟨16, 5, 14, 10⟩, ⟨16, 4, 14, 12⟩, ⟨16, 10, 13, 2⟩, ⟨16, 10, 12, 4⟩, ⟨16, 10, 11, 6⟩, ⟨16, 10, 10, 8⟩, ⟨16, 10, 9, 10⟩, ⟨16, 10, 8, 12⟩]
  exact AllWinning.cons node_23698 (AllWinning.cons node_23257 (AllWinning.cons node_22711 (AllWinning.cons node_22103 (AllWinning.cons node_21466 (AllWinning.cons node_20753 (AllWinning.cons node_23725 (AllWinning.cons node_23321 (AllWinning.cons node_22853 (AllWinning.cons node_22288 (AllWinning.cons node_21675 (AllWinning.cons node_21052 (AllWinning.cons node_23726 (AllWinning.cons node_23325 (AllWinning.cons node_22860 (AllWinning.cons node_22297 (AllWinning.cons node_21684 (AllWinning.cons node_21072 (AllWinning.nil))))))))))))))))))

theorem node_24130 : Outcome ⟨16, 10, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 10, 14, 2⟩, ⟨14, 10, 14, 4⟩, ⟨13, 10, 14, 6⟩, ⟨12, 10, 14, 8⟩, ⟨11, 10, 14, 10⟩, ⟨10, 10, 14, 12⟩, ⟨9, 10, 14, 14⟩, ⟨8, 10, 14, 16⟩, ⟨7, 10, 14, 18⟩, ⟨6, 10, 14, 20⟩, ⟨16, 9, 14, 2⟩, ⟨16, 8, 14, 4⟩, ⟨16, 7, 14, 6⟩, ⟨16, 6, 14, 8⟩, ⟨16, 5, 14, 10⟩, ⟨16, 4, 14, 12⟩, ⟨16, 3, 14, 14⟩, ⟨16, 2, 14, 16⟩, ⟨16, 1, 14, 18⟩, ⟨16, 0, 14, 20⟩, ⟨16, 10, 13, 2⟩, ⟨16, 10, 12, 4⟩, ⟨16, 10, 11, 6⟩, ⟨16, 10, 10, 8⟩, ⟨16, 10, 9, 10⟩, ⟨16, 10, 8, 12⟩, ⟨16, 10, 7, 14⟩, ⟨16, 10, 6, 16⟩, ⟨16, 10, 5, 18⟩, ⟨16, 10, 4, 20⟩]
  exact AllWinning.cons node_23698 (AllWinning.cons node_23257 (AllWinning.cons node_22711 (AllWinning.cons node_22103 (AllWinning.cons node_21466 (AllWinning.cons node_20753 (AllWinning.cons node_19963 (AllWinning.cons node_19115 (AllWinning.cons node_18155 (AllWinning.cons node_17224 (AllWinning.cons node_23725 (AllWinning.cons node_23321 (AllWinning.cons node_22853 (AllWinning.cons node_22288 (AllWinning.cons node_21675 (AllWinning.cons node_21052 (AllWinning.cons node_20293 (AllWinning.cons node_19545 (AllWinning.cons node_18656 (AllWinning.cons node_17750 (AllWinning.cons node_23726 (AllWinning.cons node_23325 (AllWinning.cons node_22860 (AllWinning.cons node_22297 (AllWinning.cons node_21684 (AllWinning.cons node_21072 (AllWinning.cons node_20306 (AllWinning.cons node_19563 (AllWinning.cons node_18682 (AllWinning.cons node_17774 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_24131 : Outcome ⟨16, 11, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 11, 13, 2⟩, ⟨14, 11, 13, 4⟩, ⟨16, 10, 13, 2⟩, ⟨16, 9, 13, 4⟩, ⟨16, 11, 12, 2⟩, ⟨16, 11, 11, 4⟩]
  exact AllWinning.cons node_23700 (AllWinning.cons node_23259 (AllWinning.cons node_23726 (AllWinning.cons node_23322 (AllWinning.cons node_23728 (AllWinning.cons node_23327 (AllWinning.nil))))))

theorem node_24132 : Outcome ⟨16, 11, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 11, 13, 2⟩, ⟨14, 11, 13, 4⟩, ⟨13, 11, 13, 6⟩, ⟨12, 11, 13, 8⟩, ⟨16, 10, 13, 2⟩, ⟨16, 9, 13, 4⟩, ⟨16, 8, 13, 6⟩, ⟨16, 7, 13, 8⟩, ⟨16, 11, 12, 2⟩, ⟨16, 11, 11, 4⟩, ⟨16, 11, 10, 6⟩, ⟨16, 11, 9, 8⟩]
  exact AllWinning.cons node_23700 (AllWinning.cons node_23259 (AllWinning.cons node_22715 (AllWinning.cons node_22105 (AllWinning.cons node_23726 (AllWinning.cons node_23322 (AllWinning.cons node_22854 (AllWinning.cons node_22290 (AllWinning.cons node_23728 (AllWinning.cons node_23327 (AllWinning.cons node_22862 (AllWinning.cons node_22299 (AllWinning.nil))))))))))))

theorem node_24133 : Outcome ⟨16, 11, 13, 10⟩ true :=
  Outcome.win (q := ⟨16, 11, 7, 12⟩) (by decide) node_21076

theorem node_24134 : Outcome ⟨16, 11, 13, 12⟩ true :=
  Outcome.win (q := ⟨16, 11, 7, 12⟩) (by decide) node_21076

theorem node_24135 : Outcome ⟨16, 12, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 12, 12, 2⟩, ⟨14, 12, 12, 4⟩, ⟨16, 11, 12, 2⟩, ⟨16, 10, 12, 4⟩, ⟨16, 12, 11, 2⟩, ⟨16, 12, 10, 4⟩]
  exact AllWinning.cons node_23702 (AllWinning.cons node_23262 (AllWinning.cons node_23728 (AllWinning.cons node_23325 (AllWinning.cons node_23730 (AllWinning.cons node_23329 (AllWinning.nil))))))

theorem node_24136 : Outcome ⟨16, 12, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 12, 12, 2⟩, ⟨14, 12, 12, 4⟩, ⟨13, 12, 12, 6⟩, ⟨12, 12, 12, 8⟩, ⟨16, 11, 12, 2⟩, ⟨16, 10, 12, 4⟩, ⟨16, 9, 12, 6⟩, ⟨16, 8, 12, 8⟩, ⟨16, 12, 11, 2⟩, ⟨16, 12, 10, 4⟩, ⟨16, 12, 9, 6⟩, ⟨16, 12, 8, 8⟩]
  exact AllWinning.cons node_23702 (AllWinning.cons node_23262 (AllWinning.cons node_22717 (AllWinning.cons node_22108 (AllWinning.cons node_23728 (AllWinning.cons node_23325 (AllWinning.cons node_22857 (AllWinning.cons node_22292 (AllWinning.cons node_23730 (AllWinning.cons node_23329 (AllWinning.cons node_22864 (AllWinning.cons node_22301 (AllWinning.nil))))))))))))

theorem node_24137 : Outcome ⟨16, 12, 12, 6⟩ true :=
  Outcome.win (q := ⟨16, 6, 12, 12⟩) (by decide) node_21059

theorem node_24138 : Outcome ⟨16, 13, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 11, 2⟩, ⟨14, 13, 11, 4⟩, ⟨16, 12, 11, 2⟩, ⟨16, 11, 11, 4⟩, ⟨16, 13, 10, 2⟩, ⟨16, 13, 9, 4⟩]
  exact AllWinning.cons node_23704 (AllWinning.cons node_23264 (AllWinning.cons node_23730 (AllWinning.cons node_23327 (AllWinning.cons node_23732 (AllWinning.cons node_23331 (AllWinning.nil))))))

theorem node_24139 : Outcome ⟨16, 13, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 11, 2⟩, ⟨14, 13, 11, 4⟩, ⟨13, 13, 11, 6⟩, ⟨12, 13, 11, 8⟩, ⟨16, 12, 11, 2⟩, ⟨16, 11, 11, 4⟩, ⟨16, 10, 11, 6⟩, ⟨16, 9, 11, 8⟩, ⟨16, 13, 10, 2⟩, ⟨16, 13, 9, 4⟩, ⟨16, 13, 8, 6⟩, ⟨16, 13, 7, 8⟩]
  exact AllWinning.cons node_23704 (AllWinning.cons node_23264 (AllWinning.cons node_22721 (AllWinning.cons node_22111 (AllWinning.cons node_23730 (AllWinning.cons node_23327 (AllWinning.cons node_22860 (AllWinning.cons node_22294 (AllWinning.cons node_23732 (AllWinning.cons node_23331 (AllWinning.cons node_22866 (AllWinning.cons node_22304 (AllWinning.nil))))))))))))

theorem node_24140 : Outcome ⟨16, 13, 11, 10⟩ true :=
  Outcome.win (q := ⟨16, 7, 11, 12⟩) (by decide) node_21066

theorem node_24141 : Outcome ⟨16, 13, 11, 12⟩ true :=
  Outcome.win (q := ⟨16, 7, 11, 12⟩) (by decide) node_21066

theorem node_24142 : Outcome ⟨16, 14, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 14, 10, 2⟩, ⟨14, 14, 10, 4⟩, ⟨16, 13, 10, 2⟩, ⟨16, 12, 10, 4⟩, ⟨16, 14, 9, 2⟩, ⟨16, 14, 8, 4⟩]
  exact AllWinning.cons node_23706 (AllWinning.cons node_23266 (AllWinning.cons node_23732 (AllWinning.cons node_23329 (AllWinning.cons node_23734 (AllWinning.cons node_23333 (AllWinning.nil))))))

theorem node_24143 : Outcome ⟨16, 14, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 14, 10, 2⟩, ⟨14, 14, 10, 4⟩, ⟨13, 14, 10, 6⟩, ⟨12, 14, 10, 8⟩, ⟨16, 13, 10, 2⟩, ⟨16, 12, 10, 4⟩, ⟨16, 11, 10, 6⟩, ⟨16, 10, 10, 8⟩, ⟨16, 14, 9, 2⟩, ⟨16, 14, 8, 4⟩, ⟨16, 14, 7, 6⟩, ⟨16, 14, 6, 8⟩]
  exact AllWinning.cons node_23706 (AllWinning.cons node_23266 (AllWinning.cons node_22723 (AllWinning.cons node_22115 (AllWinning.cons node_23732 (AllWinning.cons node_23329 (AllWinning.cons node_22862 (AllWinning.cons node_22297 (AllWinning.cons node_23734 (AllWinning.cons node_23333 (AllWinning.cons node_22869 (AllWinning.cons node_22307 (AllWinning.nil))))))))))))

theorem node_24144 : Outcome ⟨16, 14, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 14, 10, 2⟩, ⟨14, 14, 10, 4⟩, ⟨13, 14, 10, 6⟩, ⟨12, 14, 10, 8⟩, ⟨11, 14, 10, 10⟩, ⟨10, 14, 10, 12⟩, ⟨16, 13, 10, 2⟩, ⟨16, 12, 10, 4⟩, ⟨16, 11, 10, 6⟩, ⟨16, 10, 10, 8⟩, ⟨16, 9, 10, 10⟩, ⟨16, 8, 10, 12⟩, ⟨16, 14, 9, 2⟩, ⟨16, 14, 8, 4⟩, ⟨16, 14, 7, 6⟩, ⟨16, 14, 6, 8⟩, ⟨16, 14, 5, 10⟩, ⟨16, 14, 4, 12⟩]
  exact AllWinning.cons node_23706 (AllWinning.cons node_23266 (AllWinning.cons node_22723 (AllWinning.cons node_22115 (AllWinning.cons node_21478 (AllWinning.cons node_20760 (AllWinning.cons node_23732 (AllWinning.cons node_23329 (AllWinning.cons node_22862 (AllWinning.cons node_22297 (AllWinning.cons node_21682 (AllWinning.cons node_21069 (AllWinning.cons node_23734 (AllWinning.cons node_23333 (AllWinning.cons node_22869 (AllWinning.cons node_22307 (AllWinning.cons node_21691 (AllWinning.cons node_21087 (AllWinning.nil))))))))))))))))))

theorem node_24145 : Outcome ⟨16, 14, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 14, 10, 2⟩, ⟨14, 14, 10, 4⟩, ⟨13, 14, 10, 6⟩, ⟨12, 14, 10, 8⟩, ⟨11, 14, 10, 10⟩, ⟨10, 14, 10, 12⟩, ⟨9, 14, 10, 14⟩, ⟨8, 14, 10, 16⟩, ⟨7, 14, 10, 18⟩, ⟨6, 14, 10, 20⟩, ⟨16, 13, 10, 2⟩, ⟨16, 12, 10, 4⟩, ⟨16, 11, 10, 6⟩, ⟨16, 10, 10, 8⟩, ⟨16, 9, 10, 10⟩, ⟨16, 8, 10, 12⟩, ⟨16, 7, 10, 14⟩, ⟨16, 6, 10, 16⟩, ⟨16, 5, 10, 18⟩, ⟨16, 4, 10, 20⟩, ⟨16, 14, 9, 2⟩, ⟨16, 14, 8, 4⟩, ⟨16, 14, 7, 6⟩, ⟨16, 14, 6, 8⟩, ⟨16, 14, 5, 10⟩, ⟨16, 14, 4, 12⟩, ⟨16, 14, 3, 14⟩, ⟨16, 14, 2, 16⟩, ⟨16, 14, 1, 18⟩, ⟨16, 14, 0, 20⟩]
  exact AllWinning.cons node_23706 (AllWinning.cons node_23266 (AllWinning.cons node_22723 (AllWinning.cons node_22115 (AllWinning.cons node_21478 (AllWinning.cons node_20760 (AllWinning.cons node_19975 (AllWinning.cons node_19129 (AllWinning.cons node_18169 (AllWinning.cons node_17235 (AllWinning.cons node_23732 (AllWinning.cons node_23329 (AllWinning.cons node_22862 (AllWinning.cons node_22297 (AllWinning.cons node_21682 (AllWinning.cons node_21069 (AllWinning.cons node_20301 (AllWinning.cons node_19553 (AllWinning.cons node_18668 (AllWinning.cons node_17762 (AllWinning.cons node_23734 (AllWinning.cons node_23333 (AllWinning.cons node_22869 (AllWinning.cons node_22307 (AllWinning.cons node_21691 (AllWinning.cons node_21087 (AllWinning.cons node_20313 (AllWinning.cons node_19573 (AllWinning.cons node_18694 (AllWinning.cons node_17786 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_24146 : Outcome ⟨16, 15, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 9, 2⟩, ⟨14, 15, 9, 4⟩, ⟨16, 14, 9, 2⟩, ⟨16, 13, 9, 4⟩, ⟨16, 15, 8, 2⟩, ⟨16, 15, 7, 4⟩]
  exact AllWinning.cons node_23708 (AllWinning.cons node_23268 (AllWinning.cons node_23734 (AllWinning.cons node_23331 (AllWinning.cons node_23735 (AllWinning.cons node_23335 (AllWinning.nil))))))

theorem node_24147 : Outcome ⟨16, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 6⟩) (by decide) node_22727

theorem node_24148 : Outcome ⟨16, 15, 9, 6⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 6⟩) (by decide) node_22727

theorem node_24149 : Outcome ⟨16, 16, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 8, 2⟩, ⟨14, 16, 8, 4⟩, ⟨13, 16, 8, 6⟩, ⟨12, 16, 8, 8⟩, ⟨16, 15, 8, 2⟩, ⟨16, 14, 8, 4⟩, ⟨16, 13, 8, 6⟩, ⟨16, 12, 8, 8⟩, ⟨16, 16, 7, 2⟩, ⟨16, 16, 6, 4⟩, ⟨16, 16, 5, 6⟩, ⟨16, 16, 4, 8⟩]
  exact AllWinning.cons node_23709 (AllWinning.cons node_23270 (AllWinning.cons node_22730 (AllWinning.cons node_22121 (AllWinning.cons node_23735 (AllWinning.cons node_23333 (AllWinning.cons node_22866 (AllWinning.cons node_22301 (AllWinning.cons node_23737 (AllWinning.cons node_23338 (AllWinning.cons node_22874 (AllWinning.cons node_22310 (AllWinning.nil))))))))))))

theorem node_24150 : Outcome ⟨16, 16, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 8, 2⟩, ⟨14, 16, 8, 4⟩, ⟨13, 16, 8, 6⟩, ⟨12, 16, 8, 8⟩, ⟨11, 16, 8, 10⟩, ⟨10, 16, 8, 12⟩, ⟨16, 15, 8, 2⟩, ⟨16, 14, 8, 4⟩, ⟨16, 13, 8, 6⟩, ⟨16, 12, 8, 8⟩, ⟨16, 11, 8, 10⟩, ⟨16, 10, 8, 12⟩, ⟨16, 16, 7, 2⟩, ⟨16, 16, 6, 4⟩, ⟨16, 16, 5, 6⟩, ⟨16, 16, 4, 8⟩, ⟨16, 16, 3, 10⟩, ⟨16, 16, 2, 12⟩]
  exact AllWinning.cons node_23709 (AllWinning.cons node_23270 (AllWinning.cons node_22730 (AllWinning.cons node_22121 (AllWinning.cons node_21483 (AllWinning.cons node_20766 (AllWinning.cons node_23735 (AllWinning.cons node_23333 (AllWinning.cons node_22866 (AllWinning.cons node_22301 (AllWinning.cons node_21686 (AllWinning.cons node_21072 (AllWinning.cons node_23737 (AllWinning.cons node_23338 (AllWinning.cons node_22874 (AllWinning.cons node_22310 (AllWinning.cons node_21695 (AllWinning.cons node_21092 (AllWinning.nil))))))))))))))))))

theorem node_24151 : Outcome ⟨16, 16, 8, 10⟩ true :=
  Outcome.win (q := ⟨16, 16, 0, 16⟩) (by decide) node_19586

theorem node_24152 : Outcome ⟨16, 17, 7, 2⟩ true :=
  Outcome.win (q := ⟨15, 17, 7, 2⟩) (by decide) node_23711

theorem node_24153 : Outcome ⟨16, 17, 7, 4⟩ true :=
  Outcome.win (q := ⟨15, 17, 7, 2⟩) (by decide) node_23711

theorem node_24154 : Outcome ⟨16, 18, 6, 2⟩ true :=
  Outcome.win (q := ⟨16, 17, 6, 2⟩) (by decide) node_23740

theorem node_24155 : Outcome ⟨16, 19, 5, 6⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 12⟩) (by decide) node_20779

theorem node_24156 : Outcome ⟨16, 19, 5, 12⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 12⟩) (by decide) node_20779

theorem node_24157 : Outcome ⟨17, 4, 19, 2⟩ true :=
  Outcome.win (q := ⟨17, 2, 19, 4⟩) (by decide) node_23343

theorem node_24158 : Outcome ⟨17, 4, 19, 4⟩ true :=
  Outcome.win (q := ⟨14, 4, 19, 6⟩) (by decide) node_22743

theorem node_24159 : Outcome ⟨17, 5, 18, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 18, 2⟩) (by decide) node_23744

theorem node_24160 : Outcome ⟨17, 6, 17, 4⟩ true :=
  Outcome.win (q := ⟨16, 6, 17, 2⟩) (by decide) node_23718

theorem node_24161 : Outcome ⟨17, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 16, 2⟩) (by decide) node_23748

theorem node_24162 : Outcome ⟨17, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨17, 6, 16, 2⟩) (by decide) node_23748

theorem node_24163 : Outcome ⟨17, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 8, 15, 6⟩) (by decide) node_22755

theorem node_24164 : Outcome ⟨17, 9, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 6⟩) (by decide) node_22760

theorem node_24165 : Outcome ⟨17, 10, 13, 4⟩ true :=
  Outcome.win (q := ⟨17, 10, 10, 6⟩) (by decide) node_22894

theorem node_24166 : Outcome ⟨17, 11, 12, 4⟩ true :=
  Outcome.win (q := ⟨17, 9, 12, 4⟩) (by decide) node_23355

theorem node_24167 : Outcome ⟨17, 12, 11, 4⟩ true :=
  Outcome.win (q := ⟨17, 12, 9, 4⟩) (by decide) node_23362

theorem node_24168 : Outcome ⟨17, 13, 10, 4⟩ true :=
  Outcome.win (q := ⟨17, 10, 10, 6⟩) (by decide) node_22894

theorem node_24169 : Outcome ⟨17, 14, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 6⟩) (by decide) node_22777

theorem node_24170 : Outcome ⟨17, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 8, 6⟩) (by decide) node_22782

theorem node_24171 : Outcome ⟨17, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨17, 15, 7, 2⟩) (by decide) node_23762

theorem node_24172 : Outcome ⟨17, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨17, 15, 7, 2⟩) (by decide) node_23762

theorem node_24173 : Outcome ⟨17, 17, 6, 4⟩ true :=
  Outcome.win (q := ⟨16, 17, 6, 2⟩) (by decide) node_23740

theorem node_24174 : Outcome ⟨17, 18, 5, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 5, 2⟩) (by decide) node_23766

theorem node_24175 : Outcome ⟨17, 19, 4, 2⟩ true :=
  Outcome.win (q := ⟨17, 19, 2, 4⟩) (by decide) node_23374

theorem node_24176 : Outcome ⟨18, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨16, 3, 19, 4⟩) (by decide) node_23313

theorem node_24177 : Outcome ⟨18, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 18, 2⟩) (by decide) node_23744

theorem node_24178 : Outcome ⟨18, 4, 18, 8⟩ true :=
  Outcome.win (q := ⟨11, 4, 18, 14⟩) (by decide) node_20047

theorem node_24179 : Outcome ⟨18, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨17, 5, 17, 2⟩) (by decide) node_23745

theorem node_24180 : Outcome ⟨18, 6, 16, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 16, 2⟩) (by decide) node_23748

theorem node_24181 : Outcome ⟨18, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨18, 7, 13, 4⟩) (by decide) node_23385

theorem node_24182 : Outcome ⟨18, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨18, 3, 15, 8⟩) (by decide) node_22358

theorem node_24183 : Outcome ⟨18, 8, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 8, 14, 2⟩, ⟨16, 8, 14, 4⟩, ⟨18, 7, 14, 2⟩, ⟨18, 6, 14, 4⟩, ⟨18, 8, 13, 2⟩, ⟨18, 8, 12, 4⟩]
  exact AllWinning.cons node_23751 (AllWinning.cons node_23321 (AllWinning.cons node_23775 (AllWinning.cons node_23382 (AllWinning.cons node_23778 (AllWinning.cons node_23389 (AllWinning.nil))))))

theorem node_24184 : Outcome ⟨18, 8, 14, 8⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 12⟩) (by decide) node_21153

theorem node_24185 : Outcome ⟨18, 9, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 6⟩) (by decide) node_22815

theorem node_24186 : Outcome ⟨18, 9, 13, 8⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 6⟩) (by decide) node_22815

theorem node_24187 : Outcome ⟨18, 10, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 10, 12, 2⟩, ⟨16, 10, 12, 4⟩, ⟨18, 9, 12, 2⟩, ⟨18, 8, 12, 4⟩, ⟨18, 10, 11, 2⟩, ⟨18, 10, 10, 4⟩]
  exact AllWinning.cons node_23754 (AllWinning.cons node_23325 (AllWinning.cons node_23780 (AllWinning.cons node_23389 (AllWinning.cons node_23782 (AllWinning.cons node_23392 (AllWinning.nil))))))

theorem node_24188 : Outcome ⟨18, 10, 12, 8⟩ true :=
  Outcome.win (q := ⟨18, 10, 6, 12⟩) (by decide) node_21156

theorem node_24189 : Outcome ⟨18, 12, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 12, 10, 2⟩, ⟨16, 12, 10, 4⟩, ⟨18, 11, 10, 2⟩, ⟨18, 10, 10, 4⟩, ⟨18, 12, 9, 2⟩, ⟨18, 12, 8, 4⟩]
  exact AllWinning.cons node_23757 (AllWinning.cons node_23329 (AllWinning.cons node_23783 (AllWinning.cons node_23392 (AllWinning.cons node_23784 (AllWinning.cons node_23395 (AllWinning.nil))))))

theorem node_24190 : Outcome ⟨18, 12, 10, 8⟩ true :=
  Outcome.win (q := ⟨18, 6, 10, 12⟩) (by decide) node_21148

theorem node_24191 : Outcome ⟨18, 13, 9, 4⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 6⟩) (by decide) node_22826

theorem node_24192 : Outcome ⟨18, 13, 9, 8⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 6⟩) (by decide) node_22826

theorem node_24193 : Outcome ⟨18, 14, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 14, 8, 2⟩, ⟨16, 14, 8, 4⟩, ⟨18, 13, 8, 2⟩, ⟨18, 12, 8, 4⟩, ⟨18, 14, 7, 2⟩, ⟨18, 14, 6, 4⟩]
  exact AllWinning.cons node_23760 (AllWinning.cons node_23333 (AllWinning.cons node_23786 (AllWinning.cons node_23395 (AllWinning.cons node_23788 (AllWinning.cons node_23401 (AllWinning.nil))))))

theorem node_24194 : Outcome ⟨18, 14, 8, 8⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 12⟩) (by decide) node_21153

theorem node_24195 : Outcome ⟨18, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 7, 4⟩) (by decide) node_23398

theorem node_24196 : Outcome ⟨18, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨18, 15, 3, 8⟩) (by decide) node_22374

theorem node_24197 : Outcome ⟨18, 16, 6, 2⟩ true :=
  Outcome.win (q := ⟨17, 16, 6, 2⟩) (by decide) node_23763

theorem node_24198 : Outcome ⟨18, 17, 5, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 5, 2⟩) (by decide) node_23766

theorem node_24199 : Outcome ⟨18, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨17, 18, 4, 2⟩) (by decide) node_23769

theorem node_24200 : Outcome ⟨18, 18, 4, 8⟩ true :=
  Outcome.win (q := ⟨11, 18, 4, 14⟩) (by decide) node_20077

theorem node_24201 : Outcome ⟨18, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨16, 19, 3, 4⟩) (by decide) node_23342

theorem node_24202 : Outcome ⟨19, 2, 19, 6⟩ true :=
  Outcome.win (q := ⟨17, 2, 19, 4⟩) (by decide) node_23343

theorem node_24203 : Outcome ⟨19, 5, 16, 6⟩ true :=
  Outcome.win (q := ⟨19, 5, 10, 12⟩) (by decide) node_21174

theorem node_24204 : Outcome ⟨19, 5, 16, 12⟩ true :=
  Outcome.win (q := ⟨19, 5, 10, 12⟩) (by decide) node_21174

theorem node_24205 : Outcome ⟨19, 7, 14, 4⟩ true :=
  Outcome.win (q := ⟨19, 4, 14, 6⟩) (by decide) node_22930

theorem node_24206 : Outcome ⟨19, 8, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 8, 13, 2⟩, ⟨17, 8, 13, 4⟩, ⟨19, 7, 13, 2⟩, ⟨19, 6, 13, 4⟩, ⟨19, 8, 12, 2⟩, ⟨19, 8, 11, 4⟩]
  exact AllWinning.cons node_23778 (AllWinning.cons node_23352 (AllWinning.cons node_23798 (AllWinning.cons node_23412 (AllWinning.cons node_23799 (AllWinning.cons node_23413 (AllWinning.nil))))))

theorem node_24207 : Outcome ⟨19, 8, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 8, 13, 2⟩, ⟨17, 8, 13, 4⟩, ⟨16, 8, 13, 6⟩, ⟨15, 8, 13, 8⟩, ⟨19, 7, 13, 2⟩, ⟨19, 6, 13, 4⟩, ⟨19, 5, 13, 6⟩, ⟨19, 4, 13, 8⟩, ⟨19, 8, 12, 2⟩, ⟨19, 8, 11, 4⟩, ⟨19, 8, 10, 6⟩, ⟨19, 8, 9, 8⟩]
  exact AllWinning.cons node_23778 (AllWinning.cons node_23352 (AllWinning.cons node_22854 (AllWinning.cons node_22239 (AllWinning.cons node_23798 (AllWinning.cons node_23412 (AllWinning.cons node_22933 (AllWinning.cons node_22385 (AllWinning.cons node_23799 (AllWinning.cons node_23413 (AllWinning.cons node_22935 (AllWinning.cons node_22389 (AllWinning.nil))))))))))))

theorem node_24208 : Outcome ⟨19, 8, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 8, 13, 2⟩, ⟨17, 8, 13, 4⟩, ⟨16, 8, 13, 6⟩, ⟨15, 8, 13, 8⟩, ⟨14, 8, 13, 10⟩, ⟨13, 8, 13, 12⟩, ⟨19, 7, 13, 2⟩, ⟨19, 6, 13, 4⟩, ⟨19, 5, 13, 6⟩, ⟨19, 4, 13, 8⟩, ⟨19, 3, 13, 10⟩, ⟨19, 2, 13, 12⟩, ⟨19, 8, 12, 2⟩, ⟨19, 8, 11, 4⟩, ⟨19, 8, 10, 6⟩, ⟨19, 8, 9, 8⟩, ⟨19, 8, 8, 10⟩, ⟨19, 8, 7, 12⟩]
  exact AllWinning.cons node_23778 (AllWinning.cons node_23352 (AllWinning.cons node_22854 (AllWinning.cons node_22239 (AllWinning.cons node_21594 (AllWinning.cons node_20897 (AllWinning.cons node_23798 (AllWinning.cons node_23412 (AllWinning.cons node_22933 (AllWinning.cons node_22385 (AllWinning.cons node_21765 (AllWinning.cons node_21168 (AllWinning.cons node_23799 (AllWinning.cons node_23413 (AllWinning.cons node_22935 (AllWinning.cons node_22389 (AllWinning.cons node_21768 (AllWinning.cons node_21176 (AllWinning.nil))))))))))))))))))

theorem node_24209 : Outcome ⟨19, 8, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 8, 13, 2⟩, ⟨17, 8, 13, 4⟩, ⟨16, 8, 13, 6⟩, ⟨15, 8, 13, 8⟩, ⟨14, 8, 13, 10⟩, ⟨13, 8, 13, 12⟩, ⟨12, 8, 13, 14⟩, ⟨11, 8, 13, 16⟩, ⟨19, 7, 13, 2⟩, ⟨19, 6, 13, 4⟩, ⟨19, 5, 13, 6⟩, ⟨19, 4, 13, 8⟩, ⟨19, 3, 13, 10⟩, ⟨19, 2, 13, 12⟩, ⟨19, 1, 13, 14⟩, ⟨19, 0, 13, 16⟩, ⟨19, 8, 12, 2⟩, ⟨19, 8, 11, 4⟩, ⟨19, 8, 10, 6⟩, ⟨19, 8, 9, 8⟩, ⟨19, 8, 8, 10⟩, ⟨19, 8, 7, 12⟩, ⟨19, 8, 6, 14⟩, ⟨19, 8, 5, 16⟩]
  exact AllWinning.cons node_23778 (AllWinning.cons node_23352 (AllWinning.cons node_22854 (AllWinning.cons node_22239 (AllWinning.cons node_21594 (AllWinning.cons node_20897 (AllWinning.cons node_20099 (AllWinning.cons node_19273 (AllWinning.cons node_23798 (AllWinning.cons node_23412 (AllWinning.cons node_22933 (AllWinning.cons node_22385 (AllWinning.cons node_21765 (AllWinning.cons node_21168 (AllWinning.cons node_20383 (AllWinning.cons node_19658 (AllWinning.cons node_23799 (AllWinning.cons node_23413 (AllWinning.cons node_22935 (AllWinning.cons node_22389 (AllWinning.cons node_21768 (AllWinning.cons node_21176 (AllWinning.cons node_20391 (AllWinning.cons node_19675 (AllWinning.nil))))))))))))))))))))))))

theorem node_24210 : Outcome ⟨19, 9, 12, 4⟩ true :=
  Outcome.win (q := ⟨17, 9, 12, 4⟩) (by decide) node_23355

theorem node_24211 : Outcome ⟨19, 9, 12, 6⟩ true :=
  Outcome.win (q := ⟨17, 9, 12, 4⟩) (by decide) node_23355

theorem node_24212 : Outcome ⟨19, 10, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 11, 2⟩, ⟨17, 10, 11, 4⟩, ⟨19, 9, 11, 2⟩, ⟨19, 8, 11, 4⟩, ⟨19, 10, 10, 2⟩, ⟨19, 10, 9, 4⟩]
  exact AllWinning.cons node_23782 (AllWinning.cons node_23357 (AllWinning.cons node_23801 (AllWinning.cons node_23413 (AllWinning.cons node_23802 (AllWinning.cons node_23415 (AllWinning.nil))))))

theorem node_24213 : Outcome ⟨19, 10, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 11, 2⟩, ⟨17, 10, 11, 4⟩, ⟨16, 10, 11, 6⟩, ⟨15, 10, 11, 8⟩, ⟨19, 9, 11, 2⟩, ⟨19, 8, 11, 4⟩, ⟨19, 7, 11, 6⟩, ⟨19, 6, 11, 8⟩, ⟨19, 10, 10, 2⟩, ⟨19, 10, 9, 4⟩, ⟨19, 10, 8, 6⟩, ⟨19, 10, 7, 8⟩]
  exact AllWinning.cons node_23782 (AllWinning.cons node_23357 (AllWinning.cons node_22860 (AllWinning.cons node_22246 (AllWinning.cons node_23801 (AllWinning.cons node_23413 (AllWinning.cons node_22934 (AllWinning.cons node_22387 (AllWinning.cons node_23802 (AllWinning.cons node_23415 (AllWinning.cons node_22936 (AllWinning.cons node_22391 (AllWinning.nil))))))))))))

theorem node_24214 : Outcome ⟨19, 10, 11, 12⟩ true :=
  Outcome.win (q := ⟨8, 10, 11, 22⟩) (by decide) node_16364

theorem node_24215 : Outcome ⟨19, 11, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 11, 10, 2⟩, ⟨17, 11, 10, 4⟩, ⟨16, 11, 10, 6⟩, ⟨15, 11, 10, 8⟩, ⟨19, 10, 10, 2⟩, ⟨19, 9, 10, 4⟩, ⟨19, 8, 10, 6⟩, ⟨19, 7, 10, 8⟩, ⟨19, 11, 9, 2⟩, ⟨19, 11, 8, 4⟩, ⟨19, 11, 7, 6⟩, ⟨19, 11, 6, 8⟩]
  exact AllWinning.cons node_23783 (AllWinning.cons node_23359 (AllWinning.cons node_22862 (AllWinning.cons node_22249 (AllWinning.cons node_23802 (AllWinning.cons node_23414 (AllWinning.cons node_22935 (AllWinning.cons node_22388 (AllWinning.cons node_23803 (AllWinning.cons node_23416 (AllWinning.cons node_22937 (AllWinning.cons node_22392 (AllWinning.nil))))))))))))

theorem node_24216 : Outcome ⟨19, 11, 10, 12⟩ true :=
  Outcome.win (q := ⟨8, 11, 10, 22⟩) (by decide) node_16370

theorem node_24217 : Outcome ⟨19, 12, 9, 4⟩ true :=
  Outcome.win (q := ⟨17, 12, 9, 4⟩) (by decide) node_23362

theorem node_24218 : Outcome ⟨19, 12, 9, 6⟩ true :=
  Outcome.win (q := ⟨17, 12, 9, 4⟩) (by decide) node_23362

theorem node_24219 : Outcome ⟨19, 13, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 8, 2⟩, ⟨17, 13, 8, 4⟩, ⟨19, 12, 8, 2⟩, ⟨19, 11, 8, 4⟩, ⟨19, 13, 7, 2⟩, ⟨19, 13, 6, 4⟩]
  exact AllWinning.cons node_23786 (AllWinning.cons node_23364 (AllWinning.cons node_23804 (AllWinning.cons node_23416 (AllWinning.cons node_23806 (AllWinning.cons node_23417 (AllWinning.nil))))))

theorem node_24220 : Outcome ⟨19, 13, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 8, 2⟩, ⟨17, 13, 8, 4⟩, ⟨16, 13, 8, 6⟩, ⟨15, 13, 8, 8⟩, ⟨19, 12, 8, 2⟩, ⟨19, 11, 8, 4⟩, ⟨19, 10, 8, 6⟩, ⟨19, 9, 8, 8⟩, ⟨19, 13, 7, 2⟩, ⟨19, 13, 6, 4⟩, ⟨19, 13, 5, 6⟩, ⟨19, 13, 4, 8⟩]
  exact AllWinning.cons node_23786 (AllWinning.cons node_23364 (AllWinning.cons node_22866 (AllWinning.cons node_22254 (AllWinning.cons node_23804 (AllWinning.cons node_23416 (AllWinning.cons node_22936 (AllWinning.cons node_22390 (AllWinning.cons node_23806 (AllWinning.cons node_23417 (AllWinning.cons node_22939 (AllWinning.cons node_22395 (AllWinning.nil))))))))))))

theorem node_24221 : Outcome ⟨19, 13, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 8, 2⟩, ⟨17, 13, 8, 4⟩, ⟨16, 13, 8, 6⟩, ⟨15, 13, 8, 8⟩, ⟨14, 13, 8, 10⟩, ⟨13, 13, 8, 12⟩, ⟨19, 12, 8, 2⟩, ⟨19, 11, 8, 4⟩, ⟨19, 10, 8, 6⟩, ⟨19, 9, 8, 8⟩, ⟨19, 8, 8, 10⟩, ⟨19, 7, 8, 12⟩, ⟨19, 13, 7, 2⟩, ⟨19, 13, 6, 4⟩, ⟨19, 13, 5, 6⟩, ⟨19, 13, 4, 8⟩, ⟨19, 13, 3, 10⟩, ⟨19, 13, 2, 12⟩]
  exact AllWinning.cons node_23786 (AllWinning.cons node_23364 (AllWinning.cons node_22866 (AllWinning.cons node_22254 (AllWinning.cons node_21606 (AllWinning.cons node_20913 (AllWinning.cons node_23804 (AllWinning.cons node_23416 (AllWinning.cons node_22936 (AllWinning.cons node_22390 (AllWinning.cons node_21768 (AllWinning.cons node_21175 (AllWinning.cons node_23806 (AllWinning.cons node_23417 (AllWinning.cons node_22939 (AllWinning.cons node_22395 (AllWinning.cons node_21772 (AllWinning.cons node_21185 (AllWinning.nil))))))))))))))))))

theorem node_24222 : Outcome ⟨19, 13, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 8, 2⟩, ⟨17, 13, 8, 4⟩, ⟨16, 13, 8, 6⟩, ⟨15, 13, 8, 8⟩, ⟨14, 13, 8, 10⟩, ⟨13, 13, 8, 12⟩, ⟨12, 13, 8, 14⟩, ⟨11, 13, 8, 16⟩, ⟨19, 12, 8, 2⟩, ⟨19, 11, 8, 4⟩, ⟨19, 10, 8, 6⟩, ⟨19, 9, 8, 8⟩, ⟨19, 8, 8, 10⟩, ⟨19, 7, 8, 12⟩, ⟨19, 6, 8, 14⟩, ⟨19, 5, 8, 16⟩, ⟨19, 13, 7, 2⟩, ⟨19, 13, 6, 4⟩, ⟨19, 13, 5, 6⟩, ⟨19, 13, 4, 8⟩, ⟨19, 13, 3, 10⟩, ⟨19, 13, 2, 12⟩, ⟨19, 13, 1, 14⟩, ⟨19, 13, 0, 16⟩]
  exact AllWinning.cons node_23786 (AllWinning.cons node_23364 (AllWinning.cons node_22866 (AllWinning.cons node_22254 (AllWinning.cons node_21606 (AllWinning.cons node_20913 (AllWinning.cons node_20111 (AllWinning.cons node_19285 (AllWinning.cons node_23804 (AllWinning.cons node_23416 (AllWinning.cons node_22936 (AllWinning.cons node_22390 (AllWinning.cons node_21768 (AllWinning.cons node_21175 (AllWinning.cons node_20390 (AllWinning.cons node_19669 (AllWinning.cons node_23806 (AllWinning.cons node_23417 (AllWinning.cons node_22939 (AllWinning.cons node_22395 (AllWinning.cons node_21772 (AllWinning.cons node_21185 (AllWinning.cons node_20399 (AllWinning.cons node_19688 (AllWinning.nil))))))))))))))))))))))))

theorem node_24223 : Outcome ⟨19, 14, 7, 4⟩ true :=
  Outcome.win (q := ⟨19, 14, 4, 6⟩) (by decide) node_22940

theorem node_24224 : Outcome ⟨19, 16, 5, 6⟩ true :=
  Outcome.win (q := ⟨19, 10, 5, 12⟩) (by decide) node_21181

theorem node_24225 : Outcome ⟨19, 16, 5, 12⟩ true :=
  Outcome.win (q := ⟨19, 10, 5, 12⟩) (by decide) node_21181

theorem node_24226 : Outcome ⟨19, 19, 2, 6⟩ true :=
  Outcome.win (q := ⟨17, 19, 2, 4⟩) (by decide) node_23374

theorem node_24227 : Outcome ⟨1, 20, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 20, 20, 2⟩) (by decide) node_23809

theorem node_24228 : Outcome ⟨1, 20, 20, 8⟩ true :=
  Outcome.win (q := ⟨0, 20, 20, 2⟩) (by decide) node_23809

theorem node_24229 : Outcome ⟨2, 19, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 19, 17, 6⟩) (by decide) node_22974

theorem node_24230 : Outcome ⟨2, 20, 19, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 19, 6⟩) (by decide) node_22967

theorem node_24231 : Outcome ⟨3, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 18, 20, 2⟩) (by decide) node_23814

theorem node_24232 : Outcome ⟨3, 18, 20, 12⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 10⟩) (by decide) node_21843

theorem node_24233 : Outcome ⟨3, 19, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 19, 19, 2⟩, ⟨1, 19, 19, 4⟩, ⟨3, 18, 19, 2⟩, ⟨3, 17, 19, 4⟩, ⟨3, 19, 18, 2⟩, ⟨3, 19, 17, 4⟩]
  exact AllWinning.cons node_23816 (AllWinning.cons node_23427 (AllWinning.cons node_23823 (AllWinning.cons node_23440 (AllWinning.cons node_23825 (AllWinning.cons node_23445 (AllWinning.nil))))))

theorem node_24234 : Outcome ⟨3, 19, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 6⟩) (by decide) node_22948

theorem node_24235 : Outcome ⟨3, 19, 19, 10⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 6⟩) (by decide) node_22948

theorem node_24236 : Outcome ⟨3, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 20, 18, 2⟩) (by decide) node_23819

theorem node_24237 : Outcome ⟨3, 20, 18, 12⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 10⟩) (by decide) node_21830

theorem node_24238 : Outcome ⟨4, 17, 20, 4⟩ true :=
  Outcome.win (q := ⟨3, 17, 20, 2⟩) (by decide) node_23821

theorem node_24239 : Outcome ⟨4, 18, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 19, 2⟩, ⟨2, 18, 19, 4⟩, ⟨4, 17, 19, 2⟩, ⟨4, 16, 19, 4⟩, ⟨4, 18, 18, 2⟩, ⟨4, 18, 17, 4⟩]
  exact AllWinning.cons node_23823 (AllWinning.cons node_23433 (AllWinning.cons node_23831 (AllWinning.cons node_23452 (AllWinning.cons node_23833 (AllWinning.cons node_23456 (AllWinning.nil))))))

theorem node_24240 : Outcome ⟨4, 18, 19, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 8⟩) (by decide) node_22439

theorem node_24241 : Outcome ⟨4, 18, 19, 6⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 8⟩) (by decide) node_22439

theorem node_24242 : Outcome ⟨4, 19, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 19, 18, 2⟩, ⟨2, 19, 18, 4⟩, ⟨4, 18, 18, 2⟩, ⟨4, 17, 18, 4⟩, ⟨4, 19, 17, 2⟩, ⟨4, 19, 16, 4⟩]
  exact AllWinning.cons node_23825 (AllWinning.cons node_23435 (AllWinning.cons node_23833 (AllWinning.cons node_23454 (AllWinning.cons node_23835 (AllWinning.cons node_23458 (AllWinning.nil))))))

theorem node_24243 : Outcome ⟨4, 19, 18, 4⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 8⟩) (by decide) node_22451

theorem node_24244 : Outcome ⟨4, 19, 18, 6⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 8⟩) (by decide) node_22451

theorem node_24245 : Outcome ⟨4, 20, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 20, 17, 2⟩) (by decide) node_23827

theorem node_24246 : Outcome ⟨5, 16, 20, 4⟩ true :=
  Outcome.win (q := ⟨4, 16, 20, 2⟩) (by decide) node_23829

theorem node_24247 : Outcome ⟨5, 16, 20, 8⟩ true :=
  Outcome.win (q := ⟨4, 16, 20, 2⟩) (by decide) node_23829

theorem node_24248 : Outcome ⟨5, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 19, 4⟩) (by decide) node_23463

theorem node_24249 : Outcome ⟨5, 17, 19, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 19, 6⟩) (by decide) node_22967

theorem node_24250 : Outcome ⟨5, 18, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 18, 2⟩, ⟨3, 18, 18, 4⟩, ⟨5, 17, 18, 2⟩, ⟨5, 16, 18, 4⟩, ⟨5, 18, 17, 2⟩, ⟨5, 18, 16, 4⟩]
  exact AllWinning.cons node_23833 (AllWinning.cons node_23442 (AllWinning.cons node_23843 (AllWinning.cons node_23465 (AllWinning.cons node_23844 (AllWinning.cons node_23469 (AllWinning.nil))))))

theorem node_24251 : Outcome ⟨5, 18, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 18, 2⟩, ⟨3, 18, 18, 4⟩, ⟨2, 18, 18, 6⟩, ⟨1, 18, 18, 8⟩, ⟨5, 17, 18, 2⟩, ⟨5, 16, 18, 4⟩, ⟨5, 15, 18, 6⟩, ⟨5, 14, 18, 8⟩, ⟨5, 18, 17, 2⟩, ⟨5, 18, 16, 4⟩, ⟨5, 18, 15, 6⟩, ⟨5, 18, 14, 8⟩]
  exact AllWinning.cons node_23833 (AllWinning.cons node_23442 (AllWinning.cons node_22970 (AllWinning.cons node_22409 (AllWinning.cons node_23843 (AllWinning.cons node_23465 (AllWinning.cons node_23003 (AllWinning.cons node_22464 (AllWinning.cons node_23844 (AllWinning.cons node_23469 (AllWinning.cons node_23010 (AllWinning.cons node_22473 (AllWinning.nil))))))))))))

theorem node_24252 : Outcome ⟨5, 18, 18, 6⟩ true :=
  Outcome.win (q := ⟨5, 12, 18, 12⟩) (by decide) node_21283

theorem node_24253 : Outcome ⟨5, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 17, 17, 4⟩) (by decide) node_23467

theorem node_24254 : Outcome ⟨5, 19, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 19, 17, 6⟩) (by decide) node_22974

theorem node_24255 : Outcome ⟨5, 20, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 20, 16, 2⟩) (by decide) node_23837

theorem node_24256 : Outcome ⟨5, 20, 16, 8⟩ true :=
  Outcome.win (q := ⟨4, 20, 16, 2⟩) (by decide) node_23837

theorem node_24257 : Outcome ⟨6, 15, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 20, 2⟩, ⟨4, 15, 20, 4⟩, ⟨6, 14, 20, 2⟩, ⟨6, 13, 20, 4⟩, ⟨6, 15, 19, 2⟩, ⟨6, 15, 18, 4⟩]
  exact AllWinning.cons node_23839 (AllWinning.cons node_23449 (AllWinning.cons node_23849 (AllWinning.cons node_23474 (AllWinning.cons node_23850 (AllWinning.cons node_23477 (AllWinning.nil))))))

theorem node_24258 : Outcome ⟨6, 15, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 20, 2⟩, ⟨4, 15, 20, 4⟩, ⟨3, 15, 20, 6⟩, ⟨2, 15, 20, 8⟩, ⟨6, 14, 20, 2⟩, ⟨6, 13, 20, 4⟩, ⟨6, 12, 20, 6⟩, ⟨6, 11, 20, 8⟩, ⟨6, 15, 19, 2⟩, ⟨6, 15, 18, 4⟩, ⟨6, 15, 17, 6⟩, ⟨6, 15, 16, 8⟩]
  exact AllWinning.cons node_23839 (AllWinning.cons node_23449 (AllWinning.cons node_22978 (AllWinning.cons node_22414 (AllWinning.cons node_23849 (AllWinning.cons node_23474 (AllWinning.cons node_23018 (AllWinning.cons node_22481 (AllWinning.cons node_23850 (AllWinning.cons node_23477 (AllWinning.cons node_23024 (AllWinning.cons node_22490 (AllWinning.nil))))))))))))

theorem node_24259 : Outcome ⟨6, 15, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 20, 2⟩, ⟨4, 15, 20, 4⟩, ⟨3, 15, 20, 6⟩, ⟨2, 15, 20, 8⟩, ⟨1, 15, 20, 10⟩, ⟨0, 15, 20, 12⟩, ⟨6, 14, 20, 2⟩, ⟨6, 13, 20, 4⟩, ⟨6, 12, 20, 6⟩, ⟨6, 11, 20, 8⟩, ⟨6, 10, 20, 10⟩, ⟨6, 9, 20, 12⟩, ⟨6, 15, 19, 2⟩, ⟨6, 15, 18, 4⟩, ⟨6, 15, 17, 6⟩, ⟨6, 15, 16, 8⟩, ⟨6, 15, 15, 10⟩, ⟨6, 15, 14, 12⟩]
  exact AllWinning.cons node_23839 (AllWinning.cons node_23449 (AllWinning.cons node_22978 (AllWinning.cons node_22414 (AllWinning.cons node_21790 (AllWinning.cons node_21191 (AllWinning.cons node_23849 (AllWinning.cons node_23474 (AllWinning.cons node_23018 (AllWinning.cons node_22481 (AllWinning.cons node_21899 (AllWinning.cons node_21309 (AllWinning.cons node_23850 (AllWinning.cons node_23477 (AllWinning.cons node_23024 (AllWinning.cons node_22490 (AllWinning.cons node_21913 (AllWinning.cons node_21323 (AllWinning.nil))))))))))))))))))

theorem node_24260 : Outcome ⟨6, 15, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 20, 2⟩, ⟨4, 15, 20, 4⟩, ⟨3, 15, 20, 6⟩, ⟨2, 15, 20, 8⟩, ⟨1, 15, 20, 10⟩, ⟨0, 15, 20, 12⟩, ⟨6, 14, 20, 2⟩, ⟨6, 13, 20, 4⟩, ⟨6, 12, 20, 6⟩, ⟨6, 11, 20, 8⟩, ⟨6, 10, 20, 10⟩, ⟨6, 9, 20, 12⟩, ⟨6, 8, 20, 14⟩, ⟨6, 7, 20, 16⟩, ⟨6, 15, 19, 2⟩, ⟨6, 15, 18, 4⟩, ⟨6, 15, 17, 6⟩, ⟨6, 15, 16, 8⟩, ⟨6, 15, 15, 10⟩, ⟨6, 15, 14, 12⟩, ⟨6, 15, 13, 14⟩, ⟨6, 15, 12, 16⟩]
  exact AllWinning.cons node_23839 (AllWinning.cons node_23449 (AllWinning.cons node_22978 (AllWinning.cons node_22414 (AllWinning.cons node_21790 (AllWinning.cons node_21191 (AllWinning.cons node_23849 (AllWinning.cons node_23474 (AllWinning.cons node_23018 (AllWinning.cons node_22481 (AllWinning.cons node_21899 (AllWinning.cons node_21309 (AllWinning.cons node_20547 (AllWinning.cons node_19856 (AllWinning.cons node_23850 (AllWinning.cons node_23477 (AllWinning.cons node_23024 (AllWinning.cons node_22490 (AllWinning.cons node_21913 (AllWinning.cons node_21323 (AllWinning.cons node_20571 (AllWinning.cons node_19879 (AllWinning.nil))))))))))))))))))))))

theorem node_24261 : Outcome ⟨6, 15, 20, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 18⟩) (by decide) node_19003

theorem node_24262 : Outcome ⟨6, 16, 19, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 17, 4⟩) (by decide) node_23480

theorem node_24263 : Outcome ⟨6, 16, 19, 10⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 14⟩) (by decide) node_20578

theorem node_24264 : Outcome ⟨6, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 16, 4⟩) (by decide) node_23483

theorem node_24265 : Outcome ⟨6, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 17, 4⟩) (by decide) node_23480

theorem node_24266 : Outcome ⟨6, 19, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 16, 4⟩) (by decide) node_23483

theorem node_24267 : Outcome ⟨6, 19, 16, 10⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 14⟩) (by decide) node_20562

theorem node_24268 : Outcome ⟨6, 20, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 20, 15, 2⟩, ⟨4, 20, 15, 4⟩, ⟨6, 19, 15, 2⟩, ⟨6, 18, 15, 4⟩, ⟨6, 20, 14, 2⟩, ⟨6, 20, 13, 4⟩]
  exact AllWinning.cons node_23847 (AllWinning.cons node_23460 (AllWinning.cons node_23855 (AllWinning.cons node_23485 (AllWinning.cons node_23857 (AllWinning.cons node_23489 (AllWinning.nil))))))

theorem node_24269 : Outcome ⟨6, 20, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 20, 15, 2⟩, ⟨4, 20, 15, 4⟩, ⟨3, 20, 15, 6⟩, ⟨2, 20, 15, 8⟩, ⟨6, 19, 15, 2⟩, ⟨6, 18, 15, 4⟩, ⟨6, 17, 15, 6⟩, ⟨6, 16, 15, 8⟩, ⟨6, 20, 14, 2⟩, ⟨6, 20, 13, 4⟩, ⟨6, 20, 12, 6⟩, ⟨6, 20, 11, 8⟩]
  exact AllWinning.cons node_23847 (AllWinning.cons node_23460 (AllWinning.cons node_22985 (AllWinning.cons node_22421 (AllWinning.cons node_23855 (AllWinning.cons node_23485 (AllWinning.cons node_23029 (AllWinning.cons node_22493 (AllWinning.cons node_23857 (AllWinning.cons node_23489 (AllWinning.cons node_23036 (AllWinning.cons node_22502 (AllWinning.nil))))))))))))

theorem node_24270 : Outcome ⟨6, 20, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 20, 15, 2⟩, ⟨4, 20, 15, 4⟩, ⟨3, 20, 15, 6⟩, ⟨2, 20, 15, 8⟩, ⟨1, 20, 15, 10⟩, ⟨0, 20, 15, 12⟩, ⟨6, 19, 15, 2⟩, ⟨6, 18, 15, 4⟩, ⟨6, 17, 15, 6⟩, ⟨6, 16, 15, 8⟩, ⟨6, 15, 15, 10⟩, ⟨6, 14, 15, 12⟩, ⟨6, 20, 14, 2⟩, ⟨6, 20, 13, 4⟩, ⟨6, 20, 12, 6⟩, ⟨6, 20, 11, 8⟩, ⟨6, 20, 10, 10⟩, ⟨6, 20, 9, 12⟩]
  exact AllWinning.cons node_23847 (AllWinning.cons node_23460 (AllWinning.cons node_22985 (AllWinning.cons node_22421 (AllWinning.cons node_21800 (AllWinning.cons node_21199 (AllWinning.cons node_23855 (AllWinning.cons node_23485 (AllWinning.cons node_23029 (AllWinning.cons node_22493 (AllWinning.cons node_21913 (AllWinning.cons node_21320 (AllWinning.cons node_23857 (AllWinning.cons node_23489 (AllWinning.cons node_23036 (AllWinning.cons node_22502 (AllWinning.cons node_21927 (AllWinning.cons node_21335 (AllWinning.nil))))))))))))))))))

theorem node_24271 : Outcome ⟨6, 20, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 20, 15, 2⟩, ⟨4, 20, 15, 4⟩, ⟨3, 20, 15, 6⟩, ⟨2, 20, 15, 8⟩, ⟨1, 20, 15, 10⟩, ⟨0, 20, 15, 12⟩, ⟨6, 19, 15, 2⟩, ⟨6, 18, 15, 4⟩, ⟨6, 17, 15, 6⟩, ⟨6, 16, 15, 8⟩, ⟨6, 15, 15, 10⟩, ⟨6, 14, 15, 12⟩, ⟨6, 13, 15, 14⟩, ⟨6, 12, 15, 16⟩, ⟨6, 20, 14, 2⟩, ⟨6, 20, 13, 4⟩, ⟨6, 20, 12, 6⟩, ⟨6, 20, 11, 8⟩, ⟨6, 20, 10, 10⟩, ⟨6, 20, 9, 12⟩, ⟨6, 20, 8, 14⟩, ⟨6, 20, 7, 16⟩]
  exact AllWinning.cons node_23847 (AllWinning.cons node_23460 (AllWinning.cons node_22985 (AllWinning.cons node_22421 (AllWinning.cons node_21800 (AllWinning.cons node_21199 (AllWinning.cons node_23855 (AllWinning.cons node_23485 (AllWinning.cons node_23029 (AllWinning.cons node_22493 (AllWinning.cons node_21913 (AllWinning.cons node_21320 (AllWinning.cons node_20566 (AllWinning.cons node_19863 (AllWinning.cons node_23857 (AllWinning.cons node_23489 (AllWinning.cons node_23036 (AllWinning.cons node_22502 (AllWinning.cons node_21927 (AllWinning.cons node_21335 (AllWinning.cons node_20589 (AllWinning.cons node_19886 (AllWinning.nil))))))))))))))))))))))

theorem node_24272 : Outcome ⟨6, 20, 15, 14⟩ true :=
  Outcome.win (q := ⟨6, 20, 6, 18⟩) (by decide) node_19052

theorem node_24273 : Outcome ⟨7, 14, 20, 4⟩ true :=
  Outcome.win (q := ⟨7, 14, 19, 2⟩) (by decide) node_23861

theorem node_24274 : Outcome ⟨7, 15, 19, 6⟩ true :=
  Outcome.win (q := ⟨5, 15, 19, 4⟩) (by decide) node_23463

theorem node_24275 : Outcome ⟨7, 16, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 18, 2⟩, ⟨5, 16, 18, 4⟩, ⟨7, 15, 18, 2⟩, ⟨7, 14, 18, 4⟩, ⟨7, 16, 17, 2⟩, ⟨7, 16, 16, 4⟩]
  exact AllWinning.cons node_23852 (AllWinning.cons node_23465 (AllWinning.cons node_23864 (AllWinning.cons node_23494 (AllWinning.cons node_23867 (AllWinning.cons node_23497 (AllWinning.nil))))))

theorem node_24276 : Outcome ⟨7, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨7, 13, 18, 6⟩) (by decide) node_23045

theorem node_24277 : Outcome ⟨7, 16, 18, 6⟩ true :=
  Outcome.win (q := ⟨2, 16, 18, 10⟩) (by decide) node_21808

theorem node_24278 : Outcome ⟨7, 16, 18, 16⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 14⟩) (by decide) node_20631

theorem node_24279 : Outcome ⟨7, 17, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 17, 17, 4⟩) (by decide) node_23467

theorem node_24280 : Outcome ⟨7, 18, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 16, 2⟩, ⟨5, 18, 16, 4⟩, ⟨7, 17, 16, 2⟩, ⟨7, 16, 16, 4⟩, ⟨7, 18, 15, 2⟩, ⟨7, 18, 14, 4⟩]
  exact AllWinning.cons node_23854 (AllWinning.cons node_23469 (AllWinning.cons node_23870 (AllWinning.cons node_23497 (AllWinning.cons node_23873 (AllWinning.cons node_23501 (AllWinning.nil))))))

theorem node_24281 : Outcome ⟨7, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 18, 13, 6⟩) (by decide) node_23057

theorem node_24282 : Outcome ⟨7, 18, 16, 6⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 10⟩) (by decide) node_21818

theorem node_24283 : Outcome ⟨7, 18, 16, 16⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 14⟩) (by decide) node_20605

theorem node_24284 : Outcome ⟨7, 19, 15, 6⟩ true :=
  Outcome.win (q := ⟨5, 19, 15, 4⟩) (by decide) node_23471

theorem node_24285 : Outcome ⟨7, 20, 14, 4⟩ true :=
  Outcome.win (q := ⟨7, 19, 14, 2⟩) (by decide) node_23876

theorem node_24286 : Outcome ⟨8, 13, 20, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 20, 2⟩) (by decide) node_23882

theorem node_24287 : Outcome ⟨8, 13, 20, 14⟩ true :=
  Outcome.win (q := ⟨8, 7, 20, 12⟩) (by decide) node_21365

theorem node_24288 : Outcome ⟨8, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 14, 19, 2⟩) (by decide) node_23861

theorem node_24289 : Outcome ⟨8, 14, 19, 10⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 8⟩) (by decide) node_22439

theorem node_24290 : Outcome ⟨8, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 18, 2⟩) (by decide) node_23889

theorem node_24291 : Outcome ⟨8, 15, 18, 6⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 10⟩) (by decide) node_21830

theorem node_24292 : Outcome ⟨8, 15, 18, 16⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 26⟩) (by decide) node_15377

theorem node_24293 : Outcome ⟨8, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 17, 4⟩) (by decide) node_23480

theorem node_24294 : Outcome ⟨8, 16, 17, 12⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 24⟩) (by decide) node_16347

theorem node_24295 : Outcome ⟨8, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 16, 4⟩) (by decide) node_23483

theorem node_24296 : Outcome ⟨8, 17, 16, 12⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 24⟩) (by decide) node_16388

theorem node_24297 : Outcome ⟨8, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨8, 18, 14, 2⟩) (by decide) node_23897

theorem node_24298 : Outcome ⟨8, 18, 15, 6⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 10⟩) (by decide) node_21843

theorem node_24299 : Outcome ⟨8, 18, 15, 16⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 26⟩) (by decide) node_15340

theorem node_24300 : Outcome ⟨8, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨7, 19, 14, 2⟩) (by decide) node_23876

theorem node_24301 : Outcome ⟨8, 19, 14, 10⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 8⟩) (by decide) node_22451

theorem node_24302 : Outcome ⟨8, 20, 13, 2⟩ true :=
  Outcome.win (q := ⟨8, 19, 13, 2⟩) (by decide) node_23899

theorem node_24303 : Outcome ⟨8, 20, 13, 14⟩ true :=
  Outcome.win (q := ⟨8, 20, 7, 12⟩) (by decide) node_21391

theorem node_24304 : Outcome ⟨9, 12, 20, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 20, 2⟩) (by decide) node_23882

theorem node_24305 : Outcome ⟨9, 12, 20, 12⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 6⟩) (by decide) node_23084

theorem node_24306 : Outcome ⟨9, 13, 19, 2⟩ true :=
  Outcome.win (q := ⟨8, 13, 19, 2⟩) (by decide) node_23884

theorem node_24307 : Outcome ⟨9, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 18, 2⟩) (by decide) node_23889

theorem node_24308 : Outcome ⟨9, 14, 18, 6⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 8⟩) (by decide) node_22577

theorem node_24309 : Outcome ⟨9, 14, 18, 12⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 8⟩) (by decide) node_22577

theorem node_24310 : Outcome ⟨9, 15, 17, 2⟩ true :=
  Outcome.win (q := ⟨9, 15, 16, 2⟩) (by decide) node_23914

theorem node_24311 : Outcome ⟨9, 16, 16, 2⟩ true :=
  Outcome.win (q := ⟨8, 16, 16, 2⟩) (by decide) node_23892

theorem node_24312 : Outcome ⟨9, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨8, 16, 16, 2⟩) (by decide) node_23892

theorem node_24313 : Outcome ⟨9, 16, 16, 8⟩ true :=
  Outcome.win (q := ⟨8, 16, 16, 2⟩) (by decide) node_23892

theorem node_24314 : Outcome ⟨9, 17, 15, 2⟩ true :=
  Outcome.win (q := ⟨9, 16, 15, 2⟩) (by decide) node_23917

theorem node_24315 : Outcome ⟨9, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨8, 18, 14, 2⟩) (by decide) node_23897

theorem node_24316 : Outcome ⟨9, 18, 14, 6⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 8⟩) (by decide) node_22577

theorem node_24317 : Outcome ⟨9, 18, 14, 12⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 8⟩) (by decide) node_22577

theorem node_24318 : Outcome ⟨9, 19, 13, 2⟩ true :=
  Outcome.win (q := ⟨8, 19, 13, 2⟩) (by decide) node_23899

theorem node_24319 : Outcome ⟨9, 20, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 20, 12, 2⟩) (by decide) node_23904

theorem node_24320 : Outcome ⟨9, 20, 12, 12⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 6⟩) (by decide) node_23114

theorem node_24321 : Outcome ⟨10, 11, 20, 2⟩ true :=
  Outcome.win (q := ⟨10, 10, 20, 2⟩) (by decide) node_23928

theorem node_24322 : Outcome ⟨10, 12, 19, 4⟩ true :=
  Outcome.win (q := ⟨10, 11, 19, 2⟩) (by decide) node_23929

theorem node_24323 : Outcome ⟨10, 13, 18, 6⟩ true :=
  Outcome.win (q := ⟨7, 13, 18, 6⟩) (by decide) node_23045

theorem node_24324 : Outcome ⟨10, 14, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 13, 17, 2⟩) (by decide) node_23934

theorem node_24325 : Outcome ⟨10, 15, 16, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 16, 2⟩) (by decide) node_23914

theorem node_24326 : Outcome ⟨10, 16, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 16, 15, 2⟩) (by decide) node_23917

end RQ9F1
