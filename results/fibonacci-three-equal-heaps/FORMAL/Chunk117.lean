import Chunk116
set_option autoImplicit false
namespace RQ9F1

theorem node_24613 : Outcome ⟨11, 11, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 20, 2⟩, ⟨9, 11, 20, 4⟩, ⟨8, 11, 20, 6⟩, ⟨7, 11, 20, 8⟩, ⟨11, 10, 20, 2⟩, ⟨11, 9, 20, 4⟩, ⟨11, 8, 20, 6⟩, ⟨11, 7, 20, 8⟩, ⟨11, 11, 19, 2⟩, ⟨11, 11, 18, 4⟩, ⟨11, 11, 17, 6⟩, ⟨11, 11, 16, 8⟩]
  exact AllWinning.cons node_24321 (AllWinning.cons node_23906 (AllWinning.cons node_23507 (AllWinning.cons node_23038 (AllWinning.cons node_24331 (AllWinning.cons node_23959 (AllWinning.cons node_23571 (AllWinning.cons node_23143 (AllWinning.cons node_24332 (AllWinning.cons node_23963 (AllWinning.cons node_23575 (AllWinning.cons node_23151 (AllWinning.nil))))))))))))

theorem node_24614 : Outcome ⟨11, 11, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 20, 2⟩, ⟨9, 11, 20, 4⟩, ⟨8, 11, 20, 6⟩, ⟨7, 11, 20, 8⟩, ⟨6, 11, 20, 10⟩, ⟨5, 11, 20, 12⟩, ⟨11, 10, 20, 2⟩, ⟨11, 9, 20, 4⟩, ⟨11, 8, 20, 6⟩, ⟨11, 7, 20, 8⟩, ⟨11, 6, 20, 10⟩, ⟨11, 5, 20, 12⟩, ⟨11, 11, 19, 2⟩, ⟨11, 11, 18, 4⟩, ⟨11, 11, 17, 6⟩, ⟨11, 11, 16, 8⟩, ⟨11, 11, 15, 10⟩, ⟨11, 11, 14, 12⟩]
  exact AllWinning.cons node_24321 (AllWinning.cons node_23906 (AllWinning.cons node_23507 (AllWinning.cons node_23038 (AllWinning.cons node_22482 (AllWinning.cons node_21873 (AllWinning.cons node_24331 (AllWinning.cons node_23959 (AllWinning.cons node_23571 (AllWinning.cons node_23143 (AllWinning.cons node_22625 (AllWinning.cons node_22047 (AllWinning.cons node_24332 (AllWinning.cons node_23963 (AllWinning.cons node_23575 (AllWinning.cons node_23151 (AllWinning.cons node_22634 (AllWinning.cons node_22061 (AllWinning.nil))))))))))))))))))

theorem node_24615 : Outcome ⟨11, 11, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 20, 2⟩, ⟨9, 11, 20, 4⟩, ⟨8, 11, 20, 6⟩, ⟨7, 11, 20, 8⟩, ⟨6, 11, 20, 10⟩, ⟨5, 11, 20, 12⟩, ⟨4, 11, 20, 14⟩, ⟨3, 11, 20, 16⟩, ⟨11, 10, 20, 2⟩, ⟨11, 9, 20, 4⟩, ⟨11, 8, 20, 6⟩, ⟨11, 7, 20, 8⟩, ⟨11, 6, 20, 10⟩, ⟨11, 5, 20, 12⟩, ⟨11, 4, 20, 14⟩, ⟨11, 3, 20, 16⟩, ⟨11, 11, 19, 2⟩, ⟨11, 11, 18, 4⟩, ⟨11, 11, 17, 6⟩, ⟨11, 11, 16, 8⟩, ⟨11, 11, 15, 10⟩, ⟨11, 11, 14, 12⟩, ⟨11, 11, 13, 14⟩, ⟨11, 11, 12, 16⟩]
  exact AllWinning.cons node_24321 (AllWinning.cons node_23906 (AllWinning.cons node_23507 (AllWinning.cons node_23038 (AllWinning.cons node_22482 (AllWinning.cons node_21873 (AllWinning.cons node_21257 (AllWinning.cons node_20464 (AllWinning.cons node_24331 (AllWinning.cons node_23959 (AllWinning.cons node_23571 (AllWinning.cons node_23143 (AllWinning.cons node_22625 (AllWinning.cons node_22047 (AllWinning.cons node_21453 (AllWinning.cons node_20783 (AllWinning.cons node_24332 (AllWinning.cons node_23963 (AllWinning.cons node_23575 (AllWinning.cons node_23151 (AllWinning.cons node_22634 (AllWinning.cons node_22061 (AllWinning.cons node_21469 (AllWinning.cons node_20801 (AllWinning.nil))))))))))))))))))))))))

theorem node_24616 : Outcome ⟨11, 12, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 10, 19, 4⟩) (by decide) node_23961

theorem node_24617 : Outcome ⟨11, 12, 19, 8⟩ true :=
  Outcome.win (q := ⟨11, 10, 19, 4⟩) (by decide) node_23961

theorem node_24618 : Outcome ⟨11, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨7, 13, 18, 8⟩) (by decide) node_23046

theorem node_24619 : Outcome ⟨11, 14, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 14, 17, 2⟩, ⟨9, 14, 17, 4⟩, ⟨11, 13, 17, 2⟩, ⟨11, 12, 17, 4⟩, ⟨11, 14, 16, 2⟩, ⟨11, 14, 15, 4⟩]
  exact AllWinning.cons node_24324 (AllWinning.cons node_23913 (AllWinning.cons node_24335 (AllWinning.cons node_23964 (AllWinning.cons node_24336 (AllWinning.cons node_23970 (AllWinning.nil))))))

theorem node_24620 : Outcome ⟨11, 14, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 14, 17, 2⟩, ⟨9, 14, 17, 4⟩, ⟨8, 14, 17, 6⟩, ⟨7, 14, 17, 8⟩, ⟨11, 13, 17, 2⟩, ⟨11, 12, 17, 4⟩, ⟨11, 11, 17, 6⟩, ⟨11, 10, 17, 8⟩, ⟨11, 14, 16, 2⟩, ⟨11, 14, 15, 4⟩, ⟨11, 14, 14, 6⟩, ⟨11, 14, 13, 8⟩]
  exact AllWinning.cons node_24324 (AllWinning.cons node_23913 (AllWinning.cons node_23513 (AllWinning.cons node_23048 (AllWinning.cons node_24335 (AllWinning.cons node_23964 (AllWinning.cons node_23575 (AllWinning.cons node_23148 (AllWinning.cons node_24336 (AllWinning.cons node_23970 (AllWinning.cons node_23581 (AllWinning.cons node_23158 (AllWinning.nil))))))))))))

theorem node_24621 : Outcome ⟨11, 14, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 14, 17, 2⟩, ⟨9, 14, 17, 4⟩, ⟨8, 14, 17, 6⟩, ⟨7, 14, 17, 8⟩, ⟨6, 14, 17, 10⟩, ⟨5, 14, 17, 12⟩, ⟨11, 13, 17, 2⟩, ⟨11, 12, 17, 4⟩, ⟨11, 11, 17, 6⟩, ⟨11, 10, 17, 8⟩, ⟨11, 9, 17, 10⟩, ⟨11, 8, 17, 12⟩, ⟨11, 14, 16, 2⟩, ⟨11, 14, 15, 4⟩, ⟨11, 14, 14, 6⟩, ⟨11, 14, 13, 8⟩, ⟨11, 14, 12, 10⟩, ⟨11, 14, 11, 12⟩]
  exact AllWinning.cons node_24324 (AllWinning.cons node_23913 (AllWinning.cons node_23513 (AllWinning.cons node_23048 (AllWinning.cons node_22488 (AllWinning.cons node_21881 (AllWinning.cons node_24335 (AllWinning.cons node_23964 (AllWinning.cons node_23575 (AllWinning.cons node_23148 (AllWinning.cons node_22630 (AllWinning.cons node_22053 (AllWinning.cons node_24336 (AllWinning.cons node_23970 (AllWinning.cons node_23581 (AllWinning.cons node_23158 (AllWinning.cons node_22641 (AllWinning.cons node_22070 (AllWinning.nil))))))))))))))))))

theorem node_24622 : Outcome ⟨11, 15, 16, 2⟩ true :=
  Outcome.win (q := ⟨11, 13, 16, 4⟩) (by decide) node_23966

theorem node_24623 : Outcome ⟨11, 15, 16, 8⟩ true :=
  Outcome.win (q := ⟨11, 13, 16, 4⟩) (by decide) node_23966

theorem node_24624 : Outcome ⟨11, 16, 15, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 13, 4⟩) (by decide) node_23974

theorem node_24625 : Outcome ⟨11, 16, 15, 8⟩ true :=
  Outcome.win (q := ⟨11, 16, 13, 4⟩) (by decide) node_23974

theorem node_24626 : Outcome ⟨11, 17, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 14, 2⟩, ⟨9, 17, 14, 4⟩, ⟨11, 16, 14, 2⟩, ⟨11, 15, 14, 4⟩, ⟨11, 17, 13, 2⟩, ⟨11, 17, 12, 4⟩]
  exact AllWinning.cons node_24327 (AllWinning.cons node_23920 (AllWinning.cons node_24340 (AllWinning.cons node_23972 (AllWinning.cons node_24343 (AllWinning.cons node_23977 (AllWinning.nil))))))

theorem node_24627 : Outcome ⟨11, 17, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 14, 2⟩, ⟨9, 17, 14, 4⟩, ⟨8, 17, 14, 6⟩, ⟨7, 17, 14, 8⟩, ⟨11, 16, 14, 2⟩, ⟨11, 15, 14, 4⟩, ⟨11, 14, 14, 6⟩, ⟨11, 13, 14, 8⟩, ⟨11, 17, 13, 2⟩, ⟨11, 17, 12, 4⟩, ⟨11, 17, 11, 6⟩, ⟨11, 17, 10, 8⟩]
  exact AllWinning.cons node_24327 (AllWinning.cons node_23920 (AllWinning.cons node_23519 (AllWinning.cons node_23054 (AllWinning.cons node_24340 (AllWinning.cons node_23972 (AllWinning.cons node_23581 (AllWinning.cons node_23156 (AllWinning.cons node_24343 (AllWinning.cons node_23977 (AllWinning.cons node_23586 (AllWinning.cons node_23166 (AllWinning.nil))))))))))))

theorem node_24628 : Outcome ⟨11, 17, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 14, 2⟩, ⟨9, 17, 14, 4⟩, ⟨8, 17, 14, 6⟩, ⟨7, 17, 14, 8⟩, ⟨6, 17, 14, 10⟩, ⟨5, 17, 14, 12⟩, ⟨11, 16, 14, 2⟩, ⟨11, 15, 14, 4⟩, ⟨11, 14, 14, 6⟩, ⟨11, 13, 14, 8⟩, ⟨11, 12, 14, 10⟩, ⟨11, 11, 14, 12⟩, ⟨11, 17, 13, 2⟩, ⟨11, 17, 12, 4⟩, ⟨11, 17, 11, 6⟩, ⟨11, 17, 10, 8⟩, ⟨11, 17, 9, 10⟩, ⟨11, 17, 8, 12⟩]
  exact AllWinning.cons node_24327 (AllWinning.cons node_23920 (AllWinning.cons node_23519 (AllWinning.cons node_23054 (AllWinning.cons node_22497 (AllWinning.cons node_21889 (AllWinning.cons node_24340 (AllWinning.cons node_23972 (AllWinning.cons node_23581 (AllWinning.cons node_23156 (AllWinning.cons node_22636 (AllWinning.cons node_22061 (AllWinning.cons node_24343 (AllWinning.cons node_23977 (AllWinning.cons node_23586 (AllWinning.cons node_23166 (AllWinning.cons node_22647 (AllWinning.cons node_22078 (AllWinning.nil))))))))))))))))))

theorem node_24629 : Outcome ⟨11, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨7, 18, 13, 8⟩) (by decide) node_23058

theorem node_24630 : Outcome ⟨11, 19, 12, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 10, 4⟩) (by decide) node_23980

theorem node_24631 : Outcome ⟨11, 19, 12, 8⟩ true :=
  Outcome.win (q := ⟨11, 19, 10, 4⟩) (by decide) node_23980

theorem node_24632 : Outcome ⟨11, 20, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 20, 11, 2⟩, ⟨9, 20, 11, 4⟩, ⟨8, 20, 11, 6⟩, ⟨7, 20, 11, 8⟩, ⟨11, 19, 11, 2⟩, ⟨11, 18, 11, 4⟩, ⟨11, 17, 11, 6⟩, ⟨11, 16, 11, 8⟩, ⟨11, 20, 10, 2⟩, ⟨11, 20, 9, 4⟩, ⟨11, 20, 8, 6⟩, ⟨11, 20, 7, 8⟩]
  exact AllWinning.cons node_24330 (AllWinning.cons node_23926 (AllWinning.cons node_23525 (AllWinning.cons node_23063 (AllWinning.cons node_24345 (AllWinning.cons node_23978 (AllWinning.cons node_23586 (AllWinning.cons node_23164 (AllWinning.cons node_24347 (AllWinning.cons node_23982 (AllWinning.cons node_23591 (AllWinning.cons node_23170 (AllWinning.nil))))))))))))

theorem node_24633 : Outcome ⟨11, 20, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 20, 11, 2⟩, ⟨9, 20, 11, 4⟩, ⟨8, 20, 11, 6⟩, ⟨7, 20, 11, 8⟩, ⟨6, 20, 11, 10⟩, ⟨5, 20, 11, 12⟩, ⟨4, 20, 11, 14⟩, ⟨3, 20, 11, 16⟩, ⟨11, 19, 11, 2⟩, ⟨11, 18, 11, 4⟩, ⟨11, 17, 11, 6⟩, ⟨11, 16, 11, 8⟩, ⟨11, 15, 11, 10⟩, ⟨11, 14, 11, 12⟩, ⟨11, 13, 11, 14⟩, ⟨11, 12, 11, 16⟩, ⟨11, 20, 10, 2⟩, ⟨11, 20, 9, 4⟩, ⟨11, 20, 8, 6⟩, ⟨11, 20, 7, 8⟩, ⟨11, 20, 6, 10⟩, ⟨11, 20, 5, 12⟩, ⟨11, 20, 4, 14⟩, ⟨11, 20, 3, 16⟩]
  exact AllWinning.cons node_24330 (AllWinning.cons node_23926 (AllWinning.cons node_23525 (AllWinning.cons node_23063 (AllWinning.cons node_22503 (AllWinning.cons node_21897 (AllWinning.cons node_21275 (AllWinning.cons node_20486 (AllWinning.cons node_24345 (AllWinning.cons node_23978 (AllWinning.cons node_23586 (AllWinning.cons node_23164 (AllWinning.cons node_22643 (AllWinning.cons node_22070 (AllWinning.cons node_21475 (AllWinning.cons node_20803 (AllWinning.cons node_24347 (AllWinning.cons node_23982 (AllWinning.cons node_23591 (AllWinning.cons node_23170 (AllWinning.cons node_22653 (AllWinning.cons node_22083 (AllWinning.cons node_21489 (AllWinning.cons node_20821 (AllWinning.nil))))))))))))))))))))))))

theorem node_24634 : Outcome ⟨12, 10, 20, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 20, 4⟩) (by decide) node_23984

theorem node_24635 : Outcome ⟨12, 11, 19, 2⟩ true :=
  Outcome.win (q := ⟨10, 11, 19, 4⟩) (by decide) node_23930

theorem node_24636 : Outcome ⟨12, 11, 19, 8⟩ true :=
  Outcome.win (q := ⟨10, 11, 19, 4⟩) (by decide) node_23930

theorem node_24637 : Outcome ⟨12, 12, 18, 2⟩ true :=
  Outcome.win (q := ⟨10, 12, 18, 4⟩) (by decide) node_23932

theorem node_24638 : Outcome ⟨12, 12, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 12, 18, 4⟩) (by decide) node_23932

theorem node_24639 : Outcome ⟨12, 13, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 13, 17, 2⟩, ⟨10, 13, 17, 4⟩, ⟨12, 12, 17, 2⟩, ⟨12, 11, 17, 4⟩, ⟨12, 13, 16, 2⟩, ⟨12, 13, 15, 4⟩]
  exact AllWinning.cons node_24335 (AllWinning.cons node_23935 (AllWinning.cons node_24351 (AllWinning.cons node_23989 (AllWinning.cons node_24353 (AllWinning.cons node_23993 (AllWinning.nil))))))

theorem node_24640 : Outcome ⟨12, 13, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 13, 17, 2⟩, ⟨10, 13, 17, 4⟩, ⟨9, 13, 17, 6⟩, ⟨8, 13, 17, 8⟩, ⟨12, 12, 17, 2⟩, ⟨12, 11, 17, 4⟩, ⟨12, 10, 17, 6⟩, ⟨12, 9, 17, 8⟩, ⟨12, 13, 16, 2⟩, ⟨12, 13, 15, 4⟩, ⟨12, 13, 14, 6⟩, ⟨12, 13, 13, 8⟩]
  exact AllWinning.cons node_24335 (AllWinning.cons node_23935 (AllWinning.cons node_23535 (AllWinning.cons node_23071 (AllWinning.cons node_24351 (AllWinning.cons node_23989 (AllWinning.cons node_23599 (AllWinning.cons node_23179 (AllWinning.cons node_24353 (AllWinning.cons node_23993 (AllWinning.cons node_23605 (AllWinning.cons node_23190 (AllWinning.nil))))))))))))

theorem node_24641 : Outcome ⟨12, 13, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 13, 17, 2⟩, ⟨10, 13, 17, 4⟩, ⟨9, 13, 17, 6⟩, ⟨8, 13, 17, 8⟩, ⟨7, 13, 17, 10⟩, ⟨6, 13, 17, 12⟩, ⟨12, 12, 17, 2⟩, ⟨12, 11, 17, 4⟩, ⟨12, 10, 17, 6⟩, ⟨12, 9, 17, 8⟩, ⟨12, 8, 17, 10⟩, ⟨12, 7, 17, 12⟩, ⟨12, 13, 16, 2⟩, ⟨12, 13, 15, 4⟩, ⟨12, 13, 14, 6⟩, ⟨12, 13, 13, 8⟩, ⟨12, 13, 12, 10⟩, ⟨12, 13, 11, 12⟩]
  exact AllWinning.cons node_24335 (AllWinning.cons node_23935 (AllWinning.cons node_23535 (AllWinning.cons node_23071 (AllWinning.cons node_22512 (AllWinning.cons node_21907 (AllWinning.cons node_24351 (AllWinning.cons node_23989 (AllWinning.cons node_23599 (AllWinning.cons node_23179 (AllWinning.cons node_22662 (AllWinning.cons node_22093 (AllWinning.cons node_24353 (AllWinning.cons node_23993 (AllWinning.cons node_23605 (AllWinning.cons node_23190 (AllWinning.cons node_22677 (AllWinning.cons node_22112 (AllWinning.nil))))))))))))))))))

theorem node_24642 : Outcome ⟨12, 14, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 16, 4⟩) (by decide) node_23937

theorem node_24643 : Outcome ⟨12, 14, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 14, 16, 4⟩) (by decide) node_23937

theorem node_24644 : Outcome ⟨12, 15, 15, 2⟩ true :=
  Outcome.win (q := ⟨10, 15, 15, 4⟩) (by decide) node_23942

theorem node_24645 : Outcome ⟨12, 15, 15, 6⟩ true :=
  Outcome.win (q := ⟨10, 15, 15, 4⟩) (by decide) node_23942

theorem node_24646 : Outcome ⟨12, 16, 14, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 14, 4⟩) (by decide) node_23946

theorem node_24647 : Outcome ⟨12, 16, 14, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 14, 4⟩) (by decide) node_23946

theorem node_24648 : Outcome ⟨12, 17, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 17, 13, 2⟩, ⟨10, 17, 13, 4⟩, ⟨12, 16, 13, 2⟩, ⟨12, 15, 13, 4⟩, ⟨12, 17, 12, 2⟩, ⟨12, 17, 11, 4⟩]
  exact AllWinning.cons node_24343 (AllWinning.cons node_23951 (AllWinning.cons node_24362 (AllWinning.cons node_23998 (AllWinning.cons node_24365 (AllWinning.cons node_24003 (AllWinning.nil))))))

theorem node_24649 : Outcome ⟨12, 17, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 17, 13, 2⟩, ⟨10, 17, 13, 4⟩, ⟨9, 17, 13, 6⟩, ⟨8, 17, 13, 8⟩, ⟨12, 16, 13, 2⟩, ⟨12, 15, 13, 4⟩, ⟨12, 14, 13, 6⟩, ⟨12, 13, 13, 8⟩, ⟨12, 17, 12, 2⟩, ⟨12, 17, 11, 4⟩, ⟨12, 17, 10, 6⟩, ⟨12, 17, 9, 8⟩]
  exact AllWinning.cons node_24343 (AllWinning.cons node_23951 (AllWinning.cons node_23543 (AllWinning.cons node_23076 (AllWinning.cons node_24362 (AllWinning.cons node_23998 (AllWinning.cons node_23608 (AllWinning.cons node_23190 (AllWinning.cons node_24365 (AllWinning.cons node_24003 (AllWinning.cons node_23615 (AllWinning.cons node_23201 (AllWinning.nil))))))))))))

theorem node_24650 : Outcome ⟨12, 17, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 17, 13, 2⟩, ⟨10, 17, 13, 4⟩, ⟨9, 17, 13, 6⟩, ⟨8, 17, 13, 8⟩, ⟨7, 17, 13, 10⟩, ⟨6, 17, 13, 12⟩, ⟨12, 16, 13, 2⟩, ⟨12, 15, 13, 4⟩, ⟨12, 14, 13, 6⟩, ⟨12, 13, 13, 8⟩, ⟨12, 12, 13, 10⟩, ⟨12, 11, 13, 12⟩, ⟨12, 17, 12, 2⟩, ⟨12, 17, 11, 4⟩, ⟨12, 17, 10, 6⟩, ⟨12, 17, 9, 8⟩, ⟨12, 17, 8, 10⟩, ⟨12, 17, 7, 12⟩]
  exact AllWinning.cons node_24343 (AllWinning.cons node_23951 (AllWinning.cons node_23543 (AllWinning.cons node_23076 (AllWinning.cons node_22521 (AllWinning.cons node_21920 (AllWinning.cons node_24362 (AllWinning.cons node_23998 (AllWinning.cons node_23608 (AllWinning.cons node_23190 (AllWinning.cons node_22673 (AllWinning.cons node_22106 (AllWinning.cons node_24365 (AllWinning.cons node_24003 (AllWinning.cons node_23615 (AllWinning.cons node_23201 (AllWinning.cons node_22687 (AllWinning.cons node_22124 (AllWinning.nil))))))))))))))))))

theorem node_24651 : Outcome ⟨12, 18, 12, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 12, 4⟩) (by decide) node_23953

theorem node_24652 : Outcome ⟨12, 18, 12, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 12, 4⟩) (by decide) node_23953

theorem node_24653 : Outcome ⟨12, 19, 11, 2⟩ true :=
  Outcome.win (q := ⟨10, 19, 11, 4⟩) (by decide) node_23956

theorem node_24654 : Outcome ⟨12, 19, 11, 8⟩ true :=
  Outcome.win (q := ⟨10, 19, 11, 4⟩) (by decide) node_23956

theorem node_24655 : Outcome ⟨13, 9, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 9, 20, 2⟩, ⟨11, 9, 20, 4⟩, ⟨13, 8, 20, 2⟩, ⟨13, 7, 20, 4⟩, ⟨13, 9, 19, 2⟩, ⟨13, 9, 18, 4⟩]
  exact AllWinning.cons node_24348 (AllWinning.cons node_23959 (AllWinning.cons node_24370 (AllWinning.cons node_24009 (AllWinning.cons node_24372 (AllWinning.cons node_24015 (AllWinning.nil))))))

theorem node_24656 : Outcome ⟨13, 9, 20, 12⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 8⟩) (by decide) node_23085

theorem node_24657 : Outcome ⟨13, 10, 19, 4⟩ true :=
  Outcome.win (q := ⟨11, 10, 19, 4⟩) (by decide) node_23961

theorem node_24658 : Outcome ⟨13, 11, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 7, 18, 8⟩) (by decide) node_23215

theorem node_24659 : Outcome ⟨13, 12, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 12, 17, 2⟩, ⟨11, 12, 17, 4⟩, ⟨13, 11, 17, 2⟩, ⟨13, 10, 17, 4⟩, ⟨13, 12, 16, 2⟩, ⟨13, 12, 15, 4⟩]
  exact AllWinning.cons node_24351 (AllWinning.cons node_23964 (AllWinning.cons node_24374 (AllWinning.cons node_24018 (AllWinning.cons node_24375 (AllWinning.cons node_24024 (AllWinning.nil))))))

theorem node_24660 : Outcome ⟨13, 12, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 12, 17, 2⟩, ⟨11, 12, 17, 4⟩, ⟨10, 12, 17, 6⟩, ⟨9, 12, 17, 8⟩, ⟨13, 11, 17, 2⟩, ⟨13, 10, 17, 4⟩, ⟨13, 9, 17, 6⟩, ⟨13, 8, 17, 8⟩, ⟨13, 12, 16, 2⟩, ⟨13, 12, 15, 4⟩, ⟨13, 12, 14, 6⟩, ⟨13, 12, 13, 8⟩]
  exact AllWinning.cons node_24351 (AllWinning.cons node_23964 (AllWinning.cons node_23556 (AllWinning.cons node_23094 (AllWinning.cons node_24374 (AllWinning.cons node_24018 (AllWinning.cons node_23627 (AllWinning.cons node_23217 (AllWinning.cons node_24375 (AllWinning.cons node_24024 (AllWinning.cons node_23633 (AllWinning.cons node_23227 (AllWinning.nil))))))))))))

theorem node_24661 : Outcome ⟨13, 12, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 12, 17, 2⟩, ⟨11, 12, 17, 4⟩, ⟨10, 12, 17, 6⟩, ⟨9, 12, 17, 8⟩, ⟨8, 12, 17, 10⟩, ⟨7, 12, 17, 12⟩, ⟨13, 11, 17, 2⟩, ⟨13, 10, 17, 4⟩, ⟨13, 9, 17, 6⟩, ⟨13, 8, 17, 8⟩, ⟨13, 7, 17, 10⟩, ⟨13, 6, 17, 12⟩, ⟨13, 12, 16, 2⟩, ⟨13, 12, 15, 4⟩, ⟨13, 12, 14, 6⟩, ⟨13, 12, 13, 8⟩, ⟨13, 12, 12, 10⟩, ⟨13, 12, 11, 12⟩]
  exact AllWinning.cons node_24351 (AllWinning.cons node_23964 (AllWinning.cons node_23556 (AllWinning.cons node_23094 (AllWinning.cons node_22535 (AllWinning.cons node_21934 (AllWinning.cons node_24374 (AllWinning.cons node_24018 (AllWinning.cons node_23627 (AllWinning.cons node_23217 (AllWinning.cons node_22702 (AllWinning.cons node_22138 (AllWinning.cons node_24375 (AllWinning.cons node_24024 (AllWinning.cons node_23633 (AllWinning.cons node_23227 (AllWinning.cons node_22718 (AllWinning.cons node_22156 (AllWinning.nil))))))))))))))))))

theorem node_24662 : Outcome ⟨13, 13, 16, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 6⟩) (by decide) node_23637

theorem node_24663 : Outcome ⟨13, 13, 16, 6⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 6⟩) (by decide) node_23637

theorem node_24664 : Outcome ⟨13, 14, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 14, 15, 2⟩, ⟨11, 14, 15, 4⟩, ⟨13, 13, 15, 2⟩, ⟨13, 12, 15, 4⟩, ⟨13, 14, 14, 2⟩, ⟨13, 14, 13, 4⟩]
  exact AllWinning.cons node_24356 (AllWinning.cons node_23970 (AllWinning.cons node_24378 (AllWinning.cons node_24024 (AllWinning.cons node_24381 (AllWinning.cons node_24029 (AllWinning.nil))))))

theorem node_24665 : Outcome ⟨13, 14, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 14, 15, 2⟩, ⟨11, 14, 15, 4⟩, ⟨10, 14, 15, 6⟩, ⟨9, 14, 15, 8⟩, ⟨13, 13, 15, 2⟩, ⟨13, 12, 15, 4⟩, ⟨13, 11, 15, 6⟩, ⟨13, 10, 15, 8⟩, ⟨13, 14, 14, 2⟩, ⟨13, 14, 13, 4⟩, ⟨13, 14, 12, 6⟩, ⟨13, 14, 11, 8⟩]
  exact AllWinning.cons node_24356 (AllWinning.cons node_23970 (AllWinning.cons node_23560 (AllWinning.cons node_23099 (AllWinning.cons node_24378 (AllWinning.cons node_24024 (AllWinning.cons node_23631 (AllWinning.cons node_23222 (AllWinning.cons node_24381 (AllWinning.cons node_24029 (AllWinning.cons node_23642 (AllWinning.cons node_23232 (AllWinning.nil))))))))))))

theorem node_24666 : Outcome ⟨13, 14, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 14, 15, 2⟩, ⟨11, 14, 15, 4⟩, ⟨10, 14, 15, 6⟩, ⟨9, 14, 15, 8⟩, ⟨8, 14, 15, 10⟩, ⟨7, 14, 15, 12⟩, ⟨13, 13, 15, 2⟩, ⟨13, 12, 15, 4⟩, ⟨13, 11, 15, 6⟩, ⟨13, 10, 15, 8⟩, ⟨13, 9, 15, 10⟩, ⟨13, 8, 15, 12⟩, ⟨13, 14, 14, 2⟩, ⟨13, 14, 13, 4⟩, ⟨13, 14, 12, 6⟩, ⟨13, 14, 11, 8⟩, ⟨13, 14, 10, 10⟩, ⟨13, 14, 9, 12⟩]
  exact AllWinning.cons node_24356 (AllWinning.cons node_23970 (AllWinning.cons node_23560 (AllWinning.cons node_23099 (AllWinning.cons node_22543 (AllWinning.cons node_21940 (AllWinning.cons node_24378 (AllWinning.cons node_24024 (AllWinning.cons node_23631 (AllWinning.cons node_23222 (AllWinning.cons node_22709 (AllWinning.cons node_22144 (AllWinning.cons node_24381 (AllWinning.cons node_24029 (AllWinning.cons node_23642 (AllWinning.cons node_23232 (AllWinning.cons node_22724 (AllWinning.cons node_22160 (AllWinning.nil))))))))))))))))))

theorem node_24667 : Outcome ⟨13, 14, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 14, 15, 2⟩, ⟨11, 14, 15, 4⟩, ⟨10, 14, 15, 6⟩, ⟨9, 14, 15, 8⟩, ⟨8, 14, 15, 10⟩, ⟨7, 14, 15, 12⟩, ⟨6, 14, 15, 14⟩, ⟨5, 14, 15, 16⟩, ⟨13, 13, 15, 2⟩, ⟨13, 12, 15, 4⟩, ⟨13, 11, 15, 6⟩, ⟨13, 10, 15, 8⟩, ⟨13, 9, 15, 10⟩, ⟨13, 8, 15, 12⟩, ⟨13, 7, 15, 14⟩, ⟨13, 6, 15, 16⟩, ⟨13, 14, 14, 2⟩, ⟨13, 14, 13, 4⟩, ⟨13, 14, 12, 6⟩, ⟨13, 14, 11, 8⟩, ⟨13, 14, 10, 10⟩, ⟨13, 14, 9, 12⟩, ⟨13, 14, 8, 14⟩, ⟨13, 14, 7, 16⟩]
  exact AllWinning.cons node_24356 (AllWinning.cons node_23970 (AllWinning.cons node_23560 (AllWinning.cons node_23099 (AllWinning.cons node_22543 (AllWinning.cons node_21940 (AllWinning.cons node_21321 (AllWinning.cons node_20529 (AllWinning.cons node_24378 (AllWinning.cons node_24024 (AllWinning.cons node_23631 (AllWinning.cons node_23222 (AllWinning.cons node_22709 (AllWinning.cons node_22144 (AllWinning.cons node_21550 (AllWinning.cons node_20891 (AllWinning.cons node_24381 (AllWinning.cons node_24029 (AllWinning.cons node_23642 (AllWinning.cons node_23232 (AllWinning.cons node_22724 (AllWinning.cons node_22160 (AllWinning.cons node_21564 (AllWinning.cons node_20915 (AllWinning.nil))))))))))))))))))))))))

theorem node_24668 : Outcome ⟨13, 14, 15, 12⟩ true :=
  Outcome.win (q := ⟨13, 14, 6, 18⟩) (by decide) node_20170

theorem node_24669 : Outcome ⟨13, 15, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 14, 2⟩, ⟨11, 15, 14, 4⟩, ⟨13, 14, 14, 2⟩, ⟨13, 13, 14, 4⟩, ⟨13, 15, 13, 2⟩, ⟨13, 15, 12, 4⟩]
  exact AllWinning.cons node_24359 (AllWinning.cons node_23972 (AllWinning.cons node_24381 (AllWinning.cons node_24027 (AllWinning.cons node_24382 (AllWinning.cons node_24032 (AllWinning.nil))))))

theorem node_24670 : Outcome ⟨13, 15, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 14, 2⟩, ⟨11, 15, 14, 4⟩, ⟨10, 15, 14, 6⟩, ⟨9, 15, 14, 8⟩, ⟨13, 14, 14, 2⟩, ⟨13, 13, 14, 4⟩, ⟨13, 12, 14, 6⟩, ⟨13, 11, 14, 8⟩, ⟨13, 15, 13, 2⟩, ⟨13, 15, 12, 4⟩, ⟨13, 15, 11, 6⟩, ⟨13, 15, 10, 8⟩]
  exact AllWinning.cons node_24359 (AllWinning.cons node_23972 (AllWinning.cons node_23562 (AllWinning.cons node_23101 (AllWinning.cons node_24381 (AllWinning.cons node_24027 (AllWinning.cons node_23633 (AllWinning.cons node_23224 (AllWinning.cons node_24382 (AllWinning.cons node_24032 (AllWinning.cons node_23645 (AllWinning.cons node_23234 (AllWinning.nil))))))))))))

theorem node_24671 : Outcome ⟨13, 15, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 14, 2⟩, ⟨11, 15, 14, 4⟩, ⟨10, 15, 14, 6⟩, ⟨9, 15, 14, 8⟩, ⟨8, 15, 14, 10⟩, ⟨7, 15, 14, 12⟩, ⟨13, 14, 14, 2⟩, ⟨13, 13, 14, 4⟩, ⟨13, 12, 14, 6⟩, ⟨13, 11, 14, 8⟩, ⟨13, 10, 14, 10⟩, ⟨13, 9, 14, 12⟩, ⟨13, 15, 13, 2⟩, ⟨13, 15, 12, 4⟩, ⟨13, 15, 11, 6⟩, ⟨13, 15, 10, 8⟩, ⟨13, 15, 9, 10⟩, ⟨13, 15, 8, 12⟩]
  exact AllWinning.cons node_24359 (AllWinning.cons node_23972 (AllWinning.cons node_23562 (AllWinning.cons node_23101 (AllWinning.cons node_22548 (AllWinning.cons node_21942 (AllWinning.cons node_24381 (AllWinning.cons node_24027 (AllWinning.cons node_23633 (AllWinning.cons node_23224 (AllWinning.cons node_22712 (AllWinning.cons node_22146 (AllWinning.cons node_24382 (AllWinning.cons node_24032 (AllWinning.cons node_23645 (AllWinning.cons node_23234 (AllWinning.cons node_22728 (AllWinning.cons node_22163 (AllWinning.nil))))))))))))))))))

theorem node_24672 : Outcome ⟨13, 15, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 14, 2⟩, ⟨11, 15, 14, 4⟩, ⟨10, 15, 14, 6⟩, ⟨9, 15, 14, 8⟩, ⟨8, 15, 14, 10⟩, ⟨7, 15, 14, 12⟩, ⟨6, 15, 14, 14⟩, ⟨5, 15, 14, 16⟩, ⟨13, 14, 14, 2⟩, ⟨13, 13, 14, 4⟩, ⟨13, 12, 14, 6⟩, ⟨13, 11, 14, 8⟩, ⟨13, 10, 14, 10⟩, ⟨13, 9, 14, 12⟩, ⟨13, 8, 14, 14⟩, ⟨13, 7, 14, 16⟩, ⟨13, 15, 13, 2⟩, ⟨13, 15, 12, 4⟩, ⟨13, 15, 11, 6⟩, ⟨13, 15, 10, 8⟩, ⟨13, 15, 9, 10⟩, ⟨13, 15, 8, 12⟩, ⟨13, 15, 7, 14⟩, ⟨13, 15, 6, 16⟩]
  exact AllWinning.cons node_24359 (AllWinning.cons node_23972 (AllWinning.cons node_23562 (AllWinning.cons node_23101 (AllWinning.cons node_22548 (AllWinning.cons node_21942 (AllWinning.cons node_21324 (AllWinning.cons node_20532 (AllWinning.cons node_24381 (AllWinning.cons node_24027 (AllWinning.cons node_23633 (AllWinning.cons node_23224 (AllWinning.cons node_22712 (AllWinning.cons node_22146 (AllWinning.cons node_21553 (AllWinning.cons node_20893 (AllWinning.cons node_24382 (AllWinning.cons node_24032 (AllWinning.cons node_23645 (AllWinning.cons node_23234 (AllWinning.cons node_22728 (AllWinning.cons node_22163 (AllWinning.cons node_21567 (AllWinning.cons node_20918 (AllWinning.nil))))))))))))))))))))))))

theorem node_24673 : Outcome ⟨13, 15, 14, 12⟩ true :=
  Outcome.win (q := ⟨13, 6, 14, 18⟩) (by decide) node_20144

theorem node_24674 : Outcome ⟨13, 16, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 6⟩) (by decide) node_23637

theorem node_24675 : Outcome ⟨13, 16, 13, 6⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 6⟩) (by decide) node_23637

theorem node_24676 : Outcome ⟨13, 17, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 12, 2⟩, ⟨11, 17, 12, 4⟩, ⟨13, 16, 12, 2⟩, ⟨13, 15, 12, 4⟩, ⟨13, 17, 11, 2⟩, ⟨13, 17, 10, 4⟩]
  exact AllWinning.cons node_24365 (AllWinning.cons node_23977 (AllWinning.cons node_24385 (AllWinning.cons node_24032 (AllWinning.cons node_24388 (AllWinning.cons node_24040 (AllWinning.nil))))))

theorem node_24677 : Outcome ⟨13, 17, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 12, 2⟩, ⟨11, 17, 12, 4⟩, ⟨10, 17, 12, 6⟩, ⟨9, 17, 12, 8⟩, ⟨13, 16, 12, 2⟩, ⟨13, 15, 12, 4⟩, ⟨13, 14, 12, 6⟩, ⟨13, 13, 12, 8⟩, ⟨13, 17, 11, 2⟩, ⟨13, 17, 10, 4⟩, ⟨13, 17, 9, 6⟩, ⟨13, 17, 8, 8⟩]
  exact AllWinning.cons node_24365 (AllWinning.cons node_23977 (AllWinning.cons node_23566 (AllWinning.cons node_23106 (AllWinning.cons node_24385 (AllWinning.cons node_24032 (AllWinning.cons node_23642 (AllWinning.cons node_23230 (AllWinning.cons node_24388 (AllWinning.cons node_24040 (AllWinning.cons node_23650 (AllWinning.cons node_23240 (AllWinning.nil))))))))))))

theorem node_24678 : Outcome ⟨13, 17, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 12, 2⟩, ⟨11, 17, 12, 4⟩, ⟨10, 17, 12, 6⟩, ⟨9, 17, 12, 8⟩, ⟨8, 17, 12, 10⟩, ⟨7, 17, 12, 12⟩, ⟨13, 16, 12, 2⟩, ⟨13, 15, 12, 4⟩, ⟨13, 14, 12, 6⟩, ⟨13, 13, 12, 8⟩, ⟨13, 12, 12, 10⟩, ⟨13, 11, 12, 12⟩, ⟨13, 17, 11, 2⟩, ⟨13, 17, 10, 4⟩, ⟨13, 17, 9, 6⟩, ⟨13, 17, 8, 8⟩, ⟨13, 17, 7, 10⟩, ⟨13, 17, 6, 12⟩]
  exact AllWinning.cons node_24365 (AllWinning.cons node_23977 (AllWinning.cons node_23566 (AllWinning.cons node_23106 (AllWinning.cons node_22554 (AllWinning.cons node_21948 (AllWinning.cons node_24385 (AllWinning.cons node_24032 (AllWinning.cons node_23642 (AllWinning.cons node_23230 (AllWinning.cons node_22718 (AllWinning.cons node_22152 (AllWinning.cons node_24388 (AllWinning.cons node_24040 (AllWinning.cons node_23650 (AllWinning.cons node_23240 (AllWinning.cons node_22734 (AllWinning.cons node_22169 (AllWinning.nil))))))))))))))))))

theorem node_24679 : Outcome ⟨13, 18, 11, 4⟩ true :=
  Outcome.win (q := ⟨13, 18, 7, 8⟩) (by decide) node_23244

theorem node_24680 : Outcome ⟨13, 19, 10, 4⟩ true :=
  Outcome.win (q := ⟨11, 19, 10, 4⟩) (by decide) node_23980

theorem node_24681 : Outcome ⟨13, 20, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 20, 9, 2⟩, ⟨11, 20, 9, 4⟩, ⟨13, 19, 9, 2⟩, ⟨13, 18, 9, 4⟩, ⟨13, 20, 8, 2⟩, ⟨13, 20, 7, 4⟩]
  exact AllWinning.cons node_24369 (AllWinning.cons node_23982 (AllWinning.cons node_24390 (AllWinning.cons node_24041 (AllWinning.cons node_24391 (AllWinning.cons node_24047 (AllWinning.nil))))))

theorem node_24682 : Outcome ⟨13, 20, 9, 12⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 8⟩) (by decide) node_23115

theorem node_24683 : Outcome ⟨14, 8, 20, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 20, 4⟩) (by decide) node_23984

theorem node_24684 : Outcome ⟨14, 9, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 19, 2⟩, ⟨12, 9, 19, 4⟩, ⟨14, 8, 19, 2⟩, ⟨14, 7, 19, 4⟩, ⟨14, 9, 18, 2⟩, ⟨14, 9, 17, 4⟩]
  exact AllWinning.cons node_24372 (AllWinning.cons node_23985 (AllWinning.cons node_24393 (AllWinning.cons node_24050 (AllWinning.cons node_24394 (AllWinning.cons node_24053 (AllWinning.nil))))))

theorem node_24685 : Outcome ⟨14, 9, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 19, 2⟩, ⟨12, 9, 19, 4⟩, ⟨11, 9, 19, 6⟩, ⟨10, 9, 19, 8⟩, ⟨14, 8, 19, 2⟩, ⟨14, 7, 19, 4⟩, ⟨14, 6, 19, 6⟩, ⟨14, 5, 19, 8⟩, ⟨14, 9, 18, 2⟩, ⟨14, 9, 17, 4⟩, ⟨14, 9, 16, 6⟩, ⟨14, 9, 15, 8⟩]
  exact AllWinning.cons node_24372 (AllWinning.cons node_23985 (AllWinning.cons node_23573 (AllWinning.cons node_23120 (AllWinning.cons node_24393 (AllWinning.cons node_24050 (AllWinning.cons node_23656 (AllWinning.cons node_23249 (AllWinning.cons node_24394 (AllWinning.cons node_24053 (AllWinning.cons node_23663 (AllWinning.cons node_23256 (AllWinning.nil))))))))))))

theorem node_24686 : Outcome ⟨14, 10, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 10, 18, 4⟩) (by decide) node_23987

theorem node_24687 : Outcome ⟨14, 11, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 11, 17, 2⟩, ⟨12, 11, 17, 4⟩, ⟨14, 10, 17, 2⟩, ⟨14, 9, 17, 4⟩, ⟨14, 11, 16, 2⟩, ⟨14, 11, 15, 4⟩]
  exact AllWinning.cons node_24374 (AllWinning.cons node_23989 (AllWinning.cons node_24396 (AllWinning.cons node_24053 (AllWinning.cons node_24398 (AllWinning.cons node_24058 (AllWinning.nil))))))

theorem node_24688 : Outcome ⟨14, 11, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 11, 17, 2⟩, ⟨12, 11, 17, 4⟩, ⟨11, 11, 17, 6⟩, ⟨10, 11, 17, 8⟩, ⟨14, 10, 17, 2⟩, ⟨14, 9, 17, 4⟩, ⟨14, 8, 17, 6⟩, ⟨14, 7, 17, 8⟩, ⟨14, 11, 16, 2⟩, ⟨14, 11, 15, 4⟩, ⟨14, 11, 14, 6⟩, ⟨14, 11, 13, 8⟩]
  exact AllWinning.cons node_24374 (AllWinning.cons node_23989 (AllWinning.cons node_23575 (AllWinning.cons node_23123 (AllWinning.cons node_24396 (AllWinning.cons node_24053 (AllWinning.cons node_23661 (AllWinning.cons node_23253 (AllWinning.cons node_24398 (AllWinning.cons node_24058 (AllWinning.cons node_23667 (AllWinning.cons node_23260 (AllWinning.nil))))))))))))

theorem node_24689 : Outcome ⟨14, 11, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 11, 17, 2⟩, ⟨12, 11, 17, 4⟩, ⟨11, 11, 17, 6⟩, ⟨10, 11, 17, 8⟩, ⟨9, 11, 17, 10⟩, ⟨8, 11, 17, 12⟩, ⟨14, 10, 17, 2⟩, ⟨14, 9, 17, 4⟩, ⟨14, 8, 17, 6⟩, ⟨14, 7, 17, 8⟩, ⟨14, 6, 17, 10⟩, ⟨14, 5, 17, 12⟩, ⟨14, 11, 16, 2⟩, ⟨14, 11, 15, 4⟩, ⟨14, 11, 14, 6⟩, ⟨14, 11, 13, 8⟩, ⟨14, 11, 12, 10⟩, ⟨14, 11, 11, 12⟩]
  exact AllWinning.cons node_24374 (AllWinning.cons node_23989 (AllWinning.cons node_23575 (AllWinning.cons node_23123 (AllWinning.cons node_22565 (AllWinning.cons node_21961 (AllWinning.cons node_24396 (AllWinning.cons node_24053 (AllWinning.cons node_23661 (AllWinning.cons node_23253 (AllWinning.cons node_22750 (AllWinning.cons node_22181 (AllWinning.cons node_24398 (AllWinning.cons node_24058 (AllWinning.cons node_23667 (AllWinning.cons node_23260 (AllWinning.cons node_22767 (AllWinning.cons node_22195 (AllWinning.nil))))))))))))))))))

theorem node_24690 : Outcome ⟨14, 11, 17, 10⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 16⟩) (by decide) node_20941

theorem node_24691 : Outcome ⟨14, 12, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 12, 16, 4⟩) (by decide) node_23991

theorem node_24692 : Outcome ⟨14, 12, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 12, 16, 4⟩) (by decide) node_23991

theorem node_24693 : Outcome ⟨14, 12, 16, 10⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 16⟩) (by decide) node_20563

theorem node_24694 : Outcome ⟨14, 13, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 13, 15, 2⟩, ⟨12, 13, 15, 4⟩, ⟨11, 13, 15, 6⟩, ⟨10, 13, 15, 8⟩, ⟨14, 12, 15, 2⟩, ⟨14, 11, 15, 4⟩, ⟨14, 10, 15, 6⟩, ⟨14, 9, 15, 8⟩, ⟨14, 13, 14, 2⟩, ⟨14, 13, 13, 4⟩, ⟨14, 13, 12, 6⟩, ⟨14, 13, 11, 8⟩]
  exact AllWinning.cons node_24378 (AllWinning.cons node_23993 (AllWinning.cons node_23579 (AllWinning.cons node_23128 (AllWinning.cons node_24401 (AllWinning.cons node_24058 (AllWinning.cons node_23665 (AllWinning.cons node_23256 (AllWinning.cons node_24404 (AllWinning.cons node_24062 (AllWinning.cons node_23672 (AllWinning.cons node_23265 (AllWinning.nil))))))))))))

theorem node_24695 : Outcome ⟨14, 13, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 13, 15, 2⟩, ⟨12, 13, 15, 4⟩, ⟨11, 13, 15, 6⟩, ⟨10, 13, 15, 8⟩, ⟨9, 13, 15, 10⟩, ⟨8, 13, 15, 12⟩, ⟨14, 12, 15, 2⟩, ⟨14, 11, 15, 4⟩, ⟨14, 10, 15, 6⟩, ⟨14, 9, 15, 8⟩, ⟨14, 8, 15, 10⟩, ⟨14, 7, 15, 12⟩, ⟨14, 13, 14, 2⟩, ⟨14, 13, 13, 4⟩, ⟨14, 13, 12, 6⟩, ⟨14, 13, 11, 8⟩, ⟨14, 13, 10, 10⟩, ⟨14, 13, 9, 12⟩]
  exact AllWinning.cons node_24378 (AllWinning.cons node_23993 (AllWinning.cons node_23579 (AllWinning.cons node_23128 (AllWinning.cons node_22573 (AllWinning.cons node_21968 (AllWinning.cons node_24401 (AllWinning.cons node_24058 (AllWinning.cons node_23665 (AllWinning.cons node_23256 (AllWinning.cons node_22757 (AllWinning.cons node_22186 (AllWinning.cons node_24404 (AllWinning.cons node_24062 (AllWinning.cons node_23672 (AllWinning.cons node_23265 (AllWinning.cons node_22774 (AllWinning.cons node_22201 (AllWinning.nil))))))))))))))))))

theorem node_24696 : Outcome ⟨14, 14, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 14, 2⟩, ⟨12, 14, 14, 4⟩, ⟨14, 13, 14, 2⟩, ⟨14, 12, 14, 4⟩, ⟨14, 14, 13, 2⟩, ⟨14, 14, 12, 4⟩]
  exact AllWinning.cons node_24381 (AllWinning.cons node_23996 (AllWinning.cons node_24404 (AllWinning.cons node_24060 (AllWinning.cons node_24405 (AllWinning.cons node_24065 (AllWinning.nil))))))

theorem node_24697 : Outcome ⟨14, 14, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 14, 2⟩, ⟨12, 14, 14, 4⟩, ⟨11, 14, 14, 6⟩, ⟨10, 14, 14, 8⟩, ⟨14, 13, 14, 2⟩, ⟨14, 12, 14, 4⟩, ⟨14, 11, 14, 6⟩, ⟨14, 10, 14, 8⟩, ⟨14, 14, 13, 2⟩, ⟨14, 14, 12, 4⟩, ⟨14, 14, 11, 6⟩, ⟨14, 14, 10, 8⟩]
  exact AllWinning.cons node_24381 (AllWinning.cons node_23996 (AllWinning.cons node_23581 (AllWinning.cons node_23130 (AllWinning.cons node_24404 (AllWinning.cons node_24060 (AllWinning.cons node_23667 (AllWinning.cons node_23258 (AllWinning.cons node_24405 (AllWinning.cons node_24065 (AllWinning.cons node_23675 (AllWinning.cons node_23267 (AllWinning.nil))))))))))))

theorem node_24698 : Outcome ⟨14, 14, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 14, 2⟩, ⟨12, 14, 14, 4⟩, ⟨11, 14, 14, 6⟩, ⟨10, 14, 14, 8⟩, ⟨9, 14, 14, 10⟩, ⟨8, 14, 14, 12⟩, ⟨14, 13, 14, 2⟩, ⟨14, 12, 14, 4⟩, ⟨14, 11, 14, 6⟩, ⟨14, 10, 14, 8⟩, ⟨14, 9, 14, 10⟩, ⟨14, 8, 14, 12⟩, ⟨14, 14, 13, 2⟩, ⟨14, 14, 12, 4⟩, ⟨14, 14, 11, 6⟩, ⟨14, 14, 10, 8⟩, ⟨14, 14, 9, 10⟩, ⟨14, 14, 8, 12⟩]
  exact AllWinning.cons node_24381 (AllWinning.cons node_23996 (AllWinning.cons node_23581 (AllWinning.cons node_23130 (AllWinning.cons node_22578 (AllWinning.cons node_21970 (AllWinning.cons node_24404 (AllWinning.cons node_24060 (AllWinning.cons node_23667 (AllWinning.cons node_23258 (AllWinning.cons node_22762 (AllWinning.cons node_22188 (AllWinning.cons node_24405 (AllWinning.cons node_24065 (AllWinning.cons node_23675 (AllWinning.cons node_23267 (AllWinning.cons node_22779 (AllWinning.cons node_22203 (AllWinning.nil))))))))))))))))))

theorem node_24699 : Outcome ⟨14, 14, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 14, 2⟩, ⟨12, 14, 14, 4⟩, ⟨11, 14, 14, 6⟩, ⟨10, 14, 14, 8⟩, ⟨9, 14, 14, 10⟩, ⟨8, 14, 14, 12⟩, ⟨7, 14, 14, 14⟩, ⟨6, 14, 14, 16⟩, ⟨5, 14, 14, 18⟩, ⟨4, 14, 14, 20⟩, ⟨3, 14, 14, 22⟩, ⟨2, 14, 14, 24⟩, ⟨14, 13, 14, 2⟩, ⟨14, 12, 14, 4⟩, ⟨14, 11, 14, 6⟩, ⟨14, 10, 14, 8⟩, ⟨14, 9, 14, 10⟩, ⟨14, 8, 14, 12⟩, ⟨14, 7, 14, 14⟩, ⟨14, 6, 14, 16⟩, ⟨14, 5, 14, 18⟩, ⟨14, 4, 14, 20⟩, ⟨14, 3, 14, 22⟩, ⟨14, 2, 14, 24⟩, ⟨14, 14, 13, 2⟩, ⟨14, 14, 12, 4⟩, ⟨14, 14, 11, 6⟩, ⟨14, 14, 10, 8⟩, ⟨14, 14, 9, 10⟩, ⟨14, 14, 8, 12⟩, ⟨14, 14, 7, 14⟩, ⟨14, 14, 6, 16⟩, ⟨14, 14, 5, 18⟩, ⟨14, 14, 4, 20⟩, ⟨14, 14, 3, 22⟩, ⟨14, 14, 2, 24⟩]
  exact AllWinning.cons node_24381 (AllWinning.cons node_23996 (AllWinning.cons node_23581 (AllWinning.cons node_23130 (AllWinning.cons node_22578 (AllWinning.cons node_21970 (AllWinning.cons node_21349 (AllWinning.cons node_20568 (AllWinning.cons node_19842 (AllWinning.cons node_18949 (AllWinning.cons node_17995 (AllWinning.cons node_17069 (AllWinning.cons node_24404 (AllWinning.cons node_24060 (AllWinning.cons node_23667 (AllWinning.cons node_23258 (AllWinning.cons node_22762 (AllWinning.cons node_22188 (AllWinning.cons node_21592 (AllWinning.cons node_20949 (AllWinning.cons node_20199 (AllWinning.cons node_19422 (AllWinning.cons node_18555 (AllWinning.cons node_17641 (AllWinning.cons node_24405 (AllWinning.cons node_24065 (AllWinning.cons node_23675 (AllWinning.cons node_23267 (AllWinning.cons node_22779 (AllWinning.cons node_22203 (AllWinning.cons node_21608 (AllWinning.cons node_20965 (AllWinning.cons node_20228 (AllWinning.cons node_19443 (AllWinning.cons node_18592 (AllWinning.cons node_17681 (AllWinning.nil))))))))))))))))))))))))))))))))))))

theorem node_24700 : Outcome ⟨14, 15, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 13, 2⟩, ⟨12, 15, 13, 4⟩, ⟨11, 15, 13, 6⟩, ⟨10, 15, 13, 8⟩, ⟨14, 14, 13, 2⟩, ⟨14, 13, 13, 4⟩, ⟨14, 12, 13, 6⟩, ⟨14, 11, 13, 8⟩, ⟨14, 15, 12, 2⟩, ⟨14, 15, 11, 4⟩, ⟨14, 15, 10, 6⟩, ⟨14, 15, 9, 8⟩]
  exact AllWinning.cons node_24382 (AllWinning.cons node_23998 (AllWinning.cons node_23583 (AllWinning.cons node_23132 (AllWinning.cons node_24405 (AllWinning.cons node_24062 (AllWinning.cons node_23669 (AllWinning.cons node_23260 (AllWinning.cons node_24406 (AllWinning.cons node_24068 (AllWinning.cons node_23677 (AllWinning.cons node_23269 (AllWinning.nil))))))))))))

theorem node_24701 : Outcome ⟨14, 15, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 13, 2⟩, ⟨12, 15, 13, 4⟩, ⟨11, 15, 13, 6⟩, ⟨10, 15, 13, 8⟩, ⟨9, 15, 13, 10⟩, ⟨8, 15, 13, 12⟩, ⟨14, 14, 13, 2⟩, ⟨14, 13, 13, 4⟩, ⟨14, 12, 13, 6⟩, ⟨14, 11, 13, 8⟩, ⟨14, 10, 13, 10⟩, ⟨14, 9, 13, 12⟩, ⟨14, 15, 12, 2⟩, ⟨14, 15, 11, 4⟩, ⟨14, 15, 10, 6⟩, ⟨14, 15, 9, 8⟩, ⟨14, 15, 8, 10⟩, ⟨14, 15, 7, 12⟩]
  exact AllWinning.cons node_24382 (AllWinning.cons node_23998 (AllWinning.cons node_23583 (AllWinning.cons node_23132 (AllWinning.cons node_22582 (AllWinning.cons node_21973 (AllWinning.cons node_24405 (AllWinning.cons node_24062 (AllWinning.cons node_23669 (AllWinning.cons node_23260 (AllWinning.cons node_22765 (AllWinning.cons node_22190 (AllWinning.cons node_24406 (AllWinning.cons node_24068 (AllWinning.cons node_23677 (AllWinning.cons node_23269 (AllWinning.cons node_22784 (AllWinning.cons node_22205 (AllWinning.nil))))))))))))))))))

theorem node_24702 : Outcome ⟨14, 16, 12, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 12, 4⟩) (by decide) node_24001

theorem node_24703 : Outcome ⟨14, 16, 12, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 12, 4⟩) (by decide) node_24001

theorem node_24704 : Outcome ⟨14, 16, 12, 10⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 16⟩) (by decide) node_20579

theorem node_24705 : Outcome ⟨14, 17, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 11, 2⟩, ⟨12, 17, 11, 4⟩, ⟨14, 16, 11, 2⟩, ⟨14, 15, 11, 4⟩, ⟨14, 17, 10, 2⟩, ⟨14, 17, 9, 4⟩]
  exact AllWinning.cons node_24388 (AllWinning.cons node_24003 (AllWinning.cons node_24409 (AllWinning.cons node_24068 (AllWinning.cons node_24412 (AllWinning.cons node_24072 (AllWinning.nil))))))

theorem node_24706 : Outcome ⟨14, 17, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 11, 2⟩, ⟨12, 17, 11, 4⟩, ⟨11, 17, 11, 6⟩, ⟨10, 17, 11, 8⟩, ⟨14, 16, 11, 2⟩, ⟨14, 15, 11, 4⟩, ⟨14, 14, 11, 6⟩, ⟨14, 13, 11, 8⟩, ⟨14, 17, 10, 2⟩, ⟨14, 17, 9, 4⟩, ⟨14, 17, 8, 6⟩, ⟨14, 17, 7, 8⟩]
  exact AllWinning.cons node_24388 (AllWinning.cons node_24003 (AllWinning.cons node_23586 (AllWinning.cons node_23137 (AllWinning.cons node_24409 (AllWinning.cons node_24068 (AllWinning.cons node_23675 (AllWinning.cons node_23265 (AllWinning.cons node_24412 (AllWinning.cons node_24072 (AllWinning.cons node_23681 (AllWinning.cons node_23272 (AllWinning.nil))))))))))))

theorem node_24707 : Outcome ⟨14, 17, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 11, 2⟩, ⟨12, 17, 11, 4⟩, ⟨11, 17, 11, 6⟩, ⟨10, 17, 11, 8⟩, ⟨9, 17, 11, 10⟩, ⟨8, 17, 11, 12⟩, ⟨14, 16, 11, 2⟩, ⟨14, 15, 11, 4⟩, ⟨14, 14, 11, 6⟩, ⟨14, 13, 11, 8⟩, ⟨14, 12, 11, 10⟩, ⟨14, 11, 11, 12⟩, ⟨14, 17, 10, 2⟩, ⟨14, 17, 9, 4⟩, ⟨14, 17, 8, 6⟩, ⟨14, 17, 7, 8⟩, ⟨14, 17, 6, 10⟩, ⟨14, 17, 5, 12⟩]
  exact AllWinning.cons node_24388 (AllWinning.cons node_24003 (AllWinning.cons node_23586 (AllWinning.cons node_23137 (AllWinning.cons node_22588 (AllWinning.cons node_21981 (AllWinning.cons node_24409 (AllWinning.cons node_24068 (AllWinning.cons node_23675 (AllWinning.cons node_23265 (AllWinning.cons node_22770 (AllWinning.cons node_22195 (AllWinning.cons node_24412 (AllWinning.cons node_24072 (AllWinning.cons node_23681 (AllWinning.cons node_23272 (AllWinning.cons node_22788 (AllWinning.cons node_22210 (AllWinning.nil))))))))))))))))))

theorem node_24708 : Outcome ⟨14, 17, 11, 10⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 16⟩) (by decide) node_20978

theorem node_24709 : Outcome ⟨14, 18, 10, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 10, 4⟩) (by decide) node_24004

theorem node_24710 : Outcome ⟨14, 19, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 9, 2⟩, ⟨12, 19, 9, 4⟩, ⟨14, 18, 9, 2⟩, ⟨14, 17, 9, 4⟩, ⟨14, 19, 8, 2⟩, ⟨14, 19, 7, 4⟩]
  exact AllWinning.cons node_24390 (AllWinning.cons node_24006 (AllWinning.cons node_24414 (AllWinning.cons node_24072 (AllWinning.cons node_24416 (AllWinning.cons node_24075 (AllWinning.nil))))))

theorem node_24711 : Outcome ⟨14, 19, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 9, 2⟩, ⟨12, 19, 9, 4⟩, ⟨11, 19, 9, 6⟩, ⟨10, 19, 9, 8⟩, ⟨14, 18, 9, 2⟩, ⟨14, 17, 9, 4⟩, ⟨14, 16, 9, 6⟩, ⟨14, 15, 9, 8⟩, ⟨14, 19, 8, 2⟩, ⟨14, 19, 7, 4⟩, ⟨14, 19, 6, 6⟩, ⟨14, 19, 5, 8⟩]
  exact AllWinning.cons node_24390 (AllWinning.cons node_24006 (AllWinning.cons node_23589 (AllWinning.cons node_23140 (AllWinning.cons node_24414 (AllWinning.cons node_24072 (AllWinning.cons node_23679 (AllWinning.cons node_23269 (AllWinning.cons node_24416 (AllWinning.cons node_24075 (AllWinning.cons node_23685 (AllWinning.cons node_23276 (AllWinning.nil))))))))))))

theorem node_24712 : Outcome ⟨15, 7, 20, 12⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 16⟩) (by decide) node_21006

theorem node_24713 : Outcome ⟨15, 8, 19, 4⟩ true :=
  Outcome.win (q := ⟨13, 8, 19, 4⟩) (by decide) node_24012

theorem node_24714 : Outcome ⟨15, 8, 19, 8⟩ true :=
  Outcome.win (q := ⟨13, 8, 19, 4⟩) (by decide) node_24012

theorem node_24715 : Outcome ⟨15, 9, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 18, 2⟩, ⟨13, 9, 18, 4⟩, ⟨15, 8, 18, 2⟩, ⟨15, 7, 18, 4⟩, ⟨15, 9, 17, 2⟩, ⟨15, 9, 16, 4⟩]
  exact AllWinning.cons node_24394 (AllWinning.cons node_24015 (AllWinning.cons node_24421 (AllWinning.cons node_24082 (AllWinning.cons node_24424 (AllWinning.cons node_24085 (AllWinning.nil))))))

theorem node_24716 : Outcome ⟨15, 9, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 18, 2⟩, ⟨13, 9, 18, 4⟩, ⟨12, 9, 18, 6⟩, ⟨11, 9, 18, 8⟩, ⟨15, 8, 18, 2⟩, ⟨15, 7, 18, 4⟩, ⟨15, 6, 18, 6⟩, ⟨15, 5, 18, 8⟩, ⟨15, 9, 17, 2⟩, ⟨15, 9, 16, 4⟩, ⟨15, 9, 15, 6⟩, ⟨15, 9, 14, 8⟩]
  exact AllWinning.cons node_24394 (AllWinning.cons node_24015 (AllWinning.cons node_23596 (AllWinning.cons node_23146 (AllWinning.cons node_24421 (AllWinning.cons node_24082 (AllWinning.cons node_23692 (AllWinning.cons node_23282 (AllWinning.cons node_24424 (AllWinning.cons node_24085 (AllWinning.cons node_23697 (AllWinning.cons node_23290 (AllWinning.nil))))))))))))

theorem node_24717 : Outcome ⟨15, 9, 18, 14⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 12⟩) (by decide) node_22224

theorem node_24718 : Outcome ⟨15, 10, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 10, 15, 4⟩) (by decide) node_24088

theorem node_24719 : Outcome ⟨15, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨13, 11, 16, 4⟩) (by decide) node_24020

theorem node_24720 : Outcome ⟨15, 11, 16, 8⟩ true :=
  Outcome.win (q := ⟨13, 11, 16, 4⟩) (by decide) node_24020

theorem node_24721 : Outcome ⟨15, 11, 16, 14⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 20⟩) (by decide) node_19465

theorem node_24722 : Outcome ⟨15, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨15, 10, 15, 4⟩) (by decide) node_24088

theorem node_24723 : Outcome ⟨15, 12, 15, 6⟩ true :=
  Outcome.win (q := ⟨15, 10, 15, 4⟩) (by decide) node_24088

theorem node_24724 : Outcome ⟨15, 13, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 14, 2⟩, ⟨13, 13, 14, 4⟩, ⟨12, 13, 14, 6⟩, ⟨11, 13, 14, 8⟩, ⟨15, 12, 14, 2⟩, ⟨15, 11, 14, 4⟩, ⟨15, 10, 14, 6⟩, ⟨15, 9, 14, 8⟩, ⟨15, 13, 13, 2⟩, ⟨15, 13, 12, 4⟩, ⟨15, 13, 11, 6⟩, ⟨15, 13, 10, 8⟩]
  exact AllWinning.cons node_24404 (AllWinning.cons node_24027 (AllWinning.cons node_23605 (AllWinning.cons node_23156 (AllWinning.cons node_24428 (AllWinning.cons node_24092 (AllWinning.cons node_23699 (AllWinning.cons node_23290 (AllWinning.cons node_24431 (AllWinning.cons node_24098 (AllWinning.cons node_23705 (AllWinning.cons node_23300 (AllWinning.nil))))))))))))

theorem node_24725 : Outcome ⟨15, 13, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 14, 2⟩, ⟨13, 13, 14, 4⟩, ⟨12, 13, 14, 6⟩, ⟨11, 13, 14, 8⟩, ⟨10, 13, 14, 10⟩, ⟨9, 13, 14, 12⟩, ⟨15, 12, 14, 2⟩, ⟨15, 11, 14, 4⟩, ⟨15, 10, 14, 6⟩, ⟨15, 9, 14, 8⟩, ⟨15, 8, 14, 10⟩, ⟨15, 7, 14, 12⟩, ⟨15, 13, 13, 2⟩, ⟨15, 13, 12, 4⟩, ⟨15, 13, 11, 6⟩, ⟨15, 13, 10, 8⟩, ⟨15, 13, 9, 10⟩, ⟨15, 13, 8, 12⟩]
  exact AllWinning.cons node_24404 (AllWinning.cons node_24027 (AllWinning.cons node_23605 (AllWinning.cons node_23156 (AllWinning.cons node_22607 (AllWinning.cons node_21999 (AllWinning.cons node_24428 (AllWinning.cons node_24092 (AllWinning.cons node_23699 (AllWinning.cons node_23290 (AllWinning.cons node_22812 (AllWinning.cons node_22237 (AllWinning.cons node_24431 (AllWinning.cons node_24098 (AllWinning.cons node_23705 (AllWinning.cons node_23300 (AllWinning.cons node_22827 (AllWinning.cons node_22255 (AllWinning.nil))))))))))))))))))

theorem node_24726 : Outcome ⟨15, 13, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 14, 2⟩, ⟨13, 13, 14, 4⟩, ⟨12, 13, 14, 6⟩, ⟨11, 13, 14, 8⟩, ⟨10, 13, 14, 10⟩, ⟨9, 13, 14, 12⟩, ⟨8, 13, 14, 14⟩, ⟨7, 13, 14, 16⟩, ⟨15, 12, 14, 2⟩, ⟨15, 11, 14, 4⟩, ⟨15, 10, 14, 6⟩, ⟨15, 9, 14, 8⟩, ⟨15, 8, 14, 10⟩, ⟨15, 7, 14, 12⟩, ⟨15, 6, 14, 14⟩, ⟨15, 5, 14, 16⟩, ⟨15, 13, 13, 2⟩, ⟨15, 13, 12, 4⟩, ⟨15, 13, 11, 6⟩, ⟨15, 13, 10, 8⟩, ⟨15, 13, 9, 10⟩, ⟨15, 13, 8, 12⟩, ⟨15, 13, 7, 14⟩, ⟨15, 13, 6, 16⟩]
  exact AllWinning.cons node_24404 (AllWinning.cons node_24027 (AllWinning.cons node_23605 (AllWinning.cons node_23156 (AllWinning.cons node_22607 (AllWinning.cons node_21999 (AllWinning.cons node_21376 (AllWinning.cons node_20615 (AllWinning.cons node_24428 (AllWinning.cons node_24092 (AllWinning.cons node_23699 (AllWinning.cons node_23290 (AllWinning.cons node_22812 (AllWinning.cons node_22237 (AllWinning.cons node_21634 (AllWinning.cons node_20995 (AllWinning.cons node_24431 (AllWinning.cons node_24098 (AllWinning.cons node_23705 (AllWinning.cons node_23300 (AllWinning.cons node_22827 (AllWinning.cons node_22255 (AllWinning.cons node_21651 (AllWinning.cons node_21028 (AllWinning.nil))))))))))))))))))))))))

theorem node_24727 : Outcome ⟨15, 13, 14, 12⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 18⟩) (by decide) node_19870

theorem node_24728 : Outcome ⟨15, 14, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 13, 2⟩, ⟨13, 14, 13, 4⟩, ⟨12, 14, 13, 6⟩, ⟨11, 14, 13, 8⟩, ⟨15, 13, 13, 2⟩, ⟨15, 12, 13, 4⟩, ⟨15, 11, 13, 6⟩, ⟨15, 10, 13, 8⟩, ⟨15, 14, 12, 2⟩, ⟨15, 14, 11, 4⟩, ⟨15, 14, 10, 6⟩, ⟨15, 14, 9, 8⟩]
  exact AllWinning.cons node_24405 (AllWinning.cons node_24029 (AllWinning.cons node_23608 (AllWinning.cons node_23158 (AllWinning.cons node_24431 (AllWinning.cons node_24094 (AllWinning.cons node_23701 (AllWinning.cons node_23292 (AllWinning.cons node_24434 (AllWinning.cons node_24102 (AllWinning.cons node_23707 (AllWinning.cons node_23302 (AllWinning.nil))))))))))))

theorem node_24729 : Outcome ⟨15, 14, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 13, 2⟩, ⟨13, 14, 13, 4⟩, ⟨12, 14, 13, 6⟩, ⟨11, 14, 13, 8⟩, ⟨10, 14, 13, 10⟩, ⟨9, 14, 13, 12⟩, ⟨15, 13, 13, 2⟩, ⟨15, 12, 13, 4⟩, ⟨15, 11, 13, 6⟩, ⟨15, 10, 13, 8⟩, ⟨15, 9, 13, 10⟩, ⟨15, 8, 13, 12⟩, ⟨15, 14, 12, 2⟩, ⟨15, 14, 11, 4⟩, ⟨15, 14, 10, 6⟩, ⟨15, 14, 9, 8⟩, ⟨15, 14, 8, 10⟩, ⟨15, 14, 7, 12⟩]
  exact AllWinning.cons node_24405 (AllWinning.cons node_24029 (AllWinning.cons node_23608 (AllWinning.cons node_23158 (AllWinning.cons node_22610 (AllWinning.cons node_22001 (AllWinning.cons node_24431 (AllWinning.cons node_24094 (AllWinning.cons node_23701 (AllWinning.cons node_23292 (AllWinning.cons node_22816 (AllWinning.cons node_22240 (AllWinning.cons node_24434 (AllWinning.cons node_24102 (AllWinning.cons node_23707 (AllWinning.cons node_23302 (AllWinning.cons node_22832 (AllWinning.cons node_22257 (AllWinning.nil))))))))))))))))))

theorem node_24730 : Outcome ⟨15, 14, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 13, 2⟩, ⟨13, 14, 13, 4⟩, ⟨12, 14, 13, 6⟩, ⟨11, 14, 13, 8⟩, ⟨10, 14, 13, 10⟩, ⟨9, 14, 13, 12⟩, ⟨8, 14, 13, 14⟩, ⟨7, 14, 13, 16⟩, ⟨15, 13, 13, 2⟩, ⟨15, 12, 13, 4⟩, ⟨15, 11, 13, 6⟩, ⟨15, 10, 13, 8⟩, ⟨15, 9, 13, 10⟩, ⟨15, 8, 13, 12⟩, ⟨15, 7, 13, 14⟩, ⟨15, 6, 13, 16⟩, ⟨15, 14, 12, 2⟩, ⟨15, 14, 11, 4⟩, ⟨15, 14, 10, 6⟩, ⟨15, 14, 9, 8⟩, ⟨15, 14, 8, 10⟩, ⟨15, 14, 7, 12⟩, ⟨15, 14, 6, 14⟩, ⟨15, 14, 5, 16⟩]
  exact AllWinning.cons node_24405 (AllWinning.cons node_24029 (AllWinning.cons node_23608 (AllWinning.cons node_23158 (AllWinning.cons node_22610 (AllWinning.cons node_22001 (AllWinning.cons node_21379 (AllWinning.cons node_20617 (AllWinning.cons node_24431 (AllWinning.cons node_24094 (AllWinning.cons node_23701 (AllWinning.cons node_23292 (AllWinning.cons node_22816 (AllWinning.cons node_22240 (AllWinning.cons node_21637 (AllWinning.cons node_20999 (AllWinning.cons node_24434 (AllWinning.cons node_24102 (AllWinning.cons node_23707 (AllWinning.cons node_23302 (AllWinning.cons node_22832 (AllWinning.cons node_22257 (AllWinning.cons node_21654 (AllWinning.cons node_21031 (AllWinning.nil))))))))))))))))))))))))

theorem node_24731 : Outcome ⟨15, 14, 13, 12⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 18⟩) (by decide) node_19877

theorem node_24732 : Outcome ⟨15, 15, 12, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 10, 4⟩) (by decide) node_24104

theorem node_24733 : Outcome ⟨15, 15, 12, 6⟩ true :=
  Outcome.win (q := ⟨15, 15, 10, 4⟩) (by decide) node_24104

end RQ9F1
