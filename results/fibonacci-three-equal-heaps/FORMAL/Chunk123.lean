import Chunk122
set_option autoImplicit false
namespace RQ9F1

theorem node_25824 : Outcome ⟨15, 18, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 16, 2⟩, ⟨13, 18, 16, 4⟩, ⟨12, 18, 16, 6⟩, ⟨11, 18, 16, 8⟩, ⟨10, 18, 16, 10⟩, ⟨9, 18, 16, 12⟩, ⟨15, 17, 16, 2⟩, ⟨15, 16, 16, 4⟩, ⟨15, 15, 16, 6⟩, ⟨15, 14, 16, 8⟩, ⟨15, 13, 16, 10⟩, ⟨15, 12, 16, 12⟩, ⟨15, 18, 15, 2⟩, ⟨15, 18, 14, 4⟩, ⟨15, 18, 13, 6⟩, ⟨15, 18, 12, 8⟩, ⟨15, 18, 11, 10⟩, ⟨15, 18, 10, 12⟩]
  exact AllWinning.cons node_25736 (AllWinning.cons node_25622 (AllWinning.cons node_25499 (AllWinning.cons node_25326 (AllWinning.cons node_25120 (AllWinning.cons node_24879 (AllWinning.cons node_25745 (AllWinning.cons node_25646 (AllWinning.cons node_25529 (AllWinning.cons node_25388 (AllWinning.cons node_25209 (AllWinning.cons node_24977 (AllWinning.cons node_25746 (AllWinning.cons node_25650 (AllWinning.cons node_25534 (AllWinning.cons node_25397 (AllWinning.cons node_25217 (AllWinning.cons node_24989 (AllWinning.nil))))))))))))))))))

theorem node_25825 : Outcome ⟨15, 18, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 16, 2⟩, ⟨13, 18, 16, 4⟩, ⟨12, 18, 16, 6⟩, ⟨11, 18, 16, 8⟩, ⟨10, 18, 16, 10⟩, ⟨9, 18, 16, 12⟩, ⟨8, 18, 16, 14⟩, ⟨7, 18, 16, 16⟩, ⟨15, 17, 16, 2⟩, ⟨15, 16, 16, 4⟩, ⟨15, 15, 16, 6⟩, ⟨15, 14, 16, 8⟩, ⟨15, 13, 16, 10⟩, ⟨15, 12, 16, 12⟩, ⟨15, 11, 16, 14⟩, ⟨15, 10, 16, 16⟩, ⟨15, 18, 15, 2⟩, ⟨15, 18, 14, 4⟩, ⟨15, 18, 13, 6⟩, ⟨15, 18, 12, 8⟩, ⟨15, 18, 11, 10⟩, ⟨15, 18, 10, 12⟩, ⟨15, 18, 9, 14⟩, ⟨15, 18, 8, 16⟩]
  exact AllWinning.cons node_25736 (AllWinning.cons node_25622 (AllWinning.cons node_25499 (AllWinning.cons node_25326 (AllWinning.cons node_25120 (AllWinning.cons node_24879 (AllWinning.cons node_24569 (AllWinning.cons node_24283 (AllWinning.cons node_25745 (AllWinning.cons node_25646 (AllWinning.cons node_25529 (AllWinning.cons node_25388 (AllWinning.cons node_25209 (AllWinning.cons node_24977 (AllWinning.cons node_24721 (AllWinning.cons node_24426 (AllWinning.cons node_25746 (AllWinning.cons node_25650 (AllWinning.cons node_25534 (AllWinning.cons node_25397 (AllWinning.cons node_25217 (AllWinning.cons node_24989 (AllWinning.cons node_24739 (AllWinning.cons node_24443 (AllWinning.nil))))))))))))))))))))))))

theorem node_25826 : Outcome ⟨15, 19, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 19, 15, 2⟩, ⟨13, 19, 15, 4⟩, ⟨15, 18, 15, 2⟩, ⟨15, 17, 15, 4⟩, ⟨15, 19, 14, 2⟩, ⟨15, 19, 13, 4⟩]
  exact AllWinning.cons node_25738 (AllWinning.cons node_25624 (AllWinning.cons node_25746 (AllWinning.cons node_25648 (AllWinning.cons node_25747 (AllWinning.cons node_25652 (AllWinning.nil))))))

theorem node_25827 : Outcome ⟨16, 14, 19, 4⟩ true :=
  Outcome.win (q := ⟨16, 11, 19, 6⟩) (by decide) node_25539

theorem node_25828 : Outcome ⟨16, 15, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 18, 2⟩, ⟨14, 15, 18, 4⟩, ⟨16, 14, 18, 2⟩, ⟨16, 13, 18, 4⟩, ⟨16, 15, 17, 2⟩, ⟨16, 15, 16, 4⟩]
  exact AllWinning.cons node_25743 (AllWinning.cons node_25629 (AllWinning.cons node_25750 (AllWinning.cons node_25656 (AllWinning.cons node_25751 (AllWinning.cons node_25658 (AllWinning.nil))))))

theorem node_25829 : Outcome ⟨16, 15, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 18, 2⟩, ⟨14, 15, 18, 4⟩, ⟨13, 15, 18, 6⟩, ⟨12, 15, 18, 8⟩, ⟨16, 14, 18, 2⟩, ⟨16, 13, 18, 4⟩, ⟨16, 12, 18, 6⟩, ⟨16, 11, 18, 8⟩, ⟨16, 15, 17, 2⟩, ⟨16, 15, 16, 4⟩, ⟨16, 15, 15, 6⟩, ⟨16, 15, 14, 8⟩]
  exact AllWinning.cons node_25743 (AllWinning.cons node_25629 (AllWinning.cons node_25506 (AllWinning.cons node_25334 (AllWinning.cons node_25750 (AllWinning.cons node_25656 (AllWinning.cons node_25541 (AllWinning.cons node_25402 (AllWinning.cons node_25751 (AllWinning.cons node_25658 (AllWinning.cons node_25544 (AllWinning.cons node_25411 (AllWinning.nil))))))))))))

theorem node_25830 : Outcome ⟨16, 15, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 18, 2⟩, ⟨14, 15, 18, 4⟩, ⟨13, 15, 18, 6⟩, ⟨12, 15, 18, 8⟩, ⟨11, 15, 18, 10⟩, ⟨10, 15, 18, 12⟩, ⟨16, 14, 18, 2⟩, ⟨16, 13, 18, 4⟩, ⟨16, 12, 18, 6⟩, ⟨16, 11, 18, 8⟩, ⟨16, 10, 18, 10⟩, ⟨16, 9, 18, 12⟩, ⟨16, 15, 17, 2⟩, ⟨16, 15, 16, 4⟩, ⟨16, 15, 15, 6⟩, ⟨16, 15, 14, 8⟩, ⟨16, 15, 13, 10⟩, ⟨16, 15, 12, 12⟩]
  exact AllWinning.cons node_25743 (AllWinning.cons node_25629 (AllWinning.cons node_25506 (AllWinning.cons node_25334 (AllWinning.cons node_25130 (AllWinning.cons node_24890 (AllWinning.cons node_25750 (AllWinning.cons node_25656 (AllWinning.cons node_25541 (AllWinning.cons node_25402 (AllWinning.cons node_25223 (AllWinning.cons node_24994 (AllWinning.cons node_25751 (AllWinning.cons node_25658 (AllWinning.cons node_25544 (AllWinning.cons node_25411 (AllWinning.cons node_25231 (AllWinning.cons node_25004 (AllWinning.nil))))))))))))))))))

theorem node_25831 : Outcome ⟨16, 15, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 18, 2⟩, ⟨14, 15, 18, 4⟩, ⟨13, 15, 18, 6⟩, ⟨12, 15, 18, 8⟩, ⟨11, 15, 18, 10⟩, ⟨10, 15, 18, 12⟩, ⟨9, 15, 18, 14⟩, ⟨8, 15, 18, 16⟩, ⟨16, 14, 18, 2⟩, ⟨16, 13, 18, 4⟩, ⟨16, 12, 18, 6⟩, ⟨16, 11, 18, 8⟩, ⟨16, 10, 18, 10⟩, ⟨16, 9, 18, 12⟩, ⟨16, 8, 18, 14⟩, ⟨16, 7, 18, 16⟩, ⟨16, 15, 17, 2⟩, ⟨16, 15, 16, 4⟩, ⟨16, 15, 15, 6⟩, ⟨16, 15, 14, 8⟩, ⟨16, 15, 13, 10⟩, ⟨16, 15, 12, 12⟩, ⟨16, 15, 11, 14⟩, ⟨16, 15, 10, 16⟩]
  exact AllWinning.cons node_25743 (AllWinning.cons node_25629 (AllWinning.cons node_25506 (AllWinning.cons node_25334 (AllWinning.cons node_25130 (AllWinning.cons node_24890 (AllWinning.cons node_24582 (AllWinning.cons node_24292 (AllWinning.cons node_25750 (AllWinning.cons node_25656 (AllWinning.cons node_25541 (AllWinning.cons node_25402 (AllWinning.cons node_25223 (AllWinning.cons node_24994 (AllWinning.cons node_24746 (AllWinning.cons node_24450 (AllWinning.cons node_25751 (AllWinning.cons node_25658 (AllWinning.cons node_25544 (AllWinning.cons node_25411 (AllWinning.cons node_25231 (AllWinning.cons node_25004 (AllWinning.cons node_24761 (AllWinning.cons node_24467 (AllWinning.nil))))))))))))))))))))))))

theorem node_25832 : Outcome ⟨16, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 17, 4⟩) (by decide) node_25631

theorem node_25833 : Outcome ⟨16, 16, 17, 4⟩ true :=
  Outcome.win (q := ⟨16, 16, 13, 8⟩) (by decide) node_25415

theorem node_25834 : Outcome ⟨16, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 4⟩) (by decide) node_25634

theorem node_25835 : Outcome ⟨16, 17, 16, 4⟩ true :=
  Outcome.win (q := ⟨16, 13, 16, 8⟩) (by decide) node_25407

theorem node_25836 : Outcome ⟨16, 18, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 18, 15, 2⟩, ⟨14, 18, 15, 4⟩, ⟨16, 17, 15, 2⟩, ⟨16, 16, 15, 4⟩, ⟨16, 18, 14, 2⟩, ⟨16, 18, 13, 4⟩]
  exact AllWinning.cons node_25746 (AllWinning.cons node_25637 (AllWinning.cons node_25754 (AllWinning.cons node_25660 (AllWinning.cons node_25756 (AllWinning.cons node_25663 (AllWinning.nil))))))

theorem node_25837 : Outcome ⟨16, 18, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 18, 15, 2⟩, ⟨14, 18, 15, 4⟩, ⟨13, 18, 15, 6⟩, ⟨12, 18, 15, 8⟩, ⟨16, 17, 15, 2⟩, ⟨16, 16, 15, 4⟩, ⟨16, 15, 15, 6⟩, ⟨16, 14, 15, 8⟩, ⟨16, 18, 14, 2⟩, ⟨16, 18, 13, 4⟩, ⟨16, 18, 12, 6⟩, ⟨16, 18, 11, 8⟩]
  exact AllWinning.cons node_25746 (AllWinning.cons node_25637 (AllWinning.cons node_25511 (AllWinning.cons node_25341 (AllWinning.cons node_25754 (AllWinning.cons node_25660 (AllWinning.cons node_25544 (AllWinning.cons node_25409 (AllWinning.cons node_25756 (AllWinning.cons node_25663 (AllWinning.cons node_25548 (AllWinning.cons node_25418 (AllWinning.nil))))))))))))

theorem node_25838 : Outcome ⟨16, 18, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 18, 15, 2⟩, ⟨14, 18, 15, 4⟩, ⟨13, 18, 15, 6⟩, ⟨12, 18, 15, 8⟩, ⟨11, 18, 15, 10⟩, ⟨10, 18, 15, 12⟩, ⟨16, 17, 15, 2⟩, ⟨16, 16, 15, 4⟩, ⟨16, 15, 15, 6⟩, ⟨16, 14, 15, 8⟩, ⟨16, 13, 15, 10⟩, ⟨16, 12, 15, 12⟩, ⟨16, 18, 14, 2⟩, ⟨16, 18, 13, 4⟩, ⟨16, 18, 12, 6⟩, ⟨16, 18, 11, 8⟩, ⟨16, 18, 10, 10⟩, ⟨16, 18, 9, 12⟩]
  exact AllWinning.cons node_25746 (AllWinning.cons node_25637 (AllWinning.cons node_25511 (AllWinning.cons node_25341 (AllWinning.cons node_25140 (AllWinning.cons node_24897 (AllWinning.cons node_25754 (AllWinning.cons node_25660 (AllWinning.cons node_25544 (AllWinning.cons node_25409 (AllWinning.cons node_25228 (AllWinning.cons node_25000 (AllWinning.cons node_25756 (AllWinning.cons node_25663 (AllWinning.cons node_25548 (AllWinning.cons node_25418 (AllWinning.cons node_25236 (AllWinning.cons node_25009 (AllWinning.nil))))))))))))))))))

theorem node_25839 : Outcome ⟨16, 18, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 18, 15, 2⟩, ⟨14, 18, 15, 4⟩, ⟨13, 18, 15, 6⟩, ⟨12, 18, 15, 8⟩, ⟨11, 18, 15, 10⟩, ⟨10, 18, 15, 12⟩, ⟨9, 18, 15, 14⟩, ⟨8, 18, 15, 16⟩, ⟨16, 17, 15, 2⟩, ⟨16, 16, 15, 4⟩, ⟨16, 15, 15, 6⟩, ⟨16, 14, 15, 8⟩, ⟨16, 13, 15, 10⟩, ⟨16, 12, 15, 12⟩, ⟨16, 11, 15, 14⟩, ⟨16, 10, 15, 16⟩, ⟨16, 18, 14, 2⟩, ⟨16, 18, 13, 4⟩, ⟨16, 18, 12, 6⟩, ⟨16, 18, 11, 8⟩, ⟨16, 18, 10, 10⟩, ⟨16, 18, 9, 12⟩, ⟨16, 18, 8, 14⟩, ⟨16, 18, 7, 16⟩]
  exact AllWinning.cons node_25746 (AllWinning.cons node_25637 (AllWinning.cons node_25511 (AllWinning.cons node_25341 (AllWinning.cons node_25140 (AllWinning.cons node_24897 (AllWinning.cons node_24596 (AllWinning.cons node_24299 (AllWinning.cons node_25754 (AllWinning.cons node_25660 (AllWinning.cons node_25544 (AllWinning.cons node_25409 (AllWinning.cons node_25228 (AllWinning.cons node_25000 (AllWinning.cons node_24752 (AllWinning.cons node_24455 (AllWinning.cons node_25756 (AllWinning.cons node_25663 (AllWinning.cons node_25548 (AllWinning.cons node_25418 (AllWinning.cons node_25236 (AllWinning.cons node_25009 (AllWinning.cons node_24766 (AllWinning.cons node_24472 (AllWinning.nil))))))))))))))))))))))))

theorem node_25840 : Outcome ⟨16, 19, 14, 4⟩ true :=
  Outcome.win (q := ⟨16, 19, 11, 6⟩) (by decide) node_25551

theorem node_25841 : Outcome ⟨17, 13, 19, 4⟩ true :=
  Outcome.win (q := ⟨17, 13, 17, 4⟩) (by decide) node_25668

theorem node_25842 : Outcome ⟨17, 14, 18, 6⟩ true :=
  Outcome.win (q := ⟨17, 14, 16, 4⟩) (by decide) node_25670

theorem node_25843 : Outcome ⟨17, 15, 17, 6⟩ true :=
  Outcome.win (q := ⟨17, 13, 17, 4⟩) (by decide) node_25668

theorem node_25844 : Outcome ⟨17, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 8⟩) (by decide) node_25356

theorem node_25845 : Outcome ⟨17, 17, 15, 6⟩ true :=
  Outcome.win (q := ⟨17, 17, 13, 4⟩) (by decide) node_25674

theorem node_25846 : Outcome ⟨17, 18, 14, 6⟩ true :=
  Outcome.win (q := ⟨17, 16, 14, 4⟩) (by decide) node_25672

theorem node_25847 : Outcome ⟨17, 19, 13, 4⟩ true :=
  Outcome.win (q := ⟨17, 17, 13, 4⟩) (by decide) node_25674

theorem node_25848 : Outcome ⟨18, 13, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 18, 2⟩, ⟨16, 13, 18, 4⟩, ⟨18, 12, 18, 2⟩, ⟨18, 11, 18, 4⟩, ⟨18, 13, 17, 2⟩, ⟨18, 13, 16, 4⟩]
  exact AllWinning.cons node_25758 (AllWinning.cons node_25656 (AllWinning.cons node_25767 (AllWinning.cons node_25677 (AllWinning.cons node_25768 (AllWinning.cons node_25678 (AllWinning.nil))))))

theorem node_25849 : Outcome ⟨18, 15, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 15, 16, 2⟩, ⟨16, 15, 16, 4⟩, ⟨18, 14, 16, 2⟩, ⟨18, 13, 16, 4⟩, ⟨18, 15, 15, 2⟩, ⟨18, 15, 14, 4⟩]
  exact AllWinning.cons node_25761 (AllWinning.cons node_25658 (AllWinning.cons node_25769 (AllWinning.cons node_25678 (AllWinning.cons node_25770 (AllWinning.cons node_25681 (AllWinning.nil))))))

theorem node_25850 : Outcome ⟨18, 16, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 16, 15, 2⟩, ⟨16, 16, 15, 4⟩, ⟨18, 15, 15, 2⟩, ⟨18, 14, 15, 4⟩, ⟨18, 16, 14, 2⟩, ⟨18, 16, 13, 4⟩]
  exact AllWinning.cons node_25762 (AllWinning.cons node_25660 (AllWinning.cons node_25770 (AllWinning.cons node_25680 (AllWinning.cons node_25771 (AllWinning.cons node_25682 (AllWinning.nil))))))

theorem node_25851 : Outcome ⟨18, 18, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 18, 13, 2⟩, ⟨16, 18, 13, 4⟩, ⟨18, 17, 13, 2⟩, ⟨18, 16, 13, 4⟩, ⟨18, 18, 12, 2⟩, ⟨18, 18, 11, 4⟩]
  exact AllWinning.cons node_25764 (AllWinning.cons node_25663 (AllWinning.cons node_25772 (AllWinning.cons node_25682 (AllWinning.cons node_25773 (AllWinning.cons node_25683 (AllWinning.nil))))))

theorem node_25852 : Outcome ⟨19, 11, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 11, 19, 2⟩, ⟨17, 11, 19, 4⟩, ⟨19, 10, 19, 2⟩, ⟨19, 9, 19, 4⟩, ⟨19, 11, 18, 2⟩, ⟨19, 11, 17, 4⟩]
  exact AllWinning.cons node_25766 (AllWinning.cons node_25665 (AllWinning.cons node_25775 (AllWinning.cons node_25684 (AllWinning.cons node_25777 (AllWinning.cons node_25686 (AllWinning.nil))))))

theorem node_25853 : Outcome ⟨19, 11, 19, 4⟩ true :=
  Outcome.win (q := ⟨16, 11, 19, 6⟩) (by decide) node_25539

theorem node_25854 : Outcome ⟨19, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨17, 13, 17, 4⟩) (by decide) node_25668

theorem node_25855 : Outcome ⟨19, 14, 16, 4⟩ true :=
  Outcome.win (q := ⟨19, 11, 16, 6⟩) (by decide) node_25567

theorem node_25856 : Outcome ⟨19, 16, 14, 4⟩ true :=
  Outcome.win (q := ⟨19, 16, 11, 6⟩) (by decide) node_25574

theorem node_25857 : Outcome ⟨19, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨17, 17, 13, 4⟩) (by decide) node_25674

theorem node_25858 : Outcome ⟨19, 19, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 11, 2⟩, ⟨17, 19, 11, 4⟩, ⟨19, 18, 11, 2⟩, ⟨19, 17, 11, 4⟩, ⟨19, 19, 10, 2⟩, ⟨19, 19, 9, 4⟩]
  exact AllWinning.cons node_25774 (AllWinning.cons node_25676 (AllWinning.cons node_25780 (AllWinning.cons node_25691 (AllWinning.cons node_25781 (AllWinning.cons node_25692 (AllWinning.nil))))))

theorem node_25859 : Outcome ⟨19, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨16, 19, 11, 6⟩) (by decide) node_25551

theorem node_25860 : Outcome ⟨10, 20, 20, 2⟩ true :=
  Outcome.win (q := ⟨8, 20, 20, 4⟩) (by decide) node_25694

theorem node_25861 : Outcome ⟨10, 20, 20, 6⟩ true :=
  Outcome.win (q := ⟨8, 20, 20, 4⟩) (by decide) node_25694

theorem node_25862 : Outcome ⟨11, 19, 20, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 20, 4⟩) (by decide) node_25703

theorem node_25863 : Outcome ⟨11, 20, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 20, 17, 4⟩) (by decide) node_25707

theorem node_25864 : Outcome ⟨12, 18, 20, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 20, 4⟩) (by decide) node_25708

theorem node_25865 : Outcome ⟨12, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 6⟩) (by decide) node_25585

theorem node_25866 : Outcome ⟨12, 19, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 19, 2⟩) (by decide) node_25789

theorem node_25867 : Outcome ⟨12, 20, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 20, 16, 4⟩) (by decide) node_25715

theorem node_25868 : Outcome ⟨12, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨9, 20, 18, 6⟩) (by decide) node_25591

theorem node_25869 : Outcome ⟨13, 17, 20, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 20, 4⟩) (by decide) node_25703

theorem node_25870 : Outcome ⟨13, 17, 20, 6⟩ true :=
  Outcome.win (q := ⟨11, 17, 20, 4⟩) (by decide) node_25703

theorem node_25871 : Outcome ⟨13, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 18, 2⟩) (by decide) node_25800

theorem node_25872 : Outcome ⟨13, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 18, 2⟩) (by decide) node_25800

theorem node_25873 : Outcome ⟨13, 20, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 20, 17, 4⟩) (by decide) node_25707

theorem node_25874 : Outcome ⟨13, 20, 17, 6⟩ true :=
  Outcome.win (q := ⟨11, 20, 17, 4⟩) (by decide) node_25707

theorem node_25875 : Outcome ⟨14, 16, 20, 4⟩ true :=
  Outcome.win (q := ⟨14, 16, 17, 6⟩) (by decide) node_25632

theorem node_25876 : Outcome ⟨14, 17, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 19, 2⟩, ⟨12, 17, 19, 4⟩, ⟨14, 16, 19, 2⟩, ⟨14, 15, 19, 4⟩, ⟨14, 17, 18, 2⟩, ⟨14, 17, 17, 4⟩]
  exact AllWinning.cons node_25798 (AllWinning.cons node_25710 (AllWinning.cons node_25807 (AllWinning.cons node_25732 (AllWinning.cons node_25809 (AllWinning.cons node_25735 (AllWinning.nil))))))

theorem node_25877 : Outcome ⟨14, 18, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 18, 18, 2⟩) (by decide) node_25800

theorem node_25878 : Outcome ⟨14, 19, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 17, 2⟩, ⟨12, 19, 17, 4⟩, ⟨14, 18, 17, 2⟩, ⟨14, 17, 17, 4⟩, ⟨14, 19, 16, 2⟩, ⟨14, 19, 15, 4⟩]
  exact AllWinning.cons node_25803 (AllWinning.cons node_25713 (AllWinning.cons node_25811 (AllWinning.cons node_25735 (AllWinning.cons node_25813 (AllWinning.cons node_25739 (AllWinning.nil))))))

theorem node_25879 : Outcome ⟨14, 20, 16, 4⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 6⟩) (by decide) node_25635

theorem node_25880 : Outcome ⟨15, 15, 20, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 20, 4⟩) (by decide) node_25718

theorem node_25881 : Outcome ⟨15, 16, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 19, 2⟩) (by decide) node_25816

theorem node_25882 : Outcome ⟨15, 17, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 2⟩) (by decide) node_25817

theorem node_25883 : Outcome ⟨15, 18, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 2⟩) (by decide) node_25822

theorem node_25884 : Outcome ⟨15, 19, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 2⟩) (by decide) node_25822

theorem node_25885 : Outcome ⟨15, 20, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 20, 15, 4⟩) (by decide) node_25728

theorem node_25886 : Outcome ⟨16, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 19, 2⟩) (by decide) node_25816

theorem node_25887 : Outcome ⟨16, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 2⟩) (by decide) node_25817

theorem node_25888 : Outcome ⟨16, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 2⟩) (by decide) node_25817

theorem node_25889 : Outcome ⟨16, 17, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 17, 17, 2⟩, ⟨14, 17, 17, 4⟩, ⟨16, 16, 17, 2⟩, ⟨16, 15, 17, 4⟩, ⟨16, 17, 16, 2⟩, ⟨16, 17, 15, 4⟩]
  exact AllWinning.cons node_25821 (AllWinning.cons node_25735 (AllWinning.cons node_25832 (AllWinning.cons node_25752 (AllWinning.cons node_25834 (AllWinning.cons node_25755 (AllWinning.nil))))))

theorem node_25890 : Outcome ⟨16, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 2⟩) (by decide) node_25822

theorem node_25891 : Outcome ⟨16, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 2⟩) (by decide) node_25822

theorem node_25892 : Outcome ⟨16, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨15, 19, 15, 2⟩) (by decide) node_25826

theorem node_25893 : Outcome ⟨17, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨16, 15, 18, 2⟩) (by decide) node_25828

theorem node_25894 : Outcome ⟨17, 16, 17, 4⟩ true :=
  Outcome.win (q := ⟨14, 16, 17, 6⟩) (by decide) node_25632

theorem node_25895 : Outcome ⟨17, 17, 16, 4⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 6⟩) (by decide) node_25635

theorem node_25896 : Outcome ⟨17, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨16, 18, 15, 2⟩) (by decide) node_25836

theorem node_25897 : Outcome ⟨18, 13, 19, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 18, 2⟩) (by decide) node_25848

theorem node_25898 : Outcome ⟨18, 16, 16, 2⟩ true :=
  Outcome.win (q := ⟨18, 15, 16, 2⟩) (by decide) node_25849

theorem node_25899 : Outcome ⟨18, 19, 13, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 13, 2⟩) (by decide) node_25851

theorem node_25900 : Outcome ⟨19, 12, 19, 2⟩ true :=
  Outcome.win (q := ⟨19, 11, 19, 2⟩) (by decide) node_25852

theorem node_25901 : Outcome ⟨19, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 18, 2⟩) (by decide) node_25848

theorem node_25902 : Outcome ⟨19, 15, 16, 2⟩ true :=
  Outcome.win (q := ⟨18, 15, 16, 2⟩) (by decide) node_25849

theorem node_25903 : Outcome ⟨19, 16, 15, 2⟩ true :=
  Outcome.win (q := ⟨18, 16, 15, 2⟩) (by decide) node_25850

theorem node_25904 : Outcome ⟨19, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 13, 2⟩) (by decide) node_25851

theorem node_25905 : Outcome ⟨19, 19, 12, 2⟩ true :=
  Outcome.win (q := ⟨19, 19, 11, 2⟩) (by decide) node_25858

theorem node_25906 : Outcome ⟨11, 20, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 20, 20, 2⟩, ⟨9, 20, 20, 4⟩, ⟨11, 19, 20, 2⟩, ⟨11, 18, 20, 4⟩, ⟨11, 20, 19, 2⟩, ⟨11, 20, 18, 4⟩]
  exact AllWinning.cons node_25860 (AllWinning.cons node_25783 (AllWinning.cons node_25862 (AllWinning.cons node_25787 (AllWinning.cons node_25863 (AllWinning.cons node_25791 (AllWinning.nil))))))

theorem node_25907 : Outcome ⟨11, 20, 20, 4⟩ true :=
  Outcome.win (q := ⟨8, 20, 20, 6⟩) (by decide) node_25695

theorem node_25908 : Outcome ⟨12, 19, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 20, 2⟩, ⟨10, 19, 20, 4⟩, ⟨12, 18, 20, 2⟩, ⟨12, 17, 20, 4⟩, ⟨12, 19, 19, 2⟩, ⟨12, 19, 18, 4⟩]
  exact AllWinning.cons node_25862 (AllWinning.cons node_25785 (AllWinning.cons node_25864 (AllWinning.cons node_25793 (AllWinning.cons node_25866 (AllWinning.cons node_25795 (AllWinning.nil))))))

theorem node_25909 : Outcome ⟨12, 19, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 20, 2⟩, ⟨10, 19, 20, 4⟩, ⟨9, 19, 20, 6⟩, ⟨8, 19, 20, 8⟩, ⟨12, 18, 20, 2⟩, ⟨12, 17, 20, 4⟩, ⟨12, 16, 20, 6⟩, ⟨12, 15, 20, 8⟩, ⟨12, 19, 19, 2⟩, ⟨12, 19, 18, 4⟩, ⟨12, 19, 17, 6⟩, ⟨12, 19, 16, 8⟩]
  exact AllWinning.cons node_25862 (AllWinning.cons node_25785 (AllWinning.cons node_25696 (AllWinning.cons node_25580 (AllWinning.cons node_25864 (AllWinning.cons node_25793 (AllWinning.cons node_25709 (AllWinning.cons node_25606 (AllWinning.cons node_25866 (AllWinning.cons node_25795 (AllWinning.cons node_25714 (AllWinning.cons node_25612 (AllWinning.nil))))))))))))

theorem node_25910 : Outcome ⟨12, 20, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 20, 19, 2⟩, ⟨10, 20, 19, 4⟩, ⟨12, 19, 19, 2⟩, ⟨12, 18, 19, 4⟩, ⟨12, 20, 18, 2⟩, ⟨12, 20, 17, 4⟩]
  exact AllWinning.cons node_25863 (AllWinning.cons node_25786 (AllWinning.cons node_25866 (AllWinning.cons node_25794 (AllWinning.cons node_25867 (AllWinning.cons node_25796 (AllWinning.nil))))))

theorem node_25911 : Outcome ⟨12, 20, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 20, 19, 2⟩, ⟨10, 20, 19, 4⟩, ⟨9, 20, 19, 6⟩, ⟨8, 20, 19, 8⟩, ⟨12, 19, 19, 2⟩, ⟨12, 18, 19, 4⟩, ⟨12, 17, 19, 6⟩, ⟨12, 16, 19, 8⟩, ⟨12, 20, 18, 2⟩, ⟨12, 20, 17, 4⟩, ⟨12, 20, 16, 6⟩, ⟨12, 20, 15, 8⟩]
  exact AllWinning.cons node_25863 (AllWinning.cons node_25786 (AllWinning.cons node_25697 (AllWinning.cons node_25582 (AllWinning.cons node_25866 (AllWinning.cons node_25794 (AllWinning.cons node_25711 (AllWinning.cons node_25608 (AllWinning.cons node_25867 (AllWinning.cons node_25796 (AllWinning.cons node_25716 (AllWinning.cons node_25614 (AllWinning.nil))))))))))))

theorem node_25912 : Outcome ⟨13, 18, 20, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 18, 4⟩) (by decide) node_25801

theorem node_25913 : Outcome ⟨13, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 8⟩) (by decide) node_25586

theorem node_25914 : Outcome ⟨13, 19, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 19, 19, 2⟩, ⟨11, 19, 19, 4⟩, ⟨10, 19, 19, 6⟩, ⟨9, 19, 19, 8⟩, ⟨13, 18, 19, 2⟩, ⟨13, 17, 19, 4⟩, ⟨13, 16, 19, 6⟩, ⟨13, 15, 19, 8⟩, ⟨13, 19, 18, 2⟩, ⟨13, 19, 17, 4⟩, ⟨13, 19, 16, 6⟩, ⟨13, 19, 15, 8⟩]
  exact AllWinning.cons node_25866 (AllWinning.cons node_25790 (AllWinning.cons node_25700 (AllWinning.cons node_25588 (AllWinning.cons node_25871 (AllWinning.cons node_25799 (AllWinning.cons node_25721 (AllWinning.cons node_25618 (AllWinning.cons node_25872 (AllWinning.cons node_25804 (AllWinning.cons node_25726 (AllWinning.cons node_25625 (AllWinning.nil))))))))))))

theorem node_25915 : Outcome ⟨13, 20, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 18, 4⟩) (by decide) node_25801

theorem node_25916 : Outcome ⟨13, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨9, 20, 18, 8⟩) (by decide) node_25592

theorem node_25917 : Outcome ⟨14, 17, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 19, 2⟩) (by decide) node_25876

theorem node_25918 : Outcome ⟨14, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 19, 2⟩) (by decide) node_25876

theorem node_25919 : Outcome ⟨14, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨14, 19, 17, 2⟩) (by decide) node_25878

theorem node_25920 : Outcome ⟨14, 20, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 19, 17, 2⟩) (by decide) node_25878

theorem node_25921 : Outcome ⟨15, 16, 20, 2⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 4⟩) (by decide) node_25818

theorem node_25922 : Outcome ⟨15, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 19, 2⟩) (by decide) node_25876

theorem node_25923 : Outcome ⟨15, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 18, 4⟩) (by decide) node_25801

theorem node_25924 : Outcome ⟨15, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 19, 17, 2⟩) (by decide) node_25878

theorem node_25925 : Outcome ⟨15, 20, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 4⟩) (by decide) node_25823

theorem node_25926 : Outcome ⟨16, 16, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 19, 2⟩, ⟨14, 16, 19, 4⟩, ⟨16, 15, 19, 2⟩, ⟨16, 14, 19, 4⟩, ⟨16, 16, 18, 2⟩, ⟨16, 16, 17, 4⟩]
  exact AllWinning.cons node_25881 (AllWinning.cons node_25808 (AllWinning.cons node_25886 (AllWinning.cons node_25827 (AllWinning.cons node_25887 (AllWinning.cons node_25833 (AllWinning.nil))))))

theorem node_25927 : Outcome ⟨16, 16, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 19, 2⟩, ⟨14, 16, 19, 4⟩, ⟨13, 16, 19, 6⟩, ⟨12, 16, 19, 8⟩, ⟨16, 15, 19, 2⟩, ⟨16, 14, 19, 4⟩, ⟨16, 13, 19, 6⟩, ⟨16, 12, 19, 8⟩, ⟨16, 16, 18, 2⟩, ⟨16, 16, 17, 4⟩, ⟨16, 16, 16, 6⟩, ⟨16, 16, 15, 8⟩]
  exact AllWinning.cons node_25881 (AllWinning.cons node_25808 (AllWinning.cons node_25721 (AllWinning.cons node_25608 (AllWinning.cons node_25886 (AllWinning.cons node_25827 (AllWinning.cons node_25749 (AllWinning.cons node_25655 (AllWinning.cons node_25887 (AllWinning.cons node_25833 (AllWinning.cons node_25753 (AllWinning.cons node_25661 (AllWinning.nil))))))))))))

theorem node_25928 : Outcome ⟨16, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨16, 15, 18, 4⟩) (by decide) node_25829

theorem node_25929 : Outcome ⟨16, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨16, 18, 15, 4⟩) (by decide) node_25837

theorem node_25930 : Outcome ⟨16, 19, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 19, 16, 2⟩, ⟨14, 19, 16, 4⟩, ⟨16, 18, 16, 2⟩, ⟨16, 17, 16, 4⟩, ⟨16, 19, 15, 2⟩, ⟨16, 19, 14, 4⟩]
  exact AllWinning.cons node_25884 (AllWinning.cons node_25814 (AllWinning.cons node_25890 (AllWinning.cons node_25835 (AllWinning.cons node_25892 (AllWinning.cons node_25840 (AllWinning.nil))))))

theorem node_25931 : Outcome ⟨16, 19, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 19, 16, 2⟩, ⟨14, 19, 16, 4⟩, ⟨13, 19, 16, 6⟩, ⟨12, 19, 16, 8⟩, ⟨16, 18, 16, 2⟩, ⟨16, 17, 16, 4⟩, ⟨16, 16, 16, 6⟩, ⟨16, 15, 16, 8⟩, ⟨16, 19, 15, 2⟩, ⟨16, 19, 14, 4⟩, ⟨16, 19, 13, 6⟩, ⟨16, 19, 12, 8⟩]
  exact AllWinning.cons node_25884 (AllWinning.cons node_25814 (AllWinning.cons node_25726 (AllWinning.cons node_25612 (AllWinning.cons node_25890 (AllWinning.cons node_25835 (AllWinning.cons node_25753 (AllWinning.cons node_25659 (AllWinning.cons node_25892 (AllWinning.cons node_25840 (AllWinning.cons node_25757 (AllWinning.cons node_25664 (AllWinning.nil))))))))))))

theorem node_25932 : Outcome ⟨17, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 4⟩) (by decide) node_25818

theorem node_25933 : Outcome ⟨17, 17, 17, 2⟩ true :=
  Outcome.win (q := ⟨16, 17, 17, 2⟩) (by decide) node_25889

theorem node_25934 : Outcome ⟨17, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 4⟩) (by decide) node_25823

theorem node_25935 : Outcome ⟨19, 13, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 19, 2⟩, ⟨17, 13, 19, 4⟩, ⟨19, 12, 19, 2⟩, ⟨19, 11, 19, 4⟩, ⟨19, 13, 18, 2⟩, ⟨19, 13, 17, 4⟩]
  exact AllWinning.cons node_25897 (AllWinning.cons node_25841 (AllWinning.cons node_25900 (AllWinning.cons node_25853 (AllWinning.cons node_25901 (AllWinning.cons node_25854 (AllWinning.nil))))))

theorem node_25936 : Outcome ⟨19, 13, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 19, 2⟩, ⟨17, 13, 19, 4⟩, ⟨16, 13, 19, 6⟩, ⟨15, 13, 19, 8⟩, ⟨19, 12, 19, 2⟩, ⟨19, 11, 19, 4⟩, ⟨19, 10, 19, 6⟩, ⟨19, 9, 19, 8⟩, ⟨19, 13, 18, 2⟩, ⟨19, 13, 17, 4⟩, ⟨19, 13, 16, 6⟩, ⟨19, 13, 15, 8⟩]
  exact AllWinning.cons node_25897 (AllWinning.cons node_25841 (AllWinning.cons node_25749 (AllWinning.cons node_25642 (AllWinning.cons node_25900 (AllWinning.cons node_25853 (AllWinning.cons node_25776 (AllWinning.cons node_25685 (AllWinning.cons node_25901 (AllWinning.cons node_25854 (AllWinning.cons node_25778 (AllWinning.cons node_25688 (AllWinning.nil))))))))))))

theorem node_25937 : Outcome ⟨19, 13, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 19, 2⟩, ⟨17, 13, 19, 4⟩, ⟨16, 13, 19, 6⟩, ⟨15, 13, 19, 8⟩, ⟨14, 13, 19, 10⟩, ⟨13, 13, 19, 12⟩, ⟨19, 12, 19, 2⟩, ⟨19, 11, 19, 4⟩, ⟨19, 10, 19, 6⟩, ⟨19, 9, 19, 8⟩, ⟨19, 8, 19, 10⟩, ⟨19, 7, 19, 12⟩, ⟨19, 13, 18, 2⟩, ⟨19, 13, 17, 4⟩, ⟨19, 13, 16, 6⟩, ⟨19, 13, 15, 8⟩, ⟨19, 13, 14, 10⟩, ⟨19, 13, 13, 12⟩]
  exact AllWinning.cons node_25897 (AllWinning.cons node_25841 (AllWinning.cons node_25749 (AllWinning.cons node_25642 (AllWinning.cons node_25515 (AllWinning.cons node_25346 (AllWinning.cons node_25900 (AllWinning.cons node_25853 (AllWinning.cons node_25776 (AllWinning.cons node_25685 (AllWinning.cons node_25564 (AllWinning.cons node_25442 (AllWinning.cons node_25901 (AllWinning.cons node_25854 (AllWinning.cons node_25778 (AllWinning.cons node_25688 (AllWinning.cons node_25569 (AllWinning.cons node_25448 (AllWinning.nil))))))))))))))))))

theorem node_25938 : Outcome ⟨19, 16, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 16, 16, 2⟩, ⟨17, 16, 16, 4⟩, ⟨19, 15, 16, 2⟩, ⟨19, 14, 16, 4⟩, ⟨19, 16, 15, 2⟩, ⟨19, 16, 14, 4⟩]
  exact AllWinning.cons node_25898 (AllWinning.cons node_25844 (AllWinning.cons node_25902 (AllWinning.cons node_25855 (AllWinning.cons node_25903 (AllWinning.cons node_25856 (AllWinning.nil))))))

theorem node_25939 : Outcome ⟨19, 16, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 16, 16, 2⟩, ⟨17, 16, 16, 4⟩, ⟨16, 16, 16, 6⟩, ⟨15, 16, 16, 8⟩, ⟨19, 15, 16, 2⟩, ⟨19, 14, 16, 4⟩, ⟨19, 13, 16, 6⟩, ⟨19, 12, 16, 8⟩, ⟨19, 16, 15, 2⟩, ⟨19, 16, 14, 4⟩, ⟨19, 16, 13, 6⟩, ⟨19, 16, 12, 8⟩]
  exact AllWinning.cons node_25898 (AllWinning.cons node_25844 (AllWinning.cons node_25753 (AllWinning.cons node_25647 (AllWinning.cons node_25902 (AllWinning.cons node_25855 (AllWinning.cons node_25778 (AllWinning.cons node_25687 (AllWinning.cons node_25903 (AllWinning.cons node_25856 (AllWinning.cons node_25779 (AllWinning.cons node_25690 (AllWinning.nil))))))))))))

theorem node_25940 : Outcome ⟨19, 19, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 13, 2⟩, ⟨17, 19, 13, 4⟩, ⟨19, 18, 13, 2⟩, ⟨19, 17, 13, 4⟩, ⟨19, 19, 12, 2⟩, ⟨19, 19, 11, 4⟩]
  exact AllWinning.cons node_25899 (AllWinning.cons node_25847 (AllWinning.cons node_25904 (AllWinning.cons node_25857 (AllWinning.cons node_25905 (AllWinning.cons node_25859 (AllWinning.nil))))))

theorem node_25941 : Outcome ⟨19, 19, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 13, 2⟩, ⟨17, 19, 13, 4⟩, ⟨16, 19, 13, 6⟩, ⟨15, 19, 13, 8⟩, ⟨19, 18, 13, 2⟩, ⟨19, 17, 13, 4⟩, ⟨19, 16, 13, 6⟩, ⟨19, 15, 13, 8⟩, ⟨19, 19, 12, 2⟩, ⟨19, 19, 11, 4⟩, ⟨19, 19, 10, 6⟩, ⟨19, 19, 9, 8⟩]
  exact AllWinning.cons node_25899 (AllWinning.cons node_25847 (AllWinning.cons node_25757 (AllWinning.cons node_25653 (AllWinning.cons node_25904 (AllWinning.cons node_25857 (AllWinning.cons node_25779 (AllWinning.cons node_25689 (AllWinning.cons node_25905 (AllWinning.cons node_25859 (AllWinning.cons node_25782 (AllWinning.cons node_25693 (AllWinning.nil))))))))))))

theorem node_25942 : Outcome ⟨19, 19, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 13, 2⟩, ⟨17, 19, 13, 4⟩, ⟨16, 19, 13, 6⟩, ⟨15, 19, 13, 8⟩, ⟨14, 19, 13, 10⟩, ⟨13, 19, 13, 12⟩, ⟨19, 18, 13, 2⟩, ⟨19, 17, 13, 4⟩, ⟨19, 16, 13, 6⟩, ⟨19, 15, 13, 8⟩, ⟨19, 14, 13, 10⟩, ⟨19, 13, 13, 12⟩, ⟨19, 19, 12, 2⟩, ⟨19, 19, 11, 4⟩, ⟨19, 19, 10, 6⟩, ⟨19, 19, 9, 8⟩, ⟨19, 19, 8, 10⟩, ⟨19, 19, 7, 12⟩]
  exact AllWinning.cons node_25899 (AllWinning.cons node_25847 (AllWinning.cons node_25757 (AllWinning.cons node_25653 (AllWinning.cons node_25522 (AllWinning.cons node_25364 (AllWinning.cons node_25904 (AllWinning.cons node_25857 (AllWinning.cons node_25779 (AllWinning.cons node_25689 (AllWinning.cons node_25571 (AllWinning.cons node_25448 (AllWinning.cons node_25905 (AllWinning.cons node_25859 (AllWinning.cons node_25782 (AllWinning.cons node_25693 (AllWinning.cons node_25577 (AllWinning.cons node_25454 (AllWinning.nil))))))))))))))))))

theorem node_25943 : Outcome ⟨12, 20, 20, 2⟩ true :=
  Outcome.win (q := ⟨11, 20, 20, 2⟩) (by decide) node_25906

theorem node_25944 : Outcome ⟨12, 20, 20, 8⟩ true :=
  Outcome.win (q := ⟨11, 20, 20, 2⟩) (by decide) node_25906

theorem node_25945 : Outcome ⟨13, 19, 20, 2⟩ true :=
  Outcome.win (q := ⟨12, 19, 20, 2⟩) (by decide) node_25908

theorem node_25946 : Outcome ⟨13, 19, 20, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 20, 8⟩) (by decide) node_25719

theorem node_25947 : Outcome ⟨13, 20, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 20, 19, 2⟩) (by decide) node_25910

theorem node_25948 : Outcome ⟨13, 20, 19, 4⟩ true :=
  Outcome.win (q := ⟨13, 20, 15, 8⟩) (by decide) node_25729

theorem node_25949 : Outcome ⟨14, 18, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 20, 2⟩, ⟨12, 18, 20, 4⟩, ⟨14, 17, 20, 2⟩, ⟨14, 16, 20, 4⟩, ⟨14, 18, 19, 2⟩, ⟨14, 18, 18, 4⟩]
  exact AllWinning.cons node_25912 (AllWinning.cons node_25865 (AllWinning.cons node_25917 (AllWinning.cons node_25875 (AllWinning.cons node_25918 (AllWinning.cons node_25877 (AllWinning.nil))))))

theorem node_25950 : Outcome ⟨14, 18, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 20, 2⟩, ⟨12, 18, 20, 4⟩, ⟨11, 18, 20, 6⟩, ⟨10, 18, 20, 8⟩, ⟨14, 17, 20, 2⟩, ⟨14, 16, 20, 4⟩, ⟨14, 15, 20, 6⟩, ⟨14, 14, 20, 8⟩, ⟨14, 18, 19, 2⟩, ⟨14, 18, 18, 4⟩, ⟨14, 18, 17, 6⟩, ⟨14, 18, 16, 8⟩]
  exact AllWinning.cons node_25912 (AllWinning.cons node_25865 (AllWinning.cons node_25788 (AllWinning.cons node_25698 (AllWinning.cons node_25917 (AllWinning.cons node_25875 (AllWinning.cons node_25806 (AllWinning.cons node_25730 (AllWinning.cons node_25918 (AllWinning.cons node_25877 (AllWinning.cons node_25812 (AllWinning.cons node_25737 (AllWinning.nil))))))))))))

theorem node_25951 : Outcome ⟨14, 20, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 20, 18, 2⟩, ⟨12, 20, 18, 4⟩, ⟨14, 19, 18, 2⟩, ⟨14, 18, 18, 4⟩, ⟨14, 20, 17, 2⟩, ⟨14, 20, 16, 4⟩]
  exact AllWinning.cons node_25915 (AllWinning.cons node_25868 (AllWinning.cons node_25919 (AllWinning.cons node_25877 (AllWinning.cons node_25920 (AllWinning.cons node_25879 (AllWinning.nil))))))

theorem node_25952 : Outcome ⟨14, 20, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 20, 18, 2⟩, ⟨12, 20, 18, 4⟩, ⟨11, 20, 18, 6⟩, ⟨10, 20, 18, 8⟩, ⟨14, 19, 18, 2⟩, ⟨14, 18, 18, 4⟩, ⟨14, 17, 18, 6⟩, ⟨14, 16, 18, 8⟩, ⟨14, 20, 17, 2⟩, ⟨14, 20, 16, 4⟩, ⟨14, 20, 15, 6⟩, ⟨14, 20, 14, 8⟩]
  exact AllWinning.cons node_25915 (AllWinning.cons node_25868 (AllWinning.cons node_25792 (AllWinning.cons node_25701 (AllWinning.cons node_25919 (AllWinning.cons node_25877 (AllWinning.cons node_25810 (AllWinning.cons node_25734 (AllWinning.cons node_25920 (AllWinning.cons node_25879 (AllWinning.cons node_25815 (AllWinning.cons node_25740 (AllWinning.nil))))))))))))

theorem node_25953 : Outcome ⟨15, 17, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 17, 20, 2⟩, ⟨13, 17, 20, 4⟩, ⟨15, 16, 20, 2⟩, ⟨15, 15, 20, 4⟩, ⟨15, 17, 19, 2⟩, ⟨15, 17, 18, 4⟩]
  exact AllWinning.cons node_25917 (AllWinning.cons node_25869 (AllWinning.cons node_25921 (AllWinning.cons node_25880 (AllWinning.cons node_25922 (AllWinning.cons node_25882 (AllWinning.nil))))))

theorem node_25954 : Outcome ⟨15, 17, 20, 4⟩ true :=
  Outcome.win (q := ⟨15, 13, 20, 8⟩) (by decide) node_25741

theorem node_25955 : Outcome ⟨15, 18, 19, 4⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 6⟩) (by decide) node_25824

theorem node_25956 : Outcome ⟨15, 18, 19, 8⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 6⟩) (by decide) node_25824

theorem node_25957 : Outcome ⟨15, 19, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 6⟩) (by decide) node_25819

theorem node_25958 : Outcome ⟨15, 19, 18, 8⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 6⟩) (by decide) node_25819

theorem node_25959 : Outcome ⟨15, 20, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 20, 17, 2⟩, ⟨13, 20, 17, 4⟩, ⟨15, 19, 17, 2⟩, ⟨15, 18, 17, 4⟩, ⟨15, 20, 16, 2⟩, ⟨15, 20, 15, 4⟩]
  exact AllWinning.cons node_25920 (AllWinning.cons node_25873 (AllWinning.cons node_25924 (AllWinning.cons node_25883 (AllWinning.cons node_25925 (AllWinning.cons node_25885 (AllWinning.nil))))))

theorem node_25960 : Outcome ⟨15, 20, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 20, 13, 8⟩) (by decide) node_25748

theorem node_25961 : Outcome ⟨16, 16, 20, 8⟩ true :=
  Outcome.win (q := ⟨16, 16, 19, 2⟩) (by decide) node_25926

theorem node_25962 : Outcome ⟨16, 18, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 18, 18, 2⟩, ⟨14, 18, 18, 4⟩, ⟨16, 17, 18, 2⟩, ⟨16, 16, 18, 4⟩, ⟨16, 18, 17, 2⟩, ⟨16, 18, 16, 4⟩]
  exact AllWinning.cons node_25923 (AllWinning.cons node_25877 (AllWinning.cons node_25928 (AllWinning.cons node_25888 (AllWinning.cons node_25929 (AllWinning.cons node_25891 (AllWinning.nil))))))

theorem node_25963 : Outcome ⟨16, 18, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 18, 18, 6⟩) (by decide) node_25802

theorem node_25964 : Outcome ⟨16, 20, 16, 8⟩ true :=
  Outcome.win (q := ⟨16, 19, 16, 2⟩) (by decide) node_25930

theorem node_25965 : Outcome ⟨17, 16, 19, 4⟩ true :=
  Outcome.win (q := ⟨16, 16, 19, 2⟩) (by decide) node_25926

theorem node_25966 : Outcome ⟨17, 17, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 18, 2⟩, ⟨15, 17, 18, 4⟩, ⟨17, 16, 18, 2⟩, ⟨17, 15, 18, 4⟩, ⟨17, 17, 17, 2⟩, ⟨17, 17, 16, 4⟩]
  exact AllWinning.cons node_25928 (AllWinning.cons node_25882 (AllWinning.cons node_25932 (AllWinning.cons node_25893 (AllWinning.cons node_25933 (AllWinning.cons node_25895 (AllWinning.nil))))))

theorem node_25967 : Outcome ⟨17, 17, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 18, 2⟩, ⟨15, 17, 18, 4⟩, ⟨14, 17, 18, 6⟩, ⟨13, 17, 18, 8⟩, ⟨17, 16, 18, 2⟩, ⟨17, 15, 18, 4⟩, ⟨17, 14, 18, 6⟩, ⟨17, 13, 18, 8⟩, ⟨17, 17, 17, 2⟩, ⟨17, 17, 16, 4⟩, ⟨17, 17, 15, 6⟩, ⟨17, 17, 14, 8⟩]
  exact AllWinning.cons node_25928 (AllWinning.cons node_25882 (AllWinning.cons node_25810 (AllWinning.cons node_25723 (AllWinning.cons node_25932 (AllWinning.cons node_25893 (AllWinning.cons node_25842 (AllWinning.cons node_25759 (AllWinning.cons node_25933 (AllWinning.cons node_25895 (AllWinning.cons node_25845 (AllWinning.cons node_25763 (AllWinning.nil))))))))))))

theorem node_25968 : Outcome ⟨17, 18, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 18, 17, 2⟩, ⟨15, 18, 17, 4⟩, ⟨17, 17, 17, 2⟩, ⟨17, 16, 17, 4⟩, ⟨17, 18, 16, 2⟩, ⟨17, 18, 15, 4⟩]
  exact AllWinning.cons node_25929 (AllWinning.cons node_25883 (AllWinning.cons node_25933 (AllWinning.cons node_25894 (AllWinning.cons node_25934 (AllWinning.cons node_25896 (AllWinning.nil))))))

theorem node_25969 : Outcome ⟨17, 18, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 18, 17, 2⟩, ⟨15, 18, 17, 4⟩, ⟨14, 18, 17, 6⟩, ⟨13, 18, 17, 8⟩, ⟨17, 17, 17, 2⟩, ⟨17, 16, 17, 4⟩, ⟨17, 15, 17, 6⟩, ⟨17, 14, 17, 8⟩, ⟨17, 18, 16, 2⟩, ⟨17, 18, 15, 4⟩, ⟨17, 18, 14, 6⟩, ⟨17, 18, 13, 8⟩]
  exact AllWinning.cons node_25929 (AllWinning.cons node_25883 (AllWinning.cons node_25812 (AllWinning.cons node_25725 (AllWinning.cons node_25933 (AllWinning.cons node_25894 (AllWinning.cons node_25843 (AllWinning.cons node_25760 (AllWinning.cons node_25934 (AllWinning.cons node_25896 (AllWinning.cons node_25846 (AllWinning.cons node_25765 (AllWinning.nil))))))))))))

theorem node_25970 : Outcome ⟨17, 19, 16, 4⟩ true :=
  Outcome.win (q := ⟨16, 19, 16, 2⟩) (by decide) node_25930

theorem node_25971 : Outcome ⟨18, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 6⟩) (by decide) node_25819

theorem node_25972 : Outcome ⟨18, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 6⟩) (by decide) node_25824

theorem node_25973 : Outcome ⟨19, 14, 19, 4⟩ true :=
  Outcome.win (q := ⟨19, 13, 19, 2⟩) (by decide) node_25935

theorem node_25974 : Outcome ⟨19, 14, 19, 8⟩ true :=
  Outcome.win (q := ⟨19, 13, 19, 2⟩) (by decide) node_25935

theorem node_25975 : Outcome ⟨19, 15, 18, 8⟩ true :=
  Outcome.win (q := ⟨16, 15, 18, 6⟩) (by decide) node_25830

theorem node_25976 : Outcome ⟨19, 16, 17, 4⟩ true :=
  Outcome.win (q := ⟨19, 16, 16, 2⟩) (by decide) node_25938

theorem node_25977 : Outcome ⟨19, 17, 16, 4⟩ true :=
  Outcome.win (q := ⟨19, 16, 16, 2⟩) (by decide) node_25938

theorem node_25978 : Outcome ⟨19, 18, 15, 8⟩ true :=
  Outcome.win (q := ⟨16, 18, 15, 6⟩) (by decide) node_25838

theorem node_25979 : Outcome ⟨19, 19, 14, 4⟩ true :=
  Outcome.win (q := ⟨19, 19, 13, 2⟩) (by decide) node_25940

theorem node_25980 : Outcome ⟨19, 19, 14, 8⟩ true :=
  Outcome.win (q := ⟨19, 19, 13, 2⟩) (by decide) node_25940

theorem node_25981 : Outcome ⟨13, 20, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 20, 20, 2⟩, ⟨11, 20, 20, 4⟩, ⟨10, 20, 20, 6⟩, ⟨9, 20, 20, 8⟩, ⟨13, 19, 20, 2⟩, ⟨13, 18, 20, 4⟩, ⟨13, 17, 20, 6⟩, ⟨13, 16, 20, 8⟩, ⟨13, 20, 19, 2⟩, ⟨13, 20, 18, 4⟩, ⟨13, 20, 17, 6⟩, ⟨13, 20, 16, 8⟩]
  exact AllWinning.cons node_25943 (AllWinning.cons node_25907 (AllWinning.cons node_25861 (AllWinning.cons node_25784 (AllWinning.cons node_25945 (AllWinning.cons node_25913 (AllWinning.cons node_25870 (AllWinning.cons node_25797 (AllWinning.cons node_25947 (AllWinning.cons node_25916 (AllWinning.cons node_25874 (AllWinning.cons node_25805 (AllWinning.nil))))))))))))

theorem node_25982 : Outcome ⟨13, 20, 20, 6⟩ true :=
  Outcome.win (q := ⟨13, 15, 20, 10⟩) (by decide) node_25720

theorem node_25983 : Outcome ⟨14, 19, 20, 2⟩ true :=
  Outcome.win (q := ⟨12, 19, 20, 4⟩) (by decide) node_25909

theorem node_25984 : Outcome ⟨14, 20, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 20, 19, 4⟩) (by decide) node_25911

theorem node_25985 : Outcome ⟨15, 18, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 18, 20, 2⟩) (by decide) node_25949

theorem node_25986 : Outcome ⟨15, 19, 19, 2⟩ true :=
  Outcome.win (q := ⟨13, 19, 19, 4⟩) (by decide) node_25914

theorem node_25987 : Outcome ⟨15, 20, 18, 2⟩ true :=
  Outcome.win (q := ⟨14, 20, 18, 2⟩) (by decide) node_25951

theorem node_25988 : Outcome ⟨16, 17, 20, 6⟩ true :=
  Outcome.win (q := ⟨15, 17, 20, 2⟩) (by decide) node_25953

theorem node_25989 : Outcome ⟨16, 18, 19, 6⟩ true :=
  Outcome.win (q := ⟨16, 18, 15, 8⟩) (by decide) node_25839

theorem node_25990 : Outcome ⟨16, 19, 18, 6⟩ true :=
  Outcome.win (q := ⟨16, 15, 18, 8⟩) (by decide) node_25831

theorem node_25991 : Outcome ⟨16, 20, 17, 6⟩ true :=
  Outcome.win (q := ⟨15, 20, 17, 2⟩) (by decide) node_25959

theorem node_25992 : Outcome ⟨17, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨16, 18, 18, 2⟩) (by decide) node_25962

theorem node_25993 : Outcome ⟨18, 16, 19, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 19, 4⟩) (by decide) node_25927

theorem node_25994 : Outcome ⟨18, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 18, 2⟩) (by decide) node_25966

theorem node_25995 : Outcome ⟨18, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨17, 18, 17, 2⟩) (by decide) node_25968

theorem node_25996 : Outcome ⟨18, 19, 16, 2⟩ true :=
  Outcome.win (q := ⟨16, 19, 16, 4⟩) (by decide) node_25931

theorem node_25997 : Outcome ⟨19, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨19, 13, 19, 4⟩) (by decide) node_25936

theorem node_25998 : Outcome ⟨19, 15, 19, 6⟩ true :=
  Outcome.win (q := ⟨19, 13, 19, 4⟩) (by decide) node_25936

theorem node_25999 : Outcome ⟨19, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨19, 16, 16, 4⟩) (by decide) node_25939

theorem node_26000 : Outcome ⟨19, 16, 18, 6⟩ true :=
  Outcome.win (q := ⟨15, 16, 18, 8⟩) (by decide) node_25820

theorem node_26001 : Outcome ⟨19, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨19, 16, 16, 4⟩) (by decide) node_25939

theorem node_26002 : Outcome ⟨19, 18, 16, 6⟩ true :=
  Outcome.win (q := ⟨15, 18, 16, 8⟩) (by decide) node_25825

theorem node_26003 : Outcome ⟨19, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨19, 19, 13, 4⟩) (by decide) node_25941

theorem node_26004 : Outcome ⟨19, 19, 15, 6⟩ true :=
  Outcome.win (q := ⟨19, 19, 13, 4⟩) (by decide) node_25941

theorem node_26005 : Outcome ⟨14, 20, 20, 4⟩ true :=
  Outcome.win (q := ⟨14, 18, 20, 4⟩) (by decide) node_25950

theorem node_26006 : Outcome ⟨15, 19, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 19, 20, 2⟩, ⟨13, 19, 20, 4⟩, ⟨15, 18, 20, 2⟩, ⟨15, 17, 20, 4⟩, ⟨15, 19, 19, 2⟩, ⟨15, 19, 18, 4⟩]
  exact AllWinning.cons node_25983 (AllWinning.cons node_25946 (AllWinning.cons node_25985 (AllWinning.cons node_25954 (AllWinning.cons node_25986 (AllWinning.cons node_25957 (AllWinning.nil))))))

theorem node_26007 : Outcome ⟨15, 20, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 20, 19, 2⟩, ⟨13, 20, 19, 4⟩, ⟨15, 19, 19, 2⟩, ⟨15, 18, 19, 4⟩, ⟨15, 20, 18, 2⟩, ⟨15, 20, 17, 4⟩]
  exact AllWinning.cons node_25984 (AllWinning.cons node_25948 (AllWinning.cons node_25986 (AllWinning.cons node_25955 (AllWinning.cons node_25987 (AllWinning.cons node_25960 (AllWinning.nil))))))

theorem node_26008 : Outcome ⟨16, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨14, 18, 20, 4⟩) (by decide) node_25950

theorem node_26009 : Outcome ⟨16, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨14, 20, 18, 4⟩) (by decide) node_25952

theorem node_26010 : Outcome ⟨17, 18, 19, 4⟩ true :=
  Outcome.win (q := ⟨17, 18, 17, 4⟩) (by decide) node_25969

theorem node_26011 : Outcome ⟨17, 19, 18, 4⟩ true :=
  Outcome.win (q := ⟨17, 17, 18, 4⟩) (by decide) node_25967

theorem node_26012 : Outcome ⟨18, 18, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 18, 18, 2⟩, ⟨16, 18, 18, 4⟩, ⟨18, 17, 18, 2⟩, ⟨18, 16, 18, 4⟩, ⟨18, 18, 17, 2⟩, ⟨18, 18, 16, 4⟩]
  exact AllWinning.cons node_25992 (AllWinning.cons node_25963 (AllWinning.cons node_25994 (AllWinning.cons node_25971 (AllWinning.cons node_25995 (AllWinning.cons node_25972 (AllWinning.nil))))))

theorem node_26013 : Outcome ⟨19, 16, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 16, 19, 2⟩, ⟨17, 16, 19, 4⟩, ⟨19, 15, 19, 2⟩, ⟨19, 14, 19, 4⟩, ⟨19, 16, 18, 2⟩, ⟨19, 16, 17, 4⟩]
  exact AllWinning.cons node_25993 (AllWinning.cons node_25965 (AllWinning.cons node_25997 (AllWinning.cons node_25973 (AllWinning.cons node_25999 (AllWinning.cons node_25976 (AllWinning.nil))))))

theorem node_26014 : Outcome ⟨19, 16, 19, 4⟩ true :=
  Outcome.win (q := ⟨19, 13, 19, 6⟩) (by decide) node_25937

theorem node_26015 : Outcome ⟨19, 17, 18, 4⟩ true :=
  Outcome.win (q := ⟨17, 17, 18, 4⟩) (by decide) node_25967

theorem node_26016 : Outcome ⟨19, 18, 17, 4⟩ true :=
  Outcome.win (q := ⟨17, 18, 17, 4⟩) (by decide) node_25969

theorem node_26017 : Outcome ⟨19, 19, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 16, 2⟩, ⟨17, 19, 16, 4⟩, ⟨19, 18, 16, 2⟩, ⟨19, 17, 16, 4⟩, ⟨19, 19, 15, 2⟩, ⟨19, 19, 14, 4⟩]
  exact AllWinning.cons node_25996 (AllWinning.cons node_25970 (AllWinning.cons node_26001 (AllWinning.cons node_25977 (AllWinning.cons node_26003 (AllWinning.cons node_25979 (AllWinning.nil))))))

theorem node_26018 : Outcome ⟨19, 19, 16, 4⟩ true :=
  Outcome.win (q := ⟨19, 19, 13, 6⟩) (by decide) node_25942

theorem node_26019 : Outcome ⟨15, 20, 20, 2⟩ true :=
  Outcome.win (q := ⟨13, 20, 20, 4⟩) (by decide) node_25981

theorem node_26020 : Outcome ⟨16, 19, 20, 2⟩ true :=
  Outcome.win (q := ⟨15, 19, 20, 2⟩) (by decide) node_26006

theorem node_26021 : Outcome ⟨16, 20, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 20, 19, 2⟩) (by decide) node_26007

theorem node_26022 : Outcome ⟨18, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 18, 2⟩) (by decide) node_26012

theorem node_26023 : Outcome ⟨18, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 18, 2⟩) (by decide) node_26012

theorem node_26024 : Outcome ⟨19, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨19, 16, 19, 2⟩) (by decide) node_26013

theorem node_26025 : Outcome ⟨19, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 18, 2⟩) (by decide) node_26012

theorem node_26026 : Outcome ⟨19, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨19, 19, 16, 2⟩) (by decide) node_26017

theorem node_26027 : Outcome ⟨16, 20, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 20, 20, 2⟩, ⟨14, 20, 20, 4⟩, ⟨16, 19, 20, 2⟩, ⟨16, 18, 20, 4⟩, ⟨16, 20, 19, 2⟩, ⟨16, 20, 18, 4⟩]
  exact AllWinning.cons node_26019 (AllWinning.cons node_26005 (AllWinning.cons node_26020 (AllWinning.cons node_26008 (AllWinning.cons node_26021 (AllWinning.cons node_26009 (AllWinning.nil))))))

theorem node_26028 : Outcome ⟨16, 20, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 20, 20, 2⟩, ⟨14, 20, 20, 4⟩, ⟨13, 20, 20, 6⟩, ⟨12, 20, 20, 8⟩, ⟨16, 19, 20, 2⟩, ⟨16, 18, 20, 4⟩, ⟨16, 17, 20, 6⟩, ⟨16, 16, 20, 8⟩, ⟨16, 20, 19, 2⟩, ⟨16, 20, 18, 4⟩, ⟨16, 20, 17, 6⟩, ⟨16, 20, 16, 8⟩]
  exact AllWinning.cons node_26019 (AllWinning.cons node_26005 (AllWinning.cons node_25982 (AllWinning.cons node_25944 (AllWinning.cons node_26020 (AllWinning.cons node_26008 (AllWinning.cons node_25988 (AllWinning.cons node_25961 (AllWinning.cons node_26021 (AllWinning.cons node_26009 (AllWinning.cons node_25991 (AllWinning.cons node_25964 (AllWinning.nil))))))))))))

theorem node_26029 : Outcome ⟨19, 18, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 18, 19, 2⟩, ⟨17, 18, 19, 4⟩, ⟨19, 17, 19, 2⟩, ⟨19, 16, 19, 4⟩, ⟨19, 18, 18, 2⟩, ⟨19, 18, 17, 4⟩]
  exact AllWinning.cons node_26022 (AllWinning.cons node_26010 (AllWinning.cons node_26024 (AllWinning.cons node_26014 (AllWinning.cons node_26025 (AllWinning.cons node_26016 (AllWinning.nil))))))

theorem node_26030 : Outcome ⟨19, 18, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 18, 19, 2⟩, ⟨17, 18, 19, 4⟩, ⟨16, 18, 19, 6⟩, ⟨15, 18, 19, 8⟩, ⟨19, 17, 19, 2⟩, ⟨19, 16, 19, 4⟩, ⟨19, 15, 19, 6⟩, ⟨19, 14, 19, 8⟩, ⟨19, 18, 18, 2⟩, ⟨19, 18, 17, 4⟩, ⟨19, 18, 16, 6⟩, ⟨19, 18, 15, 8⟩]
  exact AllWinning.cons node_26022 (AllWinning.cons node_26010 (AllWinning.cons node_25989 (AllWinning.cons node_25956 (AllWinning.cons node_26024 (AllWinning.cons node_26014 (AllWinning.cons node_25998 (AllWinning.cons node_25974 (AllWinning.cons node_26025 (AllWinning.cons node_26016 (AllWinning.cons node_26002 (AllWinning.cons node_25978 (AllWinning.nil))))))))))))

theorem node_26031 : Outcome ⟨19, 19, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 18, 2⟩, ⟨17, 19, 18, 4⟩, ⟨19, 18, 18, 2⟩, ⟨19, 17, 18, 4⟩, ⟨19, 19, 17, 2⟩, ⟨19, 19, 16, 4⟩]
  exact AllWinning.cons node_26023 (AllWinning.cons node_26011 (AllWinning.cons node_26025 (AllWinning.cons node_26015 (AllWinning.cons node_26026 (AllWinning.cons node_26018 (AllWinning.nil))))))

end RQ9F1
