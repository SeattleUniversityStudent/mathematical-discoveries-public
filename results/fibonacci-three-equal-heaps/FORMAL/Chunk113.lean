import Chunk112
set_option autoImplicit false
namespace RQ9F1

theorem node_23762 : Outcome ⟨17, 15, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 15, 7, 2⟩, ⟨15, 15, 7, 4⟩, ⟨17, 14, 7, 2⟩, ⟨17, 13, 7, 4⟩, ⟨17, 15, 6, 2⟩, ⟨17, 15, 5, 4⟩]
  exact AllWinning.cons node_23334 (AllWinning.cons node_22833 (AllWinning.cons node_23366 (AllWinning.cons node_22899 (AllWinning.cons node_23368 (AllWinning.cons node_22902 (AllWinning.nil))))))

theorem node_23763 : Outcome ⟨17, 16, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 16, 6, 2⟩, ⟨15, 16, 6, 4⟩, ⟨17, 15, 6, 2⟩, ⟨17, 14, 6, 4⟩, ⟨17, 16, 5, 2⟩, ⟨17, 16, 4, 4⟩]
  exact AllWinning.cons node_23337 (AllWinning.cons node_22836 (AllWinning.cons node_23368 (AllWinning.cons node_22901 (AllWinning.cons node_23369 (AllWinning.cons node_22903 (AllWinning.nil))))))

theorem node_23764 : Outcome ⟨17, 16, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 16, 6, 2⟩, ⟨15, 16, 6, 4⟩, ⟨14, 16, 6, 6⟩, ⟨13, 16, 6, 8⟩, ⟨17, 15, 6, 2⟩, ⟨17, 14, 6, 4⟩, ⟨17, 13, 6, 6⟩, ⟨17, 12, 6, 8⟩, ⟨17, 16, 5, 2⟩, ⟨17, 16, 4, 4⟩, ⟨17, 16, 3, 6⟩, ⟨17, 16, 2, 8⟩]
  exact AllWinning.cons node_23337 (AllWinning.cons node_22836 (AllWinning.cons node_22207 (AllWinning.cons node_21570 (AllWinning.cons node_23368 (AllWinning.cons node_22901 (AllWinning.cons node_22343 (AllWinning.cons node_21725 (AllWinning.cons node_23369 (AllWinning.cons node_22903 (AllWinning.cons node_22348 (AllWinning.cons node_21734 (AllWinning.nil))))))))))))

theorem node_23765 : Outcome ⟨17, 16, 6, 6⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 10⟩) (by decide) node_20868

theorem node_23766 : Outcome ⟨17, 17, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 5, 2⟩, ⟨15, 17, 5, 4⟩, ⟨17, 16, 5, 2⟩, ⟨17, 15, 5, 4⟩, ⟨17, 17, 4, 2⟩, ⟨17, 17, 3, 4⟩]
  exact AllWinning.cons node_23340 (AllWinning.cons node_22839 (AllWinning.cons node_23369 (AllWinning.cons node_22902 (AllWinning.cons node_23371 (AllWinning.cons node_22904 (AllWinning.nil))))))

theorem node_23767 : Outcome ⟨17, 17, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 5, 2⟩, ⟨15, 17, 5, 4⟩, ⟨14, 17, 5, 6⟩, ⟨13, 17, 5, 8⟩, ⟨17, 16, 5, 2⟩, ⟨17, 15, 5, 4⟩, ⟨17, 14, 5, 6⟩, ⟨17, 13, 5, 8⟩, ⟨17, 17, 4, 2⟩, ⟨17, 17, 3, 4⟩, ⟨17, 17, 2, 6⟩, ⟨17, 17, 1, 8⟩]
  exact AllWinning.cons node_23340 (AllWinning.cons node_22839 (AllWinning.cons node_22209 (AllWinning.cons node_21573 (AllWinning.cons node_23369 (AllWinning.cons node_22902 (AllWinning.cons node_22345 (AllWinning.cons node_21728 (AllWinning.cons node_23371 (AllWinning.cons node_22904 (AllWinning.cons node_22350 (AllWinning.cons node_21736 (AllWinning.nil))))))))))))

theorem node_23768 : Outcome ⟨17, 17, 5, 6⟩ true :=
  Outcome.win (q := ⟨17, 17, 0, 10⟩) (by decide) node_21137

theorem node_23769 : Outcome ⟨17, 18, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 18, 4, 2⟩, ⟨15, 18, 4, 4⟩, ⟨17, 17, 4, 2⟩, ⟨17, 16, 4, 4⟩, ⟨17, 18, 3, 2⟩, ⟨17, 18, 2, 4⟩]
  exact AllWinning.cons node_23341 (AllWinning.cons node_22840 (AllWinning.cons node_23371 (AllWinning.cons node_22903 (AllWinning.cons node_23373 (AllWinning.cons node_22906 (AllWinning.nil))))))

theorem node_23770 : Outcome ⟨18, 2, 19, 4⟩ true :=
  Outcome.win (q := ⟨18, 2, 16, 6⟩) (by decide) node_22357

theorem node_23771 : Outcome ⟨18, 3, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 6⟩) (by decide) node_22221

theorem node_23772 : Outcome ⟨18, 3, 18, 10⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 6⟩) (by decide) node_22221

theorem node_23773 : Outcome ⟨18, 4, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 4, 17, 6⟩) (by decide) node_22229

theorem node_23774 : Outcome ⟨18, 5, 16, 4⟩ true :=
  Outcome.win (q := ⟨18, 5, 12, 8⟩) (by decide) node_21747

theorem node_23775 : Outcome ⟨18, 7, 14, 2⟩ true :=
  Outcome.win (q := ⟨18, 6, 14, 2⟩) (by decide) node_23381

theorem node_23776 : Outcome ⟨18, 7, 14, 4⟩ true :=
  Outcome.win (q := ⟨18, 6, 14, 2⟩) (by decide) node_23381

theorem node_23777 : Outcome ⟨18, 7, 14, 10⟩ true :=
  Outcome.win (q := ⟨18, 6, 14, 2⟩) (by decide) node_23381

theorem node_23778 : Outcome ⟨18, 8, 13, 2⟩ true :=
  Outcome.win (q := ⟨18, 7, 13, 2⟩) (by decide) node_23384

theorem node_23779 : Outcome ⟨18, 8, 13, 10⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 10⟩) (by decide) node_21152

theorem node_23780 : Outcome ⟨18, 9, 12, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 12, 2⟩) (by decide) node_23354

theorem node_23781 : Outcome ⟨18, 9, 12, 10⟩ true :=
  Outcome.win (q := ⟨18, 5, 12, 8⟩) (by decide) node_21747

theorem node_23782 : Outcome ⟨18, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨18, 9, 11, 2⟩) (by decide) node_23391

theorem node_23783 : Outcome ⟨18, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨18, 11, 9, 2⟩) (by decide) node_23393

theorem node_23784 : Outcome ⟨18, 12, 9, 2⟩ true :=
  Outcome.win (q := ⟨17, 12, 9, 2⟩) (by decide) node_23361

theorem node_23785 : Outcome ⟨18, 12, 9, 10⟩ true :=
  Outcome.win (q := ⟨18, 12, 5, 8⟩) (by decide) node_21754

theorem node_23786 : Outcome ⟨18, 13, 8, 2⟩ true :=
  Outcome.win (q := ⟨18, 12, 8, 2⟩) (by decide) node_23394

theorem node_23787 : Outcome ⟨18, 13, 8, 10⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 10⟩) (by decide) node_21152

theorem node_23788 : Outcome ⟨18, 14, 7, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 7, 2⟩) (by decide) node_23397

theorem node_23789 : Outcome ⟨18, 14, 7, 4⟩ true :=
  Outcome.win (q := ⟨18, 13, 7, 2⟩) (by decide) node_23397

theorem node_23790 : Outcome ⟨18, 14, 7, 10⟩ true :=
  Outcome.win (q := ⟨18, 13, 7, 2⟩) (by decide) node_23397

theorem node_23791 : Outcome ⟨18, 16, 5, 4⟩ true :=
  Outcome.win (q := ⟨18, 12, 5, 8⟩) (by decide) node_21754

theorem node_23792 : Outcome ⟨18, 17, 4, 4⟩ true :=
  Outcome.win (q := ⟨15, 17, 4, 6⟩) (by decide) node_22265

theorem node_23793 : Outcome ⟨18, 18, 3, 4⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 6⟩) (by decide) node_22268

theorem node_23794 : Outcome ⟨18, 18, 3, 10⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 6⟩) (by decide) node_22268

theorem node_23795 : Outcome ⟨18, 19, 2, 4⟩ true :=
  Outcome.win (q := ⟨18, 16, 2, 6⟩) (by decide) node_22377

theorem node_23796 : Outcome ⟨19, 1, 19, 8⟩ true :=
  Outcome.win (q := ⟨18, 1, 19, 2⟩) (by decide) node_23376

theorem node_23797 : Outcome ⟨19, 5, 15, 8⟩ true :=
  Outcome.win (q := ⟨19, 5, 10, 10⟩) (by decide) node_21173

theorem node_23798 : Outcome ⟨19, 7, 13, 2⟩ true :=
  Outcome.win (q := ⟨18, 7, 13, 2⟩) (by decide) node_23384

theorem node_23799 : Outcome ⟨19, 8, 12, 2⟩ true :=
  Outcome.win (q := ⟨18, 8, 12, 2⟩) (by decide) node_23388

theorem node_23800 : Outcome ⟨19, 8, 12, 8⟩ true :=
  Outcome.win (q := ⟨18, 8, 12, 2⟩) (by decide) node_23388

theorem node_23801 : Outcome ⟨19, 9, 11, 2⟩ true :=
  Outcome.win (q := ⟨18, 9, 11, 2⟩) (by decide) node_23391

theorem node_23802 : Outcome ⟨19, 10, 10, 2⟩ true :=
  Outcome.win (q := ⟨17, 10, 10, 4⟩) (by decide) node_22893

theorem node_23803 : Outcome ⟨19, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨18, 11, 9, 2⟩) (by decide) node_23393

theorem node_23804 : Outcome ⟨19, 12, 8, 2⟩ true :=
  Outcome.win (q := ⟨18, 12, 8, 2⟩) (by decide) node_23394

theorem node_23805 : Outcome ⟨19, 12, 8, 8⟩ true :=
  Outcome.win (q := ⟨18, 12, 8, 2⟩) (by decide) node_23394

theorem node_23806 : Outcome ⟨19, 13, 7, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 7, 2⟩) (by decide) node_23397

theorem node_23807 : Outcome ⟨19, 15, 5, 8⟩ true :=
  Outcome.win (q := ⟨19, 10, 5, 10⟩) (by decide) node_21180

theorem node_23808 : Outcome ⟨19, 19, 1, 8⟩ true :=
  Outcome.win (q := ⟨18, 19, 1, 2⟩) (by decide) node_23406

theorem node_23809 : Outcome ⟨0, 20, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 20, 2⟩, ⟨0, 18, 20, 4⟩, ⟨0, 20, 19, 2⟩, ⟨0, 20, 18, 4⟩]
  exact AllWinning.cons node_23423 (AllWinning.cons node_22945 (AllWinning.cons node_23424 (AllWinning.cons node_22950 (AllWinning.nil))))

theorem node_23810 : Outcome ⟨0, 20, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 20, 2⟩, ⟨0, 18, 20, 4⟩, ⟨0, 17, 20, 6⟩, ⟨0, 16, 20, 8⟩, ⟨0, 20, 19, 2⟩, ⟨0, 20, 18, 4⟩, ⟨0, 20, 17, 6⟩, ⟨0, 20, 16, 8⟩]
  exact AllWinning.cons node_23423 (AllWinning.cons node_22945 (AllWinning.cons node_22399 (AllWinning.cons node_21777 (AllWinning.cons node_23424 (AllWinning.cons node_22950 (AllWinning.cons node_22402 (AllWinning.cons node_21787 (AllWinning.nil))))))))

theorem node_23811 : Outcome ⟨0, 20, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 20, 2⟩, ⟨0, 18, 20, 4⟩, ⟨0, 17, 20, 6⟩, ⟨0, 16, 20, 8⟩, ⟨0, 15, 20, 10⟩, ⟨0, 14, 20, 12⟩, ⟨0, 20, 19, 2⟩, ⟨0, 20, 18, 4⟩, ⟨0, 20, 17, 6⟩, ⟨0, 20, 16, 8⟩, ⟨0, 20, 15, 10⟩, ⟨0, 20, 14, 12⟩]
  exact AllWinning.cons node_23423 (AllWinning.cons node_22945 (AllWinning.cons node_22399 (AllWinning.cons node_21777 (AllWinning.cons node_21190 (AllWinning.cons node_20405 (AllWinning.cons node_23424 (AllWinning.cons node_22950 (AllWinning.cons node_22402 (AllWinning.cons node_21787 (AllWinning.cons node_21198 (AllWinning.cons node_20419 (AllWinning.nil))))))))))))

theorem node_23812 : Outcome ⟨0, 20, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 20, 2⟩, ⟨0, 18, 20, 4⟩, ⟨0, 17, 20, 6⟩, ⟨0, 16, 20, 8⟩, ⟨0, 15, 20, 10⟩, ⟨0, 14, 20, 12⟩, ⟨0, 13, 20, 14⟩, ⟨0, 12, 20, 16⟩, ⟨0, 20, 19, 2⟩, ⟨0, 20, 18, 4⟩, ⟨0, 20, 17, 6⟩, ⟨0, 20, 16, 8⟩, ⟨0, 20, 15, 10⟩, ⟨0, 20, 14, 12⟩, ⟨0, 20, 13, 14⟩, ⟨0, 20, 12, 16⟩]
  exact AllWinning.cons node_23423 (AllWinning.cons node_22945 (AllWinning.cons node_22399 (AllWinning.cons node_21777 (AllWinning.cons node_21190 (AllWinning.cons node_20405 (AllWinning.cons node_19692 (AllWinning.cons node_18802 (AllWinning.cons node_23424 (AllWinning.cons node_22950 (AllWinning.cons node_22402 (AllWinning.cons node_21787 (AllWinning.cons node_21198 (AllWinning.cons node_20419 (AllWinning.cons node_19710 (AllWinning.cons node_18831 (AllWinning.nil))))))))))))))))

theorem node_23813 : Outcome ⟨0, 20, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 20, 2⟩, ⟨0, 18, 20, 4⟩, ⟨0, 17, 20, 6⟩, ⟨0, 16, 20, 8⟩, ⟨0, 15, 20, 10⟩, ⟨0, 14, 20, 12⟩, ⟨0, 13, 20, 14⟩, ⟨0, 12, 20, 16⟩, ⟨0, 11, 20, 18⟩, ⟨0, 10, 20, 20⟩, ⟨0, 20, 19, 2⟩, ⟨0, 20, 18, 4⟩, ⟨0, 20, 17, 6⟩, ⟨0, 20, 16, 8⟩, ⟨0, 20, 15, 10⟩, ⟨0, 20, 14, 12⟩, ⟨0, 20, 13, 14⟩, ⟨0, 20, 12, 16⟩, ⟨0, 20, 11, 18⟩, ⟨0, 20, 10, 20⟩]
  exact AllWinning.cons node_23423 (AllWinning.cons node_22945 (AllWinning.cons node_22399 (AllWinning.cons node_21777 (AllWinning.cons node_21190 (AllWinning.cons node_20405 (AllWinning.cons node_19692 (AllWinning.cons node_18802 (AllWinning.cons node_17881 (AllWinning.cons node_16973 (AllWinning.cons node_23424 (AllWinning.cons node_22950 (AllWinning.cons node_22402 (AllWinning.cons node_21787 (AllWinning.cons node_21198 (AllWinning.cons node_20419 (AllWinning.cons node_19710 (AllWinning.cons node_18831 (AllWinning.cons node_17906 (AllWinning.cons node_17011 (AllWinning.nil))))))))))))))))))))

theorem node_23814 : Outcome ⟨2, 18, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 20, 2⟩, ⟨0, 18, 20, 4⟩, ⟨2, 17, 20, 2⟩, ⟨2, 16, 20, 4⟩, ⟨2, 18, 19, 2⟩, ⟨2, 18, 18, 4⟩]
  exact AllWinning.cons node_23425 (AllWinning.cons node_22945 (AllWinning.cons node_23431 (AllWinning.cons node_22963 (AllWinning.cons node_23432 (AllWinning.cons node_22969 (AllWinning.nil))))))

theorem node_23815 : Outcome ⟨2, 18, 20, 14⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 8⟩) (by decide) node_21817

theorem node_23816 : Outcome ⟨2, 19, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 4⟩) (by decide) node_22947

theorem node_23817 : Outcome ⟨2, 19, 19, 6⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 4⟩) (by decide) node_22947

theorem node_23818 : Outcome ⟨2, 19, 19, 12⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 22⟩) (by decide) node_15991

theorem node_23819 : Outcome ⟨2, 20, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 18, 2⟩, ⟨0, 20, 18, 4⟩, ⟨2, 19, 18, 2⟩, ⟨2, 18, 18, 4⟩, ⟨2, 20, 17, 2⟩, ⟨2, 20, 16, 4⟩]
  exact AllWinning.cons node_23429 (AllWinning.cons node_22950 (AllWinning.cons node_23434 (AllWinning.cons node_22969 (AllWinning.cons node_23436 (AllWinning.cons node_22975 (AllWinning.nil))))))

theorem node_23820 : Outcome ⟨2, 20, 18, 14⟩ true :=
  Outcome.win (q := ⟨2, 16, 18, 8⟩) (by decide) node_21807

theorem node_23821 : Outcome ⟨3, 17, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 20, 2⟩, ⟨1, 17, 20, 4⟩, ⟨3, 16, 20, 2⟩, ⟨3, 15, 20, 4⟩, ⟨3, 17, 19, 2⟩, ⟨3, 17, 18, 4⟩]
  exact AllWinning.cons node_23431 (AllWinning.cons node_22951 (AllWinning.cons node_23437 (AllWinning.cons node_22977 (AllWinning.cons node_23439 (AllWinning.cons node_22981 (AllWinning.nil))))))

theorem node_23822 : Outcome ⟨3, 17, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 20, 2⟩, ⟨1, 17, 20, 4⟩, ⟨0, 17, 20, 6⟩, ⟨3, 16, 20, 2⟩, ⟨3, 15, 20, 4⟩, ⟨3, 14, 20, 6⟩, ⟨3, 13, 20, 8⟩, ⟨3, 17, 19, 2⟩, ⟨3, 17, 18, 4⟩, ⟨3, 17, 17, 6⟩, ⟨3, 17, 16, 8⟩]
  exact AllWinning.cons node_23431 (AllWinning.cons node_22951 (AllWinning.cons node_22399 (AllWinning.cons node_23437 (AllWinning.cons node_22977 (AllWinning.cons node_22423 (AllWinning.cons node_21825 (AllWinning.cons node_23439 (AllWinning.cons node_22981 (AllWinning.cons node_22427 (AllWinning.cons node_21838 (AllWinning.nil)))))))))))

theorem node_23823 : Outcome ⟨3, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 19, 4⟩) (by decide) node_22953

theorem node_23824 : Outcome ⟨3, 18, 19, 8⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 8⟩) (by decide) node_21842

theorem node_23825 : Outcome ⟨3, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 18, 4⟩) (by decide) node_22958

theorem node_23826 : Outcome ⟨3, 19, 18, 8⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 8⟩) (by decide) node_21829

theorem node_23827 : Outcome ⟨3, 20, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 20, 17, 2⟩, ⟨1, 20, 17, 4⟩, ⟨3, 19, 17, 2⟩, ⟨3, 18, 17, 4⟩, ⟨3, 20, 16, 2⟩, ⟨3, 20, 15, 4⟩]
  exact AllWinning.cons node_23436 (AllWinning.cons node_22962 (AllWinning.cons node_23444 (AllWinning.cons node_22983 (AllWinning.cons node_23446 (AllWinning.cons node_22984 (AllWinning.nil))))))

theorem node_23828 : Outcome ⟨3, 20, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 20, 17, 2⟩, ⟨1, 20, 17, 4⟩, ⟨0, 20, 17, 6⟩, ⟨3, 19, 17, 2⟩, ⟨3, 18, 17, 4⟩, ⟨3, 17, 17, 6⟩, ⟨3, 16, 17, 8⟩, ⟨3, 20, 16, 2⟩, ⟨3, 20, 15, 4⟩, ⟨3, 20, 14, 6⟩, ⟨3, 20, 13, 8⟩]
  exact AllWinning.cons node_23436 (AllWinning.cons node_22962 (AllWinning.cons node_22402 (AllWinning.cons node_23444 (AllWinning.cons node_22983 (AllWinning.cons node_22427 (AllWinning.cons node_21835 (AllWinning.cons node_23446 (AllWinning.cons node_22984 (AllWinning.cons node_22432 (AllWinning.cons node_21849 (AllWinning.nil)))))))))))

theorem node_23829 : Outcome ⟨4, 16, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 16, 20, 2⟩, ⟨2, 16, 20, 4⟩, ⟨4, 15, 20, 2⟩, ⟨4, 14, 20, 4⟩, ⟨4, 16, 19, 2⟩, ⟨4, 16, 18, 4⟩]
  exact AllWinning.cons node_23437 (AllWinning.cons node_22963 (AllWinning.cons node_23448 (AllWinning.cons node_22987 (AllWinning.cons node_23451 (AllWinning.cons node_22990 (AllWinning.nil))))))

theorem node_23830 : Outcome ⟨4, 16, 20, 6⟩ true :=
  Outcome.win (q := ⟨4, 13, 20, 6⟩) (by decide) node_22435

theorem node_23831 : Outcome ⟨4, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 19, 4⟩) (by decide) node_22966

theorem node_23832 : Outcome ⟨4, 17, 19, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 6⟩) (by decide) node_22438

theorem node_23833 : Outcome ⟨4, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 18, 2⟩) (by decide) node_23441

theorem node_23834 : Outcome ⟨4, 18, 18, 8⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 14⟩) (by decide) node_19800

theorem node_23835 : Outcome ⟨4, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 19, 17, 4⟩) (by decide) node_22973

theorem node_23836 : Outcome ⟨4, 19, 17, 4⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 6⟩) (by decide) node_22450

theorem node_23837 : Outcome ⟨4, 20, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 20, 16, 2⟩, ⟨2, 20, 16, 4⟩, ⟨4, 19, 16, 2⟩, ⟨4, 18, 16, 4⟩, ⟨4, 20, 15, 2⟩, ⟨4, 20, 14, 4⟩]
  exact AllWinning.cons node_23446 (AllWinning.cons node_22975 (AllWinning.cons node_23457 (AllWinning.cons node_22994 (AllWinning.cons node_23459 (AllWinning.cons node_22997 (AllWinning.nil))))))

theorem node_23838 : Outcome ⟨4, 20, 16, 6⟩ true :=
  Outcome.win (q := ⟨4, 20, 13, 6⟩) (by decide) node_22455

theorem node_23839 : Outcome ⟨5, 15, 20, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 20, 2⟩) (by decide) node_23461

theorem node_23840 : Outcome ⟨5, 15, 20, 16⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 24⟩) (by decide) node_15202

theorem node_23841 : Outcome ⟨5, 16, 19, 6⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 12⟩) (by decide) node_20521

theorem node_23842 : Outcome ⟨5, 16, 19, 12⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 12⟩) (by decide) node_20521

theorem node_23843 : Outcome ⟨5, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 18, 2⟩) (by decide) node_23453

theorem node_23844 : Outcome ⟨5, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 17, 2⟩) (by decide) node_23455

theorem node_23845 : Outcome ⟨5, 19, 16, 6⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 12⟩) (by decide) node_20543

theorem node_23846 : Outcome ⟨5, 19, 16, 12⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 12⟩) (by decide) node_20543

theorem node_23847 : Outcome ⟨5, 20, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 19, 15, 2⟩) (by decide) node_23470

theorem node_23848 : Outcome ⟨5, 20, 15, 16⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 24⟩) (by decide) node_15171

theorem node_23849 : Outcome ⟨6, 14, 20, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 20, 2⟩) (by decide) node_23461

theorem node_23850 : Outcome ⟨6, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 19, 2⟩) (by decide) node_23462

theorem node_23851 : Outcome ⟨6, 15, 19, 4⟩ true :=
  Outcome.win (q := ⟨5, 15, 19, 2⟩) (by decide) node_23462

theorem node_23852 : Outcome ⟨6, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 17, 2⟩) (by decide) node_23479

theorem node_23853 : Outcome ⟨6, 17, 17, 4⟩ true :=
  Outcome.win (q := ⟨5, 17, 17, 2⟩) (by decide) node_23466

theorem node_23854 : Outcome ⟨6, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 16, 2⟩) (by decide) node_23482

theorem node_23855 : Outcome ⟨6, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 19, 15, 2⟩) (by decide) node_23470

theorem node_23856 : Outcome ⟨6, 19, 15, 4⟩ true :=
  Outcome.win (q := ⟨5, 19, 15, 2⟩) (by decide) node_23470

theorem node_23857 : Outcome ⟨6, 20, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 20, 14, 2⟩) (by decide) node_23473

theorem node_23858 : Outcome ⟨7, 13, 20, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 20, 6⟩) (by decide) node_22435

theorem node_23859 : Outcome ⟨7, 13, 20, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 20, 10⟩) (by decide) node_21339

theorem node_23860 : Outcome ⟨7, 13, 20, 16⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 22⟩) (by decide) node_16307

theorem node_23861 : Outcome ⟨7, 14, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 14, 19, 2⟩, ⟨5, 14, 19, 4⟩, ⟨7, 13, 19, 2⟩, ⟨7, 12, 19, 4⟩, ⟨7, 14, 18, 2⟩, ⟨7, 14, 17, 4⟩]
  exact AllWinning.cons node_23475 (AllWinning.cons node_23000 (AllWinning.cons node_23492 (AllWinning.cons node_23041 (AllWinning.cons node_23493 (AllWinning.cons node_23047 (AllWinning.nil))))))

theorem node_23862 : Outcome ⟨7, 14, 19, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 6⟩) (by decide) node_22438

theorem node_23863 : Outcome ⟨7, 14, 19, 8⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 6⟩) (by decide) node_22438

theorem node_23864 : Outcome ⟨7, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨7, 13, 18, 4⟩) (by decide) node_23044

theorem node_23865 : Outcome ⟨7, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 8⟩) (by decide) node_21829

theorem node_23866 : Outcome ⟨7, 15, 18, 8⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 12⟩) (by decide) node_20623

theorem node_23867 : Outcome ⟨7, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 17, 2⟩) (by decide) node_23479

theorem node_23868 : Outcome ⟨7, 16, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 16, 17, 2⟩) (by decide) node_23479

theorem node_23869 : Outcome ⟨7, 16, 17, 6⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 12⟩) (by decide) node_20630

theorem node_23870 : Outcome ⟨7, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 16, 2⟩) (by decide) node_23482

theorem node_23871 : Outcome ⟨7, 17, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 16, 2⟩) (by decide) node_23482

theorem node_23872 : Outcome ⟨7, 17, 16, 6⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 12⟩) (by decide) node_20604

theorem node_23873 : Outcome ⟨7, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 13, 4⟩) (by decide) node_23056

theorem node_23874 : Outcome ⟨7, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 8⟩) (by decide) node_21842

theorem node_23875 : Outcome ⟨7, 18, 15, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 12⟩) (by decide) node_20612

theorem node_23876 : Outcome ⟨7, 19, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 19, 14, 2⟩, ⟨5, 19, 14, 4⟩, ⟨7, 18, 14, 2⟩, ⟨7, 17, 14, 4⟩, ⟨7, 19, 13, 2⟩, ⟨7, 19, 12, 4⟩]
  exact AllWinning.cons node_23487 (AllWinning.cons node_23013 (AllWinning.cons node_23500 (AllWinning.cons node_23053 (AllWinning.cons node_23503 (AllWinning.cons node_23060 (AllWinning.nil))))))

theorem node_23877 : Outcome ⟨7, 19, 14, 4⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 6⟩) (by decide) node_22450

theorem node_23878 : Outcome ⟨7, 19, 14, 8⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 6⟩) (by decide) node_22450

theorem node_23879 : Outcome ⟨7, 20, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 20, 13, 6⟩) (by decide) node_22455

theorem node_23880 : Outcome ⟨7, 20, 13, 6⟩ true :=
  Outcome.win (q := ⟨7, 20, 8, 10⟩) (by decide) node_21359

theorem node_23881 : Outcome ⟨7, 20, 13, 16⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 22⟩) (by decide) node_16291

theorem node_23882 : Outcome ⟨8, 12, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 20, 2⟩, ⟨6, 12, 20, 4⟩, ⟨8, 11, 20, 2⟩, ⟨8, 10, 20, 4⟩, ⟨8, 12, 19, 2⟩, ⟨8, 12, 18, 4⟩]
  exact AllWinning.cons node_23490 (AllWinning.cons node_23017 (AllWinning.cons node_23506 (AllWinning.cons node_23065 (AllWinning.cons node_23508 (AllWinning.cons node_23068 (AllWinning.nil))))))

theorem node_23883 : Outcome ⟨8, 12, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 20, 2⟩, ⟨6, 12, 20, 4⟩, ⟨5, 12, 20, 6⟩, ⟨4, 12, 20, 8⟩, ⟨8, 11, 20, 2⟩, ⟨8, 10, 20, 4⟩, ⟨8, 9, 20, 6⟩, ⟨8, 8, 20, 8⟩, ⟨8, 12, 19, 2⟩, ⟨8, 12, 18, 4⟩, ⟨8, 12, 17, 6⟩, ⟨8, 12, 16, 8⟩]
  exact AllWinning.cons node_23490 (AllWinning.cons node_23017 (AllWinning.cons node_22458 (AllWinning.cons node_21852 (AllWinning.cons node_23506 (AllWinning.cons node_23065 (AllWinning.cons node_22530 (AllWinning.cons node_21954 (AllWinning.cons node_23508 (AllWinning.cons node_23068 (AllWinning.cons node_22534 (AllWinning.cons node_21964 (AllWinning.nil))))))))))))

theorem node_23884 : Outcome ⟨8, 13, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 19, 2⟩, ⟨6, 13, 19, 4⟩, ⟨8, 12, 19, 2⟩, ⟨8, 11, 19, 4⟩, ⟨8, 13, 18, 2⟩, ⟨8, 13, 17, 4⟩]
  exact AllWinning.cons node_23492 (AllWinning.cons node_23019 (AllWinning.cons node_23508 (AllWinning.cons node_23066 (AllWinning.cons node_23510 (AllWinning.cons node_23070 (AllWinning.nil))))))

theorem node_23885 : Outcome ⟨8, 13, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 19, 2⟩, ⟨6, 13, 19, 4⟩, ⟨5, 13, 19, 6⟩, ⟨4, 13, 19, 8⟩, ⟨8, 12, 19, 2⟩, ⟨8, 11, 19, 4⟩, ⟨8, 10, 19, 6⟩, ⟨8, 9, 19, 8⟩, ⟨8, 13, 18, 2⟩, ⟨8, 13, 17, 4⟩, ⟨8, 13, 16, 6⟩, ⟨8, 13, 15, 8⟩]
  exact AllWinning.cons node_23492 (AllWinning.cons node_23019 (AllWinning.cons node_22461 (AllWinning.cons node_21854 (AllWinning.cons node_23508 (AllWinning.cons node_23066 (AllWinning.cons node_22531 (AllWinning.cons node_21955 (AllWinning.cons node_23510 (AllWinning.cons node_23070 (AllWinning.cons node_22537 (AllWinning.cons node_21967 (AllWinning.nil))))))))))))

theorem node_23886 : Outcome ⟨8, 13, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 19, 2⟩, ⟨6, 13, 19, 4⟩, ⟨5, 13, 19, 6⟩, ⟨4, 13, 19, 8⟩, ⟨3, 13, 19, 10⟩, ⟨2, 13, 19, 12⟩, ⟨8, 12, 19, 2⟩, ⟨8, 11, 19, 4⟩, ⟨8, 10, 19, 6⟩, ⟨8, 9, 19, 8⟩, ⟨8, 8, 19, 10⟩, ⟨8, 7, 19, 12⟩, ⟨8, 13, 18, 2⟩, ⟨8, 13, 17, 4⟩, ⟨8, 13, 16, 6⟩, ⟨8, 13, 15, 8⟩, ⟨8, 13, 14, 10⟩, ⟨8, 13, 13, 12⟩]
  exact AllWinning.cons node_23492 (AllWinning.cons node_23019 (AllWinning.cons node_22461 (AllWinning.cons node_21854 (AllWinning.cons node_21243 (AllWinning.cons node_20446 (AllWinning.cons node_23508 (AllWinning.cons node_23066 (AllWinning.cons node_22531 (AllWinning.cons node_21955 (AllWinning.cons node_21366 (AllWinning.cons node_20645 (AllWinning.cons node_23510 (AllWinning.cons node_23070 (AllWinning.cons node_22537 (AllWinning.cons node_21967 (AllWinning.cons node_21375 (AllWinning.cons node_20665 (AllWinning.nil))))))))))))))))))

theorem node_23887 : Outcome ⟨8, 13, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 19, 2⟩, ⟨6, 13, 19, 4⟩, ⟨5, 13, 19, 6⟩, ⟨4, 13, 19, 8⟩, ⟨3, 13, 19, 10⟩, ⟨2, 13, 19, 12⟩, ⟨1, 13, 19, 14⟩, ⟨0, 13, 19, 16⟩, ⟨8, 12, 19, 2⟩, ⟨8, 11, 19, 4⟩, ⟨8, 10, 19, 6⟩, ⟨8, 9, 19, 8⟩, ⟨8, 8, 19, 10⟩, ⟨8, 7, 19, 12⟩, ⟨8, 6, 19, 14⟩, ⟨8, 5, 19, 16⟩, ⟨8, 13, 18, 2⟩, ⟨8, 13, 17, 4⟩, ⟨8, 13, 16, 6⟩, ⟨8, 13, 15, 8⟩, ⟨8, 13, 14, 10⟩, ⟨8, 13, 13, 12⟩, ⟨8, 13, 12, 14⟩, ⟨8, 13, 11, 16⟩]
  exact AllWinning.cons node_23492 (AllWinning.cons node_23019 (AllWinning.cons node_22461 (AllWinning.cons node_21854 (AllWinning.cons node_21243 (AllWinning.cons node_20446 (AllWinning.cons node_19717 (AllWinning.cons node_18806 (AllWinning.cons node_23508 (AllWinning.cons node_23066 (AllWinning.cons node_22531 (AllWinning.cons node_21955 (AllWinning.cons node_21366 (AllWinning.cons node_20645 (AllWinning.cons node_19916 (AllWinning.cons node_19103 (AllWinning.cons node_23510 (AllWinning.cons node_23070 (AllWinning.cons node_22537 (AllWinning.cons node_21967 (AllWinning.cons node_21375 (AllWinning.cons node_20665 (AllWinning.cons node_19932 (AllWinning.cons node_19125 (AllWinning.nil))))))))))))))))))))))))

theorem node_23888 : Outcome ⟨8, 13, 19, 12⟩ true :=
  Outcome.win (q := ⟨8, 2, 19, 22⟩) (by decide) node_16336

theorem node_23889 : Outcome ⟨8, 14, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 14, 18, 2⟩, ⟨6, 14, 18, 4⟩, ⟨8, 13, 18, 2⟩, ⟨8, 12, 18, 4⟩, ⟨8, 14, 17, 2⟩, ⟨8, 14, 16, 4⟩]
  exact AllWinning.cons node_23493 (AllWinning.cons node_23021 (AllWinning.cons node_23510 (AllWinning.cons node_23068 (AllWinning.cons node_23512 (AllWinning.cons node_23072 (AllWinning.nil))))))

theorem node_23890 : Outcome ⟨8, 14, 18, 8⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 12⟩) (by decide) node_20650

theorem node_23891 : Outcome ⟨8, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 6⟩) (by decide) node_22546

theorem node_23892 : Outcome ⟨8, 16, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 16, 2⟩, ⟨6, 16, 16, 4⟩, ⟨8, 15, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨8, 16, 15, 2⟩, ⟨8, 16, 14, 4⟩]
  exact AllWinning.cons node_23496 (AllWinning.cons node_23026 (AllWinning.cons node_23514 (AllWinning.cons node_23072 (AllWinning.cons node_23516 (AllWinning.cons node_23074 (AllWinning.nil))))))

theorem node_23893 : Outcome ⟨8, 16, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 16, 2⟩, ⟨6, 16, 16, 4⟩, ⟨5, 16, 16, 6⟩, ⟨4, 16, 16, 8⟩, ⟨8, 15, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨8, 13, 16, 6⟩, ⟨8, 12, 16, 8⟩, ⟨8, 16, 15, 2⟩, ⟨8, 16, 14, 4⟩, ⟨8, 16, 13, 6⟩, ⟨8, 16, 12, 8⟩]
  exact AllWinning.cons node_23496 (AllWinning.cons node_23026 (AllWinning.cons node_22468 (AllWinning.cons node_21861 (AllWinning.cons node_23514 (AllWinning.cons node_23072 (AllWinning.cons node_22537 (AllWinning.cons node_21964 (AllWinning.cons node_23516 (AllWinning.cons node_23074 (AllWinning.cons node_22550 (AllWinning.cons node_21976 (AllWinning.nil))))))))))))

theorem node_23894 : Outcome ⟨8, 16, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 16, 2⟩, ⟨6, 16, 16, 4⟩, ⟨5, 16, 16, 6⟩, ⟨4, 16, 16, 8⟩, ⟨3, 16, 16, 10⟩, ⟨2, 16, 16, 12⟩, ⟨8, 15, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨8, 13, 16, 6⟩, ⟨8, 12, 16, 8⟩, ⟨8, 11, 16, 10⟩, ⟨8, 10, 16, 12⟩, ⟨8, 16, 15, 2⟩, ⟨8, 16, 14, 4⟩, ⟨8, 16, 13, 6⟩, ⟨8, 16, 12, 8⟩, ⟨8, 16, 11, 10⟩, ⟨8, 16, 10, 12⟩]
  exact AllWinning.cons node_23496 (AllWinning.cons node_23026 (AllWinning.cons node_22468 (AllWinning.cons node_21861 (AllWinning.cons node_21247 (AllWinning.cons node_20453 (AllWinning.cons node_23514 (AllWinning.cons node_23072 (AllWinning.cons node_22537 (AllWinning.cons node_21964 (AllWinning.cons node_21372 (AllWinning.cons node_20655 (AllWinning.cons node_23516 (AllWinning.cons node_23074 (AllWinning.cons node_22550 (AllWinning.cons node_21976 (AllWinning.cons node_21383 (AllWinning.cons node_20672 (AllWinning.nil))))))))))))))))))

theorem node_23895 : Outcome ⟨8, 16, 16, 10⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 16⟩) (by decide) node_18819

theorem node_23896 : Outcome ⟨8, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 6⟩) (by decide) node_22541

theorem node_23897 : Outcome ⟨8, 18, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 18, 14, 2⟩, ⟨6, 18, 14, 4⟩, ⟨8, 17, 14, 2⟩, ⟨8, 16, 14, 4⟩, ⟨8, 18, 13, 2⟩, ⟨8, 18, 12, 4⟩]
  exact AllWinning.cons node_23500 (AllWinning.cons node_23031 (AllWinning.cons node_23518 (AllWinning.cons node_23074 (AllWinning.cons node_23520 (AllWinning.cons node_23078 (AllWinning.nil))))))

theorem node_23898 : Outcome ⟨8, 18, 14, 8⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 12⟩) (by decide) node_20679

theorem node_23899 : Outcome ⟨8, 19, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 19, 13, 2⟩, ⟨6, 19, 13, 4⟩, ⟨8, 18, 13, 2⟩, ⟨8, 17, 13, 4⟩, ⟨8, 19, 12, 2⟩, ⟨8, 19, 11, 4⟩]
  exact AllWinning.cons node_23503 (AllWinning.cons node_23033 (AllWinning.cons node_23520 (AllWinning.cons node_23075 (AllWinning.cons node_23522 (AllWinning.cons node_23080 (AllWinning.nil))))))

theorem node_23900 : Outcome ⟨8, 19, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 19, 13, 2⟩, ⟨6, 19, 13, 4⟩, ⟨5, 19, 13, 6⟩, ⟨4, 19, 13, 8⟩, ⟨8, 18, 13, 2⟩, ⟨8, 17, 13, 4⟩, ⟨8, 16, 13, 6⟩, ⟨8, 15, 13, 8⟩, ⟨8, 19, 12, 2⟩, ⟨8, 19, 11, 4⟩, ⟨8, 19, 10, 6⟩, ⟨8, 19, 9, 8⟩]
  exact AllWinning.cons node_23503 (AllWinning.cons node_23033 (AllWinning.cons node_22476 (AllWinning.cons node_21868 (AllWinning.cons node_23520 (AllWinning.cons node_23075 (AllWinning.cons node_22550 (AllWinning.cons node_21972 (AllWinning.cons node_23522 (AllWinning.cons node_23080 (AllWinning.cons node_22556 (AllWinning.cons node_21984 (AllWinning.nil))))))))))))

theorem node_23901 : Outcome ⟨8, 19, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 19, 13, 2⟩, ⟨6, 19, 13, 4⟩, ⟨5, 19, 13, 6⟩, ⟨4, 19, 13, 8⟩, ⟨3, 19, 13, 10⟩, ⟨2, 19, 13, 12⟩, ⟨8, 18, 13, 2⟩, ⟨8, 17, 13, 4⟩, ⟨8, 16, 13, 6⟩, ⟨8, 15, 13, 8⟩, ⟨8, 14, 13, 10⟩, ⟨8, 13, 13, 12⟩, ⟨8, 19, 12, 2⟩, ⟨8, 19, 11, 4⟩, ⟨8, 19, 10, 6⟩, ⟨8, 19, 9, 8⟩, ⟨8, 19, 8, 10⟩, ⟨8, 19, 7, 12⟩]
  exact AllWinning.cons node_23503 (AllWinning.cons node_23033 (AllWinning.cons node_22476 (AllWinning.cons node_21868 (AllWinning.cons node_21251 (AllWinning.cons node_20460 (AllWinning.cons node_23520 (AllWinning.cons node_23075 (AllWinning.cons node_22550 (AllWinning.cons node_21972 (AllWinning.cons node_21378 (AllWinning.cons node_20665 (AllWinning.cons node_23522 (AllWinning.cons node_23080 (AllWinning.cons node_22556 (AllWinning.cons node_21984 (AllWinning.cons node_21387 (AllWinning.cons node_20682 (AllWinning.nil))))))))))))))))))

theorem node_23902 : Outcome ⟨8, 19, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 19, 13, 2⟩, ⟨6, 19, 13, 4⟩, ⟨5, 19, 13, 6⟩, ⟨4, 19, 13, 8⟩, ⟨3, 19, 13, 10⟩, ⟨2, 19, 13, 12⟩, ⟨1, 19, 13, 14⟩, ⟨0, 19, 13, 16⟩, ⟨8, 18, 13, 2⟩, ⟨8, 17, 13, 4⟩, ⟨8, 16, 13, 6⟩, ⟨8, 15, 13, 8⟩, ⟨8, 14, 13, 10⟩, ⟨8, 13, 13, 12⟩, ⟨8, 12, 13, 14⟩, ⟨8, 11, 13, 16⟩, ⟨8, 19, 12, 2⟩, ⟨8, 19, 11, 4⟩, ⟨8, 19, 10, 6⟩, ⟨8, 19, 9, 8⟩, ⟨8, 19, 8, 10⟩, ⟨8, 19, 7, 12⟩, ⟨8, 19, 6, 14⟩, ⟨8, 19, 5, 16⟩]
  exact AllWinning.cons node_23503 (AllWinning.cons node_23033 (AllWinning.cons node_22476 (AllWinning.cons node_21868 (AllWinning.cons node_21251 (AllWinning.cons node_20460 (AllWinning.cons node_19736 (AllWinning.cons node_18828 (AllWinning.cons node_23520 (AllWinning.cons node_23075 (AllWinning.cons node_22550 (AllWinning.cons node_21972 (AllWinning.cons node_21378 (AllWinning.cons node_20665 (AllWinning.cons node_19930 (AllWinning.cons node_19119 (AllWinning.cons node_23522 (AllWinning.cons node_23080 (AllWinning.cons node_22556 (AllWinning.cons node_21984 (AllWinning.cons node_21387 (AllWinning.cons node_20682 (AllWinning.cons node_19945 (AllWinning.cons node_19139 (AllWinning.nil))))))))))))))))))))))))

theorem node_23903 : Outcome ⟨8, 19, 13, 12⟩ true :=
  Outcome.win (q := ⟨8, 19, 2, 22⟩) (by decide) node_16397

theorem node_23904 : Outcome ⟨8, 20, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 20, 12, 2⟩, ⟨6, 20, 12, 4⟩, ⟨8, 19, 12, 2⟩, ⟨8, 18, 12, 4⟩, ⟨8, 20, 11, 2⟩, ⟨8, 20, 10, 4⟩]
  exact AllWinning.cons node_23504 (AllWinning.cons node_23035 (AllWinning.cons node_23522 (AllWinning.cons node_23078 (AllWinning.cons node_23524 (AllWinning.cons node_23081 (AllWinning.nil))))))

theorem node_23905 : Outcome ⟨8, 20, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 20, 12, 2⟩, ⟨6, 20, 12, 4⟩, ⟨5, 20, 12, 6⟩, ⟨4, 20, 12, 8⟩, ⟨8, 19, 12, 2⟩, ⟨8, 18, 12, 4⟩, ⟨8, 17, 12, 6⟩, ⟨8, 16, 12, 8⟩, ⟨8, 20, 11, 2⟩, ⟨8, 20, 10, 4⟩, ⟨8, 20, 9, 6⟩, ⟨8, 20, 8, 8⟩]
  exact AllWinning.cons node_23504 (AllWinning.cons node_23035 (AllWinning.cons node_22479 (AllWinning.cons node_21871 (AllWinning.cons node_23522 (AllWinning.cons node_23078 (AllWinning.cons node_22553 (AllWinning.cons node_21976 (AllWinning.cons node_23524 (AllWinning.cons node_23081 (AllWinning.cons node_22558 (AllWinning.cons node_21985 (AllWinning.nil))))))))))))

theorem node_23906 : Outcome ⟨9, 11, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 4⟩) (by decide) node_23083

theorem node_23907 : Outcome ⟨9, 11, 20, 14⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 4⟩) (by decide) node_23083

theorem node_23908 : Outcome ⟨9, 12, 19, 4⟩ true :=
  Outcome.win (q := ⟨9, 12, 17, 4⟩) (by decide) node_23093

theorem node_23909 : Outcome ⟨9, 12, 19, 6⟩ true :=
  Outcome.win (q := ⟨9, 12, 17, 4⟩) (by decide) node_23093

theorem node_23910 : Outcome ⟨9, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 6⟩) (by decide) node_22572

theorem node_23911 : Outcome ⟨9, 13, 18, 8⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 6⟩) (by decide) node_22572

theorem node_23912 : Outcome ⟨9, 13, 18, 14⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 22⟩) (by decide) node_16458

theorem node_23913 : Outcome ⟨9, 14, 17, 4⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 6⟩) (by decide) node_22576

theorem node_23914 : Outcome ⟨9, 15, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 15, 16, 2⟩, ⟨7, 15, 16, 4⟩, ⟨9, 14, 16, 2⟩, ⟨9, 13, 16, 4⟩, ⟨9, 15, 15, 2⟩, ⟨9, 15, 14, 4⟩]
  exact AllWinning.cons node_23514 (AllWinning.cons node_23049 (AllWinning.cons node_23536 (AllWinning.cons node_23095 (AllWinning.cons node_23538 (AllWinning.cons node_23100 (AllWinning.nil))))))

theorem node_23915 : Outcome ⟨9, 15, 16, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 6⟩) (by decide) node_22581

theorem node_23916 : Outcome ⟨9, 15, 16, 6⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 6⟩) (by decide) node_22581

theorem node_23917 : Outcome ⟨9, 16, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 16, 15, 2⟩, ⟨7, 16, 15, 4⟩, ⟨9, 15, 15, 2⟩, ⟨9, 14, 15, 4⟩, ⟨9, 16, 14, 2⟩, ⟨9, 16, 13, 4⟩]
  exact AllWinning.cons node_23516 (AllWinning.cons node_23051 (AllWinning.cons node_23538 (AllWinning.cons node_23098 (AllWinning.cons node_23540 (AllWinning.cons node_23102 (AllWinning.nil))))))

theorem node_23918 : Outcome ⟨9, 16, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 6⟩) (by decide) node_22572

theorem node_23919 : Outcome ⟨9, 16, 15, 6⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 6⟩) (by decide) node_22572

theorem node_23920 : Outcome ⟨9, 17, 14, 4⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 6⟩) (by decide) node_22576

theorem node_23921 : Outcome ⟨9, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 6⟩) (by decide) node_22581

theorem node_23922 : Outcome ⟨9, 18, 13, 8⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 6⟩) (by decide) node_22581

theorem node_23923 : Outcome ⟨9, 18, 13, 14⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 22⟩) (by decide) node_16436

theorem node_23924 : Outcome ⟨9, 19, 12, 4⟩ true :=
  Outcome.win (q := ⟨9, 17, 12, 4⟩) (by decide) node_23105

theorem node_23925 : Outcome ⟨9, 19, 12, 6⟩ true :=
  Outcome.win (q := ⟨9, 17, 12, 4⟩) (by decide) node_23105

theorem node_23926 : Outcome ⟨9, 20, 11, 4⟩ true :=
  Outcome.win (q := ⟨9, 18, 11, 4⟩) (by decide) node_23108

theorem node_23927 : Outcome ⟨9, 20, 11, 14⟩ true :=
  Outcome.win (q := ⟨9, 18, 11, 4⟩) (by decide) node_23108

theorem node_23928 : Outcome ⟨10, 10, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 10, 20, 2⟩, ⟨8, 10, 20, 4⟩, ⟨10, 9, 20, 2⟩, ⟨10, 8, 20, 4⟩, ⟨10, 10, 19, 2⟩, ⟨10, 10, 18, 4⟩]
  exact AllWinning.cons node_23526 (AllWinning.cons node_23065 (AllWinning.cons node_23552 (AllWinning.cons node_23118 (AllWinning.cons node_23553 (AllWinning.cons node_23121 (AllWinning.nil))))))

theorem node_23929 : Outcome ⟨10, 11, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 19, 2⟩, ⟨8, 11, 19, 4⟩, ⟨10, 10, 19, 2⟩, ⟨10, 9, 19, 4⟩, ⟨10, 11, 18, 2⟩, ⟨10, 11, 17, 4⟩]
  exact AllWinning.cons node_23528 (AllWinning.cons node_23066 (AllWinning.cons node_23553 (AllWinning.cons node_23119 (AllWinning.cons node_23554 (AllWinning.cons node_23122 (AllWinning.nil))))))

theorem node_23930 : Outcome ⟨10, 11, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 19, 2⟩, ⟨8, 11, 19, 4⟩, ⟨7, 11, 19, 6⟩, ⟨6, 11, 19, 8⟩, ⟨10, 10, 19, 2⟩, ⟨10, 9, 19, 4⟩, ⟨10, 8, 19, 6⟩, ⟨10, 7, 19, 8⟩, ⟨10, 11, 18, 2⟩, ⟨10, 11, 17, 4⟩, ⟨10, 11, 16, 6⟩, ⟨10, 11, 15, 8⟩]
  exact AllWinning.cons node_23528 (AllWinning.cons node_23066 (AllWinning.cons node_22507 (AllWinning.cons node_21901 (AllWinning.cons node_23553 (AllWinning.cons node_23119 (AllWinning.cons node_22594 (AllWinning.cons node_22016 (AllWinning.cons node_23554 (AllWinning.cons node_23122 (AllWinning.cons node_22601 (AllWinning.cons node_22025 (AllWinning.nil))))))))))))

theorem node_23931 : Outcome ⟨10, 11, 19, 12⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 22⟩) (by decide) node_16522

theorem node_23932 : Outcome ⟨10, 12, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 12, 18, 2⟩, ⟨8, 12, 18, 4⟩, ⟨7, 12, 18, 6⟩, ⟨6, 12, 18, 8⟩, ⟨10, 11, 18, 2⟩, ⟨10, 10, 18, 4⟩, ⟨10, 9, 18, 6⟩, ⟨10, 8, 18, 8⟩, ⟨10, 12, 17, 2⟩, ⟨10, 12, 16, 4⟩, ⟨10, 12, 15, 6⟩, ⟨10, 12, 14, 8⟩]
  exact AllWinning.cons node_23530 (AllWinning.cons node_23068 (AllWinning.cons node_22509 (AllWinning.cons node_21903 (AllWinning.cons node_23554 (AllWinning.cons node_23121 (AllWinning.cons node_22596 (AllWinning.cons node_22018 (AllWinning.cons node_23555 (AllWinning.cons node_23125 (AllWinning.cons node_22603 (AllWinning.cons node_22028 (AllWinning.nil))))))))))))

theorem node_23933 : Outcome ⟨10, 12, 18, 8⟩ true :=
  Outcome.win (q := ⟨10, 6, 18, 12⟩) (by decide) node_20742

theorem node_23934 : Outcome ⟨10, 13, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 13, 17, 2⟩, ⟨8, 13, 17, 4⟩, ⟨10, 12, 17, 2⟩, ⟨10, 11, 17, 4⟩, ⟨10, 13, 16, 2⟩, ⟨10, 13, 15, 4⟩]
  exact AllWinning.cons node_23534 (AllWinning.cons node_23070 (AllWinning.cons node_23555 (AllWinning.cons node_23122 (AllWinning.cons node_23557 (AllWinning.cons node_23127 (AllWinning.nil))))))

theorem node_23935 : Outcome ⟨10, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 6⟩) (by decide) node_22598

theorem node_23936 : Outcome ⟨10, 14, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 14, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨10, 13, 16, 2⟩, ⟨10, 12, 16, 4⟩, ⟨10, 14, 15, 2⟩, ⟨10, 14, 14, 4⟩]
  exact AllWinning.cons node_23536 (AllWinning.cons node_23072 (AllWinning.cons node_23557 (AllWinning.cons node_23125 (AllWinning.cons node_23559 (AllWinning.cons node_23129 (AllWinning.nil))))))

theorem node_23937 : Outcome ⟨10, 14, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 14, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨7, 14, 16, 6⟩, ⟨6, 14, 16, 8⟩, ⟨10, 13, 16, 2⟩, ⟨10, 12, 16, 4⟩, ⟨10, 11, 16, 6⟩, ⟨10, 10, 16, 8⟩, ⟨10, 14, 15, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 14, 13, 6⟩, ⟨10, 14, 12, 8⟩]
  exact AllWinning.cons node_23536 (AllWinning.cons node_23072 (AllWinning.cons node_22514 (AllWinning.cons node_21911 (AllWinning.cons node_23557 (AllWinning.cons node_23125 (AllWinning.cons node_22601 (AllWinning.cons node_22023 (AllWinning.cons node_23559 (AllWinning.cons node_23129 (AllWinning.cons node_22609 (AllWinning.cons node_22033 (AllWinning.nil))))))))))))

theorem node_23938 : Outcome ⟨10, 14, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 14, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨7, 14, 16, 6⟩, ⟨6, 14, 16, 8⟩, ⟨5, 14, 16, 10⟩, ⟨4, 14, 16, 12⟩, ⟨10, 13, 16, 2⟩, ⟨10, 12, 16, 4⟩, ⟨10, 11, 16, 6⟩, ⟨10, 10, 16, 8⟩, ⟨10, 9, 16, 10⟩, ⟨10, 8, 16, 12⟩, ⟨10, 14, 15, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 14, 13, 6⟩, ⟨10, 14, 12, 8⟩, ⟨10, 14, 11, 10⟩, ⟨10, 14, 10, 12⟩]
  exact AllWinning.cons node_23536 (AllWinning.cons node_23072 (AllWinning.cons node_22514 (AllWinning.cons node_21911 (AllWinning.cons node_21289 (AllWinning.cons node_20498 (AllWinning.cons node_23557 (AllWinning.cons node_23125 (AllWinning.cons node_22601 (AllWinning.cons node_22023 (AllWinning.cons node_21431 (AllWinning.cons node_20747 (AllWinning.cons node_23559 (AllWinning.cons node_23129 (AllWinning.cons node_22609 (AllWinning.cons node_22033 (AllWinning.cons node_21442 (AllWinning.cons node_20760 (AllWinning.nil))))))))))))))))))

theorem node_23939 : Outcome ⟨10, 14, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 14, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨7, 14, 16, 6⟩, ⟨6, 14, 16, 8⟩, ⟨5, 14, 16, 10⟩, ⟨4, 14, 16, 12⟩, ⟨3, 14, 16, 14⟩, ⟨2, 14, 16, 16⟩, ⟨10, 13, 16, 2⟩, ⟨10, 12, 16, 4⟩, ⟨10, 11, 16, 6⟩, ⟨10, 10, 16, 8⟩, ⟨10, 9, 16, 10⟩, ⟨10, 8, 16, 12⟩, ⟨10, 7, 16, 14⟩, ⟨10, 6, 16, 16⟩, ⟨10, 14, 15, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 14, 13, 6⟩, ⟨10, 14, 12, 8⟩, ⟨10, 14, 11, 10⟩, ⟨10, 14, 10, 12⟩, ⟨10, 14, 9, 14⟩, ⟨10, 14, 8, 16⟩]
  exact AllWinning.cons node_23536 (AllWinning.cons node_23072 (AllWinning.cons node_22514 (AllWinning.cons node_21911 (AllWinning.cons node_21289 (AllWinning.cons node_20498 (AllWinning.cons node_19774 (AllWinning.cons node_18882 (AllWinning.cons node_23557 (AllWinning.cons node_23125 (AllWinning.cons node_22601 (AllWinning.cons node_22023 (AllWinning.cons node_21431 (AllWinning.cons node_20747 (AllWinning.cons node_19998 (AllWinning.cons node_19212 (AllWinning.cons node_23559 (AllWinning.cons node_23129 (AllWinning.cons node_22609 (AllWinning.cons node_22033 (AllWinning.cons node_21442 (AllWinning.cons node_20760 (AllWinning.cons node_20021 (AllWinning.cons node_19236 (AllWinning.nil))))))))))))))))))))))))

theorem node_23940 : Outcome ⟨10, 14, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 14, 16, 2⟩, ⟨8, 14, 16, 4⟩, ⟨7, 14, 16, 6⟩, ⟨6, 14, 16, 8⟩, ⟨5, 14, 16, 10⟩, ⟨4, 14, 16, 12⟩, ⟨3, 14, 16, 14⟩, ⟨2, 14, 16, 16⟩, ⟨1, 14, 16, 18⟩, ⟨0, 14, 16, 20⟩, ⟨10, 13, 16, 2⟩, ⟨10, 12, 16, 4⟩, ⟨10, 11, 16, 6⟩, ⟨10, 10, 16, 8⟩, ⟨10, 9, 16, 10⟩, ⟨10, 8, 16, 12⟩, ⟨10, 7, 16, 14⟩, ⟨10, 6, 16, 16⟩, ⟨10, 5, 16, 18⟩, ⟨10, 4, 16, 20⟩, ⟨10, 14, 15, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 14, 13, 6⟩, ⟨10, 14, 12, 8⟩, ⟨10, 14, 11, 10⟩, ⟨10, 14, 10, 12⟩, ⟨10, 14, 9, 14⟩, ⟨10, 14, 8, 16⟩, ⟨10, 14, 7, 18⟩, ⟨10, 14, 6, 20⟩]
  exact AllWinning.cons node_23536 (AllWinning.cons node_23072 (AllWinning.cons node_22514 (AllWinning.cons node_21911 (AllWinning.cons node_21289 (AllWinning.cons node_20498 (AllWinning.cons node_19774 (AllWinning.cons node_18882 (AllWinning.cons node_17926 (AllWinning.cons node_16987 (AllWinning.cons node_23557 (AllWinning.cons node_23125 (AllWinning.cons node_22601 (AllWinning.cons node_22023 (AllWinning.cons node_21431 (AllWinning.cons node_20747 (AllWinning.cons node_19998 (AllWinning.cons node_19212 (AllWinning.cons node_18314 (AllWinning.cons node_17419 (AllWinning.cons node_23559 (AllWinning.cons node_23129 (AllWinning.cons node_22609 (AllWinning.cons node_22033 (AllWinning.cons node_21442 (AllWinning.cons node_20760 (AllWinning.cons node_20021 (AllWinning.cons node_19236 (AllWinning.cons node_18343 (AllWinning.cons node_17445 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_23941 : Outcome ⟨10, 15, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 15, 15, 2⟩, ⟨8, 15, 15, 4⟩, ⟨10, 14, 15, 2⟩, ⟨10, 13, 15, 4⟩, ⟨10, 15, 14, 2⟩, ⟨10, 15, 13, 4⟩]
  exact AllWinning.cons node_23538 (AllWinning.cons node_23073 (AllWinning.cons node_23559 (AllWinning.cons node_23127 (AllWinning.cons node_23561 (AllWinning.cons node_23131 (AllWinning.nil))))))

theorem node_23942 : Outcome ⟨10, 15, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 15, 15, 2⟩, ⟨8, 15, 15, 4⟩, ⟨7, 15, 15, 6⟩, ⟨6, 15, 15, 8⟩, ⟨10, 14, 15, 2⟩, ⟨10, 13, 15, 4⟩, ⟨10, 12, 15, 6⟩, ⟨10, 11, 15, 8⟩, ⟨10, 15, 14, 2⟩, ⟨10, 15, 13, 4⟩, ⟨10, 15, 12, 6⟩, ⟨10, 15, 11, 8⟩]
  exact AllWinning.cons node_23538 (AllWinning.cons node_23073 (AllWinning.cons node_22516 (AllWinning.cons node_21912 (AllWinning.cons node_23559 (AllWinning.cons node_23127 (AllWinning.cons node_22603 (AllWinning.cons node_22025 (AllWinning.cons node_23561 (AllWinning.cons node_23131 (AllWinning.cons node_22612 (AllWinning.cons node_22035 (AllWinning.nil))))))))))))

theorem node_23943 : Outcome ⟨10, 15, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 15, 15, 2⟩, ⟨8, 15, 15, 4⟩, ⟨7, 15, 15, 6⟩, ⟨6, 15, 15, 8⟩, ⟨5, 15, 15, 10⟩, ⟨4, 15, 15, 12⟩, ⟨10, 14, 15, 2⟩, ⟨10, 13, 15, 4⟩, ⟨10, 12, 15, 6⟩, ⟨10, 11, 15, 8⟩, ⟨10, 10, 15, 10⟩, ⟨10, 9, 15, 12⟩, ⟨10, 15, 14, 2⟩, ⟨10, 15, 13, 4⟩, ⟨10, 15, 12, 6⟩, ⟨10, 15, 11, 8⟩, ⟨10, 15, 10, 10⟩, ⟨10, 15, 9, 12⟩]
  exact AllWinning.cons node_23538 (AllWinning.cons node_23073 (AllWinning.cons node_22516 (AllWinning.cons node_21912 (AllWinning.cons node_21293 (AllWinning.cons node_20501 (AllWinning.cons node_23559 (AllWinning.cons node_23127 (AllWinning.cons node_22603 (AllWinning.cons node_22025 (AllWinning.cons node_21434 (AllWinning.cons node_20751 (AllWinning.cons node_23561 (AllWinning.cons node_23131 (AllWinning.cons node_22612 (AllWinning.cons node_22035 (AllWinning.cons node_21445 (AllWinning.cons node_20764 (AllWinning.nil))))))))))))))))))

theorem node_23944 : Outcome ⟨10, 15, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 15, 15, 2⟩, ⟨8, 15, 15, 4⟩, ⟨7, 15, 15, 6⟩, ⟨6, 15, 15, 8⟩, ⟨5, 15, 15, 10⟩, ⟨4, 15, 15, 12⟩, ⟨3, 15, 15, 14⟩, ⟨2, 15, 15, 16⟩, ⟨10, 14, 15, 2⟩, ⟨10, 13, 15, 4⟩, ⟨10, 12, 15, 6⟩, ⟨10, 11, 15, 8⟩, ⟨10, 10, 15, 10⟩, ⟨10, 9, 15, 12⟩, ⟨10, 8, 15, 14⟩, ⟨10, 7, 15, 16⟩, ⟨10, 15, 14, 2⟩, ⟨10, 15, 13, 4⟩, ⟨10, 15, 12, 6⟩, ⟨10, 15, 11, 8⟩, ⟨10, 15, 10, 10⟩, ⟨10, 15, 9, 12⟩, ⟨10, 15, 8, 14⟩, ⟨10, 15, 7, 16⟩]
  exact AllWinning.cons node_23538 (AllWinning.cons node_23073 (AllWinning.cons node_22516 (AllWinning.cons node_21912 (AllWinning.cons node_21293 (AllWinning.cons node_20501 (AllWinning.cons node_19778 (AllWinning.cons node_18886 (AllWinning.cons node_23559 (AllWinning.cons node_23127 (AllWinning.cons node_22603 (AllWinning.cons node_22025 (AllWinning.cons node_21434 (AllWinning.cons node_20751 (AllWinning.cons node_20001 (AllWinning.cons node_19215 (AllWinning.cons node_23561 (AllWinning.cons node_23131 (AllWinning.cons node_22612 (AllWinning.cons node_22035 (AllWinning.cons node_21445 (AllWinning.cons node_20764 (AllWinning.cons node_20024 (AllWinning.cons node_19239 (AllWinning.nil))))))))))))))))))))))))

theorem node_23945 : Outcome ⟨10, 16, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 16, 14, 2⟩, ⟨8, 16, 14, 4⟩, ⟨10, 15, 14, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 16, 13, 2⟩, ⟨10, 16, 12, 4⟩]
  exact AllWinning.cons node_23540 (AllWinning.cons node_23074 (AllWinning.cons node_23561 (AllWinning.cons node_23129 (AllWinning.cons node_23563 (AllWinning.cons node_23134 (AllWinning.nil))))))

theorem node_23946 : Outcome ⟨10, 16, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 16, 14, 2⟩, ⟨8, 16, 14, 4⟩, ⟨7, 16, 14, 6⟩, ⟨6, 16, 14, 8⟩, ⟨10, 15, 14, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 13, 14, 6⟩, ⟨10, 12, 14, 8⟩, ⟨10, 16, 13, 2⟩, ⟨10, 16, 12, 4⟩, ⟨10, 16, 11, 6⟩, ⟨10, 16, 10, 8⟩]
  exact AllWinning.cons node_23540 (AllWinning.cons node_23074 (AllWinning.cons node_22518 (AllWinning.cons node_21917 (AllWinning.cons node_23561 (AllWinning.cons node_23129 (AllWinning.cons node_22606 (AllWinning.cons node_22028 (AllWinning.cons node_23563 (AllWinning.cons node_23134 (AllWinning.cons node_22615 (AllWinning.cons node_22038 (AllWinning.nil))))))))))))

theorem node_23947 : Outcome ⟨10, 16, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 16, 14, 2⟩, ⟨8, 16, 14, 4⟩, ⟨7, 16, 14, 6⟩, ⟨6, 16, 14, 8⟩, ⟨5, 16, 14, 10⟩, ⟨4, 16, 14, 12⟩, ⟨10, 15, 14, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 13, 14, 6⟩, ⟨10, 12, 14, 8⟩, ⟨10, 11, 14, 10⟩, ⟨10, 10, 14, 12⟩, ⟨10, 16, 13, 2⟩, ⟨10, 16, 12, 4⟩, ⟨10, 16, 11, 6⟩, ⟨10, 16, 10, 8⟩, ⟨10, 16, 9, 10⟩, ⟨10, 16, 8, 12⟩]
  exact AllWinning.cons node_23540 (AllWinning.cons node_23074 (AllWinning.cons node_22518 (AllWinning.cons node_21917 (AllWinning.cons node_21295 (AllWinning.cons node_20505 (AllWinning.cons node_23561 (AllWinning.cons node_23129 (AllWinning.cons node_22606 (AllWinning.cons node_22028 (AllWinning.cons node_21437 (AllWinning.cons node_20753 (AllWinning.cons node_23563 (AllWinning.cons node_23134 (AllWinning.cons node_22615 (AllWinning.cons node_22038 (AllWinning.cons node_21447 (AllWinning.cons node_20766 (AllWinning.nil))))))))))))))))))

theorem node_23948 : Outcome ⟨10, 16, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 16, 14, 2⟩, ⟨8, 16, 14, 4⟩, ⟨7, 16, 14, 6⟩, ⟨6, 16, 14, 8⟩, ⟨5, 16, 14, 10⟩, ⟨4, 16, 14, 12⟩, ⟨3, 16, 14, 14⟩, ⟨2, 16, 14, 16⟩, ⟨10, 15, 14, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 13, 14, 6⟩, ⟨10, 12, 14, 8⟩, ⟨10, 11, 14, 10⟩, ⟨10, 10, 14, 12⟩, ⟨10, 9, 14, 14⟩, ⟨10, 8, 14, 16⟩, ⟨10, 16, 13, 2⟩, ⟨10, 16, 12, 4⟩, ⟨10, 16, 11, 6⟩, ⟨10, 16, 10, 8⟩, ⟨10, 16, 9, 10⟩, ⟨10, 16, 8, 12⟩, ⟨10, 16, 7, 14⟩, ⟨10, 16, 6, 16⟩]
  exact AllWinning.cons node_23540 (AllWinning.cons node_23074 (AllWinning.cons node_22518 (AllWinning.cons node_21917 (AllWinning.cons node_21295 (AllWinning.cons node_20505 (AllWinning.cons node_19780 (AllWinning.cons node_18890 (AllWinning.cons node_23561 (AllWinning.cons node_23129 (AllWinning.cons node_22606 (AllWinning.cons node_22028 (AllWinning.cons node_21437 (AllWinning.cons node_20753 (AllWinning.cons node_20005 (AllWinning.cons node_19219 (AllWinning.cons node_23563 (AllWinning.cons node_23134 (AllWinning.cons node_22615 (AllWinning.cons node_22038 (AllWinning.cons node_21447 (AllWinning.cons node_20766 (AllWinning.cons node_20027 (AllWinning.cons node_19242 (AllWinning.nil))))))))))))))))))))))))

end RQ9F1
