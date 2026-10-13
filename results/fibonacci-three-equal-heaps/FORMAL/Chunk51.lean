import Chunk50
set_option autoImplicit false
namespace RQ9F1

theorem node_12006 : Outcome ⟨0, 19, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 6, 2⟩, ⟨0, 17, 6, 4⟩, ⟨0, 16, 6, 6⟩, ⟨0, 15, 6, 8⟩, ⟨0, 14, 6, 10⟩, ⟨0, 13, 6, 12⟩, ⟨0, 12, 6, 14⟩, ⟨0, 11, 6, 16⟩, ⟨0, 19, 5, 2⟩, ⟨0, 19, 4, 4⟩, ⟨0, 19, 3, 6⟩, ⟨0, 19, 2, 8⟩, ⟨0, 19, 1, 10⟩, ⟨0, 19, 0, 12⟩]
  exact AllWinning.cons node_11024 (AllWinning.cons node_9918 (AllWinning.cons node_8964 (AllWinning.cons node_7958 (AllWinning.cons node_7004 (AllWinning.cons node_6091 (AllWinning.cons node_5365 (AllWinning.cons node_4619 (AllWinning.cons node_11028 (AllWinning.cons node_9929 (AllWinning.cons node_8975 (AllWinning.cons node_7974 (AllWinning.cons node_7024 (AllWinning.cons node_6114 (AllWinning.nil))))))))))))))

theorem node_12007 : Outcome ⟨0, 19, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 6, 2⟩, ⟨0, 17, 6, 4⟩, ⟨0, 16, 6, 6⟩, ⟨0, 15, 6, 8⟩, ⟨0, 14, 6, 10⟩, ⟨0, 13, 6, 12⟩, ⟨0, 12, 6, 14⟩, ⟨0, 11, 6, 16⟩, ⟨0, 10, 6, 18⟩, ⟨0, 9, 6, 20⟩, ⟨0, 19, 5, 2⟩, ⟨0, 19, 4, 4⟩, ⟨0, 19, 3, 6⟩, ⟨0, 19, 2, 8⟩, ⟨0, 19, 1, 10⟩, ⟨0, 19, 0, 12⟩]
  exact AllWinning.cons node_11024 (AllWinning.cons node_9918 (AllWinning.cons node_8964 (AllWinning.cons node_7958 (AllWinning.cons node_7004 (AllWinning.cons node_6091 (AllWinning.cons node_5365 (AllWinning.cons node_4619 (AllWinning.cons node_3976 (AllWinning.cons node_3357 (AllWinning.cons node_11028 (AllWinning.cons node_9929 (AllWinning.cons node_8975 (AllWinning.cons node_7974 (AllWinning.cons node_7024 (AllWinning.cons node_6114 (AllWinning.nil))))))))))))))))

theorem node_12008 : Outcome ⟨0, 19, 6, 14⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 26⟩) (by decide) node_1901

theorem node_12009 : Outcome ⟨0, 20, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 4⟩) (by decide) node_9922

theorem node_12010 : Outcome ⟨0, 20, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 4⟩) (by decide) node_9922

theorem node_12011 : Outcome ⟨1, 4, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 20, 2⟩, ⟨1, 3, 20, 2⟩, ⟨1, 2, 20, 4⟩, ⟨1, 4, 19, 2⟩, ⟨1, 4, 18, 4⟩]
  exact AllWinning.cons node_10974 (AllWinning.cons node_11033 (AllWinning.cons node_9933 (AllWinning.cons node_11034 (AllWinning.cons node_9942 (AllWinning.nil)))))

theorem node_12012 : Outcome ⟨1, 4, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 20, 2⟩, ⟨1, 3, 20, 2⟩, ⟨1, 2, 20, 4⟩, ⟨1, 1, 20, 6⟩, ⟨1, 0, 20, 8⟩, ⟨1, 4, 19, 2⟩, ⟨1, 4, 18, 4⟩, ⟨1, 4, 17, 6⟩, ⟨1, 4, 16, 8⟩]
  exact AllWinning.cons node_10974 (AllWinning.cons node_11033 (AllWinning.cons node_9933 (AllWinning.cons node_8980 (AllWinning.cons node_7979 (AllWinning.cons node_11034 (AllWinning.cons node_9942 (AllWinning.cons node_8990 (AllWinning.cons node_7990 (AllWinning.nil)))))))))

theorem node_12013 : Outcome ⟨1, 4, 20, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 10⟩) (by decide) node_7049

theorem node_12014 : Outcome ⟨1, 5, 19, 4⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 4⟩) (by decide) node_9935

theorem node_12015 : Outcome ⟨1, 5, 19, 8⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 4⟩) (by decide) node_9935

theorem node_12016 : Outcome ⟨1, 5, 19, 14⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 20⟩) (by decide) node_3421

theorem node_12017 : Outcome ⟨1, 5, 19, 18⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 20⟩) (by decide) node_3421

theorem node_12018 : Outcome ⟨1, 6, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 4⟩) (by decide) node_9952

theorem node_12019 : Outcome ⟨1, 6, 18, 18⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 30⟩) (by decide) node_1261

theorem node_12020 : Outcome ⟨1, 7, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 17, 2⟩, ⟨1, 6, 17, 2⟩, ⟨1, 5, 17, 4⟩, ⟨1, 7, 16, 2⟩, ⟨1, 7, 15, 4⟩]
  exact AllWinning.cons node_10983 (AllWinning.cons node_11040 (AllWinning.cons node_9947 (AllWinning.cons node_11043 (AllWinning.cons node_9960 (AllWinning.nil)))))

theorem node_12021 : Outcome ⟨1, 7, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 17, 2⟩, ⟨1, 6, 17, 2⟩, ⟨1, 5, 17, 4⟩, ⟨1, 4, 17, 6⟩, ⟨1, 3, 17, 8⟩, ⟨1, 7, 16, 2⟩, ⟨1, 7, 15, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 7, 13, 8⟩]
  exact AllWinning.cons node_10983 (AllWinning.cons node_11040 (AllWinning.cons node_9947 (AllWinning.cons node_8990 (AllWinning.cons node_7986 (AllWinning.cons node_11043 (AllWinning.cons node_9960 (AllWinning.cons node_9002 (AllWinning.cons node_8002 (AllWinning.nil)))))))))

theorem node_12022 : Outcome ⟨1, 7, 17, 8⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 12⟩) (by decide) node_6142

theorem node_12023 : Outcome ⟨1, 7, 17, 12⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 12⟩) (by decide) node_6142

theorem node_12024 : Outcome ⟨1, 8, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 4⟩) (by decide) node_9952

theorem node_12025 : Outcome ⟨1, 8, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 8⟩) (by decide) node_8008

theorem node_12026 : Outcome ⟨1, 8, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 8⟩) (by decide) node_8008

theorem node_12027 : Outcome ⟨1, 8, 16, 14⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 8⟩) (by decide) node_8008

theorem node_12028 : Outcome ⟨1, 9, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 4⟩) (by decide) node_9968

theorem node_12029 : Outcome ⟨1, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 4⟩) (by decide) node_9968

theorem node_12030 : Outcome ⟨1, 9, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 10⟩) (by decide) node_7049

theorem node_12031 : Outcome ⟨1, 9, 15, 14⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 20⟩) (by decide) node_3445

theorem node_12032 : Outcome ⟨1, 10, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.nil)))))

theorem node_12033 : Outcome ⟨1, 10, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.nil)))))))))

theorem node_12034 : Outcome ⟨1, 10, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.nil)))))))))))))

theorem node_12035 : Outcome ⟨1, 10, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 3, 14, 14⟩, ⟨1, 2, 14, 16⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩, ⟨1, 10, 7, 14⟩, ⟨1, 10, 6, 16⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_5403 (AllWinning.cons node_4658 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.cons node_5428 (AllWinning.cons node_4692 (AllWinning.nil)))))))))))))))))

theorem node_12036 : Outcome ⟨1, 10, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 3, 14, 14⟩, ⟨1, 2, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨1, 0, 14, 20⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩, ⟨1, 10, 7, 14⟩, ⟨1, 10, 6, 16⟩, ⟨1, 10, 5, 18⟩, ⟨1, 10, 4, 20⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_5403 (AllWinning.cons node_4658 (AllWinning.cons node_4006 (AllWinning.cons node_3390 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.cons node_5428 (AllWinning.cons node_4692 (AllWinning.cons node_4036 (AllWinning.cons node_3454 (AllWinning.nil)))))))))))))))))))))

theorem node_12037 : Outcome ⟨1, 10, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 3, 14, 14⟩, ⟨1, 2, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨1, 0, 14, 20⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩, ⟨1, 10, 7, 14⟩, ⟨1, 10, 6, 16⟩, ⟨1, 10, 5, 18⟩, ⟨1, 10, 4, 20⟩, ⟨1, 10, 3, 22⟩, ⟨1, 10, 2, 24⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_5403 (AllWinning.cons node_4658 (AllWinning.cons node_4006 (AllWinning.cons node_3390 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.cons node_5428 (AllWinning.cons node_4692 (AllWinning.cons node_4036 (AllWinning.cons node_3454 (AllWinning.cons node_2928 (AllWinning.cons node_2472 (AllWinning.nil)))))))))))))))))))))))

theorem node_12038 : Outcome ⟨1, 10, 14, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 3, 14, 14⟩, ⟨1, 2, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨1, 0, 14, 20⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩, ⟨1, 10, 7, 14⟩, ⟨1, 10, 6, 16⟩, ⟨1, 10, 5, 18⟩, ⟨1, 10, 4, 20⟩, ⟨1, 10, 3, 22⟩, ⟨1, 10, 2, 24⟩, ⟨1, 10, 1, 26⟩, ⟨1, 10, 0, 28⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_5403 (AllWinning.cons node_4658 (AllWinning.cons node_4006 (AllWinning.cons node_3390 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.cons node_5428 (AllWinning.cons node_4692 (AllWinning.cons node_4036 (AllWinning.cons node_3454 (AllWinning.cons node_2928 (AllWinning.cons node_2472 (AllWinning.cons node_1976 (AllWinning.cons node_1633 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12039 : Outcome ⟨1, 10, 14, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 3, 14, 14⟩, ⟨1, 2, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨1, 0, 14, 20⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩, ⟨1, 10, 7, 14⟩, ⟨1, 10, 6, 16⟩, ⟨1, 10, 5, 18⟩, ⟨1, 10, 4, 20⟩, ⟨1, 10, 3, 22⟩, ⟨1, 10, 2, 24⟩, ⟨1, 10, 1, 26⟩, ⟨1, 10, 0, 28⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_5403 (AllWinning.cons node_4658 (AllWinning.cons node_4006 (AllWinning.cons node_3390 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.cons node_5428 (AllWinning.cons node_4692 (AllWinning.cons node_4036 (AllWinning.cons node_3454 (AllWinning.cons node_2928 (AllWinning.cons node_2472 (AllWinning.cons node_1976 (AllWinning.cons node_1633 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12040 : Outcome ⟨1, 10, 14, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 3, 14, 14⟩, ⟨1, 2, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨1, 0, 14, 20⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩, ⟨1, 10, 7, 14⟩, ⟨1, 10, 6, 16⟩, ⟨1, 10, 5, 18⟩, ⟨1, 10, 4, 20⟩, ⟨1, 10, 3, 22⟩, ⟨1, 10, 2, 24⟩, ⟨1, 10, 1, 26⟩, ⟨1, 10, 0, 28⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_5403 (AllWinning.cons node_4658 (AllWinning.cons node_4006 (AllWinning.cons node_3390 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.cons node_5428 (AllWinning.cons node_4692 (AllWinning.cons node_4036 (AllWinning.cons node_3454 (AllWinning.cons node_2928 (AllWinning.cons node_2472 (AllWinning.cons node_1976 (AllWinning.cons node_1633 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12041 : Outcome ⟨1, 10, 14, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 14, 2⟩, ⟨1, 9, 14, 2⟩, ⟨1, 8, 14, 4⟩, ⟨1, 7, 14, 6⟩, ⟨1, 6, 14, 8⟩, ⟨1, 5, 14, 10⟩, ⟨1, 4, 14, 12⟩, ⟨1, 3, 14, 14⟩, ⟨1, 2, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨1, 0, 14, 20⟩, ⟨1, 10, 13, 2⟩, ⟨1, 10, 12, 4⟩, ⟨1, 10, 11, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 10, 9, 10⟩, ⟨1, 10, 8, 12⟩, ⟨1, 10, 7, 14⟩, ⟨1, 10, 6, 16⟩, ⟨1, 10, 5, 18⟩, ⟨1, 10, 4, 20⟩, ⟨1, 10, 3, 22⟩, ⟨1, 10, 2, 24⟩, ⟨1, 10, 1, 26⟩, ⟨1, 10, 0, 28⟩]
  exact AllWinning.cons node_10995 (AllWinning.cons node_11051 (AllWinning.cons node_9965 (AllWinning.cons node_9002 (AllWinning.cons node_7999 (AllWinning.cons node_7054 (AllWinning.cons node_6128 (AllWinning.cons node_5403 (AllWinning.cons node_4658 (AllWinning.cons node_4006 (AllWinning.cons node_3390 (AllWinning.cons node_11054 (AllWinning.cons node_9973 (AllWinning.cons node_9010 (AllWinning.cons node_8021 (AllWinning.cons node_7073 (AllWinning.cons node_6160 (AllWinning.cons node_5428 (AllWinning.cons node_4692 (AllWinning.cons node_4036 (AllWinning.cons node_3454 (AllWinning.cons node_2928 (AllWinning.cons node_2472 (AllWinning.cons node_1976 (AllWinning.cons node_1633 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12042 : Outcome ⟨1, 11, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 4⟩) (by decide) node_9968

theorem node_12043 : Outcome ⟨1, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 4⟩) (by decide) node_9968

theorem node_12044 : Outcome ⟨1, 11, 13, 12⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 12⟩) (by decide) node_6167

theorem node_12045 : Outcome ⟨1, 12, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 2⟩) (by decide) node_10999

theorem node_12046 : Outcome ⟨1, 12, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 8⟩) (by decide) node_8008

theorem node_12047 : Outcome ⟨1, 12, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 8⟩) (by decide) node_8008

theorem node_12048 : Outcome ⟨1, 12, 12, 14⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 8⟩) (by decide) node_8008

theorem node_12049 : Outcome ⟨1, 13, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 4⟩) (by decide) node_9985

theorem node_12050 : Outcome ⟨1, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 4⟩) (by decide) node_9985

theorem node_12051 : Outcome ⟨1, 13, 11, 12⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 12⟩) (by decide) node_6142

theorem node_12052 : Outcome ⟨1, 14, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.nil)))))

theorem node_12053 : Outcome ⟨1, 14, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.nil)))))))))

theorem node_12054 : Outcome ⟨1, 14, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.nil)))))))))))))

theorem node_12055 : Outcome ⟨1, 14, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 7, 10, 14⟩, ⟨1, 6, 10, 16⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩, ⟨1, 14, 3, 14⟩, ⟨1, 14, 2, 16⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_5417 (AllWinning.cons node_4676 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.cons node_5444 (AllWinning.cons node_4709 (AllWinning.nil)))))))))))))))))

theorem node_12056 : Outcome ⟨1, 14, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 7, 10, 14⟩, ⟨1, 6, 10, 16⟩, ⟨1, 5, 10, 18⟩, ⟨1, 4, 10, 20⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩, ⟨1, 14, 3, 14⟩, ⟨1, 14, 2, 16⟩, ⟨1, 14, 1, 18⟩, ⟨1, 14, 0, 20⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_5417 (AllWinning.cons node_4676 (AllWinning.cons node_4018 (AllWinning.cons node_3411 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.cons node_5444 (AllWinning.cons node_4709 (AllWinning.cons node_4049 (AllWinning.cons node_3476 (AllWinning.nil)))))))))))))))))))))

theorem node_12057 : Outcome ⟨1, 14, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 7, 10, 14⟩, ⟨1, 6, 10, 16⟩, ⟨1, 5, 10, 18⟩, ⟨1, 4, 10, 20⟩, ⟨1, 3, 10, 22⟩, ⟨1, 2, 10, 24⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩, ⟨1, 14, 3, 14⟩, ⟨1, 14, 2, 16⟩, ⟨1, 14, 1, 18⟩, ⟨1, 14, 0, 20⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_5417 (AllWinning.cons node_4676 (AllWinning.cons node_4018 (AllWinning.cons node_3411 (AllWinning.cons node_2901 (AllWinning.cons node_2441 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.cons node_5444 (AllWinning.cons node_4709 (AllWinning.cons node_4049 (AllWinning.cons node_3476 (AllWinning.nil)))))))))))))))))))))))

theorem node_12058 : Outcome ⟨1, 14, 10, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 7, 10, 14⟩, ⟨1, 6, 10, 16⟩, ⟨1, 5, 10, 18⟩, ⟨1, 4, 10, 20⟩, ⟨1, 3, 10, 22⟩, ⟨1, 2, 10, 24⟩, ⟨1, 1, 10, 26⟩, ⟨1, 0, 10, 28⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩, ⟨1, 14, 3, 14⟩, ⟨1, 14, 2, 16⟩, ⟨1, 14, 1, 18⟩, ⟨1, 14, 0, 20⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_5417 (AllWinning.cons node_4676 (AllWinning.cons node_4018 (AllWinning.cons node_3411 (AllWinning.cons node_2901 (AllWinning.cons node_2441 (AllWinning.cons node_1935 (AllWinning.cons node_1599 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.cons node_5444 (AllWinning.cons node_4709 (AllWinning.cons node_4049 (AllWinning.cons node_3476 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12059 : Outcome ⟨1, 14, 10, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 7, 10, 14⟩, ⟨1, 6, 10, 16⟩, ⟨1, 5, 10, 18⟩, ⟨1, 4, 10, 20⟩, ⟨1, 3, 10, 22⟩, ⟨1, 2, 10, 24⟩, ⟨1, 1, 10, 26⟩, ⟨1, 0, 10, 28⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩, ⟨1, 14, 3, 14⟩, ⟨1, 14, 2, 16⟩, ⟨1, 14, 1, 18⟩, ⟨1, 14, 0, 20⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_5417 (AllWinning.cons node_4676 (AllWinning.cons node_4018 (AllWinning.cons node_3411 (AllWinning.cons node_2901 (AllWinning.cons node_2441 (AllWinning.cons node_1935 (AllWinning.cons node_1599 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.cons node_5444 (AllWinning.cons node_4709 (AllWinning.cons node_4049 (AllWinning.cons node_3476 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12060 : Outcome ⟨1, 14, 10, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 7, 10, 14⟩, ⟨1, 6, 10, 16⟩, ⟨1, 5, 10, 18⟩, ⟨1, 4, 10, 20⟩, ⟨1, 3, 10, 22⟩, ⟨1, 2, 10, 24⟩, ⟨1, 1, 10, 26⟩, ⟨1, 0, 10, 28⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩, ⟨1, 14, 3, 14⟩, ⟨1, 14, 2, 16⟩, ⟨1, 14, 1, 18⟩, ⟨1, 14, 0, 20⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_5417 (AllWinning.cons node_4676 (AllWinning.cons node_4018 (AllWinning.cons node_3411 (AllWinning.cons node_2901 (AllWinning.cons node_2441 (AllWinning.cons node_1935 (AllWinning.cons node_1599 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.cons node_5444 (AllWinning.cons node_4709 (AllWinning.cons node_4049 (AllWinning.cons node_3476 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12061 : Outcome ⟨1, 14, 10, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 10, 2⟩, ⟨1, 13, 10, 2⟩, ⟨1, 12, 10, 4⟩, ⟨1, 11, 10, 6⟩, ⟨1, 10, 10, 8⟩, ⟨1, 9, 10, 10⟩, ⟨1, 8, 10, 12⟩, ⟨1, 7, 10, 14⟩, ⟨1, 6, 10, 16⟩, ⟨1, 5, 10, 18⟩, ⟨1, 4, 10, 20⟩, ⟨1, 3, 10, 22⟩, ⟨1, 2, 10, 24⟩, ⟨1, 1, 10, 26⟩, ⟨1, 0, 10, 28⟩, ⟨1, 14, 9, 2⟩, ⟨1, 14, 8, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 14, 6, 8⟩, ⟨1, 14, 5, 10⟩, ⟨1, 14, 4, 12⟩, ⟨1, 14, 3, 14⟩, ⟨1, 14, 2, 16⟩, ⟨1, 14, 1, 18⟩, ⟨1, 14, 0, 20⟩]
  exact AllWinning.cons node_11010 (AllWinning.cons node_11065 (AllWinning.cons node_9981 (AllWinning.cons node_9014 (AllWinning.cons node_8021 (AllWinning.cons node_7069 (AllWinning.cons node_6152 (AllWinning.cons node_5417 (AllWinning.cons node_4676 (AllWinning.cons node_4018 (AllWinning.cons node_3411 (AllWinning.cons node_2901 (AllWinning.cons node_2441 (AllWinning.cons node_1935 (AllWinning.cons node_1599 (AllWinning.cons node_11068 (AllWinning.cons node_9990 (AllWinning.cons node_9023 (AllWinning.cons node_8043 (AllWinning.cons node_7085 (AllWinning.cons node_6182 (AllWinning.cons node_5444 (AllWinning.cons node_4709 (AllWinning.cons node_4049 (AllWinning.cons node_3476 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12062 : Outcome ⟨1, 15, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 4⟩) (by decide) node_9985

theorem node_12063 : Outcome ⟨1, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 4⟩) (by decide) node_9985

theorem node_12064 : Outcome ⟨1, 15, 9, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 10⟩) (by decide) node_7091

theorem node_12065 : Outcome ⟨1, 15, 9, 14⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 20⟩) (by decide) node_3421

theorem node_12066 : Outcome ⟨1, 16, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 4⟩) (by decide) node_9998

theorem node_12067 : Outcome ⟨1, 16, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 8⟩) (by decide) node_8029

theorem node_12068 : Outcome ⟨1, 16, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 8⟩) (by decide) node_8029

theorem node_12069 : Outcome ⟨1, 16, 8, 14⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 8⟩) (by decide) node_8029

theorem node_12070 : Outcome ⟨1, 17, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 7, 2⟩, ⟨1, 16, 7, 2⟩, ⟨1, 15, 7, 4⟩, ⟨1, 17, 6, 2⟩, ⟨1, 17, 5, 4⟩]
  exact AllWinning.cons node_11019 (AllWinning.cons node_11075 (AllWinning.cons node_9993 (AllWinning.cons node_11079 (AllWinning.cons node_10005 (AllWinning.nil)))))

theorem node_12071 : Outcome ⟨1, 17, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 7, 2⟩, ⟨1, 16, 7, 2⟩, ⟨1, 15, 7, 4⟩, ⟨1, 14, 7, 6⟩, ⟨1, 13, 7, 8⟩, ⟨1, 17, 6, 2⟩, ⟨1, 17, 5, 4⟩, ⟨1, 17, 4, 6⟩, ⟨1, 17, 3, 8⟩]
  exact AllWinning.cons node_11019 (AllWinning.cons node_11075 (AllWinning.cons node_9993 (AllWinning.cons node_9023 (AllWinning.cons node_8039 (AllWinning.cons node_11079 (AllWinning.cons node_10005 (AllWinning.cons node_9034 (AllWinning.cons node_8054 (AllWinning.nil)))))))))

theorem node_12072 : Outcome ⟨1, 17, 7, 8⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 12⟩) (by decide) node_6167

theorem node_12073 : Outcome ⟨1, 17, 7, 12⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 12⟩) (by decide) node_6167

theorem node_12074 : Outcome ⟨1, 18, 6, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 4⟩) (by decide) node_9998

theorem node_12075 : Outcome ⟨1, 18, 6, 18⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 30⟩) (by decide) node_1233

theorem node_12076 : Outcome ⟨1, 19, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 4⟩) (by decide) node_10015

theorem node_12077 : Outcome ⟨1, 19, 5, 8⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 4⟩) (by decide) node_10015

theorem node_12078 : Outcome ⟨1, 19, 5, 14⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 20⟩) (by decide) node_3445

theorem node_12079 : Outcome ⟨1, 19, 5, 18⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 20⟩) (by decide) node_3445

theorem node_12080 : Outcome ⟨1, 20, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 20, 4, 2⟩, ⟨1, 19, 4, 2⟩, ⟨1, 18, 4, 4⟩, ⟨1, 20, 3, 2⟩, ⟨1, 20, 2, 4⟩]
  exact AllWinning.cons node_11030 (AllWinning.cons node_11085 (AllWinning.cons node_10010 (AllWinning.cons node_11088 (AllWinning.cons node_10022 (AllWinning.nil)))))

theorem node_12081 : Outcome ⟨1, 20, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 20, 4, 2⟩, ⟨1, 19, 4, 2⟩, ⟨1, 18, 4, 4⟩, ⟨1, 17, 4, 6⟩, ⟨1, 16, 4, 8⟩, ⟨1, 20, 3, 2⟩, ⟨1, 20, 2, 4⟩, ⟨1, 20, 1, 6⟩, ⟨1, 20, 0, 8⟩]
  exact AllWinning.cons node_11030 (AllWinning.cons node_11085 (AllWinning.cons node_10010 (AllWinning.cons node_9034 (AllWinning.cons node_8050 (AllWinning.cons node_11088 (AllWinning.cons node_10022 (AllWinning.cons node_9045 (AllWinning.cons node_8063 (AllWinning.nil)))))))))

theorem node_12082 : Outcome ⟨1, 20, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 10⟩) (by decide) node_7091

theorem node_12083 : Outcome ⟨2, 3, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 3, 20, 2⟩, ⟨0, 3, 20, 4⟩, ⟨2, 2, 20, 2⟩, ⟨2, 1, 20, 4⟩, ⟨2, 0, 20, 6⟩, ⟨2, 3, 19, 2⟩, ⟨2, 3, 18, 4⟩, ⟨2, 3, 17, 6⟩, ⟨2, 3, 16, 8⟩]
  exact AllWinning.cons node_11033 (AllWinning.cons node_9871 (AllWinning.cons node_11089 (AllWinning.cons node_10023 (AllWinning.cons node_9047 (AllWinning.cons node_11090 (AllWinning.cons node_10027 (AllWinning.cons node_9057 (AllWinning.cons node_8077 (AllWinning.nil)))))))))

theorem node_12084 : Outcome ⟨2, 3, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 3, 20, 2⟩, ⟨0, 3, 20, 4⟩, ⟨2, 2, 20, 2⟩, ⟨2, 1, 20, 4⟩, ⟨2, 0, 20, 6⟩, ⟨2, 3, 19, 2⟩, ⟨2, 3, 18, 4⟩, ⟨2, 3, 17, 6⟩, ⟨2, 3, 16, 8⟩, ⟨2, 3, 15, 10⟩, ⟨2, 3, 14, 12⟩]
  exact AllWinning.cons node_11033 (AllWinning.cons node_9871 (AllWinning.cons node_11089 (AllWinning.cons node_10023 (AllWinning.cons node_9047 (AllWinning.cons node_11090 (AllWinning.cons node_10027 (AllWinning.cons node_9057 (AllWinning.cons node_8077 (AllWinning.cons node_7127 (AllWinning.cons node_6208 (AllWinning.nil)))))))))))

theorem node_12085 : Outcome ⟨2, 3, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 3, 20, 2⟩, ⟨0, 3, 20, 4⟩, ⟨2, 2, 20, 2⟩, ⟨2, 1, 20, 4⟩, ⟨2, 0, 20, 6⟩, ⟨2, 3, 19, 2⟩, ⟨2, 3, 18, 4⟩, ⟨2, 3, 17, 6⟩, ⟨2, 3, 16, 8⟩, ⟨2, 3, 15, 10⟩, ⟨2, 3, 14, 12⟩, ⟨2, 3, 13, 14⟩, ⟨2, 3, 12, 16⟩]
  exact AllWinning.cons node_11033 (AllWinning.cons node_9871 (AllWinning.cons node_11089 (AllWinning.cons node_10023 (AllWinning.cons node_9047 (AllWinning.cons node_11090 (AllWinning.cons node_10027 (AllWinning.cons node_9057 (AllWinning.cons node_8077 (AllWinning.cons node_7127 (AllWinning.cons node_6208 (AllWinning.cons node_5468 (AllWinning.cons node_4739 (AllWinning.nil)))))))))))))

theorem node_12086 : Outcome ⟨2, 3, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 3, 20, 2⟩, ⟨0, 3, 20, 4⟩, ⟨2, 2, 20, 2⟩, ⟨2, 1, 20, 4⟩, ⟨2, 0, 20, 6⟩, ⟨2, 3, 19, 2⟩, ⟨2, 3, 18, 4⟩, ⟨2, 3, 17, 6⟩, ⟨2, 3, 16, 8⟩, ⟨2, 3, 15, 10⟩, ⟨2, 3, 14, 12⟩, ⟨2, 3, 13, 14⟩, ⟨2, 3, 12, 16⟩, ⟨2, 3, 11, 18⟩, ⟨2, 3, 10, 20⟩]
  exact AllWinning.cons node_11033 (AllWinning.cons node_9871 (AllWinning.cons node_11089 (AllWinning.cons node_10023 (AllWinning.cons node_9047 (AllWinning.cons node_11090 (AllWinning.cons node_10027 (AllWinning.cons node_9057 (AllWinning.cons node_8077 (AllWinning.cons node_7127 (AllWinning.cons node_6208 (AllWinning.cons node_5468 (AllWinning.cons node_4739 (AllWinning.cons node_4063 (AllWinning.cons node_3491 (AllWinning.nil)))))))))))))))

theorem node_12087 : Outcome ⟨2, 3, 20, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 3, 20, 2⟩, ⟨0, 3, 20, 4⟩, ⟨2, 2, 20, 2⟩, ⟨2, 1, 20, 4⟩, ⟨2, 0, 20, 6⟩, ⟨2, 3, 19, 2⟩, ⟨2, 3, 18, 4⟩, ⟨2, 3, 17, 6⟩, ⟨2, 3, 16, 8⟩, ⟨2, 3, 15, 10⟩, ⟨2, 3, 14, 12⟩, ⟨2, 3, 13, 14⟩, ⟨2, 3, 12, 16⟩, ⟨2, 3, 11, 18⟩, ⟨2, 3, 10, 20⟩, ⟨2, 3, 9, 22⟩, ⟨2, 3, 8, 24⟩]
  exact AllWinning.cons node_11033 (AllWinning.cons node_9871 (AllWinning.cons node_11089 (AllWinning.cons node_10023 (AllWinning.cons node_9047 (AllWinning.cons node_11090 (AllWinning.cons node_10027 (AllWinning.cons node_9057 (AllWinning.cons node_8077 (AllWinning.cons node_7127 (AllWinning.cons node_6208 (AllWinning.cons node_5468 (AllWinning.cons node_4739 (AllWinning.cons node_4063 (AllWinning.cons node_3491 (AllWinning.cons node_2952 (AllWinning.cons node_2493 (AllWinning.nil)))))))))))))))))

theorem node_12088 : Outcome ⟨2, 4, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 19, 2⟩, ⟨0, 4, 19, 4⟩, ⟨2, 3, 19, 2⟩, ⟨2, 2, 19, 4⟩, ⟨2, 4, 18, 2⟩, ⟨2, 4, 17, 4⟩]
  exact AllWinning.cons node_11034 (AllWinning.cons node_9873 (AllWinning.cons node_11090 (AllWinning.cons node_10024 (AllWinning.cons node_11093 (AllWinning.cons node_10031 (AllWinning.nil))))))

theorem node_12089 : Outcome ⟨2, 4, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 19, 2⟩, ⟨0, 4, 19, 4⟩, ⟨2, 3, 19, 2⟩, ⟨2, 2, 19, 4⟩, ⟨2, 1, 19, 6⟩, ⟨2, 0, 19, 8⟩, ⟨2, 4, 18, 2⟩, ⟨2, 4, 17, 4⟩, ⟨2, 4, 16, 6⟩, ⟨2, 4, 15, 8⟩]
  exact AllWinning.cons node_11034 (AllWinning.cons node_9873 (AllWinning.cons node_11090 (AllWinning.cons node_10024 (AllWinning.cons node_9050 (AllWinning.cons node_8066 (AllWinning.cons node_11093 (AllWinning.cons node_10031 (AllWinning.cons node_9061 (AllWinning.cons node_8082 (AllWinning.nil))))))))))

theorem node_12090 : Outcome ⟨2, 4, 19, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 10⟩) (by decide) node_7133

theorem node_12091 : Outcome ⟨2, 4, 19, 24⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 36⟩) (by decide) node_593

theorem node_12092 : Outcome ⟨2, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 4⟩) (by decide) node_9876

theorem node_12093 : Outcome ⟨2, 5, 18, 6⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 4⟩) (by decide) node_9876

theorem node_12094 : Outcome ⟨2, 5, 18, 20⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 16⟩) (by decide) node_4750

theorem node_12095 : Outcome ⟨2, 5, 18, 22⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 16⟩) (by decide) node_4750

theorem node_12096 : Outcome ⟨2, 6, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 6, 17, 2⟩, ⟨0, 6, 17, 4⟩, ⟨2, 5, 17, 2⟩, ⟨2, 4, 17, 4⟩, ⟨2, 6, 16, 2⟩, ⟨2, 6, 15, 4⟩]
  exact AllWinning.cons node_11040 (AllWinning.cons node_9883 (AllWinning.cons node_11098 (AllWinning.cons node_10031 (AllWinning.cons node_11102 (AllWinning.cons node_10038 (AllWinning.nil))))))

theorem node_12097 : Outcome ⟨2, 6, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 6, 17, 2⟩, ⟨0, 6, 17, 4⟩, ⟨2, 5, 17, 2⟩, ⟨2, 4, 17, 4⟩, ⟨2, 3, 17, 6⟩, ⟨2, 2, 17, 8⟩, ⟨2, 6, 16, 2⟩, ⟨2, 6, 15, 4⟩, ⟨2, 6, 14, 6⟩, ⟨2, 6, 13, 8⟩]
  exact AllWinning.cons node_11040 (AllWinning.cons node_9883 (AllWinning.cons node_11098 (AllWinning.cons node_10031 (AllWinning.cons node_9057 (AllWinning.cons node_8073 (AllWinning.cons node_11102 (AllWinning.cons node_10038 (AllWinning.cons node_9070 (AllWinning.cons node_8086 (AllWinning.nil))))))))))

theorem node_12098 : Outcome ⟨2, 6, 17, 8⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12099 : Outcome ⟨2, 6, 17, 10⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12100 : Outcome ⟨2, 6, 17, 14⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12101 : Outcome ⟨2, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 8⟩) (by decide) node_8092

theorem node_12102 : Outcome ⟨2, 7, 16, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 8⟩) (by decide) node_8092

theorem node_12103 : Outcome ⟨2, 7, 16, 8⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 8⟩) (by decide) node_8092

theorem node_12104 : Outcome ⟨2, 7, 16, 18⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 26⟩) (by decide) node_2036

theorem node_12105 : Outcome ⟨2, 7, 16, 22⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 26⟩) (by decide) node_2036

theorem node_12106 : Outcome ⟨2, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 15, 2⟩) (by decide) node_11047

theorem node_12107 : Outcome ⟨2, 8, 15, 6⟩ true :=
  Outcome.win (q := ⟨1, 8, 15, 2⟩) (by decide) node_11047

theorem node_12108 : Outcome ⟨2, 8, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 15, 2⟩) (by decide) node_11047

theorem node_12109 : Outcome ⟨2, 9, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 14, 4⟩) (by decide) node_9895

theorem node_12110 : Outcome ⟨2, 9, 14, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 10⟩) (by decide) node_7133

theorem node_12111 : Outcome ⟨2, 10, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 12, 2⟩) (by decide) node_11114

theorem node_12112 : Outcome ⟨2, 10, 13, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 12, 2⟩) (by decide) node_11114

theorem node_12113 : Outcome ⟨2, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 11, 12, 2⟩) (by decide) node_11057

theorem node_12114 : Outcome ⟨2, 11, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12115 : Outcome ⟨2, 11, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12116 : Outcome ⟨2, 11, 12, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12117 : Outcome ⟨2, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 11, 2⟩) (by decide) node_11061

theorem node_12118 : Outcome ⟨2, 12, 11, 6⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12119 : Outcome ⟨2, 12, 11, 8⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12120 : Outcome ⟨2, 12, 11, 10⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12121 : Outcome ⟨2, 13, 10, 2⟩ true :=
  Outcome.win (q := ⟨2, 12, 10, 2⟩) (by decide) node_11122

theorem node_12122 : Outcome ⟨2, 13, 10, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 10, 2⟩) (by decide) node_11122

theorem node_12123 : Outcome ⟨2, 14, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 9, 4⟩) (by decide) node_9907

theorem node_12124 : Outcome ⟨2, 14, 9, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 10⟩) (by decide) node_7179

theorem node_12125 : Outcome ⟨2, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 8, 2⟩) (by decide) node_11071

theorem node_12126 : Outcome ⟨2, 15, 8, 6⟩ true :=
  Outcome.win (q := ⟨1, 15, 8, 2⟩) (by decide) node_11071

theorem node_12127 : Outcome ⟨2, 15, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 8, 2⟩) (by decide) node_11071

theorem node_12128 : Outcome ⟨2, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 8⟩) (by decide) node_8118

theorem node_12129 : Outcome ⟨2, 16, 7, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 8⟩) (by decide) node_8118

theorem node_12130 : Outcome ⟨2, 16, 7, 8⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 8⟩) (by decide) node_8118

theorem node_12131 : Outcome ⟨2, 16, 7, 18⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 26⟩) (by decide) node_2006

theorem node_12132 : Outcome ⟨2, 16, 7, 22⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 26⟩) (by decide) node_2006

theorem node_12133 : Outcome ⟨2, 17, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 6, 2⟩, ⟨0, 17, 6, 4⟩, ⟨2, 16, 6, 2⟩, ⟨2, 15, 6, 4⟩, ⟨2, 17, 5, 2⟩, ⟨2, 17, 4, 4⟩]
  exact AllWinning.cons node_11079 (AllWinning.cons node_9918 (AllWinning.cons node_11133 (AllWinning.cons node_10069 (AllWinning.cons node_11137 (AllWinning.cons node_10076 (AllWinning.nil))))))

theorem node_12134 : Outcome ⟨2, 17, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 6, 2⟩, ⟨0, 17, 6, 4⟩, ⟨2, 16, 6, 2⟩, ⟨2, 15, 6, 4⟩, ⟨2, 14, 6, 6⟩, ⟨2, 13, 6, 8⟩, ⟨2, 17, 5, 2⟩, ⟨2, 17, 4, 4⟩, ⟨2, 17, 3, 6⟩, ⟨2, 17, 2, 8⟩]
  exact AllWinning.cons node_11079 (AllWinning.cons node_9918 (AllWinning.cons node_11133 (AllWinning.cons node_10069 (AllWinning.cons node_9098 (AllWinning.cons node_8123 (AllWinning.cons node_11137 (AllWinning.cons node_10076 (AllWinning.cons node_9111 (AllWinning.cons node_8138 (AllWinning.nil))))))))))

theorem node_12135 : Outcome ⟨2, 17, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12136 : Outcome ⟨2, 17, 6, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12137 : Outcome ⟨2, 17, 6, 14⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12138 : Outcome ⟨2, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 4⟩) (by decide) node_9922

theorem node_12139 : Outcome ⟨2, 18, 5, 6⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 4⟩) (by decide) node_9922

theorem node_12140 : Outcome ⟨2, 18, 5, 20⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 16⟩) (by decide) node_4779

theorem node_12141 : Outcome ⟨2, 18, 5, 22⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 16⟩) (by decide) node_4779

theorem node_12142 : Outcome ⟨2, 19, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 4, 2⟩, ⟨0, 19, 4, 4⟩, ⟨2, 18, 4, 2⟩, ⟨2, 17, 4, 4⟩, ⟨2, 19, 3, 2⟩, ⟨2, 19, 2, 4⟩]
  exact AllWinning.cons node_11085 (AllWinning.cons node_9929 (AllWinning.cons node_11141 (AllWinning.cons node_10076 (AllWinning.cons node_11146 (AllWinning.cons node_10084 (AllWinning.nil))))))

theorem node_12143 : Outcome ⟨2, 19, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 4, 2⟩, ⟨0, 19, 4, 4⟩, ⟨2, 18, 4, 2⟩, ⟨2, 17, 4, 4⟩, ⟨2, 16, 4, 6⟩, ⟨2, 15, 4, 8⟩, ⟨2, 19, 3, 2⟩, ⟨2, 19, 2, 4⟩, ⟨2, 19, 1, 6⟩, ⟨2, 19, 0, 8⟩]
  exact AllWinning.cons node_11085 (AllWinning.cons node_9929 (AllWinning.cons node_11141 (AllWinning.cons node_10076 (AllWinning.cons node_9106 (AllWinning.cons node_8129 (AllWinning.cons node_11146 (AllWinning.cons node_10084 (AllWinning.cons node_9119 (AllWinning.cons node_8145 (AllWinning.nil))))))))))

theorem node_12144 : Outcome ⟨2, 19, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 10⟩) (by decide) node_7179

theorem node_12145 : Outcome ⟨2, 19, 4, 24⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 36⟩) (by decide) node_571

theorem node_12146 : Outcome ⟨2, 20, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 3, 2⟩, ⟨0, 20, 3, 4⟩, ⟨2, 19, 3, 2⟩, ⟨2, 18, 3, 4⟩, ⟨2, 17, 3, 6⟩, ⟨2, 16, 3, 8⟩, ⟨2, 20, 2, 2⟩, ⟨2, 20, 1, 4⟩, ⟨2, 20, 0, 6⟩]
  exact AllWinning.cons node_11088 (AllWinning.cons node_9931 (AllWinning.cons node_11146 (AllWinning.cons node_10081 (AllWinning.cons node_9111 (AllWinning.cons node_8133 (AllWinning.cons node_11149 (AllWinning.cons node_10086 (AllWinning.cons node_9122 (AllWinning.nil)))))))))

theorem node_12147 : Outcome ⟨2, 20, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 3, 2⟩, ⟨0, 20, 3, 4⟩, ⟨2, 19, 3, 2⟩, ⟨2, 18, 3, 4⟩, ⟨2, 17, 3, 6⟩, ⟨2, 16, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨2, 14, 3, 12⟩, ⟨2, 20, 2, 2⟩, ⟨2, 20, 1, 4⟩, ⟨2, 20, 0, 6⟩]
  exact AllWinning.cons node_11088 (AllWinning.cons node_9931 (AllWinning.cons node_11146 (AllWinning.cons node_10081 (AllWinning.cons node_9111 (AllWinning.cons node_8133 (AllWinning.cons node_7184 (AllWinning.cons node_6260 (AllWinning.cons node_11149 (AllWinning.cons node_10086 (AllWinning.cons node_9122 (AllWinning.nil)))))))))))

theorem node_12148 : Outcome ⟨2, 20, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 3, 2⟩, ⟨0, 20, 3, 4⟩, ⟨2, 19, 3, 2⟩, ⟨2, 18, 3, 4⟩, ⟨2, 17, 3, 6⟩, ⟨2, 16, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨2, 14, 3, 12⟩, ⟨2, 13, 3, 14⟩, ⟨2, 12, 3, 16⟩, ⟨2, 20, 2, 2⟩, ⟨2, 20, 1, 4⟩, ⟨2, 20, 0, 6⟩]
  exact AllWinning.cons node_11088 (AllWinning.cons node_9931 (AllWinning.cons node_11146 (AllWinning.cons node_10081 (AllWinning.cons node_9111 (AllWinning.cons node_8133 (AllWinning.cons node_7184 (AllWinning.cons node_6260 (AllWinning.cons node_5505 (AllWinning.cons node_4790 (AllWinning.cons node_11149 (AllWinning.cons node_10086 (AllWinning.cons node_9122 (AllWinning.nil)))))))))))))

theorem node_12149 : Outcome ⟨2, 20, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 3, 2⟩, ⟨0, 20, 3, 4⟩, ⟨2, 19, 3, 2⟩, ⟨2, 18, 3, 4⟩, ⟨2, 17, 3, 6⟩, ⟨2, 16, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨2, 14, 3, 12⟩, ⟨2, 13, 3, 14⟩, ⟨2, 12, 3, 16⟩, ⟨2, 11, 3, 18⟩, ⟨2, 10, 3, 20⟩, ⟨2, 20, 2, 2⟩, ⟨2, 20, 1, 4⟩, ⟨2, 20, 0, 6⟩]
  exact AllWinning.cons node_11088 (AllWinning.cons node_9931 (AllWinning.cons node_11146 (AllWinning.cons node_10081 (AllWinning.cons node_9111 (AllWinning.cons node_8133 (AllWinning.cons node_7184 (AllWinning.cons node_6260 (AllWinning.cons node_5505 (AllWinning.cons node_4790 (AllWinning.cons node_4088 (AllWinning.cons node_3523 (AllWinning.cons node_11149 (AllWinning.cons node_10086 (AllWinning.cons node_9122 (AllWinning.nil)))))))))))))))

theorem node_12150 : Outcome ⟨2, 20, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 3, 2⟩, ⟨0, 20, 3, 4⟩, ⟨2, 19, 3, 2⟩, ⟨2, 18, 3, 4⟩, ⟨2, 17, 3, 6⟩, ⟨2, 16, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨2, 14, 3, 12⟩, ⟨2, 13, 3, 14⟩, ⟨2, 12, 3, 16⟩, ⟨2, 11, 3, 18⟩, ⟨2, 10, 3, 20⟩, ⟨2, 9, 3, 22⟩, ⟨2, 8, 3, 24⟩, ⟨2, 20, 2, 2⟩, ⟨2, 20, 1, 4⟩, ⟨2, 20, 0, 6⟩]
  exact AllWinning.cons node_11088 (AllWinning.cons node_9931 (AllWinning.cons node_11146 (AllWinning.cons node_10081 (AllWinning.cons node_9111 (AllWinning.cons node_8133 (AllWinning.cons node_7184 (AllWinning.cons node_6260 (AllWinning.cons node_5505 (AllWinning.cons node_4790 (AllWinning.cons node_4088 (AllWinning.cons node_3523 (AllWinning.cons node_2978 (AllWinning.cons node_2515 (AllWinning.cons node_11149 (AllWinning.cons node_10086 (AllWinning.cons node_9122 (AllWinning.nil)))))))))))))))))

theorem node_12151 : Outcome ⟨3, 2, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 20, 2⟩, ⟨1, 2, 20, 4⟩, ⟨0, 2, 20, 6⟩, ⟨3, 1, 20, 2⟩, ⟨3, 0, 20, 4⟩, ⟨3, 2, 19, 2⟩, ⟨3, 2, 18, 4⟩, ⟨3, 2, 17, 6⟩, ⟨3, 2, 16, 8⟩]
  exact AllWinning.cons node_11089 (AllWinning.cons node_9933 (AllWinning.cons node_8906 (AllWinning.cons node_11150 (AllWinning.cons node_10087 (AllWinning.cons node_11151 (AllWinning.cons node_10097 (AllWinning.cons node_9132 (AllWinning.cons node_8155 (AllWinning.nil)))))))))

theorem node_12152 : Outcome ⟨3, 2, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 20, 2⟩, ⟨1, 2, 20, 4⟩, ⟨0, 2, 20, 6⟩, ⟨3, 1, 20, 2⟩, ⟨3, 0, 20, 4⟩, ⟨3, 2, 19, 2⟩, ⟨3, 2, 18, 4⟩, ⟨3, 2, 17, 6⟩, ⟨3, 2, 16, 8⟩, ⟨3, 2, 15, 10⟩, ⟨3, 2, 14, 12⟩]
  exact AllWinning.cons node_11089 (AllWinning.cons node_9933 (AllWinning.cons node_8906 (AllWinning.cons node_11150 (AllWinning.cons node_10087 (AllWinning.cons node_11151 (AllWinning.cons node_10097 (AllWinning.cons node_9132 (AllWinning.cons node_8155 (AllWinning.cons node_7208 (AllWinning.cons node_6286 (AllWinning.nil)))))))))))

theorem node_12153 : Outcome ⟨3, 2, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 20, 2⟩, ⟨1, 2, 20, 4⟩, ⟨0, 2, 20, 6⟩, ⟨3, 1, 20, 2⟩, ⟨3, 0, 20, 4⟩, ⟨3, 2, 19, 2⟩, ⟨3, 2, 18, 4⟩, ⟨3, 2, 17, 6⟩, ⟨3, 2, 16, 8⟩, ⟨3, 2, 15, 10⟩, ⟨3, 2, 14, 12⟩, ⟨3, 2, 13, 14⟩, ⟨3, 2, 12, 16⟩]
  exact AllWinning.cons node_11089 (AllWinning.cons node_9933 (AllWinning.cons node_8906 (AllWinning.cons node_11150 (AllWinning.cons node_10087 (AllWinning.cons node_11151 (AllWinning.cons node_10097 (AllWinning.cons node_9132 (AllWinning.cons node_8155 (AllWinning.cons node_7208 (AllWinning.cons node_6286 (AllWinning.cons node_5529 (AllWinning.cons node_4823 (AllWinning.nil)))))))))))))

theorem node_12154 : Outcome ⟨3, 2, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 20, 2⟩, ⟨1, 2, 20, 4⟩, ⟨0, 2, 20, 6⟩, ⟨3, 1, 20, 2⟩, ⟨3, 0, 20, 4⟩, ⟨3, 2, 19, 2⟩, ⟨3, 2, 18, 4⟩, ⟨3, 2, 17, 6⟩, ⟨3, 2, 16, 8⟩, ⟨3, 2, 15, 10⟩, ⟨3, 2, 14, 12⟩, ⟨3, 2, 13, 14⟩, ⟨3, 2, 12, 16⟩, ⟨3, 2, 11, 18⟩, ⟨3, 2, 10, 20⟩]
  exact AllWinning.cons node_11089 (AllWinning.cons node_9933 (AllWinning.cons node_8906 (AllWinning.cons node_11150 (AllWinning.cons node_10087 (AllWinning.cons node_11151 (AllWinning.cons node_10097 (AllWinning.cons node_9132 (AllWinning.cons node_8155 (AllWinning.cons node_7208 (AllWinning.cons node_6286 (AllWinning.cons node_5529 (AllWinning.cons node_4823 (AllWinning.cons node_4107 (AllWinning.cons node_3545 (AllWinning.nil)))))))))))))))

theorem node_12155 : Outcome ⟨3, 2, 20, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 20, 2⟩, ⟨1, 2, 20, 4⟩, ⟨0, 2, 20, 6⟩, ⟨3, 1, 20, 2⟩, ⟨3, 0, 20, 4⟩, ⟨3, 2, 19, 2⟩, ⟨3, 2, 18, 4⟩, ⟨3, 2, 17, 6⟩, ⟨3, 2, 16, 8⟩, ⟨3, 2, 15, 10⟩, ⟨3, 2, 14, 12⟩, ⟨3, 2, 13, 14⟩, ⟨3, 2, 12, 16⟩, ⟨3, 2, 11, 18⟩, ⟨3, 2, 10, 20⟩, ⟨3, 2, 9, 22⟩, ⟨3, 2, 8, 24⟩]
  exact AllWinning.cons node_11089 (AllWinning.cons node_9933 (AllWinning.cons node_8906 (AllWinning.cons node_11150 (AllWinning.cons node_10087 (AllWinning.cons node_11151 (AllWinning.cons node_10097 (AllWinning.cons node_9132 (AllWinning.cons node_8155 (AllWinning.cons node_7208 (AllWinning.cons node_6286 (AllWinning.cons node_5529 (AllWinning.cons node_4823 (AllWinning.cons node_4107 (AllWinning.cons node_3545 (AllWinning.cons node_3004 (AllWinning.cons node_2542 (AllWinning.nil)))))))))))))))))

theorem node_12156 : Outcome ⟨3, 3, 19, 4⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 4⟩) (by decide) node_9935

theorem node_12157 : Outcome ⟨3, 3, 19, 16⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 12⟩) (by decide) node_6293

theorem node_12158 : Outcome ⟨3, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 18, 2⟩) (by decide) node_11154

theorem node_12159 : Outcome ⟨3, 4, 18, 16⟩ true :=
  Outcome.win (q := ⟨3, 3, 18, 2⟩) (by decide) node_11154

theorem node_12160 : Outcome ⟨3, 4, 18, 22⟩ true :=
  Outcome.win (q := ⟨3, 3, 18, 2⟩) (by decide) node_11154

theorem node_12161 : Outcome ⟨3, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨3, 4, 17, 2⟩) (by decide) node_11157

theorem node_12162 : Outcome ⟨3, 5, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 4, 17, 2⟩) (by decide) node_11157

theorem node_12163 : Outcome ⟨3, 5, 17, 8⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 12⟩) (by decide) node_6304

theorem node_12164 : Outcome ⟨3, 5, 17, 18⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 12⟩) (by decide) node_6304

theorem node_12165 : Outcome ⟨3, 6, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 4⟩) (by decide) node_9952

theorem node_12166 : Outcome ⟨3, 6, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 12⟩) (by decide) node_6277

theorem node_12167 : Outcome ⟨3, 6, 16, 18⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 30⟩) (by decide) node_1364

theorem node_12168 : Outcome ⟨3, 7, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 15, 2⟩, ⟨1, 7, 15, 4⟩, ⟨3, 6, 15, 2⟩, ⟨3, 5, 15, 4⟩, ⟨3, 7, 14, 2⟩, ⟨3, 7, 13, 4⟩]
  exact AllWinning.cons node_11106 (AllWinning.cons node_9960 (AllWinning.cons node_11164 (AllWinning.cons node_10106 (AllWinning.cons node_11167 (AllWinning.cons node_10116 (AllWinning.nil))))))

theorem node_12169 : Outcome ⟨3, 7, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 15, 2⟩, ⟨1, 7, 15, 4⟩, ⟨0, 7, 15, 6⟩, ⟨3, 6, 15, 2⟩, ⟨3, 5, 15, 4⟩, ⟨3, 4, 15, 6⟩, ⟨3, 3, 15, 8⟩, ⟨3, 7, 14, 2⟩, ⟨3, 7, 13, 4⟩, ⟨3, 7, 12, 6⟩, ⟨3, 7, 11, 8⟩]
  exact AllWinning.cons node_11106 (AllWinning.cons node_9960 (AllWinning.cons node_8925 (AllWinning.cons node_11164 (AllWinning.cons node_10106 (AllWinning.cons node_9138 (AllWinning.cons node_8160 (AllWinning.cons node_11167 (AllWinning.cons node_10116 (AllWinning.cons node_9148 (AllWinning.cons node_8173 (AllWinning.nil)))))))))))

end RQ9F1
