import Chunk07
set_option autoImplicit false
namespace RQ9F1

theorem node_2076 : Outcome ⟨3, 2, 7, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 7, 2⟩, ⟨1, 2, 7, 4⟩, ⟨0, 2, 7, 6⟩, ⟨3, 1, 7, 2⟩, ⟨3, 0, 7, 4⟩, ⟨3, 2, 6, 2⟩, ⟨3, 2, 5, 4⟩, ⟨3, 2, 4, 6⟩, ⟨3, 2, 3, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 2, 1, 12⟩, ⟨3, 2, 0, 14⟩]
  exact AllWinning.cons node_1644 (AllWinning.cons node_1215 (AllWinning.cons node_918 (AllWinning.cons node_1683 (AllWinning.cons node_1316 (AllWinning.cons node_1687 (AllWinning.cons node_1337 (AllWinning.cons node_1039 (AllWinning.cons node_805 (AllWinning.cons node_606 (AllWinning.cons node_425 (AllWinning.cons node_307 (AllWinning.nil))))))))))))

theorem node_2077 : Outcome ⟨3, 2, 7, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 7, 2⟩, ⟨1, 2, 7, 4⟩, ⟨0, 2, 7, 6⟩, ⟨3, 1, 7, 2⟩, ⟨3, 0, 7, 4⟩, ⟨3, 2, 6, 2⟩, ⟨3, 2, 5, 4⟩, ⟨3, 2, 4, 6⟩, ⟨3, 2, 3, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 2, 1, 12⟩, ⟨3, 2, 0, 14⟩]
  exact AllWinning.cons node_1644 (AllWinning.cons node_1215 (AllWinning.cons node_918 (AllWinning.cons node_1683 (AllWinning.cons node_1316 (AllWinning.cons node_1687 (AllWinning.cons node_1337 (AllWinning.cons node_1039 (AllWinning.cons node_805 (AllWinning.cons node_606 (AllWinning.cons node_425 (AllWinning.cons node_307 (AllWinning.nil))))))))))))

theorem node_2078 : Outcome ⟨3, 2, 7, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 7, 2⟩, ⟨1, 2, 7, 4⟩, ⟨0, 2, 7, 6⟩, ⟨3, 1, 7, 2⟩, ⟨3, 0, 7, 4⟩, ⟨3, 2, 6, 2⟩, ⟨3, 2, 5, 4⟩, ⟨3, 2, 4, 6⟩, ⟨3, 2, 3, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 2, 1, 12⟩, ⟨3, 2, 0, 14⟩]
  exact AllWinning.cons node_1644 (AllWinning.cons node_1215 (AllWinning.cons node_918 (AllWinning.cons node_1683 (AllWinning.cons node_1316 (AllWinning.cons node_1687 (AllWinning.cons node_1337 (AllWinning.cons node_1039 (AllWinning.cons node_805 (AllWinning.cons node_606 (AllWinning.cons node_425 (AllWinning.cons node_307 (AllWinning.nil))))))))))))

theorem node_2079 : Outcome ⟨3, 2, 7, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 7, 2⟩, ⟨1, 2, 7, 4⟩, ⟨0, 2, 7, 6⟩, ⟨3, 1, 7, 2⟩, ⟨3, 0, 7, 4⟩, ⟨3, 2, 6, 2⟩, ⟨3, 2, 5, 4⟩, ⟨3, 2, 4, 6⟩, ⟨3, 2, 3, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 2, 1, 12⟩, ⟨3, 2, 0, 14⟩]
  exact AllWinning.cons node_1644 (AllWinning.cons node_1215 (AllWinning.cons node_918 (AllWinning.cons node_1683 (AllWinning.cons node_1316 (AllWinning.cons node_1687 (AllWinning.cons node_1337 (AllWinning.cons node_1039 (AllWinning.cons node_805 (AllWinning.cons node_606 (AllWinning.cons node_425 (AllWinning.cons node_307 (AllWinning.nil))))))))))))

theorem node_2080 : Outcome ⟨3, 3, 6, 4⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 4⟩) (by decide) node_1220

theorem node_2081 : Outcome ⟨3, 3, 6, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 12⟩) (by decide) node_431

theorem node_2082 : Outcome ⟨3, 3, 6, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 12⟩) (by decide) node_431

theorem node_2083 : Outcome ⟨3, 3, 6, 22⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 12⟩) (by decide) node_431

theorem node_2084 : Outcome ⟨3, 4, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2085 : Outcome ⟨3, 4, 5, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2086 : Outcome ⟨3, 4, 5, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2087 : Outcome ⟨3, 4, 5, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2088 : Outcome ⟨3, 5, 4, 2⟩ true :=
  Outcome.win (q := ⟨3, 4, 4, 2⟩) (by decide) node_1694

theorem node_2089 : Outcome ⟨3, 5, 4, 4⟩ true :=
  Outcome.win (q := ⟨3, 4, 4, 2⟩) (by decide) node_1694

theorem node_2090 : Outcome ⟨3, 5, 4, 8⟩ true :=
  Outcome.win (q := ⟨3, 4, 4, 2⟩) (by decide) node_1694

theorem node_2091 : Outcome ⟨3, 5, 4, 14⟩ true :=
  Outcome.win (q := ⟨3, 4, 4, 2⟩) (by decide) node_1694

theorem node_2092 : Outcome ⟨3, 6, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 4⟩) (by decide) node_1248

theorem node_2093 : Outcome ⟨3, 6, 3, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 12⟩) (by decide) node_408

theorem node_2094 : Outcome ⟨3, 6, 3, 14⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 12⟩) (by decide) node_408

theorem node_2095 : Outcome ⟨3, 6, 3, 22⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 12⟩) (by decide) node_408

theorem node_2096 : Outcome ⟨3, 7, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))

theorem node_2097 : Outcome ⟨3, 7, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil)))))))))

theorem node_2098 : Outcome ⟨3, 7, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil)))))))))))

theorem node_2099 : Outcome ⟨3, 7, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2100 : Outcome ⟨3, 7, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2101 : Outcome ⟨3, 7, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2102 : Outcome ⟨3, 7, 2, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2103 : Outcome ⟨3, 7, 2, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2104 : Outcome ⟨3, 7, 2, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2105 : Outcome ⟨3, 7, 2, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2106 : Outcome ⟨3, 7, 2, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2107 : Outcome ⟨3, 7, 2, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2108 : Outcome ⟨3, 7, 2, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2109 : Outcome ⟨3, 7, 2, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2110 : Outcome ⟨3, 7, 2, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 2, 2⟩, ⟨1, 7, 2, 4⟩, ⟨0, 7, 2, 6⟩, ⟨3, 6, 2, 2⟩, ⟨3, 5, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨3, 3, 2, 8⟩, ⟨3, 2, 2, 10⟩, ⟨3, 1, 2, 12⟩, ⟨3, 0, 2, 14⟩, ⟨3, 7, 1, 2⟩, ⟨3, 7, 0, 4⟩]
  exact AllWinning.cons node_1664 (AllWinning.cons node_1264 (AllWinning.cons node_939 (AllWinning.cons node_1702 (AllWinning.cons node_1347 (AllWinning.cons node_1047 (AllWinning.cons node_810 (AllWinning.cons node_606 (AllWinning.cons node_422 (AllWinning.cons node_298 (AllWinning.cons node_1705 (AllWinning.cons node_1368 (AllWinning.nil))))))))))))

theorem node_2111 : Outcome ⟨3, 8, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 4⟩) (by decide) node_1269

theorem node_2112 : Outcome ⟨3, 8, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 4⟩) (by decide) node_1269

theorem node_2113 : Outcome ⟨3, 8, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 4⟩) (by decide) node_1269

theorem node_2114 : Outcome ⟨3, 8, 1, 18⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 4⟩) (by decide) node_1269

theorem node_2115 : Outcome ⟨3, 8, 1, 22⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 4⟩) (by decide) node_1269

theorem node_2116 : Outcome ⟨3, 8, 1, 30⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 4⟩) (by decide) node_1269

theorem node_2117 : Outcome ⟨3, 9, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 0, 4⟩) (by decide) node_1274

theorem node_2118 : Outcome ⟨3, 9, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 0, 4⟩) (by decide) node_1274

theorem node_2119 : Outcome ⟨3, 9, 0, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 12⟩) (by decide) node_431

theorem node_2120 : Outcome ⟨3, 9, 0, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 12⟩) (by decide) node_431

theorem node_2121 : Outcome ⟨3, 9, 0, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 12⟩) (by decide) node_431

theorem node_2122 : Outcome ⟨4, 0, 8, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 8, 2⟩) (by decide) node_1677

theorem node_2123 : Outcome ⟨4, 0, 8, 8⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 8⟩) (by decide) node_823

theorem node_2124 : Outcome ⟨4, 0, 8, 18⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 8⟩) (by decide) node_823

theorem node_2125 : Outcome ⟨4, 1, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 7, 2⟩, ⟨2, 1, 7, 4⟩, ⟨4, 0, 7, 2⟩, ⟨4, 1, 6, 2⟩, ⟨4, 1, 5, 4⟩]
  exact AllWinning.cons node_1683 (AllWinning.cons node_1282 (AllWinning.cons node_1715 (AllWinning.cons node_1720 (AllWinning.cons node_1375 (AllWinning.nil)))))

theorem node_2126 : Outcome ⟨4, 1, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 7, 2⟩, ⟨2, 1, 7, 4⟩, ⟨1, 1, 7, 6⟩, ⟨0, 1, 7, 8⟩, ⟨4, 0, 7, 2⟩, ⟨4, 1, 6, 2⟩, ⟨4, 1, 5, 4⟩, ⟨4, 1, 4, 6⟩, ⟨4, 1, 3, 8⟩]
  exact AllWinning.cons node_1683 (AllWinning.cons node_1282 (AllWinning.cons node_957 (AllWinning.cons node_687 (AllWinning.cons node_1715 (AllWinning.cons node_1720 (AllWinning.cons node_1375 (AllWinning.cons node_1064 (AllWinning.cons node_837 (AllWinning.nil)))))))))

theorem node_2127 : Outcome ⟨4, 1, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 10⟩) (by decide) node_620

theorem node_2128 : Outcome ⟨4, 1, 7, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 10⟩) (by decide) node_620

theorem node_2129 : Outcome ⟨4, 1, 7, 14⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 10⟩) (by decide) node_620

theorem node_2130 : Outcome ⟨4, 1, 7, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 10⟩) (by decide) node_620

theorem node_2131 : Outcome ⟨4, 2, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 6, 2⟩, ⟨2, 2, 6, 4⟩, ⟨4, 1, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨4, 2, 5, 2⟩, ⟨4, 2, 4, 4⟩]
  exact AllWinning.cons node_1687 (AllWinning.cons node_1286 (AllWinning.cons node_1720 (AllWinning.cons node_1371 (AllWinning.cons node_1724 (AllWinning.cons node_1381 (AllWinning.nil))))))

theorem node_2132 : Outcome ⟨4, 2, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 6, 2⟩, ⟨2, 2, 6, 4⟩, ⟨1, 2, 6, 6⟩, ⟨0, 2, 6, 8⟩, ⟨4, 1, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨4, 2, 5, 2⟩, ⟨4, 2, 4, 4⟩, ⟨4, 2, 3, 6⟩, ⟨4, 2, 2, 8⟩]
  exact AllWinning.cons node_1687 (AllWinning.cons node_1286 (AllWinning.cons node_961 (AllWinning.cons node_692 (AllWinning.cons node_1720 (AllWinning.cons node_1371 (AllWinning.cons node_1724 (AllWinning.cons node_1381 (AllWinning.cons node_1069 (AllWinning.cons node_840 (AllWinning.nil))))))))))

theorem node_2133 : Outcome ⟨4, 2, 6, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 10⟩) (by decide) node_638

theorem node_2134 : Outcome ⟨4, 2, 6, 14⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 10⟩) (by decide) node_638

theorem node_2135 : Outcome ⟨4, 2, 6, 16⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 10⟩) (by decide) node_638

theorem node_2136 : Outcome ⟨4, 3, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2137 : Outcome ⟨4, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2138 : Outcome ⟨4, 3, 5, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2139 : Outcome ⟨4, 3, 5, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 2⟩) (by decide) node_1690

theorem node_2140 : Outcome ⟨4, 4, 4, 2⟩ true :=
  Outcome.win (q := ⟨3, 4, 4, 2⟩) (by decide) node_1694

theorem node_2141 : Outcome ⟨4, 4, 4, 8⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 8⟩) (by decide) node_702

theorem node_2142 : Outcome ⟨4, 4, 4, 18⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 8⟩) (by decide) node_702

theorem node_2143 : Outcome ⟨4, 5, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 3, 2⟩) (by decide) node_1698

theorem node_2144 : Outcome ⟨4, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 5, 3, 2⟩) (by decide) node_1698

theorem node_2145 : Outcome ⟨4, 5, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 5, 3, 2⟩) (by decide) node_1698

theorem node_2146 : Outcome ⟨4, 5, 3, 14⟩ true :=
  Outcome.win (q := ⟨3, 5, 3, 2⟩) (by decide) node_1698

theorem node_2147 : Outcome ⟨4, 6, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 2, 2⟩, ⟨2, 6, 2, 4⟩, ⟨4, 5, 2, 2⟩, ⟨4, 4, 2, 4⟩, ⟨4, 6, 1, 2⟩, ⟨4, 6, 0, 4⟩]
  exact AllWinning.cons node_1702 (AllWinning.cons node_1303 (AllWinning.cons node_1738 (AllWinning.cons node_1390 (AllWinning.cons node_1744 (AllWinning.cons node_1401 (AllWinning.nil))))))

theorem node_2148 : Outcome ⟨4, 6, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 2, 2⟩, ⟨2, 6, 2, 4⟩, ⟨1, 6, 2, 6⟩, ⟨0, 6, 2, 8⟩, ⟨4, 5, 2, 2⟩, ⟨4, 4, 2, 4⟩, ⟨4, 3, 2, 6⟩, ⟨4, 2, 2, 8⟩, ⟨4, 6, 1, 2⟩, ⟨4, 6, 0, 4⟩]
  exact AllWinning.cons node_1702 (AllWinning.cons node_1303 (AllWinning.cons node_980 (AllWinning.cons node_720 (AllWinning.cons node_1738 (AllWinning.cons node_1390 (AllWinning.cons node_1073 (AllWinning.cons node_840 (AllWinning.cons node_1744 (AllWinning.cons node_1401 (AllWinning.nil))))))))))

theorem node_2149 : Outcome ⟨4, 6, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 10⟩) (by decide) node_620

theorem node_2150 : Outcome ⟨4, 6, 2, 14⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 10⟩) (by decide) node_620

theorem node_2151 : Outcome ⟨4, 6, 2, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 10⟩) (by decide) node_620

theorem node_2152 : Outcome ⟨4, 7, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 7, 1, 2⟩, ⟨2, 7, 1, 4⟩, ⟨4, 6, 1, 2⟩, ⟨4, 5, 1, 4⟩, ⟨4, 7, 0, 2⟩]
  exact AllWinning.cons node_1705 (AllWinning.cons node_1306 (AllWinning.cons node_1744 (AllWinning.cons node_1396 (AllWinning.cons node_1748 (AllWinning.nil)))))

theorem node_2153 : Outcome ⟨4, 7, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 7, 1, 2⟩, ⟨2, 7, 1, 4⟩, ⟨1, 7, 1, 6⟩, ⟨0, 7, 1, 8⟩, ⟨4, 6, 1, 2⟩, ⟨4, 5, 1, 4⟩, ⟨4, 4, 1, 6⟩, ⟨4, 3, 1, 8⟩, ⟨4, 7, 0, 2⟩]
  exact AllWinning.cons node_1705 (AllWinning.cons node_1306 (AllWinning.cons node_985 (AllWinning.cons node_725 (AllWinning.cons node_1744 (AllWinning.cons node_1396 (AllWinning.cons node_1078 (AllWinning.cons node_844 (AllWinning.cons node_1748 (AllWinning.nil)))))))))

theorem node_2154 : Outcome ⟨4, 7, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 10⟩) (by decide) node_638

theorem node_2155 : Outcome ⟨4, 7, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 10⟩) (by decide) node_638

theorem node_2156 : Outcome ⟨4, 7, 1, 14⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 10⟩) (by decide) node_638

theorem node_2157 : Outcome ⟨4, 7, 1, 16⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 10⟩) (by decide) node_638

theorem node_2158 : Outcome ⟨4, 8, 0, 2⟩ true :=
  Outcome.win (q := ⟨3, 8, 0, 2⟩) (by decide) node_1709

theorem node_2159 : Outcome ⟨4, 8, 0, 8⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 8⟩) (by decide) node_849

theorem node_2160 : Outcome ⟨4, 8, 0, 18⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 8⟩) (by decide) node_849

theorem node_2161 : Outcome ⟨5, 0, 7, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2162 : Outcome ⟨5, 0, 7, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2163 : Outcome ⟨5, 0, 7, 8⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2164 : Outcome ⟨5, 0, 7, 22⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2165 : Outcome ⟨5, 1, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 4⟩) (by decide) node_1320

theorem node_2166 : Outcome ⟨5, 1, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 4⟩) (by decide) node_1320

theorem node_2167 : Outcome ⟨5, 1, 6, 22⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 4⟩) (by decide) node_1320

theorem node_2168 : Outcome ⟨5, 2, 5, 6⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2169 : Outcome ⟨5, 2, 5, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2170 : Outcome ⟨5, 2, 5, 12⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2171 : Outcome ⟨5, 2, 5, 22⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2172 : Outcome ⟨5, 3, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 3, 4, 2⟩) (by decide) node_1730

theorem node_2173 : Outcome ⟨5, 3, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 3, 4, 2⟩) (by decide) node_1730

theorem node_2174 : Outcome ⟨5, 3, 4, 8⟩ true :=
  Outcome.win (q := ⟨4, 3, 4, 2⟩) (by decide) node_1730

theorem node_2175 : Outcome ⟨5, 3, 4, 14⟩ true :=
  Outcome.win (q := ⟨4, 3, 4, 2⟩) (by decide) node_1730

theorem node_2176 : Outcome ⟨5, 4, 3, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 3, 2⟩) (by decide) node_1734

theorem node_2177 : Outcome ⟨5, 4, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 3, 2⟩) (by decide) node_1734

theorem node_2178 : Outcome ⟨5, 4, 3, 8⟩ true :=
  Outcome.win (q := ⟨4, 4, 3, 2⟩) (by decide) node_1734

theorem node_2179 : Outcome ⟨5, 4, 3, 14⟩ true :=
  Outcome.win (q := ⟨4, 4, 3, 2⟩) (by decide) node_1734

theorem node_2180 : Outcome ⟨5, 5, 2, 6⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2181 : Outcome ⟨5, 5, 2, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2182 : Outcome ⟨5, 5, 2, 12⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2183 : Outcome ⟨5, 5, 2, 22⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2184 : Outcome ⟨5, 6, 1, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 4⟩) (by decide) node_1351

theorem node_2185 : Outcome ⟨5, 6, 1, 6⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 4⟩) (by decide) node_1351

theorem node_2186 : Outcome ⟨5, 6, 1, 22⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 4⟩) (by decide) node_1351

theorem node_2187 : Outcome ⟨5, 7, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2188 : Outcome ⟨5, 7, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2189 : Outcome ⟨5, 7, 0, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2190 : Outcome ⟨5, 7, 0, 22⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 4⟩) (by decide) node_1439

theorem node_2191 : Outcome ⟨6, 0, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.nil))))

theorem node_2192 : Outcome ⟨6, 0, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.nil))))))))

theorem node_2193 : Outcome ⟨6, 0, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2194 : Outcome ⟨6, 0, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2195 : Outcome ⟨6, 0, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2196 : Outcome ⟨6, 0, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2197 : Outcome ⟨6, 0, 6, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2198 : Outcome ⟨6, 0, 6, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2199 : Outcome ⟨6, 0, 6, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2200 : Outcome ⟨6, 0, 6, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2201 : Outcome ⟨6, 0, 6, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2202 : Outcome ⟨6, 0, 6, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2203 : Outcome ⟨6, 0, 6, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2204 : Outcome ⟨6, 0, 6, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 6, 2⟩, ⟨4, 0, 6, 4⟩, ⟨3, 0, 6, 6⟩, ⟨2, 0, 6, 8⟩, ⟨1, 0, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨6, 0, 5, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 0, 3, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 0, 1, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1753 (AllWinning.cons node_1371 (AllWinning.cons node_1031 (AllWinning.cons node_766 (AllWinning.cons node_499 (AllWinning.cons node_327 (AllWinning.cons node_1778 (AllWinning.cons node_1452 (AllWinning.cons node_1105 (AllWinning.cons node_881 (AllWinning.cons node_669 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2205 : Outcome ⟨6, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 4⟩) (by decide) node_1456

theorem node_2206 : Outcome ⟨6, 1, 5, 6⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 4⟩) (by decide) node_1456

theorem node_2207 : Outcome ⟨6, 1, 5, 22⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 4⟩) (by decide) node_1456

theorem node_2208 : Outcome ⟨6, 2, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 4, 2⟩, ⟨4, 2, 4, 4⟩, ⟨6, 1, 4, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 2, 3, 2⟩, ⟨6, 2, 2, 4⟩]
  exact AllWinning.cons node_1758 (AllWinning.cons node_1381 (AllWinning.cons node_1781 (AllWinning.cons node_1452 (AllWinning.cons node_1785 (AllWinning.cons node_1472 (AllWinning.nil))))))

theorem node_2209 : Outcome ⟨6, 2, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 4, 2⟩, ⟨4, 2, 4, 4⟩, ⟨3, 2, 4, 6⟩, ⟨2, 2, 4, 8⟩, ⟨6, 1, 4, 2⟩, ⟨6, 0, 4, 4⟩, ⟨6, 2, 3, 2⟩, ⟨6, 2, 2, 4⟩, ⟨6, 2, 1, 6⟩, ⟨6, 2, 0, 8⟩]
  exact AllWinning.cons node_1758 (AllWinning.cons node_1381 (AllWinning.cons node_1039 (AllWinning.cons node_775 (AllWinning.cons node_1781 (AllWinning.cons node_1452 (AllWinning.cons node_1785 (AllWinning.cons node_1472 (AllWinning.cons node_1114 (AllWinning.cons node_887 (AllWinning.nil))))))))))

theorem node_2210 : Outcome ⟨6, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 10⟩) (by decide) node_509

theorem node_2211 : Outcome ⟨6, 2, 4, 14⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 10⟩) (by decide) node_509

theorem node_2212 : Outcome ⟨6, 2, 4, 16⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 10⟩) (by decide) node_509

theorem node_2213 : Outcome ⟨6, 3, 3, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 4⟩) (by decide) node_1456

theorem node_2214 : Outcome ⟨6, 3, 3, 12⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 12⟩) (by decide) node_342

theorem node_2215 : Outcome ⟨6, 3, 3, 14⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 12⟩) (by decide) node_342

theorem node_2216 : Outcome ⟨6, 3, 3, 22⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 12⟩) (by decide) node_342

theorem node_2217 : Outcome ⟨6, 4, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 4, 2, 2⟩, ⟨4, 4, 2, 4⟩, ⟨6, 3, 2, 2⟩, ⟨6, 2, 2, 4⟩, ⟨6, 4, 1, 2⟩, ⟨6, 4, 0, 4⟩]
  exact AllWinning.cons node_1767 (AllWinning.cons node_1390 (AllWinning.cons node_1788 (AllWinning.cons node_1472 (AllWinning.cons node_1791 (AllWinning.cons node_1492 (AllWinning.nil))))))

theorem node_2218 : Outcome ⟨6, 4, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 4, 2, 2⟩, ⟨4, 4, 2, 4⟩, ⟨3, 4, 2, 6⟩, ⟨2, 4, 2, 8⟩, ⟨6, 3, 2, 2⟩, ⟨6, 2, 2, 4⟩, ⟨6, 1, 2, 6⟩, ⟨6, 0, 2, 8⟩, ⟨6, 4, 1, 2⟩, ⟨6, 4, 0, 4⟩]
  exact AllWinning.cons node_1767 (AllWinning.cons node_1390 (AllWinning.cons node_1047 (AllWinning.cons node_784 (AllWinning.cons node_1788 (AllWinning.cons node_1472 (AllWinning.cons node_1109 (AllWinning.cons node_881 (AllWinning.cons node_1791 (AllWinning.cons node_1492 (AllWinning.nil))))))))))

theorem node_2219 : Outcome ⟨6, 4, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 10⟩) (by decide) node_530

theorem node_2220 : Outcome ⟨6, 4, 2, 14⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 10⟩) (by decide) node_530

theorem node_2221 : Outcome ⟨6, 4, 2, 16⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 10⟩) (by decide) node_530

theorem node_2222 : Outcome ⟨6, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 4⟩) (by decide) node_1476

theorem node_2223 : Outcome ⟨6, 5, 1, 6⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 4⟩) (by decide) node_1476

theorem node_2224 : Outcome ⟨6, 5, 1, 22⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 4⟩) (by decide) node_1476

theorem node_2225 : Outcome ⟨6, 6, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.nil))))

theorem node_2226 : Outcome ⟨6, 6, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.nil))))))))

theorem node_2227 : Outcome ⟨6, 6, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2228 : Outcome ⟨6, 6, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2229 : Outcome ⟨6, 6, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2230 : Outcome ⟨6, 6, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2231 : Outcome ⟨6, 6, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2232 : Outcome ⟨6, 6, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2233 : Outcome ⟨6, 6, 0, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2234 : Outcome ⟨6, 6, 0, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2235 : Outcome ⟨6, 6, 0, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2236 : Outcome ⟨6, 6, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2237 : Outcome ⟨6, 6, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2238 : Outcome ⟨6, 6, 0, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 0, 2⟩, ⟨4, 6, 0, 4⟩, ⟨3, 6, 0, 6⟩, ⟨2, 6, 0, 8⟩, ⟨1, 6, 0, 10⟩, ⟨0, 6, 0, 12⟩, ⟨6, 5, 0, 2⟩, ⟨6, 4, 0, 4⟩, ⟨6, 3, 0, 6⟩, ⟨6, 2, 0, 8⟩, ⟨6, 1, 0, 10⟩, ⟨6, 0, 0, 12⟩]
  exact AllWinning.cons node_1775 (AllWinning.cons node_1401 (AllWinning.cons node_1056 (AllWinning.cons node_793 (AllWinning.cons node_550 (AllWinning.cons node_363 (AllWinning.cons node_1795 (AllWinning.cons node_1492 (AllWinning.cons node_1120 (AllWinning.cons node_887 (AllWinning.cons node_674 (AllWinning.cons node_464 (AllWinning.nil))))))))))))

theorem node_2239 : Outcome ⟨7, 0, 5, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2240 : Outcome ⟨7, 0, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2241 : Outcome ⟨7, 0, 5, 8⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2242 : Outcome ⟨7, 0, 5, 22⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 4⟩) (by decide) node_1405

theorem node_2243 : Outcome ⟨7, 1, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 4, 2⟩, ⟨5, 1, 4, 4⟩, ⟨7, 0, 4, 2⟩, ⟨7, 1, 3, 2⟩, ⟨7, 1, 2, 4⟩]
  exact AllWinning.cons node_1781 (AllWinning.cons node_1419 (AllWinning.cons node_1798 (AllWinning.cons node_1802 (AllWinning.cons node_1499 (AllWinning.nil)))))

theorem node_2244 : Outcome ⟨7, 1, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 4, 2⟩, ⟨5, 1, 4, 4⟩, ⟨4, 1, 4, 6⟩, ⟨3, 1, 4, 8⟩, ⟨7, 0, 4, 2⟩, ⟨7, 1, 3, 2⟩, ⟨7, 1, 2, 4⟩, ⟨7, 1, 1, 6⟩, ⟨7, 1, 0, 8⟩]
  exact AllWinning.cons node_1781 (AllWinning.cons node_1419 (AllWinning.cons node_1064 (AllWinning.cons node_801 (AllWinning.cons node_1798 (AllWinning.cons node_1802 (AllWinning.cons node_1499 (AllWinning.cons node_1129 (AllWinning.cons node_898 (AllWinning.nil)))))))))

theorem node_2245 : Outcome ⟨7, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 10⟩) (by decide) node_560

theorem node_2246 : Outcome ⟨7, 1, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 10⟩) (by decide) node_560

theorem node_2247 : Outcome ⟨7, 1, 4, 14⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 10⟩) (by decide) node_560

theorem node_2248 : Outcome ⟨7, 1, 4, 16⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 10⟩) (by decide) node_560

theorem node_2249 : Outcome ⟨7, 2, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.nil))))))

theorem node_2250 : Outcome ⟨7, 2, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil)))))))))

theorem node_2251 : Outcome ⟨7, 2, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨2, 2, 3, 10⟩, ⟨1, 2, 3, 12⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_573 (AllWinning.cons node_373 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil)))))))))))

theorem node_2252 : Outcome ⟨7, 2, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨2, 2, 3, 10⟩, ⟨1, 2, 3, 12⟩, ⟨0, 2, 3, 14⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_573 (AllWinning.cons node_373 (AllWinning.cons node_246 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil))))))))))))

theorem node_2253 : Outcome ⟨7, 2, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨2, 2, 3, 10⟩, ⟨1, 2, 3, 12⟩, ⟨0, 2, 3, 14⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_573 (AllWinning.cons node_373 (AllWinning.cons node_246 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil))))))))))))

theorem node_2254 : Outcome ⟨7, 2, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨2, 2, 3, 10⟩, ⟨1, 2, 3, 12⟩, ⟨0, 2, 3, 14⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_573 (AllWinning.cons node_373 (AllWinning.cons node_246 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil))))))))))))

theorem node_2255 : Outcome ⟨7, 2, 3, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨2, 2, 3, 10⟩, ⟨1, 2, 3, 12⟩, ⟨0, 2, 3, 14⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_573 (AllWinning.cons node_373 (AllWinning.cons node_246 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil))))))))))))

theorem node_2256 : Outcome ⟨7, 2, 3, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨2, 2, 3, 10⟩, ⟨1, 2, 3, 12⟩, ⟨0, 2, 3, 14⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_573 (AllWinning.cons node_373 (AllWinning.cons node_246 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil))))))))))))

theorem node_2257 : Outcome ⟨7, 2, 3, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 3, 2⟩, ⟨5, 2, 3, 4⟩, ⟨4, 2, 3, 6⟩, ⟨3, 2, 3, 8⟩, ⟨2, 2, 3, 10⟩, ⟨1, 2, 3, 12⟩, ⟨0, 2, 3, 14⟩, ⟨7, 1, 3, 2⟩, ⟨7, 0, 3, 4⟩, ⟨7, 2, 2, 2⟩, ⟨7, 2, 1, 4⟩, ⟨7, 2, 0, 6⟩]
  exact AllWinning.cons node_1785 (AllWinning.cons node_1425 (AllWinning.cons node_1069 (AllWinning.cons node_805 (AllWinning.cons node_573 (AllWinning.cons node_373 (AllWinning.cons node_246 (AllWinning.cons node_1802 (AllWinning.cons node_1496 (AllWinning.cons node_1806 (AllWinning.cons node_1503 (AllWinning.cons node_1134 (AllWinning.nil))))))))))))

end RQ9F1
