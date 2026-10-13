import Chunk113
set_option autoImplicit false
namespace RQ9F1

theorem node_23949 : Outcome ⟨10, 16, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 16, 14, 2⟩, ⟨8, 16, 14, 4⟩, ⟨7, 16, 14, 6⟩, ⟨6, 16, 14, 8⟩, ⟨5, 16, 14, 10⟩, ⟨4, 16, 14, 12⟩, ⟨3, 16, 14, 14⟩, ⟨2, 16, 14, 16⟩, ⟨1, 16, 14, 18⟩, ⟨0, 16, 14, 20⟩, ⟨10, 15, 14, 2⟩, ⟨10, 14, 14, 4⟩, ⟨10, 13, 14, 6⟩, ⟨10, 12, 14, 8⟩, ⟨10, 11, 14, 10⟩, ⟨10, 10, 14, 12⟩, ⟨10, 9, 14, 14⟩, ⟨10, 8, 14, 16⟩, ⟨10, 7, 14, 18⟩, ⟨10, 6, 14, 20⟩, ⟨10, 16, 13, 2⟩, ⟨10, 16, 12, 4⟩, ⟨10, 16, 11, 6⟩, ⟨10, 16, 10, 8⟩, ⟨10, 16, 9, 10⟩, ⟨10, 16, 8, 12⟩, ⟨10, 16, 7, 14⟩, ⟨10, 16, 6, 16⟩, ⟨10, 16, 5, 18⟩, ⟨10, 16, 4, 20⟩]
  exact AllWinning.cons node_23540 (AllWinning.cons node_23074 (AllWinning.cons node_22518 (AllWinning.cons node_21917 (AllWinning.cons node_21295 (AllWinning.cons node_20505 (AllWinning.cons node_19780 (AllWinning.cons node_18890 (AllWinning.cons node_17933 (AllWinning.cons node_16997 (AllWinning.cons node_23561 (AllWinning.cons node_23129 (AllWinning.cons node_22606 (AllWinning.cons node_22028 (AllWinning.cons node_21437 (AllWinning.cons node_20753 (AllWinning.cons node_20005 (AllWinning.cons node_19219 (AllWinning.cons node_18321 (AllWinning.cons node_17425 (AllWinning.cons node_23563 (AllWinning.cons node_23134 (AllWinning.cons node_22615 (AllWinning.cons node_22038 (AllWinning.cons node_21447 (AllWinning.cons node_20766 (AllWinning.cons node_20027 (AllWinning.cons node_19242 (AllWinning.cons node_18350 (AllWinning.cons node_17451 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_23950 : Outcome ⟨10, 17, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 17, 13, 2⟩, ⟨8, 17, 13, 4⟩, ⟨10, 16, 13, 2⟩, ⟨10, 15, 13, 4⟩, ⟨10, 17, 12, 2⟩, ⟨10, 17, 11, 4⟩]
  exact AllWinning.cons node_23542 (AllWinning.cons node_23075 (AllWinning.cons node_23563 (AllWinning.cons node_23131 (AllWinning.cons node_23565 (AllWinning.cons node_23136 (AllWinning.nil))))))

theorem node_23951 : Outcome ⟨10, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 6⟩) (by decide) node_22617

theorem node_23952 : Outcome ⟨10, 18, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 18, 12, 2⟩, ⟨8, 18, 12, 4⟩, ⟨10, 17, 12, 2⟩, ⟨10, 16, 12, 4⟩, ⟨10, 18, 11, 2⟩, ⟨10, 18, 10, 4⟩]
  exact AllWinning.cons node_23544 (AllWinning.cons node_23078 (AllWinning.cons node_23565 (AllWinning.cons node_23134 (AllWinning.cons node_23567 (AllWinning.cons node_23138 (AllWinning.nil))))))

theorem node_23953 : Outcome ⟨10, 18, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 18, 12, 2⟩, ⟨8, 18, 12, 4⟩, ⟨7, 18, 12, 6⟩, ⟨6, 18, 12, 8⟩, ⟨10, 17, 12, 2⟩, ⟨10, 16, 12, 4⟩, ⟨10, 15, 12, 6⟩, ⟨10, 14, 12, 8⟩, ⟨10, 18, 11, 2⟩, ⟨10, 18, 10, 4⟩, ⟨10, 18, 9, 6⟩, ⟨10, 18, 8, 8⟩]
  exact AllWinning.cons node_23544 (AllWinning.cons node_23078 (AllWinning.cons node_22523 (AllWinning.cons node_21922 (AllWinning.cons node_23565 (AllWinning.cons node_23134 (AllWinning.cons node_22612 (AllWinning.cons node_22033 (AllWinning.cons node_23567 (AllWinning.cons node_23138 (AllWinning.cons node_22620 (AllWinning.cons node_22042 (AllWinning.nil))))))))))))

theorem node_23954 : Outcome ⟨10, 18, 12, 8⟩ true :=
  Outcome.win (q := ⟨10, 18, 6, 12⟩) (by decide) node_20774

theorem node_23955 : Outcome ⟨10, 19, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 19, 11, 2⟩, ⟨8, 19, 11, 4⟩, ⟨10, 18, 11, 2⟩, ⟨10, 17, 11, 4⟩, ⟨10, 19, 10, 2⟩, ⟨10, 19, 9, 4⟩]
  exact AllWinning.cons node_23548 (AllWinning.cons node_23080 (AllWinning.cons node_23567 (AllWinning.cons node_23136 (AllWinning.cons node_23568 (AllWinning.cons node_23139 (AllWinning.nil))))))

theorem node_23956 : Outcome ⟨10, 19, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 19, 11, 2⟩, ⟨8, 19, 11, 4⟩, ⟨7, 19, 11, 6⟩, ⟨6, 19, 11, 8⟩, ⟨10, 18, 11, 2⟩, ⟨10, 17, 11, 4⟩, ⟨10, 16, 11, 6⟩, ⟨10, 15, 11, 8⟩, ⟨10, 19, 10, 2⟩, ⟨10, 19, 9, 4⟩, ⟨10, 19, 8, 6⟩, ⟨10, 19, 7, 8⟩]
  exact AllWinning.cons node_23548 (AllWinning.cons node_23080 (AllWinning.cons node_22526 (AllWinning.cons node_21925 (AllWinning.cons node_23567 (AllWinning.cons node_23136 (AllWinning.cons node_22615 (AllWinning.cons node_22035 (AllWinning.cons node_23568 (AllWinning.cons node_23139 (AllWinning.cons node_22621 (AllWinning.cons node_22044 (AllWinning.nil))))))))))))

theorem node_23957 : Outcome ⟨10, 19, 11, 12⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 22⟩) (by decide) node_16510

theorem node_23958 : Outcome ⟨10, 20, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 20, 10, 2⟩, ⟨8, 20, 10, 4⟩, ⟨10, 19, 10, 2⟩, ⟨10, 18, 10, 4⟩, ⟨10, 20, 9, 2⟩, ⟨10, 20, 8, 4⟩]
  exact AllWinning.cons node_23550 (AllWinning.cons node_23081 (AllWinning.cons node_23568 (AllWinning.cons node_23138 (AllWinning.cons node_23569 (AllWinning.cons node_23141 (AllWinning.nil))))))

theorem node_23959 : Outcome ⟨11, 9, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 4⟩) (by decide) node_23083

theorem node_23960 : Outcome ⟨11, 10, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 19, 2⟩, ⟨9, 10, 19, 4⟩, ⟨11, 9, 19, 2⟩, ⟨11, 8, 19, 4⟩, ⟨11, 10, 18, 2⟩, ⟨11, 10, 17, 4⟩]
  exact AllWinning.cons node_23553 (AllWinning.cons node_23088 (AllWinning.cons node_23572 (AllWinning.cons node_23144 (AllWinning.cons node_23574 (AllWinning.cons node_23147 (AllWinning.nil))))))

theorem node_23961 : Outcome ⟨11, 10, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 19, 2⟩, ⟨9, 10, 19, 4⟩, ⟨8, 10, 19, 6⟩, ⟨7, 10, 19, 8⟩, ⟨11, 9, 19, 2⟩, ⟨11, 8, 19, 4⟩, ⟨11, 7, 19, 6⟩, ⟨11, 6, 19, 8⟩, ⟨11, 10, 18, 2⟩, ⟨11, 10, 17, 4⟩, ⟨11, 10, 16, 6⟩, ⟨11, 10, 15, 8⟩]
  exact AllWinning.cons node_23553 (AllWinning.cons node_23088 (AllWinning.cons node_22531 (AllWinning.cons node_21931 (AllWinning.cons node_23572 (AllWinning.cons node_23144 (AllWinning.cons node_22627 (AllWinning.cons node_22049 (AllWinning.cons node_23574 (AllWinning.cons node_23147 (AllWinning.cons node_22632 (AllWinning.cons node_22059 (AllWinning.nil))))))))))))

theorem node_23962 : Outcome ⟨11, 10, 19, 12⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 22⟩) (by decide) node_16578

theorem node_23963 : Outcome ⟨11, 11, 18, 4⟩ true :=
  Outcome.win (q := ⟨9, 11, 18, 4⟩) (by decide) node_23091

theorem node_23964 : Outcome ⟨11, 12, 17, 4⟩ true :=
  Outcome.win (q := ⟨9, 12, 17, 4⟩) (by decide) node_23093

theorem node_23965 : Outcome ⟨11, 13, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 13, 16, 2⟩, ⟨9, 13, 16, 4⟩, ⟨11, 12, 16, 2⟩, ⟨11, 11, 16, 4⟩, ⟨11, 13, 15, 2⟩, ⟨11, 13, 14, 4⟩]
  exact AllWinning.cons node_23557 (AllWinning.cons node_23095 (AllWinning.cons node_23576 (AllWinning.cons node_23150 (AllWinning.cons node_23578 (AllWinning.cons node_23155 (AllWinning.nil))))))

theorem node_23966 : Outcome ⟨11, 13, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 13, 16, 2⟩, ⟨9, 13, 16, 4⟩, ⟨8, 13, 16, 6⟩, ⟨7, 13, 16, 8⟩, ⟨11, 12, 16, 2⟩, ⟨11, 11, 16, 4⟩, ⟨11, 10, 16, 6⟩, ⟨11, 9, 16, 8⟩, ⟨11, 13, 15, 2⟩, ⟨11, 13, 14, 4⟩, ⟨11, 13, 13, 6⟩, ⟨11, 13, 12, 8⟩]
  exact AllWinning.cons node_23557 (AllWinning.cons node_23095 (AllWinning.cons node_22537 (AllWinning.cons node_21937 (AllWinning.cons node_23576 (AllWinning.cons node_23150 (AllWinning.cons node_22632 (AllWinning.cons node_22055 (AllWinning.cons node_23578 (AllWinning.cons node_23155 (AllWinning.cons node_22639 (AllWinning.cons node_22067 (AllWinning.nil))))))))))))

theorem node_23967 : Outcome ⟨11, 13, 16, 10⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 12⟩) (by decide) node_20792

theorem node_23968 : Outcome ⟨11, 13, 16, 12⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 12⟩) (by decide) node_20792

theorem node_23969 : Outcome ⟨11, 14, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 14, 15, 2⟩, ⟨9, 14, 15, 4⟩, ⟨11, 13, 15, 2⟩, ⟨11, 12, 15, 4⟩, ⟨11, 14, 14, 2⟩, ⟨11, 14, 13, 4⟩]
  exact AllWinning.cons node_23559 (AllWinning.cons node_23098 (AllWinning.cons node_23578 (AllWinning.cons node_23153 (AllWinning.cons node_23580 (AllWinning.cons node_23157 (AllWinning.nil))))))

theorem node_23970 : Outcome ⟨11, 14, 15, 4⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 6⟩) (by decide) node_22541

theorem node_23971 : Outcome ⟨11, 15, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 14, 2⟩, ⟨9, 15, 14, 4⟩, ⟨11, 14, 14, 2⟩, ⟨11, 13, 14, 4⟩, ⟨11, 15, 13, 2⟩, ⟨11, 15, 12, 4⟩]
  exact AllWinning.cons node_23561 (AllWinning.cons node_23100 (AllWinning.cons node_23580 (AllWinning.cons node_23155 (AllWinning.cons node_23582 (AllWinning.cons node_23160 (AllWinning.nil))))))

theorem node_23972 : Outcome ⟨11, 15, 14, 4⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 6⟩) (by decide) node_22546

theorem node_23973 : Outcome ⟨11, 16, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 13, 2⟩, ⟨9, 16, 13, 4⟩, ⟨11, 15, 13, 2⟩, ⟨11, 14, 13, 4⟩, ⟨11, 16, 12, 2⟩, ⟨11, 16, 11, 4⟩]
  exact AllWinning.cons node_23563 (AllWinning.cons node_23102 (AllWinning.cons node_23582 (AllWinning.cons node_23157 (AllWinning.cons node_23584 (AllWinning.cons node_23163 (AllWinning.nil))))))

theorem node_23974 : Outcome ⟨11, 16, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 13, 2⟩, ⟨9, 16, 13, 4⟩, ⟨8, 16, 13, 6⟩, ⟨7, 16, 13, 8⟩, ⟨11, 15, 13, 2⟩, ⟨11, 14, 13, 4⟩, ⟨11, 13, 13, 6⟩, ⟨11, 12, 13, 8⟩, ⟨11, 16, 12, 2⟩, ⟨11, 16, 11, 4⟩, ⟨11, 16, 10, 6⟩, ⟨11, 16, 9, 8⟩]
  exact AllWinning.cons node_23563 (AllWinning.cons node_23102 (AllWinning.cons node_22550 (AllWinning.cons node_21945 (AllWinning.cons node_23582 (AllWinning.cons node_23157 (AllWinning.cons node_22639 (AllWinning.cons node_22064 (AllWinning.cons node_23584 (AllWinning.cons node_23163 (AllWinning.cons node_22645 (AllWinning.cons node_22075 (AllWinning.nil))))))))))))

theorem node_23975 : Outcome ⟨11, 16, 13, 10⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 12⟩) (by decide) node_20814

theorem node_23976 : Outcome ⟨11, 16, 13, 12⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 12⟩) (by decide) node_20814

theorem node_23977 : Outcome ⟨11, 17, 12, 4⟩ true :=
  Outcome.win (q := ⟨9, 17, 12, 4⟩) (by decide) node_23105

theorem node_23978 : Outcome ⟨11, 18, 11, 4⟩ true :=
  Outcome.win (q := ⟨9, 18, 11, 4⟩) (by decide) node_23108

theorem node_23979 : Outcome ⟨11, 19, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 10, 2⟩, ⟨9, 19, 10, 4⟩, ⟨11, 18, 10, 2⟩, ⟨11, 17, 10, 4⟩, ⟨11, 19, 9, 2⟩, ⟨11, 19, 8, 4⟩]
  exact AllWinning.cons node_23568 (AllWinning.cons node_23110 (AllWinning.cons node_23587 (AllWinning.cons node_23165 (AllWinning.cons node_23588 (AllWinning.cons node_23168 (AllWinning.nil))))))

theorem node_23980 : Outcome ⟨11, 19, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 10, 2⟩, ⟨9, 19, 10, 4⟩, ⟨8, 19, 10, 6⟩, ⟨7, 19, 10, 8⟩, ⟨11, 18, 10, 2⟩, ⟨11, 17, 10, 4⟩, ⟨11, 16, 10, 6⟩, ⟨11, 15, 10, 8⟩, ⟨11, 19, 9, 2⟩, ⟨11, 19, 8, 4⟩, ⟨11, 19, 7, 6⟩, ⟨11, 19, 6, 8⟩]
  exact AllWinning.cons node_23568 (AllWinning.cons node_23110 (AllWinning.cons node_22556 (AllWinning.cons node_21951 (AllWinning.cons node_23587 (AllWinning.cons node_23165 (AllWinning.cons node_22645 (AllWinning.cons node_22073 (AllWinning.cons node_23588 (AllWinning.cons node_23168 (AllWinning.cons node_22650 (AllWinning.cons node_22081 (AllWinning.nil))))))))))))

theorem node_23981 : Outcome ⟨11, 19, 10, 12⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 22⟩) (by decide) node_16570

theorem node_23982 : Outcome ⟨11, 20, 9, 4⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 4⟩) (by decide) node_23113

theorem node_23983 : Outcome ⟨12, 8, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 8, 20, 2⟩, ⟨10, 8, 20, 4⟩, ⟨12, 7, 20, 2⟩, ⟨12, 6, 20, 4⟩, ⟨12, 8, 19, 2⟩, ⟨12, 8, 18, 4⟩]
  exact AllWinning.cons node_23570 (AllWinning.cons node_23118 (AllWinning.cons node_23592 (AllWinning.cons node_23171 (AllWinning.cons node_23593 (AllWinning.cons node_23176 (AllWinning.nil))))))

theorem node_23984 : Outcome ⟨12, 8, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 8, 20, 2⟩, ⟨10, 8, 20, 4⟩, ⟨9, 8, 20, 6⟩, ⟨8, 8, 20, 8⟩, ⟨12, 7, 20, 2⟩, ⟨12, 6, 20, 4⟩, ⟨12, 5, 20, 6⟩, ⟨12, 4, 20, 8⟩, ⟨12, 8, 19, 2⟩, ⟨12, 8, 18, 4⟩, ⟨12, 8, 17, 6⟩, ⟨12, 8, 16, 8⟩]
  exact AllWinning.cons node_23570 (AllWinning.cons node_23118 (AllWinning.cons node_22560 (AllWinning.cons node_21954 (AllWinning.cons node_23592 (AllWinning.cons node_23171 (AllWinning.cons node_22655 (AllWinning.cons node_22085 (AllWinning.cons node_23593 (AllWinning.cons node_23176 (AllWinning.cons node_22661 (AllWinning.cons node_22096 (AllWinning.nil))))))))))))

theorem node_23985 : Outcome ⟨12, 9, 19, 4⟩ true :=
  Outcome.win (q := ⟨12, 9, 17, 4⟩) (by decide) node_23178

theorem node_23986 : Outcome ⟨12, 9, 19, 6⟩ true :=
  Outcome.win (q := ⟨12, 9, 17, 4⟩) (by decide) node_23178

theorem node_23987 : Outcome ⟨12, 10, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 10, 18, 2⟩, ⟨10, 10, 18, 4⟩, ⟨9, 10, 18, 6⟩, ⟨8, 10, 18, 8⟩, ⟨12, 9, 18, 2⟩, ⟨12, 8, 18, 4⟩, ⟨12, 7, 18, 6⟩, ⟨12, 6, 18, 8⟩, ⟨12, 10, 17, 2⟩, ⟨12, 10, 16, 4⟩, ⟨12, 10, 15, 6⟩, ⟨12, 10, 14, 8⟩]
  exact AllWinning.cons node_23574 (AllWinning.cons node_23121 (AllWinning.cons node_22563 (AllWinning.cons node_21957 (AllWinning.cons node_23595 (AllWinning.cons node_23176 (AllWinning.cons node_22659 (AllWinning.cons node_22091 (AllWinning.cons node_23598 (AllWinning.cons node_23181 (AllWinning.cons node_22668 (AllWinning.cons node_22103 (AllWinning.nil))))))))))))

theorem node_23988 : Outcome ⟨12, 10, 18, 8⟩ true :=
  Outcome.win (q := ⟨6, 10, 18, 12⟩) (by decide) node_20554

theorem node_23989 : Outcome ⟨12, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨12, 9, 17, 4⟩) (by decide) node_23178

theorem node_23990 : Outcome ⟨12, 12, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 16, 2⟩, ⟨10, 12, 16, 4⟩, ⟨12, 11, 16, 2⟩, ⟨12, 10, 16, 4⟩, ⟨12, 12, 15, 2⟩, ⟨12, 12, 14, 4⟩]
  exact AllWinning.cons node_23576 (AllWinning.cons node_23125 (AllWinning.cons node_23600 (AllWinning.cons node_23181 (AllWinning.cons node_23602 (AllWinning.cons node_23186 (AllWinning.nil))))))

theorem node_23991 : Outcome ⟨12, 12, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 16, 2⟩, ⟨10, 12, 16, 4⟩, ⟨9, 12, 16, 6⟩, ⟨8, 12, 16, 8⟩, ⟨12, 11, 16, 2⟩, ⟨12, 10, 16, 4⟩, ⟨12, 9, 16, 6⟩, ⟨12, 8, 16, 8⟩, ⟨12, 12, 15, 2⟩, ⟨12, 12, 14, 4⟩, ⟨12, 12, 13, 6⟩, ⟨12, 12, 12, 8⟩]
  exact AllWinning.cons node_23576 (AllWinning.cons node_23125 (AllWinning.cons node_22567 (AllWinning.cons node_21964 (AllWinning.cons node_23600 (AllWinning.cons node_23181 (AllWinning.cons node_22664 (AllWinning.cons node_22096 (AllWinning.cons node_23602 (AllWinning.cons node_23186 (AllWinning.cons node_22672 (AllWinning.cons node_22108 (AllWinning.nil))))))))))))

theorem node_23992 : Outcome ⟨12, 12, 16, 6⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 12⟩) (by decide) node_20561

theorem node_23993 : Outcome ⟨12, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 6⟩) (by decide) node_22572

theorem node_23994 : Outcome ⟨12, 13, 15, 6⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 12⟩) (by decide) node_20840

theorem node_23995 : Outcome ⟨12, 14, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 14, 14, 2⟩, ⟨10, 14, 14, 4⟩, ⟨12, 13, 14, 2⟩, ⟨12, 12, 14, 4⟩, ⟨12, 14, 13, 2⟩, ⟨12, 14, 12, 4⟩]
  exact AllWinning.cons node_23580 (AllWinning.cons node_23129 (AllWinning.cons node_23604 (AllWinning.cons node_23186 (AllWinning.cons node_23607 (AllWinning.cons node_23192 (AllWinning.nil))))))

theorem node_23996 : Outcome ⟨12, 14, 14, 4⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 6⟩) (by decide) node_22576

theorem node_23997 : Outcome ⟨12, 14, 14, 8⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 6⟩) (by decide) node_22576

theorem node_23998 : Outcome ⟨12, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 6⟩) (by decide) node_22581

theorem node_23999 : Outcome ⟨12, 15, 13, 6⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 12⟩) (by decide) node_20863

theorem node_24000 : Outcome ⟨12, 16, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 12, 2⟩, ⟨10, 16, 12, 4⟩, ⟨12, 15, 12, 2⟩, ⟨12, 14, 12, 4⟩, ⟨12, 16, 11, 2⟩, ⟨12, 16, 10, 4⟩]
  exact AllWinning.cons node_23584 (AllWinning.cons node_23134 (AllWinning.cons node_23610 (AllWinning.cons node_23192 (AllWinning.cons node_23612 (AllWinning.cons node_23198 (AllWinning.nil))))))

theorem node_24001 : Outcome ⟨12, 16, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 12, 2⟩, ⟨10, 16, 12, 4⟩, ⟨9, 16, 12, 6⟩, ⟨8, 16, 12, 8⟩, ⟨12, 15, 12, 2⟩, ⟨12, 14, 12, 4⟩, ⟨12, 13, 12, 6⟩, ⟨12, 12, 12, 8⟩, ⟨12, 16, 11, 2⟩, ⟨12, 16, 10, 4⟩, ⟨12, 16, 9, 6⟩, ⟨12, 16, 8, 8⟩]
  exact AllWinning.cons node_23584 (AllWinning.cons node_23134 (AllWinning.cons node_22584 (AllWinning.cons node_21976 (AllWinning.cons node_23610 (AllWinning.cons node_23192 (AllWinning.cons node_22676 (AllWinning.cons node_22108 (AllWinning.cons node_23612 (AllWinning.cons node_23198 (AllWinning.cons node_22684 (AllWinning.cons node_22121 (AllWinning.nil))))))))))))

theorem node_24002 : Outcome ⟨12, 16, 12, 6⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 12⟩) (by decide) node_20577

theorem node_24003 : Outcome ⟨12, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨12, 17, 9, 4⟩) (by decide) node_23200

theorem node_24004 : Outcome ⟨12, 18, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 18, 10, 2⟩, ⟨10, 18, 10, 4⟩, ⟨9, 18, 10, 6⟩, ⟨8, 18, 10, 8⟩, ⟨12, 17, 10, 2⟩, ⟨12, 16, 10, 4⟩, ⟨12, 15, 10, 6⟩, ⟨12, 14, 10, 8⟩, ⟨12, 18, 9, 2⟩, ⟨12, 18, 8, 4⟩, ⟨12, 18, 7, 6⟩, ⟨12, 18, 6, 8⟩]
  exact AllWinning.cons node_23587 (AllWinning.cons node_23138 (AllWinning.cons node_22590 (AllWinning.cons node_21983 (AllWinning.cons node_23614 (AllWinning.cons node_23198 (AllWinning.cons node_22681 (AllWinning.cons node_22115 (AllWinning.cons node_23616 (AllWinning.cons node_23203 (AllWinning.cons node_22689 (AllWinning.cons node_22126 (AllWinning.nil))))))))))))

theorem node_24005 : Outcome ⟨12, 18, 10, 8⟩ true :=
  Outcome.win (q := ⟨6, 18, 10, 12⟩) (by decide) node_20586

theorem node_24006 : Outcome ⟨12, 19, 9, 4⟩ true :=
  Outcome.win (q := ⟨12, 17, 9, 4⟩) (by decide) node_23200

theorem node_24007 : Outcome ⟨12, 19, 9, 6⟩ true :=
  Outcome.win (q := ⟨12, 17, 9, 4⟩) (by decide) node_23200

theorem node_24008 : Outcome ⟨12, 20, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 20, 8, 2⟩, ⟨10, 20, 8, 4⟩, ⟨12, 19, 8, 2⟩, ⟨12, 18, 8, 4⟩, ⟨12, 20, 7, 2⟩, ⟨12, 20, 6, 4⟩]
  exact AllWinning.cons node_23590 (AllWinning.cons node_23141 (AllWinning.cons node_23618 (AllWinning.cons node_23203 (AllWinning.cons node_23620 (AllWinning.cons node_23207 (AllWinning.nil))))))

theorem node_24009 : Outcome ⟨13, 7, 20, 4⟩ true :=
  Outcome.win (q := ⟨13, 4, 20, 6⟩) (by decide) node_22695

theorem node_24010 : Outcome ⟨13, 7, 20, 16⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 22⟩) (by decide) node_16694

theorem node_24011 : Outcome ⟨13, 8, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 8, 19, 2⟩, ⟨11, 8, 19, 4⟩, ⟨13, 7, 19, 2⟩, ⟨13, 6, 19, 4⟩, ⟨13, 8, 18, 2⟩, ⟨13, 8, 17, 4⟩]
  exact AllWinning.cons node_23593 (AllWinning.cons node_23144 (AllWinning.cons node_23623 (AllWinning.cons node_23211 (AllWinning.cons node_23624 (AllWinning.cons node_23216 (AllWinning.nil))))))

theorem node_24012 : Outcome ⟨13, 8, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 8, 19, 2⟩, ⟨11, 8, 19, 4⟩, ⟨10, 8, 19, 6⟩, ⟨9, 8, 19, 8⟩, ⟨13, 7, 19, 2⟩, ⟨13, 6, 19, 4⟩, ⟨13, 5, 19, 6⟩, ⟨13, 4, 19, 8⟩, ⟨13, 8, 18, 2⟩, ⟨13, 8, 17, 4⟩, ⟨13, 8, 16, 6⟩, ⟨13, 8, 15, 8⟩]
  exact AllWinning.cons node_23593 (AllWinning.cons node_23144 (AllWinning.cons node_22594 (AllWinning.cons node_21987 (AllWinning.cons node_23623 (AllWinning.cons node_23211 (AllWinning.cons node_22698 (AllWinning.cons node_22133 (AllWinning.cons node_23624 (AllWinning.cons node_23216 (AllWinning.cons node_22704 (AllWinning.cons node_22143 (AllWinning.nil))))))))))))

theorem node_24013 : Outcome ⟨13, 8, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 8, 19, 2⟩, ⟨11, 8, 19, 4⟩, ⟨10, 8, 19, 6⟩, ⟨9, 8, 19, 8⟩, ⟨8, 8, 19, 10⟩, ⟨7, 8, 19, 12⟩, ⟨13, 7, 19, 2⟩, ⟨13, 6, 19, 4⟩, ⟨13, 5, 19, 6⟩, ⟨13, 4, 19, 8⟩, ⟨13, 3, 19, 10⟩, ⟨13, 2, 19, 12⟩, ⟨13, 8, 18, 2⟩, ⟨13, 8, 17, 4⟩, ⟨13, 8, 16, 6⟩, ⟨13, 8, 15, 8⟩, ⟨13, 8, 14, 10⟩, ⟨13, 8, 13, 12⟩]
  exact AllWinning.cons node_23593 (AllWinning.cons node_23144 (AllWinning.cons node_22594 (AllWinning.cons node_21987 (AllWinning.cons node_21366 (AllWinning.cons node_20593 (AllWinning.cons node_23623 (AllWinning.cons node_23211 (AllWinning.cons node_22698 (AllWinning.cons node_22133 (AllWinning.cons node_21539 (AllWinning.cons node_20882 (AllWinning.cons node_23624 (AllWinning.cons node_23216 (AllWinning.cons node_22704 (AllWinning.cons node_22143 (AllWinning.cons node_21552 (AllWinning.cons node_20897 (AllWinning.nil))))))))))))))))))

theorem node_24014 : Outcome ⟨13, 8, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 8, 19, 2⟩, ⟨11, 8, 19, 4⟩, ⟨10, 8, 19, 6⟩, ⟨9, 8, 19, 8⟩, ⟨8, 8, 19, 10⟩, ⟨7, 8, 19, 12⟩, ⟨6, 8, 19, 14⟩, ⟨5, 8, 19, 16⟩, ⟨13, 7, 19, 2⟩, ⟨13, 6, 19, 4⟩, ⟨13, 5, 19, 6⟩, ⟨13, 4, 19, 8⟩, ⟨13, 3, 19, 10⟩, ⟨13, 2, 19, 12⟩, ⟨13, 1, 19, 14⟩, ⟨13, 0, 19, 16⟩, ⟨13, 8, 18, 2⟩, ⟨13, 8, 17, 4⟩, ⟨13, 8, 16, 6⟩, ⟨13, 8, 15, 8⟩, ⟨13, 8, 14, 10⟩, ⟨13, 8, 13, 12⟩, ⟨13, 8, 12, 14⟩, ⟨13, 8, 11, 16⟩]
  exact AllWinning.cons node_23593 (AllWinning.cons node_23144 (AllWinning.cons node_22594 (AllWinning.cons node_21987 (AllWinning.cons node_21366 (AllWinning.cons node_20593 (AllWinning.cons node_19857 (AllWinning.cons node_18970 (AllWinning.cons node_23623 (AllWinning.cons node_23211 (AllWinning.cons node_22698 (AllWinning.cons node_22133 (AllWinning.cons node_21539 (AllWinning.cons node_20882 (AllWinning.cons node_20130 (AllWinning.cons node_19355 (AllWinning.cons node_23624 (AllWinning.cons node_23216 (AllWinning.cons node_22704 (AllWinning.cons node_22143 (AllWinning.cons node_21552 (AllWinning.cons node_20897 (AllWinning.cons node_20149 (AllWinning.cons node_19376 (AllWinning.nil))))))))))))))))))))))))

theorem node_24015 : Outcome ⟨13, 9, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 6⟩) (by decide) node_22708

theorem node_24016 : Outcome ⟨13, 9, 18, 8⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 6⟩) (by decide) node_22708

theorem node_24017 : Outcome ⟨13, 10, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 10, 17, 2⟩, ⟨11, 10, 17, 4⟩, ⟨13, 9, 17, 2⟩, ⟨13, 8, 17, 4⟩, ⟨13, 10, 16, 2⟩, ⟨13, 10, 15, 4⟩]
  exact AllWinning.cons node_23598 (AllWinning.cons node_23147 (AllWinning.cons node_23626 (AllWinning.cons node_23216 (AllWinning.cons node_23628 (AllWinning.cons node_23221 (AllWinning.nil))))))

theorem node_24018 : Outcome ⟨13, 10, 17, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 6⟩) (by decide) node_22598

theorem node_24019 : Outcome ⟨13, 11, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 11, 16, 2⟩, ⟨11, 11, 16, 4⟩, ⟨13, 10, 16, 2⟩, ⟨13, 9, 16, 4⟩, ⟨13, 11, 15, 2⟩, ⟨13, 11, 14, 4⟩]
  exact AllWinning.cons node_23600 (AllWinning.cons node_23150 (AllWinning.cons node_23628 (AllWinning.cons node_23218 (AllWinning.cons node_23630 (AllWinning.cons node_23223 (AllWinning.nil))))))

theorem node_24020 : Outcome ⟨13, 11, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 11, 16, 2⟩, ⟨11, 11, 16, 4⟩, ⟨10, 11, 16, 6⟩, ⟨9, 11, 16, 8⟩, ⟨13, 10, 16, 2⟩, ⟨13, 9, 16, 4⟩, ⟨13, 8, 16, 6⟩, ⟨13, 7, 16, 8⟩, ⟨13, 11, 15, 2⟩, ⟨13, 11, 14, 4⟩, ⟨13, 11, 13, 6⟩, ⟨13, 11, 12, 8⟩]
  exact AllWinning.cons node_23600 (AllWinning.cons node_23150 (AllWinning.cons node_22601 (AllWinning.cons node_21994 (AllWinning.cons node_23628 (AllWinning.cons node_23218 (AllWinning.cons node_22704 (AllWinning.cons node_22141 (AllWinning.cons node_23630 (AllWinning.cons node_23223 (AllWinning.cons node_22715 (AllWinning.cons node_22151 (AllWinning.nil))))))))))))

theorem node_24021 : Outcome ⟨13, 11, 16, 10⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 12⟩) (by decide) node_20604

theorem node_24022 : Outcome ⟨13, 11, 16, 12⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 12⟩) (by decide) node_20604

theorem node_24023 : Outcome ⟨13, 12, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 12, 15, 2⟩, ⟨11, 12, 15, 4⟩, ⟨13, 11, 15, 2⟩, ⟨13, 10, 15, 4⟩, ⟨13, 12, 14, 2⟩, ⟨13, 12, 13, 4⟩]
  exact AllWinning.cons node_23602 (AllWinning.cons node_23153 (AllWinning.cons node_23630 (AllWinning.cons node_23221 (AllWinning.cons node_23632 (AllWinning.cons node_23226 (AllWinning.nil))))))

theorem node_24024 : Outcome ⟨13, 12, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 6⟩) (by decide) node_22708

theorem node_24025 : Outcome ⟨13, 12, 15, 6⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 12⟩) (by decide) node_20612

theorem node_24026 : Outcome ⟨13, 12, 15, 16⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 22⟩) (by decide) node_16716

theorem node_24027 : Outcome ⟨13, 13, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 2⟩) (by decide) node_23635

theorem node_24028 : Outcome ⟨13, 13, 14, 8⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 14⟩) (by decide) node_19869

theorem node_24029 : Outcome ⟨13, 14, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 2⟩) (by decide) node_23635

theorem node_24030 : Outcome ⟨13, 14, 13, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 14⟩) (by decide) node_19876

theorem node_24031 : Outcome ⟨13, 15, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 12, 2⟩, ⟨11, 15, 12, 4⟩, ⟨13, 14, 12, 2⟩, ⟨13, 13, 12, 4⟩, ⟨13, 15, 11, 2⟩, ⟨13, 15, 10, 4⟩]
  exact AllWinning.cons node_23610 (AllWinning.cons node_23160 (AllWinning.cons node_23641 (AllWinning.cons node_23229 (AllWinning.cons node_23644 (AllWinning.cons node_23233 (AllWinning.nil))))))

theorem node_24032 : Outcome ⟨13, 15, 12, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 6⟩) (by decide) node_22727

theorem node_24033 : Outcome ⟨13, 15, 12, 6⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 12⟩) (by decide) node_20623

theorem node_24034 : Outcome ⟨13, 15, 12, 16⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 22⟩) (by decide) node_16681

theorem node_24035 : Outcome ⟨13, 16, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 11, 2⟩, ⟨11, 16, 11, 4⟩, ⟨13, 15, 11, 2⟩, ⟨13, 14, 11, 4⟩, ⟨13, 16, 10, 2⟩, ⟨13, 16, 9, 4⟩]
  exact AllWinning.cons node_23612 (AllWinning.cons node_23163 (AllWinning.cons node_23644 (AllWinning.cons node_23231 (AllWinning.cons node_23647 (AllWinning.cons node_23236 (AllWinning.nil))))))

theorem node_24036 : Outcome ⟨13, 16, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 11, 2⟩, ⟨11, 16, 11, 4⟩, ⟨10, 16, 11, 6⟩, ⟨9, 16, 11, 8⟩, ⟨13, 15, 11, 2⟩, ⟨13, 14, 11, 4⟩, ⟨13, 13, 11, 6⟩, ⟨13, 12, 11, 8⟩, ⟨13, 16, 10, 2⟩, ⟨13, 16, 9, 4⟩, ⟨13, 16, 8, 6⟩, ⟨13, 16, 7, 8⟩]
  exact AllWinning.cons node_23612 (AllWinning.cons node_23163 (AllWinning.cons node_22615 (AllWinning.cons node_22005 (AllWinning.cons node_23644 (AllWinning.cons node_23231 (AllWinning.cons node_22721 (AllWinning.cons node_22155 (AllWinning.cons node_23647 (AllWinning.cons node_23236 (AllWinning.cons node_22730 (AllWinning.cons node_22166 (AllWinning.nil))))))))))))

theorem node_24037 : Outcome ⟨13, 16, 11, 10⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 12⟩) (by decide) node_20630

theorem node_24038 : Outcome ⟨13, 16, 11, 12⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 12⟩) (by decide) node_20630

theorem node_24039 : Outcome ⟨13, 17, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 10, 2⟩, ⟨11, 17, 10, 4⟩, ⟨13, 16, 10, 2⟩, ⟨13, 15, 10, 4⟩, ⟨13, 17, 9, 2⟩, ⟨13, 17, 8, 4⟩]
  exact AllWinning.cons node_23614 (AllWinning.cons node_23165 (AllWinning.cons node_23647 (AllWinning.cons node_23233 (AllWinning.cons node_23649 (AllWinning.cons node_23239 (AllWinning.nil))))))

theorem node_24040 : Outcome ⟨13, 17, 10, 4⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 6⟩) (by decide) node_22617

theorem node_24041 : Outcome ⟨13, 18, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 6⟩) (by decide) node_22727

theorem node_24042 : Outcome ⟨13, 18, 9, 8⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 6⟩) (by decide) node_22727

theorem node_24043 : Outcome ⟨13, 19, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 19, 8, 2⟩, ⟨11, 19, 8, 4⟩, ⟨13, 18, 8, 2⟩, ⟨13, 17, 8, 4⟩, ⟨13, 19, 7, 2⟩, ⟨13, 19, 6, 4⟩]
  exact AllWinning.cons node_23618 (AllWinning.cons node_23168 (AllWinning.cons node_23651 (AllWinning.cons node_23239 (AllWinning.cons node_23653 (AllWinning.cons node_23245 (AllWinning.nil))))))

theorem node_24044 : Outcome ⟨13, 19, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 19, 8, 2⟩, ⟨11, 19, 8, 4⟩, ⟨10, 19, 8, 6⟩, ⟨9, 19, 8, 8⟩, ⟨13, 18, 8, 2⟩, ⟨13, 17, 8, 4⟩, ⟨13, 16, 8, 6⟩, ⟨13, 15, 8, 8⟩, ⟨13, 19, 7, 2⟩, ⟨13, 19, 6, 4⟩, ⟨13, 19, 5, 6⟩, ⟨13, 19, 4, 8⟩]
  exact AllWinning.cons node_23618 (AllWinning.cons node_23168 (AllWinning.cons node_22621 (AllWinning.cons node_22012 (AllWinning.cons node_23651 (AllWinning.cons node_23239 (AllWinning.cons node_22730 (AllWinning.cons node_22162 (AllWinning.cons node_23653 (AllWinning.cons node_23245 (AllWinning.cons node_22738 (AllWinning.cons node_22173 (AllWinning.nil))))))))))))

theorem node_24045 : Outcome ⟨13, 19, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 19, 8, 2⟩, ⟨11, 19, 8, 4⟩, ⟨10, 19, 8, 6⟩, ⟨9, 19, 8, 8⟩, ⟨8, 19, 8, 10⟩, ⟨7, 19, 8, 12⟩, ⟨13, 18, 8, 2⟩, ⟨13, 17, 8, 4⟩, ⟨13, 16, 8, 6⟩, ⟨13, 15, 8, 8⟩, ⟨13, 14, 8, 10⟩, ⟨13, 13, 8, 12⟩, ⟨13, 19, 7, 2⟩, ⟨13, 19, 6, 4⟩, ⟨13, 19, 5, 6⟩, ⟨13, 19, 4, 8⟩, ⟨13, 19, 3, 10⟩, ⟨13, 19, 2, 12⟩]
  exact AllWinning.cons node_23618 (AllWinning.cons node_23168 (AllWinning.cons node_22621 (AllWinning.cons node_22012 (AllWinning.cons node_21387 (AllWinning.cons node_20639 (AllWinning.cons node_23651 (AllWinning.cons node_23239 (AllWinning.cons node_22730 (AllWinning.cons node_22162 (AllWinning.cons node_21563 (AllWinning.cons node_20913 (AllWinning.cons node_23653 (AllWinning.cons node_23245 (AllWinning.cons node_22738 (AllWinning.cons node_22173 (AllWinning.cons node_21578 (AllWinning.cons node_20928 (AllWinning.nil))))))))))))))))))

theorem node_24046 : Outcome ⟨13, 19, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 19, 8, 2⟩, ⟨11, 19, 8, 4⟩, ⟨10, 19, 8, 6⟩, ⟨9, 19, 8, 8⟩, ⟨8, 19, 8, 10⟩, ⟨7, 19, 8, 12⟩, ⟨6, 19, 8, 14⟩, ⟨5, 19, 8, 16⟩, ⟨13, 18, 8, 2⟩, ⟨13, 17, 8, 4⟩, ⟨13, 16, 8, 6⟩, ⟨13, 15, 8, 8⟩, ⟨13, 14, 8, 10⟩, ⟨13, 13, 8, 12⟩, ⟨13, 12, 8, 14⟩, ⟨13, 11, 8, 16⟩, ⟨13, 19, 7, 2⟩, ⟨13, 19, 6, 4⟩, ⟨13, 19, 5, 6⟩, ⟨13, 19, 4, 8⟩, ⟨13, 19, 3, 10⟩, ⟨13, 19, 2, 12⟩, ⟨13, 19, 1, 14⟩, ⟨13, 19, 0, 16⟩]
  exact AllWinning.cons node_23618 (AllWinning.cons node_23168 (AllWinning.cons node_22621 (AllWinning.cons node_22012 (AllWinning.cons node_21387 (AllWinning.cons node_20639 (AllWinning.cons node_19884 (AllWinning.cons node_18992 (AllWinning.cons node_23651 (AllWinning.cons node_23239 (AllWinning.cons node_22730 (AllWinning.cons node_22162 (AllWinning.cons node_21563 (AllWinning.cons node_20913 (AllWinning.cons node_20161 (AllWinning.cons node_19388 (AllWinning.cons node_23653 (AllWinning.cons node_23245 (AllWinning.cons node_22738 (AllWinning.cons node_22173 (AllWinning.cons node_21578 (AllWinning.cons node_20928 (AllWinning.cons node_20180 (AllWinning.cons node_19408 (AllWinning.nil))))))))))))))))))))))))

theorem node_24047 : Outcome ⟨13, 20, 7, 4⟩ true :=
  Outcome.win (q := ⟨13, 20, 4, 6⟩) (by decide) node_22740

theorem node_24048 : Outcome ⟨13, 20, 7, 16⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 22⟩) (by decide) node_16705

theorem node_24049 : Outcome ⟨14, 6, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 5, 20, 2⟩) (by decide) node_23655

theorem node_24050 : Outcome ⟨14, 7, 19, 4⟩ true :=
  Outcome.win (q := ⟨14, 4, 19, 6⟩) (by decide) node_22743

theorem node_24051 : Outcome ⟨14, 8, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 8, 18, 2⟩, ⟨12, 8, 18, 4⟩, ⟨14, 7, 18, 2⟩, ⟨14, 6, 18, 4⟩, ⟨14, 8, 17, 2⟩, ⟨14, 8, 16, 4⟩]
  exact AllWinning.cons node_23624 (AllWinning.cons node_23176 (AllWinning.cons node_23657 (AllWinning.cons node_23250 (AllWinning.cons node_23660 (AllWinning.cons node_23254 (AllWinning.nil))))))

theorem node_24052 : Outcome ⟨14, 8, 18, 8⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 12⟩) (by decide) node_20650

theorem node_24053 : Outcome ⟨14, 9, 17, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 6⟩) (by decide) node_22760

theorem node_24054 : Outcome ⟨14, 10, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 10, 16, 2⟩, ⟨12, 10, 16, 4⟩, ⟨14, 9, 16, 2⟩, ⟨14, 8, 16, 4⟩, ⟨14, 10, 15, 2⟩, ⟨14, 10, 14, 4⟩]
  exact AllWinning.cons node_23628 (AllWinning.cons node_23181 (AllWinning.cons node_23662 (AllWinning.cons node_23254 (AllWinning.cons node_23664 (AllWinning.cons node_23257 (AllWinning.nil))))))

theorem node_24055 : Outcome ⟨14, 10, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 10, 16, 2⟩, ⟨12, 10, 16, 4⟩, ⟨11, 10, 16, 6⟩, ⟨10, 10, 16, 8⟩, ⟨14, 9, 16, 2⟩, ⟨14, 8, 16, 4⟩, ⟨14, 7, 16, 6⟩, ⟨14, 6, 16, 8⟩, ⟨14, 10, 15, 2⟩, ⟨14, 10, 14, 4⟩, ⟨14, 10, 13, 6⟩, ⟨14, 10, 12, 8⟩]
  exact AllWinning.cons node_23628 (AllWinning.cons node_23181 (AllWinning.cons node_22632 (AllWinning.cons node_22023 (AllWinning.cons node_23662 (AllWinning.cons node_23254 (AllWinning.cons node_22752 (AllWinning.cons node_22184 (AllWinning.cons node_23664 (AllWinning.cons node_23257 (AllWinning.cons node_22764 (AllWinning.cons node_22193 (AllWinning.nil))))))))))))

theorem node_24056 : Outcome ⟨14, 10, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 10, 16, 2⟩, ⟨12, 10, 16, 4⟩, ⟨11, 10, 16, 6⟩, ⟨10, 10, 16, 8⟩, ⟨9, 10, 16, 10⟩, ⟨8, 10, 16, 12⟩, ⟨14, 9, 16, 2⟩, ⟨14, 8, 16, 4⟩, ⟨14, 7, 16, 6⟩, ⟨14, 6, 16, 8⟩, ⟨14, 5, 16, 10⟩, ⟨14, 4, 16, 12⟩, ⟨14, 10, 15, 2⟩, ⟨14, 10, 14, 4⟩, ⟨14, 10, 13, 6⟩, ⟨14, 10, 12, 8⟩, ⟨14, 10, 11, 10⟩, ⟨14, 10, 10, 12⟩]
  exact AllWinning.cons node_23628 (AllWinning.cons node_23181 (AllWinning.cons node_22632 (AllWinning.cons node_22023 (AllWinning.cons node_21401 (AllWinning.cons node_20655 (AllWinning.cons node_23662 (AllWinning.cons node_23254 (AllWinning.cons node_22752 (AllWinning.cons node_22184 (AllWinning.cons node_21589 (AllWinning.cons node_20945 (AllWinning.cons node_23664 (AllWinning.cons node_23257 (AllWinning.cons node_22764 (AllWinning.cons node_22193 (AllWinning.cons node_21599 (AllWinning.cons node_20957 (AllWinning.nil))))))))))))))))))

theorem node_24057 : Outcome ⟨14, 11, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 11, 15, 2⟩, ⟨12, 11, 15, 4⟩, ⟨14, 10, 15, 2⟩, ⟨14, 9, 15, 4⟩, ⟨14, 11, 14, 2⟩, ⟨14, 11, 13, 4⟩]
  exact AllWinning.cons node_23630 (AllWinning.cons node_23183 (AllWinning.cons node_23664 (AllWinning.cons node_23255 (AllWinning.cons node_23666 (AllWinning.cons node_23259 (AllWinning.nil))))))

theorem node_24058 : Outcome ⟨14, 11, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 8, 15, 6⟩) (by decide) node_22755

theorem node_24059 : Outcome ⟨14, 12, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 12, 14, 2⟩, ⟨12, 12, 14, 4⟩, ⟨14, 11, 14, 2⟩, ⟨14, 10, 14, 4⟩, ⟨14, 12, 13, 2⟩, ⟨14, 12, 12, 4⟩]
  exact AllWinning.cons node_23632 (AllWinning.cons node_23186 (AllWinning.cons node_23666 (AllWinning.cons node_23257 (AllWinning.cons node_23668 (AllWinning.cons node_23262 (AllWinning.nil))))))

theorem node_24060 : Outcome ⟨14, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 6⟩) (by decide) node_22760

theorem node_24061 : Outcome ⟨14, 12, 14, 8⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 6⟩) (by decide) node_22760

theorem node_24062 : Outcome ⟨14, 13, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 2⟩) (by decide) node_23635

theorem node_24063 : Outcome ⟨14, 13, 13, 8⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 14⟩) (by decide) node_20205

theorem node_24064 : Outcome ⟨14, 14, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 12, 2⟩, ⟨12, 14, 12, 4⟩, ⟨14, 13, 12, 2⟩, ⟨14, 12, 12, 4⟩, ⟨14, 14, 11, 2⟩, ⟨14, 14, 10, 4⟩]
  exact AllWinning.cons node_23641 (AllWinning.cons node_23192 (AllWinning.cons node_23671 (AllWinning.cons node_23262 (AllWinning.cons node_23674 (AllWinning.cons node_23266 (AllWinning.nil))))))

theorem node_24065 : Outcome ⟨14, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 6⟩) (by decide) node_22777

theorem node_24066 : Outcome ⟨14, 14, 12, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 6⟩) (by decide) node_22777

theorem node_24067 : Outcome ⟨14, 15, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 11, 2⟩, ⟨12, 15, 11, 4⟩, ⟨14, 14, 11, 2⟩, ⟨14, 13, 11, 4⟩, ⟨14, 15, 10, 2⟩, ⟨14, 15, 9, 4⟩]
  exact AllWinning.cons node_23644 (AllWinning.cons node_23195 (AllWinning.cons node_23674 (AllWinning.cons node_23264 (AllWinning.cons node_23676 (AllWinning.cons node_23268 (AllWinning.nil))))))

theorem node_24068 : Outcome ⟨14, 15, 11, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 8, 6⟩) (by decide) node_22782

theorem node_24069 : Outcome ⟨14, 16, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 10, 2⟩, ⟨12, 16, 10, 4⟩, ⟨14, 15, 10, 2⟩, ⟨14, 14, 10, 4⟩, ⟨14, 16, 9, 2⟩, ⟨14, 16, 8, 4⟩]
  exact AllWinning.cons node_23647 (AllWinning.cons node_23198 (AllWinning.cons node_23676 (AllWinning.cons node_23266 (AllWinning.cons node_23678 (AllWinning.cons node_23270 (AllWinning.nil))))))

theorem node_24070 : Outcome ⟨14, 16, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 10, 2⟩, ⟨12, 16, 10, 4⟩, ⟨11, 16, 10, 6⟩, ⟨10, 16, 10, 8⟩, ⟨14, 15, 10, 2⟩, ⟨14, 14, 10, 4⟩, ⟨14, 13, 10, 6⟩, ⟨14, 12, 10, 8⟩, ⟨14, 16, 9, 2⟩, ⟨14, 16, 8, 4⟩, ⟨14, 16, 7, 6⟩, ⟨14, 16, 6, 8⟩]
  exact AllWinning.cons node_23647 (AllWinning.cons node_23198 (AllWinning.cons node_22645 (AllWinning.cons node_22038 (AllWinning.cons node_23676 (AllWinning.cons node_23266 (AllWinning.cons node_22773 (AllWinning.cons node_22198 (AllWinning.cons node_23678 (AllWinning.cons node_23270 (AllWinning.cons node_22786 (AllWinning.cons node_22208 (AllWinning.nil))))))))))))

theorem node_24071 : Outcome ⟨14, 16, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 10, 2⟩, ⟨12, 16, 10, 4⟩, ⟨11, 16, 10, 6⟩, ⟨10, 16, 10, 8⟩, ⟨9, 16, 10, 10⟩, ⟨8, 16, 10, 12⟩, ⟨14, 15, 10, 2⟩, ⟨14, 14, 10, 4⟩, ⟨14, 13, 10, 6⟩, ⟨14, 12, 10, 8⟩, ⟨14, 11, 10, 10⟩, ⟨14, 10, 10, 12⟩, ⟨14, 16, 9, 2⟩, ⟨14, 16, 8, 4⟩, ⟨14, 16, 7, 6⟩, ⟨14, 16, 6, 8⟩, ⟨14, 16, 5, 10⟩, ⟨14, 16, 4, 12⟩]
  exact AllWinning.cons node_23647 (AllWinning.cons node_23198 (AllWinning.cons node_22645 (AllWinning.cons node_22038 (AllWinning.cons node_21417 (AllWinning.cons node_20672 (AllWinning.cons node_23676 (AllWinning.cons node_23266 (AllWinning.cons node_22773 (AllWinning.cons node_22198 (AllWinning.cons node_21602 (AllWinning.cons node_20957 (AllWinning.cons node_23678 (AllWinning.cons node_23270 (AllWinning.cons node_22786 (AllWinning.cons node_22208 (AllWinning.cons node_21611 (AllWinning.cons node_20971 (AllWinning.nil))))))))))))))))))

theorem node_24072 : Outcome ⟨14, 17, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 6⟩) (by decide) node_22777

theorem node_24073 : Outcome ⟨14, 18, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 8, 2⟩, ⟨12, 18, 8, 4⟩, ⟨14, 17, 8, 2⟩, ⟨14, 16, 8, 4⟩, ⟨14, 18, 7, 2⟩, ⟨14, 18, 6, 4⟩]
  exact AllWinning.cons node_23651 (AllWinning.cons node_23203 (AllWinning.cons node_23680 (AllWinning.cons node_23270 (AllWinning.cons node_23682 (AllWinning.cons node_23273 (AllWinning.nil))))))

theorem node_24074 : Outcome ⟨14, 18, 8, 8⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 12⟩) (by decide) node_20679

theorem node_24075 : Outcome ⟨14, 19, 7, 4⟩ true :=
  Outcome.win (q := ⟨14, 19, 4, 6⟩) (by decide) node_22793

theorem node_24076 : Outcome ⟨14, 20, 6, 2⟩ true :=
  Outcome.win (q := ⟨14, 20, 5, 2⟩) (by decide) node_23686

theorem node_24077 : Outcome ⟨15, 5, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 5, 20, 2⟩) (by decide) node_23655

theorem node_24078 : Outcome ⟨15, 5, 20, 16⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 24⟩) (by decide) node_15752

theorem node_24079 : Outcome ⟨15, 6, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 19, 2⟩) (by decide) node_23688

theorem node_24080 : Outcome ⟨15, 6, 19, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 19, 2⟩) (by decide) node_23688

theorem node_24081 : Outcome ⟨15, 7, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 7, 18, 4⟩) (by decide) node_23213

theorem node_24082 : Outcome ⟨15, 7, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 8⟩) (by decide) node_22222

theorem node_24083 : Outcome ⟨15, 8, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 14, 6⟩) (by decide) node_22810

theorem node_24084 : Outcome ⟨15, 9, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 16, 2⟩, ⟨13, 9, 16, 4⟩, ⟨15, 8, 16, 2⟩, ⟨15, 7, 16, 4⟩, ⟨15, 9, 15, 2⟩, ⟨15, 9, 14, 4⟩]
  exact AllWinning.cons node_23662 (AllWinning.cons node_23218 (AllWinning.cons node_23694 (AllWinning.cons node_23286 (AllWinning.cons node_23696 (AllWinning.cons node_23289 (AllWinning.nil))))))

theorem node_24085 : Outcome ⟨15, 9, 16, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 6⟩) (by decide) node_22815

theorem node_24086 : Outcome ⟨15, 9, 16, 6⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 6⟩) (by decide) node_22815

theorem node_24087 : Outcome ⟨15, 10, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 10, 15, 2⟩, ⟨13, 10, 15, 4⟩, ⟨15, 9, 15, 2⟩, ⟨15, 8, 15, 4⟩, ⟨15, 10, 14, 2⟩, ⟨15, 10, 13, 4⟩]
  exact AllWinning.cons node_23664 (AllWinning.cons node_23221 (AllWinning.cons node_23696 (AllWinning.cons node_23288 (AllWinning.cons node_23698 (AllWinning.cons node_23291 (AllWinning.nil))))))

theorem node_24088 : Outcome ⟨15, 10, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 10, 15, 2⟩, ⟨13, 10, 15, 4⟩, ⟨12, 10, 15, 6⟩, ⟨11, 10, 15, 8⟩, ⟨15, 9, 15, 2⟩, ⟨15, 8, 15, 4⟩, ⟨15, 7, 15, 6⟩, ⟨15, 6, 15, 8⟩, ⟨15, 10, 14, 2⟩, ⟨15, 10, 13, 4⟩, ⟨15, 10, 12, 6⟩, ⟨15, 10, 11, 8⟩]
  exact AllWinning.cons node_23664 (AllWinning.cons node_23221 (AllWinning.cons node_22668 (AllWinning.cons node_22059 (AllWinning.cons node_23696 (AllWinning.cons node_23288 (AllWinning.cons node_22807 (AllWinning.cons node_22234 (AllWinning.cons node_23698 (AllWinning.cons node_23291 (AllWinning.cons node_22818 (AllWinning.cons node_22246 (AllWinning.nil))))))))))))

theorem node_24089 : Outcome ⟨15, 10, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 10, 15, 2⟩, ⟨13, 10, 15, 4⟩, ⟨12, 10, 15, 6⟩, ⟨11, 10, 15, 8⟩, ⟨10, 10, 15, 10⟩, ⟨9, 10, 15, 12⟩, ⟨15, 9, 15, 2⟩, ⟨15, 8, 15, 4⟩, ⟨15, 7, 15, 6⟩, ⟨15, 6, 15, 8⟩, ⟨15, 5, 15, 10⟩, ⟨15, 4, 15, 12⟩, ⟨15, 10, 14, 2⟩, ⟨15, 10, 13, 4⟩, ⟨15, 10, 12, 6⟩, ⟨15, 10, 11, 8⟩, ⟨15, 10, 10, 10⟩, ⟨15, 10, 9, 12⟩]
  exact AllWinning.cons node_23664 (AllWinning.cons node_23221 (AllWinning.cons node_22668 (AllWinning.cons node_22059 (AllWinning.cons node_21434 (AllWinning.cons node_20700 (AllWinning.cons node_23696 (AllWinning.cons node_23288 (AllWinning.cons node_22807 (AllWinning.cons node_22234 (AllWinning.cons node_21631 (AllWinning.cons node_20992 (AllWinning.cons node_23698 (AllWinning.cons node_23291 (AllWinning.cons node_22818 (AllWinning.cons node_22246 (AllWinning.cons node_21644 (AllWinning.cons node_21016 (AllWinning.nil))))))))))))))))))

theorem node_24090 : Outcome ⟨15, 10, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 10, 15, 2⟩, ⟨13, 10, 15, 4⟩, ⟨12, 10, 15, 6⟩, ⟨11, 10, 15, 8⟩, ⟨10, 10, 15, 10⟩, ⟨9, 10, 15, 12⟩, ⟨8, 10, 15, 14⟩, ⟨7, 10, 15, 16⟩, ⟨15, 9, 15, 2⟩, ⟨15, 8, 15, 4⟩, ⟨15, 7, 15, 6⟩, ⟨15, 6, 15, 8⟩, ⟨15, 5, 15, 10⟩, ⟨15, 4, 15, 12⟩, ⟨15, 3, 15, 14⟩, ⟨15, 2, 15, 16⟩, ⟨15, 10, 14, 2⟩, ⟨15, 10, 13, 4⟩, ⟨15, 10, 12, 6⟩, ⟨15, 10, 11, 8⟩, ⟨15, 10, 10, 10⟩, ⟨15, 10, 9, 12⟩, ⟨15, 10, 8, 14⟩, ⟨15, 10, 7, 16⟩]
  exact AllWinning.cons node_23664 (AllWinning.cons node_23221 (AllWinning.cons node_22668 (AllWinning.cons node_22059 (AllWinning.cons node_21434 (AllWinning.cons node_20700 (AllWinning.cons node_19925 (AllWinning.cons node_19072 (AllWinning.cons node_23696 (AllWinning.cons node_23288 (AllWinning.cons node_22807 (AllWinning.cons node_22234 (AllWinning.cons node_21631 (AllWinning.cons node_20992 (AllWinning.cons node_20251 (AllWinning.cons node_19470 (AllWinning.cons node_23698 (AllWinning.cons node_23291 (AllWinning.cons node_22818 (AllWinning.cons node_22246 (AllWinning.cons node_21644 (AllWinning.cons node_21016 (AllWinning.cons node_20269 (AllWinning.cons node_19495 (AllWinning.nil))))))))))))))))))))))))

theorem node_24091 : Outcome ⟨15, 11, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 14, 2⟩, ⟨13, 11, 14, 4⟩, ⟨15, 10, 14, 2⟩, ⟨15, 9, 14, 4⟩, ⟨15, 11, 13, 2⟩, ⟨15, 11, 12, 4⟩]
  exact AllWinning.cons node_23666 (AllWinning.cons node_23223 (AllWinning.cons node_23698 (AllWinning.cons node_23289 (AllWinning.cons node_23700 (AllWinning.cons node_23294 (AllWinning.nil))))))

theorem node_24092 : Outcome ⟨15, 11, 14, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 14, 6⟩) (by decide) node_22810

theorem node_24093 : Outcome ⟨15, 12, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 12, 13, 2⟩, ⟨13, 12, 13, 4⟩, ⟨15, 11, 13, 2⟩, ⟨15, 10, 13, 4⟩, ⟨15, 12, 12, 2⟩, ⟨15, 12, 11, 4⟩]
  exact AllWinning.cons node_23668 (AllWinning.cons node_23226 (AllWinning.cons node_23700 (AllWinning.cons node_23291 (AllWinning.cons node_23702 (AllWinning.cons node_23297 (AllWinning.nil))))))

theorem node_24094 : Outcome ⟨15, 12, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 6⟩) (by decide) node_22815

theorem node_24095 : Outcome ⟨15, 12, 13, 6⟩ true :=
  Outcome.win (q := ⟨15, 12, 7, 12⟩) (by decide) node_21023

theorem node_24096 : Outcome ⟨15, 12, 13, 16⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 22⟩) (by decide) node_16110

theorem node_24097 : Outcome ⟨15, 13, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 12, 2⟩, ⟨13, 13, 12, 4⟩, ⟨15, 12, 12, 2⟩, ⟨15, 11, 12, 4⟩, ⟨15, 13, 11, 2⟩, ⟨15, 13, 10, 4⟩]
  exact AllWinning.cons node_23671 (AllWinning.cons node_23229 (AllWinning.cons node_23702 (AllWinning.cons node_23294 (AllWinning.cons node_23704 (AllWinning.cons node_23299 (AllWinning.nil))))))

theorem node_24098 : Outcome ⟨15, 13, 12, 4⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 6⟩) (by decide) node_22826

theorem node_24099 : Outcome ⟨15, 13, 12, 6⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 12⟩) (by decide) node_21005

theorem node_24100 : Outcome ⟨15, 13, 12, 16⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 22⟩) (by decide) node_16120

theorem node_24101 : Outcome ⟨15, 14, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 11, 2⟩, ⟨13, 14, 11, 4⟩, ⟨15, 13, 11, 2⟩, ⟨15, 12, 11, 4⟩, ⟨15, 14, 10, 2⟩, ⟨15, 14, 9, 4⟩]
  exact AllWinning.cons node_23674 (AllWinning.cons node_23231 (AllWinning.cons node_23704 (AllWinning.cons node_23297 (AllWinning.cons node_23706 (AllWinning.cons node_23301 (AllWinning.nil))))))

theorem node_24102 : Outcome ⟨15, 14, 11, 4⟩ true :=
  Outcome.win (q := ⟨15, 14, 8, 6⟩) (by decide) node_22830

theorem node_24103 : Outcome ⟨15, 15, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 10, 2⟩, ⟨13, 15, 10, 4⟩, ⟨15, 14, 10, 2⟩, ⟨15, 13, 10, 4⟩, ⟨15, 15, 9, 2⟩, ⟨15, 15, 8, 4⟩]
  exact AllWinning.cons node_23676 (AllWinning.cons node_23233 (AllWinning.cons node_23706 (AllWinning.cons node_23299 (AllWinning.cons node_23708 (AllWinning.cons node_23303 (AllWinning.nil))))))

theorem node_24104 : Outcome ⟨15, 15, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 10, 2⟩, ⟨13, 15, 10, 4⟩, ⟨12, 15, 10, 6⟩, ⟨11, 15, 10, 8⟩, ⟨15, 14, 10, 2⟩, ⟨15, 13, 10, 4⟩, ⟨15, 12, 10, 6⟩, ⟨15, 11, 10, 8⟩, ⟨15, 15, 9, 2⟩, ⟨15, 15, 8, 4⟩, ⟨15, 15, 7, 6⟩, ⟨15, 15, 6, 8⟩]
  exact AllWinning.cons node_23676 (AllWinning.cons node_23233 (AllWinning.cons node_22681 (AllWinning.cons node_22073 (AllWinning.cons node_23706 (AllWinning.cons node_23299 (AllWinning.cons node_22822 (AllWinning.cons node_22249 (AllWinning.cons node_23708 (AllWinning.cons node_23303 (AllWinning.cons node_22834 (AllWinning.cons node_22259 (AllWinning.nil))))))))))))

theorem node_24105 : Outcome ⟨15, 15, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 10, 2⟩, ⟨13, 15, 10, 4⟩, ⟨12, 15, 10, 6⟩, ⟨11, 15, 10, 8⟩, ⟨10, 15, 10, 10⟩, ⟨9, 15, 10, 12⟩, ⟨15, 14, 10, 2⟩, ⟨15, 13, 10, 4⟩, ⟨15, 12, 10, 6⟩, ⟨15, 11, 10, 8⟩, ⟨15, 10, 10, 10⟩, ⟨15, 9, 10, 12⟩, ⟨15, 15, 9, 2⟩, ⟨15, 15, 8, 4⟩, ⟨15, 15, 7, 6⟩, ⟨15, 15, 6, 8⟩, ⟨15, 15, 5, 10⟩, ⟨15, 15, 4, 12⟩]
  exact AllWinning.cons node_23676 (AllWinning.cons node_23233 (AllWinning.cons node_22681 (AllWinning.cons node_22073 (AllWinning.cons node_21445 (AllWinning.cons node_20716 (AllWinning.cons node_23706 (AllWinning.cons node_23299 (AllWinning.cons node_22822 (AllWinning.cons node_22249 (AllWinning.cons node_21644 (AllWinning.cons node_21012 (AllWinning.cons node_23708 (AllWinning.cons node_23303 (AllWinning.cons node_22834 (AllWinning.cons node_22259 (AllWinning.cons node_21657 (AllWinning.cons node_21034 (AllWinning.nil))))))))))))))))))

theorem node_24106 : Outcome ⟨15, 15, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 10, 2⟩, ⟨13, 15, 10, 4⟩, ⟨12, 15, 10, 6⟩, ⟨11, 15, 10, 8⟩, ⟨10, 15, 10, 10⟩, ⟨9, 15, 10, 12⟩, ⟨8, 15, 10, 14⟩, ⟨7, 15, 10, 16⟩, ⟨15, 14, 10, 2⟩, ⟨15, 13, 10, 4⟩, ⟨15, 12, 10, 6⟩, ⟨15, 11, 10, 8⟩, ⟨15, 10, 10, 10⟩, ⟨15, 9, 10, 12⟩, ⟨15, 8, 10, 14⟩, ⟨15, 7, 10, 16⟩, ⟨15, 15, 9, 2⟩, ⟨15, 15, 8, 4⟩, ⟨15, 15, 7, 6⟩, ⟨15, 15, 6, 8⟩, ⟨15, 15, 5, 10⟩, ⟨15, 15, 4, 12⟩, ⟨15, 15, 3, 14⟩, ⟨15, 15, 2, 16⟩]
  exact AllWinning.cons node_23676 (AllWinning.cons node_23233 (AllWinning.cons node_22681 (AllWinning.cons node_22073 (AllWinning.cons node_21445 (AllWinning.cons node_20716 (AllWinning.cons node_19938 (AllWinning.cons node_19081 (AllWinning.cons node_23706 (AllWinning.cons node_23299 (AllWinning.cons node_22822 (AllWinning.cons node_22249 (AllWinning.cons node_21644 (AllWinning.cons node_21012 (AllWinning.cons node_20262 (AllWinning.cons node_19488 (AllWinning.cons node_23708 (AllWinning.cons node_23303 (AllWinning.cons node_22834 (AllWinning.cons node_22259 (AllWinning.cons node_21657 (AllWinning.cons node_21034 (AllWinning.cons node_20281 (AllWinning.cons node_19515 (AllWinning.nil))))))))))))))))))))))))

theorem node_24107 : Outcome ⟨15, 16, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 9, 2⟩, ⟨13, 16, 9, 4⟩, ⟨15, 15, 9, 2⟩, ⟨15, 14, 9, 4⟩, ⟨15, 16, 8, 2⟩, ⟨15, 16, 7, 4⟩]
  exact AllWinning.cons node_23678 (AllWinning.cons node_23236 (AllWinning.cons node_23708 (AllWinning.cons node_23301 (AllWinning.cons node_23709 (AllWinning.cons node_23305 (AllWinning.nil))))))

theorem node_24108 : Outcome ⟨15, 16, 9, 4⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 6⟩) (by decide) node_22826

theorem node_24109 : Outcome ⟨15, 16, 9, 6⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 6⟩) (by decide) node_22826

theorem node_24110 : Outcome ⟨15, 17, 8, 4⟩ true :=
  Outcome.win (q := ⟨15, 14, 8, 6⟩) (by decide) node_22830

theorem node_24111 : Outcome ⟨15, 18, 7, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 7, 4⟩) (by decide) node_23242

theorem node_24112 : Outcome ⟨15, 18, 7, 4⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 8⟩) (by decide) node_22269

theorem node_24113 : Outcome ⟨15, 19, 6, 2⟩ true :=
  Outcome.win (q := ⟨15, 19, 5, 2⟩) (by decide) node_23713

theorem node_24114 : Outcome ⟨15, 20, 5, 2⟩ true :=
  Outcome.win (q := ⟨14, 20, 5, 2⟩) (by decide) node_23686

theorem node_24115 : Outcome ⟨15, 20, 5, 16⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 24⟩) (by decide) node_15769

end RQ9F1
