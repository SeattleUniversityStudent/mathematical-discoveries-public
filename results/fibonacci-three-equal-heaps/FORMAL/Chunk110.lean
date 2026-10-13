import Chunk109
set_option autoImplicit false
namespace RQ9F1

theorem node_23044 : Outcome ⟨7, 13, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 18, 2⟩, ⟨5, 13, 18, 4⟩, ⟨4, 13, 18, 6⟩, ⟨3, 13, 18, 8⟩, ⟨7, 12, 18, 2⟩, ⟨7, 11, 18, 4⟩, ⟨7, 10, 18, 6⟩, ⟨7, 9, 18, 8⟩, ⟨7, 13, 17, 2⟩, ⟨7, 13, 16, 4⟩, ⟨7, 13, 15, 6⟩, ⟨7, 13, 14, 8⟩]
  exact AllWinning.cons node_22485 (AllWinning.cons node_21879 (AllWinning.cons node_21261 (AllWinning.cons node_20468 (AllWinning.cons node_22508 (AllWinning.cons node_21932 (AllWinning.cons node_21342 (AllWinning.cons node_20595 (AllWinning.cons node_22511 (AllWinning.cons node_21936 (AllWinning.cons node_21347 (AllWinning.cons node_20614 (AllWinning.nil))))))))))))

theorem node_23045 : Outcome ⟨7, 13, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 18, 2⟩, ⟨5, 13, 18, 4⟩, ⟨4, 13, 18, 6⟩, ⟨3, 13, 18, 8⟩, ⟨2, 13, 18, 10⟩, ⟨1, 13, 18, 12⟩, ⟨7, 12, 18, 2⟩, ⟨7, 11, 18, 4⟩, ⟨7, 10, 18, 6⟩, ⟨7, 9, 18, 8⟩, ⟨7, 8, 18, 10⟩, ⟨7, 7, 18, 12⟩, ⟨7, 13, 17, 2⟩, ⟨7, 13, 16, 4⟩, ⟨7, 13, 15, 6⟩, ⟨7, 13, 14, 8⟩, ⟨7, 13, 13, 10⟩, ⟨7, 13, 12, 12⟩]
  exact AllWinning.cons node_22485 (AllWinning.cons node_21879 (AllWinning.cons node_21261 (AllWinning.cons node_20468 (AllWinning.cons node_19746 (AllWinning.cons node_18841 (AllWinning.cons node_22508 (AllWinning.cons node_21932 (AllWinning.cons node_21342 (AllWinning.cons node_20595 (AllWinning.cons node_19892 (AllWinning.cons node_19062 (AllWinning.cons node_22511 (AllWinning.cons node_21936 (AllWinning.cons node_21347 (AllWinning.cons node_20614 (AllWinning.cons node_19900 (AllWinning.cons node_19077 (AllWinning.nil))))))))))))))))))

theorem node_23046 : Outcome ⟨7, 13, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 18, 2⟩, ⟨5, 13, 18, 4⟩, ⟨4, 13, 18, 6⟩, ⟨3, 13, 18, 8⟩, ⟨2, 13, 18, 10⟩, ⟨1, 13, 18, 12⟩, ⟨0, 13, 18, 14⟩, ⟨7, 12, 18, 2⟩, ⟨7, 11, 18, 4⟩, ⟨7, 10, 18, 6⟩, ⟨7, 9, 18, 8⟩, ⟨7, 8, 18, 10⟩, ⟨7, 7, 18, 12⟩, ⟨7, 6, 18, 14⟩, ⟨7, 5, 18, 16⟩, ⟨7, 13, 17, 2⟩, ⟨7, 13, 16, 4⟩, ⟨7, 13, 15, 6⟩, ⟨7, 13, 14, 8⟩, ⟨7, 13, 13, 10⟩, ⟨7, 13, 12, 12⟩, ⟨7, 13, 11, 14⟩, ⟨7, 13, 10, 16⟩]
  exact AllWinning.cons node_22485 (AllWinning.cons node_21879 (AllWinning.cons node_21261 (AllWinning.cons node_20468 (AllWinning.cons node_19746 (AllWinning.cons node_18841 (AllWinning.cons node_17888 (AllWinning.cons node_22508 (AllWinning.cons node_21932 (AllWinning.cons node_21342 (AllWinning.cons node_20595 (AllWinning.cons node_19892 (AllWinning.cons node_19062 (AllWinning.cons node_18142 (AllWinning.cons node_17256 (AllWinning.cons node_22511 (AllWinning.cons node_21936 (AllWinning.cons node_21347 (AllWinning.cons node_20614 (AllWinning.cons node_19900 (AllWinning.cons node_19077 (AllWinning.cons node_18165 (AllWinning.cons node_17281 (AllWinning.nil)))))))))))))))))))))))

theorem node_23047 : Outcome ⟨7, 14, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 14, 17, 8⟩) (by decide) node_20472

theorem node_23048 : Outcome ⟨7, 14, 17, 8⟩ true :=
  Outcome.win (q := ⟨3, 14, 17, 8⟩) (by decide) node_20472

theorem node_23049 : Outcome ⟨7, 15, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 8⟩) (by decide) node_20602

theorem node_23050 : Outcome ⟨7, 15, 16, 10⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 12⟩) (by decide) node_18849

theorem node_23051 : Outcome ⟨7, 16, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 8⟩) (by decide) node_20610

theorem node_23052 : Outcome ⟨7, 16, 15, 10⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 12⟩) (by decide) node_18856

theorem node_23053 : Outcome ⟨7, 17, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 17, 14, 8⟩) (by decide) node_20479

theorem node_23054 : Outcome ⟨7, 17, 14, 8⟩ true :=
  Outcome.win (q := ⟨3, 17, 14, 8⟩) (by decide) node_20479

theorem node_23055 : Outcome ⟨7, 18, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 13, 2⟩, ⟨5, 18, 13, 4⟩, ⟨7, 17, 13, 2⟩, ⟨7, 16, 13, 4⟩, ⟨7, 18, 12, 2⟩, ⟨7, 18, 11, 4⟩]
  exact AllWinning.cons node_22498 (AllWinning.cons node_21891 (AllWinning.cons node_22520 (AllWinning.cons node_21944 (AllWinning.cons node_22522 (AllWinning.cons node_21949 (AllWinning.nil))))))

theorem node_23056 : Outcome ⟨7, 18, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 13, 2⟩, ⟨5, 18, 13, 4⟩, ⟨4, 18, 13, 6⟩, ⟨3, 18, 13, 8⟩, ⟨7, 17, 13, 2⟩, ⟨7, 16, 13, 4⟩, ⟨7, 15, 13, 6⟩, ⟨7, 14, 13, 8⟩, ⟨7, 18, 12, 2⟩, ⟨7, 18, 11, 4⟩, ⟨7, 18, 10, 6⟩, ⟨7, 18, 9, 8⟩]
  exact AllWinning.cons node_22498 (AllWinning.cons node_21891 (AllWinning.cons node_21271 (AllWinning.cons node_20482 (AllWinning.cons node_22520 (AllWinning.cons node_21944 (AllWinning.cons node_21351 (AllWinning.cons node_20616 (AllWinning.cons node_22522 (AllWinning.cons node_21949 (AllWinning.cons node_21355 (AllWinning.cons node_20637 (AllWinning.nil))))))))))))

theorem node_23057 : Outcome ⟨7, 18, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 13, 2⟩, ⟨5, 18, 13, 4⟩, ⟨4, 18, 13, 6⟩, ⟨3, 18, 13, 8⟩, ⟨2, 18, 13, 10⟩, ⟨1, 18, 13, 12⟩, ⟨7, 17, 13, 2⟩, ⟨7, 16, 13, 4⟩, ⟨7, 15, 13, 6⟩, ⟨7, 14, 13, 8⟩, ⟨7, 13, 13, 10⟩, ⟨7, 12, 13, 12⟩, ⟨7, 18, 12, 2⟩, ⟨7, 18, 11, 4⟩, ⟨7, 18, 10, 6⟩, ⟨7, 18, 9, 8⟩, ⟨7, 18, 8, 10⟩, ⟨7, 18, 7, 12⟩]
  exact AllWinning.cons node_22498 (AllWinning.cons node_21891 (AllWinning.cons node_21271 (AllWinning.cons node_20482 (AllWinning.cons node_19759 (AllWinning.cons node_18862 (AllWinning.cons node_22520 (AllWinning.cons node_21944 (AllWinning.cons node_21351 (AllWinning.cons node_20616 (AllWinning.cons node_19900 (AllWinning.cons node_19075 (AllWinning.cons node_22522 (AllWinning.cons node_21949 (AllWinning.cons node_21355 (AllWinning.cons node_20637 (AllWinning.cons node_19910 (AllWinning.cons node_19091 (AllWinning.nil))))))))))))))))))

theorem node_23058 : Outcome ⟨7, 18, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 13, 2⟩, ⟨5, 18, 13, 4⟩, ⟨4, 18, 13, 6⟩, ⟨3, 18, 13, 8⟩, ⟨2, 18, 13, 10⟩, ⟨1, 18, 13, 12⟩, ⟨0, 18, 13, 14⟩, ⟨7, 17, 13, 2⟩, ⟨7, 16, 13, 4⟩, ⟨7, 15, 13, 6⟩, ⟨7, 14, 13, 8⟩, ⟨7, 13, 13, 10⟩, ⟨7, 12, 13, 12⟩, ⟨7, 11, 13, 14⟩, ⟨7, 10, 13, 16⟩, ⟨7, 18, 12, 2⟩, ⟨7, 18, 11, 4⟩, ⟨7, 18, 10, 6⟩, ⟨7, 18, 9, 8⟩, ⟨7, 18, 8, 10⟩, ⟨7, 18, 7, 12⟩, ⟨7, 18, 6, 14⟩, ⟨7, 18, 5, 16⟩]
  exact AllWinning.cons node_22498 (AllWinning.cons node_21891 (AllWinning.cons node_21271 (AllWinning.cons node_20482 (AllWinning.cons node_19759 (AllWinning.cons node_18862 (AllWinning.cons node_17900 (AllWinning.cons node_22520 (AllWinning.cons node_21944 (AllWinning.cons node_21351 (AllWinning.cons node_20616 (AllWinning.cons node_19900 (AllWinning.cons node_19075 (AllWinning.cons node_18158 (AllWinning.cons node_17271 (AllWinning.cons node_22522 (AllWinning.cons node_21949 (AllWinning.cons node_21355 (AllWinning.cons node_20637 (AllWinning.cons node_19910 (AllWinning.cons node_19091 (AllWinning.cons node_18181 (AllWinning.cons node_17296 (AllWinning.nil)))))))))))))))))))))))

theorem node_23059 : Outcome ⟨7, 19, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 19, 12, 2⟩, ⟨5, 19, 12, 4⟩, ⟨7, 18, 12, 2⟩, ⟨7, 17, 12, 4⟩, ⟨7, 19, 11, 2⟩, ⟨7, 19, 10, 4⟩]
  exact AllWinning.cons node_22499 (AllWinning.cons node_21893 (AllWinning.cons node_22522 (AllWinning.cons node_21947 (AllWinning.cons node_22525 (AllWinning.cons node_21950 (AllWinning.nil))))))

theorem node_23060 : Outcome ⟨7, 19, 12, 4⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 8⟩) (by decide) node_20621

theorem node_23061 : Outcome ⟨7, 19, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 8⟩) (by decide) node_20621

theorem node_23062 : Outcome ⟨7, 20, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 11, 2⟩, ⟨5, 20, 11, 4⟩, ⟨7, 19, 11, 2⟩, ⟨7, 18, 11, 4⟩, ⟨7, 20, 10, 2⟩, ⟨7, 20, 9, 4⟩]
  exact AllWinning.cons node_22501 (AllWinning.cons node_21896 (AllWinning.cons node_22525 (AllWinning.cons node_21949 (AllWinning.cons node_22527 (AllWinning.cons node_21952 (AllWinning.nil))))))

theorem node_23063 : Outcome ⟨7, 20, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 8⟩) (by decide) node_20628

theorem node_23064 : Outcome ⟨7, 20, 11, 10⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 8⟩) (by decide) node_20628

theorem node_23065 : Outcome ⟨8, 10, 20, 4⟩ true :=
  Outcome.win (q := ⟨8, 7, 20, 6⟩) (by decide) node_21363

theorem node_23066 : Outcome ⟨8, 11, 19, 4⟩ true :=
  Outcome.win (q := ⟨8, 11, 17, 4⟩) (by decide) node_21959

theorem node_23067 : Outcome ⟨8, 12, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 18, 2⟩, ⟨6, 12, 18, 4⟩, ⟨8, 11, 18, 2⟩, ⟨8, 10, 18, 4⟩, ⟨8, 12, 17, 2⟩, ⟨8, 12, 16, 4⟩]
  exact AllWinning.cons node_22508 (AllWinning.cons node_21902 (AllWinning.cons node_22532 (AllWinning.cons node_21956 (AllWinning.cons node_22533 (AllWinning.cons node_21963 (AllWinning.nil))))))

theorem node_23068 : Outcome ⟨8, 12, 18, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 8⟩) (by decide) node_20648

theorem node_23069 : Outcome ⟨8, 12, 18, 12⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 8⟩) (by decide) node_20648

theorem node_23070 : Outcome ⟨8, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 11, 17, 4⟩) (by decide) node_21959

theorem node_23071 : Outcome ⟨8, 13, 17, 8⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 14⟩) (by decide) node_17922

theorem node_23072 : Outcome ⟨8, 14, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 14, 16, 2⟩) (by decide) node_22513

theorem node_23073 : Outcome ⟨8, 15, 15, 4⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 2⟩) (by decide) node_22539

theorem node_23074 : Outcome ⟨8, 16, 14, 4⟩ true :=
  Outcome.win (q := ⟨7, 16, 14, 2⟩) (by decide) node_22517

theorem node_23075 : Outcome ⟨8, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 11, 4⟩) (by decide) node_21979

theorem node_23076 : Outcome ⟨8, 17, 13, 8⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 14⟩) (by decide) node_17939

theorem node_23077 : Outcome ⟨8, 18, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 18, 12, 2⟩, ⟨6, 18, 12, 4⟩, ⟨8, 17, 12, 2⟩, ⟨8, 16, 12, 4⟩, ⟨8, 18, 11, 2⟩, ⟨8, 18, 10, 4⟩]
  exact AllWinning.cons node_22522 (AllWinning.cons node_21921 (AllWinning.cons node_22552 (AllWinning.cons node_21975 (AllWinning.cons node_22555 (AllWinning.cons node_21982 (AllWinning.nil))))))

theorem node_23078 : Outcome ⟨8, 18, 12, 4⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 8⟩) (by decide) node_20677

theorem node_23079 : Outcome ⟨8, 18, 12, 12⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 8⟩) (by decide) node_20677

theorem node_23080 : Outcome ⟨8, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 11, 4⟩) (by decide) node_21979

theorem node_23081 : Outcome ⟨8, 20, 10, 4⟩ true :=
  Outcome.win (q := ⟨8, 20, 7, 6⟩) (by decide) node_21389

theorem node_23082 : Outcome ⟨9, 9, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 20, 2⟩, ⟨7, 9, 20, 4⟩, ⟨9, 8, 20, 2⟩, ⟨9, 7, 20, 4⟩, ⟨9, 9, 19, 2⟩, ⟨9, 9, 18, 4⟩]
  exact AllWinning.cons node_22529 (AllWinning.cons node_21928 (AllWinning.cons node_22559 (AllWinning.cons node_21986 (AllWinning.cons node_22561 (AllWinning.cons node_21989 (AllWinning.nil))))))

theorem node_23083 : Outcome ⟨9, 9, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 20, 2⟩, ⟨7, 9, 20, 4⟩, ⟨6, 9, 20, 6⟩, ⟨5, 9, 20, 8⟩, ⟨9, 8, 20, 2⟩, ⟨9, 7, 20, 4⟩, ⟨9, 6, 20, 6⟩, ⟨9, 5, 20, 8⟩, ⟨9, 9, 19, 2⟩, ⟨9, 9, 18, 4⟩, ⟨9, 9, 17, 6⟩, ⟨9, 9, 16, 8⟩]
  exact AllWinning.cons node_22529 (AllWinning.cons node_21928 (AllWinning.cons node_21308 (AllWinning.cons node_20515 (AllWinning.cons node_22559 (AllWinning.cons node_21986 (AllWinning.cons node_21392 (AllWinning.cons node_20686 (AllWinning.cons node_22561 (AllWinning.cons node_21989 (AllWinning.cons node_21397 (AllWinning.cons node_20695 (AllWinning.nil))))))))))))

theorem node_23084 : Outcome ⟨9, 9, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 20, 2⟩, ⟨7, 9, 20, 4⟩, ⟨6, 9, 20, 6⟩, ⟨5, 9, 20, 8⟩, ⟨4, 9, 20, 10⟩, ⟨3, 9, 20, 12⟩, ⟨9, 8, 20, 2⟩, ⟨9, 7, 20, 4⟩, ⟨9, 6, 20, 6⟩, ⟨9, 5, 20, 8⟩, ⟨9, 4, 20, 10⟩, ⟨9, 3, 20, 12⟩, ⟨9, 9, 19, 2⟩, ⟨9, 9, 18, 4⟩, ⟨9, 9, 17, 6⟩, ⟨9, 9, 16, 8⟩, ⟨9, 9, 15, 10⟩, ⟨9, 9, 14, 12⟩]
  exact AllWinning.cons node_22529 (AllWinning.cons node_21928 (AllWinning.cons node_21308 (AllWinning.cons node_20515 (AllWinning.cons node_19792 (AllWinning.cons node_18902 (AllWinning.cons node_22559 (AllWinning.cons node_21986 (AllWinning.cons node_21392 (AllWinning.cons node_20686 (AllWinning.cons node_19950 (AllWinning.cons node_19145 (AllWinning.cons node_22561 (AllWinning.cons node_21989 (AllWinning.cons node_21397 (AllWinning.cons node_20695 (AllWinning.cons node_19959 (AllWinning.cons node_19164 (AllWinning.nil))))))))))))))))))

theorem node_23085 : Outcome ⟨9, 9, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 20, 2⟩, ⟨7, 9, 20, 4⟩, ⟨6, 9, 20, 6⟩, ⟨5, 9, 20, 8⟩, ⟨4, 9, 20, 10⟩, ⟨3, 9, 20, 12⟩, ⟨2, 9, 20, 14⟩, ⟨1, 9, 20, 16⟩, ⟨9, 8, 20, 2⟩, ⟨9, 7, 20, 4⟩, ⟨9, 6, 20, 6⟩, ⟨9, 5, 20, 8⟩, ⟨9, 4, 20, 10⟩, ⟨9, 3, 20, 12⟩, ⟨9, 2, 20, 14⟩, ⟨9, 1, 20, 16⟩, ⟨9, 9, 19, 2⟩, ⟨9, 9, 18, 4⟩, ⟨9, 9, 17, 6⟩, ⟨9, 9, 16, 8⟩, ⟨9, 9, 15, 10⟩, ⟨9, 9, 14, 12⟩, ⟨9, 9, 13, 14⟩, ⟨9, 9, 12, 16⟩]
  exact AllWinning.cons node_22529 (AllWinning.cons node_21928 (AllWinning.cons node_21308 (AllWinning.cons node_20515 (AllWinning.cons node_19792 (AllWinning.cons node_18902 (AllWinning.cons node_17953 (AllWinning.cons node_17014 (AllWinning.cons node_22559 (AllWinning.cons node_21986 (AllWinning.cons node_21392 (AllWinning.cons node_20686 (AllWinning.cons node_19950 (AllWinning.cons node_19145 (AllWinning.cons node_18245 (AllWinning.cons node_17355 (AllWinning.cons node_22561 (AllWinning.cons node_21989 (AllWinning.cons node_21397 (AllWinning.cons node_20695 (AllWinning.cons node_19959 (AllWinning.cons node_19164 (AllWinning.cons node_18265 (AllWinning.cons node_17376 (AllWinning.nil))))))))))))))))))))))))

theorem node_23086 : Outcome ⟨9, 9, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 20, 2⟩, ⟨7, 9, 20, 4⟩, ⟨6, 9, 20, 6⟩, ⟨5, 9, 20, 8⟩, ⟨4, 9, 20, 10⟩, ⟨3, 9, 20, 12⟩, ⟨2, 9, 20, 14⟩, ⟨1, 9, 20, 16⟩, ⟨0, 9, 20, 18⟩, ⟨9, 8, 20, 2⟩, ⟨9, 7, 20, 4⟩, ⟨9, 6, 20, 6⟩, ⟨9, 5, 20, 8⟩, ⟨9, 4, 20, 10⟩, ⟨9, 3, 20, 12⟩, ⟨9, 2, 20, 14⟩, ⟨9, 1, 20, 16⟩, ⟨9, 0, 20, 18⟩, ⟨9, 9, 19, 2⟩, ⟨9, 9, 18, 4⟩, ⟨9, 9, 17, 6⟩, ⟨9, 9, 16, 8⟩, ⟨9, 9, 15, 10⟩, ⟨9, 9, 14, 12⟩, ⟨9, 9, 13, 14⟩, ⟨9, 9, 12, 16⟩, ⟨9, 9, 11, 18⟩, ⟨9, 9, 10, 20⟩]
  exact AllWinning.cons node_22529 (AllWinning.cons node_21928 (AllWinning.cons node_21308 (AllWinning.cons node_20515 (AllWinning.cons node_19792 (AllWinning.cons node_18902 (AllWinning.cons node_17953 (AllWinning.cons node_17014 (AllWinning.cons node_15903 (AllWinning.cons node_22559 (AllWinning.cons node_21986 (AllWinning.cons node_21392 (AllWinning.cons node_20686 (AllWinning.cons node_19950 (AllWinning.cons node_19145 (AllWinning.cons node_18245 (AllWinning.cons node_17355 (AllWinning.cons node_16402 (AllWinning.cons node_22561 (AllWinning.cons node_21989 (AllWinning.cons node_21397 (AllWinning.cons node_20695 (AllWinning.cons node_19959 (AllWinning.cons node_19164 (AllWinning.cons node_18265 (AllWinning.cons node_17376 (AllWinning.cons node_16441 (AllWinning.cons node_15417 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_23087 : Outcome ⟨9, 9, 20, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 20, 2⟩, ⟨7, 9, 20, 4⟩, ⟨6, 9, 20, 6⟩, ⟨5, 9, 20, 8⟩, ⟨4, 9, 20, 10⟩, ⟨3, 9, 20, 12⟩, ⟨2, 9, 20, 14⟩, ⟨1, 9, 20, 16⟩, ⟨0, 9, 20, 18⟩, ⟨9, 8, 20, 2⟩, ⟨9, 7, 20, 4⟩, ⟨9, 6, 20, 6⟩, ⟨9, 5, 20, 8⟩, ⟨9, 4, 20, 10⟩, ⟨9, 3, 20, 12⟩, ⟨9, 2, 20, 14⟩, ⟨9, 1, 20, 16⟩, ⟨9, 0, 20, 18⟩, ⟨9, 9, 19, 2⟩, ⟨9, 9, 18, 4⟩, ⟨9, 9, 17, 6⟩, ⟨9, 9, 16, 8⟩, ⟨9, 9, 15, 10⟩, ⟨9, 9, 14, 12⟩, ⟨9, 9, 13, 14⟩, ⟨9, 9, 12, 16⟩, ⟨9, 9, 11, 18⟩, ⟨9, 9, 10, 20⟩, ⟨9, 9, 9, 22⟩, ⟨9, 9, 8, 24⟩]
  exact AllWinning.cons node_22529 (AllWinning.cons node_21928 (AllWinning.cons node_21308 (AllWinning.cons node_20515 (AllWinning.cons node_19792 (AllWinning.cons node_18902 (AllWinning.cons node_17953 (AllWinning.cons node_17014 (AllWinning.cons node_15903 (AllWinning.cons node_22559 (AllWinning.cons node_21986 (AllWinning.cons node_21392 (AllWinning.cons node_20686 (AllWinning.cons node_19950 (AllWinning.cons node_19145 (AllWinning.cons node_18245 (AllWinning.cons node_17355 (AllWinning.cons node_16402 (AllWinning.cons node_22561 (AllWinning.cons node_21989 (AllWinning.cons node_21397 (AllWinning.cons node_20695 (AllWinning.cons node_19959 (AllWinning.cons node_19164 (AllWinning.cons node_18265 (AllWinning.cons node_17376 (AllWinning.cons node_16441 (AllWinning.cons node_15417 (AllWinning.cons node_14487 (AllWinning.cons node_13519 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_23088 : Outcome ⟨9, 10, 19, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 8⟩) (by decide) node_20519

theorem node_23089 : Outcome ⟨9, 10, 19, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 8⟩) (by decide) node_20519

theorem node_23090 : Outcome ⟨9, 11, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 11, 18, 2⟩, ⟨7, 11, 18, 4⟩, ⟨9, 10, 18, 2⟩, ⟨9, 9, 18, 4⟩, ⟨9, 11, 17, 2⟩, ⟨9, 11, 16, 4⟩]
  exact AllWinning.cons node_22532 (AllWinning.cons node_21932 (AllWinning.cons node_22562 (AllWinning.cons node_21989 (AllWinning.cons node_22564 (AllWinning.cons node_21993 (AllWinning.nil))))))

theorem node_23091 : Outcome ⟨9, 11, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 11, 18, 2⟩, ⟨7, 11, 18, 4⟩, ⟨6, 11, 18, 6⟩, ⟨5, 11, 18, 8⟩, ⟨9, 10, 18, 2⟩, ⟨9, 9, 18, 4⟩, ⟨9, 8, 18, 6⟩, ⟨9, 7, 18, 8⟩, ⟨9, 11, 17, 2⟩, ⟨9, 11, 16, 4⟩, ⟨9, 11, 15, 6⟩, ⟨9, 11, 14, 8⟩]
  exact AllWinning.cons node_22532 (AllWinning.cons node_21932 (AllWinning.cons node_21312 (AllWinning.cons node_20523 (AllWinning.cons node_22562 (AllWinning.cons node_21989 (AllWinning.cons node_21395 (AllWinning.cons node_20689 (AllWinning.cons node_22564 (AllWinning.cons node_21993 (AllWinning.cons node_21405 (AllWinning.cons node_20703 (AllWinning.nil))))))))))))

theorem node_23092 : Outcome ⟨9, 11, 18, 8⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 10⟩) (by decide) node_19799

theorem node_23093 : Outcome ⟨9, 12, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 12, 17, 2⟩, ⟨7, 12, 17, 4⟩, ⟨6, 12, 17, 6⟩, ⟨5, 12, 17, 8⟩, ⟨9, 11, 17, 2⟩, ⟨9, 10, 17, 4⟩, ⟨9, 9, 17, 6⟩, ⟨9, 8, 17, 8⟩, ⟨9, 12, 16, 2⟩, ⟨9, 12, 15, 4⟩, ⟨9, 12, 14, 6⟩, ⟨9, 12, 13, 8⟩]
  exact AllWinning.cons node_22533 (AllWinning.cons node_21933 (AllWinning.cons node_21314 (AllWinning.cons node_20525 (AllWinning.cons node_22564 (AllWinning.cons node_21991 (AllWinning.cons node_21397 (AllWinning.cons node_20691 (AllWinning.cons node_22566 (AllWinning.cons node_21997 (AllWinning.cons node_21407 (AllWinning.cons node_20706 (AllWinning.nil))))))))))))

theorem node_23094 : Outcome ⟨9, 12, 17, 8⟩ true :=
  Outcome.win (q := ⟨9, 6, 17, 12⟩) (by decide) node_19155

theorem node_23095 : Outcome ⟨9, 13, 16, 4⟩ true :=
  Outcome.win (q := ⟨8, 13, 16, 2⟩) (by decide) node_22536

theorem node_23096 : Outcome ⟨9, 13, 16, 8⟩ true :=
  Outcome.win (q := ⟨8, 13, 16, 2⟩) (by decide) node_22536

theorem node_23097 : Outcome ⟨9, 13, 16, 14⟩ true :=
  Outcome.win (q := ⟨9, 4, 16, 18⟩) (by decide) node_16419

theorem node_23098 : Outcome ⟨9, 14, 15, 4⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 2⟩) (by decide) node_22539

theorem node_23099 : Outcome ⟨9, 14, 15, 8⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 2⟩) (by decide) node_22539

theorem node_23100 : Outcome ⟨9, 15, 14, 4⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 2⟩) (by decide) node_22544

theorem node_23101 : Outcome ⟨9, 15, 14, 8⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 2⟩) (by decide) node_22544

theorem node_23102 : Outcome ⟨9, 16, 13, 4⟩ true :=
  Outcome.win (q := ⟨8, 16, 13, 2⟩) (by decide) node_22549

theorem node_23103 : Outcome ⟨9, 16, 13, 8⟩ true :=
  Outcome.win (q := ⟨8, 16, 13, 2⟩) (by decide) node_22549

theorem node_23104 : Outcome ⟨9, 16, 13, 14⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 18⟩) (by decide) node_16435

theorem node_23105 : Outcome ⟨9, 17, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 17, 12, 2⟩, ⟨7, 17, 12, 4⟩, ⟨6, 17, 12, 6⟩, ⟨5, 17, 12, 8⟩, ⟨9, 16, 12, 2⟩, ⟨9, 15, 12, 4⟩, ⟨9, 14, 12, 6⟩, ⟨9, 13, 12, 8⟩, ⟨9, 17, 11, 2⟩, ⟨9, 17, 10, 4⟩, ⟨9, 17, 9, 6⟩, ⟨9, 17, 8, 8⟩]
  exact AllWinning.cons node_22552 (AllWinning.cons node_21947 (AllWinning.cons node_21329 (AllWinning.cons node_20535 (AllWinning.cons node_22583 (AllWinning.cons node_22003 (AllWinning.cons node_21411 (AllWinning.cons node_20709 (AllWinning.cons node_22587 (AllWinning.cons node_22008 (AllWinning.cons node_21420 (AllWinning.cons node_20722 (AllWinning.nil))))))))))))

theorem node_23106 : Outcome ⟨9, 17, 12, 8⟩ true :=
  Outcome.win (q := ⟨9, 17, 6, 12⟩) (by decide) node_19192

theorem node_23107 : Outcome ⟨9, 18, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 18, 11, 2⟩, ⟨7, 18, 11, 4⟩, ⟨9, 17, 11, 2⟩, ⟨9, 16, 11, 4⟩, ⟨9, 18, 10, 2⟩, ⟨9, 18, 9, 4⟩]
  exact AllWinning.cons node_22555 (AllWinning.cons node_21949 (AllWinning.cons node_22587 (AllWinning.cons node_22004 (AllWinning.cons node_22589 (AllWinning.cons node_22011 (AllWinning.nil))))))

theorem node_23108 : Outcome ⟨9, 18, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 18, 11, 2⟩, ⟨7, 18, 11, 4⟩, ⟨6, 18, 11, 6⟩, ⟨5, 18, 11, 8⟩, ⟨9, 17, 11, 2⟩, ⟨9, 16, 11, 4⟩, ⟨9, 15, 11, 6⟩, ⟨9, 14, 11, 8⟩, ⟨9, 18, 10, 2⟩, ⟨9, 18, 9, 4⟩, ⟨9, 18, 8, 6⟩, ⟨9, 18, 7, 8⟩]
  exact AllWinning.cons node_22555 (AllWinning.cons node_21949 (AllWinning.cons node_21332 (AllWinning.cons node_20537 (AllWinning.cons node_22587 (AllWinning.cons node_22004 (AllWinning.cons node_21414 (AllWinning.cons node_20712 (AllWinning.cons node_22589 (AllWinning.cons node_22011 (AllWinning.cons node_21423 (AllWinning.cons node_20725 (AllWinning.nil))))))))))))

theorem node_23109 : Outcome ⟨9, 18, 11, 8⟩ true :=
  Outcome.win (q := ⟨4, 18, 11, 10⟩) (by decide) node_19820

theorem node_23110 : Outcome ⟨9, 19, 10, 4⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 8⟩) (by decide) node_20541

theorem node_23111 : Outcome ⟨9, 19, 10, 8⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 8⟩) (by decide) node_20541

theorem node_23112 : Outcome ⟨9, 20, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 9, 2⟩, ⟨7, 20, 9, 4⟩, ⟨9, 19, 9, 2⟩, ⟨9, 18, 9, 4⟩, ⟨9, 20, 8, 2⟩, ⟨9, 20, 7, 4⟩]
  exact AllWinning.cons node_22557 (AllWinning.cons node_21952 (AllWinning.cons node_22591 (AllWinning.cons node_22011 (AllWinning.cons node_22592 (AllWinning.cons node_22013 (AllWinning.nil))))))

theorem node_23113 : Outcome ⟨9, 20, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 9, 2⟩, ⟨7, 20, 9, 4⟩, ⟨6, 20, 9, 6⟩, ⟨5, 20, 9, 8⟩, ⟨9, 19, 9, 2⟩, ⟨9, 18, 9, 4⟩, ⟨9, 17, 9, 6⟩, ⟨9, 16, 9, 8⟩, ⟨9, 20, 8, 2⟩, ⟨9, 20, 7, 4⟩, ⟨9, 20, 6, 6⟩, ⟨9, 20, 5, 8⟩]
  exact AllWinning.cons node_22557 (AllWinning.cons node_21952 (AllWinning.cons node_21334 (AllWinning.cons node_20545 (AllWinning.cons node_22591 (AllWinning.cons node_22011 (AllWinning.cons node_21420 (AllWinning.cons node_20719 (AllWinning.cons node_22592 (AllWinning.cons node_22013 (AllWinning.cons node_21424 (AllWinning.cons node_20728 (AllWinning.nil))))))))))))

theorem node_23114 : Outcome ⟨9, 20, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 9, 2⟩, ⟨7, 20, 9, 4⟩, ⟨6, 20, 9, 6⟩, ⟨5, 20, 9, 8⟩, ⟨4, 20, 9, 10⟩, ⟨3, 20, 9, 12⟩, ⟨9, 19, 9, 2⟩, ⟨9, 18, 9, 4⟩, ⟨9, 17, 9, 6⟩, ⟨9, 16, 9, 8⟩, ⟨9, 15, 9, 10⟩, ⟨9, 14, 9, 12⟩, ⟨9, 20, 8, 2⟩, ⟨9, 20, 7, 4⟩, ⟨9, 20, 6, 6⟩, ⟨9, 20, 5, 8⟩, ⟨9, 20, 4, 10⟩, ⟨9, 20, 3, 12⟩]
  exact AllWinning.cons node_22557 (AllWinning.cons node_21952 (AllWinning.cons node_21334 (AllWinning.cons node_20545 (AllWinning.cons node_19826 (AllWinning.cons node_18929 (AllWinning.cons node_22591 (AllWinning.cons node_22011 (AllWinning.cons node_21420 (AllWinning.cons node_20719 (AllWinning.cons node_19980 (AllWinning.cons node_19182 (AllWinning.cons node_22592 (AllWinning.cons node_22013 (AllWinning.cons node_21424 (AllWinning.cons node_20728 (AllWinning.cons node_19987 (AllWinning.cons node_19200 (AllWinning.nil))))))))))))))))))

theorem node_23115 : Outcome ⟨9, 20, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 9, 2⟩, ⟨7, 20, 9, 4⟩, ⟨6, 20, 9, 6⟩, ⟨5, 20, 9, 8⟩, ⟨4, 20, 9, 10⟩, ⟨3, 20, 9, 12⟩, ⟨2, 20, 9, 14⟩, ⟨1, 20, 9, 16⟩, ⟨9, 19, 9, 2⟩, ⟨9, 18, 9, 4⟩, ⟨9, 17, 9, 6⟩, ⟨9, 16, 9, 8⟩, ⟨9, 15, 9, 10⟩, ⟨9, 14, 9, 12⟩, ⟨9, 13, 9, 14⟩, ⟨9, 12, 9, 16⟩, ⟨9, 20, 8, 2⟩, ⟨9, 20, 7, 4⟩, ⟨9, 20, 6, 6⟩, ⟨9, 20, 5, 8⟩, ⟨9, 20, 4, 10⟩, ⟨9, 20, 3, 12⟩, ⟨9, 20, 2, 14⟩, ⟨9, 20, 1, 16⟩]
  exact AllWinning.cons node_22557 (AllWinning.cons node_21952 (AllWinning.cons node_21334 (AllWinning.cons node_20545 (AllWinning.cons node_19826 (AllWinning.cons node_18929 (AllWinning.cons node_17973 (AllWinning.cons node_17045 (AllWinning.cons node_22591 (AllWinning.cons node_22011 (AllWinning.cons node_21420 (AllWinning.cons node_20719 (AllWinning.cons node_19980 (AllWinning.cons node_19182 (AllWinning.cons node_18280 (AllWinning.cons node_17382 (AllWinning.cons node_22592 (AllWinning.cons node_22013 (AllWinning.cons node_21424 (AllWinning.cons node_20728 (AllWinning.cons node_19987 (AllWinning.cons node_19200 (AllWinning.cons node_18299 (AllWinning.cons node_17402 (AllWinning.nil))))))))))))))))))))))))

theorem node_23116 : Outcome ⟨9, 20, 9, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 9, 2⟩, ⟨7, 20, 9, 4⟩, ⟨6, 20, 9, 6⟩, ⟨5, 20, 9, 8⟩, ⟨4, 20, 9, 10⟩, ⟨3, 20, 9, 12⟩, ⟨2, 20, 9, 14⟩, ⟨1, 20, 9, 16⟩, ⟨0, 20, 9, 18⟩, ⟨9, 19, 9, 2⟩, ⟨9, 18, 9, 4⟩, ⟨9, 17, 9, 6⟩, ⟨9, 16, 9, 8⟩, ⟨9, 15, 9, 10⟩, ⟨9, 14, 9, 12⟩, ⟨9, 13, 9, 14⟩, ⟨9, 12, 9, 16⟩, ⟨9, 11, 9, 18⟩, ⟨9, 10, 9, 20⟩, ⟨9, 20, 8, 2⟩, ⟨9, 20, 7, 4⟩, ⟨9, 20, 6, 6⟩, ⟨9, 20, 5, 8⟩, ⟨9, 20, 4, 10⟩, ⟨9, 20, 3, 12⟩, ⟨9, 20, 2, 14⟩, ⟨9, 20, 1, 16⟩, ⟨9, 20, 0, 18⟩]
  exact AllWinning.cons node_22557 (AllWinning.cons node_21952 (AllWinning.cons node_21334 (AllWinning.cons node_20545 (AllWinning.cons node_19826 (AllWinning.cons node_18929 (AllWinning.cons node_17973 (AllWinning.cons node_17045 (AllWinning.cons node_15940 (AllWinning.cons node_22591 (AllWinning.cons node_22011 (AllWinning.cons node_21420 (AllWinning.cons node_20719 (AllWinning.cons node_19980 (AllWinning.cons node_19182 (AllWinning.cons node_18280 (AllWinning.cons node_17382 (AllWinning.cons node_16448 (AllWinning.cons node_15420 (AllWinning.cons node_22592 (AllWinning.cons node_22013 (AllWinning.cons node_21424 (AllWinning.cons node_20728 (AllWinning.cons node_19987 (AllWinning.cons node_19200 (AllWinning.cons node_18299 (AllWinning.cons node_17402 (AllWinning.cons node_16484 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_23117 : Outcome ⟨9, 20, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 9, 2⟩, ⟨7, 20, 9, 4⟩, ⟨6, 20, 9, 6⟩, ⟨5, 20, 9, 8⟩, ⟨4, 20, 9, 10⟩, ⟨3, 20, 9, 12⟩, ⟨2, 20, 9, 14⟩, ⟨1, 20, 9, 16⟩, ⟨0, 20, 9, 18⟩, ⟨9, 19, 9, 2⟩, ⟨9, 18, 9, 4⟩, ⟨9, 17, 9, 6⟩, ⟨9, 16, 9, 8⟩, ⟨9, 15, 9, 10⟩, ⟨9, 14, 9, 12⟩, ⟨9, 13, 9, 14⟩, ⟨9, 12, 9, 16⟩, ⟨9, 11, 9, 18⟩, ⟨9, 10, 9, 20⟩, ⟨9, 9, 9, 22⟩, ⟨9, 8, 9, 24⟩, ⟨9, 20, 8, 2⟩, ⟨9, 20, 7, 4⟩, ⟨9, 20, 6, 6⟩, ⟨9, 20, 5, 8⟩, ⟨9, 20, 4, 10⟩, ⟨9, 20, 3, 12⟩, ⟨9, 20, 2, 14⟩, ⟨9, 20, 1, 16⟩, ⟨9, 20, 0, 18⟩]
  exact AllWinning.cons node_22557 (AllWinning.cons node_21952 (AllWinning.cons node_21334 (AllWinning.cons node_20545 (AllWinning.cons node_19826 (AllWinning.cons node_18929 (AllWinning.cons node_17973 (AllWinning.cons node_17045 (AllWinning.cons node_15940 (AllWinning.cons node_22591 (AllWinning.cons node_22011 (AllWinning.cons node_21420 (AllWinning.cons node_20719 (AllWinning.cons node_19980 (AllWinning.cons node_19182 (AllWinning.cons node_18280 (AllWinning.cons node_17382 (AllWinning.cons node_16448 (AllWinning.cons node_15420 (AllWinning.cons node_14487 (AllWinning.cons node_13516 (AllWinning.cons node_22592 (AllWinning.cons node_22013 (AllWinning.cons node_21424 (AllWinning.cons node_20728 (AllWinning.cons node_19987 (AllWinning.cons node_19200 (AllWinning.cons node_18299 (AllWinning.cons node_17402 (AllWinning.cons node_16484 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_23118 : Outcome ⟨10, 8, 20, 4⟩ true :=
  Outcome.win (q := ⟨7, 8, 20, 6⟩) (by decide) node_21337

theorem node_23119 : Outcome ⟨10, 9, 19, 4⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 8⟩) (by decide) node_20734

theorem node_23120 : Outcome ⟨10, 9, 19, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 8⟩) (by decide) node_20734

theorem node_23121 : Outcome ⟨10, 10, 18, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 18, 8⟩) (by decide) node_20552

theorem node_23122 : Outcome ⟨10, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 11, 17, 4⟩) (by decide) node_21959

theorem node_23123 : Outcome ⟨10, 11, 17, 8⟩ true :=
  Outcome.win (q := ⟨8, 11, 17, 4⟩) (by decide) node_21959

theorem node_23124 : Outcome ⟨10, 12, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 12, 16, 2⟩, ⟨8, 12, 16, 4⟩, ⟨10, 11, 16, 2⟩, ⟨10, 10, 16, 4⟩, ⟨10, 12, 15, 2⟩, ⟨10, 12, 14, 4⟩]
  exact AllWinning.cons node_22566 (AllWinning.cons node_21963 (AllWinning.cons node_22600 (AllWinning.cons node_22022 (AllWinning.cons node_22602 (AllWinning.cons node_22027 (AllWinning.nil))))))

theorem node_23125 : Outcome ⟨10, 12, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 8⟩) (by decide) node_20559

theorem node_23126 : Outcome ⟨10, 12, 16, 10⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 8⟩) (by decide) node_20559

theorem node_23127 : Outcome ⟨10, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 2⟩) (by decide) node_22570

theorem node_23128 : Outcome ⟨10, 13, 15, 8⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 2⟩) (by decide) node_22570

theorem node_23129 : Outcome ⟨10, 14, 14, 4⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 2⟩) (by decide) node_22574

theorem node_23130 : Outcome ⟨10, 14, 14, 8⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 2⟩) (by decide) node_22574

theorem node_23131 : Outcome ⟨10, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 2⟩) (by decide) node_22579

theorem node_23132 : Outcome ⟨10, 15, 13, 8⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 2⟩) (by decide) node_22579

theorem node_23133 : Outcome ⟨10, 16, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 16, 12, 2⟩, ⟨8, 16, 12, 4⟩, ⟨10, 15, 12, 2⟩, ⟨10, 14, 12, 4⟩, ⟨10, 16, 11, 2⟩, ⟨10, 16, 10, 4⟩]
  exact AllWinning.cons node_22583 (AllWinning.cons node_21975 (AllWinning.cons node_22611 (AllWinning.cons node_22032 (AllWinning.cons node_22614 (AllWinning.cons node_22037 (AllWinning.nil))))))

theorem node_23134 : Outcome ⟨10, 16, 12, 4⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 8⟩) (by decide) node_20575

theorem node_23135 : Outcome ⟨10, 16, 12, 10⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 8⟩) (by decide) node_20575

theorem node_23136 : Outcome ⟨10, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 11, 4⟩) (by decide) node_21979

theorem node_23137 : Outcome ⟨10, 17, 11, 8⟩ true :=
  Outcome.win (q := ⟨8, 17, 11, 4⟩) (by decide) node_21979

theorem node_23138 : Outcome ⟨10, 18, 10, 4⟩ true :=
  Outcome.win (q := ⟨6, 18, 10, 8⟩) (by decide) node_20584

theorem node_23139 : Outcome ⟨10, 19, 9, 4⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 8⟩) (by decide) node_20777

theorem node_23140 : Outcome ⟨10, 19, 9, 8⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 8⟩) (by decide) node_20777

theorem node_23141 : Outcome ⟨10, 20, 8, 4⟩ true :=
  Outcome.win (q := ⟨7, 20, 8, 6⟩) (by decide) node_21357

theorem node_23142 : Outcome ⟨11, 7, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 7, 20, 2⟩, ⟨9, 7, 20, 4⟩, ⟨11, 6, 20, 2⟩, ⟨11, 5, 20, 4⟩, ⟨11, 7, 19, 2⟩, ⟨11, 7, 18, 4⟩]
  exact AllWinning.cons node_22593 (AllWinning.cons node_21986 (AllWinning.cons node_22623 (AllWinning.cons node_22046 (AllWinning.cons node_22626 (AllWinning.cons node_22050 (AllWinning.nil))))))

theorem node_23143 : Outcome ⟨11, 7, 20, 8⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 8⟩) (by decide) node_20791

theorem node_23144 : Outcome ⟨11, 8, 19, 4⟩ true :=
  Outcome.win (q := ⟨11, 8, 17, 4⟩) (by decide) node_22052

theorem node_23145 : Outcome ⟨11, 9, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 9, 18, 2⟩, ⟨9, 9, 18, 4⟩, ⟨11, 8, 18, 2⟩, ⟨11, 7, 18, 4⟩, ⟨11, 9, 17, 2⟩, ⟨11, 9, 16, 4⟩]
  exact AllWinning.cons node_22595 (AllWinning.cons node_21989 (AllWinning.cons node_22628 (AllWinning.cons node_22050 (AllWinning.cons node_22629 (AllWinning.cons node_22054 (AllWinning.nil))))))

theorem node_23146 : Outcome ⟨11, 9, 18, 8⟩ true :=
  Outcome.win (q := ⟨11, 4, 18, 10⟩) (by decide) node_20046

theorem node_23147 : Outcome ⟨11, 10, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 8, 17, 4⟩) (by decide) node_22052

theorem node_23148 : Outcome ⟨11, 10, 17, 8⟩ true :=
  Outcome.win (q := ⟨11, 8, 17, 4⟩) (by decide) node_22052

theorem node_23149 : Outcome ⟨11, 11, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 16, 2⟩, ⟨9, 11, 16, 4⟩, ⟨11, 10, 16, 2⟩, ⟨11, 9, 16, 4⟩, ⟨11, 11, 15, 2⟩, ⟨11, 11, 14, 4⟩]
  exact AllWinning.cons node_22600 (AllWinning.cons node_21993 (AllWinning.cons node_22631 (AllWinning.cons node_22054 (AllWinning.cons node_22633 (AllWinning.cons node_22060 (AllWinning.nil))))))

theorem node_23150 : Outcome ⟨11, 11, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 8⟩) (by decide) node_20602

theorem node_23151 : Outcome ⟨11, 11, 16, 8⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 8⟩) (by decide) node_20602

theorem node_23152 : Outcome ⟨11, 12, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 12, 15, 2⟩, ⟨9, 12, 15, 4⟩, ⟨11, 11, 15, 2⟩, ⟨11, 10, 15, 4⟩, ⟨11, 12, 14, 2⟩, ⟨11, 12, 13, 4⟩]
  exact AllWinning.cons node_22602 (AllWinning.cons node_21997 (AllWinning.cons node_22633 (AllWinning.cons node_22058 (AllWinning.cons node_22635 (AllWinning.cons node_22063 (AllWinning.nil))))))

theorem node_23153 : Outcome ⟨11, 12, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 8⟩) (by decide) node_20610

theorem node_23154 : Outcome ⟨11, 12, 15, 10⟩ true :=
  Outcome.win (q := ⟨11, 6, 15, 12⟩) (by decide) node_19268

theorem node_23155 : Outcome ⟨11, 13, 14, 4⟩ true :=
  Outcome.win (q := ⟨10, 13, 14, 2⟩) (by decide) node_22605

theorem node_23156 : Outcome ⟨11, 13, 14, 8⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 10⟩) (by decide) node_19867

theorem node_23157 : Outcome ⟨11, 14, 13, 4⟩ true :=
  Outcome.win (q := ⟨10, 14, 13, 2⟩) (by decide) node_22608

theorem node_23158 : Outcome ⟨11, 14, 13, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 10⟩) (by decide) node_19874

theorem node_23159 : Outcome ⟨11, 15, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 12, 2⟩, ⟨9, 15, 12, 4⟩, ⟨11, 14, 12, 2⟩, ⟨11, 13, 12, 4⟩, ⟨11, 15, 11, 2⟩, ⟨11, 15, 10, 4⟩]
  exact AllWinning.cons node_22611 (AllWinning.cons node_22003 (AllWinning.cons node_22640 (AllWinning.cons node_22066 (AllWinning.cons node_22642 (AllWinning.cons node_22072 (AllWinning.nil))))))

theorem node_23160 : Outcome ⟨11, 15, 12, 4⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 8⟩) (by decide) node_20621

theorem node_23161 : Outcome ⟨11, 15, 12, 10⟩ true :=
  Outcome.win (q := ⟨11, 15, 6, 12⟩) (by decide) node_19292

theorem node_23162 : Outcome ⟨11, 16, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 11, 2⟩, ⟨9, 16, 11, 4⟩, ⟨11, 15, 11, 2⟩, ⟨11, 14, 11, 4⟩, ⟨11, 16, 10, 2⟩, ⟨11, 16, 9, 4⟩]
  exact AllWinning.cons node_22614 (AllWinning.cons node_22004 (AllWinning.cons node_22642 (AllWinning.cons node_22069 (AllWinning.cons node_22644 (AllWinning.cons node_22074 (AllWinning.nil))))))

theorem node_23163 : Outcome ⟨11, 16, 11, 4⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 8⟩) (by decide) node_20628

theorem node_23164 : Outcome ⟨11, 16, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 8⟩) (by decide) node_20628

theorem node_23165 : Outcome ⟨11, 17, 10, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 8, 4⟩) (by decide) node_22077

theorem node_23166 : Outcome ⟨11, 17, 10, 8⟩ true :=
  Outcome.win (q := ⟨11, 17, 8, 4⟩) (by decide) node_22077

theorem node_23167 : Outcome ⟨11, 18, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 18, 9, 2⟩, ⟨9, 18, 9, 4⟩, ⟨11, 17, 9, 2⟩, ⟨11, 16, 9, 4⟩, ⟨11, 18, 8, 2⟩, ⟨11, 18, 7, 4⟩]
  exact AllWinning.cons node_22619 (AllWinning.cons node_22011 (AllWinning.cons node_22646 (AllWinning.cons node_22074 (AllWinning.cons node_22648 (AllWinning.cons node_22079 (AllWinning.nil))))))

theorem node_23168 : Outcome ⟨11, 19, 8, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 8, 4⟩) (by decide) node_22077

theorem node_23169 : Outcome ⟨11, 20, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 20, 7, 2⟩, ⟨9, 20, 7, 4⟩, ⟨11, 19, 7, 2⟩, ⟨11, 18, 7, 4⟩, ⟨11, 20, 6, 2⟩, ⟨11, 20, 5, 4⟩]
  exact AllWinning.cons node_22622 (AllWinning.cons node_22013 (AllWinning.cons node_22649 (AllWinning.cons node_22079 (AllWinning.cons node_22651 (AllWinning.cons node_22082 (AllWinning.nil))))))

theorem node_23170 : Outcome ⟨11, 20, 7, 8⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 8⟩) (by decide) node_20813

theorem node_23171 : Outcome ⟨12, 6, 20, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 8⟩) (by decide) node_20833

theorem node_23172 : Outcome ⟨12, 6, 20, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 12⟩) (by decide) node_19001

theorem node_23173 : Outcome ⟨12, 7, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 7, 19, 2⟩, ⟨10, 7, 19, 4⟩, ⟨12, 6, 19, 2⟩, ⟨12, 5, 19, 4⟩, ⟨12, 7, 18, 2⟩, ⟨12, 7, 17, 4⟩]
  exact AllWinning.cons node_22626 (AllWinning.cons node_22015 (AllWinning.cons node_22656 (AllWinning.cons node_22087 (AllWinning.cons node_22658 (AllWinning.cons node_22092 (AllWinning.nil))))))

theorem node_23174 : Outcome ⟨12, 7, 19, 10⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 8⟩) (by decide) node_20839

theorem node_23175 : Outcome ⟨12, 8, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 8, 18, 2⟩, ⟨10, 8, 18, 4⟩, ⟨12, 7, 18, 2⟩, ⟨12, 6, 18, 4⟩, ⟨12, 8, 17, 2⟩, ⟨12, 8, 16, 4⟩]
  exact AllWinning.cons node_22628 (AllWinning.cons node_22017 (AllWinning.cons node_22658 (AllWinning.cons node_22090 (AllWinning.cons node_22660 (AllWinning.cons node_22095 (AllWinning.nil))))))

theorem node_23176 : Outcome ⟨12, 8, 18, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 8⟩) (by decide) node_20648

theorem node_23177 : Outcome ⟨12, 8, 18, 12⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 8⟩) (by decide) node_20648

theorem node_23178 : Outcome ⟨12, 9, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 9, 17, 2⟩, ⟨10, 9, 17, 4⟩, ⟨9, 9, 17, 6⟩, ⟨8, 9, 17, 8⟩, ⟨12, 8, 17, 2⟩, ⟨12, 7, 17, 4⟩, ⟨12, 6, 17, 6⟩, ⟨12, 5, 17, 8⟩, ⟨12, 9, 16, 2⟩, ⟨12, 9, 15, 4⟩, ⟨12, 9, 14, 6⟩, ⟨12, 9, 13, 8⟩]
  exact AllWinning.cons node_22629 (AllWinning.cons node_22020 (AllWinning.cons node_21397 (AllWinning.cons node_20653 (AllWinning.cons node_22660 (AllWinning.cons node_22092 (AllWinning.cons node_21501 (AllWinning.cons node_20829 (AllWinning.cons node_22663 (AllWinning.cons node_22099 (AllWinning.cons node_21508 (AllWinning.cons node_20846 (AllWinning.nil))))))))))))

theorem node_23179 : Outcome ⟨12, 9, 17, 8⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 12⟩) (by decide) node_19013

theorem node_23180 : Outcome ⟨12, 10, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 10, 16, 2⟩, ⟨10, 10, 16, 4⟩, ⟨12, 9, 16, 2⟩, ⟨12, 8, 16, 4⟩, ⟨12, 10, 15, 2⟩, ⟨12, 10, 14, 4⟩]
  exact AllWinning.cons node_22631 (AllWinning.cons node_22022 (AllWinning.cons node_22663 (AllWinning.cons node_22095 (AllWinning.cons node_22667 (AllWinning.cons node_22102 (AllWinning.nil))))))

theorem node_23181 : Outcome ⟨12, 10, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 8⟩) (by decide) node_20833

theorem node_23182 : Outcome ⟨12, 10, 16, 10⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 8⟩) (by decide) node_20833

theorem node_23183 : Outcome ⟨12, 11, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 8⟩) (by decide) node_20839

theorem node_23184 : Outcome ⟨12, 11, 15, 10⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 12⟩) (by decide) node_19020

theorem node_23185 : Outcome ⟨12, 12, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 14, 2⟩, ⟨10, 12, 14, 4⟩, ⟨12, 11, 14, 2⟩, ⟨12, 10, 14, 4⟩, ⟨12, 12, 13, 2⟩, ⟨12, 12, 12, 4⟩]
  exact AllWinning.cons node_22635 (AllWinning.cons node_22027 (AllWinning.cons node_22670 (AllWinning.cons node_22102 (AllWinning.cons node_22671 (AllWinning.cons node_22107 (AllWinning.nil))))))

theorem node_23186 : Outcome ⟨12, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 12, 11, 6⟩) (by decide) node_21514

theorem node_23187 : Outcome ⟨12, 12, 14, 10⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 20⟩) (by decide) node_15033

theorem node_23188 : Outcome ⟨12, 12, 14, 12⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 20⟩) (by decide) node_15033

theorem node_23189 : Outcome ⟨12, 13, 13, 2⟩ true :=
  Outcome.win (q := ⟨11, 13, 13, 2⟩) (by decide) node_22637

theorem node_23190 : Outcome ⟨12, 13, 13, 8⟩ true :=
  Outcome.win (q := ⟨11, 13, 13, 2⟩) (by decide) node_22637

theorem node_23191 : Outcome ⟨12, 14, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 14, 12, 2⟩, ⟨10, 14, 12, 4⟩, ⟨12, 13, 12, 2⟩, ⟨12, 12, 12, 4⟩, ⟨12, 14, 11, 2⟩, ⟨12, 14, 10, 4⟩]
  exact AllWinning.cons node_22640 (AllWinning.cons node_22032 (AllWinning.cons node_22675 (AllWinning.cons node_22107 (AllWinning.cons node_22679 (AllWinning.cons node_22114 (AllWinning.nil))))))

theorem node_23192 : Outcome ⟨12, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨12, 11, 12, 6⟩) (by decide) node_21511

theorem node_23193 : Outcome ⟨12, 14, 12, 10⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 20⟩) (by decide) node_15046

theorem node_23194 : Outcome ⟨12, 14, 12, 12⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 20⟩) (by decide) node_15046

theorem node_23195 : Outcome ⟨12, 15, 11, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 8⟩) (by decide) node_20862

theorem node_23196 : Outcome ⟨12, 15, 11, 10⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 12⟩) (by decide) node_19033

theorem node_23197 : Outcome ⟨12, 16, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 10, 2⟩, ⟨10, 16, 10, 4⟩, ⟨12, 15, 10, 2⟩, ⟨12, 14, 10, 4⟩, ⟨12, 16, 9, 2⟩, ⟨12, 16, 8, 4⟩]
  exact AllWinning.cons node_22644 (AllWinning.cons node_22037 (AllWinning.cons node_22680 (AllWinning.cons node_22114 (AllWinning.cons node_22683 (AllWinning.cons node_22120 (AllWinning.nil))))))

theorem node_23198 : Outcome ⟨12, 16, 10, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 8⟩) (by decide) node_20867

theorem node_23199 : Outcome ⟨12, 16, 10, 10⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 8⟩) (by decide) node_20867

theorem node_23200 : Outcome ⟨12, 17, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 17, 9, 2⟩, ⟨10, 17, 9, 4⟩, ⟨9, 17, 9, 6⟩, ⟨8, 17, 9, 8⟩, ⟨12, 16, 9, 2⟩, ⟨12, 15, 9, 4⟩, ⟨12, 14, 9, 6⟩, ⟨12, 13, 9, 8⟩, ⟨12, 17, 8, 2⟩, ⟨12, 17, 7, 4⟩, ⟨12, 17, 6, 6⟩, ⟨12, 17, 5, 8⟩]
  exact AllWinning.cons node_22646 (AllWinning.cons node_22040 (AllWinning.cons node_21420 (AllWinning.cons node_20674 (AllWinning.cons node_22683 (AllWinning.cons node_22117 (AllWinning.cons node_21518 (AllWinning.cons node_20855 (AllWinning.cons node_22686 (AllWinning.cons node_22123 (AllWinning.cons node_21524 (AllWinning.cons node_20871 (AllWinning.nil))))))))))))

theorem node_23201 : Outcome ⟨12, 17, 9, 8⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 12⟩) (by decide) node_19041

theorem node_23202 : Outcome ⟨12, 18, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 18, 8, 2⟩, ⟨10, 18, 8, 4⟩, ⟨12, 17, 8, 2⟩, ⟨12, 16, 8, 4⟩, ⟨12, 18, 7, 2⟩, ⟨12, 18, 6, 4⟩]
  exact AllWinning.cons node_22648 (AllWinning.cons node_22041 (AllWinning.cons node_22686 (AllWinning.cons node_22120 (AllWinning.cons node_22688 (AllWinning.cons node_22125 (AllWinning.nil))))))

theorem node_23203 : Outcome ⟨12, 18, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 8⟩) (by decide) node_20677

theorem node_23204 : Outcome ⟨12, 18, 8, 12⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 8⟩) (by decide) node_20677

theorem node_23205 : Outcome ⟨12, 19, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 7, 2⟩, ⟨10, 19, 7, 4⟩, ⟨12, 18, 7, 2⟩, ⟨12, 17, 7, 4⟩, ⟨12, 19, 6, 2⟩, ⟨12, 19, 5, 4⟩]
  exact AllWinning.cons node_22649 (AllWinning.cons node_22043 (AllWinning.cons node_22688 (AllWinning.cons node_22123 (AllWinning.cons node_22690 (AllWinning.cons node_22128 (AllWinning.nil))))))

theorem node_23206 : Outcome ⟨12, 19, 7, 10⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 8⟩) (by decide) node_20862

theorem node_23207 : Outcome ⟨12, 20, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 8⟩) (by decide) node_20867

theorem node_23208 : Outcome ⟨12, 20, 6, 6⟩ true :=
  Outcome.win (q := ⟨6, 20, 6, 12⟩) (by decide) node_19051

theorem node_23209 : Outcome ⟨13, 5, 20, 2⟩ true :=
  Outcome.win (q := ⟨13, 4, 20, 2⟩) (by decide) node_22693

theorem node_23210 : Outcome ⟨13, 5, 20, 20⟩ true :=
  Outcome.win (q := ⟨13, 4, 20, 2⟩) (by decide) node_22693

theorem node_23211 : Outcome ⟨13, 6, 19, 4⟩ true :=
  Outcome.win (q := ⟨13, 5, 19, 2⟩) (by decide) node_22696

theorem node_23212 : Outcome ⟨13, 7, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 7, 18, 2⟩, ⟨11, 7, 18, 4⟩, ⟨13, 6, 18, 2⟩, ⟨13, 5, 18, 4⟩, ⟨13, 7, 17, 2⟩, ⟨13, 7, 16, 4⟩]
  exact AllWinning.cons node_22658 (AllWinning.cons node_22050 (AllWinning.cons node_22699 (AllWinning.cons node_22135 (AllWinning.cons node_22700 (AllWinning.cons node_22140 (AllWinning.nil))))))

theorem node_23213 : Outcome ⟨13, 7, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 7, 18, 2⟩, ⟨11, 7, 18, 4⟩, ⟨10, 7, 18, 6⟩, ⟨9, 7, 18, 8⟩, ⟨13, 6, 18, 2⟩, ⟨13, 5, 18, 4⟩, ⟨13, 4, 18, 6⟩, ⟨13, 3, 18, 8⟩, ⟨13, 7, 17, 2⟩, ⟨13, 7, 16, 4⟩, ⟨13, 7, 15, 6⟩, ⟨13, 7, 14, 8⟩]
  exact AllWinning.cons node_22658 (AllWinning.cons node_22050 (AllWinning.cons node_21427 (AllWinning.cons node_20689 (AllWinning.cons node_22699 (AllWinning.cons node_22135 (AllWinning.cons node_21541 (AllWinning.cons node_20884 (AllWinning.cons node_22700 (AllWinning.cons node_22140 (AllWinning.cons node_21549 (AllWinning.cons node_20892 (AllWinning.nil))))))))))))

theorem node_23214 : Outcome ⟨13, 7, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 7, 18, 2⟩, ⟨11, 7, 18, 4⟩, ⟨10, 7, 18, 6⟩, ⟨9, 7, 18, 8⟩, ⟨8, 7, 18, 10⟩, ⟨7, 7, 18, 12⟩, ⟨13, 6, 18, 2⟩, ⟨13, 5, 18, 4⟩, ⟨13, 4, 18, 6⟩, ⟨13, 3, 18, 8⟩, ⟨13, 2, 18, 10⟩, ⟨13, 1, 18, 12⟩, ⟨13, 7, 17, 2⟩, ⟨13, 7, 16, 4⟩, ⟨13, 7, 15, 6⟩, ⟨13, 7, 14, 8⟩, ⟨13, 7, 13, 10⟩, ⟨13, 7, 12, 12⟩]
  exact AllWinning.cons node_22658 (AllWinning.cons node_22050 (AllWinning.cons node_21427 (AllWinning.cons node_20689 (AllWinning.cons node_19919 (AllWinning.cons node_19062 (AllWinning.cons node_22699 (AllWinning.cons node_22135 (AllWinning.cons node_21541 (AllWinning.cons node_20884 (AllWinning.cons node_20133 (AllWinning.cons node_19358 (AllWinning.cons node_22700 (AllWinning.cons node_22140 (AllWinning.cons node_21549 (AllWinning.cons node_20892 (AllWinning.cons node_20146 (AllWinning.cons node_19372 (AllWinning.nil))))))))))))))))))

theorem node_23215 : Outcome ⟨13, 7, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 7, 18, 2⟩, ⟨11, 7, 18, 4⟩, ⟨10, 7, 18, 6⟩, ⟨9, 7, 18, 8⟩, ⟨8, 7, 18, 10⟩, ⟨7, 7, 18, 12⟩, ⟨6, 7, 18, 14⟩, ⟨5, 7, 18, 16⟩, ⟨13, 6, 18, 2⟩, ⟨13, 5, 18, 4⟩, ⟨13, 4, 18, 6⟩, ⟨13, 3, 18, 8⟩, ⟨13, 2, 18, 10⟩, ⟨13, 1, 18, 12⟩, ⟨13, 0, 18, 14⟩, ⟨13, 7, 17, 2⟩, ⟨13, 7, 16, 4⟩, ⟨13, 7, 15, 6⟩, ⟨13, 7, 14, 8⟩, ⟨13, 7, 13, 10⟩, ⟨13, 7, 12, 12⟩, ⟨13, 7, 11, 14⟩, ⟨13, 7, 10, 16⟩]
  exact AllWinning.cons node_22658 (AllWinning.cons node_22050 (AllWinning.cons node_21427 (AllWinning.cons node_20689 (AllWinning.cons node_19919 (AllWinning.cons node_19062 (AllWinning.cons node_18104 (AllWinning.cons node_17178 (AllWinning.cons node_22699 (AllWinning.cons node_22135 (AllWinning.cons node_21541 (AllWinning.cons node_20884 (AllWinning.cons node_20133 (AllWinning.cons node_19358 (AllWinning.cons node_18479 (AllWinning.cons node_22700 (AllWinning.cons node_22140 (AllWinning.cons node_21549 (AllWinning.cons node_20892 (AllWinning.cons node_20146 (AllWinning.cons node_19372 (AllWinning.cons node_18505 (AllWinning.cons node_17599 (AllWinning.nil)))))))))))))))))))))))

theorem node_23216 : Outcome ⟨13, 8, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 8, 17, 4⟩) (by decide) node_22052

theorem node_23217 : Outcome ⟨13, 8, 17, 8⟩ true :=
  Outcome.win (q := ⟨13, 1, 17, 14⟩) (by decide) node_18485

theorem node_23218 : Outcome ⟨13, 9, 16, 4⟩ true :=
  Outcome.win (q := ⟨13, 8, 16, 2⟩) (by decide) node_22703

theorem node_23219 : Outcome ⟨13, 9, 16, 8⟩ true :=
  Outcome.win (q := ⟨13, 8, 16, 2⟩) (by decide) node_22703

theorem node_23220 : Outcome ⟨13, 9, 16, 14⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 18⟩) (by decide) node_16096

theorem node_23221 : Outcome ⟨13, 10, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 2⟩) (by decide) node_22706

theorem node_23222 : Outcome ⟨13, 10, 15, 8⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 2⟩) (by decide) node_22706

theorem node_23223 : Outcome ⟨13, 11, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 10, 14, 2⟩) (by decide) node_22710

theorem node_23224 : Outcome ⟨13, 11, 14, 8⟩ true :=
  Outcome.win (q := ⟨13, 6, 14, 10⟩) (by decide) node_20142

theorem node_23225 : Outcome ⟨13, 12, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 11, 13, 2⟩) (by decide) node_22713

theorem node_23226 : Outcome ⟨13, 12, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 11, 13, 2⟩) (by decide) node_22713

theorem node_23227 : Outcome ⟨13, 12, 13, 8⟩ true :=
  Outcome.win (q := ⟨13, 11, 13, 2⟩) (by decide) node_22713

theorem node_23228 : Outcome ⟨13, 13, 12, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 11, 2⟩) (by decide) node_22719

theorem node_23229 : Outcome ⟨13, 13, 12, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 11, 2⟩) (by decide) node_22719

theorem node_23230 : Outcome ⟨13, 13, 12, 8⟩ true :=
  Outcome.win (q := ⟨13, 13, 11, 2⟩) (by decide) node_22719

theorem node_23231 : Outcome ⟨13, 14, 11, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 11, 2⟩) (by decide) node_22719

theorem node_23232 : Outcome ⟨13, 14, 11, 8⟩ true :=
  Outcome.win (q := ⟨13, 14, 6, 10⟩) (by decide) node_20168

theorem node_23233 : Outcome ⟨13, 15, 10, 4⟩ true :=
  Outcome.win (q := ⟨13, 14, 10, 2⟩) (by decide) node_22722

theorem node_23234 : Outcome ⟨13, 15, 10, 8⟩ true :=
  Outcome.win (q := ⟨13, 14, 10, 2⟩) (by decide) node_22722

theorem node_23235 : Outcome ⟨13, 15, 10, 20⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 24⟩) (by decide) node_13728

theorem node_23236 : Outcome ⟨13, 16, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 2⟩) (by decide) node_22725

theorem node_23237 : Outcome ⟨13, 16, 9, 8⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 2⟩) (by decide) node_22725

theorem node_23238 : Outcome ⟨13, 16, 9, 14⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 18⟩) (by decide) node_16132

theorem node_23239 : Outcome ⟨13, 17, 8, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 8, 4⟩) (by decide) node_22077

theorem node_23240 : Outcome ⟨13, 17, 8, 8⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 14⟩) (by decide) node_18540

theorem node_23241 : Outcome ⟨13, 18, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 7, 2⟩, ⟨11, 18, 7, 4⟩, ⟨13, 17, 7, 2⟩, ⟨13, 16, 7, 4⟩, ⟨13, 18, 6, 2⟩, ⟨13, 18, 5, 4⟩]
  exact AllWinning.cons node_22688 (AllWinning.cons node_22079 (AllWinning.cons node_22732 (AllWinning.cons node_22165 (AllWinning.cons node_22735 (AllWinning.cons node_22171 (AllWinning.nil))))))

end RQ9F1
