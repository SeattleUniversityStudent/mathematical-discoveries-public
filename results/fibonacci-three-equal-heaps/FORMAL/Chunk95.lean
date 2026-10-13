import Chunk94
set_option autoImplicit false
namespace RQ9F1

theorem node_20487 : Outcome ⟨4, 10, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 10, 20, 2⟩, ⟨2, 10, 20, 4⟩, ⟨1, 10, 20, 6⟩, ⟨0, 10, 20, 8⟩, ⟨4, 9, 20, 2⟩, ⟨4, 8, 20, 4⟩, ⟨4, 7, 20, 6⟩, ⟨4, 6, 20, 8⟩, ⟨4, 10, 19, 2⟩, ⟨4, 10, 18, 4⟩, ⟨4, 10, 17, 6⟩, ⟨4, 10, 16, 8⟩]
  exact AllWinning.cons node_19764 (AllWinning.cons node_18870 (AllWinning.cons node_17909 (AllWinning.cons node_16972 (AllWinning.cons node_19790 (AllWinning.cons node_18930 (AllWinning.cons node_18014 (AllWinning.cons node_17128 (AllWinning.cons node_19793 (AllWinning.cons node_18936 (AllWinning.cons node_18021 (AllWinning.cons node_17138 (AllWinning.nil))))))))))))

theorem node_20488 : Outcome ⟨4, 10, 20, 6⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 10⟩) (by decide) node_16075

theorem node_20489 : Outcome ⟨4, 11, 19, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 2⟩) (by decide) node_19766

theorem node_20490 : Outcome ⟨4, 11, 19, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 2⟩) (by decide) node_19766

theorem node_20491 : Outcome ⟨4, 12, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 2⟩) (by decide) node_19795

theorem node_20492 : Outcome ⟨4, 13, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 17, 2⟩, ⟨2, 13, 17, 4⟩, ⟨4, 12, 17, 2⟩, ⟨4, 11, 17, 4⟩, ⟨4, 13, 16, 2⟩, ⟨4, 13, 15, 4⟩]
  exact AllWinning.cons node_19772 (AllWinning.cons node_18877 (AllWinning.cons node_19802 (AllWinning.cons node_18938 (AllWinning.cons node_19804 (AllWinning.cons node_18943 (AllWinning.nil))))))

theorem node_20493 : Outcome ⟨4, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 6⟩) (by decide) node_17919

theorem node_20494 : Outcome ⟨4, 13, 17, 6⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 10⟩) (by decide) node_16086

theorem node_20495 : Outcome ⟨4, 14, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 14, 16, 2⟩, ⟨2, 14, 16, 4⟩, ⟨4, 13, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨4, 14, 15, 2⟩, ⟨4, 14, 14, 4⟩]
  exact AllWinning.cons node_19773 (AllWinning.cons node_18880 (AllWinning.cons node_19804 (AllWinning.cons node_18941 (AllWinning.cons node_19806 (AllWinning.cons node_18947 (AllWinning.nil))))))

theorem node_20496 : Outcome ⟨4, 14, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 14, 16, 2⟩, ⟨2, 14, 16, 4⟩, ⟨1, 14, 16, 6⟩, ⟨0, 14, 16, 8⟩, ⟨4, 13, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨4, 11, 16, 6⟩, ⟨4, 10, 16, 8⟩, ⟨4, 14, 15, 2⟩, ⟨4, 14, 14, 4⟩, ⟨4, 14, 13, 6⟩, ⟨4, 14, 12, 8⟩]
  exact AllWinning.cons node_19773 (AllWinning.cons node_18880 (AllWinning.cons node_17925 (AllWinning.cons node_16986 (AllWinning.cons node_19804 (AllWinning.cons node_18941 (AllWinning.cons node_18026 (AllWinning.cons node_17138 (AllWinning.cons node_19806 (AllWinning.cons node_18947 (AllWinning.cons node_18036 (AllWinning.cons node_17153 (AllWinning.nil))))))))))))

theorem node_20497 : Outcome ⟨4, 14, 16, 6⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 10⟩) (by decide) node_16092

theorem node_20498 : Outcome ⟨4, 14, 16, 12⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 10⟩) (by decide) node_16092

theorem node_20499 : Outcome ⟨4, 15, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 15, 15, 2⟩) (by decide) node_19775

theorem node_20500 : Outcome ⟨4, 15, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 8⟩) (by decide) node_16991

theorem node_20501 : Outcome ⟨4, 15, 15, 12⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 8⟩) (by decide) node_16991

theorem node_20502 : Outcome ⟨4, 16, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 16, 14, 2⟩, ⟨2, 16, 14, 4⟩, ⟨4, 15, 14, 2⟩, ⟨4, 14, 14, 4⟩, ⟨4, 16, 13, 2⟩, ⟨4, 16, 12, 4⟩]
  exact AllWinning.cons node_19779 (AllWinning.cons node_18888 (AllWinning.cons node_19809 (AllWinning.cons node_18947 (AllWinning.cons node_19812 (AllWinning.cons node_18955 (AllWinning.nil))))))

theorem node_20503 : Outcome ⟨4, 16, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 16, 14, 2⟩, ⟨2, 16, 14, 4⟩, ⟨1, 16, 14, 6⟩, ⟨0, 16, 14, 8⟩, ⟨4, 15, 14, 2⟩, ⟨4, 14, 14, 4⟩, ⟨4, 13, 14, 6⟩, ⟨4, 12, 14, 8⟩, ⟨4, 16, 13, 2⟩, ⟨4, 16, 12, 4⟩, ⟨4, 16, 11, 6⟩, ⟨4, 16, 10, 8⟩]
  exact AllWinning.cons node_19779 (AllWinning.cons node_18888 (AllWinning.cons node_17932 (AllWinning.cons node_16996 (AllWinning.cons node_19809 (AllWinning.cons node_18947 (AllWinning.cons node_18032 (AllWinning.cons node_17145 (AllWinning.cons node_19812 (AllWinning.cons node_18955 (AllWinning.cons node_18043 (AllWinning.cons node_17161 (AllWinning.nil))))))))))))

theorem node_20504 : Outcome ⟨4, 16, 14, 6⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 10⟩) (by decide) node_16128

theorem node_20505 : Outcome ⟨4, 16, 14, 12⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 10⟩) (by decide) node_16128

theorem node_20506 : Outcome ⟨4, 17, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 13, 2⟩, ⟨2, 17, 13, 4⟩, ⟨4, 16, 13, 2⟩, ⟨4, 15, 13, 4⟩, ⟨4, 17, 12, 2⟩, ⟨4, 17, 11, 4⟩]
  exact AllWinning.cons node_19781 (AllWinning.cons node_18891 (AllWinning.cons node_19812 (AllWinning.cons node_18951 (AllWinning.cons node_19814 (AllWinning.cons node_18957 (AllWinning.nil))))))

theorem node_20507 : Outcome ⟨4, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 6⟩) (by decide) node_17936

theorem node_20508 : Outcome ⟨4, 17, 13, 6⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 10⟩) (by decide) node_16105

theorem node_20509 : Outcome ⟨4, 18, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 11, 2⟩) (by decide) node_19816

theorem node_20510 : Outcome ⟨4, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 2⟩) (by decide) node_19784

theorem node_20511 : Outcome ⟨4, 19, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 2⟩) (by decide) node_19784

theorem node_20512 : Outcome ⟨4, 20, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 20, 10, 2⟩, ⟨2, 20, 10, 4⟩, ⟨1, 20, 10, 6⟩, ⟨0, 20, 10, 8⟩, ⟨4, 19, 10, 2⟩, ⟨4, 18, 10, 4⟩, ⟨4, 17, 10, 6⟩, ⟨4, 16, 10, 8⟩, ⟨4, 20, 9, 2⟩, ⟨4, 20, 8, 4⟩, ⟨4, 20, 7, 6⟩, ⟨4, 20, 6, 8⟩]
  exact AllWinning.cons node_19788 (AllWinning.cons node_18898 (AllWinning.cons node_17949 (AllWinning.cons node_17010 (AllWinning.cons node_19822 (AllWinning.cons node_18960 (AllWinning.cons node_18044 (AllWinning.cons node_17161 (AllWinning.cons node_19824 (AllWinning.cons node_18963 (AllWinning.cons node_18052 (AllWinning.cons node_17170 (AllWinning.nil))))))))))))

theorem node_20513 : Outcome ⟨4, 20, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 20, 5, 10⟩) (by decide) node_16148

theorem node_20514 : Outcome ⟨5, 9, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 9, 20, 2⟩, ⟨3, 9, 20, 4⟩, ⟨2, 9, 20, 6⟩, ⟨1, 9, 20, 8⟩, ⟨5, 8, 20, 2⟩, ⟨5, 7, 20, 4⟩, ⟨5, 6, 20, 6⟩, ⟨5, 5, 20, 8⟩, ⟨5, 9, 19, 2⟩, ⟨5, 9, 18, 4⟩, ⟨5, 9, 17, 6⟩, ⟨5, 9, 16, 8⟩]
  exact AllWinning.cons node_19790 (AllWinning.cons node_18900 (AllWinning.cons node_17952 (AllWinning.cons node_17013 (AllWinning.cons node_19827 (AllWinning.cons node_18967 (AllWinning.cons node_18056 (AllWinning.cons node_17172 (AllWinning.cons node_19829 (AllWinning.cons node_18971 (AllWinning.cons node_18064 (AllWinning.cons node_17182 (AllWinning.nil))))))))))))

theorem node_20515 : Outcome ⟨5, 9, 20, 8⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 12⟩) (by decide) node_15176

theorem node_20516 : Outcome ⟨5, 10, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 19, 2⟩, ⟨3, 10, 19, 4⟩, ⟨5, 9, 19, 2⟩, ⟨5, 8, 19, 4⟩, ⟨5, 10, 18, 2⟩, ⟨5, 10, 17, 4⟩]
  exact AllWinning.cons node_19793 (AllWinning.cons node_18904 (AllWinning.cons node_19829 (AllWinning.cons node_18969 (AllWinning.cons node_19830 (AllWinning.cons node_18974 (AllWinning.nil))))))

theorem node_20517 : Outcome ⟨5, 10, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 19, 2⟩, ⟨3, 10, 19, 4⟩, ⟨2, 10, 19, 6⟩, ⟨1, 10, 19, 8⟩, ⟨5, 9, 19, 2⟩, ⟨5, 8, 19, 4⟩, ⟨5, 7, 19, 6⟩, ⟨5, 6, 19, 8⟩, ⟨5, 10, 18, 2⟩, ⟨5, 10, 17, 4⟩, ⟨5, 10, 16, 6⟩, ⟨5, 10, 15, 8⟩]
  exact AllWinning.cons node_19793 (AllWinning.cons node_18904 (AllWinning.cons node_17954 (AllWinning.cons node_17017 (AllWinning.cons node_19829 (AllWinning.cons node_18969 (AllWinning.cons node_18058 (AllWinning.cons node_17174 (AllWinning.cons node_19830 (AllWinning.cons node_18974 (AllWinning.cons node_18066 (AllWinning.cons node_17184 (AllWinning.nil))))))))))))

theorem node_20518 : Outcome ⟨5, 10, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 19, 2⟩, ⟨3, 10, 19, 4⟩, ⟨2, 10, 19, 6⟩, ⟨1, 10, 19, 8⟩, ⟨0, 10, 19, 10⟩, ⟨5, 9, 19, 2⟩, ⟨5, 8, 19, 4⟩, ⟨5, 7, 19, 6⟩, ⟨5, 6, 19, 8⟩, ⟨5, 5, 19, 10⟩, ⟨5, 4, 19, 12⟩, ⟨5, 10, 18, 2⟩, ⟨5, 10, 17, 4⟩, ⟨5, 10, 16, 6⟩, ⟨5, 10, 15, 8⟩, ⟨5, 10, 14, 10⟩, ⟨5, 10, 13, 12⟩]
  exact AllWinning.cons node_19793 (AllWinning.cons node_18904 (AllWinning.cons node_17954 (AllWinning.cons node_17017 (AllWinning.cons node_15906 (AllWinning.cons node_19829 (AllWinning.cons node_18969 (AllWinning.cons node_18058 (AllWinning.cons node_17174 (AllWinning.cons node_16156 (AllWinning.cons node_15153 (AllWinning.cons node_19830 (AllWinning.cons node_18974 (AllWinning.cons node_18066 (AllWinning.cons node_17184 (AllWinning.cons node_16171 (AllWinning.cons node_15180 (AllWinning.nil)))))))))))))))))

theorem node_20519 : Outcome ⟨5, 10, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 19, 2⟩, ⟨3, 10, 19, 4⟩, ⟨2, 10, 19, 6⟩, ⟨1, 10, 19, 8⟩, ⟨0, 10, 19, 10⟩, ⟨5, 9, 19, 2⟩, ⟨5, 8, 19, 4⟩, ⟨5, 7, 19, 6⟩, ⟨5, 6, 19, 8⟩, ⟨5, 5, 19, 10⟩, ⟨5, 4, 19, 12⟩, ⟨5, 3, 19, 14⟩, ⟨5, 2, 19, 16⟩, ⟨5, 10, 18, 2⟩, ⟨5, 10, 17, 4⟩, ⟨5, 10, 16, 6⟩, ⟨5, 10, 15, 8⟩, ⟨5, 10, 14, 10⟩, ⟨5, 10, 13, 12⟩, ⟨5, 10, 12, 14⟩, ⟨5, 10, 11, 16⟩]
  exact AllWinning.cons node_19793 (AllWinning.cons node_18904 (AllWinning.cons node_17954 (AllWinning.cons node_17017 (AllWinning.cons node_15906 (AllWinning.cons node_19829 (AllWinning.cons node_18969 (AllWinning.cons node_18058 (AllWinning.cons node_17174 (AllWinning.cons node_16156 (AllWinning.cons node_15153 (AllWinning.cons node_14210 (AllWinning.cons node_13248 (AllWinning.cons node_19830 (AllWinning.cons node_18974 (AllWinning.cons node_18066 (AllWinning.cons node_17184 (AllWinning.cons node_16171 (AllWinning.cons node_15180 (AllWinning.cons node_14231 (AllWinning.cons node_13269 (AllWinning.nil)))))))))))))))))))))

theorem node_20520 : Outcome ⟨5, 10, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 19, 2⟩, ⟨3, 10, 19, 4⟩, ⟨2, 10, 19, 6⟩, ⟨1, 10, 19, 8⟩, ⟨0, 10, 19, 10⟩, ⟨5, 9, 19, 2⟩, ⟨5, 8, 19, 4⟩, ⟨5, 7, 19, 6⟩, ⟨5, 6, 19, 8⟩, ⟨5, 5, 19, 10⟩, ⟨5, 4, 19, 12⟩, ⟨5, 3, 19, 14⟩, ⟨5, 2, 19, 16⟩, ⟨5, 1, 19, 18⟩, ⟨5, 0, 19, 20⟩, ⟨5, 10, 18, 2⟩, ⟨5, 10, 17, 4⟩, ⟨5, 10, 16, 6⟩, ⟨5, 10, 15, 8⟩, ⟨5, 10, 14, 10⟩, ⟨5, 10, 13, 12⟩, ⟨5, 10, 12, 14⟩, ⟨5, 10, 11, 16⟩, ⟨5, 10, 10, 18⟩, ⟨5, 10, 9, 20⟩]
  exact AllWinning.cons node_19793 (AllWinning.cons node_18904 (AllWinning.cons node_17954 (AllWinning.cons node_17017 (AllWinning.cons node_15906 (AllWinning.cons node_19829 (AllWinning.cons node_18969 (AllWinning.cons node_18058 (AllWinning.cons node_17174 (AllWinning.cons node_16156 (AllWinning.cons node_15153 (AllWinning.cons node_14210 (AllWinning.cons node_13248 (AllWinning.cons node_12284 (AllWinning.cons node_11299 (AllWinning.cons node_19830 (AllWinning.cons node_18974 (AllWinning.cons node_18066 (AllWinning.cons node_17184 (AllWinning.cons node_16171 (AllWinning.cons node_15180 (AllWinning.cons node_14231 (AllWinning.cons node_13269 (AllWinning.cons node_12310 (AllWinning.cons node_11334 (AllWinning.nil)))))))))))))))))))))))))

theorem node_20521 : Outcome ⟨5, 10, 19, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 19, 2⟩, ⟨3, 10, 19, 4⟩, ⟨2, 10, 19, 6⟩, ⟨1, 10, 19, 8⟩, ⟨0, 10, 19, 10⟩, ⟨5, 9, 19, 2⟩, ⟨5, 8, 19, 4⟩, ⟨5, 7, 19, 6⟩, ⟨5, 6, 19, 8⟩, ⟨5, 5, 19, 10⟩, ⟨5, 4, 19, 12⟩, ⟨5, 3, 19, 14⟩, ⟨5, 2, 19, 16⟩, ⟨5, 1, 19, 18⟩, ⟨5, 0, 19, 20⟩, ⟨5, 10, 18, 2⟩, ⟨5, 10, 17, 4⟩, ⟨5, 10, 16, 6⟩, ⟨5, 10, 15, 8⟩, ⟨5, 10, 14, 10⟩, ⟨5, 10, 13, 12⟩, ⟨5, 10, 12, 14⟩, ⟨5, 10, 11, 16⟩, ⟨5, 10, 10, 18⟩, ⟨5, 10, 9, 20⟩, ⟨5, 10, 8, 22⟩, ⟨5, 10, 7, 24⟩]
  exact AllWinning.cons node_19793 (AllWinning.cons node_18904 (AllWinning.cons node_17954 (AllWinning.cons node_17017 (AllWinning.cons node_15906 (AllWinning.cons node_19829 (AllWinning.cons node_18969 (AllWinning.cons node_18058 (AllWinning.cons node_17174 (AllWinning.cons node_16156 (AllWinning.cons node_15153 (AllWinning.cons node_14210 (AllWinning.cons node_13248 (AllWinning.cons node_12284 (AllWinning.cons node_11299 (AllWinning.cons node_19830 (AllWinning.cons node_18974 (AllWinning.cons node_18066 (AllWinning.cons node_17184 (AllWinning.cons node_16171 (AllWinning.cons node_15180 (AllWinning.cons node_14231 (AllWinning.cons node_13269 (AllWinning.cons node_12310 (AllWinning.cons node_11334 (AllWinning.cons node_10298 (AllWinning.cons node_9311 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_20522 : Outcome ⟨5, 11, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 2⟩) (by decide) node_19795

theorem node_20523 : Outcome ⟨5, 11, 18, 8⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 2⟩) (by decide) node_19795

theorem node_20524 : Outcome ⟨5, 12, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 11, 17, 2⟩) (by decide) node_19832

theorem node_20525 : Outcome ⟨5, 12, 17, 8⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 10⟩) (by decide) node_16164

theorem node_20526 : Outcome ⟨5, 13, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 16, 4⟩) (by decide) node_18910

theorem node_20527 : Outcome ⟨5, 14, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 14, 2⟩) (by decide) node_19839

theorem node_20528 : Outcome ⟨5, 14, 15, 6⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 12⟩) (by decide) node_15167

theorem node_20529 : Outcome ⟨5, 14, 15, 16⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 12⟩) (by decide) node_15167

theorem node_20530 : Outcome ⟨5, 15, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 14, 2⟩) (by decide) node_19839

theorem node_20531 : Outcome ⟨5, 15, 14, 6⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 12⟩) (by decide) node_15176

theorem node_20532 : Outcome ⟨5, 15, 14, 16⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 12⟩) (by decide) node_15176

theorem node_20533 : Outcome ⟨5, 16, 13, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 13, 4⟩) (by decide) node_18920

theorem node_20534 : Outcome ⟨5, 17, 12, 2⟩ true :=
  Outcome.win (q := ⟨5, 17, 11, 2⟩) (by decide) node_19848

theorem node_20535 : Outcome ⟨5, 17, 12, 8⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 10⟩) (by decide) node_16186

theorem node_20536 : Outcome ⟨5, 18, 11, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 11, 2⟩) (by decide) node_19816

theorem node_20537 : Outcome ⟨5, 18, 11, 8⟩ true :=
  Outcome.win (q := ⟨4, 18, 11, 2⟩) (by decide) node_19816

theorem node_20538 : Outcome ⟨5, 19, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 10, 2⟩, ⟨3, 19, 10, 4⟩, ⟨5, 18, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨5, 19, 9, 2⟩, ⟨5, 19, 8, 4⟩]
  exact AllWinning.cons node_19822 (AllWinning.cons node_18926 (AllWinning.cons node_19850 (AllWinning.cons node_18987 (AllWinning.cons node_19852 (AllWinning.cons node_18991 (AllWinning.nil))))))

theorem node_20539 : Outcome ⟨5, 19, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 10, 2⟩, ⟨3, 19, 10, 4⟩, ⟨2, 19, 10, 6⟩, ⟨1, 19, 10, 8⟩, ⟨5, 18, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨5, 16, 10, 6⟩, ⟨5, 15, 10, 8⟩, ⟨5, 19, 9, 2⟩, ⟨5, 19, 8, 4⟩, ⟨5, 19, 7, 6⟩, ⟨5, 19, 6, 8⟩]
  exact AllWinning.cons node_19822 (AllWinning.cons node_18926 (AllWinning.cons node_17969 (AllWinning.cons node_17041 (AllWinning.cons node_19850 (AllWinning.cons node_18987 (AllWinning.cons node_18087 (AllWinning.cons node_17196 (AllWinning.cons node_19852 (AllWinning.cons node_18991 (AllWinning.cons node_18096 (AllWinning.cons node_17206 (AllWinning.nil))))))))))))

theorem node_20540 : Outcome ⟨5, 19, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 10, 2⟩, ⟨3, 19, 10, 4⟩, ⟨2, 19, 10, 6⟩, ⟨1, 19, 10, 8⟩, ⟨0, 19, 10, 10⟩, ⟨5, 18, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨5, 16, 10, 6⟩, ⟨5, 15, 10, 8⟩, ⟨5, 14, 10, 10⟩, ⟨5, 13, 10, 12⟩, ⟨5, 19, 9, 2⟩, ⟨5, 19, 8, 4⟩, ⟨5, 19, 7, 6⟩, ⟨5, 19, 6, 8⟩, ⟨5, 19, 5, 10⟩, ⟨5, 19, 4, 12⟩]
  exact AllWinning.cons node_19822 (AllWinning.cons node_18926 (AllWinning.cons node_17969 (AllWinning.cons node_17041 (AllWinning.cons node_15936 (AllWinning.cons node_19850 (AllWinning.cons node_18987 (AllWinning.cons node_18087 (AllWinning.cons node_17196 (AllWinning.cons node_16178 (AllWinning.cons node_15188 (AllWinning.cons node_19852 (AllWinning.cons node_18991 (AllWinning.cons node_18096 (AllWinning.cons node_17206 (AllWinning.cons node_16191 (AllWinning.cons node_15211 (AllWinning.nil)))))))))))))))))

theorem node_20541 : Outcome ⟨5, 19, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 10, 2⟩, ⟨3, 19, 10, 4⟩, ⟨2, 19, 10, 6⟩, ⟨1, 19, 10, 8⟩, ⟨0, 19, 10, 10⟩, ⟨5, 18, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨5, 16, 10, 6⟩, ⟨5, 15, 10, 8⟩, ⟨5, 14, 10, 10⟩, ⟨5, 13, 10, 12⟩, ⟨5, 12, 10, 14⟩, ⟨5, 11, 10, 16⟩, ⟨5, 19, 9, 2⟩, ⟨5, 19, 8, 4⟩, ⟨5, 19, 7, 6⟩, ⟨5, 19, 6, 8⟩, ⟨5, 19, 5, 10⟩, ⟨5, 19, 4, 12⟩, ⟨5, 19, 3, 14⟩, ⟨5, 19, 2, 16⟩]
  exact AllWinning.cons node_19822 (AllWinning.cons node_18926 (AllWinning.cons node_17969 (AllWinning.cons node_17041 (AllWinning.cons node_15936 (AllWinning.cons node_19850 (AllWinning.cons node_18987 (AllWinning.cons node_18087 (AllWinning.cons node_17196 (AllWinning.cons node_16178 (AllWinning.cons node_15188 (AllWinning.cons node_14239 (AllWinning.cons node_13272 (AllWinning.cons node_19852 (AllWinning.cons node_18991 (AllWinning.cons node_18096 (AllWinning.cons node_17206 (AllWinning.cons node_16191 (AllWinning.cons node_15211 (AllWinning.cons node_14260 (AllWinning.cons node_13293 (AllWinning.nil)))))))))))))))))))))

theorem node_20542 : Outcome ⟨5, 19, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 10, 2⟩, ⟨3, 19, 10, 4⟩, ⟨2, 19, 10, 6⟩, ⟨1, 19, 10, 8⟩, ⟨0, 19, 10, 10⟩, ⟨5, 18, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨5, 16, 10, 6⟩, ⟨5, 15, 10, 8⟩, ⟨5, 14, 10, 10⟩, ⟨5, 13, 10, 12⟩, ⟨5, 12, 10, 14⟩, ⟨5, 11, 10, 16⟩, ⟨5, 10, 10, 18⟩, ⟨5, 9, 10, 20⟩, ⟨5, 19, 9, 2⟩, ⟨5, 19, 8, 4⟩, ⟨5, 19, 7, 6⟩, ⟨5, 19, 6, 8⟩, ⟨5, 19, 5, 10⟩, ⟨5, 19, 4, 12⟩, ⟨5, 19, 3, 14⟩, ⟨5, 19, 2, 16⟩, ⟨5, 19, 1, 18⟩, ⟨5, 19, 0, 20⟩]
  exact AllWinning.cons node_19822 (AllWinning.cons node_18926 (AllWinning.cons node_17969 (AllWinning.cons node_17041 (AllWinning.cons node_15936 (AllWinning.cons node_19850 (AllWinning.cons node_18987 (AllWinning.cons node_18087 (AllWinning.cons node_17196 (AllWinning.cons node_16178 (AllWinning.cons node_15188 (AllWinning.cons node_14239 (AllWinning.cons node_13272 (AllWinning.cons node_12310 (AllWinning.cons node_11330 (AllWinning.cons node_19852 (AllWinning.cons node_18991 (AllWinning.cons node_18096 (AllWinning.cons node_17206 (AllWinning.cons node_16191 (AllWinning.cons node_15211 (AllWinning.cons node_14260 (AllWinning.cons node_13293 (AllWinning.cons node_12339 (AllWinning.cons node_11362 (AllWinning.nil)))))))))))))))))))))))))

theorem node_20543 : Outcome ⟨5, 19, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 10, 2⟩, ⟨3, 19, 10, 4⟩, ⟨2, 19, 10, 6⟩, ⟨1, 19, 10, 8⟩, ⟨0, 19, 10, 10⟩, ⟨5, 18, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨5, 16, 10, 6⟩, ⟨5, 15, 10, 8⟩, ⟨5, 14, 10, 10⟩, ⟨5, 13, 10, 12⟩, ⟨5, 12, 10, 14⟩, ⟨5, 11, 10, 16⟩, ⟨5, 10, 10, 18⟩, ⟨5, 9, 10, 20⟩, ⟨5, 8, 10, 22⟩, ⟨5, 7, 10, 24⟩, ⟨5, 19, 9, 2⟩, ⟨5, 19, 8, 4⟩, ⟨5, 19, 7, 6⟩, ⟨5, 19, 6, 8⟩, ⟨5, 19, 5, 10⟩, ⟨5, 19, 4, 12⟩, ⟨5, 19, 3, 14⟩, ⟨5, 19, 2, 16⟩, ⟨5, 19, 1, 18⟩, ⟨5, 19, 0, 20⟩]
  exact AllWinning.cons node_19822 (AllWinning.cons node_18926 (AllWinning.cons node_17969 (AllWinning.cons node_17041 (AllWinning.cons node_15936 (AllWinning.cons node_19850 (AllWinning.cons node_18987 (AllWinning.cons node_18087 (AllWinning.cons node_17196 (AllWinning.cons node_16178 (AllWinning.cons node_15188 (AllWinning.cons node_14239 (AllWinning.cons node_13272 (AllWinning.cons node_12310 (AllWinning.cons node_11330 (AllWinning.cons node_10288 (AllWinning.cons node_9298 (AllWinning.cons node_19852 (AllWinning.cons node_18991 (AllWinning.cons node_18096 (AllWinning.cons node_17206 (AllWinning.cons node_16191 (AllWinning.cons node_15211 (AllWinning.cons node_14260 (AllWinning.cons node_13293 (AllWinning.cons node_12339 (AllWinning.cons node_11362 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_20544 : Outcome ⟨5, 20, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 9, 2⟩, ⟨3, 20, 9, 4⟩, ⟨2, 20, 9, 6⟩, ⟨1, 20, 9, 8⟩, ⟨5, 19, 9, 2⟩, ⟨5, 18, 9, 4⟩, ⟨5, 17, 9, 6⟩, ⟨5, 16, 9, 8⟩, ⟨5, 20, 8, 2⟩, ⟨5, 20, 7, 4⟩, ⟨5, 20, 6, 6⟩, ⟨5, 20, 5, 8⟩]
  exact AllWinning.cons node_19824 (AllWinning.cons node_18927 (AllWinning.cons node_17972 (AllWinning.cons node_17044 (AllWinning.cons node_19852 (AllWinning.cons node_18989 (AllWinning.cons node_18091 (AllWinning.cons node_17198 (AllWinning.cons node_19853 (AllWinning.cons node_18994 (AllWinning.cons node_18098 (AllWinning.cons node_17208 (AllWinning.nil))))))))))))

theorem node_20545 : Outcome ⟨5, 20, 9, 8⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 12⟩) (by decide) node_15193

theorem node_20546 : Outcome ⟨6, 8, 20, 2⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 4⟩) (by decide) node_18997

theorem node_20547 : Outcome ⟨6, 8, 20, 14⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 26⟩) (by decide) node_8390

theorem node_20548 : Outcome ⟨6, 9, 19, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 19, 4⟩) (by decide) node_19004

theorem node_20549 : Outcome ⟨6, 10, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 10, 18, 2⟩, ⟨4, 10, 18, 4⟩, ⟨6, 9, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨6, 10, 17, 2⟩, ⟨6, 10, 16, 4⟩]
  exact AllWinning.cons node_19830 (AllWinning.cons node_18936 (AllWinning.cons node_19858 (AllWinning.cons node_19007 (AllWinning.cons node_19859 (AllWinning.cons node_19014 (AllWinning.nil))))))

theorem node_20550 : Outcome ⟨6, 10, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 10, 18, 2⟩, ⟨4, 10, 18, 4⟩, ⟨3, 10, 18, 6⟩, ⟨2, 10, 18, 8⟩, ⟨6, 9, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨6, 7, 18, 6⟩, ⟨6, 6, 18, 8⟩, ⟨6, 10, 17, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 10, 15, 6⟩, ⟨6, 10, 14, 8⟩]
  exact AllWinning.cons node_19830 (AllWinning.cons node_18936 (AllWinning.cons node_17979 (AllWinning.cons node_17052 (AllWinning.cons node_19858 (AllWinning.cons node_19007 (AllWinning.cons node_18103 (AllWinning.cons node_17214 (AllWinning.cons node_19859 (AllWinning.cons node_19014 (AllWinning.cons node_18111 (AllWinning.cons node_17223 (AllWinning.nil))))))))))))

theorem node_20551 : Outcome ⟨6, 10, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 10, 18, 2⟩, ⟨4, 10, 18, 4⟩, ⟨3, 10, 18, 6⟩, ⟨2, 10, 18, 8⟩, ⟨1, 10, 18, 10⟩, ⟨0, 10, 18, 12⟩, ⟨6, 9, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨6, 7, 18, 6⟩, ⟨6, 6, 18, 8⟩, ⟨6, 5, 18, 10⟩, ⟨6, 4, 18, 12⟩, ⟨6, 10, 17, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 10, 15, 6⟩, ⟨6, 10, 14, 8⟩, ⟨6, 10, 13, 10⟩, ⟨6, 10, 12, 12⟩]
  exact AllWinning.cons node_19830 (AllWinning.cons node_18936 (AllWinning.cons node_17979 (AllWinning.cons node_17052 (AllWinning.cons node_15949 (AllWinning.cons node_14927 (AllWinning.cons node_19858 (AllWinning.cons node_19007 (AllWinning.cons node_18103 (AllWinning.cons node_17214 (AllWinning.cons node_16205 (AllWinning.cons node_15221 (AllWinning.cons node_19859 (AllWinning.cons node_19014 (AllWinning.cons node_18111 (AllWinning.cons node_17223 (AllWinning.cons node_16224 (AllWinning.cons node_15239 (AllWinning.nil))))))))))))))))))

theorem node_20552 : Outcome ⟨6, 10, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 10, 18, 2⟩, ⟨4, 10, 18, 4⟩, ⟨3, 10, 18, 6⟩, ⟨2, 10, 18, 8⟩, ⟨1, 10, 18, 10⟩, ⟨0, 10, 18, 12⟩, ⟨6, 9, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨6, 7, 18, 6⟩, ⟨6, 6, 18, 8⟩, ⟨6, 5, 18, 10⟩, ⟨6, 4, 18, 12⟩, ⟨6, 3, 18, 14⟩, ⟨6, 2, 18, 16⟩, ⟨6, 10, 17, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 10, 15, 6⟩, ⟨6, 10, 14, 8⟩, ⟨6, 10, 13, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 10, 11, 14⟩, ⟨6, 10, 10, 16⟩]
  exact AllWinning.cons node_19830 (AllWinning.cons node_18936 (AllWinning.cons node_17979 (AllWinning.cons node_17052 (AllWinning.cons node_15949 (AllWinning.cons node_14927 (AllWinning.cons node_19858 (AllWinning.cons node_19007 (AllWinning.cons node_18103 (AllWinning.cons node_17214 (AllWinning.cons node_16205 (AllWinning.cons node_15221 (AllWinning.cons node_14269 (AllWinning.cons node_13300 (AllWinning.cons node_19859 (AllWinning.cons node_19014 (AllWinning.cons node_18111 (AllWinning.cons node_17223 (AllWinning.cons node_16224 (AllWinning.cons node_15239 (AllWinning.cons node_14291 (AllWinning.cons node_13328 (AllWinning.nil))))))))))))))))))))))

theorem node_20553 : Outcome ⟨6, 10, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 10, 18, 2⟩, ⟨4, 10, 18, 4⟩, ⟨3, 10, 18, 6⟩, ⟨2, 10, 18, 8⟩, ⟨1, 10, 18, 10⟩, ⟨0, 10, 18, 12⟩, ⟨6, 9, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨6, 7, 18, 6⟩, ⟨6, 6, 18, 8⟩, ⟨6, 5, 18, 10⟩, ⟨6, 4, 18, 12⟩, ⟨6, 3, 18, 14⟩, ⟨6, 2, 18, 16⟩, ⟨6, 1, 18, 18⟩, ⟨6, 0, 18, 20⟩, ⟨6, 10, 17, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 10, 15, 6⟩, ⟨6, 10, 14, 8⟩, ⟨6, 10, 13, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 10, 11, 14⟩, ⟨6, 10, 10, 16⟩, ⟨6, 10, 9, 18⟩, ⟨6, 10, 8, 20⟩]
  exact AllWinning.cons node_19830 (AllWinning.cons node_18936 (AllWinning.cons node_17979 (AllWinning.cons node_17052 (AllWinning.cons node_15949 (AllWinning.cons node_14927 (AllWinning.cons node_19858 (AllWinning.cons node_19007 (AllWinning.cons node_18103 (AllWinning.cons node_17214 (AllWinning.cons node_16205 (AllWinning.cons node_15221 (AllWinning.cons node_14269 (AllWinning.cons node_13300 (AllWinning.cons node_12350 (AllWinning.cons node_11366 (AllWinning.cons node_19859 (AllWinning.cons node_19014 (AllWinning.cons node_18111 (AllWinning.cons node_17223 (AllWinning.cons node_16224 (AllWinning.cons node_15239 (AllWinning.cons node_14291 (AllWinning.cons node_13328 (AllWinning.cons node_12384 (AllWinning.cons node_11401 (AllWinning.nil))))))))))))))))))))))))))

theorem node_20554 : Outcome ⟨6, 10, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 10, 18, 2⟩, ⟨4, 10, 18, 4⟩, ⟨3, 10, 18, 6⟩, ⟨2, 10, 18, 8⟩, ⟨1, 10, 18, 10⟩, ⟨0, 10, 18, 12⟩, ⟨6, 9, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨6, 7, 18, 6⟩, ⟨6, 6, 18, 8⟩, ⟨6, 5, 18, 10⟩, ⟨6, 4, 18, 12⟩, ⟨6, 3, 18, 14⟩, ⟨6, 2, 18, 16⟩, ⟨6, 1, 18, 18⟩, ⟨6, 0, 18, 20⟩, ⟨6, 10, 17, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 10, 15, 6⟩, ⟨6, 10, 14, 8⟩, ⟨6, 10, 13, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 10, 11, 14⟩, ⟨6, 10, 10, 16⟩, ⟨6, 10, 9, 18⟩, ⟨6, 10, 8, 20⟩, ⟨6, 10, 7, 22⟩, ⟨6, 10, 6, 24⟩]
  exact AllWinning.cons node_19830 (AllWinning.cons node_18936 (AllWinning.cons node_17979 (AllWinning.cons node_17052 (AllWinning.cons node_15949 (AllWinning.cons node_14927 (AllWinning.cons node_19858 (AllWinning.cons node_19007 (AllWinning.cons node_18103 (AllWinning.cons node_17214 (AllWinning.cons node_16205 (AllWinning.cons node_15221 (AllWinning.cons node_14269 (AllWinning.cons node_13300 (AllWinning.cons node_12350 (AllWinning.cons node_11366 (AllWinning.cons node_19859 (AllWinning.cons node_19014 (AllWinning.cons node_18111 (AllWinning.cons node_17223 (AllWinning.cons node_16224 (AllWinning.cons node_15239 (AllWinning.cons node_14291 (AllWinning.cons node_13328 (AllWinning.cons node_12384 (AllWinning.cons node_11401 (AllWinning.cons node_10385 (AllWinning.cons node_9379 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_20555 : Outcome ⟨6, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 8⟩) (by decide) node_17056

theorem node_20556 : Outcome ⟨6, 12, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.nil))))))

theorem node_20557 : Outcome ⟨6, 12, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨3, 12, 16, 6⟩, ⟨2, 12, 16, 8⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 9, 16, 6⟩, ⟨6, 8, 16, 8⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩, ⟨6, 12, 13, 6⟩, ⟨6, 12, 12, 8⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_17985 (AllWinning.cons node_17060 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_18107 (AllWinning.cons node_17217 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.cons node_18115 (AllWinning.cons node_17228 (AllWinning.nil))))))))))))

theorem node_20558 : Outcome ⟨6, 12, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨3, 12, 16, 6⟩, ⟨2, 12, 16, 8⟩, ⟨1, 12, 16, 10⟩, ⟨0, 12, 16, 12⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 9, 16, 6⟩, ⟨6, 8, 16, 8⟩, ⟨6, 7, 16, 10⟩, ⟨6, 6, 16, 12⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩, ⟨6, 12, 13, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 12, 11, 10⟩, ⟨6, 12, 10, 12⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_17985 (AllWinning.cons node_17060 (AllWinning.cons node_15956 (AllWinning.cons node_14934 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_18107 (AllWinning.cons node_17217 (AllWinning.cons node_16212 (AllWinning.cons node_15226 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.cons node_18115 (AllWinning.cons node_17228 (AllWinning.cons node_16233 (AllWinning.cons node_15244 (AllWinning.nil))))))))))))))))))

theorem node_20559 : Outcome ⟨6, 12, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨3, 12, 16, 6⟩, ⟨2, 12, 16, 8⟩, ⟨1, 12, 16, 10⟩, ⟨0, 12, 16, 12⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 9, 16, 6⟩, ⟨6, 8, 16, 8⟩, ⟨6, 7, 16, 10⟩, ⟨6, 6, 16, 12⟩, ⟨6, 5, 16, 14⟩, ⟨6, 4, 16, 16⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩, ⟨6, 12, 13, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 12, 11, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 12, 9, 14⟩, ⟨6, 12, 8, 16⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_17985 (AllWinning.cons node_17060 (AllWinning.cons node_15956 (AllWinning.cons node_14934 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_18107 (AllWinning.cons node_17217 (AllWinning.cons node_16212 (AllWinning.cons node_15226 (AllWinning.cons node_14275 (AllWinning.cons node_13308 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.cons node_18115 (AllWinning.cons node_17228 (AllWinning.cons node_16233 (AllWinning.cons node_15244 (AllWinning.cons node_14297 (AllWinning.cons node_13335 (AllWinning.nil))))))))))))))))))))))

theorem node_20560 : Outcome ⟨6, 12, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨3, 12, 16, 6⟩, ⟨2, 12, 16, 8⟩, ⟨1, 12, 16, 10⟩, ⟨0, 12, 16, 12⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 9, 16, 6⟩, ⟨6, 8, 16, 8⟩, ⟨6, 7, 16, 10⟩, ⟨6, 6, 16, 12⟩, ⟨6, 5, 16, 14⟩, ⟨6, 4, 16, 16⟩, ⟨6, 3, 16, 18⟩, ⟨6, 2, 16, 20⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩, ⟨6, 12, 13, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 12, 11, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 12, 9, 14⟩, ⟨6, 12, 8, 16⟩, ⟨6, 12, 7, 18⟩, ⟨6, 12, 6, 20⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_17985 (AllWinning.cons node_17060 (AllWinning.cons node_15956 (AllWinning.cons node_14934 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_18107 (AllWinning.cons node_17217 (AllWinning.cons node_16212 (AllWinning.cons node_15226 (AllWinning.cons node_14275 (AllWinning.cons node_13308 (AllWinning.cons node_12358 (AllWinning.cons node_11372 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.cons node_18115 (AllWinning.cons node_17228 (AllWinning.cons node_16233 (AllWinning.cons node_15244 (AllWinning.cons node_14297 (AllWinning.cons node_13335 (AllWinning.cons node_12392 (AllWinning.cons node_11411 (AllWinning.nil))))))))))))))))))))))))))

theorem node_20561 : Outcome ⟨6, 12, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨3, 12, 16, 6⟩, ⟨2, 12, 16, 8⟩, ⟨1, 12, 16, 10⟩, ⟨0, 12, 16, 12⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 9, 16, 6⟩, ⟨6, 8, 16, 8⟩, ⟨6, 7, 16, 10⟩, ⟨6, 6, 16, 12⟩, ⟨6, 5, 16, 14⟩, ⟨6, 4, 16, 16⟩, ⟨6, 3, 16, 18⟩, ⟨6, 2, 16, 20⟩, ⟨6, 1, 16, 22⟩, ⟨6, 0, 16, 24⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩, ⟨6, 12, 13, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 12, 11, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 12, 9, 14⟩, ⟨6, 12, 8, 16⟩, ⟨6, 12, 7, 18⟩, ⟨6, 12, 6, 20⟩, ⟨6, 12, 5, 22⟩, ⟨6, 12, 4, 24⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_17985 (AllWinning.cons node_17060 (AllWinning.cons node_15956 (AllWinning.cons node_14934 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_18107 (AllWinning.cons node_17217 (AllWinning.cons node_16212 (AllWinning.cons node_15226 (AllWinning.cons node_14275 (AllWinning.cons node_13308 (AllWinning.cons node_12358 (AllWinning.cons node_11372 (AllWinning.cons node_10346 (AllWinning.cons node_9339 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.cons node_18115 (AllWinning.cons node_17228 (AllWinning.cons node_16233 (AllWinning.cons node_15244 (AllWinning.cons node_14297 (AllWinning.cons node_13335 (AllWinning.cons node_12392 (AllWinning.cons node_11411 (AllWinning.cons node_10390 (AllWinning.cons node_9386 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_20562 : Outcome ⟨6, 12, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨3, 12, 16, 6⟩, ⟨2, 12, 16, 8⟩, ⟨1, 12, 16, 10⟩, ⟨0, 12, 16, 12⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 9, 16, 6⟩, ⟨6, 8, 16, 8⟩, ⟨6, 7, 16, 10⟩, ⟨6, 6, 16, 12⟩, ⟨6, 5, 16, 14⟩, ⟨6, 4, 16, 16⟩, ⟨6, 3, 16, 18⟩, ⟨6, 2, 16, 20⟩, ⟨6, 1, 16, 22⟩, ⟨6, 0, 16, 24⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩, ⟨6, 12, 13, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 12, 11, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 12, 9, 14⟩, ⟨6, 12, 8, 16⟩, ⟨6, 12, 7, 18⟩, ⟨6, 12, 6, 20⟩, ⟨6, 12, 5, 22⟩, ⟨6, 12, 4, 24⟩, ⟨6, 12, 3, 26⟩, ⟨6, 12, 2, 28⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_17985 (AllWinning.cons node_17060 (AllWinning.cons node_15956 (AllWinning.cons node_14934 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_18107 (AllWinning.cons node_17217 (AllWinning.cons node_16212 (AllWinning.cons node_15226 (AllWinning.cons node_14275 (AllWinning.cons node_13308 (AllWinning.cons node_12358 (AllWinning.cons node_11372 (AllWinning.cons node_10346 (AllWinning.cons node_9339 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.cons node_18115 (AllWinning.cons node_17228 (AllWinning.cons node_16233 (AllWinning.cons node_15244 (AllWinning.cons node_14297 (AllWinning.cons node_13335 (AllWinning.cons node_12392 (AllWinning.cons node_11411 (AllWinning.cons node_10390 (AllWinning.cons node_9386 (AllWinning.cons node_8404 (AllWinning.cons node_7472 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_20563 : Outcome ⟨6, 12, 16, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 16, 2⟩, ⟨4, 12, 16, 4⟩, ⟨3, 12, 16, 6⟩, ⟨2, 12, 16, 8⟩, ⟨1, 12, 16, 10⟩, ⟨0, 12, 16, 12⟩, ⟨6, 11, 16, 2⟩, ⟨6, 10, 16, 4⟩, ⟨6, 9, 16, 6⟩, ⟨6, 8, 16, 8⟩, ⟨6, 7, 16, 10⟩, ⟨6, 6, 16, 12⟩, ⟨6, 5, 16, 14⟩, ⟨6, 4, 16, 16⟩, ⟨6, 3, 16, 18⟩, ⟨6, 2, 16, 20⟩, ⟨6, 1, 16, 22⟩, ⟨6, 0, 16, 24⟩, ⟨6, 12, 15, 2⟩, ⟨6, 12, 14, 4⟩, ⟨6, 12, 13, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 12, 11, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 12, 9, 14⟩, ⟨6, 12, 8, 16⟩, ⟨6, 12, 7, 18⟩, ⟨6, 12, 6, 20⟩, ⟨6, 12, 5, 22⟩, ⟨6, 12, 4, 24⟩, ⟨6, 12, 3, 26⟩, ⟨6, 12, 2, 28⟩, ⟨6, 12, 1, 30⟩, ⟨6, 12, 0, 32⟩]
  exact AllWinning.cons node_19834 (AllWinning.cons node_18941 (AllWinning.cons node_17985 (AllWinning.cons node_17060 (AllWinning.cons node_15956 (AllWinning.cons node_14934 (AllWinning.cons node_19861 (AllWinning.cons node_19014 (AllWinning.cons node_18107 (AllWinning.cons node_17217 (AllWinning.cons node_16212 (AllWinning.cons node_15226 (AllWinning.cons node_14275 (AllWinning.cons node_13308 (AllWinning.cons node_12358 (AllWinning.cons node_11372 (AllWinning.cons node_10346 (AllWinning.cons node_9339 (AllWinning.cons node_19862 (AllWinning.cons node_19022 (AllWinning.cons node_18115 (AllWinning.cons node_17228 (AllWinning.cons node_16233 (AllWinning.cons node_15244 (AllWinning.cons node_14297 (AllWinning.cons node_13335 (AllWinning.cons node_12392 (AllWinning.cons node_11411 (AllWinning.cons node_10390 (AllWinning.cons node_9386 (AllWinning.cons node_8404 (AllWinning.cons node_7472 (AllWinning.cons node_6543 (AllWinning.cons node_5728 (AllWinning.nil))))))))))))))))))))))))))))))))))

theorem node_20564 : Outcome ⟨6, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 4⟩) (by decide) node_19017

theorem node_20565 : Outcome ⟨6, 13, 15, 6⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 4⟩) (by decide) node_19017

theorem node_20566 : Outcome ⟨6, 13, 15, 14⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 4⟩) (by decide) node_19017

theorem node_20567 : Outcome ⟨6, 14, 14, 6⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 12⟩) (by decide) node_14942

theorem node_20568 : Outcome ⟨6, 14, 14, 16⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 12⟩) (by decide) node_14942

theorem node_20569 : Outcome ⟨6, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 4⟩) (by decide) node_19029

theorem node_20570 : Outcome ⟨6, 15, 13, 6⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 4⟩) (by decide) node_19029

theorem node_20571 : Outcome ⟨6, 15, 13, 14⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 4⟩) (by decide) node_19029

theorem node_20572 : Outcome ⟨6, 16, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.nil))))))

theorem node_20573 : Outcome ⟨6, 16, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨3, 16, 12, 6⟩, ⟨2, 16, 12, 8⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 13, 12, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 16, 9, 6⟩, ⟨6, 16, 8, 8⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_18001 (AllWinning.cons node_17074 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_18117 (AllWinning.cons node_17228 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.cons node_18124 (AllWinning.cons node_17239 (AllWinning.nil))))))))))))

theorem node_20574 : Outcome ⟨6, 16, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨3, 16, 12, 6⟩, ⟨2, 16, 12, 8⟩, ⟨1, 16, 12, 10⟩, ⟨0, 16, 12, 12⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 13, 12, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 11, 12, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 16, 9, 6⟩, ⟨6, 16, 8, 8⟩, ⟨6, 16, 7, 10⟩, ⟨6, 16, 6, 12⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_18001 (AllWinning.cons node_17074 (AllWinning.cons node_15970 (AllWinning.cons node_14950 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_18117 (AllWinning.cons node_17228 (AllWinning.cons node_16228 (AllWinning.cons node_15239 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.cons node_18124 (AllWinning.cons node_17239 (AllWinning.cons node_16249 (AllWinning.cons node_15258 (AllWinning.nil))))))))))))))))))

theorem node_20575 : Outcome ⟨6, 16, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨3, 16, 12, 6⟩, ⟨2, 16, 12, 8⟩, ⟨1, 16, 12, 10⟩, ⟨0, 16, 12, 12⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 13, 12, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 11, 12, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 9, 12, 14⟩, ⟨6, 8, 12, 16⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 16, 9, 6⟩, ⟨6, 16, 8, 8⟩, ⟨6, 16, 7, 10⟩, ⟨6, 16, 6, 12⟩, ⟨6, 16, 5, 14⟩, ⟨6, 16, 4, 16⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_18001 (AllWinning.cons node_17074 (AllWinning.cons node_15970 (AllWinning.cons node_14950 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_18117 (AllWinning.cons node_17228 (AllWinning.cons node_16228 (AllWinning.cons node_15239 (AllWinning.cons node_14288 (AllWinning.cons node_13323 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.cons node_18124 (AllWinning.cons node_17239 (AllWinning.cons node_16249 (AllWinning.cons node_15258 (AllWinning.cons node_14310 (AllWinning.cons node_13350 (AllWinning.nil))))))))))))))))))))))

theorem node_20576 : Outcome ⟨6, 16, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨3, 16, 12, 6⟩, ⟨2, 16, 12, 8⟩, ⟨1, 16, 12, 10⟩, ⟨0, 16, 12, 12⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 13, 12, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 11, 12, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 9, 12, 14⟩, ⟨6, 8, 12, 16⟩, ⟨6, 7, 12, 18⟩, ⟨6, 6, 12, 20⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 16, 9, 6⟩, ⟨6, 16, 8, 8⟩, ⟨6, 16, 7, 10⟩, ⟨6, 16, 6, 12⟩, ⟨6, 16, 5, 14⟩, ⟨6, 16, 4, 16⟩, ⟨6, 16, 3, 18⟩, ⟨6, 16, 2, 20⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_18001 (AllWinning.cons node_17074 (AllWinning.cons node_15970 (AllWinning.cons node_14950 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_18117 (AllWinning.cons node_17228 (AllWinning.cons node_16228 (AllWinning.cons node_15239 (AllWinning.cons node_14288 (AllWinning.cons node_13323 (AllWinning.cons node_12372 (AllWinning.cons node_11386 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.cons node_18124 (AllWinning.cons node_17239 (AllWinning.cons node_16249 (AllWinning.cons node_15258 (AllWinning.cons node_14310 (AllWinning.cons node_13350 (AllWinning.cons node_12405 (AllWinning.cons node_11422 (AllWinning.nil))))))))))))))))))))))))))

theorem node_20577 : Outcome ⟨6, 16, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨3, 16, 12, 6⟩, ⟨2, 16, 12, 8⟩, ⟨1, 16, 12, 10⟩, ⟨0, 16, 12, 12⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 13, 12, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 11, 12, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 9, 12, 14⟩, ⟨6, 8, 12, 16⟩, ⟨6, 7, 12, 18⟩, ⟨6, 6, 12, 20⟩, ⟨6, 5, 12, 22⟩, ⟨6, 4, 12, 24⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 16, 9, 6⟩, ⟨6, 16, 8, 8⟩, ⟨6, 16, 7, 10⟩, ⟨6, 16, 6, 12⟩, ⟨6, 16, 5, 14⟩, ⟨6, 16, 4, 16⟩, ⟨6, 16, 3, 18⟩, ⟨6, 16, 2, 20⟩, ⟨6, 16, 1, 22⟩, ⟨6, 16, 0, 24⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_18001 (AllWinning.cons node_17074 (AllWinning.cons node_15970 (AllWinning.cons node_14950 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_18117 (AllWinning.cons node_17228 (AllWinning.cons node_16228 (AllWinning.cons node_15239 (AllWinning.cons node_14288 (AllWinning.cons node_13323 (AllWinning.cons node_12372 (AllWinning.cons node_11386 (AllWinning.cons node_10362 (AllWinning.cons node_9355 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.cons node_18124 (AllWinning.cons node_17239 (AllWinning.cons node_16249 (AllWinning.cons node_15258 (AllWinning.cons node_14310 (AllWinning.cons node_13350 (AllWinning.cons node_12405 (AllWinning.cons node_11422 (AllWinning.cons node_10412 (AllWinning.cons node_9403 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_20578 : Outcome ⟨6, 16, 12, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨3, 16, 12, 6⟩, ⟨2, 16, 12, 8⟩, ⟨1, 16, 12, 10⟩, ⟨0, 16, 12, 12⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 13, 12, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 11, 12, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 9, 12, 14⟩, ⟨6, 8, 12, 16⟩, ⟨6, 7, 12, 18⟩, ⟨6, 6, 12, 20⟩, ⟨6, 5, 12, 22⟩, ⟨6, 4, 12, 24⟩, ⟨6, 3, 12, 26⟩, ⟨6, 2, 12, 28⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 16, 9, 6⟩, ⟨6, 16, 8, 8⟩, ⟨6, 16, 7, 10⟩, ⟨6, 16, 6, 12⟩, ⟨6, 16, 5, 14⟩, ⟨6, 16, 4, 16⟩, ⟨6, 16, 3, 18⟩, ⟨6, 16, 2, 20⟩, ⟨6, 16, 1, 22⟩, ⟨6, 16, 0, 24⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_18001 (AllWinning.cons node_17074 (AllWinning.cons node_15970 (AllWinning.cons node_14950 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_18117 (AllWinning.cons node_17228 (AllWinning.cons node_16228 (AllWinning.cons node_15239 (AllWinning.cons node_14288 (AllWinning.cons node_13323 (AllWinning.cons node_12372 (AllWinning.cons node_11386 (AllWinning.cons node_10362 (AllWinning.cons node_9355 (AllWinning.cons node_8355 (AllWinning.cons node_7422 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.cons node_18124 (AllWinning.cons node_17239 (AllWinning.cons node_16249 (AllWinning.cons node_15258 (AllWinning.cons node_14310 (AllWinning.cons node_13350 (AllWinning.cons node_12405 (AllWinning.cons node_11422 (AllWinning.cons node_10412 (AllWinning.cons node_9403 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_20579 : Outcome ⟨6, 16, 12, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 12, 2⟩, ⟨4, 16, 12, 4⟩, ⟨3, 16, 12, 6⟩, ⟨2, 16, 12, 8⟩, ⟨1, 16, 12, 10⟩, ⟨0, 16, 12, 12⟩, ⟨6, 15, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨6, 13, 12, 6⟩, ⟨6, 12, 12, 8⟩, ⟨6, 11, 12, 10⟩, ⟨6, 10, 12, 12⟩, ⟨6, 9, 12, 14⟩, ⟨6, 8, 12, 16⟩, ⟨6, 7, 12, 18⟩, ⟨6, 6, 12, 20⟩, ⟨6, 5, 12, 22⟩, ⟨6, 4, 12, 24⟩, ⟨6, 3, 12, 26⟩, ⟨6, 2, 12, 28⟩, ⟨6, 1, 12, 30⟩, ⟨6, 0, 12, 32⟩, ⟨6, 16, 11, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 16, 9, 6⟩, ⟨6, 16, 8, 8⟩, ⟨6, 16, 7, 10⟩, ⟨6, 16, 6, 12⟩, ⟨6, 16, 5, 14⟩, ⟨6, 16, 4, 16⟩, ⟨6, 16, 3, 18⟩, ⟨6, 16, 2, 20⟩, ⟨6, 16, 1, 22⟩, ⟨6, 16, 0, 24⟩]
  exact AllWinning.cons node_19845 (AllWinning.cons node_18955 (AllWinning.cons node_18001 (AllWinning.cons node_17074 (AllWinning.cons node_15970 (AllWinning.cons node_14950 (AllWinning.cons node_19878 (AllWinning.cons node_19027 (AllWinning.cons node_18117 (AllWinning.cons node_17228 (AllWinning.cons node_16228 (AllWinning.cons node_15239 (AllWinning.cons node_14288 (AllWinning.cons node_13323 (AllWinning.cons node_12372 (AllWinning.cons node_11386 (AllWinning.cons node_10362 (AllWinning.cons node_9355 (AllWinning.cons node_8355 (AllWinning.cons node_7422 (AllWinning.cons node_6495 (AllWinning.cons node_5685 (AllWinning.cons node_19880 (AllWinning.cons node_19034 (AllWinning.cons node_18124 (AllWinning.cons node_17239 (AllWinning.cons node_16249 (AllWinning.cons node_15258 (AllWinning.cons node_14310 (AllWinning.cons node_13350 (AllWinning.cons node_12405 (AllWinning.cons node_11422 (AllWinning.cons node_10412 (AllWinning.cons node_9403 (AllWinning.nil))))))))))))))))))))))))))))))))))

theorem node_20580 : Outcome ⟨6, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 8⟩) (by decide) node_17078

theorem node_20581 : Outcome ⟨6, 18, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 10, 2⟩, ⟨4, 18, 10, 4⟩, ⟨6, 17, 10, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 18, 9, 2⟩, ⟨6, 18, 8, 4⟩]
  exact AllWinning.cons node_19850 (AllWinning.cons node_18960 (AllWinning.cons node_19881 (AllWinning.cons node_19034 (AllWinning.cons node_19883 (AllWinning.cons node_19042 (AllWinning.nil))))))

theorem node_20582 : Outcome ⟨6, 18, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 10, 2⟩, ⟨4, 18, 10, 4⟩, ⟨3, 18, 10, 6⟩, ⟨2, 18, 10, 8⟩, ⟨6, 17, 10, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 15, 10, 6⟩, ⟨6, 14, 10, 8⟩, ⟨6, 18, 9, 2⟩, ⟨6, 18, 8, 4⟩, ⟨6, 18, 7, 6⟩, ⟨6, 18, 6, 8⟩]
  exact AllWinning.cons node_19850 (AllWinning.cons node_18960 (AllWinning.cons node_18008 (AllWinning.cons node_17082 (AllWinning.cons node_19881 (AllWinning.cons node_19034 (AllWinning.cons node_18122 (AllWinning.cons node_17234 (AllWinning.cons node_19883 (AllWinning.cons node_19042 (AllWinning.cons node_18128 (AllWinning.cons node_17243 (AllWinning.nil))))))))))))

theorem node_20583 : Outcome ⟨6, 18, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 10, 2⟩, ⟨4, 18, 10, 4⟩, ⟨3, 18, 10, 6⟩, ⟨2, 18, 10, 8⟩, ⟨1, 18, 10, 10⟩, ⟨0, 18, 10, 12⟩, ⟨6, 17, 10, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 15, 10, 6⟩, ⟨6, 14, 10, 8⟩, ⟨6, 13, 10, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 18, 9, 2⟩, ⟨6, 18, 8, 4⟩, ⟨6, 18, 7, 6⟩, ⟨6, 18, 6, 8⟩, ⟨6, 18, 5, 10⟩, ⟨6, 18, 4, 12⟩]
  exact AllWinning.cons node_19850 (AllWinning.cons node_18960 (AllWinning.cons node_18008 (AllWinning.cons node_17082 (AllWinning.cons node_15975 (AllWinning.cons node_14957 (AllWinning.cons node_19881 (AllWinning.cons node_19034 (AllWinning.cons node_18122 (AllWinning.cons node_17234 (AllWinning.cons node_16237 (AllWinning.cons node_15244 (AllWinning.cons node_19883 (AllWinning.cons node_19042 (AllWinning.cons node_18128 (AllWinning.cons node_17243 (AllWinning.cons node_16254 (AllWinning.cons node_15263 (AllWinning.nil))))))))))))))))))

theorem node_20584 : Outcome ⟨6, 18, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 10, 2⟩, ⟨4, 18, 10, 4⟩, ⟨3, 18, 10, 6⟩, ⟨2, 18, 10, 8⟩, ⟨1, 18, 10, 10⟩, ⟨0, 18, 10, 12⟩, ⟨6, 17, 10, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 15, 10, 6⟩, ⟨6, 14, 10, 8⟩, ⟨6, 13, 10, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 11, 10, 14⟩, ⟨6, 10, 10, 16⟩, ⟨6, 18, 9, 2⟩, ⟨6, 18, 8, 4⟩, ⟨6, 18, 7, 6⟩, ⟨6, 18, 6, 8⟩, ⟨6, 18, 5, 10⟩, ⟨6, 18, 4, 12⟩, ⟨6, 18, 3, 14⟩, ⟨6, 18, 2, 16⟩]
  exact AllWinning.cons node_19850 (AllWinning.cons node_18960 (AllWinning.cons node_18008 (AllWinning.cons node_17082 (AllWinning.cons node_15975 (AllWinning.cons node_14957 (AllWinning.cons node_19881 (AllWinning.cons node_19034 (AllWinning.cons node_18122 (AllWinning.cons node_17234 (AllWinning.cons node_16237 (AllWinning.cons node_15244 (AllWinning.cons node_14294 (AllWinning.cons node_13328 (AllWinning.cons node_19883 (AllWinning.cons node_19042 (AllWinning.cons node_18128 (AllWinning.cons node_17243 (AllWinning.cons node_16254 (AllWinning.cons node_15263 (AllWinning.cons node_14315 (AllWinning.cons node_13356 (AllWinning.nil))))))))))))))))))))))

theorem node_20585 : Outcome ⟨6, 18, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 10, 2⟩, ⟨4, 18, 10, 4⟩, ⟨3, 18, 10, 6⟩, ⟨2, 18, 10, 8⟩, ⟨1, 18, 10, 10⟩, ⟨0, 18, 10, 12⟩, ⟨6, 17, 10, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 15, 10, 6⟩, ⟨6, 14, 10, 8⟩, ⟨6, 13, 10, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 11, 10, 14⟩, ⟨6, 10, 10, 16⟩, ⟨6, 9, 10, 18⟩, ⟨6, 8, 10, 20⟩, ⟨6, 18, 9, 2⟩, ⟨6, 18, 8, 4⟩, ⟨6, 18, 7, 6⟩, ⟨6, 18, 6, 8⟩, ⟨6, 18, 5, 10⟩, ⟨6, 18, 4, 12⟩, ⟨6, 18, 3, 14⟩, ⟨6, 18, 2, 16⟩, ⟨6, 18, 1, 18⟩, ⟨6, 18, 0, 20⟩]
  exact AllWinning.cons node_19850 (AllWinning.cons node_18960 (AllWinning.cons node_18008 (AllWinning.cons node_17082 (AllWinning.cons node_15975 (AllWinning.cons node_14957 (AllWinning.cons node_19881 (AllWinning.cons node_19034 (AllWinning.cons node_18122 (AllWinning.cons node_17234 (AllWinning.cons node_16237 (AllWinning.cons node_15244 (AllWinning.cons node_14294 (AllWinning.cons node_13328 (AllWinning.cons node_12380 (AllWinning.cons node_11394 (AllWinning.cons node_19883 (AllWinning.cons node_19042 (AllWinning.cons node_18128 (AllWinning.cons node_17243 (AllWinning.cons node_16254 (AllWinning.cons node_15263 (AllWinning.cons node_14315 (AllWinning.cons node_13356 (AllWinning.cons node_12412 (AllWinning.cons node_11428 (AllWinning.nil))))))))))))))))))))))))))

end RQ9F1
