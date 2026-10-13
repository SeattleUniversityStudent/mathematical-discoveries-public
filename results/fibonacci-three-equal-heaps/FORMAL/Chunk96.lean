import Chunk95
set_option autoImplicit false
namespace RQ9F1

theorem node_20586 : Outcome ⟨6, 18, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 10, 2⟩, ⟨4, 18, 10, 4⟩, ⟨3, 18, 10, 6⟩, ⟨2, 18, 10, 8⟩, ⟨1, 18, 10, 10⟩, ⟨0, 18, 10, 12⟩, ⟨6, 17, 10, 2⟩, ⟨6, 16, 10, 4⟩, ⟨6, 15, 10, 6⟩, ⟨6, 14, 10, 8⟩, ⟨6, 13, 10, 10⟩, ⟨6, 12, 10, 12⟩, ⟨6, 11, 10, 14⟩, ⟨6, 10, 10, 16⟩, ⟨6, 9, 10, 18⟩, ⟨6, 8, 10, 20⟩, ⟨6, 7, 10, 22⟩, ⟨6, 6, 10, 24⟩, ⟨6, 18, 9, 2⟩, ⟨6, 18, 8, 4⟩, ⟨6, 18, 7, 6⟩, ⟨6, 18, 6, 8⟩, ⟨6, 18, 5, 10⟩, ⟨6, 18, 4, 12⟩, ⟨6, 18, 3, 14⟩, ⟨6, 18, 2, 16⟩, ⟨6, 18, 1, 18⟩, ⟨6, 18, 0, 20⟩]
  exact AllWinning.cons node_19850 (AllWinning.cons node_18960 (AllWinning.cons node_18008 (AllWinning.cons node_17082 (AllWinning.cons node_15975 (AllWinning.cons node_14957 (AllWinning.cons node_19881 (AllWinning.cons node_19034 (AllWinning.cons node_18122 (AllWinning.cons node_17234 (AllWinning.cons node_16237 (AllWinning.cons node_15244 (AllWinning.cons node_14294 (AllWinning.cons node_13328 (AllWinning.cons node_12380 (AllWinning.cons node_11394 (AllWinning.cons node_10371 (AllWinning.cons node_9362 (AllWinning.cons node_19883 (AllWinning.cons node_19042 (AllWinning.cons node_18128 (AllWinning.cons node_17243 (AllWinning.cons node_16254 (AllWinning.cons node_15263 (AllWinning.cons node_14315 (AllWinning.cons node_13356 (AllWinning.cons node_12412 (AllWinning.cons node_11428 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_20587 : Outcome ⟨6, 19, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 4⟩) (by decide) node_19037

theorem node_20588 : Outcome ⟨6, 20, 8, 2⟩ true :=
  Outcome.win (q := ⟨6, 20, 6, 4⟩) (by decide) node_19047

theorem node_20589 : Outcome ⟨6, 20, 8, 14⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 26⟩) (by decide) node_8378

theorem node_20590 : Outcome ⟨7, 7, 20, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 18, 4⟩) (by decide) node_19061

theorem node_20591 : Outcome ⟨7, 7, 20, 18⟩ true :=
  Outcome.win (q := ⟨7, 7, 18, 4⟩) (by decide) node_19061

theorem node_20592 : Outcome ⟨7, 8, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 19, 4⟩) (by decide) node_19057

theorem node_20593 : Outcome ⟨7, 8, 19, 12⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 10⟩) (by decide) node_15988

theorem node_20594 : Outcome ⟨7, 9, 18, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 18, 4⟩) (by decide) node_19061

theorem node_20595 : Outcome ⟨7, 9, 18, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 14⟩) (by decide) node_14335

theorem node_20596 : Outcome ⟨7, 10, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 10, 17, 2⟩, ⟨5, 10, 17, 4⟩, ⟨7, 9, 17, 2⟩, ⟨7, 8, 17, 4⟩, ⟨7, 10, 16, 2⟩, ⟨7, 10, 15, 4⟩]
  exact AllWinning.cons node_19859 (AllWinning.cons node_18974 (AllWinning.cons node_19893 (AllWinning.cons node_19064 (AllWinning.cons node_19894 (AllWinning.cons node_19071 (AllWinning.nil))))))

theorem node_20597 : Outcome ⟨7, 10, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 10, 17, 2⟩, ⟨5, 10, 17, 4⟩, ⟨4, 10, 17, 6⟩, ⟨3, 10, 17, 8⟩, ⟨7, 9, 17, 2⟩, ⟨7, 8, 17, 4⟩, ⟨7, 7, 17, 6⟩, ⟨7, 6, 17, 8⟩, ⟨7, 10, 16, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 10, 14, 6⟩, ⟨7, 10, 13, 8⟩]
  exact AllWinning.cons node_19859 (AllWinning.cons node_18974 (AllWinning.cons node_18021 (AllWinning.cons node_17095 (AllWinning.cons node_19893 (AllWinning.cons node_19064 (AllWinning.cons node_18144 (AllWinning.cons node_17258 (AllWinning.cons node_19894 (AllWinning.cons node_19071 (AllWinning.cons node_18154 (AllWinning.cons node_17270 (AllWinning.nil))))))))))))

theorem node_20598 : Outcome ⟨7, 10, 17, 6⟩ true :=
  Outcome.win (q := ⟨7, 5, 17, 10⟩) (by decide) node_16272

theorem node_20599 : Outcome ⟨7, 11, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 16, 2⟩, ⟨5, 11, 16, 4⟩, ⟨7, 10, 16, 2⟩, ⟨7, 9, 16, 4⟩, ⟨7, 11, 15, 2⟩, ⟨7, 11, 14, 4⟩]
  exact AllWinning.cons node_19861 (AllWinning.cons node_18977 (AllWinning.cons node_19894 (AllWinning.cons node_19067 (AllWinning.cons node_19897 (AllWinning.cons node_19073 (AllWinning.nil))))))

theorem node_20600 : Outcome ⟨7, 11, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 16, 2⟩, ⟨5, 11, 16, 4⟩, ⟨4, 11, 16, 6⟩, ⟨3, 11, 16, 8⟩, ⟨7, 10, 16, 2⟩, ⟨7, 9, 16, 4⟩, ⟨7, 8, 16, 6⟩, ⟨7, 7, 16, 8⟩, ⟨7, 11, 15, 2⟩, ⟨7, 11, 14, 4⟩, ⟨7, 11, 13, 6⟩, ⟨7, 11, 12, 8⟩]
  exact AllWinning.cons node_19861 (AllWinning.cons node_18977 (AllWinning.cons node_18026 (AllWinning.cons node_17099 (AllWinning.cons node_19894 (AllWinning.cons node_19067 (AllWinning.cons node_18146 (AllWinning.cons node_17260 (AllWinning.cons node_19897 (AllWinning.cons node_19073 (AllWinning.cons node_18157 (AllWinning.cons node_17273 (AllWinning.nil))))))))))))

theorem node_20601 : Outcome ⟨7, 11, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 16, 2⟩, ⟨5, 11, 16, 4⟩, ⟨4, 11, 16, 6⟩, ⟨3, 11, 16, 8⟩, ⟨2, 11, 16, 10⟩, ⟨1, 11, 16, 12⟩, ⟨7, 10, 16, 2⟩, ⟨7, 9, 16, 4⟩, ⟨7, 8, 16, 6⟩, ⟨7, 7, 16, 8⟩, ⟨7, 6, 16, 10⟩, ⟨7, 5, 16, 12⟩, ⟨7, 11, 15, 2⟩, ⟨7, 11, 14, 4⟩, ⟨7, 11, 13, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 11, 10, 12⟩]
  exact AllWinning.cons node_19861 (AllWinning.cons node_18977 (AllWinning.cons node_18026 (AllWinning.cons node_17099 (AllWinning.cons node_15997 (AllWinning.cons node_14977 (AllWinning.cons node_19894 (AllWinning.cons node_19067 (AllWinning.cons node_18146 (AllWinning.cons node_17260 (AllWinning.cons node_16276 (AllWinning.cons node_15279 (AllWinning.cons node_19897 (AllWinning.cons node_19073 (AllWinning.cons node_18157 (AllWinning.cons node_17273 (AllWinning.cons node_16295 (AllWinning.cons node_15297 (AllWinning.nil))))))))))))))))))

theorem node_20602 : Outcome ⟨7, 11, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 16, 2⟩, ⟨5, 11, 16, 4⟩, ⟨4, 11, 16, 6⟩, ⟨3, 11, 16, 8⟩, ⟨2, 11, 16, 10⟩, ⟨1, 11, 16, 12⟩, ⟨0, 11, 16, 14⟩, ⟨7, 10, 16, 2⟩, ⟨7, 9, 16, 4⟩, ⟨7, 8, 16, 6⟩, ⟨7, 7, 16, 8⟩, ⟨7, 6, 16, 10⟩, ⟨7, 5, 16, 12⟩, ⟨7, 4, 16, 14⟩, ⟨7, 3, 16, 16⟩, ⟨7, 11, 15, 2⟩, ⟨7, 11, 14, 4⟩, ⟨7, 11, 13, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 11, 10, 12⟩, ⟨7, 11, 9, 14⟩, ⟨7, 11, 8, 16⟩]
  exact AllWinning.cons node_19861 (AllWinning.cons node_18977 (AllWinning.cons node_18026 (AllWinning.cons node_17099 (AllWinning.cons node_15997 (AllWinning.cons node_14977 (AllWinning.cons node_13963 (AllWinning.cons node_19894 (AllWinning.cons node_19067 (AllWinning.cons node_18146 (AllWinning.cons node_17260 (AllWinning.cons node_16276 (AllWinning.cons node_15279 (AllWinning.cons node_14340 (AllWinning.cons node_13372 (AllWinning.cons node_19897 (AllWinning.cons node_19073 (AllWinning.cons node_18157 (AllWinning.cons node_17273 (AllWinning.cons node_16295 (AllWinning.cons node_15297 (AllWinning.cons node_14365 (AllWinning.cons node_13399 (AllWinning.nil)))))))))))))))))))))))

theorem node_20603 : Outcome ⟨7, 11, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 16, 2⟩, ⟨5, 11, 16, 4⟩, ⟨4, 11, 16, 6⟩, ⟨3, 11, 16, 8⟩, ⟨2, 11, 16, 10⟩, ⟨1, 11, 16, 12⟩, ⟨0, 11, 16, 14⟩, ⟨7, 10, 16, 2⟩, ⟨7, 9, 16, 4⟩, ⟨7, 8, 16, 6⟩, ⟨7, 7, 16, 8⟩, ⟨7, 6, 16, 10⟩, ⟨7, 5, 16, 12⟩, ⟨7, 4, 16, 14⟩, ⟨7, 3, 16, 16⟩, ⟨7, 2, 16, 18⟩, ⟨7, 1, 16, 20⟩, ⟨7, 11, 15, 2⟩, ⟨7, 11, 14, 4⟩, ⟨7, 11, 13, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 11, 10, 12⟩, ⟨7, 11, 9, 14⟩, ⟨7, 11, 8, 16⟩, ⟨7, 11, 7, 18⟩, ⟨7, 11, 6, 20⟩]
  exact AllWinning.cons node_19861 (AllWinning.cons node_18977 (AllWinning.cons node_18026 (AllWinning.cons node_17099 (AllWinning.cons node_15997 (AllWinning.cons node_14977 (AllWinning.cons node_13963 (AllWinning.cons node_19894 (AllWinning.cons node_19067 (AllWinning.cons node_18146 (AllWinning.cons node_17260 (AllWinning.cons node_16276 (AllWinning.cons node_15279 (AllWinning.cons node_14340 (AllWinning.cons node_13372 (AllWinning.cons node_12429 (AllWinning.cons node_11437 (AllWinning.cons node_19897 (AllWinning.cons node_19073 (AllWinning.cons node_18157 (AllWinning.cons node_17273 (AllWinning.cons node_16295 (AllWinning.cons node_15297 (AllWinning.cons node_14365 (AllWinning.cons node_13399 (AllWinning.cons node_12459 (AllWinning.cons node_11472 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_20604 : Outcome ⟨7, 11, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 16, 2⟩, ⟨5, 11, 16, 4⟩, ⟨4, 11, 16, 6⟩, ⟨3, 11, 16, 8⟩, ⟨2, 11, 16, 10⟩, ⟨1, 11, 16, 12⟩, ⟨0, 11, 16, 14⟩, ⟨7, 10, 16, 2⟩, ⟨7, 9, 16, 4⟩, ⟨7, 8, 16, 6⟩, ⟨7, 7, 16, 8⟩, ⟨7, 6, 16, 10⟩, ⟨7, 5, 16, 12⟩, ⟨7, 4, 16, 14⟩, ⟨7, 3, 16, 16⟩, ⟨7, 2, 16, 18⟩, ⟨7, 1, 16, 20⟩, ⟨7, 0, 16, 22⟩, ⟨7, 11, 15, 2⟩, ⟨7, 11, 14, 4⟩, ⟨7, 11, 13, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 11, 10, 12⟩, ⟨7, 11, 9, 14⟩, ⟨7, 11, 8, 16⟩, ⟨7, 11, 7, 18⟩, ⟨7, 11, 6, 20⟩, ⟨7, 11, 5, 22⟩, ⟨7, 11, 4, 24⟩]
  exact AllWinning.cons node_19861 (AllWinning.cons node_18977 (AllWinning.cons node_18026 (AllWinning.cons node_17099 (AllWinning.cons node_15997 (AllWinning.cons node_14977 (AllWinning.cons node_13963 (AllWinning.cons node_19894 (AllWinning.cons node_19067 (AllWinning.cons node_18146 (AllWinning.cons node_17260 (AllWinning.cons node_16276 (AllWinning.cons node_15279 (AllWinning.cons node_14340 (AllWinning.cons node_13372 (AllWinning.cons node_12429 (AllWinning.cons node_11437 (AllWinning.cons node_10419 (AllWinning.cons node_19897 (AllWinning.cons node_19073 (AllWinning.cons node_18157 (AllWinning.cons node_17273 (AllWinning.cons node_16295 (AllWinning.cons node_15297 (AllWinning.cons node_14365 (AllWinning.cons node_13399 (AllWinning.cons node_12459 (AllWinning.cons node_11472 (AllWinning.cons node_10469 (AllWinning.cons node_9451 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_20605 : Outcome ⟨7, 11, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 16, 2⟩, ⟨5, 11, 16, 4⟩, ⟨4, 11, 16, 6⟩, ⟨3, 11, 16, 8⟩, ⟨2, 11, 16, 10⟩, ⟨1, 11, 16, 12⟩, ⟨0, 11, 16, 14⟩, ⟨7, 10, 16, 2⟩, ⟨7, 9, 16, 4⟩, ⟨7, 8, 16, 6⟩, ⟨7, 7, 16, 8⟩, ⟨7, 6, 16, 10⟩, ⟨7, 5, 16, 12⟩, ⟨7, 4, 16, 14⟩, ⟨7, 3, 16, 16⟩, ⟨7, 2, 16, 18⟩, ⟨7, 1, 16, 20⟩, ⟨7, 0, 16, 22⟩, ⟨7, 11, 15, 2⟩, ⟨7, 11, 14, 4⟩, ⟨7, 11, 13, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 11, 10, 12⟩, ⟨7, 11, 9, 14⟩, ⟨7, 11, 8, 16⟩, ⟨7, 11, 7, 18⟩, ⟨7, 11, 6, 20⟩, ⟨7, 11, 5, 22⟩, ⟨7, 11, 4, 24⟩, ⟨7, 11, 3, 26⟩, ⟨7, 11, 2, 28⟩]
  exact AllWinning.cons node_19861 (AllWinning.cons node_18977 (AllWinning.cons node_18026 (AllWinning.cons node_17099 (AllWinning.cons node_15997 (AllWinning.cons node_14977 (AllWinning.cons node_13963 (AllWinning.cons node_19894 (AllWinning.cons node_19067 (AllWinning.cons node_18146 (AllWinning.cons node_17260 (AllWinning.cons node_16276 (AllWinning.cons node_15279 (AllWinning.cons node_14340 (AllWinning.cons node_13372 (AllWinning.cons node_12429 (AllWinning.cons node_11437 (AllWinning.cons node_10419 (AllWinning.cons node_19897 (AllWinning.cons node_19073 (AllWinning.cons node_18157 (AllWinning.cons node_17273 (AllWinning.cons node_16295 (AllWinning.cons node_15297 (AllWinning.cons node_14365 (AllWinning.cons node_13399 (AllWinning.cons node_12459 (AllWinning.cons node_11472 (AllWinning.cons node_10469 (AllWinning.cons node_9451 (AllWinning.cons node_8481 (AllWinning.cons node_7530 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_20606 : Outcome ⟨7, 11, 16, 18⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 30⟩) (by decide) node_6613

theorem node_20607 : Outcome ⟨7, 12, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 15, 2⟩, ⟨5, 12, 15, 4⟩, ⟨7, 11, 15, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 12, 14, 2⟩, ⟨7, 12, 13, 4⟩]
  exact AllWinning.cons node_19862 (AllWinning.cons node_18978 (AllWinning.cons node_19897 (AllWinning.cons node_19071 (AllWinning.cons node_19898 (AllWinning.cons node_19074 (AllWinning.nil))))))

theorem node_20608 : Outcome ⟨7, 12, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 15, 2⟩, ⟨5, 12, 15, 4⟩, ⟨4, 12, 15, 6⟩, ⟨3, 12, 15, 8⟩, ⟨7, 11, 15, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 9, 15, 6⟩, ⟨7, 8, 15, 8⟩, ⟨7, 12, 14, 2⟩, ⟨7, 12, 13, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 12, 11, 8⟩]
  exact AllWinning.cons node_19862 (AllWinning.cons node_18978 (AllWinning.cons node_18028 (AllWinning.cons node_17101 (AllWinning.cons node_19897 (AllWinning.cons node_19071 (AllWinning.cons node_18150 (AllWinning.cons node_17263 (AllWinning.cons node_19898 (AllWinning.cons node_19074 (AllWinning.cons node_18161 (AllWinning.cons node_17276 (AllWinning.nil))))))))))))

theorem node_20609 : Outcome ⟨7, 12, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 15, 2⟩, ⟨5, 12, 15, 4⟩, ⟨4, 12, 15, 6⟩, ⟨3, 12, 15, 8⟩, ⟨2, 12, 15, 10⟩, ⟨1, 12, 15, 12⟩, ⟨7, 11, 15, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 9, 15, 6⟩, ⟨7, 8, 15, 8⟩, ⟨7, 7, 15, 10⟩, ⟨7, 6, 15, 12⟩, ⟨7, 12, 14, 2⟩, ⟨7, 12, 13, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 12, 10, 10⟩, ⟨7, 12, 9, 12⟩]
  exact AllWinning.cons node_19862 (AllWinning.cons node_18978 (AllWinning.cons node_18028 (AllWinning.cons node_17101 (AllWinning.cons node_16000 (AllWinning.cons node_14981 (AllWinning.cons node_19897 (AllWinning.cons node_19071 (AllWinning.cons node_18150 (AllWinning.cons node_17263 (AllWinning.cons node_16278 (AllWinning.cons node_15283 (AllWinning.cons node_19898 (AllWinning.cons node_19074 (AllWinning.cons node_18161 (AllWinning.cons node_17276 (AllWinning.cons node_16297 (AllWinning.cons node_15300 (AllWinning.nil))))))))))))))))))

theorem node_20610 : Outcome ⟨7, 12, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 15, 2⟩, ⟨5, 12, 15, 4⟩, ⟨4, 12, 15, 6⟩, ⟨3, 12, 15, 8⟩, ⟨2, 12, 15, 10⟩, ⟨1, 12, 15, 12⟩, ⟨0, 12, 15, 14⟩, ⟨7, 11, 15, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 9, 15, 6⟩, ⟨7, 8, 15, 8⟩, ⟨7, 7, 15, 10⟩, ⟨7, 6, 15, 12⟩, ⟨7, 5, 15, 14⟩, ⟨7, 4, 15, 16⟩, ⟨7, 12, 14, 2⟩, ⟨7, 12, 13, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 12, 10, 10⟩, ⟨7, 12, 9, 12⟩, ⟨7, 12, 8, 14⟩, ⟨7, 12, 7, 16⟩]
  exact AllWinning.cons node_19862 (AllWinning.cons node_18978 (AllWinning.cons node_18028 (AllWinning.cons node_17101 (AllWinning.cons node_16000 (AllWinning.cons node_14981 (AllWinning.cons node_13966 (AllWinning.cons node_19897 (AllWinning.cons node_19071 (AllWinning.cons node_18150 (AllWinning.cons node_17263 (AllWinning.cons node_16278 (AllWinning.cons node_15283 (AllWinning.cons node_14343 (AllWinning.cons node_13373 (AllWinning.cons node_19898 (AllWinning.cons node_19074 (AllWinning.cons node_18161 (AllWinning.cons node_17276 (AllWinning.cons node_16297 (AllWinning.cons node_15300 (AllWinning.cons node_14368 (AllWinning.cons node_13406 (AllWinning.nil)))))))))))))))))))))))

theorem node_20611 : Outcome ⟨7, 12, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 15, 2⟩, ⟨5, 12, 15, 4⟩, ⟨4, 12, 15, 6⟩, ⟨3, 12, 15, 8⟩, ⟨2, 12, 15, 10⟩, ⟨1, 12, 15, 12⟩, ⟨0, 12, 15, 14⟩, ⟨7, 11, 15, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 9, 15, 6⟩, ⟨7, 8, 15, 8⟩, ⟨7, 7, 15, 10⟩, ⟨7, 6, 15, 12⟩, ⟨7, 5, 15, 14⟩, ⟨7, 4, 15, 16⟩, ⟨7, 3, 15, 18⟩, ⟨7, 2, 15, 20⟩, ⟨7, 12, 14, 2⟩, ⟨7, 12, 13, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 12, 10, 10⟩, ⟨7, 12, 9, 12⟩, ⟨7, 12, 8, 14⟩, ⟨7, 12, 7, 16⟩, ⟨7, 12, 6, 18⟩, ⟨7, 12, 5, 20⟩]
  exact AllWinning.cons node_19862 (AllWinning.cons node_18978 (AllWinning.cons node_18028 (AllWinning.cons node_17101 (AllWinning.cons node_16000 (AllWinning.cons node_14981 (AllWinning.cons node_13966 (AllWinning.cons node_19897 (AllWinning.cons node_19071 (AllWinning.cons node_18150 (AllWinning.cons node_17263 (AllWinning.cons node_16278 (AllWinning.cons node_15283 (AllWinning.cons node_14343 (AllWinning.cons node_13373 (AllWinning.cons node_12436 (AllWinning.cons node_11441 (AllWinning.cons node_19898 (AllWinning.cons node_19074 (AllWinning.cons node_18161 (AllWinning.cons node_17276 (AllWinning.cons node_16297 (AllWinning.cons node_15300 (AllWinning.cons node_14368 (AllWinning.cons node_13406 (AllWinning.cons node_12463 (AllWinning.cons node_11476 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_20612 : Outcome ⟨7, 12, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 15, 2⟩, ⟨5, 12, 15, 4⟩, ⟨4, 12, 15, 6⟩, ⟨3, 12, 15, 8⟩, ⟨2, 12, 15, 10⟩, ⟨1, 12, 15, 12⟩, ⟨0, 12, 15, 14⟩, ⟨7, 11, 15, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 9, 15, 6⟩, ⟨7, 8, 15, 8⟩, ⟨7, 7, 15, 10⟩, ⟨7, 6, 15, 12⟩, ⟨7, 5, 15, 14⟩, ⟨7, 4, 15, 16⟩, ⟨7, 3, 15, 18⟩, ⟨7, 2, 15, 20⟩, ⟨7, 1, 15, 22⟩, ⟨7, 0, 15, 24⟩, ⟨7, 12, 14, 2⟩, ⟨7, 12, 13, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 12, 10, 10⟩, ⟨7, 12, 9, 12⟩, ⟨7, 12, 8, 14⟩, ⟨7, 12, 7, 16⟩, ⟨7, 12, 6, 18⟩, ⟨7, 12, 5, 20⟩, ⟨7, 12, 4, 22⟩, ⟨7, 12, 3, 24⟩]
  exact AllWinning.cons node_19862 (AllWinning.cons node_18978 (AllWinning.cons node_18028 (AllWinning.cons node_17101 (AllWinning.cons node_16000 (AllWinning.cons node_14981 (AllWinning.cons node_13966 (AllWinning.cons node_19897 (AllWinning.cons node_19071 (AllWinning.cons node_18150 (AllWinning.cons node_17263 (AllWinning.cons node_16278 (AllWinning.cons node_15283 (AllWinning.cons node_14343 (AllWinning.cons node_13373 (AllWinning.cons node_12436 (AllWinning.cons node_11441 (AllWinning.cons node_10424 (AllWinning.cons node_9409 (AllWinning.cons node_19898 (AllWinning.cons node_19074 (AllWinning.cons node_18161 (AllWinning.cons node_17276 (AllWinning.cons node_16297 (AllWinning.cons node_15300 (AllWinning.cons node_14368 (AllWinning.cons node_13406 (AllWinning.cons node_12463 (AllWinning.cons node_11476 (AllWinning.cons node_10474 (AllWinning.cons node_9456 (AllWinning.nil)))))))))))))))))))))))))))))))

theorem node_20613 : Outcome ⟨7, 12, 15, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 15, 2⟩, ⟨5, 12, 15, 4⟩, ⟨4, 12, 15, 6⟩, ⟨3, 12, 15, 8⟩, ⟨2, 12, 15, 10⟩, ⟨1, 12, 15, 12⟩, ⟨0, 12, 15, 14⟩, ⟨7, 11, 15, 2⟩, ⟨7, 10, 15, 4⟩, ⟨7, 9, 15, 6⟩, ⟨7, 8, 15, 8⟩, ⟨7, 7, 15, 10⟩, ⟨7, 6, 15, 12⟩, ⟨7, 5, 15, 14⟩, ⟨7, 4, 15, 16⟩, ⟨7, 3, 15, 18⟩, ⟨7, 2, 15, 20⟩, ⟨7, 1, 15, 22⟩, ⟨7, 0, 15, 24⟩, ⟨7, 12, 14, 2⟩, ⟨7, 12, 13, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 12, 10, 10⟩, ⟨7, 12, 9, 12⟩, ⟨7, 12, 8, 14⟩, ⟨7, 12, 7, 16⟩, ⟨7, 12, 6, 18⟩, ⟨7, 12, 5, 20⟩, ⟨7, 12, 4, 22⟩, ⟨7, 12, 3, 24⟩, ⟨7, 12, 2, 26⟩, ⟨7, 12, 1, 28⟩, ⟨7, 12, 0, 30⟩]
  exact AllWinning.cons node_19862 (AllWinning.cons node_18978 (AllWinning.cons node_18028 (AllWinning.cons node_17101 (AllWinning.cons node_16000 (AllWinning.cons node_14981 (AllWinning.cons node_13966 (AllWinning.cons node_19897 (AllWinning.cons node_19071 (AllWinning.cons node_18150 (AllWinning.cons node_17263 (AllWinning.cons node_16278 (AllWinning.cons node_15283 (AllWinning.cons node_14343 (AllWinning.cons node_13373 (AllWinning.cons node_12436 (AllWinning.cons node_11441 (AllWinning.cons node_10424 (AllWinning.cons node_9409 (AllWinning.cons node_19898 (AllWinning.cons node_19074 (AllWinning.cons node_18161 (AllWinning.cons node_17276 (AllWinning.cons node_16297 (AllWinning.cons node_15300 (AllWinning.cons node_14368 (AllWinning.cons node_13406 (AllWinning.cons node_12463 (AllWinning.cons node_11476 (AllWinning.cons node_10474 (AllWinning.cons node_9456 (AllWinning.cons node_8489 (AllWinning.cons node_7533 (AllWinning.cons node_6620 (AllWinning.nil))))))))))))))))))))))))))))))))))

theorem node_20614 : Outcome ⟨7, 13, 14, 8⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 10⟩) (by decide) node_16302

theorem node_20615 : Outcome ⟨7, 13, 14, 16⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 10⟩) (by decide) node_16302

theorem node_20616 : Outcome ⟨7, 14, 13, 8⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 10⟩) (by decide) node_16286

theorem node_20617 : Outcome ⟨7, 14, 13, 16⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 10⟩) (by decide) node_16286

theorem node_20618 : Outcome ⟨7, 15, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 12, 2⟩, ⟨5, 15, 12, 4⟩, ⟨7, 14, 12, 2⟩, ⟨7, 13, 12, 4⟩, ⟨7, 15, 11, 2⟩, ⟨7, 15, 10, 4⟩]
  exact AllWinning.cons node_19878 (AllWinning.cons node_18982 (AllWinning.cons node_19902 (AllWinning.cons node_19076 (AllWinning.cons node_19903 (AllWinning.cons node_19080 (AllWinning.nil))))))

theorem node_20619 : Outcome ⟨7, 15, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 12, 2⟩, ⟨5, 15, 12, 4⟩, ⟨4, 15, 12, 6⟩, ⟨3, 15, 12, 8⟩, ⟨7, 14, 12, 2⟩, ⟨7, 13, 12, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 15, 11, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 15, 9, 6⟩, ⟨7, 15, 8, 8⟩]
  exact AllWinning.cons node_19878 (AllWinning.cons node_18982 (AllWinning.cons node_18039 (AllWinning.cons node_17113 (AllWinning.cons node_19902 (AllWinning.cons node_19076 (AllWinning.cons node_18161 (AllWinning.cons node_17273 (AllWinning.cons node_19903 (AllWinning.cons node_19080 (AllWinning.cons node_18171 (AllWinning.cons node_17286 (AllWinning.nil))))))))))))

theorem node_20620 : Outcome ⟨7, 15, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 12, 2⟩, ⟨5, 15, 12, 4⟩, ⟨4, 15, 12, 6⟩, ⟨3, 15, 12, 8⟩, ⟨2, 15, 12, 10⟩, ⟨1, 15, 12, 12⟩, ⟨7, 14, 12, 2⟩, ⟨7, 13, 12, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 10, 12, 10⟩, ⟨7, 9, 12, 12⟩, ⟨7, 15, 11, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 15, 9, 6⟩, ⟨7, 15, 8, 8⟩, ⟨7, 15, 7, 10⟩, ⟨7, 15, 6, 12⟩]
  exact AllWinning.cons node_19878 (AllWinning.cons node_18982 (AllWinning.cons node_18039 (AllWinning.cons node_17113 (AllWinning.cons node_16006 (AllWinning.cons node_14993 (AllWinning.cons node_19902 (AllWinning.cons node_19076 (AllWinning.cons node_18161 (AllWinning.cons node_17273 (AllWinning.cons node_16293 (AllWinning.cons node_15291 (AllWinning.cons node_19903 (AllWinning.cons node_19080 (AllWinning.cons node_18171 (AllWinning.cons node_17286 (AllWinning.cons node_16312 (AllWinning.cons node_15309 (AllWinning.nil))))))))))))))))))

theorem node_20621 : Outcome ⟨7, 15, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 12, 2⟩, ⟨5, 15, 12, 4⟩, ⟨4, 15, 12, 6⟩, ⟨3, 15, 12, 8⟩, ⟨2, 15, 12, 10⟩, ⟨1, 15, 12, 12⟩, ⟨0, 15, 12, 14⟩, ⟨7, 14, 12, 2⟩, ⟨7, 13, 12, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 10, 12, 10⟩, ⟨7, 9, 12, 12⟩, ⟨7, 8, 12, 14⟩, ⟨7, 7, 12, 16⟩, ⟨7, 15, 11, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 15, 9, 6⟩, ⟨7, 15, 8, 8⟩, ⟨7, 15, 7, 10⟩, ⟨7, 15, 6, 12⟩, ⟨7, 15, 5, 14⟩, ⟨7, 15, 4, 16⟩]
  exact AllWinning.cons node_19878 (AllWinning.cons node_18982 (AllWinning.cons node_18039 (AllWinning.cons node_17113 (AllWinning.cons node_16006 (AllWinning.cons node_14993 (AllWinning.cons node_13975 (AllWinning.cons node_19902 (AllWinning.cons node_19076 (AllWinning.cons node_18161 (AllWinning.cons node_17273 (AllWinning.cons node_16293 (AllWinning.cons node_15291 (AllWinning.cons node_14352 (AllWinning.cons node_13386 (AllWinning.cons node_19903 (AllWinning.cons node_19080 (AllWinning.cons node_18171 (AllWinning.cons node_17286 (AllWinning.cons node_16312 (AllWinning.cons node_15309 (AllWinning.cons node_14378 (AllWinning.cons node_13414 (AllWinning.nil)))))))))))))))))))))))

theorem node_20622 : Outcome ⟨7, 15, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 12, 2⟩, ⟨5, 15, 12, 4⟩, ⟨4, 15, 12, 6⟩, ⟨3, 15, 12, 8⟩, ⟨2, 15, 12, 10⟩, ⟨1, 15, 12, 12⟩, ⟨0, 15, 12, 14⟩, ⟨7, 14, 12, 2⟩, ⟨7, 13, 12, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 10, 12, 10⟩, ⟨7, 9, 12, 12⟩, ⟨7, 8, 12, 14⟩, ⟨7, 7, 12, 16⟩, ⟨7, 6, 12, 18⟩, ⟨7, 5, 12, 20⟩, ⟨7, 15, 11, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 15, 9, 6⟩, ⟨7, 15, 8, 8⟩, ⟨7, 15, 7, 10⟩, ⟨7, 15, 6, 12⟩, ⟨7, 15, 5, 14⟩, ⟨7, 15, 4, 16⟩, ⟨7, 15, 3, 18⟩, ⟨7, 15, 2, 20⟩]
  exact AllWinning.cons node_19878 (AllWinning.cons node_18982 (AllWinning.cons node_18039 (AllWinning.cons node_17113 (AllWinning.cons node_16006 (AllWinning.cons node_14993 (AllWinning.cons node_13975 (AllWinning.cons node_19902 (AllWinning.cons node_19076 (AllWinning.cons node_18161 (AllWinning.cons node_17273 (AllWinning.cons node_16293 (AllWinning.cons node_15291 (AllWinning.cons node_14352 (AllWinning.cons node_13386 (AllWinning.cons node_12445 (AllWinning.cons node_11451 (AllWinning.cons node_19903 (AllWinning.cons node_19080 (AllWinning.cons node_18171 (AllWinning.cons node_17286 (AllWinning.cons node_16312 (AllWinning.cons node_15309 (AllWinning.cons node_14378 (AllWinning.cons node_13414 (AllWinning.cons node_12475 (AllWinning.cons node_11487 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_20623 : Outcome ⟨7, 15, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 12, 2⟩, ⟨5, 15, 12, 4⟩, ⟨4, 15, 12, 6⟩, ⟨3, 15, 12, 8⟩, ⟨2, 15, 12, 10⟩, ⟨1, 15, 12, 12⟩, ⟨0, 15, 12, 14⟩, ⟨7, 14, 12, 2⟩, ⟨7, 13, 12, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 10, 12, 10⟩, ⟨7, 9, 12, 12⟩, ⟨7, 8, 12, 14⟩, ⟨7, 7, 12, 16⟩, ⟨7, 6, 12, 18⟩, ⟨7, 5, 12, 20⟩, ⟨7, 4, 12, 22⟩, ⟨7, 3, 12, 24⟩, ⟨7, 15, 11, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 15, 9, 6⟩, ⟨7, 15, 8, 8⟩, ⟨7, 15, 7, 10⟩, ⟨7, 15, 6, 12⟩, ⟨7, 15, 5, 14⟩, ⟨7, 15, 4, 16⟩, ⟨7, 15, 3, 18⟩, ⟨7, 15, 2, 20⟩, ⟨7, 15, 1, 22⟩, ⟨7, 15, 0, 24⟩]
  exact AllWinning.cons node_19878 (AllWinning.cons node_18982 (AllWinning.cons node_18039 (AllWinning.cons node_17113 (AllWinning.cons node_16006 (AllWinning.cons node_14993 (AllWinning.cons node_13975 (AllWinning.cons node_19902 (AllWinning.cons node_19076 (AllWinning.cons node_18161 (AllWinning.cons node_17273 (AllWinning.cons node_16293 (AllWinning.cons node_15291 (AllWinning.cons node_14352 (AllWinning.cons node_13386 (AllWinning.cons node_12445 (AllWinning.cons node_11451 (AllWinning.cons node_10436 (AllWinning.cons node_9419 (AllWinning.cons node_19903 (AllWinning.cons node_19080 (AllWinning.cons node_18171 (AllWinning.cons node_17286 (AllWinning.cons node_16312 (AllWinning.cons node_15309 (AllWinning.cons node_14378 (AllWinning.cons node_13414 (AllWinning.cons node_12475 (AllWinning.cons node_11487 (AllWinning.cons node_10486 (AllWinning.cons node_9467 (AllWinning.nil)))))))))))))))))))))))))))))))

theorem node_20624 : Outcome ⟨7, 15, 12, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 12, 2⟩, ⟨5, 15, 12, 4⟩, ⟨4, 15, 12, 6⟩, ⟨3, 15, 12, 8⟩, ⟨2, 15, 12, 10⟩, ⟨1, 15, 12, 12⟩, ⟨0, 15, 12, 14⟩, ⟨7, 14, 12, 2⟩, ⟨7, 13, 12, 4⟩, ⟨7, 12, 12, 6⟩, ⟨7, 11, 12, 8⟩, ⟨7, 10, 12, 10⟩, ⟨7, 9, 12, 12⟩, ⟨7, 8, 12, 14⟩, ⟨7, 7, 12, 16⟩, ⟨7, 6, 12, 18⟩, ⟨7, 5, 12, 20⟩, ⟨7, 4, 12, 22⟩, ⟨7, 3, 12, 24⟩, ⟨7, 2, 12, 26⟩, ⟨7, 1, 12, 28⟩, ⟨7, 0, 12, 30⟩, ⟨7, 15, 11, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 15, 9, 6⟩, ⟨7, 15, 8, 8⟩, ⟨7, 15, 7, 10⟩, ⟨7, 15, 6, 12⟩, ⟨7, 15, 5, 14⟩, ⟨7, 15, 4, 16⟩, ⟨7, 15, 3, 18⟩, ⟨7, 15, 2, 20⟩, ⟨7, 15, 1, 22⟩, ⟨7, 15, 0, 24⟩]
  exact AllWinning.cons node_19878 (AllWinning.cons node_18982 (AllWinning.cons node_18039 (AllWinning.cons node_17113 (AllWinning.cons node_16006 (AllWinning.cons node_14993 (AllWinning.cons node_13975 (AllWinning.cons node_19902 (AllWinning.cons node_19076 (AllWinning.cons node_18161 (AllWinning.cons node_17273 (AllWinning.cons node_16293 (AllWinning.cons node_15291 (AllWinning.cons node_14352 (AllWinning.cons node_13386 (AllWinning.cons node_12445 (AllWinning.cons node_11451 (AllWinning.cons node_10436 (AllWinning.cons node_9419 (AllWinning.cons node_8431 (AllWinning.cons node_7490 (AllWinning.cons node_6555 (AllWinning.cons node_19903 (AllWinning.cons node_19080 (AllWinning.cons node_18171 (AllWinning.cons node_17286 (AllWinning.cons node_16312 (AllWinning.cons node_15309 (AllWinning.cons node_14378 (AllWinning.cons node_13414 (AllWinning.cons node_12475 (AllWinning.cons node_11487 (AllWinning.cons node_10486 (AllWinning.cons node_9467 (AllWinning.nil))))))))))))))))))))))))))))))))))

theorem node_20625 : Outcome ⟨7, 16, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 11, 2⟩, ⟨5, 16, 11, 4⟩, ⟨7, 15, 11, 2⟩, ⟨7, 14, 11, 4⟩, ⟨7, 16, 10, 2⟩, ⟨7, 16, 9, 4⟩]
  exact AllWinning.cons node_19880 (AllWinning.cons node_18985 (AllWinning.cons node_19903 (AllWinning.cons node_19078 (AllWinning.cons node_19904 (AllWinning.cons node_19082 (AllWinning.nil))))))

theorem node_20626 : Outcome ⟨7, 16, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 11, 2⟩, ⟨5, 16, 11, 4⟩, ⟨4, 16, 11, 6⟩, ⟨3, 16, 11, 8⟩, ⟨7, 15, 11, 2⟩, ⟨7, 14, 11, 4⟩, ⟨7, 13, 11, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 16, 10, 2⟩, ⟨7, 16, 9, 4⟩, ⟨7, 16, 8, 6⟩, ⟨7, 16, 7, 8⟩]
  exact AllWinning.cons node_19880 (AllWinning.cons node_18985 (AllWinning.cons node_18043 (AllWinning.cons node_17118 (AllWinning.cons node_19903 (AllWinning.cons node_19078 (AllWinning.cons node_18164 (AllWinning.cons node_17276 (AllWinning.cons node_19904 (AllWinning.cons node_19082 (AllWinning.cons node_18174 (AllWinning.cons node_17290 (AllWinning.nil))))))))))))

theorem node_20627 : Outcome ⟨7, 16, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 11, 2⟩, ⟨5, 16, 11, 4⟩, ⟨4, 16, 11, 6⟩, ⟨3, 16, 11, 8⟩, ⟨2, 16, 11, 10⟩, ⟨1, 16, 11, 12⟩, ⟨7, 15, 11, 2⟩, ⟨7, 14, 11, 4⟩, ⟨7, 13, 11, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 10, 11, 12⟩, ⟨7, 16, 10, 2⟩, ⟨7, 16, 9, 4⟩, ⟨7, 16, 8, 6⟩, ⟨7, 16, 7, 8⟩, ⟨7, 16, 6, 10⟩, ⟨7, 16, 5, 12⟩]
  exact AllWinning.cons node_19880 (AllWinning.cons node_18985 (AllWinning.cons node_18043 (AllWinning.cons node_17118 (AllWinning.cons node_16008 (AllWinning.cons node_14996 (AllWinning.cons node_19903 (AllWinning.cons node_19078 (AllWinning.cons node_18164 (AllWinning.cons node_17276 (AllWinning.cons node_16295 (AllWinning.cons node_15294 (AllWinning.cons node_19904 (AllWinning.cons node_19082 (AllWinning.cons node_18174 (AllWinning.cons node_17290 (AllWinning.cons node_16315 (AllWinning.cons node_15311 (AllWinning.nil))))))))))))))))))

theorem node_20628 : Outcome ⟨7, 16, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 11, 2⟩, ⟨5, 16, 11, 4⟩, ⟨4, 16, 11, 6⟩, ⟨3, 16, 11, 8⟩, ⟨2, 16, 11, 10⟩, ⟨1, 16, 11, 12⟩, ⟨0, 16, 11, 14⟩, ⟨7, 15, 11, 2⟩, ⟨7, 14, 11, 4⟩, ⟨7, 13, 11, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 10, 11, 12⟩, ⟨7, 9, 11, 14⟩, ⟨7, 8, 11, 16⟩, ⟨7, 16, 10, 2⟩, ⟨7, 16, 9, 4⟩, ⟨7, 16, 8, 6⟩, ⟨7, 16, 7, 8⟩, ⟨7, 16, 6, 10⟩, ⟨7, 16, 5, 12⟩, ⟨7, 16, 4, 14⟩, ⟨7, 16, 3, 16⟩]
  exact AllWinning.cons node_19880 (AllWinning.cons node_18985 (AllWinning.cons node_18043 (AllWinning.cons node_17118 (AllWinning.cons node_16008 (AllWinning.cons node_14996 (AllWinning.cons node_13980 (AllWinning.cons node_19903 (AllWinning.cons node_19078 (AllWinning.cons node_18164 (AllWinning.cons node_17276 (AllWinning.cons node_16295 (AllWinning.cons node_15294 (AllWinning.cons node_14356 (AllWinning.cons node_13390 (AllWinning.cons node_19904 (AllWinning.cons node_19082 (AllWinning.cons node_18174 (AllWinning.cons node_17290 (AllWinning.cons node_16315 (AllWinning.cons node_15311 (AllWinning.cons node_14380 (AllWinning.cons node_13417 (AllWinning.nil)))))))))))))))))))))))

theorem node_20629 : Outcome ⟨7, 16, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 11, 2⟩, ⟨5, 16, 11, 4⟩, ⟨4, 16, 11, 6⟩, ⟨3, 16, 11, 8⟩, ⟨2, 16, 11, 10⟩, ⟨1, 16, 11, 12⟩, ⟨0, 16, 11, 14⟩, ⟨7, 15, 11, 2⟩, ⟨7, 14, 11, 4⟩, ⟨7, 13, 11, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 10, 11, 12⟩, ⟨7, 9, 11, 14⟩, ⟨7, 8, 11, 16⟩, ⟨7, 7, 11, 18⟩, ⟨7, 6, 11, 20⟩, ⟨7, 16, 10, 2⟩, ⟨7, 16, 9, 4⟩, ⟨7, 16, 8, 6⟩, ⟨7, 16, 7, 8⟩, ⟨7, 16, 6, 10⟩, ⟨7, 16, 5, 12⟩, ⟨7, 16, 4, 14⟩, ⟨7, 16, 3, 16⟩, ⟨7, 16, 2, 18⟩, ⟨7, 16, 1, 20⟩]
  exact AllWinning.cons node_19880 (AllWinning.cons node_18985 (AllWinning.cons node_18043 (AllWinning.cons node_17118 (AllWinning.cons node_16008 (AllWinning.cons node_14996 (AllWinning.cons node_13980 (AllWinning.cons node_19903 (AllWinning.cons node_19078 (AllWinning.cons node_18164 (AllWinning.cons node_17276 (AllWinning.cons node_16295 (AllWinning.cons node_15294 (AllWinning.cons node_14356 (AllWinning.cons node_13390 (AllWinning.cons node_12447 (AllWinning.cons node_11456 (AllWinning.cons node_19904 (AllWinning.cons node_19082 (AllWinning.cons node_18174 (AllWinning.cons node_17290 (AllWinning.cons node_16315 (AllWinning.cons node_15311 (AllWinning.cons node_14380 (AllWinning.cons node_13417 (AllWinning.cons node_12479 (AllWinning.cons node_11490 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_20630 : Outcome ⟨7, 16, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 11, 2⟩, ⟨5, 16, 11, 4⟩, ⟨4, 16, 11, 6⟩, ⟨3, 16, 11, 8⟩, ⟨2, 16, 11, 10⟩, ⟨1, 16, 11, 12⟩, ⟨0, 16, 11, 14⟩, ⟨7, 15, 11, 2⟩, ⟨7, 14, 11, 4⟩, ⟨7, 13, 11, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 10, 11, 12⟩, ⟨7, 9, 11, 14⟩, ⟨7, 8, 11, 16⟩, ⟨7, 7, 11, 18⟩, ⟨7, 6, 11, 20⟩, ⟨7, 5, 11, 22⟩, ⟨7, 4, 11, 24⟩, ⟨7, 16, 10, 2⟩, ⟨7, 16, 9, 4⟩, ⟨7, 16, 8, 6⟩, ⟨7, 16, 7, 8⟩, ⟨7, 16, 6, 10⟩, ⟨7, 16, 5, 12⟩, ⟨7, 16, 4, 14⟩, ⟨7, 16, 3, 16⟩, ⟨7, 16, 2, 18⟩, ⟨7, 16, 1, 20⟩, ⟨7, 16, 0, 22⟩]
  exact AllWinning.cons node_19880 (AllWinning.cons node_18985 (AllWinning.cons node_18043 (AllWinning.cons node_17118 (AllWinning.cons node_16008 (AllWinning.cons node_14996 (AllWinning.cons node_13980 (AllWinning.cons node_19903 (AllWinning.cons node_19078 (AllWinning.cons node_18164 (AllWinning.cons node_17276 (AllWinning.cons node_16295 (AllWinning.cons node_15294 (AllWinning.cons node_14356 (AllWinning.cons node_13390 (AllWinning.cons node_12447 (AllWinning.cons node_11456 (AllWinning.cons node_10441 (AllWinning.cons node_9424 (AllWinning.cons node_19904 (AllWinning.cons node_19082 (AllWinning.cons node_18174 (AllWinning.cons node_17290 (AllWinning.cons node_16315 (AllWinning.cons node_15311 (AllWinning.cons node_14380 (AllWinning.cons node_13417 (AllWinning.cons node_12479 (AllWinning.cons node_11490 (AllWinning.cons node_10490 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_20631 : Outcome ⟨7, 16, 11, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 11, 2⟩, ⟨5, 16, 11, 4⟩, ⟨4, 16, 11, 6⟩, ⟨3, 16, 11, 8⟩, ⟨2, 16, 11, 10⟩, ⟨1, 16, 11, 12⟩, ⟨0, 16, 11, 14⟩, ⟨7, 15, 11, 2⟩, ⟨7, 14, 11, 4⟩, ⟨7, 13, 11, 6⟩, ⟨7, 12, 11, 8⟩, ⟨7, 11, 11, 10⟩, ⟨7, 10, 11, 12⟩, ⟨7, 9, 11, 14⟩, ⟨7, 8, 11, 16⟩, ⟨7, 7, 11, 18⟩, ⟨7, 6, 11, 20⟩, ⟨7, 5, 11, 22⟩, ⟨7, 4, 11, 24⟩, ⟨7, 3, 11, 26⟩, ⟨7, 2, 11, 28⟩, ⟨7, 16, 10, 2⟩, ⟨7, 16, 9, 4⟩, ⟨7, 16, 8, 6⟩, ⟨7, 16, 7, 8⟩, ⟨7, 16, 6, 10⟩, ⟨7, 16, 5, 12⟩, ⟨7, 16, 4, 14⟩, ⟨7, 16, 3, 16⟩, ⟨7, 16, 2, 18⟩, ⟨7, 16, 1, 20⟩, ⟨7, 16, 0, 22⟩]
  exact AllWinning.cons node_19880 (AllWinning.cons node_18985 (AllWinning.cons node_18043 (AllWinning.cons node_17118 (AllWinning.cons node_16008 (AllWinning.cons node_14996 (AllWinning.cons node_13980 (AllWinning.cons node_19903 (AllWinning.cons node_19078 (AllWinning.cons node_18164 (AllWinning.cons node_17276 (AllWinning.cons node_16295 (AllWinning.cons node_15294 (AllWinning.cons node_14356 (AllWinning.cons node_13390 (AllWinning.cons node_12447 (AllWinning.cons node_11456 (AllWinning.cons node_10441 (AllWinning.cons node_9424 (AllWinning.cons node_8435 (AllWinning.cons node_7496 (AllWinning.cons node_19904 (AllWinning.cons node_19082 (AllWinning.cons node_18174 (AllWinning.cons node_17290 (AllWinning.cons node_16315 (AllWinning.cons node_15311 (AllWinning.cons node_14380 (AllWinning.cons node_13417 (AllWinning.cons node_12479 (AllWinning.cons node_11490 (AllWinning.cons node_10490 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_20632 : Outcome ⟨7, 16, 11, 18⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 30⟩) (by decide) node_6568

theorem node_20633 : Outcome ⟨7, 17, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 17, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨7, 16, 10, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 17, 9, 2⟩, ⟨7, 17, 8, 4⟩]
  exact AllWinning.cons node_19881 (AllWinning.cons node_18987 (AllWinning.cons node_19904 (AllWinning.cons node_19080 (AllWinning.cons node_19907 (AllWinning.cons node_19086 (AllWinning.nil))))))

theorem node_20634 : Outcome ⟨7, 17, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 17, 10, 2⟩, ⟨5, 17, 10, 4⟩, ⟨4, 17, 10, 6⟩, ⟨3, 17, 10, 8⟩, ⟨7, 16, 10, 2⟩, ⟨7, 15, 10, 4⟩, ⟨7, 14, 10, 6⟩, ⟨7, 13, 10, 8⟩, ⟨7, 17, 9, 2⟩, ⟨7, 17, 8, 4⟩, ⟨7, 17, 7, 6⟩, ⟨7, 17, 6, 8⟩]
  exact AllWinning.cons node_19881 (AllWinning.cons node_18987 (AllWinning.cons node_18044 (AllWinning.cons node_17120 (AllWinning.cons node_19904 (AllWinning.cons node_19080 (AllWinning.cons node_18168 (AllWinning.cons node_17280 (AllWinning.cons node_19907 (AllWinning.cons node_19086 (AllWinning.cons node_18178 (AllWinning.cons node_17292 (AllWinning.nil))))))))))))

theorem node_20635 : Outcome ⟨7, 17, 10, 6⟩ true :=
  Outcome.win (q := ⟨7, 17, 5, 10⟩) (by decide) node_16319

theorem node_20636 : Outcome ⟨7, 18, 9, 4⟩ true :=
  Outcome.win (q := ⟨7, 18, 7, 4⟩) (by decide) node_19090

theorem node_20637 : Outcome ⟨7, 18, 9, 8⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 14⟩) (by decide) node_14389

theorem node_20638 : Outcome ⟨7, 19, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 19, 6, 4⟩) (by decide) node_19092

theorem node_20639 : Outcome ⟨7, 19, 8, 12⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 10⟩) (by decide) node_16017

theorem node_20640 : Outcome ⟨7, 20, 7, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 7, 4⟩) (by decide) node_19090

theorem node_20641 : Outcome ⟨7, 20, 7, 18⟩ true :=
  Outcome.win (q := ⟨7, 18, 7, 4⟩) (by decide) node_19090

theorem node_20642 : Outcome ⟨8, 6, 20, 2⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 4⟩) (by decide) node_18997

theorem node_20643 : Outcome ⟨8, 6, 20, 14⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 26⟩) (by decide) node_8540

theorem node_20644 : Outcome ⟨8, 7, 19, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 19, 4⟩) (by decide) node_19004

theorem node_20645 : Outcome ⟨8, 7, 19, 12⟩ true :=
  Outcome.win (q := ⟨8, 2, 19, 10⟩) (by decide) node_16333

theorem node_20646 : Outcome ⟨8, 8, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨8, 7, 18, 2⟩, ⟨8, 6, 18, 4⟩, ⟨8, 8, 17, 2⟩, ⟨8, 8, 16, 4⟩]
  exact AllWinning.cons node_19890 (AllWinning.cons node_19007 (AllWinning.cons node_19917 (AllWinning.cons node_19104 (AllWinning.cons node_19920 (AllWinning.cons node_19109 (AllWinning.nil))))))

theorem node_20647 : Outcome ⟨8, 8, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨5, 8, 18, 6⟩, ⟨4, 8, 18, 8⟩, ⟨8, 7, 18, 2⟩, ⟨8, 6, 18, 4⟩, ⟨8, 5, 18, 6⟩, ⟨8, 4, 18, 8⟩, ⟨8, 8, 17, 2⟩, ⟨8, 8, 16, 4⟩, ⟨8, 8, 15, 6⟩, ⟨8, 8, 14, 8⟩]
  exact AllWinning.cons node_19890 (AllWinning.cons node_19007 (AllWinning.cons node_18060 (AllWinning.cons node_17133 (AllWinning.cons node_19917 (AllWinning.cons node_19104 (AllWinning.cons node_18194 (AllWinning.cons node_17308 (AllWinning.cons node_19920 (AllWinning.cons node_19109 (AllWinning.cons node_18203 (AllWinning.cons node_17319 (AllWinning.nil))))))))))))

theorem node_20648 : Outcome ⟨8, 8, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨5, 8, 18, 6⟩, ⟨4, 8, 18, 8⟩, ⟨3, 8, 18, 10⟩, ⟨2, 8, 18, 12⟩, ⟨1, 8, 18, 14⟩, ⟨0, 8, 18, 16⟩, ⟨8, 7, 18, 2⟩, ⟨8, 6, 18, 4⟩, ⟨8, 5, 18, 6⟩, ⟨8, 4, 18, 8⟩, ⟨8, 3, 18, 10⟩, ⟨8, 2, 18, 12⟩, ⟨8, 1, 18, 14⟩, ⟨8, 0, 18, 16⟩, ⟨8, 8, 17, 2⟩, ⟨8, 8, 16, 4⟩, ⟨8, 8, 15, 6⟩, ⟨8, 8, 14, 8⟩, ⟨8, 8, 13, 10⟩, ⟨8, 8, 12, 12⟩, ⟨8, 8, 11, 14⟩, ⟨8, 8, 10, 16⟩]
  exact AllWinning.cons node_19890 (AllWinning.cons node_19007 (AllWinning.cons node_18060 (AllWinning.cons node_17133 (AllWinning.cons node_16028 (AllWinning.cons node_15013 (AllWinning.cons node_14004 (AllWinning.cons node_12986 (AllWinning.cons node_19917 (AllWinning.cons node_19104 (AllWinning.cons node_18194 (AllWinning.cons node_17308 (AllWinning.cons node_16338 (AllWinning.cons node_15326 (AllWinning.cons node_14404 (AllWinning.cons node_13428 (AllWinning.cons node_19920 (AllWinning.cons node_19109 (AllWinning.cons node_18203 (AllWinning.cons node_17319 (AllWinning.cons node_16357 (AllWinning.cons node_15350 (AllWinning.cons node_14427 (AllWinning.cons node_13455 (AllWinning.nil))))))))))))))))))))))))

theorem node_20649 : Outcome ⟨8, 8, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨5, 8, 18, 6⟩, ⟨4, 8, 18, 8⟩, ⟨3, 8, 18, 10⟩, ⟨2, 8, 18, 12⟩, ⟨1, 8, 18, 14⟩, ⟨0, 8, 18, 16⟩, ⟨8, 7, 18, 2⟩, ⟨8, 6, 18, 4⟩, ⟨8, 5, 18, 6⟩, ⟨8, 4, 18, 8⟩, ⟨8, 3, 18, 10⟩, ⟨8, 2, 18, 12⟩, ⟨8, 1, 18, 14⟩, ⟨8, 0, 18, 16⟩, ⟨8, 8, 17, 2⟩, ⟨8, 8, 16, 4⟩, ⟨8, 8, 15, 6⟩, ⟨8, 8, 14, 8⟩, ⟨8, 8, 13, 10⟩, ⟨8, 8, 12, 12⟩, ⟨8, 8, 11, 14⟩, ⟨8, 8, 10, 16⟩, ⟨8, 8, 9, 18⟩, ⟨8, 8, 8, 20⟩]
  exact AllWinning.cons node_19890 (AllWinning.cons node_19007 (AllWinning.cons node_18060 (AllWinning.cons node_17133 (AllWinning.cons node_16028 (AllWinning.cons node_15013 (AllWinning.cons node_14004 (AllWinning.cons node_12986 (AllWinning.cons node_19917 (AllWinning.cons node_19104 (AllWinning.cons node_18194 (AllWinning.cons node_17308 (AllWinning.cons node_16338 (AllWinning.cons node_15326 (AllWinning.cons node_14404 (AllWinning.cons node_13428 (AllWinning.cons node_19920 (AllWinning.cons node_19109 (AllWinning.cons node_18203 (AllWinning.cons node_17319 (AllWinning.cons node_16357 (AllWinning.cons node_15350 (AllWinning.cons node_14427 (AllWinning.cons node_13455 (AllWinning.cons node_12515 (AllWinning.cons node_11526 (AllWinning.nil))))))))))))))))))))))))))

theorem node_20650 : Outcome ⟨8, 8, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨5, 8, 18, 6⟩, ⟨4, 8, 18, 8⟩, ⟨3, 8, 18, 10⟩, ⟨2, 8, 18, 12⟩, ⟨1, 8, 18, 14⟩, ⟨0, 8, 18, 16⟩, ⟨8, 7, 18, 2⟩, ⟨8, 6, 18, 4⟩, ⟨8, 5, 18, 6⟩, ⟨8, 4, 18, 8⟩, ⟨8, 3, 18, 10⟩, ⟨8, 2, 18, 12⟩, ⟨8, 1, 18, 14⟩, ⟨8, 0, 18, 16⟩, ⟨8, 8, 17, 2⟩, ⟨8, 8, 16, 4⟩, ⟨8, 8, 15, 6⟩, ⟨8, 8, 14, 8⟩, ⟨8, 8, 13, 10⟩, ⟨8, 8, 12, 12⟩, ⟨8, 8, 11, 14⟩, ⟨8, 8, 10, 16⟩, ⟨8, 8, 9, 18⟩, ⟨8, 8, 8, 20⟩, ⟨8, 8, 7, 22⟩, ⟨8, 8, 6, 24⟩]
  exact AllWinning.cons node_19890 (AllWinning.cons node_19007 (AllWinning.cons node_18060 (AllWinning.cons node_17133 (AllWinning.cons node_16028 (AllWinning.cons node_15013 (AllWinning.cons node_14004 (AllWinning.cons node_12986 (AllWinning.cons node_19917 (AllWinning.cons node_19104 (AllWinning.cons node_18194 (AllWinning.cons node_17308 (AllWinning.cons node_16338 (AllWinning.cons node_15326 (AllWinning.cons node_14404 (AllWinning.cons node_13428 (AllWinning.cons node_19920 (AllWinning.cons node_19109 (AllWinning.cons node_18203 (AllWinning.cons node_17319 (AllWinning.cons node_16357 (AllWinning.cons node_15350 (AllWinning.cons node_14427 (AllWinning.cons node_13455 (AllWinning.cons node_12515 (AllWinning.cons node_11526 (AllWinning.cons node_10524 (AllWinning.cons node_9495 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_20651 : Outcome ⟨8, 8, 18, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 18, 2⟩, ⟨6, 8, 18, 4⟩, ⟨5, 8, 18, 6⟩, ⟨4, 8, 18, 8⟩, ⟨3, 8, 18, 10⟩, ⟨2, 8, 18, 12⟩, ⟨1, 8, 18, 14⟩, ⟨0, 8, 18, 16⟩, ⟨8, 7, 18, 2⟩, ⟨8, 6, 18, 4⟩, ⟨8, 5, 18, 6⟩, ⟨8, 4, 18, 8⟩, ⟨8, 3, 18, 10⟩, ⟨8, 2, 18, 12⟩, ⟨8, 1, 18, 14⟩, ⟨8, 0, 18, 16⟩, ⟨8, 8, 17, 2⟩, ⟨8, 8, 16, 4⟩, ⟨8, 8, 15, 6⟩, ⟨8, 8, 14, 8⟩, ⟨8, 8, 13, 10⟩, ⟨8, 8, 12, 12⟩, ⟨8, 8, 11, 14⟩, ⟨8, 8, 10, 16⟩, ⟨8, 8, 9, 18⟩, ⟨8, 8, 8, 20⟩, ⟨8, 8, 7, 22⟩, ⟨8, 8, 6, 24⟩, ⟨8, 8, 5, 26⟩, ⟨8, 8, 4, 28⟩, ⟨8, 8, 3, 30⟩, ⟨8, 8, 2, 32⟩]
  exact AllWinning.cons node_19890 (AllWinning.cons node_19007 (AllWinning.cons node_18060 (AllWinning.cons node_17133 (AllWinning.cons node_16028 (AllWinning.cons node_15013 (AllWinning.cons node_14004 (AllWinning.cons node_12986 (AllWinning.cons node_19917 (AllWinning.cons node_19104 (AllWinning.cons node_18194 (AllWinning.cons node_17308 (AllWinning.cons node_16338 (AllWinning.cons node_15326 (AllWinning.cons node_14404 (AllWinning.cons node_13428 (AllWinning.cons node_19920 (AllWinning.cons node_19109 (AllWinning.cons node_18203 (AllWinning.cons node_17319 (AllWinning.cons node_16357 (AllWinning.cons node_15350 (AllWinning.cons node_14427 (AllWinning.cons node_13455 (AllWinning.cons node_12515 (AllWinning.cons node_11526 (AllWinning.cons node_10524 (AllWinning.cons node_9495 (AllWinning.cons node_8557 (AllWinning.cons node_7570 (AllWinning.cons node_6653 (AllWinning.cons node_5812 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_20652 : Outcome ⟨8, 9, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 4⟩) (by decide) node_19009

theorem node_20653 : Outcome ⟨8, 9, 17, 8⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 10⟩) (by decide) node_16344

theorem node_20654 : Outcome ⟨8, 10, 16, 2⟩ true :=
  Outcome.win (q := ⟨8, 10, 15, 2⟩) (by decide) node_19923

theorem node_20655 : Outcome ⟨8, 10, 16, 12⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 14⟩) (by decide) node_14411

theorem node_20656 : Outcome ⟨8, 11, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 4⟩) (by decide) node_19017

theorem node_20657 : Outcome ⟨8, 11, 15, 6⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 12⟩) (by decide) node_15336

theorem node_20658 : Outcome ⟨8, 12, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 14, 2⟩, ⟨6, 12, 14, 4⟩, ⟨8, 11, 14, 2⟩, ⟨8, 10, 14, 4⟩, ⟨8, 12, 13, 2⟩, ⟨8, 12, 12, 4⟩]
  exact AllWinning.cons node_19898 (AllWinning.cons node_19022 (AllWinning.cons node_19926 (AllWinning.cons node_19113 (AllWinning.cons node_19929 (AllWinning.cons node_19120 (AllWinning.nil))))))

theorem node_20659 : Outcome ⟨8, 12, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 14, 2⟩, ⟨6, 12, 14, 4⟩, ⟨5, 12, 14, 6⟩, ⟨4, 12, 14, 8⟩, ⟨8, 11, 14, 2⟩, ⟨8, 10, 14, 4⟩, ⟨8, 9, 14, 6⟩, ⟨8, 8, 14, 8⟩, ⟨8, 12, 13, 2⟩, ⟨8, 12, 12, 4⟩, ⟨8, 12, 11, 6⟩, ⟨8, 12, 10, 8⟩]
  exact AllWinning.cons node_19898 (AllWinning.cons node_19022 (AllWinning.cons node_18073 (AllWinning.cons node_17145 (AllWinning.cons node_19926 (AllWinning.cons node_19113 (AllWinning.cons node_18206 (AllWinning.cons node_17319 (AllWinning.cons node_19929 (AllWinning.cons node_19120 (AllWinning.cons node_18218 (AllWinning.cons node_17330 (AllWinning.nil))))))))))))

theorem node_20660 : Outcome ⟨8, 12, 14, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 12⟩) (by decide) node_15030

theorem node_20661 : Outcome ⟨8, 13, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 13, 2⟩, ⟨6, 13, 13, 4⟩, ⟨8, 12, 13, 2⟩, ⟨8, 11, 13, 4⟩, ⟨8, 13, 12, 2⟩, ⟨8, 13, 11, 4⟩]
  exact AllWinning.cons node_19899 (AllWinning.cons node_19024 (AllWinning.cons node_19929 (AllWinning.cons node_19117 (AllWinning.cons node_19931 (AllWinning.cons node_19123 (AllWinning.nil))))))

theorem node_20662 : Outcome ⟨8, 13, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 13, 2⟩, ⟨6, 13, 13, 4⟩, ⟨5, 13, 13, 6⟩, ⟨4, 13, 13, 8⟩, ⟨8, 12, 13, 2⟩, ⟨8, 11, 13, 4⟩, ⟨8, 10, 13, 6⟩, ⟨8, 9, 13, 8⟩, ⟨8, 13, 12, 2⟩, ⟨8, 13, 11, 4⟩, ⟨8, 13, 10, 6⟩, ⟨8, 13, 9, 8⟩]
  exact AllWinning.cons node_19899 (AllWinning.cons node_19024 (AllWinning.cons node_18077 (AllWinning.cons node_17149 (AllWinning.cons node_19929 (AllWinning.cons node_19117 (AllWinning.cons node_18210 (AllWinning.cons node_17323 (AllWinning.cons node_19931 (AllWinning.cons node_19123 (AllWinning.cons node_18223 (AllWinning.cons node_17333 (AllWinning.nil))))))))))))

theorem node_20663 : Outcome ⟨8, 13, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 13, 2⟩, ⟨6, 13, 13, 4⟩, ⟨5, 13, 13, 6⟩, ⟨4, 13, 13, 8⟩, ⟨3, 13, 13, 10⟩, ⟨2, 13, 13, 12⟩, ⟨8, 12, 13, 2⟩, ⟨8, 11, 13, 4⟩, ⟨8, 10, 13, 6⟩, ⟨8, 9, 13, 8⟩, ⟨8, 8, 13, 10⟩, ⟨8, 7, 13, 12⟩, ⟨8, 13, 12, 2⟩, ⟨8, 13, 11, 4⟩, ⟨8, 13, 10, 6⟩, ⟨8, 13, 9, 8⟩, ⟨8, 13, 8, 10⟩, ⟨8, 13, 7, 12⟩]
  exact AllWinning.cons node_19899 (AllWinning.cons node_19024 (AllWinning.cons node_18077 (AllWinning.cons node_17149 (AllWinning.cons node_16047 (AllWinning.cons node_15037 (AllWinning.cons node_19929 (AllWinning.cons node_19117 (AllWinning.cons node_18210 (AllWinning.cons node_17323 (AllWinning.cons node_16357 (AllWinning.cons node_15345 (AllWinning.cons node_19931 (AllWinning.cons node_19123 (AllWinning.cons node_18223 (AllWinning.cons node_17333 (AllWinning.cons node_16373 (AllWinning.cons node_15363 (AllWinning.nil))))))))))))))))))

theorem node_20664 : Outcome ⟨8, 13, 13, 10⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 16⟩) (by decide) node_13008

theorem node_20665 : Outcome ⟨8, 13, 13, 12⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 16⟩) (by decide) node_13008

theorem node_20666 : Outcome ⟨8, 14, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 14, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨8, 13, 12, 2⟩, ⟨8, 12, 12, 4⟩, ⟨8, 14, 11, 2⟩, ⟨8, 14, 10, 4⟩]
  exact AllWinning.cons node_19902 (AllWinning.cons node_19027 (AllWinning.cons node_19931 (AllWinning.cons node_19120 (AllWinning.cons node_19933 (AllWinning.cons node_19127 (AllWinning.nil))))))

theorem node_20667 : Outcome ⟨8, 14, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 14, 12, 2⟩, ⟨6, 14, 12, 4⟩, ⟨5, 14, 12, 6⟩, ⟨4, 14, 12, 8⟩, ⟨8, 13, 12, 2⟩, ⟨8, 12, 12, 4⟩, ⟨8, 11, 12, 6⟩, ⟨8, 10, 12, 8⟩, ⟨8, 14, 11, 2⟩, ⟨8, 14, 10, 4⟩, ⟨8, 14, 9, 6⟩, ⟨8, 14, 8, 8⟩]
  exact AllWinning.cons node_19902 (AllWinning.cons node_19027 (AllWinning.cons node_18081 (AllWinning.cons node_17153 (AllWinning.cons node_19931 (AllWinning.cons node_19120 (AllWinning.cons node_18213 (AllWinning.cons node_17325 (AllWinning.cons node_19933 (AllWinning.cons node_19127 (AllWinning.cons node_18225 (AllWinning.cons node_17335 (AllWinning.nil))))))))))))

theorem node_20668 : Outcome ⟨8, 14, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 12⟩) (by decide) node_15043

theorem node_20669 : Outcome ⟨8, 15, 11, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 4⟩) (by decide) node_19029

theorem node_20670 : Outcome ⟨8, 15, 11, 6⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 12⟩) (by decide) node_15373

theorem node_20671 : Outcome ⟨8, 16, 10, 2⟩ true :=
  Outcome.win (q := ⟨8, 15, 10, 2⟩) (by decide) node_19936

theorem node_20672 : Outcome ⟨8, 16, 10, 12⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 14⟩) (by decide) node_14447

theorem node_20673 : Outcome ⟨8, 17, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 4⟩) (by decide) node_19037

theorem node_20674 : Outcome ⟨8, 17, 9, 8⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 10⟩) (by decide) node_16386

theorem node_20675 : Outcome ⟨8, 18, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 18, 8, 2⟩, ⟨6, 18, 8, 4⟩, ⟨8, 17, 8, 2⟩, ⟨8, 16, 8, 4⟩, ⟨8, 18, 7, 2⟩, ⟨8, 18, 6, 4⟩]
  exact AllWinning.cons node_19908 (AllWinning.cons node_19042 (AllWinning.cons node_19940 (AllWinning.cons node_19132 (AllWinning.cons node_19942 (AllWinning.cons node_19137 (AllWinning.nil))))))

theorem node_20676 : Outcome ⟨8, 18, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 18, 8, 2⟩, ⟨6, 18, 8, 4⟩, ⟨5, 18, 8, 6⟩, ⟨4, 18, 8, 8⟩, ⟨8, 17, 8, 2⟩, ⟨8, 16, 8, 4⟩, ⟨8, 15, 8, 6⟩, ⟨8, 14, 8, 8⟩, ⟨8, 18, 7, 2⟩, ⟨8, 18, 6, 4⟩, ⟨8, 18, 5, 6⟩, ⟨8, 18, 4, 8⟩]
  exact AllWinning.cons node_19908 (AllWinning.cons node_19042 (AllWinning.cons node_18093 (AllWinning.cons node_17166 (AllWinning.cons node_19940 (AllWinning.cons node_19132 (AllWinning.cons node_18229 (AllWinning.cons node_17335 (AllWinning.cons node_19942 (AllWinning.cons node_19137 (AllWinning.cons node_18237 (AllWinning.cons node_17348 (AllWinning.nil))))))))))))

end RQ9F1
