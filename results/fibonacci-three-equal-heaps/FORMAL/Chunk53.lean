import Chunk52
set_option autoImplicit false
namespace RQ9F1

theorem node_12413 : Outcome ⟨6, 19, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 19, 0, 2⟩, ⟨4, 19, 0, 4⟩, ⟨6, 18, 0, 2⟩, ⟨6, 17, 0, 4⟩]
  exact AllWinning.cons node_11361 (AllWinning.cons node_10244 (AllWinning.cons node_11426 (AllWinning.cons node_10413 (AllWinning.nil))))

theorem node_12414 : Outcome ⟨6, 19, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 19, 0, 2⟩, ⟨4, 19, 0, 4⟩, ⟨3, 19, 0, 6⟩, ⟨2, 19, 0, 8⟩, ⟨6, 18, 0, 2⟩, ⟨6, 17, 0, 4⟩, ⟨6, 16, 0, 6⟩, ⟨6, 15, 0, 8⟩]
  exact AllWinning.cons node_11361 (AllWinning.cons node_10244 (AllWinning.cons node_9193 (AllWinning.cons node_8145 (AllWinning.cons node_11426 (AllWinning.cons node_10413 (AllWinning.cons node_9401 (AllWinning.cons node_8412 (AllWinning.nil))))))))

theorem node_12415 : Outcome ⟨6, 19, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 19, 0, 2⟩, ⟨4, 19, 0, 4⟩, ⟨3, 19, 0, 6⟩, ⟨2, 19, 0, 8⟩, ⟨1, 19, 0, 10⟩, ⟨0, 19, 0, 12⟩, ⟨6, 18, 0, 2⟩, ⟨6, 17, 0, 4⟩, ⟨6, 16, 0, 6⟩, ⟨6, 15, 0, 8⟩, ⟨6, 14, 0, 10⟩, ⟨6, 13, 0, 12⟩]
  exact AllWinning.cons node_11361 (AllWinning.cons node_10244 (AllWinning.cons node_9193 (AllWinning.cons node_8145 (AllWinning.cons node_7111 (AllWinning.cons node_6114 (AllWinning.cons node_11426 (AllWinning.cons node_10413 (AllWinning.cons node_9401 (AllWinning.cons node_8412 (AllWinning.cons node_7480 (AllWinning.cons node_6546 (AllWinning.nil))))))))))))

theorem node_12416 : Outcome ⟨6, 19, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 19, 0, 2⟩, ⟨4, 19, 0, 4⟩, ⟨3, 19, 0, 6⟩, ⟨2, 19, 0, 8⟩, ⟨1, 19, 0, 10⟩, ⟨0, 19, 0, 12⟩, ⟨6, 18, 0, 2⟩, ⟨6, 17, 0, 4⟩, ⟨6, 16, 0, 6⟩, ⟨6, 15, 0, 8⟩, ⟨6, 14, 0, 10⟩, ⟨6, 13, 0, 12⟩, ⟨6, 12, 0, 14⟩, ⟨6, 11, 0, 16⟩]
  exact AllWinning.cons node_11361 (AllWinning.cons node_10244 (AllWinning.cons node_9193 (AllWinning.cons node_8145 (AllWinning.cons node_7111 (AllWinning.cons node_6114 (AllWinning.cons node_11426 (AllWinning.cons node_10413 (AllWinning.cons node_9401 (AllWinning.cons node_8412 (AllWinning.cons node_7480 (AllWinning.cons node_6546 (AllWinning.cons node_5727 (AllWinning.cons node_5029 (AllWinning.nil))))))))))))))

theorem node_12417 : Outcome ⟨6, 19, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 19, 0, 2⟩, ⟨4, 19, 0, 4⟩, ⟨3, 19, 0, 6⟩, ⟨2, 19, 0, 8⟩, ⟨1, 19, 0, 10⟩, ⟨0, 19, 0, 12⟩, ⟨6, 18, 0, 2⟩, ⟨6, 17, 0, 4⟩, ⟨6, 16, 0, 6⟩, ⟨6, 15, 0, 8⟩, ⟨6, 14, 0, 10⟩, ⟨6, 13, 0, 12⟩, ⟨6, 12, 0, 14⟩, ⟨6, 11, 0, 16⟩, ⟨6, 10, 0, 18⟩, ⟨6, 9, 0, 20⟩]
  exact AllWinning.cons node_11361 (AllWinning.cons node_10244 (AllWinning.cons node_9193 (AllWinning.cons node_8145 (AllWinning.cons node_7111 (AllWinning.cons node_6114 (AllWinning.cons node_11426 (AllWinning.cons node_10413 (AllWinning.cons node_9401 (AllWinning.cons node_8412 (AllWinning.cons node_7480 (AllWinning.cons node_6546 (AllWinning.cons node_5727 (AllWinning.cons node_5029 (AllWinning.cons node_4325 (AllWinning.cons node_3725 (AllWinning.nil))))))))))))))))

theorem node_12418 : Outcome ⟨6, 19, 0, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 26⟩) (by decide) node_2237

theorem node_12419 : Outcome ⟨6, 19, 0, 26⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 26⟩) (by decide) node_2237

theorem node_12420 : Outcome ⟨7, 0, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 4⟩) (by decide) node_10247

theorem node_12421 : Outcome ⟨7, 0, 18, 6⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 4⟩) (by decide) node_10247

theorem node_12422 : Outcome ⟨7, 1, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 17, 2⟩, ⟨5, 1, 17, 4⟩, ⟨7, 0, 17, 2⟩, ⟨7, 1, 16, 2⟩, ⟨7, 1, 15, 4⟩]
  exact AllWinning.cons node_11367 (AllWinning.cons node_10254 (AllWinning.cons node_11429 (AllWinning.cons node_11434 (AllWinning.cons node_10421 (AllWinning.nil)))))

theorem node_12423 : Outcome ⟨7, 1, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 1, 17, 2⟩, ⟨5, 1, 17, 4⟩, ⟨4, 1, 17, 6⟩, ⟨3, 1, 17, 8⟩, ⟨7, 0, 17, 2⟩, ⟨7, 1, 16, 2⟩, ⟨7, 1, 15, 4⟩, ⟨7, 1, 14, 6⟩, ⟨7, 1, 13, 8⟩]
  exact AllWinning.cons node_11367 (AllWinning.cons node_10254 (AllWinning.cons node_9201 (AllWinning.cons node_8151 (AllWinning.cons node_11429 (AllWinning.cons node_11434 (AllWinning.cons node_10421 (AllWinning.cons node_9410 (AllWinning.cons node_8421 (AllWinning.nil)))))))))

theorem node_12424 : Outcome ⟨7, 1, 17, 8⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 12⟩) (by decide) node_6561

theorem node_12425 : Outcome ⟨7, 1, 17, 12⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 12⟩) (by decide) node_6561

theorem node_12426 : Outcome ⟨7, 2, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 8⟩) (by decide) node_8427

theorem node_12427 : Outcome ⟨7, 2, 16, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 8⟩) (by decide) node_8427

theorem node_12428 : Outcome ⟨7, 2, 16, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 8⟩) (by decide) node_8427

theorem node_12429 : Outcome ⟨7, 2, 16, 18⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 26⟩) (by decide) node_2261

theorem node_12430 : Outcome ⟨7, 3, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 15, 2⟩, ⟨5, 3, 15, 4⟩, ⟨7, 2, 15, 2⟩, ⟨7, 1, 15, 4⟩, ⟨7, 3, 14, 2⟩, ⟨7, 3, 13, 4⟩]
  exact AllWinning.cons node_11373 (AllWinning.cons node_10261 (AllWinning.cons node_11438 (AllWinning.cons node_10421 (AllWinning.cons node_11442 (AllWinning.cons node_10429 (AllWinning.nil))))))

theorem node_12431 : Outcome ⟨7, 3, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 15, 2⟩, ⟨5, 3, 15, 4⟩, ⟨4, 3, 15, 6⟩, ⟨3, 3, 15, 8⟩, ⟨7, 2, 15, 2⟩, ⟨7, 1, 15, 4⟩, ⟨7, 0, 15, 6⟩, ⟨7, 3, 14, 2⟩, ⟨7, 3, 13, 4⟩, ⟨7, 3, 12, 6⟩, ⟨7, 3, 11, 8⟩]
  exact AllWinning.cons node_11373 (AllWinning.cons node_10261 (AllWinning.cons node_9210 (AllWinning.cons node_8160 (AllWinning.cons node_11438 (AllWinning.cons node_10421 (AllWinning.cons node_9406 (AllWinning.cons node_11442 (AllWinning.cons node_10429 (AllWinning.cons node_9417 (AllWinning.cons node_8434 (AllWinning.nil)))))))))))

theorem node_12432 : Outcome ⟨7, 3, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 15, 2⟩, ⟨5, 3, 15, 4⟩, ⟨4, 3, 15, 6⟩, ⟨3, 3, 15, 8⟩, ⟨2, 3, 15, 10⟩, ⟨1, 3, 15, 12⟩, ⟨7, 2, 15, 2⟩, ⟨7, 1, 15, 4⟩, ⟨7, 0, 15, 6⟩, ⟨7, 3, 14, 2⟩, ⟨7, 3, 13, 4⟩, ⟨7, 3, 12, 6⟩, ⟨7, 3, 11, 8⟩, ⟨7, 3, 10, 10⟩, ⟨7, 3, 9, 12⟩]
  exact AllWinning.cons node_11373 (AllWinning.cons node_10261 (AllWinning.cons node_9210 (AllWinning.cons node_8160 (AllWinning.cons node_7127 (AllWinning.cons node_6125 (AllWinning.cons node_11438 (AllWinning.cons node_10421 (AllWinning.cons node_9406 (AllWinning.cons node_11442 (AllWinning.cons node_10429 (AllWinning.cons node_9417 (AllWinning.cons node_8434 (AllWinning.cons node_7500 (AllWinning.cons node_6576 (AllWinning.nil)))))))))))))))

theorem node_12433 : Outcome ⟨7, 3, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 15, 2⟩, ⟨5, 3, 15, 4⟩, ⟨4, 3, 15, 6⟩, ⟨3, 3, 15, 8⟩, ⟨2, 3, 15, 10⟩, ⟨1, 3, 15, 12⟩, ⟨0, 3, 15, 14⟩, ⟨7, 2, 15, 2⟩, ⟨7, 1, 15, 4⟩, ⟨7, 0, 15, 6⟩, ⟨7, 3, 14, 2⟩, ⟨7, 3, 13, 4⟩, ⟨7, 3, 12, 6⟩, ⟨7, 3, 11, 8⟩, ⟨7, 3, 10, 10⟩, ⟨7, 3, 9, 12⟩, ⟨7, 3, 8, 14⟩, ⟨7, 3, 7, 16⟩]
  exact AllWinning.cons node_11373 (AllWinning.cons node_10261 (AllWinning.cons node_9210 (AllWinning.cons node_8160 (AllWinning.cons node_7127 (AllWinning.cons node_6125 (AllWinning.cons node_5323 (AllWinning.cons node_11438 (AllWinning.cons node_10421 (AllWinning.cons node_9406 (AllWinning.cons node_11442 (AllWinning.cons node_10429 (AllWinning.cons node_9417 (AllWinning.cons node_8434 (AllWinning.cons node_7500 (AllWinning.cons node_6576 (AllWinning.cons node_5743 (AllWinning.cons node_5048 (AllWinning.nil))))))))))))))))))

theorem node_12434 : Outcome ⟨7, 3, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 15, 2⟩, ⟨5, 3, 15, 4⟩, ⟨4, 3, 15, 6⟩, ⟨3, 3, 15, 8⟩, ⟨2, 3, 15, 10⟩, ⟨1, 3, 15, 12⟩, ⟨0, 3, 15, 14⟩, ⟨7, 2, 15, 2⟩, ⟨7, 1, 15, 4⟩, ⟨7, 0, 15, 6⟩, ⟨7, 3, 14, 2⟩, ⟨7, 3, 13, 4⟩, ⟨7, 3, 12, 6⟩, ⟨7, 3, 11, 8⟩, ⟨7, 3, 10, 10⟩, ⟨7, 3, 9, 12⟩, ⟨7, 3, 8, 14⟩, ⟨7, 3, 7, 16⟩, ⟨7, 3, 6, 18⟩, ⟨7, 3, 5, 20⟩]
  exact AllWinning.cons node_11373 (AllWinning.cons node_10261 (AllWinning.cons node_9210 (AllWinning.cons node_8160 (AllWinning.cons node_7127 (AllWinning.cons node_6125 (AllWinning.cons node_5323 (AllWinning.cons node_11438 (AllWinning.cons node_10421 (AllWinning.cons node_9406 (AllWinning.cons node_11442 (AllWinning.cons node_10429 (AllWinning.cons node_9417 (AllWinning.cons node_8434 (AllWinning.cons node_7500 (AllWinning.cons node_6576 (AllWinning.cons node_5743 (AllWinning.cons node_5048 (AllWinning.cons node_4342 (AllWinning.cons node_3741 (AllWinning.nil))))))))))))))))))))

theorem node_12435 : Outcome ⟨7, 3, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 15, 2⟩, ⟨5, 3, 15, 4⟩, ⟨4, 3, 15, 6⟩, ⟨3, 3, 15, 8⟩, ⟨2, 3, 15, 10⟩, ⟨1, 3, 15, 12⟩, ⟨0, 3, 15, 14⟩, ⟨7, 2, 15, 2⟩, ⟨7, 1, 15, 4⟩, ⟨7, 0, 15, 6⟩, ⟨7, 3, 14, 2⟩, ⟨7, 3, 13, 4⟩, ⟨7, 3, 12, 6⟩, ⟨7, 3, 11, 8⟩, ⟨7, 3, 10, 10⟩, ⟨7, 3, 9, 12⟩, ⟨7, 3, 8, 14⟩, ⟨7, 3, 7, 16⟩, ⟨7, 3, 6, 18⟩, ⟨7, 3, 5, 20⟩, ⟨7, 3, 4, 22⟩, ⟨7, 3, 3, 24⟩]
  exact AllWinning.cons node_11373 (AllWinning.cons node_10261 (AllWinning.cons node_9210 (AllWinning.cons node_8160 (AllWinning.cons node_7127 (AllWinning.cons node_6125 (AllWinning.cons node_5323 (AllWinning.cons node_11438 (AllWinning.cons node_10421 (AllWinning.cons node_9406 (AllWinning.cons node_11442 (AllWinning.cons node_10429 (AllWinning.cons node_9417 (AllWinning.cons node_8434 (AllWinning.cons node_7500 (AllWinning.cons node_6576 (AllWinning.cons node_5743 (AllWinning.cons node_5048 (AllWinning.cons node_4342 (AllWinning.cons node_3741 (AllWinning.cons node_3185 (AllWinning.cons node_2707 (AllWinning.nil))))))))))))))))))))))

theorem node_12436 : Outcome ⟨7, 3, 15, 18⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 26⟩) (by decide) node_2277

theorem node_12437 : Outcome ⟨7, 4, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 4, 14, 2⟩, ⟨5, 4, 14, 4⟩, ⟨7, 3, 14, 2⟩, ⟨7, 2, 14, 4⟩, ⟨7, 4, 13, 2⟩, ⟨7, 4, 12, 4⟩]
  exact AllWinning.cons node_11375 (AllWinning.cons node_10263 (AllWinning.cons node_11442 (AllWinning.cons node_10425 (AllWinning.cons node_11445 (AllWinning.cons node_10433 (AllWinning.nil))))))

theorem node_12438 : Outcome ⟨7, 4, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 4, 14, 2⟩, ⟨5, 4, 14, 4⟩, ⟨4, 4, 14, 6⟩, ⟨3, 4, 14, 8⟩, ⟨7, 3, 14, 2⟩, ⟨7, 2, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨7, 0, 14, 8⟩, ⟨7, 4, 13, 2⟩, ⟨7, 4, 12, 4⟩, ⟨7, 4, 11, 6⟩, ⟨7, 4, 10, 8⟩]
  exact AllWinning.cons node_11375 (AllWinning.cons node_10263 (AllWinning.cons node_9212 (AllWinning.cons node_8163 (AllWinning.cons node_11442 (AllWinning.cons node_10425 (AllWinning.cons node_9410 (AllWinning.cons node_8417 (AllWinning.cons node_11445 (AllWinning.cons node_10433 (AllWinning.cons node_9422 (AllWinning.cons node_8438 (AllWinning.nil))))))))))))

theorem node_12439 : Outcome ⟨7, 4, 14, 24⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 18⟩) (by decide) node_4351

theorem node_12440 : Outcome ⟨7, 5, 13, 2⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 4⟩) (by decide) node_10269

theorem node_12441 : Outcome ⟨7, 5, 13, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 4⟩) (by decide) node_10269

theorem node_12442 : Outcome ⟨7, 6, 12, 2⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 2⟩) (by decide) node_11381

theorem node_12443 : Outcome ⟨7, 6, 12, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 8⟩) (by decide) node_8427

theorem node_12444 : Outcome ⟨7, 6, 12, 14⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 8⟩) (by decide) node_8427

theorem node_12445 : Outcome ⟨7, 6, 12, 18⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 8⟩) (by decide) node_8427

theorem node_12446 : Outcome ⟨7, 7, 11, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 11, 2⟩) (by decide) node_11387

theorem node_12447 : Outcome ⟨7, 7, 11, 18⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 22⟩) (by decide) node_3208

theorem node_12448 : Outcome ⟨7, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 10, 4⟩) (by decide) node_10284

theorem node_12449 : Outcome ⟨7, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 8⟩) (by decide) node_8462

theorem node_12450 : Outcome ⟨7, 8, 10, 8⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 8⟩) (by decide) node_8462

theorem node_12451 : Outcome ⟨7, 8, 10, 20⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 8⟩) (by decide) node_8462

theorem node_12452 : Outcome ⟨7, 9, 9, 2⟩ true :=
  Outcome.win (q := ⟨5, 9, 9, 4⟩) (by decide) node_10290

theorem node_12453 : Outcome ⟨7, 9, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 14⟩) (by decide) node_5350

theorem node_12454 : Outcome ⟨7, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 8, 4⟩) (by decide) node_10294

theorem node_12455 : Outcome ⟨7, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 8⟩) (by decide) node_8446

theorem node_12456 : Outcome ⟨7, 10, 8, 8⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 8⟩) (by decide) node_8446

theorem node_12457 : Outcome ⟨7, 10, 8, 20⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 8⟩) (by decide) node_8446

theorem node_12458 : Outcome ⟨7, 11, 7, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 7, 2⟩) (by decide) node_11402

theorem node_12459 : Outcome ⟨7, 11, 7, 18⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 22⟩) (by decide) node_3171

theorem node_12460 : Outcome ⟨7, 12, 6, 2⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 2⟩) (by decide) node_11406

theorem node_12461 : Outcome ⟨7, 12, 6, 8⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 8⟩) (by decide) node_8462

theorem node_12462 : Outcome ⟨7, 12, 6, 14⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 8⟩) (by decide) node_8462

theorem node_12463 : Outcome ⟨7, 12, 6, 18⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 8⟩) (by decide) node_8462

theorem node_12464 : Outcome ⟨7, 13, 5, 2⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 4⟩) (by decide) node_10309

theorem node_12465 : Outcome ⟨7, 13, 5, 8⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 4⟩) (by decide) node_10309

theorem node_12466 : Outcome ⟨7, 14, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 14, 4, 2⟩, ⟨5, 14, 4, 4⟩, ⟨7, 13, 4, 2⟩, ⟨7, 12, 4, 4⟩, ⟨7, 14, 3, 2⟩, ⟨7, 14, 2, 4⟩]
  exact AllWinning.cons node_11414 (AllWinning.cons node_10314 (AllWinning.cons node_11478 (AllWinning.cons node_10471 (AllWinning.cons node_11481 (AllWinning.cons node_10480 (AllWinning.nil))))))

theorem node_12467 : Outcome ⟨7, 14, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 14, 4, 2⟩, ⟨5, 14, 4, 4⟩, ⟨4, 14, 4, 6⟩, ⟨3, 14, 4, 8⟩, ⟨7, 13, 4, 2⟩, ⟨7, 12, 4, 4⟩, ⟨7, 11, 4, 6⟩, ⟨7, 10, 4, 8⟩, ⟨7, 14, 3, 2⟩, ⟨7, 14, 2, 4⟩, ⟨7, 14, 1, 6⟩, ⟨7, 14, 0, 8⟩]
  exact AllWinning.cons node_11414 (AllWinning.cons node_10314 (AllWinning.cons node_9253 (AllWinning.cons node_8202 (AllWinning.cons node_11478 (AllWinning.cons node_10471 (AllWinning.cons node_9449 (AllWinning.cons node_8476 (AllWinning.cons node_11481 (AllWinning.cons node_10480 (AllWinning.cons node_9461 (AllWinning.cons node_8496 (AllWinning.nil))))))))))))

theorem node_12468 : Outcome ⟨7, 14, 4, 24⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 18⟩) (by decide) node_4366

theorem node_12469 : Outcome ⟨7, 15, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 3, 2⟩, ⟨5, 15, 3, 4⟩, ⟨7, 14, 3, 2⟩, ⟨7, 13, 3, 4⟩, ⟨7, 15, 2, 2⟩, ⟨7, 15, 1, 4⟩]
  exact AllWinning.cons node_11418 (AllWinning.cons node_10320 (AllWinning.cons node_11481 (AllWinning.cons node_10476 (AllWinning.cons node_11484 (AllWinning.cons node_10483 (AllWinning.nil))))))

theorem node_12470 : Outcome ⟨7, 15, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 3, 2⟩, ⟨5, 15, 3, 4⟩, ⟨4, 15, 3, 6⟩, ⟨3, 15, 3, 8⟩, ⟨7, 14, 3, 2⟩, ⟨7, 13, 3, 4⟩, ⟨7, 12, 3, 6⟩, ⟨7, 11, 3, 8⟩, ⟨7, 15, 2, 2⟩, ⟨7, 15, 1, 4⟩, ⟨7, 15, 0, 6⟩]
  exact AllWinning.cons node_11418 (AllWinning.cons node_10320 (AllWinning.cons node_9257 (AllWinning.cons node_8206 (AllWinning.cons node_11481 (AllWinning.cons node_10476 (AllWinning.cons node_9454 (AllWinning.cons node_8480 (AllWinning.cons node_11484 (AllWinning.cons node_10483 (AllWinning.cons node_9464 (AllWinning.nil)))))))))))

theorem node_12471 : Outcome ⟨7, 15, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 3, 2⟩, ⟨5, 15, 3, 4⟩, ⟨4, 15, 3, 6⟩, ⟨3, 15, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨1, 15, 3, 12⟩, ⟨7, 14, 3, 2⟩, ⟨7, 13, 3, 4⟩, ⟨7, 12, 3, 6⟩, ⟨7, 11, 3, 8⟩, ⟨7, 10, 3, 10⟩, ⟨7, 9, 3, 12⟩, ⟨7, 15, 2, 2⟩, ⟨7, 15, 1, 4⟩, ⟨7, 15, 0, 6⟩]
  exact AllWinning.cons node_11418 (AllWinning.cons node_10320 (AllWinning.cons node_9257 (AllWinning.cons node_8206 (AllWinning.cons node_7184 (AllWinning.cons node_6186 (AllWinning.cons node_11481 (AllWinning.cons node_10476 (AllWinning.cons node_9454 (AllWinning.cons node_8480 (AllWinning.cons node_7523 (AllWinning.cons node_6597 (AllWinning.cons node_11484 (AllWinning.cons node_10483 (AllWinning.cons node_9464 (AllWinning.nil)))))))))))))))

theorem node_12472 : Outcome ⟨7, 15, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 3, 2⟩, ⟨5, 15, 3, 4⟩, ⟨4, 15, 3, 6⟩, ⟨3, 15, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨1, 15, 3, 12⟩, ⟨0, 15, 3, 14⟩, ⟨7, 14, 3, 2⟩, ⟨7, 13, 3, 4⟩, ⟨7, 12, 3, 6⟩, ⟨7, 11, 3, 8⟩, ⟨7, 10, 3, 10⟩, ⟨7, 9, 3, 12⟩, ⟨7, 8, 3, 14⟩, ⟨7, 7, 3, 16⟩, ⟨7, 15, 2, 2⟩, ⟨7, 15, 1, 4⟩, ⟨7, 15, 0, 6⟩]
  exact AllWinning.cons node_11418 (AllWinning.cons node_10320 (AllWinning.cons node_9257 (AllWinning.cons node_8206 (AllWinning.cons node_7184 (AllWinning.cons node_6186 (AllWinning.cons node_5376 (AllWinning.cons node_11481 (AllWinning.cons node_10476 (AllWinning.cons node_9454 (AllWinning.cons node_8480 (AllWinning.cons node_7523 (AllWinning.cons node_6597 (AllWinning.cons node_5762 (AllWinning.cons node_5062 (AllWinning.cons node_11484 (AllWinning.cons node_10483 (AllWinning.cons node_9464 (AllWinning.nil))))))))))))))))))

theorem node_12473 : Outcome ⟨7, 15, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 3, 2⟩, ⟨5, 15, 3, 4⟩, ⟨4, 15, 3, 6⟩, ⟨3, 15, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨1, 15, 3, 12⟩, ⟨0, 15, 3, 14⟩, ⟨7, 14, 3, 2⟩, ⟨7, 13, 3, 4⟩, ⟨7, 12, 3, 6⟩, ⟨7, 11, 3, 8⟩, ⟨7, 10, 3, 10⟩, ⟨7, 9, 3, 12⟩, ⟨7, 8, 3, 14⟩, ⟨7, 7, 3, 16⟩, ⟨7, 6, 3, 18⟩, ⟨7, 5, 3, 20⟩, ⟨7, 15, 2, 2⟩, ⟨7, 15, 1, 4⟩, ⟨7, 15, 0, 6⟩]
  exact AllWinning.cons node_11418 (AllWinning.cons node_10320 (AllWinning.cons node_9257 (AllWinning.cons node_8206 (AllWinning.cons node_7184 (AllWinning.cons node_6186 (AllWinning.cons node_5376 (AllWinning.cons node_11481 (AllWinning.cons node_10476 (AllWinning.cons node_9454 (AllWinning.cons node_8480 (AllWinning.cons node_7523 (AllWinning.cons node_6597 (AllWinning.cons node_5762 (AllWinning.cons node_5062 (AllWinning.cons node_4378 (AllWinning.cons node_3748 (AllWinning.cons node_11484 (AllWinning.cons node_10483 (AllWinning.cons node_9464 (AllWinning.nil))))))))))))))))))))

theorem node_12474 : Outcome ⟨7, 15, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 3, 2⟩, ⟨5, 15, 3, 4⟩, ⟨4, 15, 3, 6⟩, ⟨3, 15, 3, 8⟩, ⟨2, 15, 3, 10⟩, ⟨1, 15, 3, 12⟩, ⟨0, 15, 3, 14⟩, ⟨7, 14, 3, 2⟩, ⟨7, 13, 3, 4⟩, ⟨7, 12, 3, 6⟩, ⟨7, 11, 3, 8⟩, ⟨7, 10, 3, 10⟩, ⟨7, 9, 3, 12⟩, ⟨7, 8, 3, 14⟩, ⟨7, 7, 3, 16⟩, ⟨7, 6, 3, 18⟩, ⟨7, 5, 3, 20⟩, ⟨7, 4, 3, 22⟩, ⟨7, 3, 3, 24⟩, ⟨7, 15, 2, 2⟩, ⟨7, 15, 1, 4⟩, ⟨7, 15, 0, 6⟩]
  exact AllWinning.cons node_11418 (AllWinning.cons node_10320 (AllWinning.cons node_9257 (AllWinning.cons node_8206 (AllWinning.cons node_7184 (AllWinning.cons node_6186 (AllWinning.cons node_5376 (AllWinning.cons node_11481 (AllWinning.cons node_10476 (AllWinning.cons node_9454 (AllWinning.cons node_8480 (AllWinning.cons node_7523 (AllWinning.cons node_6597 (AllWinning.cons node_5762 (AllWinning.cons node_5062 (AllWinning.cons node_4378 (AllWinning.cons node_3748 (AllWinning.cons node_3188 (AllWinning.cons node_2707 (AllWinning.cons node_11484 (AllWinning.cons node_10483 (AllWinning.cons node_9464 (AllWinning.nil))))))))))))))))))))))

theorem node_12475 : Outcome ⟨7, 15, 3, 18⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 26⟩) (by decide) node_2261

theorem node_12476 : Outcome ⟨7, 16, 2, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 8⟩) (by decide) node_8485

theorem node_12477 : Outcome ⟨7, 16, 2, 6⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 8⟩) (by decide) node_8485

theorem node_12478 : Outcome ⟨7, 16, 2, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 8⟩) (by decide) node_8485

theorem node_12479 : Outcome ⟨7, 16, 2, 18⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 26⟩) (by decide) node_2277

theorem node_12480 : Outcome ⟨7, 17, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 17, 1, 2⟩, ⟨5, 17, 1, 4⟩, ⟨7, 16, 1, 2⟩, ⟨7, 15, 1, 4⟩, ⟨7, 17, 0, 2⟩]
  exact AllWinning.cons node_11423 (AllWinning.cons node_10325 (AllWinning.cons node_11488 (AllWinning.cons node_10483 (AllWinning.cons node_11491 (AllWinning.nil)))))

theorem node_12481 : Outcome ⟨7, 17, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 17, 1, 2⟩, ⟨5, 17, 1, 4⟩, ⟨4, 17, 1, 6⟩, ⟨3, 17, 1, 8⟩, ⟨7, 16, 1, 2⟩, ⟨7, 15, 1, 4⟩, ⟨7, 14, 1, 6⟩, ⟨7, 13, 1, 8⟩, ⟨7, 17, 0, 2⟩]
  exact AllWinning.cons node_11423 (AllWinning.cons node_10325 (AllWinning.cons node_9264 (AllWinning.cons node_8214 (AllWinning.cons node_11488 (AllWinning.cons node_10483 (AllWinning.cons node_9461 (AllWinning.cons node_8491 (AllWinning.cons node_11491 (AllWinning.nil)))))))))

theorem node_12482 : Outcome ⟨7, 17, 1, 8⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 12⟩) (by decide) node_6608

theorem node_12483 : Outcome ⟨7, 17, 1, 12⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 12⟩) (by decide) node_6608

theorem node_12484 : Outcome ⟨7, 18, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 4⟩) (by decide) node_10330

theorem node_12485 : Outcome ⟨7, 18, 0, 6⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 4⟩) (by decide) node_10330

theorem node_12486 : Outcome ⟨8, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 16, 2⟩) (by decide) node_11496

theorem node_12487 : Outcome ⟨8, 0, 17, 8⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 8⟩) (by decide) node_8222

theorem node_12488 : Outcome ⟨8, 0, 17, 18⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 18⟩) (by decide) node_4398

theorem node_12489 : Outcome ⟨8, 1, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 4⟩) (by decide) node_10340

theorem node_12490 : Outcome ⟨8, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 8⟩) (by decide) node_8505

theorem node_12491 : Outcome ⟨8, 1, 16, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 8⟩) (by decide) node_8505

theorem node_12492 : Outcome ⟨8, 1, 16, 14⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 8⟩) (by decide) node_8505

theorem node_12493 : Outcome ⟨8, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 15, 2⟩) (by decide) node_11500

theorem node_12494 : Outcome ⟨8, 2, 15, 6⟩ true :=
  Outcome.win (q := ⟨8, 1, 15, 2⟩) (by decide) node_11500

theorem node_12495 : Outcome ⟨8, 2, 15, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 15, 2⟩) (by decide) node_11500

theorem node_12496 : Outcome ⟨8, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 4⟩) (by decide) node_10351

theorem node_12497 : Outcome ⟨8, 3, 14, 6⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 4⟩) (by decide) node_10351

theorem node_12498 : Outcome ⟨8, 3, 14, 18⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 4⟩) (by decide) node_10351

theorem node_12499 : Outcome ⟨8, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨8, 4, 12, 2⟩) (by decide) node_11508

theorem node_12500 : Outcome ⟨8, 4, 13, 8⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 8⟩) (by decide) node_8236

theorem node_12501 : Outcome ⟨8, 5, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 10, 4⟩) (by decide) node_10508

theorem node_12502 : Outcome ⟨8, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 8⟩) (by decide) node_8505

theorem node_12503 : Outcome ⟨8, 5, 12, 6⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 8⟩) (by decide) node_8505

theorem node_12504 : Outcome ⟨8, 5, 12, 20⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 8⟩) (by decide) node_8505

theorem node_12505 : Outcome ⟨8, 6, 11, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 11, 2⟩) (by decide) node_11453

theorem node_12506 : Outcome ⟨8, 6, 11, 6⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12507 : Outcome ⟨8, 6, 11, 8⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12508 : Outcome ⟨8, 6, 11, 14⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 12⟩) (by decide) node_6222

theorem node_12509 : Outcome ⟨8, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 10, 4⟩) (by decide) node_10508

theorem node_12510 : Outcome ⟨8, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 8⟩) (by decide) node_8544

theorem node_12511 : Outcome ⟨8, 7, 10, 8⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 8⟩) (by decide) node_8544

theorem node_12512 : Outcome ⟨8, 7, 10, 20⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 8⟩) (by decide) node_8544

theorem node_12513 : Outcome ⟨8, 8, 9, 2⟩ true :=
  Outcome.win (q := ⟨7, 8, 9, 2⟩) (by decide) node_11459

theorem node_12514 : Outcome ⟨8, 8, 9, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 9, 2⟩) (by decide) node_11459

theorem node_12515 : Outcome ⟨8, 8, 9, 18⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 18⟩) (by decide) node_4439

theorem node_12516 : Outcome ⟨8, 9, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 9, 8, 2⟩) (by decide) node_11463

theorem node_12517 : Outcome ⟨8, 9, 8, 6⟩ true :=
  Outcome.win (q := ⟨7, 9, 8, 2⟩) (by decide) node_11463

theorem node_12518 : Outcome ⟨8, 9, 8, 18⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 18⟩) (by decide) node_4398

theorem node_12519 : Outcome ⟨8, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨8, 10, 5, 4⟩) (by decide) node_10530

theorem node_12520 : Outcome ⟨8, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 8⟩) (by decide) node_8532

theorem node_12521 : Outcome ⟨8, 10, 7, 8⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 8⟩) (by decide) node_8532

theorem node_12522 : Outcome ⟨8, 10, 7, 20⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 8⟩) (by decide) node_8532

theorem node_12523 : Outcome ⟨8, 11, 6, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 6, 2⟩) (by decide) node_11469

theorem node_12524 : Outcome ⟨8, 11, 6, 6⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12525 : Outcome ⟨8, 11, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12526 : Outcome ⟨8, 11, 6, 14⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 12⟩) (by decide) node_6246

theorem node_12527 : Outcome ⟨8, 12, 5, 2⟩ true :=
  Outcome.win (q := ⟨8, 10, 5, 4⟩) (by decide) node_10530

theorem node_12528 : Outcome ⟨8, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 8⟩) (by decide) node_8572

theorem node_12529 : Outcome ⟨8, 12, 5, 6⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 8⟩) (by decide) node_8572

theorem node_12530 : Outcome ⟨8, 12, 5, 20⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 8⟩) (by decide) node_8572

theorem node_12531 : Outcome ⟨8, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 4, 2⟩) (by decide) node_11538

theorem node_12532 : Outcome ⟨8, 13, 4, 8⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 8⟩) (by decide) node_8270

theorem node_12533 : Outcome ⟨8, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 4⟩) (by decide) node_10397

theorem node_12534 : Outcome ⟨8, 14, 3, 6⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 4⟩) (by decide) node_10397

theorem node_12535 : Outcome ⟨8, 14, 3, 18⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 4⟩) (by decide) node_10397

theorem node_12536 : Outcome ⟨8, 15, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 2, 2⟩) (by decide) node_11543

theorem node_12537 : Outcome ⟨8, 15, 2, 6⟩ true :=
  Outcome.win (q := ⟨8, 14, 2, 2⟩) (by decide) node_11543

theorem node_12538 : Outcome ⟨8, 15, 2, 8⟩ true :=
  Outcome.win (q := ⟨8, 14, 2, 2⟩) (by decide) node_11543

theorem node_12539 : Outcome ⟨8, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 8⟩) (by decide) node_8572

theorem node_12540 : Outcome ⟨8, 16, 1, 8⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 8⟩) (by decide) node_8572

theorem node_12541 : Outcome ⟨8, 16, 1, 14⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 8⟩) (by decide) node_8572

theorem node_12542 : Outcome ⟨8, 17, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 16, 0, 2⟩) (by decide) node_11549

theorem node_12543 : Outcome ⟨8, 17, 0, 8⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 8⟩) (by decide) node_8284

theorem node_12544 : Outcome ⟨8, 17, 0, 18⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 18⟩) (by decide) node_4439

theorem node_12545 : Outcome ⟨9, 0, 16, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 14, 4⟩) (by decide) node_10553

theorem node_12546 : Outcome ⟨9, 0, 16, 4⟩ true :=
  Outcome.win (q := ⟨9, 0, 14, 4⟩) (by decide) node_10553

theorem node_12547 : Outcome ⟨9, 0, 16, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 14⟩) (by decide) node_5826

theorem node_12548 : Outcome ⟨9, 0, 16, 14⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 14⟩) (by decide) node_5826

theorem node_12549 : Outcome ⟨9, 1, 15, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 13, 4⟩) (by decide) node_10557

theorem node_12550 : Outcome ⟨9, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 13, 4⟩) (by decide) node_10557

theorem node_12551 : Outcome ⟨9, 1, 15, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 10⟩) (by decide) node_7274

theorem node_12552 : Outcome ⟨9, 1, 15, 14⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 20⟩) (by decide) node_3804

theorem node_12553 : Outcome ⟨9, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 14, 4⟩) (by decide) node_10553

theorem node_12554 : Outcome ⟨9, 2, 14, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 10⟩) (by decide) node_7281

theorem node_12555 : Outcome ⟨9, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 13, 4⟩) (by decide) node_10557

theorem node_12556 : Outcome ⟨9, 3, 13, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 12⟩) (by decide) node_6293

theorem node_12557 : Outcome ⟨9, 4, 12, 8⟩ true :=
  Outcome.win (q := ⟨8, 4, 12, 2⟩) (by decide) node_11508

theorem node_12558 : Outcome ⟨9, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨9, 5, 9, 4⟩) (by decide) node_10570

theorem node_12559 : Outcome ⟨9, 5, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 12⟩) (by decide) node_6304

theorem node_12560 : Outcome ⟨9, 5, 11, 12⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 20⟩) (by decide) node_3832

theorem node_12561 : Outcome ⟨9, 6, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 6, 10, 2⟩, ⟨7, 6, 10, 4⟩, ⟨9, 5, 10, 2⟩, ⟨9, 4, 10, 4⟩, ⟨9, 6, 9, 2⟩, ⟨9, 6, 8, 4⟩]
  exact AllWinning.cons node_11515 (AllWinning.cons node_10443 (AllWinning.cons node_11573 (AllWinning.cons node_10567 (AllWinning.cons node_11577 (AllWinning.cons node_10573 (AllWinning.nil))))))

theorem node_12562 : Outcome ⟨9, 6, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 6, 10, 2⟩, ⟨7, 6, 10, 4⟩, ⟨6, 6, 10, 6⟩, ⟨5, 6, 10, 8⟩, ⟨9, 5, 10, 2⟩, ⟨9, 4, 10, 4⟩, ⟨9, 3, 10, 6⟩, ⟨9, 2, 10, 8⟩, ⟨9, 6, 9, 2⟩, ⟨9, 6, 8, 4⟩, ⟨9, 6, 7, 6⟩, ⟨9, 6, 6, 8⟩]
  exact AllWinning.cons node_11515 (AllWinning.cons node_10443 (AllWinning.cons node_9360 (AllWinning.cons node_8308 (AllWinning.cons node_11573 (AllWinning.cons node_10567 (AllWinning.cons node_9525 (AllWinning.cons node_8590 (AllWinning.cons node_11577 (AllWinning.cons node_10573 (AllWinning.cons node_9534 (AllWinning.cons node_8604 (AllWinning.nil))))))))))))

theorem node_12563 : Outcome ⟨9, 6, 10, 14⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 10⟩) (by decide) node_7297

theorem node_12564 : Outcome ⟨9, 6, 10, 18⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 10⟩) (by decide) node_7297

theorem node_12565 : Outcome ⟨9, 7, 9, 2⟩ true :=
  Outcome.win (q := ⟨9, 5, 9, 4⟩) (by decide) node_10570

theorem node_12566 : Outcome ⟨9, 7, 9, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 14⟩) (by decide) node_5826

theorem node_12567 : Outcome ⟨9, 8, 8, 2⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 2⟩) (by decide) node_11522

theorem node_12568 : Outcome ⟨9, 8, 8, 6⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 2⟩) (by decide) node_11522

theorem node_12569 : Outcome ⟨9, 8, 8, 18⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 18⟩) (by decide) node_3966

theorem node_12570 : Outcome ⟨9, 9, 7, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 5, 4⟩) (by decide) node_10583

theorem node_12571 : Outcome ⟨9, 9, 7, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 14⟩) (by decide) node_5876

theorem node_12572 : Outcome ⟨9, 10, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 10, 6, 2⟩, ⟨7, 10, 6, 4⟩, ⟨9, 9, 6, 2⟩, ⟨9, 8, 6, 4⟩, ⟨9, 10, 5, 2⟩, ⟨9, 10, 4, 4⟩]
  exact AllWinning.cons node_11530 (AllWinning.cons node_10460 (AllWinning.cons node_11584 (AllWinning.cons node_10579 (AllWinning.cons node_11587 (AllWinning.cons node_10587 (AllWinning.nil))))))

theorem node_12573 : Outcome ⟨9, 10, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 10, 6, 2⟩, ⟨7, 10, 6, 4⟩, ⟨6, 10, 6, 6⟩, ⟨5, 10, 6, 8⟩, ⟨9, 9, 6, 2⟩, ⟨9, 8, 6, 4⟩, ⟨9, 7, 6, 6⟩, ⟨9, 6, 6, 8⟩, ⟨9, 10, 5, 2⟩, ⟨9, 10, 4, 4⟩, ⟨9, 10, 3, 6⟩, ⟨9, 10, 2, 8⟩]
  exact AllWinning.cons node_11530 (AllWinning.cons node_10460 (AllWinning.cons node_9377 (AllWinning.cons node_8322 (AllWinning.cons node_11584 (AllWinning.cons node_10579 (AllWinning.cons node_9539 (AllWinning.cons node_8604 (AllWinning.cons node_11587 (AllWinning.cons node_10587 (AllWinning.cons node_9551 (AllWinning.cons node_8618 (AllWinning.nil))))))))))))

theorem node_12574 : Outcome ⟨9, 10, 6, 14⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 10⟩) (by decide) node_7317

theorem node_12575 : Outcome ⟨9, 10, 6, 18⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 10⟩) (by decide) node_7317

theorem node_12576 : Outcome ⟨9, 11, 5, 4⟩ true :=
  Outcome.win (q := ⟨9, 9, 5, 4⟩) (by decide) node_10583

theorem node_12577 : Outcome ⟨9, 11, 5, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 12⟩) (by decide) node_6335

theorem node_12578 : Outcome ⟨9, 11, 5, 12⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 20⟩) (by decide) node_3804

theorem node_12579 : Outcome ⟨9, 12, 4, 8⟩ true :=
  Outcome.win (q := ⟨8, 12, 4, 2⟩) (by decide) node_11538

theorem node_12580 : Outcome ⟨9, 13, 3, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 1, 4⟩) (by decide) node_10595

theorem node_12581 : Outcome ⟨9, 13, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 12⟩) (by decide) node_6350

theorem node_12582 : Outcome ⟨9, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 0, 4⟩) (by decide) node_10599

theorem node_12583 : Outcome ⟨9, 14, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 10⟩) (by decide) node_7337

theorem node_12584 : Outcome ⟨9, 15, 1, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 1, 4⟩) (by decide) node_10595

theorem node_12585 : Outcome ⟨9, 15, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 1, 4⟩) (by decide) node_10595

theorem node_12586 : Outcome ⟨9, 15, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 10⟩) (by decide) node_7344

theorem node_12587 : Outcome ⟨9, 15, 1, 14⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 20⟩) (by decide) node_3832

theorem node_12588 : Outcome ⟨9, 16, 0, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 0, 4⟩) (by decide) node_10599

theorem node_12589 : Outcome ⟨9, 16, 0, 4⟩ true :=
  Outcome.win (q := ⟨9, 14, 0, 4⟩) (by decide) node_10599

theorem node_12590 : Outcome ⟨9, 16, 0, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 14⟩) (by decide) node_5876

theorem node_12591 : Outcome ⟨9, 16, 0, 14⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 14⟩) (by decide) node_5876

theorem node_12592 : Outcome ⟨10, 0, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 0, 15, 2⟩, ⟨8, 0, 15, 4⟩, ⟨10, 0, 14, 2⟩, ⟨10, 0, 13, 4⟩]
  exact AllWinning.cons node_11553 (AllWinning.cons node_10492 (AllWinning.cons node_11610 (AllWinning.cons node_10602 (AllWinning.nil))))

theorem node_12593 : Outcome ⟨10, 0, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 0, 15, 2⟩, ⟨8, 0, 15, 4⟩, ⟨7, 0, 15, 6⟩, ⟨6, 0, 15, 8⟩, ⟨10, 0, 14, 2⟩, ⟨10, 0, 13, 4⟩, ⟨10, 0, 12, 6⟩, ⟨10, 0, 11, 8⟩]
  exact AllWinning.cons node_11553 (AllWinning.cons node_10492 (AllWinning.cons node_9406 (AllWinning.cons node_8344 (AllWinning.cons node_11610 (AllWinning.cons node_10602 (AllWinning.cons node_9562 (AllWinning.cons node_8627 (AllWinning.nil))))))))

theorem node_12594 : Outcome ⟨10, 0, 15, 6⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 10⟩) (by decide) node_7633

theorem node_12595 : Outcome ⟨10, 0, 15, 10⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 10⟩) (by decide) node_7633

theorem node_12596 : Outcome ⟨10, 1, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.nil)))))

theorem node_12597 : Outcome ⟨10, 1, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.nil)))))))))

theorem node_12598 : Outcome ⟨10, 1, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨5, 1, 14, 10⟩, ⟨4, 1, 14, 12⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩, ⟨10, 1, 9, 10⟩, ⟨10, 1, 8, 12⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_7357 (AllWinning.cons node_6373 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.cons node_7642 (AllWinning.cons node_6705 (AllWinning.nil)))))))))))))

theorem node_12599 : Outcome ⟨10, 1, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨5, 1, 14, 10⟩, ⟨4, 1, 14, 12⟩, ⟨3, 1, 14, 14⟩, ⟨2, 1, 14, 16⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩, ⟨10, 1, 9, 10⟩, ⟨10, 1, 8, 12⟩, ⟨10, 1, 7, 14⟩, ⟨10, 1, 6, 16⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_7357 (AllWinning.cons node_6373 (AllWinning.cons node_5526 (AllWinning.cons node_4728 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.cons node_7642 (AllWinning.cons node_6705 (AllWinning.cons node_5889 (AllWinning.cons node_5151 (AllWinning.nil)))))))))))))))))

theorem node_12600 : Outcome ⟨10, 1, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨5, 1, 14, 10⟩, ⟨4, 1, 14, 12⟩, ⟨3, 1, 14, 14⟩, ⟨2, 1, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨0, 1, 14, 20⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩, ⟨10, 1, 9, 10⟩, ⟨10, 1, 8, 12⟩, ⟨10, 1, 7, 14⟩, ⟨10, 1, 6, 16⟩, ⟨10, 1, 5, 18⟩, ⟨10, 1, 4, 20⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_7357 (AllWinning.cons node_6373 (AllWinning.cons node_5526 (AllWinning.cons node_4728 (AllWinning.cons node_4006 (AllWinning.cons node_3327 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.cons node_7642 (AllWinning.cons node_6705 (AllWinning.cons node_5889 (AllWinning.cons node_5151 (AllWinning.cons node_4476 (AllWinning.cons node_3848 (AllWinning.nil)))))))))))))))))))))

theorem node_12601 : Outcome ⟨10, 1, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨5, 1, 14, 10⟩, ⟨4, 1, 14, 12⟩, ⟨3, 1, 14, 14⟩, ⟨2, 1, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨0, 1, 14, 20⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩, ⟨10, 1, 9, 10⟩, ⟨10, 1, 8, 12⟩, ⟨10, 1, 7, 14⟩, ⟨10, 1, 6, 16⟩, ⟨10, 1, 5, 18⟩, ⟨10, 1, 4, 20⟩, ⟨10, 1, 3, 22⟩, ⟨10, 1, 2, 24⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_7357 (AllWinning.cons node_6373 (AllWinning.cons node_5526 (AllWinning.cons node_4728 (AllWinning.cons node_4006 (AllWinning.cons node_3327 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.cons node_7642 (AllWinning.cons node_6705 (AllWinning.cons node_5889 (AllWinning.cons node_5151 (AllWinning.cons node_4476 (AllWinning.cons node_3848 (AllWinning.cons node_3266 (AllWinning.cons node_2782 (AllWinning.nil)))))))))))))))))))))))

theorem node_12602 : Outcome ⟨10, 1, 14, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨5, 1, 14, 10⟩, ⟨4, 1, 14, 12⟩, ⟨3, 1, 14, 14⟩, ⟨2, 1, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨0, 1, 14, 20⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩, ⟨10, 1, 9, 10⟩, ⟨10, 1, 8, 12⟩, ⟨10, 1, 7, 14⟩, ⟨10, 1, 6, 16⟩, ⟨10, 1, 5, 18⟩, ⟨10, 1, 4, 20⟩, ⟨10, 1, 3, 22⟩, ⟨10, 1, 2, 24⟩, ⟨10, 1, 1, 26⟩, ⟨10, 1, 0, 28⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_7357 (AllWinning.cons node_6373 (AllWinning.cons node_5526 (AllWinning.cons node_4728 (AllWinning.cons node_4006 (AllWinning.cons node_3327 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.cons node_7642 (AllWinning.cons node_6705 (AllWinning.cons node_5889 (AllWinning.cons node_5151 (AllWinning.cons node_4476 (AllWinning.cons node_3848 (AllWinning.cons node_3266 (AllWinning.cons node_2782 (AllWinning.cons node_2341 (AllWinning.cons node_1859 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12603 : Outcome ⟨10, 1, 14, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨5, 1, 14, 10⟩, ⟨4, 1, 14, 12⟩, ⟨3, 1, 14, 14⟩, ⟨2, 1, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨0, 1, 14, 20⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩, ⟨10, 1, 9, 10⟩, ⟨10, 1, 8, 12⟩, ⟨10, 1, 7, 14⟩, ⟨10, 1, 6, 16⟩, ⟨10, 1, 5, 18⟩, ⟨10, 1, 4, 20⟩, ⟨10, 1, 3, 22⟩, ⟨10, 1, 2, 24⟩, ⟨10, 1, 1, 26⟩, ⟨10, 1, 0, 28⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_7357 (AllWinning.cons node_6373 (AllWinning.cons node_5526 (AllWinning.cons node_4728 (AllWinning.cons node_4006 (AllWinning.cons node_3327 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.cons node_7642 (AllWinning.cons node_6705 (AllWinning.cons node_5889 (AllWinning.cons node_5151 (AllWinning.cons node_4476 (AllWinning.cons node_3848 (AllWinning.cons node_3266 (AllWinning.cons node_2782 (AllWinning.cons node_2341 (AllWinning.cons node_1859 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12604 : Outcome ⟨10, 1, 14, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 14, 2⟩, ⟨8, 1, 14, 4⟩, ⟨7, 1, 14, 6⟩, ⟨6, 1, 14, 8⟩, ⟨5, 1, 14, 10⟩, ⟨4, 1, 14, 12⟩, ⟨3, 1, 14, 14⟩, ⟨2, 1, 14, 16⟩, ⟨1, 1, 14, 18⟩, ⟨0, 1, 14, 20⟩, ⟨10, 0, 14, 2⟩, ⟨10, 1, 13, 2⟩, ⟨10, 1, 12, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 1, 10, 8⟩, ⟨10, 1, 9, 10⟩, ⟨10, 1, 8, 12⟩, ⟨10, 1, 7, 14⟩, ⟨10, 1, 6, 16⟩, ⟨10, 1, 5, 18⟩, ⟨10, 1, 4, 20⟩, ⟨10, 1, 3, 22⟩, ⟨10, 1, 2, 24⟩, ⟨10, 1, 1, 26⟩, ⟨10, 1, 0, 28⟩]
  exact AllWinning.cons node_11556 (AllWinning.cons node_10496 (AllWinning.cons node_9410 (AllWinning.cons node_8348 (AllWinning.cons node_7357 (AllWinning.cons node_6373 (AllWinning.cons node_5526 (AllWinning.cons node_4728 (AllWinning.cons node_4006 (AllWinning.cons node_3327 (AllWinning.cons node_11610 (AllWinning.cons node_11612 (AllWinning.cons node_10605 (AllWinning.cons node_9565 (AllWinning.cons node_8630 (AllWinning.cons node_7642 (AllWinning.cons node_6705 (AllWinning.cons node_5889 (AllWinning.cons node_5151 (AllWinning.cons node_4476 (AllWinning.cons node_3848 (AllWinning.cons node_3266 (AllWinning.cons node_2782 (AllWinning.cons node_2341 (AllWinning.cons node_1859 (AllWinning.nil)))))))))))))))))))))))))

theorem node_12605 : Outcome ⟨10, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 12, 2⟩) (by decide) node_11615

theorem node_12606 : Outcome ⟨10, 2, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 2, 12, 2⟩) (by decide) node_11615

theorem node_12607 : Outcome ⟨10, 3, 12, 2⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 2⟩) (by decide) node_11561

theorem node_12608 : Outcome ⟨10, 3, 12, 4⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 2⟩) (by decide) node_11561

theorem node_12609 : Outcome ⟨10, 4, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 4, 11, 2⟩, ⟨8, 4, 11, 4⟩, ⟨10, 3, 11, 2⟩, ⟨10, 2, 11, 4⟩, ⟨10, 4, 10, 2⟩, ⟨10, 4, 9, 4⟩]
  exact AllWinning.cons node_11570 (AllWinning.cons node_10504 (AllWinning.cons node_11618 (AllWinning.cons node_10608 (AllWinning.cons node_11622 (AllWinning.cons node_10617 (AllWinning.nil))))))

theorem node_12610 : Outcome ⟨10, 4, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 4, 11, 2⟩, ⟨8, 4, 11, 4⟩, ⟨7, 4, 11, 6⟩, ⟨6, 4, 11, 8⟩, ⟨10, 3, 11, 2⟩, ⟨10, 2, 11, 4⟩, ⟨10, 1, 11, 6⟩, ⟨10, 0, 11, 8⟩, ⟨10, 4, 10, 2⟩, ⟨10, 4, 9, 4⟩, ⟨10, 4, 8, 6⟩, ⟨10, 4, 7, 8⟩]
  exact AllWinning.cons node_11570 (AllWinning.cons node_10504 (AllWinning.cons node_9422 (AllWinning.cons node_8357 (AllWinning.cons node_11618 (AllWinning.cons node_10608 (AllWinning.cons node_9565 (AllWinning.cons node_8627 (AllWinning.cons node_11622 (AllWinning.cons node_10617 (AllWinning.cons node_9577 (AllWinning.cons node_8643 (AllWinning.nil))))))))))))

theorem node_12611 : Outcome ⟨10, 4, 11, 8⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 10⟩) (by decide) node_7655

theorem node_12612 : Outcome ⟨10, 5, 10, 4⟩ true :=
  Outcome.win (q := ⟨8, 5, 10, 4⟩) (by decide) node_10508

theorem node_12613 : Outcome ⟨10, 5, 10, 18⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 16⟩) (by decide) node_4750

theorem node_12614 : Outcome ⟨10, 5, 10, 24⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 16⟩) (by decide) node_4750

theorem node_12615 : Outcome ⟨10, 6, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 6, 9, 2⟩, ⟨8, 6, 9, 4⟩, ⟨10, 5, 9, 2⟩, ⟨10, 4, 9, 4⟩, ⟨10, 6, 8, 2⟩, ⟨10, 6, 7, 4⟩]
  exact AllWinning.cons node_11577 (AllWinning.cons node_10513 (AllWinning.cons node_11624 (AllWinning.cons node_10617 (AllWinning.cons node_11628 (AllWinning.cons node_10626 (AllWinning.nil))))))

theorem node_12616 : Outcome ⟨10, 6, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 6, 9, 2⟩, ⟨8, 6, 9, 4⟩, ⟨7, 6, 9, 6⟩, ⟨6, 6, 9, 8⟩, ⟨10, 5, 9, 2⟩, ⟨10, 4, 9, 4⟩, ⟨10, 3, 9, 6⟩, ⟨10, 2, 9, 8⟩, ⟨10, 6, 8, 2⟩, ⟨10, 6, 7, 4⟩, ⟨10, 6, 6, 6⟩, ⟨10, 6, 5, 8⟩]
  exact AllWinning.cons node_11577 (AllWinning.cons node_10513 (AllWinning.cons node_9430 (AllWinning.cons node_8365 (AllWinning.cons node_11624 (AllWinning.cons node_10617 (AllWinning.cons node_9573 (AllWinning.cons node_8633 (AllWinning.cons node_11628 (AllWinning.cons node_10626 (AllWinning.cons node_9585 (AllWinning.cons node_8650 (AllWinning.nil))))))))))))

theorem node_12617 : Outcome ⟨10, 6, 9, 14⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 10⟩) (by decide) node_7669

theorem node_12618 : Outcome ⟨10, 6, 9, 18⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 10⟩) (by decide) node_7669

theorem node_12619 : Outcome ⟨10, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 8, 4⟩) (by decide) node_10620

theorem node_12620 : Outcome ⟨10, 7, 8, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 8⟩) (by decide) node_8370

theorem node_12621 : Outcome ⟨10, 7, 8, 8⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 8⟩) (by decide) node_8370

theorem node_12622 : Outcome ⟨10, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨10, 8, 5, 4⟩) (by decide) node_10638

theorem node_12623 : Outcome ⟨10, 8, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 8⟩) (by decide) node_8382

theorem node_12624 : Outcome ⟨10, 8, 7, 8⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 8⟩) (by decide) node_8382

theorem node_12625 : Outcome ⟨10, 9, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 9, 6, 2⟩, ⟨8, 9, 6, 4⟩, ⟨10, 8, 6, 2⟩, ⟨10, 7, 6, 4⟩, ⟨10, 9, 5, 2⟩, ⟨10, 9, 4, 4⟩]
  exact AllWinning.cons node_11584 (AllWinning.cons node_10526 (AllWinning.cons node_11635 (AllWinning.cons node_10632 (AllWinning.cons node_11639 (AllWinning.cons node_10644 (AllWinning.nil))))))

theorem node_12626 : Outcome ⟨10, 9, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 9, 6, 2⟩, ⟨8, 9, 6, 4⟩, ⟨7, 9, 6, 6⟩, ⟨6, 9, 6, 8⟩, ⟨10, 8, 6, 2⟩, ⟨10, 7, 6, 4⟩, ⟨10, 6, 6, 6⟩, ⟨10, 5, 6, 8⟩, ⟨10, 9, 5, 2⟩, ⟨10, 9, 4, 4⟩, ⟨10, 9, 3, 6⟩, ⟨10, 9, 2, 8⟩]
  exact AllWinning.cons node_11584 (AllWinning.cons node_10526 (AllWinning.cons node_9439 (AllWinning.cons node_8393 (AllWinning.cons node_11635 (AllWinning.cons node_10632 (AllWinning.cons node_9585 (AllWinning.cons node_8646 (AllWinning.cons node_11639 (AllWinning.cons node_10644 (AllWinning.cons node_9598 (AllWinning.cons node_8662 (AllWinning.nil))))))))))))

theorem node_12627 : Outcome ⟨10, 9, 6, 14⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 10⟩) (by decide) node_7655

theorem node_12628 : Outcome ⟨10, 9, 6, 18⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 10⟩) (by decide) node_7655

theorem node_12629 : Outcome ⟨10, 10, 5, 4⟩ true :=
  Outcome.win (q := ⟨8, 10, 5, 4⟩) (by decide) node_10530

theorem node_12630 : Outcome ⟨10, 10, 5, 18⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 16⟩) (by decide) node_4779

theorem node_12631 : Outcome ⟨10, 10, 5, 24⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 16⟩) (by decide) node_4779

theorem node_12632 : Outcome ⟨10, 11, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 4, 2⟩, ⟨8, 11, 4, 4⟩, ⟨10, 10, 4, 2⟩, ⟨10, 9, 4, 4⟩, ⟨10, 11, 3, 2⟩, ⟨10, 11, 2, 4⟩]
  exact AllWinning.cons node_11591 (AllWinning.cons node_10536 (AllWinning.cons node_11643 (AllWinning.cons node_10644 (AllWinning.cons node_11645 (AllWinning.cons node_10650 (AllWinning.nil))))))

theorem node_12633 : Outcome ⟨10, 11, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 4, 2⟩, ⟨8, 11, 4, 4⟩, ⟨7, 11, 4, 6⟩, ⟨6, 11, 4, 8⟩, ⟨10, 10, 4, 2⟩, ⟨10, 9, 4, 4⟩, ⟨10, 8, 4, 6⟩, ⟨10, 7, 4, 8⟩, ⟨10, 11, 3, 2⟩, ⟨10, 11, 2, 4⟩, ⟨10, 11, 1, 6⟩, ⟨10, 11, 0, 8⟩]
  exact AllWinning.cons node_11591 (AllWinning.cons node_10536 (AllWinning.cons node_9449 (AllWinning.cons node_8400 (AllWinning.cons node_11643 (AllWinning.cons node_10644 (AllWinning.cons node_9594 (AllWinning.cons node_8654 (AllWinning.cons node_11645 (AllWinning.cons node_10650 (AllWinning.cons node_9603 (AllWinning.cons node_8668 (AllWinning.nil))))))))))))

theorem node_12634 : Outcome ⟨10, 11, 4, 8⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 10⟩) (by decide) node_7669

theorem node_12635 : Outcome ⟨10, 12, 3, 2⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 2⟩) (by decide) node_11594

theorem node_12636 : Outcome ⟨10, 12, 3, 4⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 2⟩) (by decide) node_11594

theorem node_12637 : Outcome ⟨10, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 12, 2, 2⟩) (by decide) node_11649

theorem node_12638 : Outcome ⟨10, 13, 2, 6⟩ true :=
  Outcome.win (q := ⟨10, 12, 2, 2⟩) (by decide) node_11649

end RQ9F1
