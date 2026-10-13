import Chunk01
set_option autoImplicit false
namespace RQ9F1

theorem node_565 : Outcome ⟨2, 1, 4, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 4, 2⟩, ⟨0, 1, 4, 4⟩, ⟨2, 0, 4, 2⟩, ⟨2, 1, 3, 2⟩, ⟨2, 1, 2, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 1, 0, 8⟩]
  exact AllWinning.cons node_368 (AllWinning.cons node_240 (AllWinning.cons node_383 (AllWinning.cons node_388 (AllWinning.cons node_285 (AllWinning.cons node_201 (AllWinning.cons node_126 (AllWinning.nil)))))))

theorem node_566 : Outcome ⟨2, 1, 4, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 4, 2⟩, ⟨0, 1, 4, 4⟩, ⟨2, 0, 4, 2⟩, ⟨2, 1, 3, 2⟩, ⟨2, 1, 2, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 1, 0, 8⟩]
  exact AllWinning.cons node_368 (AllWinning.cons node_240 (AllWinning.cons node_383 (AllWinning.cons node_388 (AllWinning.cons node_285 (AllWinning.cons node_201 (AllWinning.cons node_126 (AllWinning.nil)))))))

theorem node_567 : Outcome ⟨2, 1, 4, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 4, 2⟩, ⟨0, 1, 4, 4⟩, ⟨2, 0, 4, 2⟩, ⟨2, 1, 3, 2⟩, ⟨2, 1, 2, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 1, 0, 8⟩]
  exact AllWinning.cons node_368 (AllWinning.cons node_240 (AllWinning.cons node_383 (AllWinning.cons node_388 (AllWinning.cons node_285 (AllWinning.cons node_201 (AllWinning.cons node_126 (AllWinning.nil)))))))

theorem node_568 : Outcome ⟨2, 1, 4, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 4, 2⟩, ⟨0, 1, 4, 4⟩, ⟨2, 0, 4, 2⟩, ⟨2, 1, 3, 2⟩, ⟨2, 1, 2, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 1, 0, 8⟩]
  exact AllWinning.cons node_368 (AllWinning.cons node_240 (AllWinning.cons node_383 (AllWinning.cons node_388 (AllWinning.cons node_285 (AllWinning.cons node_201 (AllWinning.cons node_126 (AllWinning.nil)))))))

theorem node_569 : Outcome ⟨2, 1, 4, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 4, 2⟩, ⟨0, 1, 4, 4⟩, ⟨2, 0, 4, 2⟩, ⟨2, 1, 3, 2⟩, ⟨2, 1, 2, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 1, 0, 8⟩]
  exact AllWinning.cons node_368 (AllWinning.cons node_240 (AllWinning.cons node_383 (AllWinning.cons node_388 (AllWinning.cons node_285 (AllWinning.cons node_201 (AllWinning.cons node_126 (AllWinning.nil)))))))

theorem node_570 : Outcome ⟨2, 1, 4, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 4, 2⟩, ⟨0, 1, 4, 4⟩, ⟨2, 0, 4, 2⟩, ⟨2, 1, 3, 2⟩, ⟨2, 1, 2, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 1, 0, 8⟩]
  exact AllWinning.cons node_368 (AllWinning.cons node_240 (AllWinning.cons node_383 (AllWinning.cons node_388 (AllWinning.cons node_285 (AllWinning.cons node_201 (AllWinning.cons node_126 (AllWinning.nil)))))))

theorem node_571 : Outcome ⟨2, 1, 4, 36⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 4, 2⟩, ⟨0, 1, 4, 4⟩, ⟨2, 0, 4, 2⟩, ⟨2, 1, 3, 2⟩, ⟨2, 1, 2, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 1, 0, 8⟩]
  exact AllWinning.cons node_368 (AllWinning.cons node_240 (AllWinning.cons node_383 (AllWinning.cons node_388 (AllWinning.cons node_285 (AllWinning.cons node_201 (AllWinning.cons node_126 (AllWinning.nil)))))))

theorem node_572 : Outcome ⟨2, 2, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_573 : Outcome ⟨2, 2, 3, 10⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_574 : Outcome ⟨2, 2, 3, 20⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_575 : Outcome ⟨2, 3, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 6⟩) (by decide) node_185

theorem node_576 : Outcome ⟨2, 3, 2, 10⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 6⟩) (by decide) node_185

theorem node_577 : Outcome ⟨2, 3, 2, 20⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 6⟩) (by decide) node_185

theorem node_578 : Outcome ⟨2, 4, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_398 (AllWinning.nil)))))

theorem node_579 : Outcome ⟨2, 4, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_580 : Outcome ⟨2, 4, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_581 : Outcome ⟨2, 4, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_582 : Outcome ⟨2, 4, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_583 : Outcome ⟨2, 4, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_584 : Outcome ⟨2, 4, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_585 : Outcome ⟨2, 4, 1, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_586 : Outcome ⟨2, 4, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_587 : Outcome ⟨2, 4, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_588 : Outcome ⟨2, 4, 1, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_589 : Outcome ⟨2, 4, 1, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_590 : Outcome ⟨2, 4, 1, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_591 : Outcome ⟨2, 4, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_592 : Outcome ⟨2, 4, 1, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_593 : Outcome ⟨2, 4, 1, 36⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 1, 2⟩, ⟨0, 4, 1, 4⟩, ⟨2, 3, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨2, 4, 0, 2⟩]
  exact AllWinning.cons node_377 (AllWinning.cons node_253 (AllWinning.cons node_395 (AllWinning.cons node_288 (AllWinning.cons node_201 (AllWinning.cons node_122 (AllWinning.cons node_398 (AllWinning.nil)))))))

theorem node_594 : Outcome ⟨2, 5, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_595 : Outcome ⟨2, 5, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_596 : Outcome ⟨2, 5, 0, 10⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_597 : Outcome ⟨2, 5, 0, 20⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_598 : Outcome ⟨3, 0, 4, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_599 : Outcome ⟨3, 0, 4, 24⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_600 : Outcome ⟨3, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_601 : Outcome ⟨3, 1, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_602 : Outcome ⟨3, 1, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_603 : Outcome ⟨3, 1, 3, 24⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_604 : Outcome ⟨3, 2, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 2, 2⟩, ⟨1, 2, 2, 4⟩, ⟨3, 1, 2, 2⟩, ⟨3, 0, 2, 4⟩, ⟨3, 2, 1, 2⟩, ⟨3, 2, 0, 4⟩]
  exact AllWinning.cons node_391 (AllWinning.cons node_270 (AllWinning.cons node_420 (AllWinning.cons node_296 (AllWinning.cons node_423 (AllWinning.cons node_305 (AllWinning.nil))))))

theorem node_605 : Outcome ⟨3, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 6⟩) (by decide) node_143

theorem node_606 : Outcome ⟨3, 2, 2, 10⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 6⟩) (by decide) node_143

theorem node_607 : Outcome ⟨3, 2, 2, 20⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 6⟩) (by decide) node_143

theorem node_608 : Outcome ⟨3, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_609 : Outcome ⟨3, 3, 1, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_610 : Outcome ⟨3, 3, 1, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_611 : Outcome ⟨3, 3, 1, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_612 : Outcome ⟨3, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_613 : Outcome ⟨3, 4, 0, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_614 : Outcome ⟨4, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_615 : Outcome ⟨4, 0, 3, 24⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 2⟩) (by decide) node_403

theorem node_616 : Outcome ⟨4, 1, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))

theorem node_617 : Outcome ⟨4, 1, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_618 : Outcome ⟨4, 1, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_619 : Outcome ⟨4, 1, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_620 : Outcome ⟨4, 1, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_621 : Outcome ⟨4, 1, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_622 : Outcome ⟨4, 1, 2, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_623 : Outcome ⟨4, 1, 2, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_624 : Outcome ⟨4, 1, 2, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_625 : Outcome ⟨4, 1, 2, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_626 : Outcome ⟨4, 1, 2, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_627 : Outcome ⟨4, 1, 2, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_628 : Outcome ⟨4, 1, 2, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_629 : Outcome ⟨4, 1, 2, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_630 : Outcome ⟨4, 1, 2, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_631 : Outcome ⟨4, 1, 2, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_632 : Outcome ⟨4, 1, 2, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_633 : Outcome ⟨4, 1, 2, 36⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 2, 2⟩, ⟨2, 1, 2, 4⟩, ⟨1, 1, 2, 6⟩, ⟨0, 1, 2, 8⟩, ⟨4, 0, 2, 2⟩, ⟨4, 1, 1, 2⟩, ⟨4, 1, 0, 4⟩]
  exact AllWinning.cons node_420 (AllWinning.cons node_285 (AllWinning.cons node_171 (AllWinning.cons node_100 (AllWinning.cons node_443 (AllWinning.cons node_448 (AllWinning.cons node_315 (AllWinning.nil)))))))

theorem node_634 : Outcome ⟨4, 2, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))

theorem node_635 : Outcome ⟨4, 2, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_636 : Outcome ⟨4, 2, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_637 : Outcome ⟨4, 2, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_638 : Outcome ⟨4, 2, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_639 : Outcome ⟨4, 2, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_640 : Outcome ⟨4, 2, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_641 : Outcome ⟨4, 2, 1, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_642 : Outcome ⟨4, 2, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_643 : Outcome ⟨4, 2, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_644 : Outcome ⟨4, 2, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_645 : Outcome ⟨4, 2, 1, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_646 : Outcome ⟨4, 2, 1, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_647 : Outcome ⟨4, 2, 1, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_648 : Outcome ⟨4, 2, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_649 : Outcome ⟨4, 2, 1, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_650 : Outcome ⟨4, 2, 1, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_651 : Outcome ⟨4, 2, 1, 36⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 1, 2⟩, ⟨2, 2, 1, 4⟩, ⟨1, 2, 1, 6⟩, ⟨0, 2, 1, 8⟩, ⟨4, 1, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨4, 2, 0, 2⟩]
  exact AllWinning.cons node_423 (AllWinning.cons node_288 (AllWinning.cons node_175 (AllWinning.cons node_104 (AllWinning.cons node_448 (AllWinning.cons node_310 (AllWinning.cons node_451 (AllWinning.nil)))))))

theorem node_652 : Outcome ⟨4, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_653 : Outcome ⟨4, 3, 0, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 2⟩) (by decide) node_426

theorem node_654 : Outcome ⟨5, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 6⟩) (by decide) node_185

theorem node_655 : Outcome ⟨5, 0, 2, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 6⟩) (by decide) node_185

theorem node_656 : Outcome ⟨5, 0, 2, 10⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 6⟩) (by decide) node_185

theorem node_657 : Outcome ⟨5, 0, 2, 20⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 6⟩) (by decide) node_185

theorem node_658 : Outcome ⟨5, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 1, 2⟩, ⟨3, 1, 1, 4⟩, ⟨5, 0, 1, 2⟩, ⟨5, 1, 0, 2⟩]
  exact AllWinning.cons node_448 (AllWinning.cons node_301 (AllWinning.cons node_456 (AllWinning.cons node_459 (AllWinning.nil))))

theorem node_659 : Outcome ⟨5, 1, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 1, 2⟩, ⟨3, 1, 1, 4⟩, ⟨2, 1, 1, 6⟩, ⟨1, 1, 1, 8⟩, ⟨5, 0, 1, 2⟩, ⟨5, 1, 0, 2⟩]
  exact AllWinning.cons node_448 (AllWinning.cons node_301 (AllWinning.cons node_201 (AllWinning.cons node_115 (AllWinning.cons node_456 (AllWinning.cons node_459 (AllWinning.nil))))))

theorem node_660 : Outcome ⟨5, 1, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 10⟩) (by decide) node_36

theorem node_661 : Outcome ⟨5, 1, 1, 16⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 10⟩) (by decide) node_36

theorem node_662 : Outcome ⟨5, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_663 : Outcome ⟨5, 2, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_664 : Outcome ⟨5, 2, 0, 10⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_665 : Outcome ⟨5, 2, 0, 20⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 6⟩) (by decide) node_206

theorem node_666 : Outcome ⟨6, 0, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨6, 0, 0, 2⟩]
  exact AllWinning.cons node_456 (AllWinning.cons node_310 (AllWinning.cons node_462 (AllWinning.nil)))

theorem node_667 : Outcome ⟨6, 0, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 0, 1, 2⟩, ⟨4, 0, 1, 4⟩, ⟨3, 0, 1, 6⟩, ⟨2, 0, 1, 8⟩, ⟨6, 0, 0, 2⟩]
  exact AllWinning.cons node_456 (AllWinning.cons node_310 (AllWinning.cons node_223 (AllWinning.cons node_122 (AllWinning.cons node_462 (AllWinning.nil)))))

theorem node_668 : Outcome ⟨6, 0, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 10⟩) (by decide) node_58

theorem node_669 : Outcome ⟨6, 0, 1, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 10⟩) (by decide) node_58

theorem node_670 : Outcome ⟨6, 0, 1, 16⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 10⟩) (by decide) node_58

theorem node_671 : Outcome ⟨6, 1, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 0, 2⟩, ⟨4, 1, 0, 4⟩, ⟨6, 0, 0, 2⟩]
  exact AllWinning.cons node_459 (AllWinning.cons node_315 (AllWinning.cons node_462 (AllWinning.nil)))

theorem node_672 : Outcome ⟨6, 1, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 0, 2⟩, ⟨4, 1, 0, 4⟩, ⟨3, 1, 0, 6⟩, ⟨2, 1, 0, 8⟩, ⟨6, 0, 0, 2⟩]
  exact AllWinning.cons node_459 (AllWinning.cons node_315 (AllWinning.cons node_228 (AllWinning.cons node_126 (AllWinning.cons node_462 (AllWinning.nil)))))

theorem node_673 : Outcome ⟨6, 1, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 10⟩) (by decide) node_75

theorem node_674 : Outcome ⟨6, 1, 0, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 10⟩) (by decide) node_75

theorem node_675 : Outcome ⟨6, 1, 0, 16⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 10⟩) (by decide) node_75

theorem node_676 : Outcome ⟨7, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 0, 4⟩) (by decide) node_320

theorem node_677 : Outcome ⟨7, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 0, 4⟩) (by decide) node_320

theorem node_678 : Outcome ⟨7, 0, 0, 12⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 14⟩) (by decide) node_6

theorem node_679 : Outcome ⟨7, 0, 0, 14⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 14⟩) (by decide) node_6

theorem node_680 : Outcome ⟨0, 0, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 7, 2⟩, ⟨0, 0, 6, 4⟩]
  exact AllWinning.cons node_466 (AllWinning.cons node_326 (AllWinning.nil))

theorem node_681 : Outcome ⟨0, 0, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 7, 2⟩, ⟨0, 0, 6, 4⟩, ⟨0, 0, 5, 6⟩, ⟨0, 0, 4, 8⟩]
  exact AllWinning.cons node_466 (AllWinning.cons node_326 (AllWinning.cons node_236 (AllWinning.cons node_134 (AllWinning.nil))))

theorem node_682 : Outcome ⟨0, 0, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 7, 2⟩, ⟨0, 0, 6, 4⟩, ⟨0, 0, 5, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 0, 3, 10⟩, ⟨0, 0, 2, 12⟩]
  exact AllWinning.cons node_466 (AllWinning.cons node_326 (AllWinning.cons node_236 (AllWinning.cons node_134 (AllWinning.cons node_96 (AllWinning.cons node_30 (AllWinning.nil))))))

theorem node_683 : Outcome ⟨0, 0, 8, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 16⟩) (by decide) node_7

theorem node_684 : Outcome ⟨0, 0, 8, 16⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 16⟩) (by decide) node_7

theorem node_685 : Outcome ⟨0, 1, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 2⟩) (by decide) node_470

theorem node_686 : Outcome ⟨0, 1, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 2⟩) (by decide) node_470

theorem node_687 : Outcome ⟨0, 1, 7, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_688 : Outcome ⟨0, 1, 7, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_689 : Outcome ⟨0, 1, 7, 14⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_690 : Outcome ⟨0, 1, 7, 22⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_691 : Outcome ⟨0, 2, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 2⟩) (by decide) node_470

theorem node_692 : Outcome ⟨0, 2, 6, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_693 : Outcome ⟨0, 2, 6, 18⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_694 : Outcome ⟨0, 2, 6, 22⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_695 : Outcome ⟨0, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_696 : Outcome ⟨0, 3, 5, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_697 : Outcome ⟨0, 3, 5, 12⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_698 : Outcome ⟨0, 3, 5, 22⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_699 : Outcome ⟨0, 4, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.nil))))

theorem node_700 : Outcome ⟨0, 4, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_701 : Outcome ⟨0, 4, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_702 : Outcome ⟨0, 4, 4, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_703 : Outcome ⟨0, 4, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_704 : Outcome ⟨0, 4, 4, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_705 : Outcome ⟨0, 4, 4, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_706 : Outcome ⟨0, 4, 4, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_707 : Outcome ⟨0, 4, 4, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_708 : Outcome ⟨0, 4, 4, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_709 : Outcome ⟨0, 4, 4, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_710 : Outcome ⟨0, 4, 4, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_711 : Outcome ⟨0, 4, 4, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_712 : Outcome ⟨0, 4, 4, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_713 : Outcome ⟨0, 4, 4, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_714 : Outcome ⟨0, 4, 4, 38⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 4, 2⟩, ⟨0, 2, 4, 4⟩, ⟨0, 1, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨0, 4, 3, 2⟩, ⟨0, 4, 2, 4⟩, ⟨0, 4, 1, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_479 (AllWinning.cons node_333 (AllWinning.cons node_241 (AllWinning.cons node_134 (AllWinning.cons node_481 (AllWinning.cons node_354 (AllWinning.cons node_254 (AllWinning.cons node_163 (AllWinning.nil))))))))

theorem node_715 : Outcome ⟨0, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_716 : Outcome ⟨0, 5, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_717 : Outcome ⟨0, 5, 3, 12⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_718 : Outcome ⟨0, 5, 3, 22⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_719 : Outcome ⟨0, 6, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 2⟩) (by decide) node_487

theorem node_720 : Outcome ⟨0, 6, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_721 : Outcome ⟨0, 6, 2, 18⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_722 : Outcome ⟨0, 6, 2, 22⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_723 : Outcome ⟨0, 7, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 2⟩) (by decide) node_487

theorem node_724 : Outcome ⟨0, 7, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 2⟩) (by decide) node_487

theorem node_725 : Outcome ⟨0, 7, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_726 : Outcome ⟨0, 7, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_727 : Outcome ⟨0, 7, 1, 14⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_728 : Outcome ⟨0, 7, 1, 22⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_729 : Outcome ⟨0, 8, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 0, 2⟩, ⟨0, 6, 0, 4⟩]
  exact AllWinning.cons node_492 (AllWinning.cons node_362 (AllWinning.nil))

theorem node_730 : Outcome ⟨0, 8, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 0, 2⟩, ⟨0, 6, 0, 4⟩, ⟨0, 5, 0, 6⟩, ⟨0, 4, 0, 8⟩]
  exact AllWinning.cons node_492 (AllWinning.cons node_362 (AllWinning.cons node_259 (AllWinning.cons node_163 (AllWinning.nil))))

theorem node_731 : Outcome ⟨0, 8, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 0, 2⟩, ⟨0, 6, 0, 4⟩, ⟨0, 5, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨0, 3, 0, 10⟩, ⟨0, 2, 0, 12⟩]
  exact AllWinning.cons node_492 (AllWinning.cons node_362 (AllWinning.cons node_259 (AllWinning.cons node_163 (AllWinning.cons node_109 (AllWinning.cons node_52 (AllWinning.nil))))))

theorem node_732 : Outcome ⟨0, 8, 0, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 16⟩) (by decide) node_7

theorem node_733 : Outcome ⟨0, 8, 0, 16⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 16⟩) (by decide) node_7

theorem node_734 : Outcome ⟨1, 0, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 2⟩) (by decide) node_496

theorem node_735 : Outcome ⟨1, 0, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 2⟩) (by decide) node_496

theorem node_736 : Outcome ⟨1, 0, 7, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_737 : Outcome ⟨1, 0, 7, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_738 : Outcome ⟨1, 0, 7, 14⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_739 : Outcome ⟨1, 0, 7, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_740 : Outcome ⟨1, 1, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 2⟩) (by decide) node_470

theorem node_741 : Outcome ⟨1, 1, 6, 14⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_742 : Outcome ⟨1, 2, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_743 : Outcome ⟨1, 2, 5, 14⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_744 : Outcome ⟨1, 2, 5, 18⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_745 : Outcome ⟨1, 2, 5, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_746 : Outcome ⟨1, 3, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 2⟩) (by decide) node_505

theorem node_747 : Outcome ⟨1, 3, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 2⟩) (by decide) node_505

theorem node_748 : Outcome ⟨1, 3, 4, 24⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 2⟩) (by decide) node_505

theorem node_749 : Outcome ⟨1, 4, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_750 : Outcome ⟨1, 4, 3, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_751 : Outcome ⟨1, 4, 3, 24⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_752 : Outcome ⟨1, 5, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_753 : Outcome ⟨1, 5, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_754 : Outcome ⟨1, 5, 2, 14⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_755 : Outcome ⟨1, 5, 2, 18⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_756 : Outcome ⟨1, 5, 2, 24⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_757 : Outcome ⟨1, 6, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 2⟩) (by decide) node_487

theorem node_758 : Outcome ⟨1, 6, 1, 14⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_759 : Outcome ⟨1, 7, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 0, 2⟩) (by decide) node_547

theorem node_760 : Outcome ⟨1, 7, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 0, 2⟩) (by decide) node_547

theorem node_761 : Outcome ⟨1, 7, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_762 : Outcome ⟨1, 7, 0, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_763 : Outcome ⟨1, 7, 0, 14⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_764 : Outcome ⟨1, 7, 0, 22⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_765 : Outcome ⟨2, 0, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 2⟩) (by decide) node_496

theorem node_766 : Outcome ⟨2, 0, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_767 : Outcome ⟨2, 0, 6, 18⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_768 : Outcome ⟨2, 0, 6, 22⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_769 : Outcome ⟨2, 1, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_770 : Outcome ⟨2, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_771 : Outcome ⟨2, 1, 5, 14⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_772 : Outcome ⟨2, 1, 5, 18⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_773 : Outcome ⟨2, 1, 5, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 2⟩) (by decide) node_501

theorem node_774 : Outcome ⟨2, 2, 4, 2⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 2⟩) (by decide) node_505

theorem node_775 : Outcome ⟨2, 2, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_776 : Outcome ⟨2, 2, 4, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_777 : Outcome ⟨2, 2, 4, 24⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_778 : Outcome ⟨2, 3, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_779 : Outcome ⟨2, 3, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_780 : Outcome ⟨2, 3, 3, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_781 : Outcome ⟨2, 3, 3, 12⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_782 : Outcome ⟨2, 3, 3, 22⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 4⟩) (by decide) node_338

theorem node_783 : Outcome ⟨2, 4, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 2⟩) (by decide) node_526

theorem node_784 : Outcome ⟨2, 4, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_785 : Outcome ⟨2, 4, 2, 18⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_786 : Outcome ⟨2, 4, 2, 24⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_787 : Outcome ⟨2, 5, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 2⟩) (by decide) node_543

theorem node_788 : Outcome ⟨2, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 2⟩) (by decide) node_543

theorem node_789 : Outcome ⟨2, 5, 1, 14⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 2⟩) (by decide) node_543

theorem node_790 : Outcome ⟨2, 5, 1, 18⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 2⟩) (by decide) node_543

theorem node_791 : Outcome ⟨2, 5, 1, 24⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 2⟩) (by decide) node_543

theorem node_792 : Outcome ⟨2, 6, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 0, 2⟩) (by decide) node_547

theorem node_793 : Outcome ⟨2, 6, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_794 : Outcome ⟨2, 6, 0, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_795 : Outcome ⟨2, 6, 0, 22⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_796 : Outcome ⟨3, 0, 5, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_797 : Outcome ⟨3, 0, 5, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_798 : Outcome ⟨3, 0, 5, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_799 : Outcome ⟨3, 0, 5, 22⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_800 : Outcome ⟨3, 1, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 2⟩) (by decide) node_556

theorem node_801 : Outcome ⟨3, 1, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 2⟩) (by decide) node_556

theorem node_802 : Outcome ⟨3, 1, 4, 24⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 2⟩) (by decide) node_556

theorem node_803 : Outcome ⟨3, 2, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_804 : Outcome ⟨3, 2, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_805 : Outcome ⟨3, 2, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_806 : Outcome ⟨3, 2, 3, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_807 : Outcome ⟨3, 2, 3, 22⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_808 : Outcome ⟨3, 3, 2, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_809 : Outcome ⟨3, 3, 2, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_810 : Outcome ⟨3, 3, 2, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_811 : Outcome ⟨3, 3, 2, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_812 : Outcome ⟨3, 3, 2, 22⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

end RQ9F1
