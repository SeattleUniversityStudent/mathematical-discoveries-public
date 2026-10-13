import Chunk62
set_option autoImplicit false
namespace RQ9F1

theorem node_14426 : Outcome ⟨8, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 6⟩) (by decide) node_11524

theorem node_14427 : Outcome ⟨8, 8, 11, 14⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 22⟩) (by decide) node_4441

theorem node_14428 : Outcome ⟨8, 9, 10, 4⟩ true :=
  Outcome.win (q := ⟨6, 9, 10, 4⟩) (by decide) node_12378

theorem node_14429 : Outcome ⟨8, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 9, 4⟩) (by decide) node_12382

theorem node_14430 : Outcome ⟨8, 11, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 2⟩) (by decide) node_13396

theorem node_14431 : Outcome ⟨8, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 6⟩) (by decide) node_11524

theorem node_14432 : Outcome ⟨8, 11, 8, 14⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 22⟩) (by decide) node_4400

theorem node_14433 : Outcome ⟨8, 12, 7, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 2⟩) (by decide) node_13401

theorem node_14434 : Outcome ⟨8, 12, 7, 8⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 12⟩) (by decide) node_8534

theorem node_14435 : Outcome ⟨8, 12, 7, 14⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 12⟩) (by decide) node_8534

theorem node_14436 : Outcome ⟨8, 12, 7, 16⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 12⟩) (by decide) node_8534

theorem node_14437 : Outcome ⟨8, 13, 6, 2⟩ true :=
  Outcome.win (q := ⟨7, 13, 6, 2⟩) (by decide) node_13407

theorem node_14438 : Outcome ⟨8, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨7, 13, 6, 2⟩) (by decide) node_13407

theorem node_14439 : Outcome ⟨8, 13, 6, 12⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 12⟩) (by decide) node_8546

theorem node_14440 : Outcome ⟨8, 14, 5, 2⟩ true :=
  Outcome.win (q := ⟨8, 13, 5, 2⟩) (by decide) node_13470

theorem node_14441 : Outcome ⟨8, 15, 4, 2⟩ true :=
  Outcome.win (q := ⟨6, 15, 4, 4⟩) (by decide) node_12401

theorem node_14442 : Outcome ⟨8, 15, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 4, 4⟩) (by decide) node_12401

theorem node_14443 : Outcome ⟨8, 16, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.nil))))))

theorem node_14444 : Outcome ⟨8, 16, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨5, 16, 3, 6⟩, ⟨4, 16, 3, 8⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 13, 3, 6⟩, ⟨8, 12, 3, 8⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 16, 0, 6⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_11353 (AllWinning.cons node_10232 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_11542 (AllWinning.cons node_10540 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.cons node_11551 (AllWinning.nil)))))))))))

theorem node_14445 : Outcome ⟨8, 16, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨5, 16, 3, 6⟩, ⟨4, 16, 3, 8⟩, ⟨3, 16, 3, 10⟩, ⟨2, 16, 3, 12⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 13, 3, 6⟩, ⟨8, 12, 3, 8⟩, ⟨8, 11, 3, 10⟩, ⟨8, 10, 3, 12⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 16, 0, 6⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_11353 (AllWinning.cons node_10232 (AllWinning.cons node_9185 (AllWinning.cons node_8134 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_11542 (AllWinning.cons node_10540 (AllWinning.cons node_9505 (AllWinning.cons node_8564 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.cons node_11551 (AllWinning.nil)))))))))))))))

theorem node_14446 : Outcome ⟨8, 16, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨5, 16, 3, 6⟩, ⟨4, 16, 3, 8⟩, ⟨3, 16, 3, 10⟩, ⟨2, 16, 3, 12⟩, ⟨1, 16, 3, 14⟩, ⟨0, 16, 3, 16⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 13, 3, 6⟩, ⟨8, 12, 3, 8⟩, ⟨8, 11, 3, 10⟩, ⟨8, 10, 3, 12⟩, ⟨8, 9, 3, 14⟩, ⟨8, 8, 3, 16⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 16, 0, 6⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_11353 (AllWinning.cons node_10232 (AllWinning.cons node_9185 (AllWinning.cons node_8134 (AllWinning.cons node_7097 (AllWinning.cons node_6106 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_11542 (AllWinning.cons node_10540 (AllWinning.cons node_9505 (AllWinning.cons node_8564 (AllWinning.cons node_7575 (AllWinning.cons node_6652 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.cons node_11551 (AllWinning.nil)))))))))))))))))))

theorem node_14447 : Outcome ⟨8, 16, 3, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨5, 16, 3, 6⟩, ⟨4, 16, 3, 8⟩, ⟨3, 16, 3, 10⟩, ⟨2, 16, 3, 12⟩, ⟨1, 16, 3, 14⟩, ⟨0, 16, 3, 16⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 13, 3, 6⟩, ⟨8, 12, 3, 8⟩, ⟨8, 11, 3, 10⟩, ⟨8, 10, 3, 12⟩, ⟨8, 9, 3, 14⟩, ⟨8, 8, 3, 16⟩, ⟨8, 7, 3, 18⟩, ⟨8, 6, 3, 20⟩, ⟨8, 5, 3, 22⟩, ⟨8, 4, 3, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 2, 3, 28⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 16, 0, 6⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_11353 (AllWinning.cons node_10232 (AllWinning.cons node_9185 (AllWinning.cons node_8134 (AllWinning.cons node_7097 (AllWinning.cons node_6106 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_11542 (AllWinning.cons node_10540 (AllWinning.cons node_9505 (AllWinning.cons node_8564 (AllWinning.cons node_7575 (AllWinning.cons node_6652 (AllWinning.cons node_5807 (AllWinning.cons node_5103 (AllWinning.cons node_4421 (AllWinning.cons node_3776 (AllWinning.cons node_3227 (AllWinning.cons node_2734 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.cons node_11551 (AllWinning.nil)))))))))))))))))))))))))

theorem node_14448 : Outcome ⟨8, 16, 3, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨5, 16, 3, 6⟩, ⟨4, 16, 3, 8⟩, ⟨3, 16, 3, 10⟩, ⟨2, 16, 3, 12⟩, ⟨1, 16, 3, 14⟩, ⟨0, 16, 3, 16⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 13, 3, 6⟩, ⟨8, 12, 3, 8⟩, ⟨8, 11, 3, 10⟩, ⟨8, 10, 3, 12⟩, ⟨8, 9, 3, 14⟩, ⟨8, 8, 3, 16⟩, ⟨8, 7, 3, 18⟩, ⟨8, 6, 3, 20⟩, ⟨8, 5, 3, 22⟩, ⟨8, 4, 3, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 2, 3, 28⟩, ⟨8, 1, 3, 30⟩, ⟨8, 0, 3, 32⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 16, 0, 6⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_11353 (AllWinning.cons node_10232 (AllWinning.cons node_9185 (AllWinning.cons node_8134 (AllWinning.cons node_7097 (AllWinning.cons node_6106 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_11542 (AllWinning.cons node_10540 (AllWinning.cons node_9505 (AllWinning.cons node_8564 (AllWinning.cons node_7575 (AllWinning.cons node_6652 (AllWinning.cons node_5807 (AllWinning.cons node_5103 (AllWinning.cons node_4421 (AllWinning.cons node_3776 (AllWinning.cons node_3227 (AllWinning.cons node_2734 (AllWinning.cons node_2300 (AllWinning.cons node_1821 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.cons node_11551 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14449 : Outcome ⟨8, 16, 3, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨5, 16, 3, 6⟩, ⟨4, 16, 3, 8⟩, ⟨3, 16, 3, 10⟩, ⟨2, 16, 3, 12⟩, ⟨1, 16, 3, 14⟩, ⟨0, 16, 3, 16⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 13, 3, 6⟩, ⟨8, 12, 3, 8⟩, ⟨8, 11, 3, 10⟩, ⟨8, 10, 3, 12⟩, ⟨8, 9, 3, 14⟩, ⟨8, 8, 3, 16⟩, ⟨8, 7, 3, 18⟩, ⟨8, 6, 3, 20⟩, ⟨8, 5, 3, 22⟩, ⟨8, 4, 3, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 2, 3, 28⟩, ⟨8, 1, 3, 30⟩, ⟨8, 0, 3, 32⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 16, 0, 6⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_11353 (AllWinning.cons node_10232 (AllWinning.cons node_9185 (AllWinning.cons node_8134 (AllWinning.cons node_7097 (AllWinning.cons node_6106 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_11542 (AllWinning.cons node_10540 (AllWinning.cons node_9505 (AllWinning.cons node_8564 (AllWinning.cons node_7575 (AllWinning.cons node_6652 (AllWinning.cons node_5807 (AllWinning.cons node_5103 (AllWinning.cons node_4421 (AllWinning.cons node_3776 (AllWinning.cons node_3227 (AllWinning.cons node_2734 (AllWinning.cons node_2300 (AllWinning.cons node_1821 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.cons node_11551 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14450 : Outcome ⟨8, 16, 3, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨5, 16, 3, 6⟩, ⟨4, 16, 3, 8⟩, ⟨3, 16, 3, 10⟩, ⟨2, 16, 3, 12⟩, ⟨1, 16, 3, 14⟩, ⟨0, 16, 3, 16⟩, ⟨8, 15, 3, 2⟩, ⟨8, 14, 3, 4⟩, ⟨8, 13, 3, 6⟩, ⟨8, 12, 3, 8⟩, ⟨8, 11, 3, 10⟩, ⟨8, 10, 3, 12⟩, ⟨8, 9, 3, 14⟩, ⟨8, 8, 3, 16⟩, ⟨8, 7, 3, 18⟩, ⟨8, 6, 3, 20⟩, ⟨8, 5, 3, 22⟩, ⟨8, 4, 3, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 2, 3, 28⟩, ⟨8, 1, 3, 30⟩, ⟨8, 0, 3, 32⟩, ⟨8, 16, 2, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 16, 0, 6⟩]
  exact AllWinning.cons node_13415 (AllWinning.cons node_12403 (AllWinning.cons node_11353 (AllWinning.cons node_10232 (AllWinning.cons node_9185 (AllWinning.cons node_8134 (AllWinning.cons node_7097 (AllWinning.cons node_6106 (AllWinning.cons node_13475 (AllWinning.cons node_12533 (AllWinning.cons node_11542 (AllWinning.cons node_10540 (AllWinning.cons node_9505 (AllWinning.cons node_8564 (AllWinning.cons node_7575 (AllWinning.cons node_6652 (AllWinning.cons node_5807 (AllWinning.cons node_5103 (AllWinning.cons node_4421 (AllWinning.cons node_3776 (AllWinning.cons node_3227 (AllWinning.cons node_2734 (AllWinning.cons node_2300 (AllWinning.cons node_1821 (AllWinning.cons node_13479 (AllWinning.cons node_12539 (AllWinning.cons node_11551 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14451 : Outcome ⟨8, 17, 2, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 2, 4⟩) (by decide) node_12407

theorem node_14452 : Outcome ⟨8, 17, 2, 6⟩ true :=
  Outcome.win (q := ⟨6, 17, 2, 4⟩) (by decide) node_12407

theorem node_14453 : Outcome ⟨8, 18, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 18, 1, 2⟩, ⟨6, 18, 1, 4⟩, ⟨8, 17, 1, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 18, 0, 2⟩]
  exact AllWinning.cons node_13421 (AllWinning.cons node_12411 (AllWinning.cons node_13482 (AllWinning.cons node_12539 (AllWinning.cons node_13485 (AllWinning.nil)))))

theorem node_14454 : Outcome ⟨8, 18, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 18, 1, 2⟩, ⟨6, 18, 1, 4⟩, ⟨5, 18, 1, 6⟩, ⟨4, 18, 1, 8⟩, ⟨8, 17, 1, 2⟩, ⟨8, 16, 1, 4⟩, ⟨8, 15, 1, 6⟩, ⟨8, 14, 1, 8⟩, ⟨8, 18, 0, 2⟩]
  exact AllWinning.cons node_13421 (AllWinning.cons node_12411 (AllWinning.cons node_11358 (AllWinning.cons node_10242 (AllWinning.cons node_13482 (AllWinning.cons node_12539 (AllWinning.cons node_11546 (AllWinning.cons node_10547 (AllWinning.cons node_13485 (AllWinning.nil)))))))))

theorem node_14455 : Outcome ⟨8, 18, 1, 14⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 12⟩) (by decide) node_8574

theorem node_14456 : Outcome ⟨8, 19, 0, 4⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 4⟩) (by decide) node_12414

theorem node_14457 : Outcome ⟨8, 19, 0, 6⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 4⟩) (by decide) node_12414

theorem node_14458 : Outcome ⟨8, 19, 0, 22⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 22⟩) (by decide) node_4441

theorem node_14459 : Outcome ⟨9, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 17, 2⟩) (by decide) node_13488

theorem node_14460 : Outcome ⟨9, 0, 18, 8⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 8⟩) (by decide) node_10249

theorem node_14461 : Outcome ⟨9, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 4⟩) (by decide) node_12423

theorem node_14462 : Outcome ⟨9, 1, 17, 4⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 4⟩) (by decide) node_12423

theorem node_14463 : Outcome ⟨9, 1, 17, 8⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 4⟩) (by decide) node_12423

theorem node_14464 : Outcome ⟨9, 1, 17, 10⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 4⟩) (by decide) node_12423

theorem node_14465 : Outcome ⟨9, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 16, 2⟩) (by decide) node_13493

theorem node_14466 : Outcome ⟨9, 2, 16, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 16, 2⟩) (by decide) node_13493

theorem node_14467 : Outcome ⟨9, 2, 16, 8⟩ true :=
  Outcome.win (q := ⟨9, 1, 16, 2⟩) (by decide) node_13493

theorem node_14468 : Outcome ⟨9, 3, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 6⟩) (by decide) node_11563

theorem node_14469 : Outcome ⟨9, 3, 15, 6⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 6⟩) (by decide) node_11563

theorem node_14470 : Outcome ⟨9, 3, 15, 12⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 6⟩) (by decide) node_11563

theorem node_14471 : Outcome ⟨9, 3, 15, 18⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 6⟩) (by decide) node_11563

theorem node_14472 : Outcome ⟨9, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 4⟩) (by decide) node_12438

theorem node_14473 : Outcome ⟨9, 4, 14, 4⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 4⟩) (by decide) node_12438

theorem node_14474 : Outcome ⟨9, 4, 14, 20⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 4⟩) (by decide) node_12438

theorem node_14475 : Outcome ⟨9, 5, 13, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 13, 2⟩) (by decide) node_13443

theorem node_14476 : Outcome ⟨9, 5, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 8⟩) (by decide) node_10271

theorem node_14477 : Outcome ⟨9, 5, 13, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 8⟩) (by decide) node_10271

theorem node_14478 : Outcome ⟨9, 6, 12, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 6⟩) (by decide) node_11383

theorem node_14479 : Outcome ⟨9, 6, 12, 10⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 6⟩) (by decide) node_11383

theorem node_14480 : Outcome ⟨9, 6, 12, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 6⟩) (by decide) node_11383

theorem node_14481 : Outcome ⟨9, 7, 11, 4⟩ true :=
  Outcome.win (q := ⟨8, 7, 11, 2⟩) (by decide) node_13448

theorem node_14482 : Outcome ⟨9, 7, 11, 8⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 16⟩) (by decide) node_6144

theorem node_14483 : Outcome ⟨9, 7, 11, 14⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 16⟩) (by decide) node_6144

theorem node_14484 : Outcome ⟨9, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨9, 6, 10, 4⟩) (by decide) node_12562

theorem node_14485 : Outcome ⟨9, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨8, 9, 9, 2⟩) (by decide) node_13456

theorem node_14486 : Outcome ⟨9, 9, 9, 12⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 18⟩) (by decide) node_5352

theorem node_14487 : Outcome ⟨9, 9, 9, 22⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 18⟩) (by decide) node_5352

theorem node_14488 : Outcome ⟨9, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨9, 10, 6, 4⟩) (by decide) node_12573

theorem node_14489 : Outcome ⟨9, 11, 7, 4⟩ true :=
  Outcome.win (q := ⟨8, 11, 7, 2⟩) (by decide) node_13462

theorem node_14490 : Outcome ⟨9, 11, 7, 8⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 16⟩) (by decide) node_6169

theorem node_14491 : Outcome ⟨9, 11, 7, 14⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 16⟩) (by decide) node_6169

theorem node_14492 : Outcome ⟨9, 12, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 6⟩) (by decide) node_11408

theorem node_14493 : Outcome ⟨9, 12, 6, 10⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 6⟩) (by decide) node_11408

theorem node_14494 : Outcome ⟨9, 12, 6, 14⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 6⟩) (by decide) node_11408

theorem node_14495 : Outcome ⟨9, 13, 5, 2⟩ true :=
  Outcome.win (q := ⟨8, 13, 5, 2⟩) (by decide) node_13470

theorem node_14496 : Outcome ⟨9, 13, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 8⟩) (by decide) node_10311

theorem node_14497 : Outcome ⟨9, 13, 5, 8⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 8⟩) (by decide) node_10311

theorem node_14498 : Outcome ⟨9, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 4⟩) (by decide) node_12467

theorem node_14499 : Outcome ⟨9, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 4⟩) (by decide) node_12467

theorem node_14500 : Outcome ⟨9, 14, 4, 20⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 4⟩) (by decide) node_12467

theorem node_14501 : Outcome ⟨9, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 6⟩) (by decide) node_11596

theorem node_14502 : Outcome ⟨9, 15, 3, 6⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 6⟩) (by decide) node_11596

theorem node_14503 : Outcome ⟨9, 15, 3, 12⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 6⟩) (by decide) node_11596

theorem node_14504 : Outcome ⟨9, 15, 3, 18⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 6⟩) (by decide) node_11596

theorem node_14505 : Outcome ⟨9, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 2⟩) (by decide) node_13532

theorem node_14506 : Outcome ⟨9, 16, 2, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 2⟩) (by decide) node_13532

theorem node_14507 : Outcome ⟨9, 16, 2, 8⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 2⟩) (by decide) node_13532

theorem node_14508 : Outcome ⟨9, 17, 1, 4⟩ true :=
  Outcome.win (q := ⟨7, 17, 1, 4⟩) (by decide) node_12481

theorem node_14509 : Outcome ⟨9, 17, 1, 8⟩ true :=
  Outcome.win (q := ⟨7, 17, 1, 4⟩) (by decide) node_12481

theorem node_14510 : Outcome ⟨9, 17, 1, 10⟩ true :=
  Outcome.win (q := ⟨7, 17, 1, 4⟩) (by decide) node_12481

theorem node_14511 : Outcome ⟨9, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨9, 17, 0, 2⟩) (by decide) node_13541

theorem node_14512 : Outcome ⟨9, 18, 0, 8⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 8⟩) (by decide) node_10332

theorem node_14513 : Outcome ⟨10, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 15, 4⟩) (by decide) node_12593

theorem node_14514 : Outcome ⟨10, 0, 17, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 15, 4⟩) (by decide) node_12593

theorem node_14515 : Outcome ⟨10, 0, 17, 14⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 14⟩) (by decide) node_7635

theorem node_14516 : Outcome ⟨10, 0, 17, 20⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 14⟩) (by decide) node_7635

theorem node_14517 : Outcome ⟨10, 1, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 4⟩) (by decide) node_12597

theorem node_14518 : Outcome ⟨10, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 8⟩) (by decide) node_10342

theorem node_14519 : Outcome ⟨10, 1, 16, 8⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 8⟩) (by decide) node_10342

theorem node_14520 : Outcome ⟨10, 1, 16, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 8⟩) (by decide) node_10342

theorem node_14521 : Outcome ⟨10, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 15, 4⟩) (by decide) node_12593

theorem node_14522 : Outcome ⟨10, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 4⟩) (by decide) node_12597

theorem node_14523 : Outcome ⟨10, 3, 14, 8⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 8⟩) (by decide) node_10353

theorem node_14524 : Outcome ⟨10, 3, 14, 14⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 8⟩) (by decide) node_10353

theorem node_14525 : Outcome ⟨10, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨10, 4, 11, 4⟩) (by decide) node_12610

theorem node_14526 : Outcome ⟨10, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 11, 4⟩) (by decide) node_12610

theorem node_14527 : Outcome ⟨10, 4, 13, 12⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 14⟩) (by decide) node_7657

theorem node_14528 : Outcome ⟨10, 5, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 5, 12, 2⟩, ⟨8, 5, 12, 4⟩, ⟨10, 4, 12, 2⟩, ⟨10, 3, 12, 4⟩, ⟨10, 5, 11, 2⟩, ⟨10, 5, 10, 4⟩]
  exact AllWinning.cons node_13506 (AllWinning.cons node_12502 (AllWinning.cons node_13561 (AllWinning.cons node_12608 (AllWinning.cons node_13564 (AllWinning.cons node_12612 (AllWinning.nil))))))

theorem node_14529 : Outcome ⟨10, 5, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 5, 12, 2⟩, ⟨8, 5, 12, 4⟩, ⟨7, 5, 12, 6⟩, ⟨6, 5, 12, 8⟩, ⟨10, 4, 12, 2⟩, ⟨10, 3, 12, 4⟩, ⟨10, 2, 12, 6⟩, ⟨10, 1, 12, 8⟩, ⟨10, 5, 11, 2⟩, ⟨10, 5, 10, 4⟩, ⟨10, 5, 9, 6⟩, ⟨10, 5, 8, 8⟩]
  exact AllWinning.cons node_13506 (AllWinning.cons node_12502 (AllWinning.cons node_11449 (AllWinning.cons node_10361 (AllWinning.cons node_13561 (AllWinning.cons node_12608 (AllWinning.cons node_11616 (AllWinning.cons node_10606 (AllWinning.cons node_13564 (AllWinning.cons node_12612 (AllWinning.cons node_11625 (AllWinning.cons node_10621 (AllWinning.nil))))))))))))

theorem node_14530 : Outcome ⟨10, 5, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 5, 12, 2⟩, ⟨8, 5, 12, 4⟩, ⟨7, 5, 12, 6⟩, ⟨6, 5, 12, 8⟩, ⟨5, 5, 12, 10⟩, ⟨4, 5, 12, 12⟩, ⟨10, 4, 12, 2⟩, ⟨10, 3, 12, 4⟩, ⟨10, 2, 12, 6⟩, ⟨10, 1, 12, 8⟩, ⟨10, 0, 12, 10⟩, ⟨10, 5, 11, 2⟩, ⟨10, 5, 10, 4⟩, ⟨10, 5, 9, 6⟩, ⟨10, 5, 8, 8⟩, ⟨10, 5, 7, 10⟩, ⟨10, 5, 6, 12⟩]
  exact AllWinning.cons node_13506 (AllWinning.cons node_12502 (AllWinning.cons node_11449 (AllWinning.cons node_10361 (AllWinning.cons node_9289 (AllWinning.cons node_8241 (AllWinning.cons node_13561 (AllWinning.cons node_12608 (AllWinning.cons node_11616 (AllWinning.cons node_10606 (AllWinning.cons node_9563 (AllWinning.cons node_13564 (AllWinning.cons node_12612 (AllWinning.cons node_11625 (AllWinning.cons node_10621 (AllWinning.cons node_9581 (AllWinning.cons node_8647 (AllWinning.nil)))))))))))))))))

theorem node_14531 : Outcome ⟨10, 5, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 5, 12, 2⟩, ⟨8, 5, 12, 4⟩, ⟨7, 5, 12, 6⟩, ⟨6, 5, 12, 8⟩, ⟨5, 5, 12, 10⟩, ⟨4, 5, 12, 12⟩, ⟨3, 5, 12, 14⟩, ⟨2, 5, 12, 16⟩, ⟨10, 4, 12, 2⟩, ⟨10, 3, 12, 4⟩, ⟨10, 2, 12, 6⟩, ⟨10, 1, 12, 8⟩, ⟨10, 0, 12, 10⟩, ⟨10, 5, 11, 2⟩, ⟨10, 5, 10, 4⟩, ⟨10, 5, 9, 6⟩, ⟨10, 5, 8, 8⟩, ⟨10, 5, 7, 10⟩, ⟨10, 5, 6, 12⟩, ⟨10, 5, 5, 14⟩, ⟨10, 5, 4, 16⟩]
  exact AllWinning.cons node_13506 (AllWinning.cons node_12502 (AllWinning.cons node_11449 (AllWinning.cons node_10361 (AllWinning.cons node_9289 (AllWinning.cons node_8241 (AllWinning.cons node_7219 (AllWinning.cons node_6215 (AllWinning.cons node_13561 (AllWinning.cons node_12608 (AllWinning.cons node_11616 (AllWinning.cons node_10606 (AllWinning.cons node_9563 (AllWinning.cons node_13564 (AllWinning.cons node_12612 (AllWinning.cons node_11625 (AllWinning.cons node_10621 (AllWinning.cons node_9581 (AllWinning.cons node_8647 (AllWinning.cons node_7664 (AllWinning.cons node_6721 (AllWinning.nil)))))))))))))))))))))

theorem node_14532 : Outcome ⟨10, 5, 12, 14⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 20⟩) (by decide) node_5180

theorem node_14533 : Outcome ⟨10, 5, 12, 16⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 20⟩) (by decide) node_5180

theorem node_14534 : Outcome ⟨10, 6, 11, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 11, 4⟩) (by decide) node_12610

theorem node_14535 : Outcome ⟨10, 6, 11, 10⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 16⟩) (by decide) node_6224

theorem node_14536 : Outcome ⟨10, 6, 11, 14⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 16⟩) (by decide) node_6224

theorem node_14537 : Outcome ⟨10, 7, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 7, 10, 2⟩, ⟨8, 7, 10, 4⟩, ⟨10, 6, 10, 2⟩, ⟨10, 5, 10, 4⟩, ⟨10, 7, 9, 2⟩, ⟨10, 7, 8, 4⟩]
  exact AllWinning.cons node_13512 (AllWinning.cons node_12510 (AllWinning.cons node_13567 (AllWinning.cons node_12612 (AllWinning.cons node_13570 (AllWinning.cons node_12620 (AllWinning.nil))))))

theorem node_14538 : Outcome ⟨10, 7, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 7, 10, 2⟩, ⟨8, 7, 10, 4⟩, ⟨7, 7, 10, 6⟩, ⟨6, 7, 10, 8⟩, ⟨10, 6, 10, 2⟩, ⟨10, 5, 10, 4⟩, ⟨10, 4, 10, 6⟩, ⟨10, 3, 10, 8⟩, ⟨10, 7, 9, 2⟩, ⟨10, 7, 8, 4⟩, ⟨10, 7, 7, 6⟩, ⟨10, 7, 6, 8⟩]
  exact AllWinning.cons node_13512 (AllWinning.cons node_12510 (AllWinning.cons node_11458 (AllWinning.cons node_10369 (AllWinning.cons node_13567 (AllWinning.cons node_12612 (AllWinning.cons node_11623 (AllWinning.cons node_10615 (AllWinning.cons node_13570 (AllWinning.cons node_12620 (AllWinning.cons node_11634 (AllWinning.cons node_10634 (AllWinning.nil))))))))))))

theorem node_14539 : Outcome ⟨10, 7, 10, 8⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 14⟩) (by decide) node_7635

theorem node_14540 : Outcome ⟨10, 7, 10, 12⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 14⟩) (by decide) node_7635

theorem node_14541 : Outcome ⟨10, 7, 10, 20⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 14⟩) (by decide) node_7635

theorem node_14542 : Outcome ⟨10, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 9, 4⟩) (by decide) node_12616

theorem node_14543 : Outcome ⟨10, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨10, 9, 6, 4⟩) (by decide) node_12626

theorem node_14544 : Outcome ⟨10, 10, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 10, 7, 2⟩, ⟨8, 10, 7, 4⟩, ⟨10, 9, 7, 2⟩, ⟨10, 8, 7, 4⟩, ⟨10, 10, 6, 2⟩, ⟨10, 10, 5, 4⟩]
  exact AllWinning.cons node_13520 (AllWinning.cons node_12520 (AllWinning.cons node_13575 (AllWinning.cons node_12623 (AllWinning.cons node_13577 (AllWinning.cons node_12629 (AllWinning.nil))))))

theorem node_14545 : Outcome ⟨10, 10, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 10, 7, 2⟩, ⟨8, 10, 7, 4⟩, ⟨7, 10, 7, 6⟩, ⟨6, 10, 7, 8⟩, ⟨10, 9, 7, 2⟩, ⟨10, 8, 7, 4⟩, ⟨10, 7, 7, 6⟩, ⟨10, 6, 7, 8⟩, ⟨10, 10, 6, 2⟩, ⟨10, 10, 5, 4⟩, ⟨10, 10, 4, 6⟩, ⟨10, 10, 3, 8⟩]
  exact AllWinning.cons node_13520 (AllWinning.cons node_12520 (AllWinning.cons node_11468 (AllWinning.cons node_10383 (AllWinning.cons node_13575 (AllWinning.cons node_12623 (AllWinning.cons node_11634 (AllWinning.cons node_10628 (AllWinning.cons node_13577 (AllWinning.cons node_12629 (AllWinning.cons node_11644 (AllWinning.cons node_10648 (AllWinning.nil))))))))))))

theorem node_14546 : Outcome ⟨10, 10, 7, 8⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 14⟩) (by decide) node_7694

theorem node_14547 : Outcome ⟨10, 10, 7, 12⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 14⟩) (by decide) node_7694

theorem node_14548 : Outcome ⟨10, 10, 7, 20⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 14⟩) (by decide) node_7694

theorem node_14549 : Outcome ⟨10, 11, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 9, 6, 4⟩) (by decide) node_12626

theorem node_14550 : Outcome ⟨10, 11, 6, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 16⟩) (by decide) node_6248

theorem node_14551 : Outcome ⟨10, 11, 6, 14⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 16⟩) (by decide) node_6248

theorem node_14552 : Outcome ⟨10, 12, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 12, 5, 2⟩, ⟨8, 12, 5, 4⟩, ⟨10, 11, 5, 2⟩, ⟨10, 10, 5, 4⟩, ⟨10, 12, 4, 2⟩, ⟨10, 12, 3, 4⟩]
  exact AllWinning.cons node_13525 (AllWinning.cons node_12528 (AllWinning.cons node_13580 (AllWinning.cons node_12629 (AllWinning.cons node_13583 (AllWinning.cons node_12636 (AllWinning.nil))))))

theorem node_14553 : Outcome ⟨10, 12, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 12, 5, 2⟩, ⟨8, 12, 5, 4⟩, ⟨7, 12, 5, 6⟩, ⟨6, 12, 5, 8⟩, ⟨10, 11, 5, 2⟩, ⟨10, 10, 5, 4⟩, ⟨10, 9, 5, 6⟩, ⟨10, 8, 5, 8⟩, ⟨10, 12, 4, 2⟩, ⟨10, 12, 3, 4⟩, ⟨10, 12, 2, 6⟩, ⟨10, 12, 1, 8⟩]
  exact AllWinning.cons node_13525 (AllWinning.cons node_12528 (AllWinning.cons node_11474 (AllWinning.cons node_10389 (AllWinning.cons node_13580 (AllWinning.cons node_12629 (AllWinning.cons node_11640 (AllWinning.cons node_10639 (AllWinning.cons node_13583 (AllWinning.cons node_12636 (AllWinning.cons node_11650 (AllWinning.cons node_10657 (AllWinning.nil))))))))))))

theorem node_14554 : Outcome ⟨10, 12, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 12, 5, 2⟩, ⟨8, 12, 5, 4⟩, ⟨7, 12, 5, 6⟩, ⟨6, 12, 5, 8⟩, ⟨5, 12, 5, 10⟩, ⟨4, 12, 5, 12⟩, ⟨10, 11, 5, 2⟩, ⟨10, 10, 5, 4⟩, ⟨10, 9, 5, 6⟩, ⟨10, 8, 5, 8⟩, ⟨10, 7, 5, 10⟩, ⟨10, 6, 5, 12⟩, ⟨10, 12, 4, 2⟩, ⟨10, 12, 3, 4⟩, ⟨10, 12, 2, 6⟩, ⟨10, 12, 1, 8⟩, ⟨10, 12, 0, 10⟩]
  exact AllWinning.cons node_13525 (AllWinning.cons node_12528 (AllWinning.cons node_11474 (AllWinning.cons node_10389 (AllWinning.cons node_9317 (AllWinning.cons node_8265 (AllWinning.cons node_13580 (AllWinning.cons node_12629 (AllWinning.cons node_11640 (AllWinning.cons node_10639 (AllWinning.cons node_9589 (AllWinning.cons node_8651 (AllWinning.cons node_13583 (AllWinning.cons node_12636 (AllWinning.cons node_11650 (AllWinning.cons node_10657 (AllWinning.cons node_9608 (AllWinning.nil)))))))))))))))))

theorem node_14555 : Outcome ⟨10, 12, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 12, 5, 2⟩, ⟨8, 12, 5, 4⟩, ⟨7, 12, 5, 6⟩, ⟨6, 12, 5, 8⟩, ⟨5, 12, 5, 10⟩, ⟨4, 12, 5, 12⟩, ⟨3, 12, 5, 14⟩, ⟨2, 12, 5, 16⟩, ⟨10, 11, 5, 2⟩, ⟨10, 10, 5, 4⟩, ⟨10, 9, 5, 6⟩, ⟨10, 8, 5, 8⟩, ⟨10, 7, 5, 10⟩, ⟨10, 6, 5, 12⟩, ⟨10, 5, 5, 14⟩, ⟨10, 4, 5, 16⟩, ⟨10, 12, 4, 2⟩, ⟨10, 12, 3, 4⟩, ⟨10, 12, 2, 6⟩, ⟨10, 12, 1, 8⟩, ⟨10, 12, 0, 10⟩]
  exact AllWinning.cons node_13525 (AllWinning.cons node_12528 (AllWinning.cons node_11474 (AllWinning.cons node_10389 (AllWinning.cons node_9317 (AllWinning.cons node_8265 (AllWinning.cons node_7248 (AllWinning.cons node_6253 (AllWinning.cons node_13580 (AllWinning.cons node_12629 (AllWinning.cons node_11640 (AllWinning.cons node_10639 (AllWinning.cons node_9589 (AllWinning.cons node_8651 (AllWinning.cons node_7664 (AllWinning.cons node_6717 (AllWinning.cons node_13583 (AllWinning.cons node_12636 (AllWinning.cons node_11650 (AllWinning.cons node_10657 (AllWinning.cons node_9608 (AllWinning.nil)))))))))))))))))))))

theorem node_14556 : Outcome ⟨10, 12, 5, 14⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 20⟩) (by decide) node_5161

theorem node_14557 : Outcome ⟨10, 12, 5, 16⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 20⟩) (by decide) node_5161

theorem node_14558 : Outcome ⟨10, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 11, 4, 4⟩) (by decide) node_12633

theorem node_14559 : Outcome ⟨10, 13, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 11, 4, 4⟩) (by decide) node_12633

theorem node_14560 : Outcome ⟨10, 13, 4, 12⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 14⟩) (by decide) node_7671

theorem node_14561 : Outcome ⟨10, 14, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 4⟩) (by decide) node_12640

theorem node_14562 : Outcome ⟨10, 14, 3, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 8⟩) (by decide) node_10399

theorem node_14563 : Outcome ⟨10, 14, 3, 14⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 8⟩) (by decide) node_10399

theorem node_14564 : Outcome ⟨10, 15, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 15, 0, 4⟩) (by decide) node_12649

theorem node_14565 : Outcome ⟨10, 16, 1, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 4⟩) (by decide) node_12640

theorem node_14566 : Outcome ⟨10, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 8⟩) (by decide) node_10408

theorem node_14567 : Outcome ⟨10, 16, 1, 8⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 8⟩) (by decide) node_10408

theorem node_14568 : Outcome ⟨10, 16, 1, 10⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 8⟩) (by decide) node_10408

theorem node_14569 : Outcome ⟨10, 17, 0, 2⟩ true :=
  Outcome.win (q := ⟨10, 15, 0, 4⟩) (by decide) node_12649

theorem node_14570 : Outcome ⟨10, 17, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 15, 0, 4⟩) (by decide) node_12649

theorem node_14571 : Outcome ⟨10, 17, 0, 14⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 14⟩) (by decide) node_7694

theorem node_14572 : Outcome ⟨10, 17, 0, 20⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 14⟩) (by decide) node_7694

theorem node_14573 : Outcome ⟨11, 0, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 16, 2⟩, ⟨9, 0, 16, 4⟩, ⟨11, 0, 15, 2⟩, ⟨11, 0, 14, 4⟩]
  exact AllWinning.cons node_13546 (AllWinning.cons node_12546 (AllWinning.cons node_13600 (AllWinning.cons node_12652 (AllWinning.nil))))

theorem node_14574 : Outcome ⟨11, 0, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 16, 2⟩, ⟨9, 0, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨7, 0, 16, 8⟩, ⟨11, 0, 15, 2⟩, ⟨11, 0, 14, 4⟩, ⟨11, 0, 13, 6⟩, ⟨11, 0, 12, 8⟩]
  exact AllWinning.cons node_13546 (AllWinning.cons node_12546 (AllWinning.cons node_11498 (AllWinning.cons node_10417 (AllWinning.cons node_13600 (AllWinning.cons node_12652 (AllWinning.cons node_11658 (AllWinning.cons node_10661 (AllWinning.nil))))))))

theorem node_14575 : Outcome ⟨11, 0, 16, 6⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 10⟩) (by decide) node_9613

theorem node_14576 : Outcome ⟨11, 0, 16, 10⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 10⟩) (by decide) node_9613

theorem node_14577 : Outcome ⟨11, 0, 16, 14⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 10⟩) (by decide) node_9613

theorem node_14578 : Outcome ⟨11, 1, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 15, 2⟩, ⟨9, 1, 15, 4⟩, ⟨11, 0, 15, 2⟩, ⟨11, 1, 14, 2⟩, ⟨11, 1, 13, 4⟩]
  exact AllWinning.cons node_13549 (AllWinning.cons node_12550 (AllWinning.cons node_13600 (AllWinning.cons node_13603 (AllWinning.cons node_12655 (AllWinning.nil)))))

theorem node_14579 : Outcome ⟨11, 1, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 15, 2⟩, ⟨9, 1, 15, 4⟩, ⟨8, 1, 15, 6⟩, ⟨7, 1, 15, 8⟩, ⟨11, 0, 15, 2⟩, ⟨11, 1, 14, 2⟩, ⟨11, 1, 13, 4⟩, ⟨11, 1, 12, 6⟩, ⟨11, 1, 11, 8⟩]
  exact AllWinning.cons node_13549 (AllWinning.cons node_12550 (AllWinning.cons node_11501 (AllWinning.cons node_10422 (AllWinning.cons node_13600 (AllWinning.cons node_13603 (AllWinning.cons node_12655 (AllWinning.cons node_11661 (AllWinning.cons node_10663 (AllWinning.nil)))))))))

theorem node_14580 : Outcome ⟨11, 1, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 15, 2⟩, ⟨9, 1, 15, 4⟩, ⟨8, 1, 15, 6⟩, ⟨7, 1, 15, 8⟩, ⟨6, 1, 15, 10⟩, ⟨5, 1, 15, 12⟩, ⟨11, 0, 15, 2⟩, ⟨11, 1, 14, 2⟩, ⟨11, 1, 13, 4⟩, ⟨11, 1, 12, 6⟩, ⟨11, 1, 11, 8⟩, ⟨11, 1, 10, 10⟩, ⟨11, 1, 9, 12⟩]
  exact AllWinning.cons node_13549 (AllWinning.cons node_12550 (AllWinning.cons node_11501 (AllWinning.cons node_10422 (AllWinning.cons node_9343 (AllWinning.cons node_8292 (AllWinning.cons node_13600 (AllWinning.cons node_13603 (AllWinning.cons node_12655 (AllWinning.cons node_11661 (AllWinning.cons node_10663 (AllWinning.cons node_9621 (AllWinning.cons node_8675 (AllWinning.nil)))))))))))))

theorem node_14581 : Outcome ⟨11, 1, 15, 10⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 16⟩) (by decide) node_6748

theorem node_14582 : Outcome ⟨11, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨11, 2, 13, 2⟩) (by decide) node_13605

theorem node_14583 : Outcome ⟨11, 2, 14, 6⟩ true :=
  Outcome.win (q := ⟨11, 2, 13, 2⟩) (by decide) node_13605

theorem node_14584 : Outcome ⟨11, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 2⟩) (by decide) node_13553

theorem node_14585 : Outcome ⟨11, 3, 13, 12⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 16⟩) (by decide) node_6767

theorem node_14586 : Outcome ⟨11, 4, 12, 4⟩ true :=
  Outcome.win (q := ⟨11, 4, 10, 4⟩) (by decide) node_12666

theorem node_14587 : Outcome ⟨11, 4, 12, 12⟩ true :=
  Outcome.win (q := ⟨11, 4, 10, 4⟩) (by decide) node_12666

theorem node_14588 : Outcome ⟨11, 5, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 5, 11, 2⟩, ⟨9, 5, 11, 4⟩, ⟨11, 4, 11, 2⟩, ⟨11, 3, 11, 4⟩, ⟨11, 5, 10, 2⟩, ⟨11, 5, 9, 4⟩]
  exact AllWinning.cons node_13564 (AllWinning.cons node_12558 (AllWinning.cons node_13614 (AllWinning.cons node_12661 (AllWinning.cons node_13617 (AllWinning.cons node_12669 (AllWinning.nil))))))

theorem node_14589 : Outcome ⟨11, 5, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 5, 11, 2⟩, ⟨9, 5, 11, 4⟩, ⟨8, 5, 11, 6⟩, ⟨7, 5, 11, 8⟩, ⟨11, 4, 11, 2⟩, ⟨11, 3, 11, 4⟩, ⟨11, 2, 11, 6⟩, ⟨11, 1, 11, 8⟩, ⟨11, 5, 10, 2⟩, ⟨11, 5, 9, 4⟩, ⟨11, 5, 8, 6⟩, ⟨11, 5, 7, 8⟩]
  exact AllWinning.cons node_13564 (AllWinning.cons node_12558 (AllWinning.cons node_11512 (AllWinning.cons node_10439 (AllWinning.cons node_13614 (AllWinning.cons node_12661 (AllWinning.cons node_11663 (AllWinning.cons node_10663 (AllWinning.cons node_13617 (AllWinning.cons node_12669 (AllWinning.cons node_11677 (AllWinning.cons node_10681 (AllWinning.nil))))))))))))

theorem node_14590 : Outcome ⟨11, 5, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 16⟩) (by decide) node_6306

theorem node_14591 : Outcome ⟨11, 6, 10, 4⟩ true :=
  Outcome.win (q := ⟨9, 6, 10, 4⟩) (by decide) node_12562

theorem node_14592 : Outcome ⟨11, 6, 10, 10⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 16⟩) (by decide) node_6792

theorem node_14593 : Outcome ⟨11, 6, 10, 14⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 16⟩) (by decide) node_6792

theorem node_14594 : Outcome ⟨11, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 8, 2⟩) (by decide) node_13623

theorem node_14595 : Outcome ⟨11, 7, 9, 8⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 16⟩) (by decide) node_6801

theorem node_14596 : Outcome ⟨11, 7, 9, 14⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 16⟩) (by decide) node_6801

theorem node_14597 : Outcome ⟨11, 8, 8, 2⟩ true :=
  Outcome.win (q := ⟨11, 7, 8, 2⟩) (by decide) node_13623

theorem node_14598 : Outcome ⟨11, 8, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 6⟩) (by decide) node_11524

theorem node_14599 : Outcome ⟨11, 8, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 22⟩) (by decide) node_3968

theorem node_14600 : Outcome ⟨11, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨11, 8, 7, 2⟩) (by decide) node_13627

theorem node_14601 : Outcome ⟨11, 9, 7, 8⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 16⟩) (by decide) node_6748

theorem node_14602 : Outcome ⟨11, 9, 7, 14⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 16⟩) (by decide) node_6748

theorem node_14603 : Outcome ⟨11, 10, 6, 4⟩ true :=
  Outcome.win (q := ⟨9, 10, 6, 4⟩) (by decide) node_12573

theorem node_14604 : Outcome ⟨11, 10, 6, 10⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 16⟩) (by decide) node_6758

theorem node_14605 : Outcome ⟨11, 10, 6, 14⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 16⟩) (by decide) node_6758

theorem node_14606 : Outcome ⟨11, 11, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 5, 2⟩, ⟨9, 11, 5, 4⟩, ⟨11, 10, 5, 2⟩, ⟨11, 9, 5, 4⟩, ⟨11, 11, 4, 2⟩, ⟨11, 11, 3, 4⟩]
  exact AllWinning.cons node_13580 (AllWinning.cons node_12576 (AllWinning.cons node_13634 (AllWinning.cons node_12682 (AllWinning.cons node_13637 (AllWinning.cons node_12689 (AllWinning.nil))))))

theorem node_14607 : Outcome ⟨11, 11, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 5, 2⟩, ⟨9, 11, 5, 4⟩, ⟨8, 11, 5, 6⟩, ⟨7, 11, 5, 8⟩, ⟨11, 10, 5, 2⟩, ⟨11, 9, 5, 4⟩, ⟨11, 8, 5, 6⟩, ⟨11, 7, 5, 8⟩, ⟨11, 11, 4, 2⟩, ⟨11, 11, 3, 4⟩, ⟨11, 11, 2, 6⟩, ⟨11, 11, 1, 8⟩]
  exact AllWinning.cons node_13580 (AllWinning.cons node_12576 (AllWinning.cons node_11535 (AllWinning.cons node_10467 (AllWinning.cons node_13634 (AllWinning.cons node_12682 (AllWinning.cons node_11689 (AllWinning.cons node_10688 (AllWinning.cons node_13637 (AllWinning.cons node_12689 (AllWinning.cons node_11702 (AllWinning.cons node_10706 (AllWinning.nil))))))))))))

theorem node_14608 : Outcome ⟨11, 11, 5, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 16⟩) (by decide) node_6337

theorem node_14609 : Outcome ⟨11, 12, 4, 4⟩ true :=
  Outcome.win (q := ⟨11, 10, 4, 4⟩) (by decide) node_12686

theorem node_14610 : Outcome ⟨11, 12, 4, 12⟩ true :=
  Outcome.win (q := ⟨11, 10, 4, 4⟩) (by decide) node_12686

theorem node_14611 : Outcome ⟨11, 13, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 2⟩) (by decide) node_13586

theorem node_14612 : Outcome ⟨11, 13, 3, 12⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 16⟩) (by decide) node_6781

theorem node_14613 : Outcome ⟨11, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨11, 13, 2, 2⟩) (by decide) node_13645

theorem node_14614 : Outcome ⟨11, 14, 2, 6⟩ true :=
  Outcome.win (q := ⟨11, 13, 2, 2⟩) (by decide) node_13645

theorem node_14615 : Outcome ⟨11, 15, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 1, 2⟩, ⟨9, 15, 1, 4⟩, ⟨11, 14, 1, 2⟩, ⟨11, 13, 1, 4⟩, ⟨11, 15, 0, 2⟩]
  exact AllWinning.cons node_13595 (AllWinning.cons node_12585 (AllWinning.cons node_13649 (AllWinning.cons node_12698 (AllWinning.cons node_13651 (AllWinning.nil)))))

theorem node_14616 : Outcome ⟨11, 15, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 1, 2⟩, ⟨9, 15, 1, 4⟩, ⟨8, 15, 1, 6⟩, ⟨7, 15, 1, 8⟩, ⟨11, 14, 1, 2⟩, ⟨11, 13, 1, 4⟩, ⟨11, 12, 1, 6⟩, ⟨11, 11, 1, 8⟩, ⟨11, 15, 0, 2⟩]
  exact AllWinning.cons node_13595 (AllWinning.cons node_12585 (AllWinning.cons node_11546 (AllWinning.cons node_10484 (AllWinning.cons node_13649 (AllWinning.cons node_12698 (AllWinning.cons node_11706 (AllWinning.cons node_10706 (AllWinning.cons node_13651 (AllWinning.nil)))))))))

theorem node_14617 : Outcome ⟨11, 15, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 1, 2⟩, ⟨9, 15, 1, 4⟩, ⟨8, 15, 1, 6⟩, ⟨7, 15, 1, 8⟩, ⟨6, 15, 1, 10⟩, ⟨5, 15, 1, 12⟩, ⟨11, 14, 1, 2⟩, ⟨11, 13, 1, 4⟩, ⟨11, 12, 1, 6⟩, ⟨11, 11, 1, 8⟩, ⟨11, 10, 1, 10⟩, ⟨11, 9, 1, 12⟩, ⟨11, 15, 0, 2⟩]
  exact AllWinning.cons node_13595 (AllWinning.cons node_12585 (AllWinning.cons node_11546 (AllWinning.cons node_10484 (AllWinning.cons node_9397 (AllWinning.cons node_8337 (AllWinning.cons node_13649 (AllWinning.cons node_12698 (AllWinning.cons node_11706 (AllWinning.cons node_10706 (AllWinning.cons node_9659 (AllWinning.cons node_8706 (AllWinning.cons node_13651 (AllWinning.nil)))))))))))))

theorem node_14618 : Outcome ⟨11, 15, 1, 10⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 16⟩) (by decide) node_6801

theorem node_14619 : Outcome ⟨11, 16, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 0, 2⟩, ⟨9, 16, 0, 4⟩, ⟨11, 15, 0, 2⟩, ⟨11, 14, 0, 4⟩]
  exact AllWinning.cons node_13597 (AllWinning.cons node_12589 (AllWinning.cons node_13651 (AllWinning.cons node_12700 (AllWinning.nil))))

theorem node_14620 : Outcome ⟨11, 16, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 0, 2⟩, ⟨9, 16, 0, 4⟩, ⟨8, 16, 0, 6⟩, ⟨7, 16, 0, 8⟩, ⟨11, 15, 0, 2⟩, ⟨11, 14, 0, 4⟩, ⟨11, 13, 0, 6⟩, ⟨11, 12, 0, 8⟩]
  exact AllWinning.cons node_13597 (AllWinning.cons node_12589 (AllWinning.cons node_11551 (AllWinning.cons node_10488 (AllWinning.cons node_13651 (AllWinning.cons node_12700 (AllWinning.cons node_11708 (AllWinning.cons node_10709 (AllWinning.nil))))))))

theorem node_14621 : Outcome ⟨11, 16, 0, 6⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 10⟩) (by decide) node_9665

theorem node_14622 : Outcome ⟨11, 16, 0, 10⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 10⟩) (by decide) node_9665

theorem node_14623 : Outcome ⟨11, 16, 0, 14⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 10⟩) (by decide) node_9665

theorem node_14624 : Outcome ⟨12, 0, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 6⟩) (by decide) node_11711

theorem node_14625 : Outcome ⟨12, 0, 15, 6⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 6⟩) (by decide) node_11711

theorem node_14626 : Outcome ⟨12, 0, 15, 14⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 6⟩) (by decide) node_11711

theorem node_14627 : Outcome ⟨12, 1, 14, 2⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 4⟩) (by decide) node_12597

theorem node_14628 : Outcome ⟨12, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 4⟩) (by decide) node_12597

theorem node_14629 : Outcome ⟨12, 1, 14, 10⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 12⟩) (by decide) node_8718

theorem node_14630 : Outcome ⟨12, 1, 14, 12⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 12⟩) (by decide) node_8718

theorem node_14631 : Outcome ⟨12, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨11, 2, 13, 2⟩) (by decide) node_13605

theorem node_14632 : Outcome ⟨12, 2, 13, 4⟩ true :=
  Outcome.win (q := ⟨11, 2, 13, 2⟩) (by decide) node_13605

theorem node_14633 : Outcome ⟨12, 3, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 3, 12, 2⟩, ⟨10, 3, 12, 4⟩, ⟨12, 2, 12, 2⟩, ⟨12, 1, 12, 4⟩, ⟨12, 3, 11, 2⟩, ⟨12, 3, 10, 4⟩]
  exact AllWinning.cons node_13609 (AllWinning.cons node_12608 (AllWinning.cons node_13661 (AllWinning.cons node_12705 (AllWinning.cons node_13663 (AllWinning.cons node_12713 (AllWinning.nil))))))

theorem node_14634 : Outcome ⟨12, 3, 12, 6⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 6⟩) (by decide) node_11563

theorem node_14635 : Outcome ⟨12, 3, 12, 8⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 6⟩) (by decide) node_11563

theorem node_14636 : Outcome ⟨12, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 11, 4⟩) (by decide) node_12610

theorem node_14637 : Outcome ⟨12, 4, 11, 12⟩ true :=
  Outcome.win (q := ⟨10, 4, 11, 4⟩) (by decide) node_12610

theorem node_14638 : Outcome ⟨12, 5, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 5, 10, 2⟩, ⟨10, 5, 10, 4⟩, ⟨12, 4, 10, 2⟩, ⟨12, 3, 10, 4⟩, ⟨12, 5, 9, 2⟩, ⟨12, 5, 8, 4⟩]
  exact AllWinning.cons node_13617 (AllWinning.cons node_12612 (AllWinning.cons node_13667 (AllWinning.cons node_12713 (AllWinning.cons node_13670 (AllWinning.cons node_12717 (AllWinning.nil))))))

theorem node_14639 : Outcome ⟨12, 5, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 5, 10, 2⟩, ⟨10, 5, 10, 4⟩, ⟨9, 5, 10, 6⟩, ⟨8, 5, 10, 8⟩, ⟨7, 5, 10, 10⟩, ⟨6, 5, 10, 12⟩, ⟨12, 4, 10, 2⟩, ⟨12, 3, 10, 4⟩, ⟨12, 2, 10, 6⟩, ⟨12, 1, 10, 8⟩, ⟨12, 0, 10, 10⟩, ⟨12, 5, 9, 2⟩, ⟨12, 5, 8, 4⟩, ⟨12, 5, 7, 6⟩, ⟨12, 5, 6, 8⟩, ⟨12, 5, 5, 10⟩, ⟨12, 5, 4, 12⟩]
  exact AllWinning.cons node_13617 (AllWinning.cons node_12612 (AllWinning.cons node_11574 (AllWinning.cons node_10509 (AllWinning.cons node_9426 (AllWinning.cons node_8362 (AllWinning.cons node_13667 (AllWinning.cons node_12713 (AllWinning.cons node_11723 (AllWinning.cons node_10714 (AllWinning.cons node_9673 (AllWinning.cons node_13670 (AllWinning.cons node_12717 (AllWinning.cons node_11738 (AllWinning.cons node_10727 (AllWinning.cons node_9689 (AllWinning.cons node_8740 (AllWinning.nil)))))))))))))))))

theorem node_14640 : Outcome ⟨12, 5, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 5, 10, 2⟩, ⟨10, 5, 10, 4⟩, ⟨9, 5, 10, 6⟩, ⟨8, 5, 10, 8⟩, ⟨7, 5, 10, 10⟩, ⟨6, 5, 10, 12⟩, ⟨5, 5, 10, 14⟩, ⟨4, 5, 10, 16⟩, ⟨12, 4, 10, 2⟩, ⟨12, 3, 10, 4⟩, ⟨12, 2, 10, 6⟩, ⟨12, 1, 10, 8⟩, ⟨12, 0, 10, 10⟩, ⟨12, 5, 9, 2⟩, ⟨12, 5, 8, 4⟩, ⟨12, 5, 7, 6⟩, ⟨12, 5, 6, 8⟩, ⟨12, 5, 5, 10⟩, ⟨12, 5, 4, 12⟩, ⟨12, 5, 3, 14⟩, ⟨12, 5, 2, 16⟩]
  exact AllWinning.cons node_13617 (AllWinning.cons node_12612 (AllWinning.cons node_11574 (AllWinning.cons node_10509 (AllWinning.cons node_9426 (AllWinning.cons node_8362 (AllWinning.cons node_7370 (AllWinning.cons node_6387 (AllWinning.cons node_13667 (AllWinning.cons node_12713 (AllWinning.cons node_11723 (AllWinning.cons node_10714 (AllWinning.cons node_9673 (AllWinning.cons node_13670 (AllWinning.cons node_12717 (AllWinning.cons node_11738 (AllWinning.cons node_10727 (AllWinning.cons node_9689 (AllWinning.cons node_8740 (AllWinning.cons node_7749 (AllWinning.cons node_6830 (AllWinning.nil)))))))))))))))))))))

theorem node_14641 : Outcome ⟨12, 5, 10, 14⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 20⟩) (by decide) node_4752

theorem node_14642 : Outcome ⟨12, 5, 10, 16⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 20⟩) (by decide) node_4752

theorem node_14643 : Outcome ⟨12, 6, 9, 4⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 6⟩) (by decide) node_11727

theorem node_14644 : Outcome ⟨12, 6, 9, 10⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 6⟩) (by decide) node_11727

theorem node_14645 : Outcome ⟨12, 6, 9, 14⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 6⟩) (by decide) node_11727

theorem node_14646 : Outcome ⟨12, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨11, 7, 8, 2⟩) (by decide) node_13623

theorem node_14647 : Outcome ⟨12, 7, 8, 8⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 12⟩) (by decide) node_8372

theorem node_14648 : Outcome ⟨12, 7, 8, 14⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 12⟩) (by decide) node_8372

theorem node_14649 : Outcome ⟨12, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨11, 8, 7, 2⟩) (by decide) node_13627

theorem node_14650 : Outcome ⟨12, 8, 7, 8⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 12⟩) (by decide) node_8384

theorem node_14651 : Outcome ⟨12, 8, 7, 14⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 12⟩) (by decide) node_8384

theorem node_14652 : Outcome ⟨12, 9, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 6, 6⟩) (by decide) node_11744

theorem node_14653 : Outcome ⟨12, 9, 6, 10⟩ true :=
  Outcome.win (q := ⟨12, 6, 6, 6⟩) (by decide) node_11744

theorem node_14654 : Outcome ⟨12, 9, 6, 14⟩ true :=
  Outcome.win (q := ⟨12, 6, 6, 6⟩) (by decide) node_11744

theorem node_14655 : Outcome ⟨12, 10, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 10, 5, 2⟩, ⟨10, 10, 5, 4⟩, ⟨12, 9, 5, 2⟩, ⟨12, 8, 5, 4⟩, ⟨12, 10, 4, 2⟩, ⟨12, 10, 3, 4⟩]
  exact AllWinning.cons node_13634 (AllWinning.cons node_12629 (AllWinning.cons node_13685 (AllWinning.cons node_12729 (AllWinning.cons node_13688 (AllWinning.cons node_12734 (AllWinning.nil))))))

theorem node_14656 : Outcome ⟨12, 10, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 10, 5, 2⟩, ⟨10, 10, 5, 4⟩, ⟨9, 10, 5, 6⟩, ⟨8, 10, 5, 8⟩, ⟨7, 10, 5, 10⟩, ⟨6, 10, 5, 12⟩, ⟨12, 9, 5, 2⟩, ⟨12, 8, 5, 4⟩, ⟨12, 7, 5, 6⟩, ⟨12, 6, 5, 8⟩, ⟨12, 5, 5, 10⟩, ⟨12, 4, 5, 12⟩, ⟨12, 10, 4, 2⟩, ⟨12, 10, 3, 4⟩, ⟨12, 10, 2, 6⟩, ⟨12, 10, 1, 8⟩, ⟨12, 10, 0, 10⟩]
  exact AllWinning.cons node_13634 (AllWinning.cons node_12629 (AllWinning.cons node_11588 (AllWinning.cons node_10531 (AllWinning.cons node_9444 (AllWinning.cons node_8398 (AllWinning.cons node_13685 (AllWinning.cons node_12729 (AllWinning.cons node_11748 (AllWinning.cons node_10731 (AllWinning.cons node_9689 (AllWinning.cons node_8736 (AllWinning.cons node_13688 (AllWinning.cons node_12734 (AllWinning.cons node_11765 (AllWinning.cons node_10747 (AllWinning.cons node_9706 (AllWinning.nil)))))))))))))))))

theorem node_14657 : Outcome ⟨12, 10, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 10, 5, 2⟩, ⟨10, 10, 5, 4⟩, ⟨9, 10, 5, 6⟩, ⟨8, 10, 5, 8⟩, ⟨7, 10, 5, 10⟩, ⟨6, 10, 5, 12⟩, ⟨5, 10, 5, 14⟩, ⟨4, 10, 5, 16⟩, ⟨12, 9, 5, 2⟩, ⟨12, 8, 5, 4⟩, ⟨12, 7, 5, 6⟩, ⟨12, 6, 5, 8⟩, ⟨12, 5, 5, 10⟩, ⟨12, 4, 5, 12⟩, ⟨12, 3, 5, 14⟩, ⟨12, 2, 5, 16⟩, ⟨12, 10, 4, 2⟩, ⟨12, 10, 3, 4⟩, ⟨12, 10, 2, 6⟩, ⟨12, 10, 1, 8⟩, ⟨12, 10, 0, 10⟩]
  exact AllWinning.cons node_13634 (AllWinning.cons node_12629 (AllWinning.cons node_11588 (AllWinning.cons node_10531 (AllWinning.cons node_9444 (AllWinning.cons node_8398 (AllWinning.cons node_7390 (AllWinning.cons node_6404 (AllWinning.cons node_13685 (AllWinning.cons node_12729 (AllWinning.cons node_11748 (AllWinning.cons node_10731 (AllWinning.cons node_9689 (AllWinning.cons node_8736 (AllWinning.cons node_7744 (AllWinning.cons node_6818 (AllWinning.cons node_13688 (AllWinning.cons node_12734 (AllWinning.cons node_11765 (AllWinning.cons node_10747 (AllWinning.cons node_9706 (AllWinning.nil)))))))))))))))))))))

theorem node_14658 : Outcome ⟨12, 10, 5, 14⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 20⟩) (by decide) node_4781

theorem node_14659 : Outcome ⟨12, 10, 5, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 20⟩) (by decide) node_4781

theorem node_14660 : Outcome ⟨12, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 11, 4, 4⟩) (by decide) node_12633

theorem node_14661 : Outcome ⟨12, 11, 4, 12⟩ true :=
  Outcome.win (q := ⟨10, 11, 4, 4⟩) (by decide) node_12633

theorem node_14662 : Outcome ⟨12, 12, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 3, 2⟩, ⟨10, 12, 3, 4⟩, ⟨12, 11, 3, 2⟩, ⟨12, 10, 3, 4⟩, ⟨12, 12, 2, 2⟩, ⟨12, 12, 1, 4⟩]
  exact AllWinning.cons node_13640 (AllWinning.cons node_12636 (AllWinning.cons node_13691 (AllWinning.cons node_12734 (AllWinning.cons node_13695 (AllWinning.cons node_12740 (AllWinning.nil))))))

theorem node_14663 : Outcome ⟨12, 12, 3, 6⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 6⟩) (by decide) node_11596

theorem node_14664 : Outcome ⟨12, 12, 3, 8⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 6⟩) (by decide) node_11596

theorem node_14665 : Outcome ⟨12, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨11, 13, 2, 2⟩) (by decide) node_13645

theorem node_14666 : Outcome ⟨12, 13, 2, 4⟩ true :=
  Outcome.win (q := ⟨11, 13, 2, 2⟩) (by decide) node_13645

theorem node_14667 : Outcome ⟨12, 14, 1, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 4⟩) (by decide) node_12640

theorem node_14668 : Outcome ⟨12, 14, 1, 4⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 4⟩) (by decide) node_12640

theorem node_14669 : Outcome ⟨12, 14, 1, 10⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 12⟩) (by decide) node_8756

theorem node_14670 : Outcome ⟨12, 14, 1, 12⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 12⟩) (by decide) node_8756

end RQ9F1
