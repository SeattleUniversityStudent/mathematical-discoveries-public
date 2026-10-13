import Chunk44
set_option autoImplicit false
namespace RQ9F1

theorem node_10547 : Outcome ⟨8, 14, 1, 8⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10548 : Outcome ⟨8, 15, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 13, 0, 4⟩) (by decide) node_8580

theorem node_10549 : Outcome ⟨8, 15, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 13, 0, 4⟩) (by decide) node_8580

theorem node_10550 : Outcome ⟨8, 15, 0, 10⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 14⟩) (by decide) node_4437

theorem node_10551 : Outcome ⟨8, 15, 0, 14⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 14⟩) (by decide) node_4437

theorem node_10552 : Outcome ⟨9, 0, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 14, 2⟩, ⟨7, 0, 14, 4⟩, ⟨9, 0, 13, 2⟩, ⟨9, 0, 12, 4⟩]
  exact AllWinning.cons node_9468 (AllWinning.cons node_8416 (AllWinning.cons node_9515 (AllWinning.cons node_8583 (AllWinning.nil))))

theorem node_10553 : Outcome ⟨9, 0, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 14, 2⟩, ⟨7, 0, 14, 4⟩, ⟨6, 0, 14, 6⟩, ⟨5, 0, 14, 8⟩, ⟨9, 0, 13, 2⟩, ⟨9, 0, 12, 4⟩, ⟨9, 0, 11, 6⟩, ⟨9, 0, 10, 8⟩]
  exact AllWinning.cons node_9468 (AllWinning.cons node_8416 (AllWinning.cons node_7411 (AllWinning.cons node_6423 (AllWinning.cons node_9515 (AllWinning.cons node_8583 (AllWinning.cons node_7586 (AllWinning.cons node_6666 (AllWinning.nil))))))))

theorem node_10554 : Outcome ⟨9, 0, 14, 6⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 10⟩) (by decide) node_5824

theorem node_10555 : Outcome ⟨9, 0, 14, 10⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 10⟩) (by decide) node_5824

theorem node_10556 : Outcome ⟨9, 1, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 13, 2⟩, ⟨7, 1, 13, 4⟩, ⟨9, 0, 13, 2⟩, ⟨9, 1, 12, 2⟩, ⟨9, 1, 11, 4⟩]
  exact AllWinning.cons node_9471 (AllWinning.cons node_8420 (AllWinning.cons node_9515 (AllWinning.cons node_9518 (AllWinning.cons node_8586 (AllWinning.nil)))))

theorem node_10557 : Outcome ⟨9, 1, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 13, 2⟩, ⟨7, 1, 13, 4⟩, ⟨6, 1, 13, 6⟩, ⟨5, 1, 13, 8⟩, ⟨9, 0, 13, 2⟩, ⟨9, 1, 12, 2⟩, ⟨9, 1, 11, 4⟩, ⟨9, 1, 10, 6⟩, ⟨9, 1, 9, 8⟩]
  exact AllWinning.cons node_9471 (AllWinning.cons node_8420 (AllWinning.cons node_7416 (AllWinning.cons node_6426 (AllWinning.cons node_9515 (AllWinning.cons node_9518 (AllWinning.cons node_8586 (AllWinning.cons node_7589 (AllWinning.cons node_6669 (AllWinning.nil)))))))))

theorem node_10558 : Outcome ⟨9, 1, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 13, 2⟩, ⟨7, 1, 13, 4⟩, ⟨6, 1, 13, 6⟩, ⟨5, 1, 13, 8⟩, ⟨4, 1, 13, 10⟩, ⟨3, 1, 13, 12⟩, ⟨9, 0, 13, 2⟩, ⟨9, 1, 12, 2⟩, ⟨9, 1, 11, 4⟩, ⟨9, 1, 10, 6⟩, ⟨9, 1, 9, 8⟩, ⟨9, 1, 8, 10⟩, ⟨9, 1, 7, 12⟩]
  exact AllWinning.cons node_9471 (AllWinning.cons node_8420 (AllWinning.cons node_7416 (AllWinning.cons node_6426 (AllWinning.cons node_5582 (AllWinning.cons node_4817 (AllWinning.cons node_9515 (AllWinning.cons node_9518 (AllWinning.cons node_8586 (AllWinning.cons node_7589 (AllWinning.cons node_6669 (AllWinning.cons node_5836 (AllWinning.cons node_5119 (AllWinning.nil)))))))))))))

theorem node_10559 : Outcome ⟨9, 1, 13, 12⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 16⟩) (by decide) node_3802

theorem node_10560 : Outcome ⟨9, 1, 13, 16⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 16⟩) (by decide) node_3802

theorem node_10561 : Outcome ⟨9, 2, 12, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 4⟩) (by decide) node_8425

theorem node_10562 : Outcome ⟨9, 2, 12, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 4⟩) (by decide) node_8425

theorem node_10563 : Outcome ⟨9, 2, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 4⟩) (by decide) node_8425

theorem node_10564 : Outcome ⟨9, 3, 11, 2⟩ true :=
  Outcome.win (q := ⟨8, 3, 11, 2⟩) (by decide) node_9477

theorem node_10565 : Outcome ⟨9, 3, 11, 16⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 8⟩) (by decide) node_6435

theorem node_10566 : Outcome ⟨9, 4, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 4, 10, 2⟩, ⟨7, 4, 10, 4⟩, ⟨9, 3, 10, 2⟩, ⟨9, 2, 10, 4⟩, ⟨9, 4, 9, 2⟩, ⟨9, 4, 8, 4⟩]
  exact AllWinning.cons node_9481 (AllWinning.cons node_8437 (AllWinning.cons node_9523 (AllWinning.cons node_8589 (AllWinning.cons node_9527 (AllWinning.cons node_8597 (AllWinning.nil))))))

theorem node_10567 : Outcome ⟨9, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 6⟩) (by decide) node_7428

theorem node_10568 : Outcome ⟨9, 4, 10, 12⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 6⟩) (by decide) node_7428

theorem node_10569 : Outcome ⟨9, 5, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 9, 2⟩, ⟨7, 5, 9, 4⟩, ⟨9, 4, 9, 2⟩, ⟨9, 3, 9, 4⟩, ⟨9, 5, 8, 2⟩, ⟨9, 5, 7, 4⟩]
  exact AllWinning.cons node_9485 (AllWinning.cons node_8440 (AllWinning.cons node_9527 (AllWinning.cons node_8594 (AllWinning.cons node_9530 (AllWinning.cons node_8600 (AllWinning.nil))))))

theorem node_10570 : Outcome ⟨9, 5, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 9, 2⟩, ⟨7, 5, 9, 4⟩, ⟨6, 5, 9, 6⟩, ⟨5, 5, 9, 8⟩, ⟨9, 4, 9, 2⟩, ⟨9, 3, 9, 4⟩, ⟨9, 2, 9, 6⟩, ⟨9, 1, 9, 8⟩, ⟨9, 5, 8, 2⟩, ⟨9, 5, 7, 4⟩, ⟨9, 5, 6, 6⟩, ⟨9, 5, 5, 8⟩]
  exact AllWinning.cons node_9485 (AllWinning.cons node_8440 (AllWinning.cons node_7439 (AllWinning.cons node_6447 (AllWinning.cons node_9527 (AllWinning.cons node_8594 (AllWinning.cons node_7593 (AllWinning.cons node_6669 (AllWinning.cons node_9530 (AllWinning.cons node_8600 (AllWinning.cons node_7604 (AllWinning.cons node_6681 (AllWinning.nil))))))))))))

theorem node_10571 : Outcome ⟨9, 5, 9, 6⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 10⟩) (by decide) node_5824

theorem node_10572 : Outcome ⟨9, 5, 9, 10⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 16⟩) (by decide) node_3419

theorem node_10573 : Outcome ⟨9, 6, 8, 4⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 4⟩) (by decide) node_8444

theorem node_10574 : Outcome ⟨9, 6, 8, 6⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 4⟩) (by decide) node_8444

theorem node_10575 : Outcome ⟨9, 6, 8, 18⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 4⟩) (by decide) node_8444

theorem node_10576 : Outcome ⟨9, 7, 7, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 4⟩) (by decide) node_8456

theorem node_10577 : Outcome ⟨9, 7, 7, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 4⟩) (by decide) node_8456

theorem node_10578 : Outcome ⟨9, 7, 7, 12⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 18⟩) (by decide) node_2857

theorem node_10579 : Outcome ⟨9, 8, 6, 4⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 4⟩) (by decide) node_8460

theorem node_10580 : Outcome ⟨9, 8, 6, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 4⟩) (by decide) node_8460

theorem node_10581 : Outcome ⟨9, 8, 6, 18⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 4⟩) (by decide) node_8460

theorem node_10582 : Outcome ⟨9, 9, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 5, 2⟩, ⟨7, 9, 5, 4⟩, ⟨9, 8, 5, 2⟩, ⟨9, 7, 5, 4⟩, ⟨9, 9, 4, 2⟩, ⟨9, 9, 3, 4⟩]
  exact AllWinning.cons node_9496 (AllWinning.cons node_8471 (AllWinning.cons node_9543 (AllWinning.cons node_8606 (AllWinning.cons node_9546 (AllWinning.cons node_8613 (AllWinning.nil))))))

theorem node_10583 : Outcome ⟨9, 9, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 5, 2⟩, ⟨7, 9, 5, 4⟩, ⟨6, 9, 5, 6⟩, ⟨5, 9, 5, 8⟩, ⟨9, 8, 5, 2⟩, ⟨9, 7, 5, 4⟩, ⟨9, 6, 5, 6⟩, ⟨9, 5, 5, 8⟩, ⟨9, 9, 4, 2⟩, ⟨9, 9, 3, 4⟩, ⟨9, 9, 2, 6⟩, ⟨9, 9, 1, 8⟩]
  exact AllWinning.cons node_9496 (AllWinning.cons node_8471 (AllWinning.cons node_7452 (AllWinning.cons node_6459 (AllWinning.cons node_9543 (AllWinning.cons node_8606 (AllWinning.cons node_7608 (AllWinning.cons node_6681 (AllWinning.cons node_9546 (AllWinning.cons node_8613 (AllWinning.cons node_7621 (AllWinning.cons node_6696 (AllWinning.nil))))))))))))

theorem node_10584 : Outcome ⟨9, 9, 5, 6⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 10⟩) (by decide) node_5874

theorem node_10585 : Outcome ⟨9, 9, 5, 10⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 16⟩) (by decide) node_3443

theorem node_10586 : Outcome ⟨9, 10, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 10, 4, 2⟩, ⟨7, 10, 4, 4⟩, ⟨9, 9, 4, 2⟩, ⟨9, 8, 4, 4⟩, ⟨9, 10, 3, 2⟩, ⟨9, 10, 2, 4⟩]
  exact AllWinning.cons node_9499 (AllWinning.cons node_8475 (AllWinning.cons node_9546 (AllWinning.cons node_8609 (AllWinning.cons node_9549 (AllWinning.cons node_8617 (AllWinning.nil))))))

theorem node_10587 : Outcome ⟨9, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 6⟩) (by decide) node_7457

theorem node_10588 : Outcome ⟨9, 10, 4, 12⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 6⟩) (by decide) node_7457

theorem node_10589 : Outcome ⟨9, 11, 3, 2⟩ true :=
  Outcome.win (q := ⟨8, 11, 3, 2⟩) (by decide) node_9503

theorem node_10590 : Outcome ⟨9, 11, 3, 16⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 8⟩) (by decide) node_6468

theorem node_10591 : Outcome ⟨9, 12, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 4⟩) (by decide) node_8483

theorem node_10592 : Outcome ⟨9, 12, 2, 6⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 4⟩) (by decide) node_8483

theorem node_10593 : Outcome ⟨9, 12, 2, 10⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 4⟩) (by decide) node_8483

theorem node_10594 : Outcome ⟨9, 13, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 13, 1, 2⟩, ⟨7, 13, 1, 4⟩, ⟨9, 12, 1, 2⟩, ⟨9, 11, 1, 4⟩, ⟨9, 13, 0, 2⟩]
  exact AllWinning.cons node_9510 (AllWinning.cons node_8490 (AllWinning.cons node_9556 (AllWinning.cons node_8622 (AllWinning.cons node_9558 (AllWinning.nil)))))

theorem node_10595 : Outcome ⟨9, 13, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 13, 1, 2⟩, ⟨7, 13, 1, 4⟩, ⟨6, 13, 1, 6⟩, ⟨5, 13, 1, 8⟩, ⟨9, 12, 1, 2⟩, ⟨9, 11, 1, 4⟩, ⟨9, 10, 1, 6⟩, ⟨9, 9, 1, 8⟩, ⟨9, 13, 0, 2⟩]
  exact AllWinning.cons node_9510 (AllWinning.cons node_8490 (AllWinning.cons node_7474 (AllWinning.cons node_6481 (AllWinning.cons node_9556 (AllWinning.cons node_8622 (AllWinning.cons node_7625 (AllWinning.cons node_6696 (AllWinning.cons node_9558 (AllWinning.nil)))))))))

theorem node_10596 : Outcome ⟨9, 13, 1, 12⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 16⟩) (by decide) node_3830

theorem node_10597 : Outcome ⟨9, 13, 1, 16⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 16⟩) (by decide) node_3830

theorem node_10598 : Outcome ⟨9, 14, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 14, 0, 2⟩, ⟨7, 14, 0, 4⟩, ⟨9, 13, 0, 2⟩, ⟨9, 12, 0, 4⟩]
  exact AllWinning.cons node_9512 (AllWinning.cons node_8495 (AllWinning.cons node_9558 (AllWinning.cons node_8624 (AllWinning.nil))))

theorem node_10599 : Outcome ⟨9, 14, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 14, 0, 2⟩, ⟨7, 14, 0, 4⟩, ⟨6, 14, 0, 6⟩, ⟨5, 14, 0, 8⟩, ⟨9, 13, 0, 2⟩, ⟨9, 12, 0, 4⟩, ⟨9, 11, 0, 6⟩, ⟨9, 10, 0, 8⟩]
  exact AllWinning.cons node_9512 (AllWinning.cons node_8495 (AllWinning.cons node_7479 (AllWinning.cons node_6484 (AllWinning.cons node_9558 (AllWinning.cons node_8624 (AllWinning.cons node_7628 (AllWinning.cons node_6698 (AllWinning.nil))))))))

theorem node_10600 : Outcome ⟨9, 14, 0, 6⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 10⟩) (by decide) node_5874

theorem node_10601 : Outcome ⟨9, 14, 0, 10⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 10⟩) (by decide) node_5874

theorem node_10602 : Outcome ⟨10, 0, 13, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 6⟩) (by decide) node_7631

theorem node_10603 : Outcome ⟨10, 0, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 6⟩) (by decide) node_7631

theorem node_10604 : Outcome ⟨10, 1, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10605 : Outcome ⟨10, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10606 : Outcome ⟨10, 1, 12, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10607 : Outcome ⟨10, 2, 11, 2⟩ true :=
  Outcome.win (q := ⟨9, 2, 11, 2⟩) (by decide) node_9520

theorem node_10608 : Outcome ⟨10, 2, 11, 4⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 8⟩) (by decide) node_6499

theorem node_10609 : Outcome ⟨10, 2, 11, 6⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10610 : Outcome ⟨10, 2, 11, 10⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10611 : Outcome ⟨10, 2, 11, 12⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10612 : Outcome ⟨10, 2, 11, 14⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10613 : Outcome ⟨10, 3, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 3, 10, 2⟩, ⟨8, 3, 10, 4⟩, ⟨10, 2, 10, 2⟩, ⟨10, 1, 10, 4⟩, ⟨10, 3, 9, 2⟩, ⟨10, 3, 8, 4⟩]
  exact AllWinning.cons node_9523 (AllWinning.cons node_8517 (AllWinning.cons node_9568 (AllWinning.cons node_8629 (AllWinning.cons node_9571 (AllWinning.cons node_8637 (AllWinning.nil))))))

theorem node_10614 : Outcome ⟨10, 3, 10, 6⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 6⟩) (by decide) node_7499

theorem node_10615 : Outcome ⟨10, 3, 10, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 6⟩) (by decide) node_7499

theorem node_10616 : Outcome ⟨10, 4, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 4, 9, 2⟩, ⟨8, 4, 9, 4⟩, ⟨10, 3, 9, 2⟩, ⟨10, 2, 9, 4⟩, ⟨10, 4, 8, 2⟩, ⟨10, 4, 7, 4⟩]
  exact AllWinning.cons node_9527 (AllWinning.cons node_8521 (AllWinning.cons node_9571 (AllWinning.cons node_8632 (AllWinning.cons node_9575 (AllWinning.cons node_8642 (AllWinning.nil))))))

theorem node_10617 : Outcome ⟨10, 4, 9, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10618 : Outcome ⟨10, 4, 9, 12⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10619 : Outcome ⟨10, 5, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 5, 8, 2⟩, ⟨8, 5, 8, 4⟩, ⟨10, 4, 8, 2⟩, ⟨10, 3, 8, 4⟩, ⟨10, 5, 7, 2⟩, ⟨10, 5, 6, 4⟩]
  exact AllWinning.cons node_9530 (AllWinning.cons node_8525 (AllWinning.cons node_9575 (AllWinning.cons node_8637 (AllWinning.cons node_9579 (AllWinning.cons node_8645 (AllWinning.nil))))))

theorem node_10620 : Outcome ⟨10, 5, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 5, 8, 2⟩, ⟨8, 5, 8, 4⟩, ⟨7, 5, 8, 6⟩, ⟨6, 5, 8, 8⟩, ⟨10, 4, 8, 2⟩, ⟨10, 3, 8, 4⟩, ⟨10, 2, 8, 6⟩, ⟨10, 1, 8, 8⟩, ⟨10, 5, 7, 2⟩, ⟨10, 5, 6, 4⟩, ⟨10, 5, 5, 6⟩, ⟨10, 5, 4, 8⟩]
  exact AllWinning.cons node_9530 (AllWinning.cons node_8525 (AllWinning.cons node_7506 (AllWinning.cons node_6513 (AllWinning.cons node_9575 (AllWinning.cons node_8637 (AllWinning.cons node_7644 (AllWinning.cons node_6704 (AllWinning.cons node_9579 (AllWinning.cons node_8645 (AllWinning.cons node_7663 (AllWinning.cons node_6720 (AllWinning.nil))))))))))))

theorem node_10621 : Outcome ⟨10, 5, 8, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10622 : Outcome ⟨10, 5, 8, 10⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10623 : Outcome ⟨10, 5, 8, 12⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10624 : Outcome ⟨10, 5, 8, 22⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10625 : Outcome ⟨10, 6, 7, 2⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 4⟩) (by decide) node_8530

theorem node_10626 : Outcome ⟨10, 6, 7, 4⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 6⟩) (by decide) node_7648

theorem node_10627 : Outcome ⟨10, 6, 7, 6⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 6⟩) (by decide) node_7648

theorem node_10628 : Outcome ⟨10, 6, 7, 8⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 6⟩) (by decide) node_7648

theorem node_10629 : Outcome ⟨10, 6, 7, 18⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 6⟩) (by decide) node_7648

theorem node_10630 : Outcome ⟨10, 6, 7, 22⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 6⟩) (by decide) node_7648

theorem node_10631 : Outcome ⟨10, 7, 6, 2⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 4⟩) (by decide) node_8542

theorem node_10632 : Outcome ⟨10, 7, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10633 : Outcome ⟨10, 7, 6, 6⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10634 : Outcome ⟨10, 7, 6, 8⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10635 : Outcome ⟨10, 7, 6, 18⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10636 : Outcome ⟨10, 7, 6, 22⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10637 : Outcome ⟨10, 8, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 5, 2⟩, ⟨8, 8, 5, 4⟩, ⟨10, 7, 5, 2⟩, ⟨10, 6, 5, 4⟩, ⟨10, 8, 4, 2⟩, ⟨10, 8, 3, 4⟩]
  exact AllWinning.cons node_9543 (AllWinning.cons node_8554 (AllWinning.cons node_9587 (AllWinning.cons node_8649 (AllWinning.cons node_9592 (AllWinning.cons node_8656 (AllWinning.nil))))))

theorem node_10638 : Outcome ⟨10, 8, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 5, 2⟩, ⟨8, 8, 5, 4⟩, ⟨7, 8, 5, 6⟩, ⟨6, 8, 5, 8⟩, ⟨10, 7, 5, 2⟩, ⟨10, 6, 5, 4⟩, ⟨10, 5, 5, 6⟩, ⟨10, 4, 5, 8⟩, ⟨10, 8, 4, 2⟩, ⟨10, 8, 3, 4⟩, ⟨10, 8, 2, 6⟩, ⟨10, 8, 1, 8⟩]
  exact AllWinning.cons node_9543 (AllWinning.cons node_8554 (AllWinning.cons node_7514 (AllWinning.cons node_6522 (AllWinning.cons node_9587 (AllWinning.cons node_8649 (AllWinning.cons node_7663 (AllWinning.cons node_6716 (AllWinning.cons node_9592 (AllWinning.cons node_8656 (AllWinning.cons node_7682 (AllWinning.cons node_6731 (AllWinning.nil))))))))))))

theorem node_10639 : Outcome ⟨10, 8, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10640 : Outcome ⟨10, 8, 5, 10⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10641 : Outcome ⟨10, 8, 5, 12⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10642 : Outcome ⟨10, 8, 5, 22⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10643 : Outcome ⟨10, 9, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 9, 4, 2⟩, ⟨8, 9, 4, 4⟩, ⟨10, 8, 4, 2⟩, ⟨10, 7, 4, 4⟩, ⟨10, 9, 3, 2⟩, ⟨10, 9, 2, 4⟩]
  exact AllWinning.cons node_9546 (AllWinning.cons node_8558 (AllWinning.cons node_9592 (AllWinning.cons node_8653 (AllWinning.cons node_9596 (AllWinning.cons node_8661 (AllWinning.nil))))))

theorem node_10644 : Outcome ⟨10, 9, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 6⟩) (by decide) node_7667

theorem node_10645 : Outcome ⟨10, 9, 4, 12⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 6⟩) (by decide) node_7667

theorem node_10646 : Outcome ⟨10, 10, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 10, 3, 2⟩, ⟨8, 10, 3, 4⟩, ⟨10, 9, 3, 2⟩, ⟨10, 8, 3, 4⟩, ⟨10, 10, 2, 2⟩, ⟨10, 10, 1, 4⟩]
  exact AllWinning.cons node_9549 (AllWinning.cons node_8562 (AllWinning.cons node_9596 (AllWinning.cons node_8656 (AllWinning.cons node_9600 (AllWinning.cons node_8665 (AllWinning.nil))))))

theorem node_10647 : Outcome ⟨10, 10, 3, 6⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 6⟩) (by decide) node_7522

theorem node_10648 : Outcome ⟨10, 10, 3, 8⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 6⟩) (by decide) node_7522

theorem node_10649 : Outcome ⟨10, 11, 2, 2⟩ true :=
  Outcome.win (q := ⟨9, 11, 2, 2⟩) (by decide) node_9553

theorem node_10650 : Outcome ⟨10, 11, 2, 4⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 8⟩) (by decide) node_6533

theorem node_10651 : Outcome ⟨10, 11, 2, 6⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10652 : Outcome ⟨10, 11, 2, 10⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10653 : Outcome ⟨10, 11, 2, 12⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10654 : Outcome ⟨10, 11, 2, 14⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10655 : Outcome ⟨10, 12, 1, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10656 : Outcome ⟨10, 12, 1, 4⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10657 : Outcome ⟨10, 12, 1, 8⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10658 : Outcome ⟨10, 13, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 6⟩) (by decide) node_7690

theorem node_10659 : Outcome ⟨10, 13, 0, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 6⟩) (by decide) node_7690

theorem node_10660 : Outcome ⟨11, 0, 12, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 2⟩) (by decide) node_9609

theorem node_10661 : Outcome ⟨11, 0, 12, 8⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 2⟩) (by decide) node_9609

theorem node_10662 : Outcome ⟨11, 1, 11, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 2⟩) (by decide) node_9609

theorem node_10663 : Outcome ⟨11, 1, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 8⟩) (by decide) node_6559

theorem node_10664 : Outcome ⟨11, 1, 11, 16⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 8⟩) (by decide) node_6559

theorem node_10665 : Outcome ⟨11, 2, 10, 2⟩ true :=
  Outcome.win (q := ⟨11, 2, 9, 2⟩) (by decide) node_9623

theorem node_10666 : Outcome ⟨11, 2, 10, 4⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 8⟩) (by decide) node_6754

theorem node_10667 : Outcome ⟨11, 2, 10, 6⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 12⟩) (by decide) node_4935

theorem node_10668 : Outcome ⟨11, 2, 10, 10⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 12⟩) (by decide) node_4935

theorem node_10669 : Outcome ⟨11, 2, 10, 12⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 12⟩) (by decide) node_4935

theorem node_10670 : Outcome ⟨11, 2, 10, 14⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 12⟩) (by decide) node_4935

theorem node_10671 : Outcome ⟨11, 3, 9, 2⟩ true :=
  Outcome.win (q := ⟨11, 2, 9, 2⟩) (by decide) node_9623

theorem node_10672 : Outcome ⟨11, 3, 9, 16⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 8⟩) (by decide) node_6763

theorem node_10673 : Outcome ⟨11, 3, 9, 20⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 8⟩) (by decide) node_6763

theorem node_10674 : Outcome ⟨11, 4, 8, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 8, 2⟩) (by decide) node_9626

theorem node_10675 : Outcome ⟨11, 4, 8, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 8, 2⟩) (by decide) node_9626

theorem node_10676 : Outcome ⟨11, 4, 8, 6⟩ true :=
  Outcome.win (q := ⟨11, 3, 8, 2⟩) (by decide) node_9626

theorem node_10677 : Outcome ⟨11, 4, 8, 12⟩ true :=
  Outcome.win (q := ⟨11, 3, 8, 2⟩) (by decide) node_9626

theorem node_10678 : Outcome ⟨11, 4, 8, 20⟩ true :=
  Outcome.win (q := ⟨11, 3, 8, 2⟩) (by decide) node_9626

theorem node_10679 : Outcome ⟨11, 5, 7, 2⟩ true :=
  Outcome.win (q := ⟨11, 4, 7, 2⟩) (by decide) node_9631

theorem node_10680 : Outcome ⟨11, 5, 7, 6⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 8⟩) (by decide) node_6744

theorem node_10681 : Outcome ⟨11, 5, 7, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 14⟩) (by decide) node_4176

theorem node_10682 : Outcome ⟨11, 5, 7, 12⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 14⟩) (by decide) node_4176

theorem node_10683 : Outcome ⟨11, 5, 7, 22⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 14⟩) (by decide) node_4176

theorem node_10684 : Outcome ⟨11, 6, 6, 2⟩ true :=
  Outcome.win (q := ⟨11, 5, 6, 2⟩) (by decide) node_9637

theorem node_10685 : Outcome ⟨11, 6, 6, 18⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 22⟩) (by decide) node_1899

theorem node_10686 : Outcome ⟨11, 7, 5, 2⟩ true :=
  Outcome.win (q := ⟨11, 6, 5, 2⟩) (by decide) node_9640

theorem node_10687 : Outcome ⟨11, 7, 5, 6⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 8⟩) (by decide) node_6763

theorem node_10688 : Outcome ⟨11, 7, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 14⟩) (by decide) node_4193

theorem node_10689 : Outcome ⟨11, 7, 5, 12⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 14⟩) (by decide) node_4193

theorem node_10690 : Outcome ⟨11, 7, 5, 22⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 14⟩) (by decide) node_4193

theorem node_10691 : Outcome ⟨11, 8, 4, 2⟩ true :=
  Outcome.win (q := ⟨11, 7, 4, 2⟩) (by decide) node_9643

theorem node_10692 : Outcome ⟨11, 8, 4, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 4, 2⟩) (by decide) node_9643

theorem node_10693 : Outcome ⟨11, 8, 4, 6⟩ true :=
  Outcome.win (q := ⟨11, 7, 4, 2⟩) (by decide) node_9643

theorem node_10694 : Outcome ⟨11, 8, 4, 12⟩ true :=
  Outcome.win (q := ⟨11, 7, 4, 2⟩) (by decide) node_9643

theorem node_10695 : Outcome ⟨11, 8, 4, 20⟩ true :=
  Outcome.win (q := ⟨11, 7, 4, 2⟩) (by decide) node_9643

theorem node_10696 : Outcome ⟨11, 9, 3, 2⟩ true :=
  Outcome.win (q := ⟨11, 8, 3, 2⟩) (by decide) node_9649

theorem node_10697 : Outcome ⟨11, 9, 3, 16⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 8⟩) (by decide) node_6777

theorem node_10698 : Outcome ⟨11, 9, 3, 20⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 8⟩) (by decide) node_6777

theorem node_10699 : Outcome ⟨11, 10, 2, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 2, 2⟩) (by decide) node_9654

theorem node_10700 : Outcome ⟨11, 10, 2, 4⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 8⟩) (by decide) node_6788

theorem node_10701 : Outcome ⟨11, 10, 2, 6⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10702 : Outcome ⟨11, 10, 2, 10⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10703 : Outcome ⟨11, 10, 2, 12⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10704 : Outcome ⟨11, 10, 2, 14⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10705 : Outcome ⟨11, 11, 1, 2⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 2⟩) (by decide) node_9661

theorem node_10706 : Outcome ⟨11, 11, 1, 8⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 8⟩) (by decide) node_6606

theorem node_10707 : Outcome ⟨11, 11, 1, 16⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 8⟩) (by decide) node_6606

theorem node_10708 : Outcome ⟨11, 12, 0, 2⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 2⟩) (by decide) node_9661

theorem node_10709 : Outcome ⟨11, 12, 0, 8⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 2⟩) (by decide) node_9661

theorem node_10710 : Outcome ⟨12, 0, 11, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 2⟩) (by decide) node_9609

theorem node_10711 : Outcome ⟨12, 0, 11, 8⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 2⟩) (by decide) node_9609

theorem node_10712 : Outcome ⟨12, 1, 10, 2⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10713 : Outcome ⟨12, 1, 10, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10714 : Outcome ⟨12, 1, 10, 8⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10715 : Outcome ⟨12, 2, 9, 2⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 4⟩) (by decide) node_8725

theorem node_10716 : Outcome ⟨12, 2, 9, 6⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 4⟩) (by decide) node_8725

theorem node_10717 : Outcome ⟨12, 2, 9, 10⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 4⟩) (by decide) node_8725

theorem node_10718 : Outcome ⟨12, 3, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10719 : Outcome ⟨12, 3, 8, 8⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10720 : Outcome ⟨12, 3, 8, 10⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10721 : Outcome ⟨12, 4, 7, 2⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 4⟩) (by decide) node_8725

theorem node_10722 : Outcome ⟨12, 4, 7, 4⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 4⟩) (by decide) node_8725

theorem node_10723 : Outcome ⟨12, 4, 7, 6⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 4⟩) (by decide) node_8725

theorem node_10724 : Outcome ⟨12, 4, 7, 12⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 14⟩) (by decide) node_4242

theorem node_10725 : Outcome ⟨12, 4, 7, 22⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 14⟩) (by decide) node_4242

theorem node_10726 : Outcome ⟨12, 5, 6, 2⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 4⟩) (by decide) node_8739

theorem node_10727 : Outcome ⟨12, 5, 6, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 4⟩) (by decide) node_8739

theorem node_10728 : Outcome ⟨12, 5, 6, 22⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 4⟩) (by decide) node_8739

theorem node_10729 : Outcome ⟨12, 5, 6, 24⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 4⟩) (by decide) node_8739

theorem node_10730 : Outcome ⟨12, 6, 5, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 5, 4⟩) (by decide) node_8735

theorem node_10731 : Outcome ⟨12, 6, 5, 8⟩ true :=
  Outcome.win (q := ⟨12, 4, 5, 4⟩) (by decide) node_8735

theorem node_10732 : Outcome ⟨12, 6, 5, 22⟩ true :=
  Outcome.win (q := ⟨12, 4, 5, 4⟩) (by decide) node_8735

theorem node_10733 : Outcome ⟨12, 6, 5, 24⟩ true :=
  Outcome.win (q := ⟨12, 4, 5, 4⟩) (by decide) node_8735

theorem node_10734 : Outcome ⟨12, 7, 4, 2⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 4⟩) (by decide) node_8739

theorem node_10735 : Outcome ⟨12, 7, 4, 4⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 4⟩) (by decide) node_8739

theorem node_10736 : Outcome ⟨12, 7, 4, 6⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 4⟩) (by decide) node_8739

theorem node_10737 : Outcome ⟨12, 7, 4, 12⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 14⟩) (by decide) node_4259

theorem node_10738 : Outcome ⟨12, 7, 4, 22⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 14⟩) (by decide) node_4259

theorem node_10739 : Outcome ⟨12, 8, 3, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10740 : Outcome ⟨12, 8, 3, 8⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10741 : Outcome ⟨12, 8, 3, 10⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10742 : Outcome ⟨12, 9, 2, 2⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 4⟩) (by decide) node_8746

theorem node_10743 : Outcome ⟨12, 9, 2, 6⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 4⟩) (by decide) node_8746

theorem node_10744 : Outcome ⟨12, 9, 2, 10⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 4⟩) (by decide) node_8746

theorem node_10745 : Outcome ⟨12, 10, 1, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10746 : Outcome ⟨12, 10, 1, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10747 : Outcome ⟨12, 10, 1, 8⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10748 : Outcome ⟨12, 11, 0, 2⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 2⟩) (by decide) node_9661

theorem node_10749 : Outcome ⟨12, 11, 0, 8⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 2⟩) (by decide) node_9661

theorem node_10750 : Outcome ⟨13, 0, 10, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 6⟩) (by decide) node_7631

theorem node_10751 : Outcome ⟨13, 0, 10, 6⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 6⟩) (by decide) node_7631

theorem node_10752 : Outcome ⟨13, 1, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 9, 2⟩, ⟨11, 1, 9, 4⟩, ⟨13, 0, 9, 2⟩, ⟨13, 1, 8, 2⟩, ⟨13, 1, 7, 4⟩]
  exact AllWinning.cons node_9674 (AllWinning.cons node_8674 (AllWinning.cons node_9707 (AllWinning.cons node_9710 (AllWinning.cons node_8768 (AllWinning.nil)))))

theorem node_10753 : Outcome ⟨13, 1, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 9, 2⟩, ⟨11, 1, 9, 4⟩, ⟨10, 1, 9, 6⟩, ⟨9, 1, 9, 8⟩, ⟨13, 0, 9, 2⟩, ⟨13, 1, 8, 2⟩, ⟨13, 1, 7, 4⟩, ⟨13, 1, 6, 6⟩, ⟨13, 1, 5, 8⟩]
  exact AllWinning.cons node_9674 (AllWinning.cons node_8674 (AllWinning.cons node_7641 (AllWinning.cons node_6669 (AllWinning.cons node_9707 (AllWinning.cons node_9710 (AllWinning.cons node_8768 (AllWinning.cons node_7764 (AllWinning.cons node_6846 (AllWinning.nil)))))))))

theorem node_10754 : Outcome ⟨13, 1, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 9, 2⟩, ⟨11, 1, 9, 4⟩, ⟨10, 1, 9, 6⟩, ⟨9, 1, 9, 8⟩, ⟨8, 1, 9, 10⟩, ⟨7, 1, 9, 12⟩, ⟨13, 0, 9, 2⟩, ⟨13, 1, 8, 2⟩, ⟨13, 1, 7, 4⟩, ⟨13, 1, 6, 6⟩, ⟨13, 1, 5, 8⟩, ⟨13, 1, 4, 10⟩, ⟨13, 1, 3, 12⟩]
  exact AllWinning.cons node_9674 (AllWinning.cons node_8674 (AllWinning.cons node_7641 (AllWinning.cons node_6669 (AllWinning.cons node_5781 (AllWinning.cons node_5037 (AllWinning.cons node_9707 (AllWinning.cons node_9710 (AllWinning.cons node_8768 (AllWinning.cons node_7764 (AllWinning.cons node_6846 (AllWinning.cons node_5960 (AllWinning.cons node_5244 (AllWinning.nil)))))))))))))

theorem node_10755 : Outcome ⟨13, 1, 9, 12⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 16⟩) (by decide) node_3641

theorem node_10756 : Outcome ⟨13, 1, 9, 16⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 16⟩) (by decide) node_3641

theorem node_10757 : Outcome ⟨13, 2, 8, 2⟩ true :=
  Outcome.win (q := ⟨13, 0, 8, 4⟩) (by decide) node_8765

theorem node_10758 : Outcome ⟨13, 2, 8, 6⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 12⟩) (by decide) node_5252

theorem node_10759 : Outcome ⟨13, 2, 8, 12⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 12⟩) (by decide) node_5252

theorem node_10760 : Outcome ⟨13, 3, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 3, 7, 2⟩, ⟨11, 3, 7, 4⟩, ⟨13, 2, 7, 2⟩, ⟨13, 1, 7, 4⟩, ⟨13, 3, 6, 2⟩, ⟨13, 3, 5, 4⟩]
  exact AllWinning.cons node_9679 (AllWinning.cons node_8681 (AllWinning.cons node_9712 (AllWinning.cons node_8768 (AllWinning.cons node_9716 (AllWinning.cons node_8775 (AllWinning.nil))))))

theorem node_10761 : Outcome ⟨13, 3, 7, 4⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 8⟩) (by decide) node_6854

theorem node_10762 : Outcome ⟨13, 3, 7, 6⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 8⟩) (by decide) node_6854

theorem node_10763 : Outcome ⟨13, 3, 7, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 22⟩) (by decide) node_2004

theorem node_10764 : Outcome ⟨13, 4, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10765 : Outcome ⟨13, 4, 6, 6⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10766 : Outcome ⟨13, 4, 6, 12⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10767 : Outcome ⟨13, 4, 6, 20⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 6⟩) (by decide) node_7653

theorem node_10768 : Outcome ⟨13, 5, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 5, 2⟩, ⟨11, 5, 5, 4⟩, ⟨13, 4, 5, 2⟩, ⟨13, 3, 5, 4⟩, ⟨13, 5, 4, 2⟩, ⟨13, 5, 3, 4⟩]
  exact AllWinning.cons node_9688 (AllWinning.cons node_8690 (AllWinning.cons node_9719 (AllWinning.cons node_8775 (AllWinning.cons node_9722 (AllWinning.cons node_8783 (AllWinning.nil))))))

theorem node_10769 : Outcome ⟨13, 5, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 5, 2⟩, ⟨11, 5, 5, 4⟩, ⟨10, 5, 5, 6⟩, ⟨9, 5, 5, 8⟩, ⟨13, 4, 5, 2⟩, ⟨13, 3, 5, 4⟩, ⟨13, 2, 5, 6⟩, ⟨13, 1, 5, 8⟩, ⟨13, 5, 4, 2⟩, ⟨13, 5, 3, 4⟩, ⟨13, 5, 2, 6⟩, ⟨13, 5, 1, 8⟩]
  exact AllWinning.cons node_9688 (AllWinning.cons node_8690 (AllWinning.cons node_7663 (AllWinning.cons node_6681 (AllWinning.cons node_9719 (AllWinning.cons node_8775 (AllWinning.cons node_7768 (AllWinning.cons node_6846 (AllWinning.cons node_9722 (AllWinning.cons node_8783 (AllWinning.cons node_7777 (AllWinning.cons node_6862 (AllWinning.nil))))))))))))

theorem node_10770 : Outcome ⟨13, 5, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 5, 2⟩, ⟨11, 5, 5, 4⟩, ⟨10, 5, 5, 6⟩, ⟨9, 5, 5, 8⟩, ⟨8, 5, 5, 10⟩, ⟨7, 5, 5, 12⟩, ⟨13, 4, 5, 2⟩, ⟨13, 3, 5, 4⟩, ⟨13, 2, 5, 6⟩, ⟨13, 1, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨13, 5, 4, 2⟩, ⟨13, 5, 3, 4⟩, ⟨13, 5, 2, 6⟩, ⟨13, 5, 1, 8⟩, ⟨13, 5, 0, 10⟩]
  exact AllWinning.cons node_9688 (AllWinning.cons node_8690 (AllWinning.cons node_7663 (AllWinning.cons node_6681 (AllWinning.cons node_5798 (AllWinning.cons node_5054 (AllWinning.cons node_9719 (AllWinning.cons node_8775 (AllWinning.cons node_7768 (AllWinning.cons node_6846 (AllWinning.cons node_5955 (AllWinning.cons node_9722 (AllWinning.cons node_8783 (AllWinning.cons node_7777 (AllWinning.cons node_6862 (AllWinning.cons node_5976 (AllWinning.nil))))))))))))))))

theorem node_10771 : Outcome ⟨13, 5, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 5, 2⟩, ⟨11, 5, 5, 4⟩, ⟨10, 5, 5, 6⟩, ⟨9, 5, 5, 8⟩, ⟨8, 5, 5, 10⟩, ⟨7, 5, 5, 12⟩, ⟨6, 5, 5, 14⟩, ⟨5, 5, 5, 16⟩, ⟨13, 4, 5, 2⟩, ⟨13, 3, 5, 4⟩, ⟨13, 2, 5, 6⟩, ⟨13, 1, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨13, 5, 4, 2⟩, ⟨13, 5, 3, 4⟩, ⟨13, 5, 2, 6⟩, ⟨13, 5, 1, 8⟩, ⟨13, 5, 0, 10⟩]
  exact AllWinning.cons node_9688 (AllWinning.cons node_8690 (AllWinning.cons node_7663 (AllWinning.cons node_6681 (AllWinning.cons node_5798 (AllWinning.cons node_5054 (AllWinning.cons node_4304 (AllWinning.cons node_3660 (AllWinning.cons node_9719 (AllWinning.cons node_8775 (AllWinning.cons node_7768 (AllWinning.cons node_6846 (AllWinning.cons node_5955 (AllWinning.cons node_9722 (AllWinning.cons node_8783 (AllWinning.cons node_7777 (AllWinning.cons node_6862 (AllWinning.cons node_5976 (AllWinning.nil))))))))))))))))))

theorem node_10772 : Outcome ⟨13, 5, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 5, 2⟩, ⟨11, 5, 5, 4⟩, ⟨10, 5, 5, 6⟩, ⟨9, 5, 5, 8⟩, ⟨8, 5, 5, 10⟩, ⟨7, 5, 5, 12⟩, ⟨6, 5, 5, 14⟩, ⟨5, 5, 5, 16⟩, ⟨4, 5, 5, 18⟩, ⟨3, 5, 5, 20⟩, ⟨13, 4, 5, 2⟩, ⟨13, 3, 5, 4⟩, ⟨13, 2, 5, 6⟩, ⟨13, 1, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨13, 5, 4, 2⟩, ⟨13, 5, 3, 4⟩, ⟨13, 5, 2, 6⟩, ⟨13, 5, 1, 8⟩, ⟨13, 5, 0, 10⟩]
  exact AllWinning.cons node_9688 (AllWinning.cons node_8690 (AllWinning.cons node_7663 (AllWinning.cons node_6681 (AllWinning.cons node_5798 (AllWinning.cons node_5054 (AllWinning.cons node_4304 (AllWinning.cons node_3660 (AllWinning.cons node_3066 (AllWinning.cons node_2555 (AllWinning.cons node_9719 (AllWinning.cons node_8775 (AllWinning.cons node_7768 (AllWinning.cons node_6846 (AllWinning.cons node_5955 (AllWinning.cons node_9722 (AllWinning.cons node_8783 (AllWinning.cons node_7777 (AllWinning.cons node_6862 (AllWinning.cons node_5976 (AllWinning.nil))))))))))))))))))))

theorem node_10773 : Outcome ⟨13, 5, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 5, 2⟩, ⟨11, 5, 5, 4⟩, ⟨10, 5, 5, 6⟩, ⟨9, 5, 5, 8⟩, ⟨8, 5, 5, 10⟩, ⟨7, 5, 5, 12⟩, ⟨6, 5, 5, 14⟩, ⟨5, 5, 5, 16⟩, ⟨4, 5, 5, 18⟩, ⟨3, 5, 5, 20⟩, ⟨2, 5, 5, 22⟩, ⟨1, 5, 5, 24⟩, ⟨13, 4, 5, 2⟩, ⟨13, 3, 5, 4⟩, ⟨13, 2, 5, 6⟩, ⟨13, 1, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨13, 5, 4, 2⟩, ⟨13, 5, 3, 4⟩, ⟨13, 5, 2, 6⟩, ⟨13, 5, 1, 8⟩, ⟨13, 5, 0, 10⟩]
  exact AllWinning.cons node_9688 (AllWinning.cons node_8690 (AllWinning.cons node_7663 (AllWinning.cons node_6681 (AllWinning.cons node_5798 (AllWinning.cons node_5054 (AllWinning.cons node_4304 (AllWinning.cons node_3660 (AllWinning.cons node_3066 (AllWinning.cons node_2555 (AllWinning.cons node_2018 (AllWinning.cons node_1615 (AllWinning.cons node_9719 (AllWinning.cons node_8775 (AllWinning.cons node_7768 (AllWinning.cons node_6846 (AllWinning.cons node_5955 (AllWinning.cons node_9722 (AllWinning.cons node_8783 (AllWinning.cons node_7777 (AllWinning.cons node_6862 (AllWinning.cons node_5976 (AllWinning.nil))))))))))))))))))))))

theorem node_10774 : Outcome ⟨13, 6, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 6⟩) (by decide) node_7667

theorem node_10775 : Outcome ⟨13, 6, 4, 6⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 6⟩) (by decide) node_7667

theorem node_10776 : Outcome ⟨13, 6, 4, 12⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 6⟩) (by decide) node_7667

theorem node_10777 : Outcome ⟨13, 6, 4, 20⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 6⟩) (by decide) node_7667

theorem node_10778 : Outcome ⟨13, 7, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 7, 3, 2⟩, ⟨11, 7, 3, 4⟩, ⟨13, 6, 3, 2⟩, ⟨13, 5, 3, 4⟩, ⟨13, 7, 2, 2⟩, ⟨13, 7, 1, 4⟩]
  exact AllWinning.cons node_9694 (AllWinning.cons node_8696 (AllWinning.cons node_9725 (AllWinning.cons node_8783 (AllWinning.cons node_9728 (AllWinning.cons node_8789 (AllWinning.nil))))))

theorem node_10779 : Outcome ⟨13, 7, 3, 4⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 8⟩) (by decide) node_6854

theorem node_10780 : Outcome ⟨13, 7, 3, 6⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 8⟩) (by decide) node_6854

theorem node_10781 : Outcome ⟨13, 7, 3, 12⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 22⟩) (by decide) node_2034

theorem node_10782 : Outcome ⟨13, 8, 2, 2⟩ true :=
  Outcome.win (q := ⟨13, 8, 0, 4⟩) (by decide) node_8793

theorem node_10783 : Outcome ⟨13, 8, 2, 6⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 12⟩) (by decide) node_5252

theorem node_10784 : Outcome ⟨13, 8, 2, 12⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 12⟩) (by decide) node_5252

theorem node_10785 : Outcome ⟨13, 9, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 9, 1, 2⟩, ⟨11, 9, 1, 4⟩, ⟨13, 8, 1, 2⟩, ⟨13, 7, 1, 4⟩, ⟨13, 9, 0, 2⟩]
  exact AllWinning.cons node_9702 (AllWinning.cons node_8705 (AllWinning.cons node_9732 (AllWinning.cons node_8789 (AllWinning.cons node_9734 (AllWinning.nil)))))

theorem node_10786 : Outcome ⟨13, 9, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 9, 1, 2⟩, ⟨11, 9, 1, 4⟩, ⟨10, 9, 1, 6⟩, ⟨9, 9, 1, 8⟩, ⟨13, 8, 1, 2⟩, ⟨13, 7, 1, 4⟩, ⟨13, 6, 1, 6⟩, ⟨13, 5, 1, 8⟩, ⟨13, 9, 0, 2⟩]
  exact AllWinning.cons node_9702 (AllWinning.cons node_8705 (AllWinning.cons node_7686 (AllWinning.cons node_6696 (AllWinning.cons node_9732 (AllWinning.cons node_8789 (AllWinning.cons node_7781 (AllWinning.cons node_6862 (AllWinning.cons node_9734 (AllWinning.nil)))))))))

theorem node_10787 : Outcome ⟨13, 9, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 9, 1, 2⟩, ⟨11, 9, 1, 4⟩, ⟨10, 9, 1, 6⟩, ⟨9, 9, 1, 8⟩, ⟨8, 9, 1, 10⟩, ⟨7, 9, 1, 12⟩, ⟨13, 8, 1, 2⟩, ⟨13, 7, 1, 4⟩, ⟨13, 6, 1, 6⟩, ⟨13, 5, 1, 8⟩, ⟨13, 4, 1, 10⟩, ⟨13, 3, 1, 12⟩, ⟨13, 9, 0, 2⟩]
  exact AllWinning.cons node_9702 (AllWinning.cons node_8705 (AllWinning.cons node_7686 (AllWinning.cons node_6696 (AllWinning.cons node_5816 (AllWinning.cons node_5071 (AllWinning.cons node_9732 (AllWinning.cons node_8789 (AllWinning.cons node_7781 (AllWinning.cons node_6862 (AllWinning.cons node_5970 (AllWinning.cons node_5256 (AllWinning.cons node_9734 (AllWinning.nil)))))))))))))

theorem node_10788 : Outcome ⟨13, 9, 1, 12⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 16⟩) (by decide) node_3679

theorem node_10789 : Outcome ⟨13, 9, 1, 16⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 16⟩) (by decide) node_3679

theorem node_10790 : Outcome ⟨13, 10, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 6⟩) (by decide) node_7690

theorem node_10791 : Outcome ⟨13, 10, 0, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 6⟩) (by decide) node_7690

theorem node_10792 : Outcome ⟨14, 0, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 9, 2⟩, ⟨12, 0, 9, 4⟩, ⟨14, 0, 8, 2⟩, ⟨14, 0, 7, 4⟩]
  exact AllWinning.cons node_9707 (AllWinning.cons node_8711 (AllWinning.cons node_9737 (AllWinning.cons node_8797 (AllWinning.nil))))

theorem node_10793 : Outcome ⟨14, 0, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 9, 2⟩, ⟨12, 0, 9, 4⟩, ⟨11, 0, 9, 6⟩, ⟨10, 0, 9, 8⟩, ⟨14, 0, 8, 2⟩, ⟨14, 0, 7, 4⟩, ⟨14, 0, 6, 6⟩, ⟨14, 0, 5, 8⟩]
  exact AllWinning.cons node_9707 (AllWinning.cons node_8711 (AllWinning.cons node_7700 (AllWinning.cons node_6701 (AllWinning.cons node_9737 (AllWinning.cons node_8797 (AllWinning.cons node_7790 (AllWinning.cons node_6870 (AllWinning.nil))))))))

theorem node_10794 : Outcome ⟨14, 0, 9, 6⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 10⟩) (by decide) node_5824

theorem node_10795 : Outcome ⟨14, 0, 9, 10⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 10⟩) (by decide) node_5824

theorem node_10796 : Outcome ⟨14, 1, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10797 : Outcome ⟨14, 1, 8, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 4⟩) (by decide) node_8714

theorem node_10798 : Outcome ⟨14, 2, 7, 2⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 4⟩) (by decide) node_8725

theorem node_10799 : Outcome ⟨14, 2, 7, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10800 : Outcome ⟨14, 2, 7, 8⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10801 : Outcome ⟨14, 2, 7, 10⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10802 : Outcome ⟨14, 3, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 6, 2⟩, ⟨12, 3, 6, 4⟩, ⟨14, 2, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨14, 3, 5, 2⟩, ⟨14, 3, 4, 4⟩]
  exact AllWinning.cons node_9716 (AllWinning.cons node_8731 (AllWinning.cons node_9741 (AllWinning.cons node_8800 (AllWinning.cons node_9746 (AllWinning.cons node_8805 (AllWinning.nil))))))

theorem node_10803 : Outcome ⟨14, 3, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 6, 2⟩, ⟨12, 3, 6, 4⟩, ⟨11, 3, 6, 6⟩, ⟨10, 3, 6, 8⟩, ⟨14, 2, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨14, 0, 6, 6⟩, ⟨14, 3, 5, 2⟩, ⟨14, 3, 4, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 3, 2, 8⟩]
  exact AllWinning.cons node_9716 (AllWinning.cons node_8731 (AllWinning.cons node_7711 (AllWinning.cons node_6712 (AllWinning.cons node_9741 (AllWinning.cons node_8800 (AllWinning.cons node_7790 (AllWinning.cons node_9746 (AllWinning.cons node_8805 (AllWinning.cons node_7806 (AllWinning.cons node_6880 (AllWinning.nil)))))))))))

theorem node_10804 : Outcome ⟨14, 3, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 6, 2⟩, ⟨12, 3, 6, 4⟩, ⟨11, 3, 6, 6⟩, ⟨10, 3, 6, 8⟩, ⟨9, 3, 6, 10⟩, ⟨8, 3, 6, 12⟩, ⟨14, 2, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨14, 0, 6, 6⟩, ⟨14, 3, 5, 2⟩, ⟨14, 3, 4, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 3, 2, 8⟩, ⟨14, 3, 1, 10⟩, ⟨14, 3, 0, 12⟩]
  exact AllWinning.cons node_9716 (AllWinning.cons node_8731 (AllWinning.cons node_7711 (AllWinning.cons node_6712 (AllWinning.cons node_5845 (AllWinning.cons node_5089 (AllWinning.cons node_9741 (AllWinning.cons node_8800 (AllWinning.cons node_7790 (AllWinning.cons node_9746 (AllWinning.cons node_8805 (AllWinning.cons node_7806 (AllWinning.cons node_6880 (AllWinning.cons node_5991 (AllWinning.cons node_5279 (AllWinning.nil)))))))))))))))

theorem node_10805 : Outcome ⟨14, 3, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 6, 2⟩, ⟨12, 3, 6, 4⟩, ⟨11, 3, 6, 6⟩, ⟨10, 3, 6, 8⟩, ⟨9, 3, 6, 10⟩, ⟨8, 3, 6, 12⟩, ⟨7, 3, 6, 14⟩, ⟨6, 3, 6, 16⟩, ⟨14, 2, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨14, 0, 6, 6⟩, ⟨14, 3, 5, 2⟩, ⟨14, 3, 4, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 3, 2, 8⟩, ⟨14, 3, 1, 10⟩, ⟨14, 3, 0, 12⟩]
  exact AllWinning.cons node_9716 (AllWinning.cons node_8731 (AllWinning.cons node_7711 (AllWinning.cons node_6712 (AllWinning.cons node_5845 (AllWinning.cons node_5089 (AllWinning.cons node_4341 (AllWinning.cons node_3702 (AllWinning.cons node_9741 (AllWinning.cons node_8800 (AllWinning.cons node_7790 (AllWinning.cons node_9746 (AllWinning.cons node_8805 (AllWinning.cons node_7806 (AllWinning.cons node_6880 (AllWinning.cons node_5991 (AllWinning.cons node_5279 (AllWinning.nil)))))))))))))))))

theorem node_10806 : Outcome ⟨14, 3, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 6, 2⟩, ⟨12, 3, 6, 4⟩, ⟨11, 3, 6, 6⟩, ⟨10, 3, 6, 8⟩, ⟨9, 3, 6, 10⟩, ⟨8, 3, 6, 12⟩, ⟨7, 3, 6, 14⟩, ⟨6, 3, 6, 16⟩, ⟨5, 3, 6, 18⟩, ⟨4, 3, 6, 20⟩, ⟨14, 2, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨14, 0, 6, 6⟩, ⟨14, 3, 5, 2⟩, ⟨14, 3, 4, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 3, 2, 8⟩, ⟨14, 3, 1, 10⟩, ⟨14, 3, 0, 12⟩]
  exact AllWinning.cons node_9716 (AllWinning.cons node_8731 (AllWinning.cons node_7711 (AllWinning.cons node_6712 (AllWinning.cons node_5845 (AllWinning.cons node_5089 (AllWinning.cons node_4341 (AllWinning.cons node_3702 (AllWinning.cons node_3099 (AllWinning.cons node_2598 (AllWinning.cons node_9741 (AllWinning.cons node_8800 (AllWinning.cons node_7790 (AllWinning.cons node_9746 (AllWinning.cons node_8805 (AllWinning.cons node_7806 (AllWinning.cons node_6880 (AllWinning.cons node_5991 (AllWinning.cons node_5279 (AllWinning.nil)))))))))))))))))))

theorem node_10807 : Outcome ⟨14, 3, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 6, 2⟩, ⟨12, 3, 6, 4⟩, ⟨11, 3, 6, 6⟩, ⟨10, 3, 6, 8⟩, ⟨9, 3, 6, 10⟩, ⟨8, 3, 6, 12⟩, ⟨7, 3, 6, 14⟩, ⟨6, 3, 6, 16⟩, ⟨5, 3, 6, 18⟩, ⟨4, 3, 6, 20⟩, ⟨3, 3, 6, 22⟩, ⟨2, 3, 6, 24⟩, ⟨14, 2, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨14, 0, 6, 6⟩, ⟨14, 3, 5, 2⟩, ⟨14, 3, 4, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 3, 2, 8⟩, ⟨14, 3, 1, 10⟩, ⟨14, 3, 0, 12⟩]
  exact AllWinning.cons node_9716 (AllWinning.cons node_8731 (AllWinning.cons node_7711 (AllWinning.cons node_6712 (AllWinning.cons node_5845 (AllWinning.cons node_5089 (AllWinning.cons node_4341 (AllWinning.cons node_3702 (AllWinning.cons node_3099 (AllWinning.cons node_2598 (AllWinning.cons node_2083 (AllWinning.cons node_1648 (AllWinning.cons node_9741 (AllWinning.cons node_8800 (AllWinning.cons node_7790 (AllWinning.cons node_9746 (AllWinning.cons node_8805 (AllWinning.cons node_7806 (AllWinning.cons node_6880 (AllWinning.cons node_5991 (AllWinning.cons node_5279 (AllWinning.nil)))))))))))))))))))))

theorem node_10808 : Outcome ⟨14, 3, 6, 20⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 26⟩) (by decide) node_1231

theorem node_10809 : Outcome ⟨14, 3, 6, 22⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 26⟩) (by decide) node_1231

theorem node_10810 : Outcome ⟨14, 4, 5, 4⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10811 : Outcome ⟨14, 4, 5, 6⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10812 : Outcome ⟨14, 4, 5, 10⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 14⟩) (by decide) node_4349

theorem node_10813 : Outcome ⟨14, 4, 5, 28⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 14⟩) (by decide) node_4349

theorem node_10814 : Outcome ⟨14, 5, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10815 : Outcome ⟨14, 5, 4, 6⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10816 : Outcome ⟨14, 5, 4, 10⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 14⟩) (by decide) node_4364

theorem node_10817 : Outcome ⟨14, 5, 4, 28⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 14⟩) (by decide) node_4364

theorem node_10818 : Outcome ⟨14, 6, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 6, 3, 2⟩, ⟨12, 6, 3, 4⟩, ⟨14, 5, 3, 2⟩, ⟨14, 4, 3, 4⟩, ⟨14, 6, 2, 2⟩, ⟨14, 6, 1, 4⟩]
  exact AllWinning.cons node_9725 (AllWinning.cons node_8742 (AllWinning.cons node_9754 (AllWinning.cons node_8809 (AllWinning.cons node_9758 (AllWinning.cons node_8815 (AllWinning.nil))))))

theorem node_10819 : Outcome ⟨14, 6, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 6, 3, 2⟩, ⟨12, 6, 3, 4⟩, ⟨11, 6, 3, 6⟩, ⟨10, 6, 3, 8⟩, ⟨14, 5, 3, 2⟩, ⟨14, 4, 3, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 2, 3, 8⟩, ⟨14, 6, 2, 2⟩, ⟨14, 6, 1, 4⟩, ⟨14, 6, 0, 6⟩]
  exact AllWinning.cons node_9725 (AllWinning.cons node_8742 (AllWinning.cons node_7720 (AllWinning.cons node_6723 (AllWinning.cons node_9754 (AllWinning.cons node_8809 (AllWinning.cons node_7806 (AllWinning.cons node_6876 (AllWinning.cons node_9758 (AllWinning.cons node_8815 (AllWinning.cons node_7822 (AllWinning.nil)))))))))))

theorem node_10820 : Outcome ⟨14, 6, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 6, 3, 2⟩, ⟨12, 6, 3, 4⟩, ⟨11, 6, 3, 6⟩, ⟨10, 6, 3, 8⟩, ⟨9, 6, 3, 10⟩, ⟨8, 6, 3, 12⟩, ⟨14, 5, 3, 2⟩, ⟨14, 4, 3, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 2, 3, 8⟩, ⟨14, 1, 3, 10⟩, ⟨14, 0, 3, 12⟩, ⟨14, 6, 2, 2⟩, ⟨14, 6, 1, 4⟩, ⟨14, 6, 0, 6⟩]
  exact AllWinning.cons node_9725 (AllWinning.cons node_8742 (AllWinning.cons node_7720 (AllWinning.cons node_6723 (AllWinning.cons node_5859 (AllWinning.cons node_5102 (AllWinning.cons node_9754 (AllWinning.cons node_8809 (AllWinning.cons node_7806 (AllWinning.cons node_6876 (AllWinning.cons node_5983 (AllWinning.cons node_5266 (AllWinning.cons node_9758 (AllWinning.cons node_8815 (AllWinning.cons node_7822 (AllWinning.nil)))))))))))))))

end RQ9F1
