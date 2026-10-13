import Chunk80
set_option autoImplicit false
namespace RQ9F1

theorem node_17511 : Outcome ⟨11, 17, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 2, 2⟩, ⟨9, 17, 2, 4⟩, ⟨8, 17, 2, 6⟩, ⟨7, 17, 2, 8⟩, ⟨6, 17, 2, 10⟩, ⟨5, 17, 2, 12⟩, ⟨4, 17, 2, 14⟩, ⟨3, 17, 2, 16⟩, ⟨2, 17, 2, 18⟩, ⟨1, 17, 2, 20⟩, ⟨11, 16, 2, 2⟩, ⟨11, 15, 2, 4⟩, ⟨11, 14, 2, 6⟩, ⟨11, 13, 2, 8⟩, ⟨11, 12, 2, 10⟩, ⟨11, 11, 2, 12⟩, ⟨11, 10, 2, 14⟩, ⟨11, 9, 2, 16⟩, ⟨11, 8, 2, 18⟩, ⟨11, 7, 2, 20⟩, ⟨11, 17, 1, 2⟩, ⟨11, 17, 0, 4⟩]
  exact AllWinning.cons node_16534 (AllWinning.cons node_15441 (AllWinning.cons node_14452 (AllWinning.cons node_13420 (AllWinning.cons node_12409 (AllWinning.cons node_11357 (AllWinning.cons node_10238 (AllWinning.cons node_9188 (AllWinning.cons node_8139 (AllWinning.cons node_7104 (AllWinning.cons node_16594 (AllWinning.cons node_15550 (AllWinning.cons node_14614 (AllWinning.cons node_13648 (AllWinning.cons node_12696 (AllWinning.cons node_11703 (AllWinning.cons node_10704 (AllWinning.cons node_9656 (AllWinning.cons node_8703 (AllWinning.cons node_7726 (AllWinning.cons node_16596 (AllWinning.cons node_15556 (AllWinning.nil))))))))))))))))))))))

theorem node_17512 : Outcome ⟨11, 18, 1, 6⟩ true :=
  Outcome.win (q := ⟨11, 15, 1, 6⟩) (by decide) node_14617

theorem node_17513 : Outcome ⟨11, 19, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 0, 2⟩, ⟨9, 19, 0, 4⟩, ⟨11, 18, 0, 2⟩, ⟨11, 17, 0, 4⟩]
  exact AllWinning.cons node_16539 (AllWinning.cons node_15446 (AllWinning.cons node_16598 (AllWinning.cons node_15556 (AllWinning.nil))))

theorem node_17514 : Outcome ⟨11, 19, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 0, 2⟩, ⟨9, 19, 0, 4⟩, ⟨8, 19, 0, 6⟩, ⟨7, 19, 0, 8⟩, ⟨11, 18, 0, 2⟩, ⟨11, 17, 0, 4⟩, ⟨11, 16, 0, 6⟩, ⟨11, 15, 0, 8⟩]
  exact AllWinning.cons node_16539 (AllWinning.cons node_15446 (AllWinning.cons node_14457 (AllWinning.cons node_13423 (AllWinning.cons node_16598 (AllWinning.cons node_15556 (AllWinning.cons node_14621 (AllWinning.cons node_13652 (AllWinning.nil))))))))

theorem node_17515 : Outcome ⟨11, 19, 0, 6⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 10⟩) (by decide) node_12417

theorem node_17516 : Outcome ⟨11, 19, 0, 16⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 16⟩) (by decide) node_9668

theorem node_17517 : Outcome ⟨12, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 18, 4⟩) (by decide) node_15449

theorem node_17518 : Outcome ⟨12, 0, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 18, 4⟩) (by decide) node_15449

theorem node_17519 : Outcome ⟨12, 0, 18, 10⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 12⟩) (by decide) node_11714

theorem node_17520 : Outcome ⟨12, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨12, 0, 17, 2⟩) (by decide) node_16601

theorem node_17521 : Outcome ⟨12, 1, 17, 4⟩ true :=
  Outcome.win (q := ⟨12, 0, 17, 2⟩) (by decide) node_16601

theorem node_17522 : Outcome ⟨12, 2, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 4⟩) (by decide) node_15455

theorem node_17523 : Outcome ⟨12, 2, 16, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 4⟩) (by decide) node_15455

theorem node_17524 : Outcome ⟨12, 2, 16, 12⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 4⟩) (by decide) node_15455

theorem node_17525 : Outcome ⟨12, 3, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 3, 15, 2⟩, ⟨10, 3, 15, 4⟩, ⟨12, 2, 15, 2⟩, ⟨12, 1, 15, 4⟩, ⟨12, 3, 14, 2⟩, ⟨12, 3, 13, 4⟩]
  exact AllWinning.cons node_16550 (AllWinning.cons node_15459 (AllWinning.cons node_16609 (AllWinning.cons node_15562 (AllWinning.cons node_16611 (AllWinning.cons node_15572 (AllWinning.nil))))))

theorem node_17526 : Outcome ⟨12, 3, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 3, 15, 2⟩, ⟨10, 3, 15, 4⟩, ⟨9, 3, 15, 6⟩, ⟨8, 3, 15, 8⟩, ⟨12, 2, 15, 2⟩, ⟨12, 1, 15, 4⟩, ⟨12, 0, 15, 6⟩, ⟨12, 3, 14, 2⟩, ⟨12, 3, 13, 4⟩, ⟨12, 3, 12, 6⟩, ⟨12, 3, 11, 8⟩]
  exact AllWinning.cons node_16550 (AllWinning.cons node_15459 (AllWinning.cons node_14469 (AllWinning.cons node_13438 (AllWinning.cons node_16609 (AllWinning.cons node_15562 (AllWinning.cons node_14625 (AllWinning.cons node_16611 (AllWinning.cons node_15572 (AllWinning.cons node_14634 (AllWinning.cons node_13666 (AllWinning.nil)))))))))))

theorem node_17527 : Outcome ⟨12, 3, 15, 8⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 12⟩) (by decide) node_11730

theorem node_17528 : Outcome ⟨12, 3, 15, 10⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 12⟩) (by decide) node_11730

theorem node_17529 : Outcome ⟨12, 3, 15, 12⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 12⟩) (by decide) node_11730

theorem node_17530 : Outcome ⟨12, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17531 : Outcome ⟨12, 4, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17532 : Outcome ⟨12, 4, 14, 8⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17533 : Outcome ⟨12, 4, 14, 14⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17534 : Outcome ⟨12, 5, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 2⟩) (by decide) node_16615

theorem node_17535 : Outcome ⟨12, 5, 13, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 6⟩) (by decide) node_14639

theorem node_17536 : Outcome ⟨12, 5, 13, 10⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 6⟩) (by decide) node_14639

theorem node_17537 : Outcome ⟨12, 6, 12, 2⟩ true :=
  Outcome.win (q := ⟨11, 6, 12, 2⟩) (by decide) node_16558

theorem node_17538 : Outcome ⟨12, 6, 12, 8⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 12⟩) (by decide) node_11714

theorem node_17539 : Outcome ⟨12, 6, 12, 10⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 12⟩) (by decide) node_11714

theorem node_17540 : Outcome ⟨12, 7, 11, 2⟩ true :=
  Outcome.win (q := ⟨12, 6, 11, 2⟩) (by decide) node_16623

theorem node_17541 : Outcome ⟨12, 7, 11, 8⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 8⟩) (by decide) node_13679

theorem node_17542 : Outcome ⟨12, 7, 11, 10⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 8⟩) (by decide) node_13679

theorem node_17543 : Outcome ⟨12, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 4⟩) (by decide) node_15584

theorem node_17544 : Outcome ⟨12, 8, 10, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 6⟩) (by decide) node_14639

theorem node_17545 : Outcome ⟨12, 9, 9, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 9, 2⟩) (by decide) node_16571

theorem node_17546 : Outcome ⟨12, 9, 9, 6⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 12⟩) (by decide) node_11730

theorem node_17547 : Outcome ⟨12, 9, 9, 8⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 12⟩) (by decide) node_11730

theorem node_17548 : Outcome ⟨12, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 4⟩) (by decide) node_15584

theorem node_17549 : Outcome ⟨12, 10, 8, 8⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 6⟩) (by decide) node_14656

theorem node_17550 : Outcome ⟨12, 11, 7, 2⟩ true :=
  Outcome.win (q := ⟨12, 11, 6, 2⟩) (by decide) node_16634

theorem node_17551 : Outcome ⟨12, 11, 7, 8⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 8⟩) (by decide) node_13679

theorem node_17552 : Outcome ⟨12, 11, 7, 10⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 8⟩) (by decide) node_13679

theorem node_17553 : Outcome ⟨12, 12, 6, 2⟩ true :=
  Outcome.win (q := ⟨11, 12, 6, 2⟩) (by decide) node_16581

theorem node_17554 : Outcome ⟨12, 12, 6, 8⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 12⟩) (by decide) node_11775

theorem node_17555 : Outcome ⟨12, 12, 6, 10⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 12⟩) (by decide) node_11775

theorem node_17556 : Outcome ⟨12, 13, 5, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 2⟩) (by decide) node_16641

theorem node_17557 : Outcome ⟨12, 13, 5, 8⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 6⟩) (by decide) node_14656

theorem node_17558 : Outcome ⟨12, 13, 5, 10⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 6⟩) (by decide) node_14656

theorem node_17559 : Outcome ⟨12, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17560 : Outcome ⟨12, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17561 : Outcome ⟨12, 14, 4, 8⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17562 : Outcome ⟨12, 14, 4, 14⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17563 : Outcome ⟨12, 15, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 15, 3, 2⟩, ⟨10, 15, 3, 4⟩, ⟨12, 14, 3, 2⟩, ⟨12, 13, 3, 4⟩, ⟨12, 15, 2, 2⟩, ⟨12, 15, 1, 4⟩]
  exact AllWinning.cons node_16590 (AllWinning.cons node_15494 (AllWinning.cons node_16647 (AllWinning.cons node_15597 (AllWinning.cons node_16651 (AllWinning.cons node_15606 (AllWinning.nil))))))

theorem node_17564 : Outcome ⟨12, 15, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 15, 3, 2⟩, ⟨10, 15, 3, 4⟩, ⟨9, 15, 3, 6⟩, ⟨8, 15, 3, 8⟩, ⟨12, 14, 3, 2⟩, ⟨12, 13, 3, 4⟩, ⟨12, 12, 3, 6⟩, ⟨12, 11, 3, 8⟩, ⟨12, 15, 2, 2⟩, ⟨12, 15, 1, 4⟩, ⟨12, 15, 0, 6⟩]
  exact AllWinning.cons node_16590 (AllWinning.cons node_15494 (AllWinning.cons node_14502 (AllWinning.cons node_13477 (AllWinning.cons node_16647 (AllWinning.cons node_15597 (AllWinning.cons node_14663 (AllWinning.cons node_13694 (AllWinning.cons node_16651 (AllWinning.cons node_15606 (AllWinning.cons node_14672 (AllWinning.nil)))))))))))

theorem node_17565 : Outcome ⟨12, 15, 3, 8⟩ true :=
  Outcome.win (q := ⟨12, 9, 3, 12⟩) (by decide) node_11760

theorem node_17566 : Outcome ⟨12, 15, 3, 10⟩ true :=
  Outcome.win (q := ⟨12, 9, 3, 12⟩) (by decide) node_11760

theorem node_17567 : Outcome ⟨12, 15, 3, 12⟩ true :=
  Outcome.win (q := ⟨12, 9, 3, 12⟩) (by decide) node_11760

theorem node_17568 : Outcome ⟨12, 16, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 4⟩) (by decide) node_15498

theorem node_17569 : Outcome ⟨12, 16, 2, 8⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 4⟩) (by decide) node_15498

theorem node_17570 : Outcome ⟨12, 16, 2, 12⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 4⟩) (by decide) node_15498

theorem node_17571 : Outcome ⟨12, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 2⟩) (by decide) node_16653

theorem node_17572 : Outcome ⟨12, 17, 1, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 2⟩) (by decide) node_16653

theorem node_17573 : Outcome ⟨12, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 0, 4⟩) (by decide) node_15505

theorem node_17574 : Outcome ⟨12, 18, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 0, 4⟩) (by decide) node_15505

theorem node_17575 : Outcome ⟨12, 18, 0, 10⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 12⟩) (by decide) node_11775

theorem node_17576 : Outcome ⟨13, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨12, 0, 17, 2⟩) (by decide) node_16601

theorem node_17577 : Outcome ⟨13, 0, 17, 8⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 8⟩) (by decide) node_13706

theorem node_17578 : Outcome ⟨13, 1, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 2⟩) (by decide) node_16605

theorem node_17579 : Outcome ⟨13, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 2⟩) (by decide) node_16605

theorem node_17580 : Outcome ⟨13, 2, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 2, 15, 2⟩, ⟨11, 2, 15, 4⟩, ⟨13, 1, 15, 2⟩, ⟨13, 0, 15, 4⟩, ⟨13, 2, 14, 2⟩, ⟨13, 2, 13, 4⟩]
  exact AllWinning.cons node_16609 (AllWinning.cons node_15514 (AllWinning.cons node_16663 (AllWinning.cons node_15612 (AllWinning.cons node_16666 (AllWinning.cons node_15618 (AllWinning.nil))))))

theorem node_17581 : Outcome ⟨13, 2, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 8⟩) (by decide) node_13498

theorem node_17582 : Outcome ⟨13, 2, 15, 8⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 8⟩) (by decide) node_13498

theorem node_17583 : Outcome ⟨13, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 14, 4⟩) (by decide) node_15517

theorem node_17584 : Outcome ⟨13, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17585 : Outcome ⟨13, 3, 14, 6⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17586 : Outcome ⟨13, 3, 14, 8⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17587 : Outcome ⟨13, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 2⟩) (by decide) node_16615

theorem node_17588 : Outcome ⟨13, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 8⟩) (by decide) node_13706

theorem node_17589 : Outcome ⟨13, 4, 13, 8⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 8⟩) (by decide) node_13706

theorem node_17590 : Outcome ⟨13, 4, 13, 18⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 8⟩) (by decide) node_13706

theorem node_17591 : Outcome ⟨13, 5, 12, 2⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 2⟩) (by decide) node_16672

theorem node_17592 : Outcome ⟨13, 5, 12, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 6⟩) (by decide) node_14530

theorem node_17593 : Outcome ⟨13, 5, 12, 10⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 6⟩) (by decide) node_14530

theorem node_17594 : Outcome ⟨13, 6, 11, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 11, 2⟩) (by decide) node_16623

theorem node_17595 : Outcome ⟨13, 6, 11, 6⟩ true :=
  Outcome.win (q := ⟨12, 6, 11, 2⟩) (by decide) node_16623

theorem node_17596 : Outcome ⟨13, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨13, 6, 10, 2⟩) (by decide) node_16683

theorem node_17597 : Outcome ⟨13, 7, 10, 6⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17598 : Outcome ⟨13, 7, 10, 8⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17599 : Outcome ⟨13, 7, 10, 16⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17600 : Outcome ⟨13, 8, 9, 2⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 2⟩) (by decide) node_16686

theorem node_17601 : Outcome ⟨13, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 2⟩) (by decide) node_16686

theorem node_17602 : Outcome ⟨13, 8, 9, 8⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 2⟩) (by decide) node_16686

theorem node_17603 : Outcome ⟨13, 9, 8, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 2⟩) (by decide) node_16697

theorem node_17604 : Outcome ⟨13, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 2⟩) (by decide) node_16697

theorem node_17605 : Outcome ⟨13, 9, 8, 8⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 2⟩) (by decide) node_16697

theorem node_17606 : Outcome ⟨13, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 2⟩) (by decide) node_16697

theorem node_17607 : Outcome ⟨13, 10, 7, 6⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

theorem node_17608 : Outcome ⟨13, 10, 7, 8⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

theorem node_17609 : Outcome ⟨13, 10, 7, 16⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

theorem node_17610 : Outcome ⟨13, 11, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 11, 6, 2⟩) (by decide) node_16634

theorem node_17611 : Outcome ⟨13, 11, 6, 6⟩ true :=
  Outcome.win (q := ⟨12, 11, 6, 2⟩) (by decide) node_16634

theorem node_17612 : Outcome ⟨13, 12, 5, 2⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 2⟩) (by decide) node_16709

theorem node_17613 : Outcome ⟨13, 12, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 6⟩) (by decide) node_14554

theorem node_17614 : Outcome ⟨13, 12, 5, 10⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 6⟩) (by decide) node_14554

theorem node_17615 : Outcome ⟨13, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 2⟩) (by decide) node_16641

theorem node_17616 : Outcome ⟨13, 13, 4, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 8⟩) (by decide) node_13764

theorem node_17617 : Outcome ⟨13, 13, 4, 8⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 8⟩) (by decide) node_13764

theorem node_17618 : Outcome ⟨13, 13, 4, 18⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 8⟩) (by decide) node_13764

theorem node_17619 : Outcome ⟨13, 14, 3, 2⟩ true :=
  Outcome.win (q := ⟨11, 14, 3, 4⟩) (by decide) node_15547

theorem node_17620 : Outcome ⟨13, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

theorem node_17621 : Outcome ⟨13, 14, 3, 6⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

theorem node_17622 : Outcome ⟨13, 14, 3, 8⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

theorem node_17623 : Outcome ⟨13, 15, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 2, 2⟩, ⟨11, 15, 2, 4⟩, ⟨13, 14, 2, 2⟩, ⟨13, 13, 2, 4⟩, ⟨13, 15, 1, 2⟩, ⟨13, 15, 0, 4⟩]
  exact AllWinning.cons node_16651 (AllWinning.cons node_15550 (AllWinning.cons node_16721 (AllWinning.cons node_15653 (AllWinning.cons node_16723 (AllWinning.cons node_15660 (AllWinning.nil))))))

theorem node_17624 : Outcome ⟨13, 15, 2, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 8⟩) (by decide) node_13535

theorem node_17625 : Outcome ⟨13, 15, 2, 8⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 8⟩) (by decide) node_13535

theorem node_17626 : Outcome ⟨13, 16, 1, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 2⟩) (by decide) node_16653

theorem node_17627 : Outcome ⟨13, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 2⟩) (by decide) node_16653

theorem node_17628 : Outcome ⟨13, 17, 0, 2⟩ true :=
  Outcome.win (q := ⟨12, 17, 0, 2⟩) (by decide) node_16657

theorem node_17629 : Outcome ⟨13, 17, 0, 8⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 8⟩) (by decide) node_13764

theorem node_17630 : Outcome ⟨14, 0, 16, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 4⟩) (by decide) node_15663

theorem node_17631 : Outcome ⟨14, 0, 16, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 4⟩) (by decide) node_15663

theorem node_17632 : Outcome ⟨14, 0, 16, 8⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 4⟩) (by decide) node_15663

theorem node_17633 : Outcome ⟨14, 1, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 15, 2⟩, ⟨12, 1, 15, 4⟩, ⟨14, 0, 15, 2⟩, ⟨14, 1, 14, 2⟩, ⟨14, 1, 13, 4⟩]
  exact AllWinning.cons node_16663 (AllWinning.cons node_15562 (AllWinning.cons node_16728 (AllWinning.cons node_16731 (AllWinning.cons node_15672 (AllWinning.nil)))))

theorem node_17634 : Outcome ⟨14, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨11, 1, 15, 6⟩) (by decide) node_14580

theorem node_17635 : Outcome ⟨14, 1, 15, 6⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 10⟩) (by decide) node_12780

theorem node_17636 : Outcome ⟨14, 1, 15, 14⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 10⟩) (by decide) node_12780

theorem node_17637 : Outcome ⟨14, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17638 : Outcome ⟨14, 2, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17639 : Outcome ⟨14, 2, 14, 6⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17640 : Outcome ⟨14, 2, 14, 14⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17641 : Outcome ⟨14, 2, 14, 24⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 4⟩) (by decide) node_15566

theorem node_17642 : Outcome ⟨14, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨14, 3, 11, 4⟩) (by decide) node_15684

theorem node_17643 : Outcome ⟨14, 3, 13, 4⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17644 : Outcome ⟨14, 3, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17645 : Outcome ⟨14, 3, 13, 8⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17646 : Outcome ⟨14, 4, 12, 2⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 4⟩) (by decide) node_15676

theorem node_17647 : Outcome ⟨14, 4, 12, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 4⟩) (by decide) node_15676

theorem node_17648 : Outcome ⟨14, 4, 12, 8⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 4⟩) (by decide) node_15676

theorem node_17649 : Outcome ⟨14, 4, 12, 14⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 4⟩) (by decide) node_15676

theorem node_17650 : Outcome ⟨14, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨14, 3, 11, 4⟩) (by decide) node_15684

theorem node_17651 : Outcome ⟨14, 5, 11, 6⟩ true :=
  Outcome.win (q := ⟨14, 3, 11, 4⟩) (by decide) node_15684

theorem node_17652 : Outcome ⟨14, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨14, 6, 8, 4⟩) (by decide) node_15695

theorem node_17653 : Outcome ⟨14, 6, 10, 6⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 10⟩) (by decide) node_12780

theorem node_17654 : Outcome ⟨14, 6, 10, 8⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 10⟩) (by decide) node_12780

theorem node_17655 : Outcome ⟨14, 7, 9, 2⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 4⟩) (by decide) node_15690

theorem node_17656 : Outcome ⟨14, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 4⟩) (by decide) node_15690

theorem node_17657 : Outcome ⟨14, 7, 9, 14⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 4⟩) (by decide) node_15690

theorem node_17658 : Outcome ⟨14, 8, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 4⟩) (by decide) node_15584

theorem node_17659 : Outcome ⟨14, 8, 8, 8⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 4⟩) (by decide) node_15584

theorem node_17660 : Outcome ⟨14, 8, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 28⟩) (by decide) node_3970

theorem node_17661 : Outcome ⟨14, 9, 7, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 4⟩) (by decide) node_15702

theorem node_17662 : Outcome ⟨14, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 4⟩) (by decide) node_15702

theorem node_17663 : Outcome ⟨14, 9, 7, 14⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 4⟩) (by decide) node_15702

theorem node_17664 : Outcome ⟨14, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨14, 8, 6, 4⟩) (by decide) node_15699

theorem node_17665 : Outcome ⟨14, 10, 6, 6⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 10⟩) (by decide) node_12813

theorem node_17666 : Outcome ⟨14, 10, 6, 8⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 10⟩) (by decide) node_12813

theorem node_17667 : Outcome ⟨14, 11, 5, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 4⟩) (by decide) node_15702

theorem node_17668 : Outcome ⟨14, 11, 5, 6⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 4⟩) (by decide) node_15702

theorem node_17669 : Outcome ⟨14, 12, 4, 2⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 4⟩) (by decide) node_15713

theorem node_17670 : Outcome ⟨14, 12, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 4⟩) (by decide) node_15713

theorem node_17671 : Outcome ⟨14, 12, 4, 8⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 4⟩) (by decide) node_15713

theorem node_17672 : Outcome ⟨14, 12, 4, 14⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 4⟩) (by decide) node_15713

theorem node_17673 : Outcome ⟨14, 13, 3, 2⟩ true :=
  Outcome.win (q := ⟨14, 11, 3, 4⟩) (by decide) node_15710

theorem node_17674 : Outcome ⟨14, 13, 3, 4⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17675 : Outcome ⟨14, 13, 3, 6⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17676 : Outcome ⟨14, 13, 3, 8⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17677 : Outcome ⟨14, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17678 : Outcome ⟨14, 14, 2, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17679 : Outcome ⟨14, 14, 2, 6⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17680 : Outcome ⟨14, 14, 2, 14⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17681 : Outcome ⟨14, 14, 2, 24⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 4⟩) (by decide) node_15600

theorem node_17682 : Outcome ⟨14, 15, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 1, 2⟩, ⟨12, 15, 1, 4⟩, ⟨14, 14, 1, 2⟩, ⟨14, 13, 1, 4⟩, ⟨14, 15, 0, 2⟩]
  exact AllWinning.cons node_16723 (AllWinning.cons node_15606 (AllWinning.cons node_16771 (AllWinning.cons node_15719 (AllWinning.cons node_16775 (AllWinning.nil)))))

theorem node_17683 : Outcome ⟨14, 15, 1, 4⟩ true :=
  Outcome.win (q := ⟨11, 15, 1, 6⟩) (by decide) node_14617

theorem node_17684 : Outcome ⟨14, 15, 1, 6⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 10⟩) (by decide) node_12813

theorem node_17685 : Outcome ⟨14, 15, 1, 14⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 10⟩) (by decide) node_12813

theorem node_17686 : Outcome ⟨14, 16, 0, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 4⟩) (by decide) node_15723

theorem node_17687 : Outcome ⟨14, 16, 0, 6⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 4⟩) (by decide) node_15723

theorem node_17688 : Outcome ⟨14, 16, 0, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 4⟩) (by decide) node_15723

theorem node_17689 : Outcome ⟨15, 0, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 15, 2⟩, ⟨13, 0, 15, 4⟩, ⟨15, 0, 14, 2⟩, ⟨15, 0, 13, 4⟩]
  exact AllWinning.cons node_16728 (AllWinning.cons node_15612 (AllWinning.cons node_16778 (AllWinning.cons node_15731 (AllWinning.nil))))

theorem node_17690 : Outcome ⟨15, 0, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 15, 2⟩, ⟨13, 0, 15, 4⟩, ⟨12, 0, 15, 6⟩, ⟨11, 0, 15, 8⟩, ⟨15, 0, 14, 2⟩, ⟨15, 0, 13, 4⟩, ⟨15, 0, 12, 6⟩, ⟨15, 0, 11, 8⟩]
  exact AllWinning.cons node_16728 (AllWinning.cons node_15612 (AllWinning.cons node_14625 (AllWinning.cons node_13601 (AllWinning.cons node_16778 (AllWinning.cons node_15731 (AllWinning.cons node_14751 (AllWinning.cons node_13799 (AllWinning.nil))))))))

theorem node_17691 : Outcome ⟨15, 0, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 15, 2⟩, ⟨13, 0, 15, 4⟩, ⟨12, 0, 15, 6⟩, ⟨11, 0, 15, 8⟩, ⟨10, 0, 15, 10⟩, ⟨9, 0, 15, 12⟩, ⟨15, 0, 14, 2⟩, ⟨15, 0, 13, 4⟩, ⟨15, 0, 12, 6⟩, ⟨15, 0, 11, 8⟩, ⟨15, 0, 10, 10⟩, ⟨15, 0, 9, 12⟩]
  exact AllWinning.cons node_16728 (AllWinning.cons node_15612 (AllWinning.cons node_14625 (AllWinning.cons node_13601 (AllWinning.cons node_12595 (AllWinning.cons node_11555 (AllWinning.cons node_16778 (AllWinning.cons node_15731 (AllWinning.cons node_14751 (AllWinning.cons node_13799 (AllWinning.cons node_12824 (AllWinning.cons node_11838 (AllWinning.nil))))))))))))

theorem node_17692 : Outcome ⟨15, 0, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 15, 2⟩, ⟨13, 0, 15, 4⟩, ⟨12, 0, 15, 6⟩, ⟨11, 0, 15, 8⟩, ⟨10, 0, 15, 10⟩, ⟨9, 0, 15, 12⟩, ⟨8, 0, 15, 14⟩, ⟨7, 0, 15, 16⟩, ⟨15, 0, 14, 2⟩, ⟨15, 0, 13, 4⟩, ⟨15, 0, 12, 6⟩, ⟨15, 0, 11, 8⟩, ⟨15, 0, 10, 10⟩, ⟨15, 0, 9, 12⟩, ⟨15, 0, 8, 14⟩, ⟨15, 0, 7, 16⟩]
  exact AllWinning.cons node_16728 (AllWinning.cons node_15612 (AllWinning.cons node_14625 (AllWinning.cons node_13601 (AllWinning.cons node_12595 (AllWinning.cons node_11555 (AllWinning.cons node_10494 (AllWinning.cons node_9408 (AllWinning.cons node_16778 (AllWinning.cons node_15731 (AllWinning.cons node_14751 (AllWinning.cons node_13799 (AllWinning.cons node_12824 (AllWinning.cons node_11838 (AllWinning.cons node_10839 (AllWinning.cons node_9770 (AllWinning.nil))))))))))))))))

theorem node_17693 : Outcome ⟨15, 0, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 15, 2⟩, ⟨13, 0, 15, 4⟩, ⟨12, 0, 15, 6⟩, ⟨11, 0, 15, 8⟩, ⟨10, 0, 15, 10⟩, ⟨9, 0, 15, 12⟩, ⟨8, 0, 15, 14⟩, ⟨7, 0, 15, 16⟩, ⟨6, 0, 15, 18⟩, ⟨5, 0, 15, 20⟩, ⟨15, 0, 14, 2⟩, ⟨15, 0, 13, 4⟩, ⟨15, 0, 12, 6⟩, ⟨15, 0, 11, 8⟩, ⟨15, 0, 10, 10⟩, ⟨15, 0, 9, 12⟩, ⟨15, 0, 8, 14⟩, ⟨15, 0, 7, 16⟩, ⟨15, 0, 6, 18⟩, ⟨15, 0, 5, 20⟩]
  exact AllWinning.cons node_16728 (AllWinning.cons node_15612 (AllWinning.cons node_14625 (AllWinning.cons node_13601 (AllWinning.cons node_12595 (AllWinning.cons node_11555 (AllWinning.cons node_10494 (AllWinning.cons node_9408 (AllWinning.cons node_8345 (AllWinning.cons node_7354 (AllWinning.cons node_16778 (AllWinning.cons node_15731 (AllWinning.cons node_14751 (AllWinning.cons node_13799 (AllWinning.cons node_12824 (AllWinning.cons node_11838 (AllWinning.cons node_10839 (AllWinning.cons node_9770 (AllWinning.cons node_8824 (AllWinning.cons node_7829 (AllWinning.nil))))))))))))))))))))

theorem node_17694 : Outcome ⟨15, 0, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 15, 2⟩, ⟨13, 0, 15, 4⟩, ⟨12, 0, 15, 6⟩, ⟨11, 0, 15, 8⟩, ⟨10, 0, 15, 10⟩, ⟨9, 0, 15, 12⟩, ⟨8, 0, 15, 14⟩, ⟨7, 0, 15, 16⟩, ⟨6, 0, 15, 18⟩, ⟨5, 0, 15, 20⟩, ⟨4, 0, 15, 22⟩, ⟨3, 0, 15, 24⟩, ⟨15, 0, 14, 2⟩, ⟨15, 0, 13, 4⟩, ⟨15, 0, 12, 6⟩, ⟨15, 0, 11, 8⟩, ⟨15, 0, 10, 10⟩, ⟨15, 0, 9, 12⟩, ⟨15, 0, 8, 14⟩, ⟨15, 0, 7, 16⟩, ⟨15, 0, 6, 18⟩, ⟨15, 0, 5, 20⟩, ⟨15, 0, 4, 22⟩, ⟨15, 0, 3, 24⟩]
  exact AllWinning.cons node_16728 (AllWinning.cons node_15612 (AllWinning.cons node_14625 (AllWinning.cons node_13601 (AllWinning.cons node_12595 (AllWinning.cons node_11555 (AllWinning.cons node_10494 (AllWinning.cons node_9408 (AllWinning.cons node_8345 (AllWinning.cons node_7354 (AllWinning.cons node_6371 (AllWinning.cons node_5522 (AllWinning.cons node_16778 (AllWinning.cons node_15731 (AllWinning.cons node_14751 (AllWinning.cons node_13799 (AllWinning.cons node_12824 (AllWinning.cons node_11838 (AllWinning.cons node_10839 (AllWinning.cons node_9770 (AllWinning.cons node_8824 (AllWinning.cons node_7829 (AllWinning.cons node_6892 (AllWinning.cons node_6000 (AllWinning.nil))))))))))))))))))))))))

theorem node_17695 : Outcome ⟨15, 1, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 14, 2⟩, ⟨13, 1, 14, 4⟩, ⟨15, 0, 14, 2⟩, ⟨15, 1, 13, 2⟩, ⟨15, 1, 12, 4⟩]
  exact AllWinning.cons node_16731 (AllWinning.cons node_15615 (AllWinning.cons node_16778 (AllWinning.cons node_16781 (AllWinning.cons node_15734 (AllWinning.nil)))))

theorem node_17696 : Outcome ⟨15, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨15, 1, 11, 6⟩) (by decide) node_14755

theorem node_17697 : Outcome ⟨15, 1, 14, 6⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 10⟩) (by decide) node_12600

theorem node_17698 : Outcome ⟨15, 1, 14, 14⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 10⟩) (by decide) node_12600

theorem node_17699 : Outcome ⟨15, 2, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 2, 13, 2⟩, ⟨13, 2, 13, 4⟩, ⟨15, 1, 13, 2⟩, ⟨15, 0, 13, 4⟩, ⟨15, 2, 12, 2⟩, ⟨15, 2, 11, 4⟩]
  exact AllWinning.cons node_16735 (AllWinning.cons node_15618 (AllWinning.cons node_16781 (AllWinning.cons node_15731 (AllWinning.cons node_16784 (AllWinning.cons node_15737 (AllWinning.nil))))))

theorem node_17700 : Outcome ⟨15, 2, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 8⟩) (by decide) node_13806

theorem node_17701 : Outcome ⟨15, 2, 13, 8⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 8⟩) (by decide) node_13806

theorem node_17702 : Outcome ⟨15, 3, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 12, 2⟩, ⟨13, 3, 12, 4⟩, ⟨12, 3, 12, 6⟩, ⟨11, 3, 12, 8⟩, ⟨15, 2, 12, 2⟩, ⟨15, 1, 12, 4⟩, ⟨15, 0, 12, 6⟩, ⟨15, 3, 11, 2⟩, ⟨15, 3, 10, 4⟩, ⟨15, 3, 9, 6⟩, ⟨15, 3, 8, 8⟩]
  exact AllWinning.cons node_16737 (AllWinning.cons node_15623 (AllWinning.cons node_14634 (AllWinning.cons node_13612 (AllWinning.cons node_16784 (AllWinning.cons node_15734 (AllWinning.cons node_14751 (AllWinning.cons node_16786 (AllWinning.cons node_15739 (AllWinning.cons node_14759 (AllWinning.cons node_13813 (AllWinning.nil)))))))))))

theorem node_17703 : Outcome ⟨15, 3, 12, 8⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 12⟩) (by decide) node_11566

theorem node_17704 : Outcome ⟨15, 3, 12, 12⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 12⟩) (by decide) node_11566

theorem node_17705 : Outcome ⟨15, 4, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 11, 2⟩, ⟨13, 4, 11, 4⟩, ⟨15, 3, 11, 2⟩, ⟨15, 2, 11, 4⟩, ⟨15, 4, 10, 2⟩, ⟨15, 4, 9, 4⟩]
  exact AllWinning.cons node_16740 (AllWinning.cons node_15626 (AllWinning.cons node_16786 (AllWinning.cons node_15737 (AllWinning.cons node_16790 (AllWinning.cons node_15743 (AllWinning.nil))))))

theorem node_17706 : Outcome ⟨15, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨15, 1, 11, 6⟩) (by decide) node_14755

theorem node_17707 : Outcome ⟨15, 4, 11, 6⟩ true :=
  Outcome.win (q := ⟨15, 1, 11, 6⟩) (by decide) node_14755

theorem node_17708 : Outcome ⟨15, 4, 11, 12⟩ true :=
  Outcome.win (q := ⟨15, 1, 11, 6⟩) (by decide) node_14755

theorem node_17709 : Outcome ⟨15, 5, 10, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 4⟩) (by decide) node_15745

theorem node_17710 : Outcome ⟨15, 5, 10, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 6⟩) (by decide) node_14639

theorem node_17711 : Outcome ⟨15, 6, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 6, 9, 2⟩, ⟨13, 6, 9, 4⟩, ⟨15, 5, 9, 2⟩, ⟨15, 4, 9, 4⟩, ⟨15, 6, 8, 2⟩, ⟨15, 6, 7, 4⟩]
  exact AllWinning.cons node_16746 (AllWinning.cons node_15633 (AllWinning.cons node_16791 (AllWinning.cons node_15743 (AllWinning.cons node_16793 (AllWinning.cons node_15755 (AllWinning.nil))))))

theorem node_17712 : Outcome ⟨15, 6, 9, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 8⟩) (by decide) node_13806

theorem node_17713 : Outcome ⟨15, 6, 9, 6⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 8⟩) (by decide) node_13806

theorem node_17714 : Outcome ⟨15, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 4⟩) (by decide) node_15745

theorem node_17715 : Outcome ⟨15, 7, 8, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 4⟩) (by decide) node_15745

theorem node_17716 : Outcome ⟨15, 7, 8, 8⟩ true :=
  Outcome.win (q := ⟨15, 7, 3, 10⟩) (by decide) node_12851

theorem node_17717 : Outcome ⟨15, 7, 8, 14⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 18⟩) (by decide) node_8375

theorem node_17718 : Outcome ⟨15, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 4⟩) (by decide) node_15762

theorem node_17719 : Outcome ⟨15, 8, 7, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 4⟩) (by decide) node_15762

theorem node_17720 : Outcome ⟨15, 8, 7, 8⟩ true :=
  Outcome.win (q := ⟨15, 3, 7, 10⟩) (by decide) node_12836

theorem node_17721 : Outcome ⟨15, 8, 7, 14⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 18⟩) (by decide) node_8387

theorem node_17722 : Outcome ⟨15, 9, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 6, 2⟩, ⟨13, 9, 6, 4⟩, ⟨15, 8, 6, 2⟩, ⟨15, 7, 6, 4⟩, ⟨15, 9, 5, 2⟩, ⟨15, 9, 4, 4⟩]
  exact AllWinning.cons node_16755 (AllWinning.cons node_15641 (AllWinning.cons node_16798 (AllWinning.cons node_15759 (AllWinning.cons node_16802 (AllWinning.cons node_15772 (AllWinning.nil))))))

theorem node_17723 : Outcome ⟨15, 9, 6, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 8⟩) (by decide) node_13830

theorem node_17724 : Outcome ⟨15, 9, 6, 6⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 8⟩) (by decide) node_13830

theorem node_17725 : Outcome ⟨15, 10, 5, 2⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 4⟩) (by decide) node_15762

theorem node_17726 : Outcome ⟨15, 10, 5, 8⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 6⟩) (by decide) node_14656

theorem node_17727 : Outcome ⟨15, 11, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 4, 2⟩, ⟨13, 11, 4, 4⟩, ⟨15, 10, 4, 2⟩, ⟨15, 9, 4, 4⟩, ⟨15, 11, 3, 2⟩, ⟨15, 11, 2, 4⟩]
  exact AllWinning.cons node_16763 (AllWinning.cons node_15648 (AllWinning.cons node_16804 (AllWinning.cons node_15772 (AllWinning.cons node_16805 (AllWinning.cons node_15777 (AllWinning.nil))))))

theorem node_17728 : Outcome ⟨15, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨15, 11, 1, 6⟩) (by decide) node_14781

theorem node_17729 : Outcome ⟨15, 11, 4, 6⟩ true :=
  Outcome.win (q := ⟨15, 11, 1, 6⟩) (by decide) node_14781

theorem node_17730 : Outcome ⟨15, 11, 4, 12⟩ true :=
  Outcome.win (q := ⟨15, 11, 1, 6⟩) (by decide) node_14781

theorem node_17731 : Outcome ⟨15, 12, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 12, 3, 2⟩, ⟨13, 12, 3, 4⟩, ⟨15, 11, 3, 2⟩, ⟨15, 10, 3, 4⟩, ⟨15, 12, 2, 2⟩, ⟨15, 12, 1, 4⟩]
  exact AllWinning.cons node_16766 (AllWinning.cons node_15651 (AllWinning.cons node_16805 (AllWinning.cons node_15774 (AllWinning.cons node_16809 (AllWinning.cons node_15780 (AllWinning.nil))))))

theorem node_17732 : Outcome ⟨15, 12, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 12, 3, 2⟩, ⟨13, 12, 3, 4⟩, ⟨12, 12, 3, 6⟩, ⟨11, 12, 3, 8⟩, ⟨15, 11, 3, 2⟩, ⟨15, 10, 3, 4⟩, ⟨15, 9, 3, 6⟩, ⟨15, 8, 3, 8⟩, ⟨15, 12, 2, 2⟩, ⟨15, 12, 1, 4⟩, ⟨15, 12, 0, 6⟩]
  exact AllWinning.cons node_16766 (AllWinning.cons node_15651 (AllWinning.cons node_14663 (AllWinning.cons node_13643 (AllWinning.cons node_16805 (AllWinning.cons node_15774 (AllWinning.cons node_14775 (AllWinning.cons node_13825 (AllWinning.cons node_16809 (AllWinning.cons node_15780 (AllWinning.cons node_14784 (AllWinning.nil)))))))))))

theorem node_17733 : Outcome ⟨15, 12, 3, 8⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 12⟩) (by decide) node_11599

theorem node_17734 : Outcome ⟨15, 12, 3, 12⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 12⟩) (by decide) node_11599

theorem node_17735 : Outcome ⟨15, 13, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 2, 2⟩, ⟨13, 13, 2, 4⟩, ⟨15, 12, 2, 2⟩, ⟨15, 11, 2, 4⟩, ⟨15, 13, 1, 2⟩, ⟨15, 13, 0, 4⟩]
  exact AllWinning.cons node_16769 (AllWinning.cons node_15653 (AllWinning.cons node_16809 (AllWinning.cons node_15777 (AllWinning.cons node_16811 (AllWinning.cons node_15783 (AllWinning.nil))))))

theorem node_17736 : Outcome ⟨15, 13, 2, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 8⟩) (by decide) node_13830

theorem node_17737 : Outcome ⟨15, 13, 2, 8⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 8⟩) (by decide) node_13830

theorem node_17738 : Outcome ⟨15, 14, 1, 4⟩ true :=
  Outcome.win (q := ⟨15, 11, 1, 6⟩) (by decide) node_14781

theorem node_17739 : Outcome ⟨15, 14, 1, 6⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 10⟩) (by decide) node_12643

theorem node_17740 : Outcome ⟨15, 14, 1, 14⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 10⟩) (by decide) node_12643

theorem node_17741 : Outcome ⟨15, 15, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 0, 2⟩, ⟨13, 15, 0, 4⟩, ⟨15, 14, 0, 2⟩, ⟨15, 13, 0, 4⟩]
  exact AllWinning.cons node_16775 (AllWinning.cons node_15660 (AllWinning.cons node_16814 (AllWinning.cons node_15783 (AllWinning.nil))))

theorem node_17742 : Outcome ⟨15, 15, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 0, 2⟩, ⟨13, 15, 0, 4⟩, ⟨12, 15, 0, 6⟩, ⟨11, 15, 0, 8⟩, ⟨15, 14, 0, 2⟩, ⟨15, 13, 0, 4⟩, ⟨15, 12, 0, 6⟩, ⟨15, 11, 0, 8⟩]
  exact AllWinning.cons node_16775 (AllWinning.cons node_15660 (AllWinning.cons node_14672 (AllWinning.cons node_13652 (AllWinning.cons node_16814 (AllWinning.cons node_15783 (AllWinning.cons node_14784 (AllWinning.cons node_13837 (AllWinning.nil))))))))

theorem node_17743 : Outcome ⟨15, 15, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 0, 2⟩, ⟨13, 15, 0, 4⟩, ⟨12, 15, 0, 6⟩, ⟨11, 15, 0, 8⟩, ⟨10, 15, 0, 10⟩, ⟨9, 15, 0, 12⟩, ⟨15, 14, 0, 2⟩, ⟨15, 13, 0, 4⟩, ⟨15, 12, 0, 6⟩, ⟨15, 11, 0, 8⟩, ⟨15, 10, 0, 10⟩, ⟨15, 9, 0, 12⟩]
  exact AllWinning.cons node_16775 (AllWinning.cons node_15660 (AllWinning.cons node_14672 (AllWinning.cons node_13652 (AllWinning.cons node_12651 (AllWinning.cons node_11609 (AllWinning.cons node_16814 (AllWinning.cons node_15783 (AllWinning.cons node_14784 (AllWinning.cons node_13837 (AllWinning.cons node_12865 (AllWinning.cons node_11867 (AllWinning.nil))))))))))))

theorem node_17744 : Outcome ⟨15, 15, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 0, 2⟩, ⟨13, 15, 0, 4⟩, ⟨12, 15, 0, 6⟩, ⟨11, 15, 0, 8⟩, ⟨10, 15, 0, 10⟩, ⟨9, 15, 0, 12⟩, ⟨8, 15, 0, 14⟩, ⟨7, 15, 0, 16⟩, ⟨15, 14, 0, 2⟩, ⟨15, 13, 0, 4⟩, ⟨15, 12, 0, 6⟩, ⟨15, 11, 0, 8⟩, ⟨15, 10, 0, 10⟩, ⟨15, 9, 0, 12⟩, ⟨15, 8, 0, 14⟩, ⟨15, 7, 0, 16⟩]
  exact AllWinning.cons node_16775 (AllWinning.cons node_15660 (AllWinning.cons node_14672 (AllWinning.cons node_13652 (AllWinning.cons node_12651 (AllWinning.cons node_11609 (AllWinning.cons node_10551 (AllWinning.cons node_9466 (AllWinning.cons node_16814 (AllWinning.cons node_15783 (AllWinning.cons node_14784 (AllWinning.cons node_13837 (AllWinning.cons node_12865 (AllWinning.cons node_11867 (AllWinning.cons node_10868 (AllWinning.cons node_9797 (AllWinning.nil))))))))))))))))

theorem node_17745 : Outcome ⟨15, 15, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 0, 2⟩, ⟨13, 15, 0, 4⟩, ⟨12, 15, 0, 6⟩, ⟨11, 15, 0, 8⟩, ⟨10, 15, 0, 10⟩, ⟨9, 15, 0, 12⟩, ⟨8, 15, 0, 14⟩, ⟨7, 15, 0, 16⟩, ⟨6, 15, 0, 18⟩, ⟨5, 15, 0, 20⟩, ⟨15, 14, 0, 2⟩, ⟨15, 13, 0, 4⟩, ⟨15, 12, 0, 6⟩, ⟨15, 11, 0, 8⟩, ⟨15, 10, 0, 10⟩, ⟨15, 9, 0, 12⟩, ⟨15, 8, 0, 14⟩, ⟨15, 7, 0, 16⟩, ⟨15, 6, 0, 18⟩, ⟨15, 5, 0, 20⟩]
  exact AllWinning.cons node_16775 (AllWinning.cons node_15660 (AllWinning.cons node_14672 (AllWinning.cons node_13652 (AllWinning.cons node_12651 (AllWinning.cons node_11609 (AllWinning.cons node_10551 (AllWinning.cons node_9466 (AllWinning.cons node_8413 (AllWinning.cons node_7408 (AllWinning.cons node_16814 (AllWinning.cons node_15783 (AllWinning.cons node_14784 (AllWinning.cons node_13837 (AllWinning.cons node_12865 (AllWinning.cons node_11867 (AllWinning.cons node_10868 (AllWinning.cons node_9797 (AllWinning.cons node_8847 (AllWinning.cons node_7855 (AllWinning.nil))))))))))))))))))))

theorem node_17746 : Outcome ⟨15, 15, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 0, 2⟩, ⟨13, 15, 0, 4⟩, ⟨12, 15, 0, 6⟩, ⟨11, 15, 0, 8⟩, ⟨10, 15, 0, 10⟩, ⟨9, 15, 0, 12⟩, ⟨8, 15, 0, 14⟩, ⟨7, 15, 0, 16⟩, ⟨6, 15, 0, 18⟩, ⟨5, 15, 0, 20⟩, ⟨4, 15, 0, 22⟩, ⟨3, 15, 0, 24⟩, ⟨15, 14, 0, 2⟩, ⟨15, 13, 0, 4⟩, ⟨15, 12, 0, 6⟩, ⟨15, 11, 0, 8⟩, ⟨15, 10, 0, 10⟩, ⟨15, 9, 0, 12⟩, ⟨15, 8, 0, 14⟩, ⟨15, 7, 0, 16⟩, ⟨15, 6, 0, 18⟩, ⟨15, 5, 0, 20⟩, ⟨15, 4, 0, 22⟩, ⟨15, 3, 0, 24⟩]
  exact AllWinning.cons node_16775 (AllWinning.cons node_15660 (AllWinning.cons node_14672 (AllWinning.cons node_13652 (AllWinning.cons node_12651 (AllWinning.cons node_11609 (AllWinning.cons node_10551 (AllWinning.cons node_9466 (AllWinning.cons node_8413 (AllWinning.cons node_7408 (AllWinning.cons node_6421 (AllWinning.cons node_5575 (AllWinning.cons node_16814 (AllWinning.cons node_15783 (AllWinning.cons node_14784 (AllWinning.cons node_13837 (AllWinning.cons node_12865 (AllWinning.cons node_11867 (AllWinning.cons node_10868 (AllWinning.cons node_9797 (AllWinning.cons node_8847 (AllWinning.cons node_7855 (AllWinning.cons node_6907 (AllWinning.cons node_6012 (AllWinning.nil))))))))))))))))))))))))

theorem node_17747 : Outcome ⟨16, 0, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 4⟩) (by decide) node_15663

theorem node_17748 : Outcome ⟨16, 0, 14, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 4⟩) (by decide) node_15663

theorem node_17749 : Outcome ⟨16, 0, 14, 8⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 4⟩) (by decide) node_15663

theorem node_17750 : Outcome ⟨16, 0, 14, 20⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 4⟩) (by decide) node_15663

theorem node_17751 : Outcome ⟨16, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 2⟩) (by decide) node_16819

theorem node_17752 : Outcome ⟨16, 1, 13, 4⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 2⟩) (by decide) node_16819

theorem node_17753 : Outcome ⟨16, 2, 12, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 4⟩) (by decide) node_15676

theorem node_17754 : Outcome ⟨16, 2, 12, 8⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 4⟩) (by decide) node_15676

theorem node_17755 : Outcome ⟨16, 2, 12, 12⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 4⟩) (by decide) node_15676

theorem node_17756 : Outcome ⟨16, 3, 11, 4⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 6⟩) (by decide) node_14799

theorem node_17757 : Outcome ⟨16, 3, 11, 6⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 6⟩) (by decide) node_14799

theorem node_17758 : Outcome ⟨16, 3, 11, 8⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 6⟩) (by decide) node_14799

theorem node_17759 : Outcome ⟨16, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 4⟩) (by decide) node_15792

theorem node_17760 : Outcome ⟨16, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 4⟩) (by decide) node_15792

theorem node_17761 : Outcome ⟨16, 4, 10, 8⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 4⟩) (by decide) node_15792

theorem node_17762 : Outcome ⟨16, 4, 10, 20⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 20⟩) (by decide) node_7435

theorem node_17763 : Outcome ⟨16, 5, 9, 2⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 4⟩) (by decide) node_15690

theorem node_17764 : Outcome ⟨16, 5, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 4⟩) (by decide) node_15690

theorem node_17765 : Outcome ⟨16, 6, 8, 8⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 6⟩) (by decide) node_14799

theorem node_17766 : Outcome ⟨16, 7, 7, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 8⟩) (by decide) node_13679

theorem node_17767 : Outcome ⟨16, 7, 7, 8⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 8⟩) (by decide) node_13679

theorem node_17768 : Outcome ⟨16, 8, 6, 8⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 6⟩) (by decide) node_14817

theorem node_17769 : Outcome ⟨16, 9, 5, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 4⟩) (by decide) node_15702

theorem node_17770 : Outcome ⟨16, 9, 5, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 4⟩) (by decide) node_15702

theorem node_17771 : Outcome ⟨16, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 4⟩) (by decide) node_15810

theorem node_17772 : Outcome ⟨16, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 4⟩) (by decide) node_15810

theorem node_17773 : Outcome ⟨16, 10, 4, 8⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 4⟩) (by decide) node_15810

theorem node_17774 : Outcome ⟨16, 10, 4, 20⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 20⟩) (by decide) node_7464

theorem node_17775 : Outcome ⟨16, 11, 3, 4⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 6⟩) (by decide) node_14817

theorem node_17776 : Outcome ⟨16, 11, 3, 6⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 6⟩) (by decide) node_14817

theorem node_17777 : Outcome ⟨16, 11, 3, 8⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 6⟩) (by decide) node_14817

theorem node_17778 : Outcome ⟨16, 12, 2, 4⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 4⟩) (by decide) node_15713

theorem node_17779 : Outcome ⟨16, 12, 2, 8⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 4⟩) (by decide) node_15713

theorem node_17780 : Outcome ⟨16, 12, 2, 12⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 4⟩) (by decide) node_15713

theorem node_17781 : Outcome ⟨16, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 2⟩) (by decide) node_16859

theorem node_17782 : Outcome ⟨16, 13, 1, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 2⟩) (by decide) node_16859

theorem node_17783 : Outcome ⟨16, 14, 0, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 4⟩) (by decide) node_15723

theorem node_17784 : Outcome ⟨16, 14, 0, 6⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 4⟩) (by decide) node_15723

theorem node_17785 : Outcome ⟨16, 14, 0, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 4⟩) (by decide) node_15723

theorem node_17786 : Outcome ⟨16, 14, 0, 20⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 4⟩) (by decide) node_15723

theorem node_17787 : Outcome ⟨17, 0, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 0, 12, 2⟩) (by decide) node_16865

theorem node_17788 : Outcome ⟨17, 0, 13, 8⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 8⟩) (by decide) node_13706

theorem node_17789 : Outcome ⟨17, 1, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 2⟩) (by decide) node_16819

theorem node_17790 : Outcome ⟨17, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 2⟩) (by decide) node_16819

theorem node_17791 : Outcome ⟨17, 2, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 11, 2⟩, ⟨15, 2, 11, 4⟩, ⟨17, 1, 11, 2⟩, ⟨17, 0, 11, 4⟩, ⟨17, 2, 10, 2⟩, ⟨17, 2, 9, 4⟩]
  exact AllWinning.cons node_16823 (AllWinning.cons node_15737 (AllWinning.cons node_16868 (AllWinning.cons node_15822 (AllWinning.cons node_16870 (AllWinning.cons node_15827 (AllWinning.nil))))))

theorem node_17792 : Outcome ⟨17, 2, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 11, 2⟩, ⟨15, 2, 11, 4⟩, ⟨14, 2, 11, 6⟩, ⟨13, 2, 11, 8⟩, ⟨17, 1, 11, 2⟩, ⟨17, 0, 11, 4⟩, ⟨17, 2, 10, 2⟩, ⟨17, 2, 9, 4⟩, ⟨17, 2, 8, 6⟩, ⟨17, 2, 7, 8⟩]
  exact AllWinning.cons node_16823 (AllWinning.cons node_15737 (AllWinning.cons node_14717 (AllWinning.cons node_13719 (AllWinning.cons node_16868 (AllWinning.cons node_15822 (AllWinning.cons node_16870 (AllWinning.cons node_15827 (AllWinning.cons node_14842 (AllWinning.cons node_13881 (AllWinning.nil))))))))))

theorem node_17793 : Outcome ⟨17, 2, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 11, 2⟩, ⟨15, 2, 11, 4⟩, ⟨14, 2, 11, 6⟩, ⟨13, 2, 11, 8⟩, ⟨12, 2, 11, 10⟩, ⟨11, 2, 11, 12⟩, ⟨10, 2, 11, 14⟩, ⟨9, 2, 11, 16⟩, ⟨17, 1, 11, 2⟩, ⟨17, 0, 11, 4⟩, ⟨17, 2, 10, 2⟩, ⟨17, 2, 9, 4⟩, ⟨17, 2, 8, 6⟩, ⟨17, 2, 7, 8⟩, ⟨17, 2, 6, 10⟩, ⟨17, 2, 5, 12⟩, ⟨17, 2, 4, 14⟩, ⟨17, 2, 3, 16⟩]
  exact AllWinning.cons node_16823 (AllWinning.cons node_15737 (AllWinning.cons node_14717 (AllWinning.cons node_13719 (AllWinning.cons node_12711 (AllWinning.cons node_11664 (AllWinning.cons node_10612 (AllWinning.cons node_9522 (AllWinning.cons node_16868 (AllWinning.cons node_15822 (AllWinning.cons node_16870 (AllWinning.cons node_15827 (AllWinning.cons node_14842 (AllWinning.cons node_13881 (AllWinning.cons node_12914 (AllWinning.cons node_11909 (AllWinning.cons node_10921 (AllWinning.cons node_9838 (AllWinning.nil))))))))))))))))))

theorem node_17794 : Outcome ⟨17, 2, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 11, 2⟩, ⟨15, 2, 11, 4⟩, ⟨14, 2, 11, 6⟩, ⟨13, 2, 11, 8⟩, ⟨12, 2, 11, 10⟩, ⟨11, 2, 11, 12⟩, ⟨10, 2, 11, 14⟩, ⟨9, 2, 11, 16⟩, ⟨8, 2, 11, 18⟩, ⟨7, 2, 11, 20⟩, ⟨17, 1, 11, 2⟩, ⟨17, 0, 11, 4⟩, ⟨17, 2, 10, 2⟩, ⟨17, 2, 9, 4⟩, ⟨17, 2, 8, 6⟩, ⟨17, 2, 7, 8⟩, ⟨17, 2, 6, 10⟩, ⟨17, 2, 5, 12⟩, ⟨17, 2, 4, 14⟩, ⟨17, 2, 3, 16⟩, ⟨17, 2, 2, 18⟩, ⟨17, 2, 1, 20⟩]
  exact AllWinning.cons node_16823 (AllWinning.cons node_15737 (AllWinning.cons node_14717 (AllWinning.cons node_13719 (AllWinning.cons node_12711 (AllWinning.cons node_11664 (AllWinning.cons node_10612 (AllWinning.cons node_9522 (AllWinning.cons node_8515 (AllWinning.cons node_7495 (AllWinning.cons node_16868 (AllWinning.cons node_15822 (AllWinning.cons node_16870 (AllWinning.cons node_15827 (AllWinning.cons node_14842 (AllWinning.cons node_13881 (AllWinning.cons node_12914 (AllWinning.cons node_11909 (AllWinning.cons node_10921 (AllWinning.cons node_9838 (AllWinning.cons node_8882 (AllWinning.cons node_7891 (AllWinning.nil))))))))))))))))))))))

theorem node_17795 : Outcome ⟨17, 2, 11, 12⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 22⟩) (by decide) node_6505

theorem node_17796 : Outcome ⟨17, 3, 10, 2⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 2⟩) (by decide) node_16872

theorem node_17797 : Outcome ⟨17, 3, 10, 8⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17798 : Outcome ⟨17, 3, 10, 14⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 8⟩) (by decide) node_13722

theorem node_17799 : Outcome ⟨17, 4, 9, 4⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 2⟩) (by decide) node_16828

theorem node_17800 : Outcome ⟨17, 5, 8, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 4⟩) (by decide) node_15745

theorem node_17801 : Outcome ⟨17, 5, 8, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 4⟩) (by decide) node_15745

theorem node_17802 : Outcome ⟨17, 6, 7, 4⟩ true :=
  Outcome.win (q := ⟨16, 6, 7, 2⟩) (by decide) node_16837

theorem node_17803 : Outcome ⟨17, 6, 7, 8⟩ true :=
  Outcome.win (q := ⟨16, 6, 7, 2⟩) (by decide) node_16837

theorem node_17804 : Outcome ⟨17, 7, 6, 4⟩ true :=
  Outcome.win (q := ⟨16, 7, 6, 2⟩) (by decide) node_16841

theorem node_17805 : Outcome ⟨17, 7, 6, 8⟩ true :=
  Outcome.win (q := ⟨16, 7, 6, 2⟩) (by decide) node_16841

theorem node_17806 : Outcome ⟨17, 8, 5, 2⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 4⟩) (by decide) node_15762

theorem node_17807 : Outcome ⟨17, 8, 5, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 4⟩) (by decide) node_15762

theorem node_17808 : Outcome ⟨17, 8, 5, 12⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 4⟩) (by decide) node_15762

theorem node_17809 : Outcome ⟨17, 9, 4, 4⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 2⟩) (by decide) node_16846

theorem node_17810 : Outcome ⟨17, 10, 3, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 3, 2⟩) (by decide) node_16899

theorem node_17811 : Outcome ⟨17, 10, 3, 8⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

theorem node_17812 : Outcome ⟨17, 10, 3, 14⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 8⟩) (by decide) node_13748

end RQ9F1
