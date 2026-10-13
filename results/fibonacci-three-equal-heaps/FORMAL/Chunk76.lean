import Chunk75
set_option autoImplicit false
namespace RQ9F1

theorem node_16488 : Outcome ⟨10, 0, 19, 18⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 18⟩) (by decide) node_7637

theorem node_16489 : Outcome ⟨10, 1, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 8⟩) (by decide) node_12599

theorem node_16490 : Outcome ⟨10, 1, 18, 8⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 8⟩) (by decide) node_12599

theorem node_16491 : Outcome ⟨10, 1, 18, 10⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 8⟩) (by decide) node_12599

theorem node_16492 : Outcome ⟨10, 2, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 1, 17, 2⟩) (by decide) node_15452

theorem node_16493 : Outcome ⟨10, 2, 17, 16⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 24⟩) (by decide) node_5163

theorem node_16494 : Outcome ⟨10, 3, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 6⟩) (by decide) node_13555

theorem node_16495 : Outcome ⟨10, 3, 16, 6⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 6⟩) (by decide) node_13555

theorem node_16496 : Outcome ⟨10, 4, 15, 2⟩ true :=
  Outcome.win (q := ⟨10, 4, 14, 2⟩) (by decide) node_15462

theorem node_16497 : Outcome ⟨10, 5, 14, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 8⟩) (by decide) node_12599

theorem node_16498 : Outcome ⟨10, 5, 14, 8⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 8⟩) (by decide) node_12599

theorem node_16499 : Outcome ⟨10, 5, 14, 10⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 8⟩) (by decide) node_12599

theorem node_16500 : Outcome ⟨10, 6, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 6, 13, 2⟩, ⟨8, 6, 13, 4⟩, ⟨10, 5, 13, 2⟩, ⟨10, 4, 13, 4⟩, ⟨10, 6, 12, 2⟩, ⟨10, 6, 11, 4⟩]
  exact AllWinning.cons node_15406 (AllWinning.cons node_14419 (AllWinning.cons node_15465 (AllWinning.cons node_14526 (AllWinning.cons node_15469 (AllWinning.cons node_14534 (AllWinning.nil))))))

theorem node_16501 : Outcome ⟨10, 6, 13, 8⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 6⟩) (by decide) node_13555

theorem node_16502 : Outcome ⟨10, 6, 13, 10⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 18⟩) (by decide) node_7673

theorem node_16503 : Outcome ⟨10, 7, 12, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 6⟩) (by decide) node_13383

theorem node_16504 : Outcome ⟨10, 7, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 6⟩) (by decide) node_13383

theorem node_16505 : Outcome ⟨10, 8, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 11, 2⟩, ⟨8, 8, 11, 4⟩, ⟨10, 7, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨10, 8, 10, 2⟩, ⟨10, 8, 9, 4⟩]
  exact AllWinning.cons node_15413 (AllWinning.cons node_14426 (AllWinning.cons node_15471 (AllWinning.cons node_14534 (AllWinning.cons node_15474 (AllWinning.cons node_14542 (AllWinning.nil))))))

theorem node_16506 : Outcome ⟨10, 8, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 11, 2⟩, ⟨8, 8, 11, 4⟩, ⟨7, 8, 11, 6⟩, ⟨6, 8, 11, 8⟩, ⟨10, 7, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨10, 5, 11, 6⟩, ⟨10, 4, 11, 8⟩, ⟨10, 8, 10, 2⟩, ⟨10, 8, 9, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 8, 7, 8⟩]
  exact AllWinning.cons node_15413 (AllWinning.cons node_14426 (AllWinning.cons node_13389 (AllWinning.cons node_12375 (AllWinning.cons node_15471 (AllWinning.cons node_14534 (AllWinning.cons node_13565 (AllWinning.cons node_12611 (AllWinning.cons node_15474 (AllWinning.cons node_14542 (AllWinning.cons node_13573 (AllWinning.cons node_12624 (AllWinning.nil))))))))))))

theorem node_16507 : Outcome ⟨10, 8, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 11, 2⟩, ⟨8, 8, 11, 4⟩, ⟨7, 8, 11, 6⟩, ⟨6, 8, 11, 8⟩, ⟨5, 8, 11, 10⟩, ⟨4, 8, 11, 12⟩, ⟨10, 7, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨10, 5, 11, 6⟩, ⟨10, 4, 11, 8⟩, ⟨10, 3, 11, 10⟩, ⟨10, 2, 11, 12⟩, ⟨10, 8, 10, 2⟩, ⟨10, 8, 9, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 8, 7, 8⟩, ⟨10, 8, 6, 10⟩, ⟨10, 8, 5, 12⟩]
  exact AllWinning.cons node_15413 (AllWinning.cons node_14426 (AllWinning.cons node_13389 (AllWinning.cons node_12375 (AllWinning.cons node_11326 (AllWinning.cons node_10202 (AllWinning.cons node_15471 (AllWinning.cons node_14534 (AllWinning.cons node_13565 (AllWinning.cons node_12611 (AllWinning.cons node_11621 (AllWinning.cons node_10611 (AllWinning.cons node_15474 (AllWinning.cons node_14542 (AllWinning.cons node_13573 (AllWinning.cons node_12624 (AllWinning.cons node_11637 (AllWinning.cons node_10641 (AllWinning.nil))))))))))))))))))

theorem node_16508 : Outcome ⟨10, 8, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 11, 2⟩, ⟨8, 8, 11, 4⟩, ⟨7, 8, 11, 6⟩, ⟨6, 8, 11, 8⟩, ⟨5, 8, 11, 10⟩, ⟨4, 8, 11, 12⟩, ⟨3, 8, 11, 14⟩, ⟨2, 8, 11, 16⟩, ⟨10, 7, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨10, 5, 11, 6⟩, ⟨10, 4, 11, 8⟩, ⟨10, 3, 11, 10⟩, ⟨10, 2, 11, 12⟩, ⟨10, 1, 11, 14⟩, ⟨10, 0, 11, 16⟩, ⟨10, 8, 10, 2⟩, ⟨10, 8, 9, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 8, 7, 8⟩, ⟨10, 8, 6, 10⟩, ⟨10, 8, 5, 12⟩, ⟨10, 8, 4, 14⟩, ⟨10, 8, 3, 16⟩]
  exact AllWinning.cons node_15413 (AllWinning.cons node_14426 (AllWinning.cons node_13389 (AllWinning.cons node_12375 (AllWinning.cons node_11326 (AllWinning.cons node_10202 (AllWinning.cons node_9154 (AllWinning.cons node_8099 (AllWinning.cons node_15471 (AllWinning.cons node_14534 (AllWinning.cons node_13565 (AllWinning.cons node_12611 (AllWinning.cons node_11621 (AllWinning.cons node_10611 (AllWinning.cons node_9567 (AllWinning.cons node_8628 (AllWinning.cons node_15474 (AllWinning.cons node_14542 (AllWinning.cons node_13573 (AllWinning.cons node_12624 (AllWinning.cons node_11637 (AllWinning.cons node_10641 (AllWinning.cons node_9595 (AllWinning.cons node_8659 (AllWinning.nil))))))))))))))))))))))))

theorem node_16509 : Outcome ⟨10, 8, 11, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 11, 2⟩, ⟨8, 8, 11, 4⟩, ⟨7, 8, 11, 6⟩, ⟨6, 8, 11, 8⟩, ⟨5, 8, 11, 10⟩, ⟨4, 8, 11, 12⟩, ⟨3, 8, 11, 14⟩, ⟨2, 8, 11, 16⟩, ⟨1, 8, 11, 18⟩, ⟨0, 8, 11, 20⟩, ⟨10, 7, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨10, 5, 11, 6⟩, ⟨10, 4, 11, 8⟩, ⟨10, 3, 11, 10⟩, ⟨10, 2, 11, 12⟩, ⟨10, 1, 11, 14⟩, ⟨10, 0, 11, 16⟩, ⟨10, 8, 10, 2⟩, ⟨10, 8, 9, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 8, 7, 8⟩, ⟨10, 8, 6, 10⟩, ⟨10, 8, 5, 12⟩, ⟨10, 8, 4, 14⟩, ⟨10, 8, 3, 16⟩, ⟨10, 8, 2, 18⟩, ⟨10, 8, 1, 20⟩, ⟨10, 8, 0, 22⟩]
  exact AllWinning.cons node_15413 (AllWinning.cons node_14426 (AllWinning.cons node_13389 (AllWinning.cons node_12375 (AllWinning.cons node_11326 (AllWinning.cons node_10202 (AllWinning.cons node_9154 (AllWinning.cons node_8099 (AllWinning.cons node_7065 (AllWinning.cons node_6072 (AllWinning.cons node_15471 (AllWinning.cons node_14534 (AllWinning.cons node_13565 (AllWinning.cons node_12611 (AllWinning.cons node_11621 (AllWinning.cons node_10611 (AllWinning.cons node_9567 (AllWinning.cons node_8628 (AllWinning.cons node_15474 (AllWinning.cons node_14542 (AllWinning.cons node_13573 (AllWinning.cons node_12624 (AllWinning.cons node_11637 (AllWinning.cons node_10641 (AllWinning.cons node_9595 (AllWinning.cons node_8659 (AllWinning.cons node_7684 (AllWinning.cons node_6733 (AllWinning.cons node_5911 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16510 : Outcome ⟨10, 8, 11, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 8, 11, 2⟩, ⟨8, 8, 11, 4⟩, ⟨7, 8, 11, 6⟩, ⟨6, 8, 11, 8⟩, ⟨5, 8, 11, 10⟩, ⟨4, 8, 11, 12⟩, ⟨3, 8, 11, 14⟩, ⟨2, 8, 11, 16⟩, ⟨1, 8, 11, 18⟩, ⟨0, 8, 11, 20⟩, ⟨10, 7, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨10, 5, 11, 6⟩, ⟨10, 4, 11, 8⟩, ⟨10, 3, 11, 10⟩, ⟨10, 2, 11, 12⟩, ⟨10, 1, 11, 14⟩, ⟨10, 0, 11, 16⟩, ⟨10, 8, 10, 2⟩, ⟨10, 8, 9, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 8, 7, 8⟩, ⟨10, 8, 6, 10⟩, ⟨10, 8, 5, 12⟩, ⟨10, 8, 4, 14⟩, ⟨10, 8, 3, 16⟩, ⟨10, 8, 2, 18⟩, ⟨10, 8, 1, 20⟩, ⟨10, 8, 0, 22⟩]
  exact AllWinning.cons node_15413 (AllWinning.cons node_14426 (AllWinning.cons node_13389 (AllWinning.cons node_12375 (AllWinning.cons node_11326 (AllWinning.cons node_10202 (AllWinning.cons node_9154 (AllWinning.cons node_8099 (AllWinning.cons node_7065 (AllWinning.cons node_6072 (AllWinning.cons node_15471 (AllWinning.cons node_14534 (AllWinning.cons node_13565 (AllWinning.cons node_12611 (AllWinning.cons node_11621 (AllWinning.cons node_10611 (AllWinning.cons node_9567 (AllWinning.cons node_8628 (AllWinning.cons node_15474 (AllWinning.cons node_14542 (AllWinning.cons node_13573 (AllWinning.cons node_12624 (AllWinning.cons node_11637 (AllWinning.cons node_10641 (AllWinning.cons node_9595 (AllWinning.cons node_8659 (AllWinning.cons node_7684 (AllWinning.cons node_6733 (AllWinning.cons node_5911 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16511 : Outcome ⟨10, 9, 10, 4⟩ true :=
  Outcome.win (q := ⟨10, 7, 10, 4⟩) (by decide) node_14538

theorem node_16512 : Outcome ⟨10, 9, 10, 8⟩ true :=
  Outcome.win (q := ⟨10, 7, 10, 4⟩) (by decide) node_14538

theorem node_16513 : Outcome ⟨10, 9, 10, 16⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 18⟩) (by decide) node_7637

theorem node_16514 : Outcome ⟨10, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 7, 4⟩) (by decide) node_14545

theorem node_16515 : Outcome ⟨10, 10, 9, 8⟩ true :=
  Outcome.win (q := ⟨10, 10, 7, 4⟩) (by decide) node_14545

theorem node_16516 : Outcome ⟨10, 10, 9, 16⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 18⟩) (by decide) node_7696

theorem node_16517 : Outcome ⟨10, 11, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 8, 2⟩, ⟨8, 11, 8, 4⟩, ⟨10, 10, 8, 2⟩, ⟨10, 9, 8, 4⟩, ⟨10, 11, 7, 2⟩, ⟨10, 11, 6, 4⟩]
  exact AllWinning.cons node_15421 (AllWinning.cons node_14431 (AllWinning.cons node_15479 (AllWinning.cons node_14543 (AllWinning.cons node_15482 (AllWinning.cons node_14549 (AllWinning.nil))))))

theorem node_16518 : Outcome ⟨10, 11, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 8, 2⟩, ⟨8, 11, 8, 4⟩, ⟨7, 11, 8, 6⟩, ⟨6, 11, 8, 8⟩, ⟨10, 10, 8, 2⟩, ⟨10, 9, 8, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 7, 8, 8⟩, ⟨10, 11, 7, 2⟩, ⟨10, 11, 6, 4⟩, ⟨10, 11, 5, 6⟩, ⟨10, 11, 4, 8⟩]
  exact AllWinning.cons node_15421 (AllWinning.cons node_14431 (AllWinning.cons node_13398 (AllWinning.cons node_12387 (AllWinning.cons node_15479 (AllWinning.cons node_14543 (AllWinning.cons node_13573 (AllWinning.cons node_12621 (AllWinning.cons node_15482 (AllWinning.cons node_14549 (AllWinning.cons node_13581 (AllWinning.cons node_12634 (AllWinning.nil))))))))))))

theorem node_16519 : Outcome ⟨10, 11, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 8, 2⟩, ⟨8, 11, 8, 4⟩, ⟨7, 11, 8, 6⟩, ⟨6, 11, 8, 8⟩, ⟨5, 11, 8, 10⟩, ⟨4, 11, 8, 12⟩, ⟨10, 10, 8, 2⟩, ⟨10, 9, 8, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 7, 8, 8⟩, ⟨10, 6, 8, 10⟩, ⟨10, 5, 8, 12⟩, ⟨10, 11, 7, 2⟩, ⟨10, 11, 6, 4⟩, ⟨10, 11, 5, 6⟩, ⟨10, 11, 4, 8⟩, ⟨10, 11, 3, 10⟩, ⟨10, 11, 2, 12⟩]
  exact AllWinning.cons node_15421 (AllWinning.cons node_14431 (AllWinning.cons node_13398 (AllWinning.cons node_12387 (AllWinning.cons node_11338 (AllWinning.cons node_10213 (AllWinning.cons node_15479 (AllWinning.cons node_14543 (AllWinning.cons node_13573 (AllWinning.cons node_12621 (AllWinning.cons node_11630 (AllWinning.cons node_10623 (AllWinning.cons node_15482 (AllWinning.cons node_14549 (AllWinning.cons node_13581 (AllWinning.cons node_12634 (AllWinning.cons node_11648 (AllWinning.cons node_10653 (AllWinning.nil))))))))))))))))))

theorem node_16520 : Outcome ⟨10, 11, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 8, 2⟩, ⟨8, 11, 8, 4⟩, ⟨7, 11, 8, 6⟩, ⟨6, 11, 8, 8⟩, ⟨5, 11, 8, 10⟩, ⟨4, 11, 8, 12⟩, ⟨3, 11, 8, 14⟩, ⟨2, 11, 8, 16⟩, ⟨10, 10, 8, 2⟩, ⟨10, 9, 8, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 7, 8, 8⟩, ⟨10, 6, 8, 10⟩, ⟨10, 5, 8, 12⟩, ⟨10, 4, 8, 14⟩, ⟨10, 3, 8, 16⟩, ⟨10, 11, 7, 2⟩, ⟨10, 11, 6, 4⟩, ⟨10, 11, 5, 6⟩, ⟨10, 11, 4, 8⟩, ⟨10, 11, 3, 10⟩, ⟨10, 11, 2, 12⟩, ⟨10, 11, 1, 14⟩, ⟨10, 11, 0, 16⟩]
  exact AllWinning.cons node_15421 (AllWinning.cons node_14431 (AllWinning.cons node_13398 (AllWinning.cons node_12387 (AllWinning.cons node_11338 (AllWinning.cons node_10213 (AllWinning.cons node_9167 (AllWinning.cons node_8113 (AllWinning.cons node_15479 (AllWinning.cons node_14543 (AllWinning.cons node_13573 (AllWinning.cons node_12621 (AllWinning.cons node_11630 (AllWinning.cons node_10623 (AllWinning.cons node_9578 (AllWinning.cons node_8640 (AllWinning.cons node_15482 (AllWinning.cons node_14549 (AllWinning.cons node_13581 (AllWinning.cons node_12634 (AllWinning.cons node_11648 (AllWinning.cons node_10653 (AllWinning.cons node_9605 (AllWinning.cons node_8669 (AllWinning.nil))))))))))))))))))))))))

theorem node_16521 : Outcome ⟨10, 11, 8, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 8, 2⟩, ⟨8, 11, 8, 4⟩, ⟨7, 11, 8, 6⟩, ⟨6, 11, 8, 8⟩, ⟨5, 11, 8, 10⟩, ⟨4, 11, 8, 12⟩, ⟨3, 11, 8, 14⟩, ⟨2, 11, 8, 16⟩, ⟨1, 11, 8, 18⟩, ⟨0, 11, 8, 20⟩, ⟨10, 10, 8, 2⟩, ⟨10, 9, 8, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 7, 8, 8⟩, ⟨10, 6, 8, 10⟩, ⟨10, 5, 8, 12⟩, ⟨10, 4, 8, 14⟩, ⟨10, 3, 8, 16⟩, ⟨10, 2, 8, 18⟩, ⟨10, 1, 8, 20⟩, ⟨10, 0, 8, 22⟩, ⟨10, 11, 7, 2⟩, ⟨10, 11, 6, 4⟩, ⟨10, 11, 5, 6⟩, ⟨10, 11, 4, 8⟩, ⟨10, 11, 3, 10⟩, ⟨10, 11, 2, 12⟩, ⟨10, 11, 1, 14⟩, ⟨10, 11, 0, 16⟩]
  exact AllWinning.cons node_15421 (AllWinning.cons node_14431 (AllWinning.cons node_13398 (AllWinning.cons node_12387 (AllWinning.cons node_11338 (AllWinning.cons node_10213 (AllWinning.cons node_9167 (AllWinning.cons node_8113 (AllWinning.cons node_7076 (AllWinning.cons node_6081 (AllWinning.cons node_15479 (AllWinning.cons node_14543 (AllWinning.cons node_13573 (AllWinning.cons node_12621 (AllWinning.cons node_11630 (AllWinning.cons node_10623 (AllWinning.cons node_9578 (AllWinning.cons node_8640 (AllWinning.cons node_7646 (AllWinning.cons node_6706 (AllWinning.cons node_5886 (AllWinning.cons node_15482 (AllWinning.cons node_14549 (AllWinning.cons node_13581 (AllWinning.cons node_12634 (AllWinning.cons node_11648 (AllWinning.cons node_10653 (AllWinning.cons node_9605 (AllWinning.cons node_8669 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16522 : Outcome ⟨10, 11, 8, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 8, 2⟩, ⟨8, 11, 8, 4⟩, ⟨7, 11, 8, 6⟩, ⟨6, 11, 8, 8⟩, ⟨5, 11, 8, 10⟩, ⟨4, 11, 8, 12⟩, ⟨3, 11, 8, 14⟩, ⟨2, 11, 8, 16⟩, ⟨1, 11, 8, 18⟩, ⟨0, 11, 8, 20⟩, ⟨10, 10, 8, 2⟩, ⟨10, 9, 8, 4⟩, ⟨10, 8, 8, 6⟩, ⟨10, 7, 8, 8⟩, ⟨10, 6, 8, 10⟩, ⟨10, 5, 8, 12⟩, ⟨10, 4, 8, 14⟩, ⟨10, 3, 8, 16⟩, ⟨10, 2, 8, 18⟩, ⟨10, 1, 8, 20⟩, ⟨10, 0, 8, 22⟩, ⟨10, 11, 7, 2⟩, ⟨10, 11, 6, 4⟩, ⟨10, 11, 5, 6⟩, ⟨10, 11, 4, 8⟩, ⟨10, 11, 3, 10⟩, ⟨10, 11, 2, 12⟩, ⟨10, 11, 1, 14⟩, ⟨10, 11, 0, 16⟩]
  exact AllWinning.cons node_15421 (AllWinning.cons node_14431 (AllWinning.cons node_13398 (AllWinning.cons node_12387 (AllWinning.cons node_11338 (AllWinning.cons node_10213 (AllWinning.cons node_9167 (AllWinning.cons node_8113 (AllWinning.cons node_7076 (AllWinning.cons node_6081 (AllWinning.cons node_15479 (AllWinning.cons node_14543 (AllWinning.cons node_13573 (AllWinning.cons node_12621 (AllWinning.cons node_11630 (AllWinning.cons node_10623 (AllWinning.cons node_9578 (AllWinning.cons node_8640 (AllWinning.cons node_7646 (AllWinning.cons node_6706 (AllWinning.cons node_5886 (AllWinning.cons node_15482 (AllWinning.cons node_14549 (AllWinning.cons node_13581 (AllWinning.cons node_12634 (AllWinning.cons node_11648 (AllWinning.cons node_10653 (AllWinning.cons node_9605 (AllWinning.cons node_8669 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16523 : Outcome ⟨10, 12, 7, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 6⟩) (by decide) node_13403

theorem node_16524 : Outcome ⟨10, 12, 7, 10⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 6⟩) (by decide) node_13403

theorem node_16525 : Outcome ⟨10, 13, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 13, 6, 2⟩, ⟨8, 13, 6, 4⟩, ⟨10, 12, 6, 2⟩, ⟨10, 11, 6, 4⟩, ⟨10, 13, 5, 2⟩, ⟨10, 13, 4, 4⟩]
  exact AllWinning.cons node_15426 (AllWinning.cons node_14438 (AllWinning.cons node_15485 (AllWinning.cons node_14549 (AllWinning.cons node_15487 (AllWinning.cons node_14559 (AllWinning.nil))))))

theorem node_16526 : Outcome ⟨10, 13, 6, 8⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 6⟩) (by decide) node_13588

theorem node_16527 : Outcome ⟨10, 13, 6, 10⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 18⟩) (by decide) node_7659

theorem node_16528 : Outcome ⟨10, 14, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 8⟩) (by decide) node_12642

theorem node_16529 : Outcome ⟨10, 14, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 8⟩) (by decide) node_12642

theorem node_16530 : Outcome ⟨10, 14, 5, 10⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 8⟩) (by decide) node_12642

theorem node_16531 : Outcome ⟨10, 15, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 4, 2⟩) (by decide) node_15491

theorem node_16532 : Outcome ⟨10, 16, 3, 4⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 6⟩) (by decide) node_13588

theorem node_16533 : Outcome ⟨10, 16, 3, 6⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 6⟩) (by decide) node_13588

theorem node_16534 : Outcome ⟨10, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 2⟩) (by decide) node_15497

theorem node_16535 : Outcome ⟨10, 17, 2, 16⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 24⟩) (by decide) node_5182

theorem node_16536 : Outcome ⟨10, 18, 1, 4⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 8⟩) (by decide) node_12642

theorem node_16537 : Outcome ⟨10, 18, 1, 8⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 8⟩) (by decide) node_12642

theorem node_16538 : Outcome ⟨10, 18, 1, 10⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 8⟩) (by decide) node_12642

theorem node_16539 : Outcome ⟨10, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 0, 2⟩) (by decide) node_15504

theorem node_16540 : Outcome ⟨10, 19, 0, 8⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 8⟩) (by decide) node_12416

theorem node_16541 : Outcome ⟨10, 19, 0, 10⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 18⟩) (by decide) node_7696

theorem node_16542 : Outcome ⟨10, 19, 0, 18⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 18⟩) (by decide) node_7696

theorem node_16543 : Outcome ⟨11, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 16, 4⟩) (by decide) node_14574

theorem node_16544 : Outcome ⟨11, 0, 18, 4⟩ true :=
  Outcome.win (q := ⟨11, 0, 16, 4⟩) (by decide) node_14574

theorem node_16545 : Outcome ⟨11, 0, 18, 8⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 14⟩) (by decide) node_9615

theorem node_16546 : Outcome ⟨11, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨11, 1, 15, 4⟩) (by decide) node_14579

theorem node_16547 : Outcome ⟨11, 1, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 1, 15, 4⟩) (by decide) node_14579

theorem node_16548 : Outcome ⟨11, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 16, 4⟩) (by decide) node_14574

theorem node_16549 : Outcome ⟨11, 2, 16, 10⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 20⟩) (by decide) node_6759

theorem node_16550 : Outcome ⟨11, 3, 15, 2⟩ true :=
  Outcome.win (q := ⟨11, 1, 15, 4⟩) (by decide) node_14579

theorem node_16551 : Outcome ⟨11, 3, 15, 6⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 8⟩) (by decide) node_12433

theorem node_16552 : Outcome ⟨11, 3, 15, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 8⟩) (by decide) node_12433

theorem node_16553 : Outcome ⟨11, 3, 15, 14⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 20⟩) (by decide) node_6769

theorem node_16554 : Outcome ⟨11, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨10, 4, 14, 2⟩) (by decide) node_15462

theorem node_16555 : Outcome ⟨11, 4, 14, 8⟩ true :=
  Outcome.win (q := ⟨10, 4, 14, 2⟩) (by decide) node_15462

theorem node_16556 : Outcome ⟨11, 4, 14, 16⟩ true :=
  Outcome.win (q := ⟨10, 4, 14, 2⟩) (by decide) node_15462

theorem node_16557 : Outcome ⟨11, 5, 13, 4⟩ true :=
  Outcome.win (q := ⟨11, 2, 13, 6⟩) (by decide) node_13607

theorem node_16558 : Outcome ⟨11, 6, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 12, 2⟩, ⟨9, 6, 12, 4⟩, ⟨11, 5, 12, 2⟩, ⟨11, 4, 12, 4⟩, ⟨11, 6, 11, 2⟩, ⟨11, 6, 10, 4⟩]
  exact AllWinning.cons node_15469 (AllWinning.cons node_14478 (AllWinning.cons node_15523 (AllWinning.cons node_14586 (AllWinning.cons node_15525 (AllWinning.cons node_14591 (AllWinning.nil))))))

theorem node_16559 : Outcome ⟨11, 6, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 12, 2⟩, ⟨9, 6, 12, 4⟩, ⟨8, 6, 12, 6⟩, ⟨7, 6, 12, 8⟩, ⟨11, 5, 12, 2⟩, ⟨11, 4, 12, 4⟩, ⟨11, 3, 12, 6⟩, ⟨11, 2, 12, 8⟩, ⟨11, 6, 11, 2⟩, ⟨11, 6, 10, 4⟩, ⟨11, 6, 9, 6⟩, ⟨11, 6, 8, 8⟩]
  exact AllWinning.cons node_15469 (AllWinning.cons node_14478 (AllWinning.cons node_13446 (AllWinning.cons node_12443 (AllWinning.cons node_15523 (AllWinning.cons node_14586 (AllWinning.cons node_13611 (AllWinning.cons node_12659 (AllWinning.cons node_15525 (AllWinning.cons node_14591 (AllWinning.cons node_13620 (AllWinning.cons node_12674 (AllWinning.nil))))))))))))

theorem node_16560 : Outcome ⟨11, 6, 12, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 10⟩) (by decide) node_11384

theorem node_16561 : Outcome ⟨11, 6, 12, 10⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 20⟩) (by decide) node_6793

theorem node_16562 : Outcome ⟨11, 6, 12, 12⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 20⟩) (by decide) node_6793

theorem node_16563 : Outcome ⟨11, 7, 11, 4⟩ true :=
  Outcome.win (q := ⟨11, 5, 11, 4⟩) (by decide) node_14589

theorem node_16564 : Outcome ⟨11, 7, 11, 10⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 20⟩) (by decide) node_6146

theorem node_16565 : Outcome ⟨11, 8, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 10, 2⟩, ⟨9, 8, 10, 4⟩, ⟨11, 7, 10, 2⟩, ⟨11, 6, 10, 4⟩, ⟨11, 8, 9, 2⟩, ⟨11, 8, 8, 4⟩]
  exact AllWinning.cons node_15474 (AllWinning.cons node_14484 (AllWinning.cons node_15528 (AllWinning.cons node_14591 (AllWinning.cons node_15531 (AllWinning.cons node_14598 (AllWinning.nil))))))

theorem node_16566 : Outcome ⟨11, 8, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 10, 2⟩, ⟨9, 8, 10, 4⟩, ⟨8, 8, 10, 6⟩, ⟨7, 8, 10, 8⟩, ⟨11, 7, 10, 2⟩, ⟨11, 6, 10, 4⟩, ⟨11, 5, 10, 6⟩, ⟨11, 4, 10, 8⟩, ⟨11, 8, 9, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 8, 7, 6⟩, ⟨11, 8, 6, 8⟩]
  exact AllWinning.cons node_15474 (AllWinning.cons node_14484 (AllWinning.cons node_13454 (AllWinning.cons node_12450 (AllWinning.cons node_15528 (AllWinning.cons node_14591 (AllWinning.cons node_13618 (AllWinning.cons node_12667 (AllWinning.cons node_15531 (AllWinning.cons node_14598 (AllWinning.cons node_13629 (AllWinning.cons node_12680 (AllWinning.nil))))))))))))

theorem node_16567 : Outcome ⟨11, 8, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 10, 2⟩, ⟨9, 8, 10, 4⟩, ⟨8, 8, 10, 6⟩, ⟨7, 8, 10, 8⟩, ⟨6, 8, 10, 10⟩, ⟨5, 8, 10, 12⟩, ⟨11, 7, 10, 2⟩, ⟨11, 6, 10, 4⟩, ⟨11, 5, 10, 6⟩, ⟨11, 4, 10, 8⟩, ⟨11, 3, 10, 10⟩, ⟨11, 2, 10, 12⟩, ⟨11, 8, 9, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 8, 7, 6⟩, ⟨11, 8, 6, 8⟩, ⟨11, 8, 5, 10⟩, ⟨11, 8, 4, 12⟩]
  exact AllWinning.cons node_15474 (AllWinning.cons node_14484 (AllWinning.cons node_13454 (AllWinning.cons node_12450 (AllWinning.cons node_11393 (AllWinning.cons node_10287 (AllWinning.cons node_15528 (AllWinning.cons node_14591 (AllWinning.cons node_13618 (AllWinning.cons node_12667 (AllWinning.cons node_11669 (AllWinning.cons node_10669 (AllWinning.cons node_15531 (AllWinning.cons node_14598 (AllWinning.cons node_13629 (AllWinning.cons node_12680 (AllWinning.cons node_11691 (AllWinning.cons node_10694 (AllWinning.nil))))))))))))))))))

theorem node_16568 : Outcome ⟨11, 8, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 10, 2⟩, ⟨9, 8, 10, 4⟩, ⟨8, 8, 10, 6⟩, ⟨7, 8, 10, 8⟩, ⟨6, 8, 10, 10⟩, ⟨5, 8, 10, 12⟩, ⟨4, 8, 10, 14⟩, ⟨3, 8, 10, 16⟩, ⟨11, 7, 10, 2⟩, ⟨11, 6, 10, 4⟩, ⟨11, 5, 10, 6⟩, ⟨11, 4, 10, 8⟩, ⟨11, 3, 10, 10⟩, ⟨11, 2, 10, 12⟩, ⟨11, 1, 10, 14⟩, ⟨11, 0, 10, 16⟩, ⟨11, 8, 9, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 8, 7, 6⟩, ⟨11, 8, 6, 8⟩, ⟨11, 8, 5, 10⟩, ⟨11, 8, 4, 12⟩, ⟨11, 8, 3, 14⟩, ⟨11, 8, 2, 16⟩]
  exact AllWinning.cons node_15474 (AllWinning.cons node_14484 (AllWinning.cons node_13454 (AllWinning.cons node_12450 (AllWinning.cons node_11393 (AllWinning.cons node_10287 (AllWinning.cons node_9231 (AllWinning.cons node_8180 (AllWinning.cons node_15528 (AllWinning.cons node_14591 (AllWinning.cons node_13618 (AllWinning.cons node_12667 (AllWinning.cons node_11669 (AllWinning.cons node_10669 (AllWinning.cons node_9622 (AllWinning.cons node_8672 (AllWinning.cons node_15531 (AllWinning.cons node_14598 (AllWinning.cons node_13629 (AllWinning.cons node_12680 (AllWinning.cons node_11691 (AllWinning.cons node_10694 (AllWinning.cons node_9652 (AllWinning.cons node_8702 (AllWinning.nil))))))))))))))))))))))))

theorem node_16569 : Outcome ⟨11, 8, 10, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 10, 2⟩, ⟨9, 8, 10, 4⟩, ⟨8, 8, 10, 6⟩, ⟨7, 8, 10, 8⟩, ⟨6, 8, 10, 10⟩, ⟨5, 8, 10, 12⟩, ⟨4, 8, 10, 14⟩, ⟨3, 8, 10, 16⟩, ⟨2, 8, 10, 18⟩, ⟨1, 8, 10, 20⟩, ⟨0, 8, 10, 22⟩, ⟨11, 7, 10, 2⟩, ⟨11, 6, 10, 4⟩, ⟨11, 5, 10, 6⟩, ⟨11, 4, 10, 8⟩, ⟨11, 3, 10, 10⟩, ⟨11, 2, 10, 12⟩, ⟨11, 1, 10, 14⟩, ⟨11, 0, 10, 16⟩, ⟨11, 8, 9, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 8, 7, 6⟩, ⟨11, 8, 6, 8⟩, ⟨11, 8, 5, 10⟩, ⟨11, 8, 4, 12⟩, ⟨11, 8, 3, 14⟩, ⟨11, 8, 2, 16⟩, ⟨11, 8, 1, 18⟩, ⟨11, 8, 0, 20⟩]
  exact AllWinning.cons node_15474 (AllWinning.cons node_14484 (AllWinning.cons node_13454 (AllWinning.cons node_12450 (AllWinning.cons node_11393 (AllWinning.cons node_10287 (AllWinning.cons node_9231 (AllWinning.cons node_8180 (AllWinning.cons node_7153 (AllWinning.cons node_6153 (AllWinning.cons node_5343 (AllWinning.cons node_15528 (AllWinning.cons node_14591 (AllWinning.cons node_13618 (AllWinning.cons node_12667 (AllWinning.cons node_11669 (AllWinning.cons node_10669 (AllWinning.cons node_9622 (AllWinning.cons node_8672 (AllWinning.cons node_15531 (AllWinning.cons node_14598 (AllWinning.cons node_13629 (AllWinning.cons node_12680 (AllWinning.cons node_11691 (AllWinning.cons node_10694 (AllWinning.cons node_9652 (AllWinning.cons node_8702 (AllWinning.cons node_7730 (AllWinning.cons node_6807 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16570 : Outcome ⟨11, 8, 10, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 10, 2⟩, ⟨9, 8, 10, 4⟩, ⟨8, 8, 10, 6⟩, ⟨7, 8, 10, 8⟩, ⟨6, 8, 10, 10⟩, ⟨5, 8, 10, 12⟩, ⟨4, 8, 10, 14⟩, ⟨3, 8, 10, 16⟩, ⟨2, 8, 10, 18⟩, ⟨1, 8, 10, 20⟩, ⟨0, 8, 10, 22⟩, ⟨11, 7, 10, 2⟩, ⟨11, 6, 10, 4⟩, ⟨11, 5, 10, 6⟩, ⟨11, 4, 10, 8⟩, ⟨11, 3, 10, 10⟩, ⟨11, 2, 10, 12⟩, ⟨11, 1, 10, 14⟩, ⟨11, 0, 10, 16⟩, ⟨11, 8, 9, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 8, 7, 6⟩, ⟨11, 8, 6, 8⟩, ⟨11, 8, 5, 10⟩, ⟨11, 8, 4, 12⟩, ⟨11, 8, 3, 14⟩, ⟨11, 8, 2, 16⟩, ⟨11, 8, 1, 18⟩, ⟨11, 8, 0, 20⟩]
  exact AllWinning.cons node_15474 (AllWinning.cons node_14484 (AllWinning.cons node_13454 (AllWinning.cons node_12450 (AllWinning.cons node_11393 (AllWinning.cons node_10287 (AllWinning.cons node_9231 (AllWinning.cons node_8180 (AllWinning.cons node_7153 (AllWinning.cons node_6153 (AllWinning.cons node_5343 (AllWinning.cons node_15528 (AllWinning.cons node_14591 (AllWinning.cons node_13618 (AllWinning.cons node_12667 (AllWinning.cons node_11669 (AllWinning.cons node_10669 (AllWinning.cons node_9622 (AllWinning.cons node_8672 (AllWinning.cons node_15531 (AllWinning.cons node_14598 (AllWinning.cons node_13629 (AllWinning.cons node_12680 (AllWinning.cons node_11691 (AllWinning.cons node_10694 (AllWinning.cons node_9652 (AllWinning.cons node_8702 (AllWinning.cons node_7730 (AllWinning.cons node_6807 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16571 : Outcome ⟨11, 9, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 9, 9, 2⟩, ⟨9, 9, 9, 4⟩, ⟨11, 8, 9, 2⟩, ⟨11, 7, 9, 4⟩, ⟨11, 9, 8, 2⟩, ⟨11, 9, 7, 4⟩]
  exact AllWinning.cons node_15477 (AllWinning.cons node_14485 (AllWinning.cons node_15531 (AllWinning.cons node_14594 (AllWinning.cons node_15533 (AllWinning.cons node_14600 (AllWinning.nil))))))

theorem node_16572 : Outcome ⟨11, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨8, 9, 9, 6⟩) (by decide) node_13458

theorem node_16573 : Outcome ⟨11, 9, 9, 8⟩ true :=
  Outcome.win (q := ⟨8, 9, 9, 6⟩) (by decide) node_13458

theorem node_16574 : Outcome ⟨11, 10, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 8, 2⟩, ⟨9, 10, 8, 4⟩, ⟨8, 10, 8, 6⟩, ⟨7, 10, 8, 8⟩, ⟨11, 9, 8, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 7, 8, 6⟩, ⟨11, 6, 8, 8⟩, ⟨11, 10, 7, 2⟩, ⟨11, 10, 6, 4⟩, ⟨11, 10, 5, 6⟩, ⟨11, 10, 4, 8⟩]
  exact AllWinning.cons node_15479 (AllWinning.cons node_14488 (AllWinning.cons node_13460 (AllWinning.cons node_12456 (AllWinning.cons node_15533 (AllWinning.cons node_14598 (AllWinning.cons node_13625 (AllWinning.cons node_12674 (AllWinning.cons node_15535 (AllWinning.cons node_14603 (AllWinning.cons node_13635 (AllWinning.cons node_12687 (AllWinning.nil))))))))))))

theorem node_16575 : Outcome ⟨11, 10, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 8, 2⟩, ⟨9, 10, 8, 4⟩, ⟨8, 10, 8, 6⟩, ⟨7, 10, 8, 8⟩, ⟨6, 10, 8, 10⟩, ⟨5, 10, 8, 12⟩, ⟨11, 9, 8, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 7, 8, 6⟩, ⟨11, 6, 8, 8⟩, ⟨11, 5, 8, 10⟩, ⟨11, 4, 8, 12⟩, ⟨11, 10, 7, 2⟩, ⟨11, 10, 6, 4⟩, ⟨11, 10, 5, 6⟩, ⟨11, 10, 4, 8⟩, ⟨11, 10, 3, 10⟩, ⟨11, 10, 2, 12⟩]
  exact AllWinning.cons node_15479 (AllWinning.cons node_14488 (AllWinning.cons node_13460 (AllWinning.cons node_12456 (AllWinning.cons node_11400 (AllWinning.cons node_10297 (AllWinning.cons node_15533 (AllWinning.cons node_14598 (AllWinning.cons node_13625 (AllWinning.cons node_12674 (AllWinning.cons node_11679 (AllWinning.cons node_10677 (AllWinning.cons node_15535 (AllWinning.cons node_14603 (AllWinning.cons node_13635 (AllWinning.cons node_12687 (AllWinning.cons node_11699 (AllWinning.cons node_10703 (AllWinning.nil))))))))))))))))))

theorem node_16576 : Outcome ⟨11, 10, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 8, 2⟩, ⟨9, 10, 8, 4⟩, ⟨8, 10, 8, 6⟩, ⟨7, 10, 8, 8⟩, ⟨6, 10, 8, 10⟩, ⟨5, 10, 8, 12⟩, ⟨4, 10, 8, 14⟩, ⟨3, 10, 8, 16⟩, ⟨11, 9, 8, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 7, 8, 6⟩, ⟨11, 6, 8, 8⟩, ⟨11, 5, 8, 10⟩, ⟨11, 4, 8, 12⟩, ⟨11, 3, 8, 14⟩, ⟨11, 2, 8, 16⟩, ⟨11, 10, 7, 2⟩, ⟨11, 10, 6, 4⟩, ⟨11, 10, 5, 6⟩, ⟨11, 10, 4, 8⟩, ⟨11, 10, 3, 10⟩, ⟨11, 10, 2, 12⟩, ⟨11, 10, 1, 14⟩, ⟨11, 10, 0, 16⟩]
  exact AllWinning.cons node_15479 (AllWinning.cons node_14488 (AllWinning.cons node_13460 (AllWinning.cons node_12456 (AllWinning.cons node_11400 (AllWinning.cons node_10297 (AllWinning.cons node_9238 (AllWinning.cons node_8189 (AllWinning.cons node_15533 (AllWinning.cons node_14598 (AllWinning.cons node_13625 (AllWinning.cons node_12674 (AllWinning.cons node_11679 (AllWinning.cons node_10677 (AllWinning.cons node_9629 (AllWinning.cons node_8678 (AllWinning.cons node_15535 (AllWinning.cons node_14603 (AllWinning.cons node_13635 (AllWinning.cons node_12687 (AllWinning.cons node_11699 (AllWinning.cons node_10703 (AllWinning.cons node_9660 (AllWinning.cons node_8709 (AllWinning.nil))))))))))))))))))))))))

theorem node_16577 : Outcome ⟨11, 10, 8, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 8, 2⟩, ⟨9, 10, 8, 4⟩, ⟨8, 10, 8, 6⟩, ⟨7, 10, 8, 8⟩, ⟨6, 10, 8, 10⟩, ⟨5, 10, 8, 12⟩, ⟨4, 10, 8, 14⟩, ⟨3, 10, 8, 16⟩, ⟨2, 10, 8, 18⟩, ⟨1, 10, 8, 20⟩, ⟨0, 10, 8, 22⟩, ⟨11, 9, 8, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 7, 8, 6⟩, ⟨11, 6, 8, 8⟩, ⟨11, 5, 8, 10⟩, ⟨11, 4, 8, 12⟩, ⟨11, 3, 8, 14⟩, ⟨11, 2, 8, 16⟩, ⟨11, 1, 8, 18⟩, ⟨11, 0, 8, 20⟩, ⟨11, 10, 7, 2⟩, ⟨11, 10, 6, 4⟩, ⟨11, 10, 5, 6⟩, ⟨11, 10, 4, 8⟩, ⟨11, 10, 3, 10⟩, ⟨11, 10, 2, 12⟩, ⟨11, 10, 1, 14⟩, ⟨11, 10, 0, 16⟩]
  exact AllWinning.cons node_15479 (AllWinning.cons node_14488 (AllWinning.cons node_13460 (AllWinning.cons node_12456 (AllWinning.cons node_11400 (AllWinning.cons node_10297 (AllWinning.cons node_9238 (AllWinning.cons node_8189 (AllWinning.cons node_7161 (AllWinning.cons node_6161 (AllWinning.cons node_5358 (AllWinning.cons node_15533 (AllWinning.cons node_14598 (AllWinning.cons node_13625 (AllWinning.cons node_12674 (AllWinning.cons node_11679 (AllWinning.cons node_10677 (AllWinning.cons node_9629 (AllWinning.cons node_8678 (AllWinning.cons node_7703 (AllWinning.cons node_6740 (AllWinning.cons node_15535 (AllWinning.cons node_14603 (AllWinning.cons node_13635 (AllWinning.cons node_12687 (AllWinning.cons node_11699 (AllWinning.cons node_10703 (AllWinning.cons node_9660 (AllWinning.cons node_8709 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16578 : Outcome ⟨11, 10, 8, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 8, 2⟩, ⟨9, 10, 8, 4⟩, ⟨8, 10, 8, 6⟩, ⟨7, 10, 8, 8⟩, ⟨6, 10, 8, 10⟩, ⟨5, 10, 8, 12⟩, ⟨4, 10, 8, 14⟩, ⟨3, 10, 8, 16⟩, ⟨2, 10, 8, 18⟩, ⟨1, 10, 8, 20⟩, ⟨0, 10, 8, 22⟩, ⟨11, 9, 8, 2⟩, ⟨11, 8, 8, 4⟩, ⟨11, 7, 8, 6⟩, ⟨11, 6, 8, 8⟩, ⟨11, 5, 8, 10⟩, ⟨11, 4, 8, 12⟩, ⟨11, 3, 8, 14⟩, ⟨11, 2, 8, 16⟩, ⟨11, 1, 8, 18⟩, ⟨11, 0, 8, 20⟩, ⟨11, 10, 7, 2⟩, ⟨11, 10, 6, 4⟩, ⟨11, 10, 5, 6⟩, ⟨11, 10, 4, 8⟩, ⟨11, 10, 3, 10⟩, ⟨11, 10, 2, 12⟩, ⟨11, 10, 1, 14⟩, ⟨11, 10, 0, 16⟩]
  exact AllWinning.cons node_15479 (AllWinning.cons node_14488 (AllWinning.cons node_13460 (AllWinning.cons node_12456 (AllWinning.cons node_11400 (AllWinning.cons node_10297 (AllWinning.cons node_9238 (AllWinning.cons node_8189 (AllWinning.cons node_7161 (AllWinning.cons node_6161 (AllWinning.cons node_5358 (AllWinning.cons node_15533 (AllWinning.cons node_14598 (AllWinning.cons node_13625 (AllWinning.cons node_12674 (AllWinning.cons node_11679 (AllWinning.cons node_10677 (AllWinning.cons node_9629 (AllWinning.cons node_8678 (AllWinning.cons node_7703 (AllWinning.cons node_6740 (AllWinning.cons node_15535 (AllWinning.cons node_14603 (AllWinning.cons node_13635 (AllWinning.cons node_12687 (AllWinning.cons node_11699 (AllWinning.cons node_10703 (AllWinning.cons node_9660 (AllWinning.cons node_8709 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16579 : Outcome ⟨11, 11, 7, 4⟩ true :=
  Outcome.win (q := ⟨11, 11, 5, 4⟩) (by decide) node_14607

theorem node_16580 : Outcome ⟨11, 11, 7, 10⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 20⟩) (by decide) node_6171

theorem node_16581 : Outcome ⟨11, 12, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 12, 6, 2⟩, ⟨9, 12, 6, 4⟩, ⟨11, 11, 6, 2⟩, ⟨11, 10, 6, 4⟩, ⟨11, 12, 5, 2⟩, ⟨11, 12, 4, 4⟩]
  exact AllWinning.cons node_15485 (AllWinning.cons node_14492 (AllWinning.cons node_15538 (AllWinning.cons node_14603 (AllWinning.cons node_15541 (AllWinning.cons node_14609 (AllWinning.nil))))))

theorem node_16582 : Outcome ⟨11, 12, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 12, 6, 2⟩, ⟨9, 12, 6, 4⟩, ⟨8, 12, 6, 6⟩, ⟨7, 12, 6, 8⟩, ⟨11, 11, 6, 2⟩, ⟨11, 10, 6, 4⟩, ⟨11, 9, 6, 6⟩, ⟨11, 8, 6, 8⟩, ⟨11, 12, 5, 2⟩, ⟨11, 12, 4, 4⟩, ⟨11, 12, 3, 6⟩, ⟨11, 12, 2, 8⟩]
  exact AllWinning.cons node_15485 (AllWinning.cons node_14492 (AllWinning.cons node_13468 (AllWinning.cons node_12461 (AllWinning.cons node_15538 (AllWinning.cons node_14603 (AllWinning.cons node_13631 (AllWinning.cons node_12680 (AllWinning.cons node_15541 (AllWinning.cons node_14609 (AllWinning.cons node_13642 (AllWinning.cons node_12695 (AllWinning.nil))))))))))))

theorem node_16583 : Outcome ⟨11, 12, 6, 6⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 10⟩) (by decide) node_11409

theorem node_16584 : Outcome ⟨11, 12, 6, 10⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 20⟩) (by decide) node_6759

theorem node_16585 : Outcome ⟨11, 12, 6, 12⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 20⟩) (by decide) node_6759

theorem node_16586 : Outcome ⟨11, 13, 5, 4⟩ true :=
  Outcome.win (q := ⟨11, 13, 2, 6⟩) (by decide) node_13647

theorem node_16587 : Outcome ⟨11, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 4, 2⟩) (by decide) node_15491

theorem node_16588 : Outcome ⟨11, 14, 4, 8⟩ true :=
  Outcome.win (q := ⟨10, 14, 4, 2⟩) (by decide) node_15491

theorem node_16589 : Outcome ⟨11, 14, 4, 16⟩ true :=
  Outcome.win (q := ⟨10, 14, 4, 2⟩) (by decide) node_15491

theorem node_16590 : Outcome ⟨11, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨11, 15, 1, 4⟩) (by decide) node_14616

theorem node_16591 : Outcome ⟨11, 15, 3, 6⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 8⟩) (by decide) node_12472

theorem node_16592 : Outcome ⟨11, 15, 3, 8⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 8⟩) (by decide) node_12472

theorem node_16593 : Outcome ⟨11, 15, 3, 14⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 20⟩) (by decide) node_6783

theorem node_16594 : Outcome ⟨11, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 0, 4⟩) (by decide) node_14620

theorem node_16595 : Outcome ⟨11, 16, 2, 10⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 20⟩) (by decide) node_6793

theorem node_16596 : Outcome ⟨11, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨11, 15, 1, 4⟩) (by decide) node_14616

theorem node_16597 : Outcome ⟨11, 17, 1, 4⟩ true :=
  Outcome.win (q := ⟨11, 15, 1, 4⟩) (by decide) node_14616

theorem node_16598 : Outcome ⟨11, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 0, 4⟩) (by decide) node_14620

theorem node_16599 : Outcome ⟨11, 18, 0, 4⟩ true :=
  Outcome.win (q := ⟨11, 16, 0, 4⟩) (by decide) node_14620

theorem node_16600 : Outcome ⟨11, 18, 0, 8⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 14⟩) (by decide) node_9667

theorem node_16601 : Outcome ⟨12, 0, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 0, 17, 2⟩, ⟨10, 0, 17, 4⟩, ⟨12, 0, 16, 2⟩, ⟨12, 0, 15, 4⟩]
  exact AllWinning.cons node_15508 (AllWinning.cons node_14514 (AllWinning.cons node_15558 (AllWinning.cons node_14624 (AllWinning.nil))))

theorem node_16602 : Outcome ⟨12, 0, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 0, 17, 2⟩, ⟨10, 0, 17, 4⟩, ⟨9, 0, 17, 6⟩, ⟨8, 0, 17, 8⟩, ⟨12, 0, 16, 2⟩, ⟨12, 0, 15, 4⟩, ⟨12, 0, 14, 6⟩, ⟨12, 0, 13, 8⟩]
  exact AllWinning.cons node_15508 (AllWinning.cons node_14514 (AllWinning.cons node_13490 (AllWinning.cons node_12487 (AllWinning.cons node_15558 (AllWinning.cons node_14624 (AllWinning.cons node_13655 (AllWinning.cons node_12703 (AllWinning.nil))))))))

theorem node_16603 : Outcome ⟨12, 0, 17, 6⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 10⟩) (by decide) node_11713

theorem node_16604 : Outcome ⟨12, 0, 17, 10⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 10⟩) (by decide) node_11713

theorem node_16605 : Outcome ⟨12, 1, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 16, 2⟩, ⟨10, 1, 16, 4⟩, ⟨12, 0, 16, 2⟩, ⟨12, 1, 15, 2⟩, ⟨12, 1, 14, 4⟩]
  exact AllWinning.cons node_15511 (AllWinning.cons node_14518 (AllWinning.cons node_15558 (AllWinning.cons node_15561 (AllWinning.cons node_14628 (AllWinning.nil)))))

theorem node_16606 : Outcome ⟨12, 1, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 16, 2⟩, ⟨10, 1, 16, 4⟩, ⟨9, 1, 16, 6⟩, ⟨8, 1, 16, 8⟩, ⟨12, 0, 16, 2⟩, ⟨12, 1, 15, 2⟩, ⟨12, 1, 14, 4⟩, ⟨12, 1, 13, 6⟩, ⟨12, 1, 12, 8⟩]
  exact AllWinning.cons node_15511 (AllWinning.cons node_14518 (AllWinning.cons node_13494 (AllWinning.cons node_12491 (AllWinning.cons node_15558 (AllWinning.cons node_15561 (AllWinning.cons node_14628 (AllWinning.cons node_13658 (AllWinning.cons node_12706 (AllWinning.nil)))))))))

theorem node_16607 : Outcome ⟨12, 1, 16, 6⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 12⟩) (by decide) node_10344

theorem node_16608 : Outcome ⟨12, 1, 16, 10⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 16⟩) (by decide) node_8720

theorem node_16609 : Outcome ⟨12, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 2⟩) (by decide) node_15565

theorem node_16610 : Outcome ⟨12, 2, 15, 10⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 6⟩) (by decide) node_13497

theorem node_16611 : Outcome ⟨12, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 14, 2⟩) (by decide) node_15516

theorem node_16612 : Outcome ⟨12, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 14, 2⟩) (by decide) node_15516

theorem node_16613 : Outcome ⟨12, 3, 14, 10⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 12⟩) (by decide) node_10354

theorem node_16614 : Outcome ⟨12, 3, 14, 12⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 12⟩) (by decide) node_10354

theorem node_16615 : Outcome ⟨12, 4, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 4, 13, 2⟩, ⟨10, 4, 13, 4⟩, ⟨12, 3, 13, 2⟩, ⟨12, 2, 13, 4⟩, ⟨12, 4, 12, 2⟩, ⟨12, 4, 11, 4⟩]
  exact AllWinning.cons node_15520 (AllWinning.cons node_14526 (AllWinning.cons node_15571 (AllWinning.cons node_14632 (AllWinning.cons node_15574 (AllWinning.cons node_14636 (AllWinning.nil))))))

theorem node_16616 : Outcome ⟨12, 4, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 4, 13, 2⟩, ⟨10, 4, 13, 4⟩, ⟨9, 4, 13, 6⟩, ⟨8, 4, 13, 8⟩, ⟨12, 3, 13, 2⟩, ⟨12, 2, 13, 4⟩, ⟨12, 1, 13, 6⟩, ⟨12, 0, 13, 8⟩, ⟨12, 4, 12, 2⟩, ⟨12, 4, 11, 4⟩, ⟨12, 4, 10, 6⟩, ⟨12, 4, 9, 8⟩]
  exact AllWinning.cons node_15520 (AllWinning.cons node_14526 (AllWinning.cons node_13505 (AllWinning.cons node_12500 (AllWinning.cons node_15571 (AllWinning.cons node_14632 (AllWinning.cons node_13658 (AllWinning.cons node_12703 (AllWinning.cons node_15574 (AllWinning.cons node_14636 (AllWinning.cons node_13669 (AllWinning.cons node_12715 (AllWinning.nil))))))))))))

theorem node_16617 : Outcome ⟨12, 4, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 4, 13, 2⟩, ⟨10, 4, 13, 4⟩, ⟨9, 4, 13, 6⟩, ⟨8, 4, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨6, 4, 13, 12⟩, ⟨12, 3, 13, 2⟩, ⟨12, 2, 13, 4⟩, ⟨12, 1, 13, 6⟩, ⟨12, 0, 13, 8⟩, ⟨12, 4, 12, 2⟩, ⟨12, 4, 11, 4⟩, ⟨12, 4, 10, 6⟩, ⟨12, 4, 9, 8⟩, ⟨12, 4, 8, 10⟩, ⟨12, 4, 7, 12⟩]
  exact AllWinning.cons node_15520 (AllWinning.cons node_14526 (AllWinning.cons node_13505 (AllWinning.cons node_12500 (AllWinning.cons node_11447 (AllWinning.cons node_10358 (AllWinning.cons node_15571 (AllWinning.cons node_14632 (AllWinning.cons node_13658 (AllWinning.cons node_12703 (AllWinning.cons node_15574 (AllWinning.cons node_14636 (AllWinning.cons node_13669 (AllWinning.cons node_12715 (AllWinning.cons node_11736 (AllWinning.cons node_10724 (AllWinning.nil))))))))))))))))

theorem node_16618 : Outcome ⟨12, 4, 13, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 4, 13, 2⟩, ⟨10, 4, 13, 4⟩, ⟨9, 4, 13, 6⟩, ⟨8, 4, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨6, 4, 13, 12⟩, ⟨5, 4, 13, 14⟩, ⟨4, 4, 13, 16⟩, ⟨3, 4, 13, 18⟩, ⟨2, 4, 13, 20⟩, ⟨1, 4, 13, 22⟩, ⟨0, 4, 13, 24⟩, ⟨12, 3, 13, 2⟩, ⟨12, 2, 13, 4⟩, ⟨12, 1, 13, 6⟩, ⟨12, 0, 13, 8⟩, ⟨12, 4, 12, 2⟩, ⟨12, 4, 11, 4⟩, ⟨12, 4, 10, 6⟩, ⟨12, 4, 9, 8⟩, ⟨12, 4, 8, 10⟩, ⟨12, 4, 7, 12⟩, ⟨12, 4, 6, 14⟩, ⟨12, 4, 5, 16⟩, ⟨12, 4, 4, 18⟩, ⟨12, 4, 3, 20⟩, ⟨12, 4, 2, 22⟩, ⟨12, 4, 1, 24⟩]
  exact AllWinning.cons node_15520 (AllWinning.cons node_14526 (AllWinning.cons node_13505 (AllWinning.cons node_12500 (AllWinning.cons node_11447 (AllWinning.cons node_10358 (AllWinning.cons node_9286 (AllWinning.cons node_8238 (AllWinning.cons node_7216 (AllWinning.cons node_6212 (AllWinning.cons node_5407 (AllWinning.cons node_4590 (AllWinning.cons node_15571 (AllWinning.cons node_14632 (AllWinning.cons node_13658 (AllWinning.cons node_12703 (AllWinning.cons node_15574 (AllWinning.cons node_14636 (AllWinning.cons node_13669 (AllWinning.cons node_12715 (AllWinning.cons node_11736 (AllWinning.cons node_10724 (AllWinning.cons node_9686 (AllWinning.cons node_8737 (AllWinning.cons node_7746 (AllWinning.cons node_6827 (AllWinning.cons node_5945 (AllWinning.cons node_5232 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_16619 : Outcome ⟨12, 4, 13, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 4, 13, 2⟩, ⟨10, 4, 13, 4⟩, ⟨9, 4, 13, 6⟩, ⟨8, 4, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨6, 4, 13, 12⟩, ⟨5, 4, 13, 14⟩, ⟨4, 4, 13, 16⟩, ⟨3, 4, 13, 18⟩, ⟨2, 4, 13, 20⟩, ⟨1, 4, 13, 22⟩, ⟨0, 4, 13, 24⟩, ⟨12, 3, 13, 2⟩, ⟨12, 2, 13, 4⟩, ⟨12, 1, 13, 6⟩, ⟨12, 0, 13, 8⟩, ⟨12, 4, 12, 2⟩, ⟨12, 4, 11, 4⟩, ⟨12, 4, 10, 6⟩, ⟨12, 4, 9, 8⟩, ⟨12, 4, 8, 10⟩, ⟨12, 4, 7, 12⟩, ⟨12, 4, 6, 14⟩, ⟨12, 4, 5, 16⟩, ⟨12, 4, 4, 18⟩, ⟨12, 4, 3, 20⟩, ⟨12, 4, 2, 22⟩, ⟨12, 4, 1, 24⟩, ⟨12, 4, 0, 26⟩]
  exact AllWinning.cons node_15520 (AllWinning.cons node_14526 (AllWinning.cons node_13505 (AllWinning.cons node_12500 (AllWinning.cons node_11447 (AllWinning.cons node_10358 (AllWinning.cons node_9286 (AllWinning.cons node_8238 (AllWinning.cons node_7216 (AllWinning.cons node_6212 (AllWinning.cons node_5407 (AllWinning.cons node_4590 (AllWinning.cons node_15571 (AllWinning.cons node_14632 (AllWinning.cons node_13658 (AllWinning.cons node_12703 (AllWinning.cons node_15574 (AllWinning.cons node_14636 (AllWinning.cons node_13669 (AllWinning.cons node_12715 (AllWinning.cons node_11736 (AllWinning.cons node_10724 (AllWinning.cons node_9686 (AllWinning.cons node_8737 (AllWinning.cons node_7746 (AllWinning.cons node_6827 (AllWinning.cons node_5945 (AllWinning.cons node_5232 (AllWinning.cons node_4534 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16620 : Outcome ⟨12, 4, 13, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 4, 13, 2⟩, ⟨10, 4, 13, 4⟩, ⟨9, 4, 13, 6⟩, ⟨8, 4, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨6, 4, 13, 12⟩, ⟨5, 4, 13, 14⟩, ⟨4, 4, 13, 16⟩, ⟨3, 4, 13, 18⟩, ⟨2, 4, 13, 20⟩, ⟨1, 4, 13, 22⟩, ⟨0, 4, 13, 24⟩, ⟨12, 3, 13, 2⟩, ⟨12, 2, 13, 4⟩, ⟨12, 1, 13, 6⟩, ⟨12, 0, 13, 8⟩, ⟨12, 4, 12, 2⟩, ⟨12, 4, 11, 4⟩, ⟨12, 4, 10, 6⟩, ⟨12, 4, 9, 8⟩, ⟨12, 4, 8, 10⟩, ⟨12, 4, 7, 12⟩, ⟨12, 4, 6, 14⟩, ⟨12, 4, 5, 16⟩, ⟨12, 4, 4, 18⟩, ⟨12, 4, 3, 20⟩, ⟨12, 4, 2, 22⟩, ⟨12, 4, 1, 24⟩, ⟨12, 4, 0, 26⟩]
  exact AllWinning.cons node_15520 (AllWinning.cons node_14526 (AllWinning.cons node_13505 (AllWinning.cons node_12500 (AllWinning.cons node_11447 (AllWinning.cons node_10358 (AllWinning.cons node_9286 (AllWinning.cons node_8238 (AllWinning.cons node_7216 (AllWinning.cons node_6212 (AllWinning.cons node_5407 (AllWinning.cons node_4590 (AllWinning.cons node_15571 (AllWinning.cons node_14632 (AllWinning.cons node_13658 (AllWinning.cons node_12703 (AllWinning.cons node_15574 (AllWinning.cons node_14636 (AllWinning.cons node_13669 (AllWinning.cons node_12715 (AllWinning.cons node_11736 (AllWinning.cons node_10724 (AllWinning.cons node_9686 (AllWinning.cons node_8737 (AllWinning.cons node_7746 (AllWinning.cons node_6827 (AllWinning.cons node_5945 (AllWinning.cons node_5232 (AllWinning.cons node_4534 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16621 : Outcome ⟨12, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 4⟩) (by decide) node_14529

theorem node_16622 : Outcome ⟨12, 5, 12, 12⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 10⟩) (by decide) node_11713

theorem node_16623 : Outcome ⟨12, 6, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 6, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨12, 5, 11, 2⟩, ⟨12, 4, 11, 4⟩, ⟨12, 6, 10, 2⟩, ⟨12, 6, 9, 4⟩]
  exact AllWinning.cons node_15525 (AllWinning.cons node_14534 (AllWinning.cons node_15576 (AllWinning.cons node_14636 (AllWinning.cons node_15578 (AllWinning.cons node_14643 (AllWinning.nil))))))

theorem node_16624 : Outcome ⟨12, 6, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 6, 11, 2⟩, ⟨10, 6, 11, 4⟩, ⟨9, 6, 11, 6⟩, ⟨8, 6, 11, 8⟩, ⟨12, 5, 11, 2⟩, ⟨12, 4, 11, 4⟩, ⟨12, 3, 11, 6⟩, ⟨12, 2, 11, 8⟩, ⟨12, 6, 10, 2⟩, ⟨12, 6, 9, 4⟩, ⟨12, 6, 8, 6⟩, ⟨12, 6, 7, 8⟩]
  exact AllWinning.cons node_15525 (AllWinning.cons node_14534 (AllWinning.cons node_13509 (AllWinning.cons node_12507 (AllWinning.cons node_15576 (AllWinning.cons node_14636 (AllWinning.cons node_13665 (AllWinning.cons node_12710 (AllWinning.cons node_15578 (AllWinning.cons node_14643 (AllWinning.cons node_13674 (AllWinning.cons node_12721 (AllWinning.nil))))))))))))

theorem node_16625 : Outcome ⟨12, 6, 11, 6⟩ true :=
  Outcome.win (q := ⟨12, 6, 6, 10⟩) (by decide) node_11745

theorem node_16626 : Outcome ⟨12, 6, 11, 10⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 20⟩) (by decide) node_6225

theorem node_16627 : Outcome ⟨12, 6, 11, 12⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 20⟩) (by decide) node_6225

theorem node_16628 : Outcome ⟨12, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 6⟩) (by decide) node_13678

theorem node_16629 : Outcome ⟨12, 7, 10, 10⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 6⟩) (by decide) node_13678

theorem node_16630 : Outcome ⟨12, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨9, 8, 9, 6⟩) (by decide) node_13515

theorem node_16631 : Outcome ⟨12, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨9, 9, 8, 6⟩) (by decide) node_13518

theorem node_16632 : Outcome ⟨12, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 6⟩) (by decide) node_13678

theorem node_16633 : Outcome ⟨12, 10, 7, 10⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 6⟩) (by decide) node_13678

theorem node_16634 : Outcome ⟨12, 11, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 11, 6, 2⟩, ⟨10, 11, 6, 4⟩, ⟨12, 10, 6, 2⟩, ⟨12, 9, 6, 4⟩, ⟨12, 11, 5, 2⟩, ⟨12, 11, 4, 4⟩]
  exact AllWinning.cons node_15538 (AllWinning.cons node_14549 (AllWinning.cons node_15590 (AllWinning.cons node_14652 (AllWinning.cons node_15592 (AllWinning.cons node_14660 (AllWinning.nil))))))

theorem node_16635 : Outcome ⟨12, 11, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 11, 6, 2⟩, ⟨10, 11, 6, 4⟩, ⟨9, 11, 6, 6⟩, ⟨8, 11, 6, 8⟩, ⟨12, 10, 6, 2⟩, ⟨12, 9, 6, 4⟩, ⟨12, 8, 6, 6⟩, ⟨12, 7, 6, 8⟩, ⟨12, 11, 5, 2⟩, ⟨12, 11, 4, 4⟩, ⟨12, 11, 3, 6⟩, ⟨12, 11, 2, 8⟩]
  exact AllWinning.cons node_15538 (AllWinning.cons node_14549 (AllWinning.cons node_13522 (AllWinning.cons node_12525 (AllWinning.cons node_15590 (AllWinning.cons node_14652 (AllWinning.cons node_13683 (AllWinning.cons node_12725 (AllWinning.cons node_15592 (AllWinning.cons node_14660 (AllWinning.cons node_13693 (AllWinning.cons node_12737 (AllWinning.nil))))))))))))

theorem node_16636 : Outcome ⟨12, 11, 6, 6⟩ true :=
  Outcome.win (q := ⟨12, 6, 6, 10⟩) (by decide) node_11745

theorem node_16637 : Outcome ⟨12, 11, 6, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 20⟩) (by decide) node_6249

theorem node_16638 : Outcome ⟨12, 11, 6, 12⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 20⟩) (by decide) node_6249

theorem node_16639 : Outcome ⟨12, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 4⟩) (by decide) node_14553

theorem node_16640 : Outcome ⟨12, 12, 5, 12⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 10⟩) (by decide) node_11774

theorem node_16641 : Outcome ⟨12, 13, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 13, 4, 2⟩, ⟨10, 13, 4, 4⟩, ⟨12, 12, 4, 2⟩, ⟨12, 11, 4, 4⟩, ⟨12, 13, 3, 2⟩, ⟨12, 13, 2, 4⟩]
  exact AllWinning.cons node_15543 (AllWinning.cons node_14559 (AllWinning.cons node_15594 (AllWinning.cons node_14660 (AllWinning.cons node_15596 (AllWinning.cons node_14666 (AllWinning.nil))))))

theorem node_16642 : Outcome ⟨12, 13, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 13, 4, 2⟩, ⟨10, 13, 4, 4⟩, ⟨9, 13, 4, 6⟩, ⟨8, 13, 4, 8⟩, ⟨12, 12, 4, 2⟩, ⟨12, 11, 4, 4⟩, ⟨12, 10, 4, 6⟩, ⟨12, 9, 4, 8⟩, ⟨12, 13, 3, 2⟩, ⟨12, 13, 2, 4⟩, ⟨12, 13, 1, 6⟩, ⟨12, 13, 0, 8⟩]
  exact AllWinning.cons node_15543 (AllWinning.cons node_14559 (AllWinning.cons node_13528 (AllWinning.cons node_12532 (AllWinning.cons node_15594 (AllWinning.cons node_14660 (AllWinning.cons node_13690 (AllWinning.cons node_12732 (AllWinning.cons node_15596 (AllWinning.cons node_14666 (AllWinning.cons node_13698 (AllWinning.cons node_12744 (AllWinning.nil))))))))))))

theorem node_16643 : Outcome ⟨12, 13, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 13, 4, 2⟩, ⟨10, 13, 4, 4⟩, ⟨9, 13, 4, 6⟩, ⟨8, 13, 4, 8⟩, ⟨7, 13, 4, 10⟩, ⟨6, 13, 4, 12⟩, ⟨12, 12, 4, 2⟩, ⟨12, 11, 4, 4⟩, ⟨12, 10, 4, 6⟩, ⟨12, 9, 4, 8⟩, ⟨12, 8, 4, 10⟩, ⟨12, 7, 4, 12⟩, ⟨12, 13, 3, 2⟩, ⟨12, 13, 2, 4⟩, ⟨12, 13, 1, 6⟩, ⟨12, 13, 0, 8⟩]
  exact AllWinning.cons node_15543 (AllWinning.cons node_14559 (AllWinning.cons node_13528 (AllWinning.cons node_12532 (AllWinning.cons node_11480 (AllWinning.cons node_10394 (AllWinning.cons node_15594 (AllWinning.cons node_14660 (AllWinning.cons node_13690 (AllWinning.cons node_12732 (AllWinning.cons node_11754 (AllWinning.cons node_10737 (AllWinning.cons node_15596 (AllWinning.cons node_14666 (AllWinning.cons node_13698 (AllWinning.cons node_12744 (AllWinning.nil))))))))))))))))

end RQ9F1
