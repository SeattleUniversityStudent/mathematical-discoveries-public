import Chunk40
set_option autoImplicit false
namespace RQ9F1

theorem node_9495 : Outcome ⟨8, 8, 6, 24⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 12⟩) (by decide) node_4436

theorem node_9496 : Outcome ⟨8, 9, 5, 2⟩ true :=
  Outcome.win (q := ⟨8, 8, 5, 2⟩) (by decide) node_8553

theorem node_9497 : Outcome ⟨8, 9, 5, 8⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 14⟩) (by decide) node_3442

theorem node_9498 : Outcome ⟨8, 9, 5, 12⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 14⟩) (by decide) node_3442

theorem node_9499 : Outcome ⟨8, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9500 : Outcome ⟨8, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9501 : Outcome ⟨8, 10, 4, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9502 : Outcome ⟨8, 10, 4, 14⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9503 : Outcome ⟨8, 11, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 11, 3, 2⟩, ⟨6, 11, 3, 4⟩, ⟨8, 10, 3, 2⟩, ⟨8, 9, 3, 4⟩, ⟨8, 11, 2, 2⟩, ⟨8, 11, 1, 4⟩]
  exact AllWinning.cons node_8478 (AllWinning.cons node_7466 (AllWinning.cons node_8561 (AllWinning.cons node_7572 (AllWinning.cons node_8566 (AllWinning.cons node_7581 (AllWinning.nil))))))

theorem node_9504 : Outcome ⟨8, 11, 3, 8⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 6⟩) (by decide) node_6467

theorem node_9505 : Outcome ⟨8, 11, 3, 10⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 6⟩) (by decide) node_6467

theorem node_9506 : Outcome ⟨8, 11, 3, 14⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 6⟩) (by decide) node_6467

theorem node_9507 : Outcome ⟨8, 12, 2, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 2⟩) (by decide) node_8482

theorem node_9508 : Outcome ⟨8, 12, 2, 12⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 2⟩) (by decide) node_8482

theorem node_9509 : Outcome ⟨8, 12, 2, 14⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 2⟩) (by decide) node_8482

theorem node_9510 : Outcome ⟨8, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨6, 13, 1, 4⟩) (by decide) node_7473

theorem node_9511 : Outcome ⟨8, 13, 1, 18⟩ true :=
  Outcome.win (q := ⟨6, 13, 1, 4⟩) (by decide) node_7473

theorem node_9512 : Outcome ⟨8, 14, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 0, 4⟩) (by decide) node_7478

theorem node_9513 : Outcome ⟨8, 14, 0, 4⟩ true :=
  Outcome.win (q := ⟨6, 14, 0, 4⟩) (by decide) node_7478

theorem node_9514 : Outcome ⟨8, 14, 0, 12⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 12⟩) (by decide) node_4436

theorem node_9515 : Outcome ⟨9, 0, 13, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 13, 2⟩) (by decide) node_8499

theorem node_9516 : Outcome ⟨9, 0, 13, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 8⟩) (by decide) node_5823

theorem node_9517 : Outcome ⟨9, 0, 13, 14⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 8⟩) (by decide) node_5823

theorem node_9518 : Outcome ⟨9, 1, 12, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 10, 4⟩) (by decide) node_7588

theorem node_9519 : Outcome ⟨9, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 10, 4⟩) (by decide) node_7588

theorem node_9520 : Outcome ⟨9, 2, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 2, 11, 2⟩, ⟨7, 2, 11, 4⟩, ⟨9, 1, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨9, 2, 10, 2⟩, ⟨9, 2, 9, 4⟩]
  exact AllWinning.cons node_8512 (AllWinning.cons node_7492 (AllWinning.cons node_8585 (AllWinning.cons node_7585 (AllWinning.cons node_8588 (AllWinning.cons node_7592 (AllWinning.nil))))))

theorem node_9521 : Outcome ⟨9, 2, 11, 8⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 6⟩) (by decide) node_6498

theorem node_9522 : Outcome ⟨9, 2, 11, 16⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 6⟩) (by decide) node_6498

theorem node_9523 : Outcome ⟨9, 3, 10, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9524 : Outcome ⟨9, 3, 10, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9525 : Outcome ⟨9, 3, 10, 6⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9526 : Outcome ⟨9, 3, 10, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9527 : Outcome ⟨9, 4, 9, 2⟩ true :=
  Outcome.win (q := ⟨9, 3, 9, 2⟩) (by decide) node_8593

theorem node_9528 : Outcome ⟨9, 4, 9, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 8⟩) (by decide) node_5823

theorem node_9529 : Outcome ⟨9, 4, 9, 14⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 8⟩) (by decide) node_5823

theorem node_9530 : Outcome ⟨9, 5, 8, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 8, 2⟩) (by decide) node_8524

theorem node_9531 : Outcome ⟨9, 5, 8, 8⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 14⟩) (by decide) node_3829

theorem node_9532 : Outcome ⟨9, 5, 8, 12⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 14⟩) (by decide) node_3829

theorem node_9533 : Outcome ⟨9, 6, 7, 4⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 2⟩) (by decide) node_8529

theorem node_9534 : Outcome ⟨9, 6, 7, 6⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 2⟩) (by decide) node_8529

theorem node_9535 : Outcome ⟨9, 6, 7, 8⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 2⟩) (by decide) node_8529

theorem node_9536 : Outcome ⟨9, 6, 7, 14⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 2⟩) (by decide) node_8529

theorem node_9537 : Outcome ⟨9, 6, 7, 20⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 2⟩) (by decide) node_8529

theorem node_9538 : Outcome ⟨9, 7, 6, 4⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 2⟩) (by decide) node_8541

theorem node_9539 : Outcome ⟨9, 7, 6, 6⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 2⟩) (by decide) node_8541

theorem node_9540 : Outcome ⟨9, 7, 6, 8⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 2⟩) (by decide) node_8541

theorem node_9541 : Outcome ⟨9, 7, 6, 14⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 2⟩) (by decide) node_8541

theorem node_9542 : Outcome ⟨9, 7, 6, 20⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 2⟩) (by decide) node_8541

theorem node_9543 : Outcome ⟨9, 8, 5, 2⟩ true :=
  Outcome.win (q := ⟨8, 8, 5, 2⟩) (by decide) node_8553

theorem node_9544 : Outcome ⟨9, 8, 5, 8⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 14⟩) (by decide) node_3801

theorem node_9545 : Outcome ⟨9, 8, 5, 12⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 14⟩) (by decide) node_3801

theorem node_9546 : Outcome ⟨9, 9, 4, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 3, 2⟩) (by decide) node_8612

theorem node_9547 : Outcome ⟨9, 9, 4, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 8⟩) (by decide) node_5873

theorem node_9548 : Outcome ⟨9, 9, 4, 14⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 8⟩) (by decide) node_5873

theorem node_9549 : Outcome ⟨9, 10, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9550 : Outcome ⟨9, 10, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9551 : Outcome ⟨9, 10, 3, 6⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9552 : Outcome ⟨9, 10, 3, 8⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9553 : Outcome ⟨9, 11, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 11, 2, 2⟩, ⟨7, 11, 2, 4⟩, ⟨9, 10, 2, 2⟩, ⟨9, 9, 2, 4⟩, ⟨9, 11, 1, 2⟩, ⟨9, 11, 0, 4⟩]
  exact AllWinning.cons node_8566 (AllWinning.cons node_7526 (AllWinning.cons node_8616 (AllWinning.cons node_7620 (AllWinning.cons node_8621 (AllWinning.cons node_7627 (AllWinning.nil))))))

theorem node_9554 : Outcome ⟨9, 11, 2, 8⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 6⟩) (by decide) node_6532

theorem node_9555 : Outcome ⟨9, 11, 2, 16⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 6⟩) (by decide) node_6532

theorem node_9556 : Outcome ⟨9, 12, 1, 2⟩ true :=
  Outcome.win (q := ⟨9, 10, 1, 4⟩) (by decide) node_7624

theorem node_9557 : Outcome ⟨9, 12, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 10, 1, 4⟩) (by decide) node_7624

theorem node_9558 : Outcome ⟨9, 13, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 13, 0, 2⟩) (by decide) node_8579

theorem node_9559 : Outcome ⟨9, 13, 0, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 8⟩) (by decide) node_5873

theorem node_9560 : Outcome ⟨9, 13, 0, 14⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 8⟩) (by decide) node_5873

theorem node_9561 : Outcome ⟨10, 0, 12, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9562 : Outcome ⟨10, 0, 12, 6⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9563 : Outcome ⟨10, 0, 12, 10⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9564 : Outcome ⟨10, 1, 11, 4⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 6⟩) (by decide) node_6558

theorem node_9565 : Outcome ⟨10, 1, 11, 6⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 6⟩) (by decide) node_6558

theorem node_9566 : Outcome ⟨10, 1, 11, 10⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 6⟩) (by decide) node_6558

theorem node_9567 : Outcome ⟨10, 1, 11, 14⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 6⟩) (by decide) node_6558

theorem node_9568 : Outcome ⟨10, 2, 10, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9569 : Outcome ⟨10, 2, 10, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9570 : Outcome ⟨10, 2, 10, 12⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 10⟩) (by decide) node_4934

theorem node_9571 : Outcome ⟨10, 3, 9, 2⟩ true :=
  Outcome.win (q := ⟨10, 1, 9, 4⟩) (by decide) node_7640

theorem node_9572 : Outcome ⟨10, 3, 9, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 9, 4⟩) (by decide) node_7640

theorem node_9573 : Outcome ⟨10, 3, 9, 6⟩ true :=
  Outcome.win (q := ⟨10, 1, 9, 4⟩) (by decide) node_7640

theorem node_9574 : Outcome ⟨10, 3, 9, 8⟩ true :=
  Outcome.win (q := ⟨10, 1, 9, 4⟩) (by decide) node_7640

theorem node_9575 : Outcome ⟨10, 4, 8, 2⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9576 : Outcome ⟨10, 4, 8, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9577 : Outcome ⟨10, 4, 8, 6⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9578 : Outcome ⟨10, 4, 8, 14⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9579 : Outcome ⟨10, 5, 7, 2⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 4⟩) (by decide) node_7647

theorem node_9580 : Outcome ⟨10, 5, 7, 4⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 4⟩) (by decide) node_7647

theorem node_9581 : Outcome ⟨10, 5, 7, 10⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9582 : Outcome ⟨10, 5, 7, 14⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9583 : Outcome ⟨10, 5, 7, 24⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9584 : Outcome ⟨10, 6, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9585 : Outcome ⟨10, 6, 6, 6⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9586 : Outcome ⟨10, 6, 6, 24⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 20⟩) (by decide) node_1898

theorem node_9587 : Outcome ⟨10, 7, 5, 2⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9588 : Outcome ⟨10, 7, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9589 : Outcome ⟨10, 7, 5, 10⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9590 : Outcome ⟨10, 7, 5, 14⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9591 : Outcome ⟨10, 7, 5, 24⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9592 : Outcome ⟨10, 8, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9593 : Outcome ⟨10, 8, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9594 : Outcome ⟨10, 8, 4, 6⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9595 : Outcome ⟨10, 8, 4, 14⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9596 : Outcome ⟨10, 9, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9597 : Outcome ⟨10, 9, 3, 4⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9598 : Outcome ⟨10, 9, 3, 6⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9599 : Outcome ⟨10, 9, 3, 8⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9600 : Outcome ⟨10, 10, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9601 : Outcome ⟨10, 10, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9602 : Outcome ⟨10, 10, 2, 12⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 10⟩) (by decide) node_4972

theorem node_9603 : Outcome ⟨10, 11, 1, 6⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 6⟩) (by decide) node_6605

theorem node_9604 : Outcome ⟨10, 11, 1, 10⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 6⟩) (by decide) node_6605

theorem node_9605 : Outcome ⟨10, 11, 1, 14⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 6⟩) (by decide) node_6605

theorem node_9606 : Outcome ⟨10, 12, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9607 : Outcome ⟨10, 12, 0, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9608 : Outcome ⟨10, 12, 0, 10⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9609 : Outcome ⟨11, 0, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.nil))))

theorem node_9610 : Outcome ⟨11, 0, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.nil))))))))

theorem node_9611 : Outcome ⟨11, 0, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.nil))))))))))))

theorem node_9612 : Outcome ⟨11, 0, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨4, 0, 11, 14⟩, ⟨3, 0, 11, 16⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩, ⟨11, 0, 4, 14⟩, ⟨11, 0, 3, 16⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_3586 (AllWinning.cons node_2995 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.cons node_3866 (AllWinning.cons node_3283 (AllWinning.nil))))))))))))))))

theorem node_9613 : Outcome ⟨11, 0, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨4, 0, 11, 14⟩, ⟨3, 0, 11, 16⟩, ⟨2, 0, 11, 18⟩, ⟨1, 0, 11, 20⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩, ⟨11, 0, 4, 14⟩, ⟨11, 0, 3, 16⟩, ⟨11, 0, 2, 18⟩, ⟨11, 0, 1, 20⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_3586 (AllWinning.cons node_2995 (AllWinning.cons node_2483 (AllWinning.cons node_1932 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.cons node_3866 (AllWinning.cons node_3283 (AllWinning.cons node_2795 (AllWinning.cons node_2351 (AllWinning.nil))))))))))))))))))))

theorem node_9614 : Outcome ⟨11, 0, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨4, 0, 11, 14⟩, ⟨3, 0, 11, 16⟩, ⟨2, 0, 11, 18⟩, ⟨1, 0, 11, 20⟩, ⟨0, 0, 11, 22⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩, ⟨11, 0, 4, 14⟩, ⟨11, 0, 3, 16⟩, ⟨11, 0, 2, 18⟩, ⟨11, 0, 1, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_3586 (AllWinning.cons node_2995 (AllWinning.cons node_2483 (AllWinning.cons node_1932 (AllWinning.cons node_1543 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.cons node_3866 (AllWinning.cons node_3283 (AllWinning.cons node_2795 (AllWinning.cons node_2351 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9615 : Outcome ⟨11, 0, 11, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨4, 0, 11, 14⟩, ⟨3, 0, 11, 16⟩, ⟨2, 0, 11, 18⟩, ⟨1, 0, 11, 20⟩, ⟨0, 0, 11, 22⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩, ⟨11, 0, 4, 14⟩, ⟨11, 0, 3, 16⟩, ⟨11, 0, 2, 18⟩, ⟨11, 0, 1, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_3586 (AllWinning.cons node_2995 (AllWinning.cons node_2483 (AllWinning.cons node_1932 (AllWinning.cons node_1543 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.cons node_3866 (AllWinning.cons node_3283 (AllWinning.cons node_2795 (AllWinning.cons node_2351 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9616 : Outcome ⟨11, 0, 11, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨4, 0, 11, 14⟩, ⟨3, 0, 11, 16⟩, ⟨2, 0, 11, 18⟩, ⟨1, 0, 11, 20⟩, ⟨0, 0, 11, 22⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩, ⟨11, 0, 4, 14⟩, ⟨11, 0, 3, 16⟩, ⟨11, 0, 2, 18⟩, ⟨11, 0, 1, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_3586 (AllWinning.cons node_2995 (AllWinning.cons node_2483 (AllWinning.cons node_1932 (AllWinning.cons node_1543 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.cons node_3866 (AllWinning.cons node_3283 (AllWinning.cons node_2795 (AllWinning.cons node_2351 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9617 : Outcome ⟨11, 0, 11, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨4, 0, 11, 14⟩, ⟨3, 0, 11, 16⟩, ⟨2, 0, 11, 18⟩, ⟨1, 0, 11, 20⟩, ⟨0, 0, 11, 22⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩, ⟨11, 0, 4, 14⟩, ⟨11, 0, 3, 16⟩, ⟨11, 0, 2, 18⟩, ⟨11, 0, 1, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_3586 (AllWinning.cons node_2995 (AllWinning.cons node_2483 (AllWinning.cons node_1932 (AllWinning.cons node_1543 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.cons node_3866 (AllWinning.cons node_3283 (AllWinning.cons node_2795 (AllWinning.cons node_2351 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9618 : Outcome ⟨11, 0, 11, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 11, 2⟩, ⟨9, 0, 11, 4⟩, ⟨8, 0, 11, 6⟩, ⟨7, 0, 11, 8⟩, ⟨6, 0, 11, 10⟩, ⟨5, 0, 11, 12⟩, ⟨4, 0, 11, 14⟩, ⟨3, 0, 11, 16⟩, ⟨2, 0, 11, 18⟩, ⟨1, 0, 11, 20⟩, ⟨0, 0, 11, 22⟩, ⟨11, 0, 10, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 0, 8, 6⟩, ⟨11, 0, 7, 8⟩, ⟨11, 0, 6, 10⟩, ⟨11, 0, 5, 12⟩, ⟨11, 0, 4, 14⟩, ⟨11, 0, 3, 16⟩, ⟨11, 0, 2, 18⟩, ⟨11, 0, 1, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8626 (AllWinning.cons node_7585 (AllWinning.cons node_6622 (AllWinning.cons node_5730 (AllWinning.cons node_4991 (AllWinning.cons node_4223 (AllWinning.cons node_3586 (AllWinning.cons node_2995 (AllWinning.cons node_2483 (AllWinning.cons node_1932 (AllWinning.cons node_1543 (AllWinning.cons node_8670 (AllWinning.cons node_7699 (AllWinning.cons node_6739 (AllWinning.cons node_5913 (AllWinning.cons node_5192 (AllWinning.cons node_4495 (AllWinning.cons node_3866 (AllWinning.cons node_3283 (AllWinning.cons node_2795 (AllWinning.cons node_2351 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9619 : Outcome ⟨11, 1, 10, 4⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 6⟩) (by decide) node_6743

theorem node_9620 : Outcome ⟨11, 1, 10, 6⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 6⟩) (by decide) node_6743

theorem node_9621 : Outcome ⟨11, 1, 10, 10⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 6⟩) (by decide) node_6743

theorem node_9622 : Outcome ⟨11, 1, 10, 14⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 6⟩) (by decide) node_6743

theorem node_9623 : Outcome ⟨11, 2, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 9, 2⟩, ⟨9, 2, 9, 4⟩, ⟨11, 1, 9, 2⟩, ⟨11, 0, 9, 4⟩, ⟨11, 2, 8, 2⟩, ⟨11, 2, 7, 4⟩]
  exact AllWinning.cons node_8631 (AllWinning.cons node_7592 (AllWinning.cons node_8673 (AllWinning.cons node_7699 (AllWinning.cons node_8676 (AllWinning.cons node_7705 (AllWinning.nil))))))

theorem node_9624 : Outcome ⟨11, 2, 9, 8⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9625 : Outcome ⟨11, 2, 9, 16⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9626 : Outcome ⟨11, 3, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 3, 8, 2⟩, ⟨9, 3, 8, 4⟩, ⟨11, 2, 8, 2⟩, ⟨11, 1, 8, 4⟩, ⟨11, 3, 7, 2⟩, ⟨11, 3, 6, 4⟩]
  exact AllWinning.cons node_8636 (AllWinning.cons node_7596 (AllWinning.cons node_8676 (AllWinning.cons node_7702 (AllWinning.cons node_8680 (AllWinning.cons node_7710 (AllWinning.nil))))))

theorem node_9627 : Outcome ⟨11, 3, 8, 8⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9628 : Outcome ⟨11, 3, 8, 10⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9629 : Outcome ⟨11, 3, 8, 14⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9630 : Outcome ⟨11, 3, 8, 22⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9631 : Outcome ⟨11, 4, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 4, 7, 2⟩, ⟨9, 4, 7, 4⟩, ⟨11, 3, 7, 2⟩, ⟨11, 2, 7, 4⟩, ⟨11, 4, 6, 2⟩, ⟨11, 4, 5, 4⟩]
  exact AllWinning.cons node_8641 (AllWinning.cons node_7601 (AllWinning.cons node_8680 (AllWinning.cons node_7705 (AllWinning.cons node_8685 (AllWinning.cons node_7714 (AllWinning.nil))))))

theorem node_9632 : Outcome ⟨11, 4, 7, 4⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 6⟩) (by decide) node_6743

theorem node_9633 : Outcome ⟨11, 4, 7, 6⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9634 : Outcome ⟨11, 4, 7, 8⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9635 : Outcome ⟨11, 4, 7, 22⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9636 : Outcome ⟨11, 4, 7, 24⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9637 : Outcome ⟨11, 5, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 5, 6, 2⟩, ⟨9, 5, 6, 4⟩, ⟨11, 4, 6, 2⟩, ⟨11, 3, 6, 4⟩, ⟨11, 5, 5, 2⟩, ⟨11, 5, 4, 4⟩]
  exact AllWinning.cons node_8644 (AllWinning.cons node_7603 (AllWinning.cons node_8685 (AllWinning.cons node_7710 (AllWinning.cons node_8689 (AllWinning.cons node_7717 (AllWinning.nil))))))

theorem node_9638 : Outcome ⟨11, 5, 6, 4⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9639 : Outcome ⟨11, 5, 6, 20⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9640 : Outcome ⟨11, 6, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 5, 2⟩, ⟨9, 6, 5, 4⟩, ⟨11, 5, 5, 2⟩, ⟨11, 4, 5, 4⟩, ⟨11, 6, 4, 2⟩, ⟨11, 6, 3, 4⟩]
  exact AllWinning.cons node_8648 (AllWinning.cons node_7607 (AllWinning.cons node_8689 (AllWinning.cons node_7714 (AllWinning.cons node_8691 (AllWinning.cons node_7719 (AllWinning.nil))))))

theorem node_9641 : Outcome ⟨11, 6, 5, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9642 : Outcome ⟨11, 6, 5, 20⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9643 : Outcome ⟨11, 7, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 7, 4, 2⟩, ⟨9, 7, 4, 4⟩, ⟨11, 6, 4, 2⟩, ⟨11, 5, 4, 4⟩, ⟨11, 7, 3, 2⟩, ⟨11, 7, 2, 4⟩]
  exact AllWinning.cons node_8652 (AllWinning.cons node_7612 (AllWinning.cons node_8691 (AllWinning.cons node_7717 (AllWinning.cons node_8695 (AllWinning.cons node_7723 (AllWinning.nil))))))

theorem node_9644 : Outcome ⟨11, 7, 4, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 6⟩) (by decide) node_6796

theorem node_9645 : Outcome ⟨11, 7, 4, 6⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9646 : Outcome ⟨11, 7, 4, 8⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9647 : Outcome ⟨11, 7, 4, 22⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9648 : Outcome ⟨11, 7, 4, 24⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9649 : Outcome ⟨11, 8, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 3, 2⟩, ⟨9, 8, 3, 4⟩, ⟨11, 7, 3, 2⟩, ⟨11, 6, 3, 4⟩, ⟨11, 8, 2, 2⟩, ⟨11, 8, 1, 4⟩]
  exact AllWinning.cons node_8655 (AllWinning.cons node_7615 (AllWinning.cons node_8695 (AllWinning.cons node_7719 (AllWinning.cons node_8700 (AllWinning.cons node_7729 (AllWinning.nil))))))

theorem node_9650 : Outcome ⟨11, 8, 3, 8⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 6⟩) (by decide) node_6776

theorem node_9651 : Outcome ⟨11, 8, 3, 10⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 6⟩) (by decide) node_6776

theorem node_9652 : Outcome ⟨11, 8, 3, 14⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 6⟩) (by decide) node_6776

theorem node_9653 : Outcome ⟨11, 8, 3, 22⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 6⟩) (by decide) node_6776

theorem node_9654 : Outcome ⟨11, 9, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 9, 2, 2⟩, ⟨9, 9, 2, 4⟩, ⟨11, 8, 2, 2⟩, ⟨11, 7, 2, 4⟩, ⟨11, 9, 1, 2⟩, ⟨11, 9, 0, 4⟩]
  exact AllWinning.cons node_8660 (AllWinning.cons node_7620 (AllWinning.cons node_8700 (AllWinning.cons node_7723 (AllWinning.cons node_8704 (AllWinning.cons node_7732 (AllWinning.nil))))))

theorem node_9655 : Outcome ⟨11, 9, 2, 8⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 6⟩) (by decide) node_6787

theorem node_9656 : Outcome ⟨11, 9, 2, 16⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 6⟩) (by decide) node_6787

theorem node_9657 : Outcome ⟨11, 10, 1, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 6⟩) (by decide) node_6796

theorem node_9658 : Outcome ⟨11, 10, 1, 6⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 6⟩) (by decide) node_6796

theorem node_9659 : Outcome ⟨11, 10, 1, 10⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 6⟩) (by decide) node_6796

theorem node_9660 : Outcome ⟨11, 10, 1, 14⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 6⟩) (by decide) node_6796

theorem node_9661 : Outcome ⟨11, 11, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.nil))))

theorem node_9662 : Outcome ⟨11, 11, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.nil))))))))

theorem node_9663 : Outcome ⟨11, 11, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.nil))))))))))))

theorem node_9664 : Outcome ⟨11, 11, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨4, 11, 0, 14⟩, ⟨3, 11, 0, 16⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩, ⟨11, 4, 0, 14⟩, ⟨11, 3, 0, 16⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_3627 (AllWinning.cons node_3044 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.cons node_3879 (AllWinning.cons node_3294 (AllWinning.nil))))))))))))))))

theorem node_9665 : Outcome ⟨11, 11, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨4, 11, 0, 14⟩, ⟨3, 11, 0, 16⟩, ⟨2, 11, 0, 18⟩, ⟨1, 11, 0, 20⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩, ⟨11, 4, 0, 14⟩, ⟨11, 3, 0, 16⟩, ⟨11, 2, 0, 18⟩, ⟨11, 1, 0, 20⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_3627 (AllWinning.cons node_3044 (AllWinning.cons node_2528 (AllWinning.cons node_1981 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.cons node_3879 (AllWinning.cons node_3294 (AllWinning.cons node_2803 (AllWinning.cons node_2356 (AllWinning.nil))))))))))))))))))))

theorem node_9666 : Outcome ⟨11, 11, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨4, 11, 0, 14⟩, ⟨3, 11, 0, 16⟩, ⟨2, 11, 0, 18⟩, ⟨1, 11, 0, 20⟩, ⟨0, 11, 0, 22⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩, ⟨11, 4, 0, 14⟩, ⟨11, 3, 0, 16⟩, ⟨11, 2, 0, 18⟩, ⟨11, 1, 0, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_3627 (AllWinning.cons node_3044 (AllWinning.cons node_2528 (AllWinning.cons node_1981 (AllWinning.cons node_1595 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.cons node_3879 (AllWinning.cons node_3294 (AllWinning.cons node_2803 (AllWinning.cons node_2356 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9667 : Outcome ⟨11, 11, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨4, 11, 0, 14⟩, ⟨3, 11, 0, 16⟩, ⟨2, 11, 0, 18⟩, ⟨1, 11, 0, 20⟩, ⟨0, 11, 0, 22⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩, ⟨11, 4, 0, 14⟩, ⟨11, 3, 0, 16⟩, ⟨11, 2, 0, 18⟩, ⟨11, 1, 0, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_3627 (AllWinning.cons node_3044 (AllWinning.cons node_2528 (AllWinning.cons node_1981 (AllWinning.cons node_1595 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.cons node_3879 (AllWinning.cons node_3294 (AllWinning.cons node_2803 (AllWinning.cons node_2356 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9668 : Outcome ⟨11, 11, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨4, 11, 0, 14⟩, ⟨3, 11, 0, 16⟩, ⟨2, 11, 0, 18⟩, ⟨1, 11, 0, 20⟩, ⟨0, 11, 0, 22⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩, ⟨11, 4, 0, 14⟩, ⟨11, 3, 0, 16⟩, ⟨11, 2, 0, 18⟩, ⟨11, 1, 0, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_3627 (AllWinning.cons node_3044 (AllWinning.cons node_2528 (AllWinning.cons node_1981 (AllWinning.cons node_1595 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.cons node_3879 (AllWinning.cons node_3294 (AllWinning.cons node_2803 (AllWinning.cons node_2356 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9669 : Outcome ⟨11, 11, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨4, 11, 0, 14⟩, ⟨3, 11, 0, 16⟩, ⟨2, 11, 0, 18⟩, ⟨1, 11, 0, 20⟩, ⟨0, 11, 0, 22⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩, ⟨11, 4, 0, 14⟩, ⟨11, 3, 0, 16⟩, ⟨11, 2, 0, 18⟩, ⟨11, 1, 0, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_3627 (AllWinning.cons node_3044 (AllWinning.cons node_2528 (AllWinning.cons node_1981 (AllWinning.cons node_1595 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.cons node_3879 (AllWinning.cons node_3294 (AllWinning.cons node_2803 (AllWinning.cons node_2356 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9670 : Outcome ⟨11, 11, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 11, 0, 2⟩, ⟨9, 11, 0, 4⟩, ⟨8, 11, 0, 6⟩, ⟨7, 11, 0, 8⟩, ⟨6, 11, 0, 10⟩, ⟨5, 11, 0, 12⟩, ⟨4, 11, 0, 14⟩, ⟨3, 11, 0, 16⟩, ⟨2, 11, 0, 18⟩, ⟨1, 11, 0, 20⟩, ⟨0, 11, 0, 22⟩, ⟨11, 10, 0, 2⟩, ⟨11, 9, 0, 4⟩, ⟨11, 8, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨11, 6, 0, 10⟩, ⟨11, 5, 0, 12⟩, ⟨11, 4, 0, 14⟩, ⟨11, 3, 0, 16⟩, ⟨11, 2, 0, 18⟩, ⟨11, 1, 0, 20⟩, ⟨11, 0, 0, 22⟩]
  exact AllWinning.cons node_8667 (AllWinning.cons node_7627 (AllWinning.cons node_6663 (AllWinning.cons node_5773 (AllWinning.cons node_5028 (AllWinning.cons node_4280 (AllWinning.cons node_3627 (AllWinning.cons node_3044 (AllWinning.cons node_2528 (AllWinning.cons node_1981 (AllWinning.cons node_1595 (AllWinning.cons node_8707 (AllWinning.cons node_7732 (AllWinning.cons node_6806 (AllWinning.cons node_5927 (AllWinning.cons node_5209 (AllWinning.cons node_4510 (AllWinning.cons node_3879 (AllWinning.cons node_3294 (AllWinning.cons node_2803 (AllWinning.cons node_2356 (AllWinning.cons node_1863 (AllWinning.nil))))))))))))))))))))))

theorem node_9671 : Outcome ⟨12, 0, 10, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9672 : Outcome ⟨12, 0, 10, 6⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9673 : Outcome ⟨12, 0, 10, 10⟩ true :=
  Outcome.win (q := ⟨10, 0, 10, 4⟩) (by decide) node_7630

theorem node_9674 : Outcome ⟨12, 1, 9, 2⟩ true :=
  Outcome.win (q := ⟨10, 1, 9, 4⟩) (by decide) node_7640

theorem node_9675 : Outcome ⟨12, 1, 9, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 9, 4⟩) (by decide) node_7640

theorem node_9676 : Outcome ⟨12, 2, 8, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 2⟩) (by decide) node_8713

theorem node_9677 : Outcome ⟨12, 2, 8, 12⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 2⟩) (by decide) node_8713

theorem node_9678 : Outcome ⟨12, 2, 8, 14⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 2⟩) (by decide) node_8713

theorem node_9679 : Outcome ⟨12, 3, 7, 2⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 4⟩) (by decide) node_7647

theorem node_9680 : Outcome ⟨12, 3, 7, 4⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 4⟩) (by decide) node_7647

theorem node_9681 : Outcome ⟨12, 3, 7, 6⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 4⟩) (by decide) node_7647

theorem node_9682 : Outcome ⟨12, 3, 7, 8⟩ true :=
  Outcome.win (q := ⟨10, 3, 7, 4⟩) (by decide) node_7647

theorem node_9683 : Outcome ⟨12, 3, 7, 24⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 20⟩) (by decide) node_2003

theorem node_9684 : Outcome ⟨12, 4, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9685 : Outcome ⟨12, 4, 6, 6⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9686 : Outcome ⟨12, 4, 6, 14⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9687 : Outcome ⟨12, 4, 6, 24⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 4⟩) (by decide) node_7652

theorem node_9688 : Outcome ⟨12, 5, 5, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 5, 2⟩) (by decide) node_8734

theorem node_9689 : Outcome ⟨12, 5, 5, 10⟩ true :=
  Outcome.win (q := ⟨12, 4, 5, 2⟩) (by decide) node_8734

theorem node_9690 : Outcome ⟨12, 6, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9691 : Outcome ⟨12, 6, 4, 6⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9692 : Outcome ⟨12, 6, 4, 14⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9693 : Outcome ⟨12, 6, 4, 24⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 4⟩) (by decide) node_7666

theorem node_9694 : Outcome ⟨12, 7, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9695 : Outcome ⟨12, 7, 3, 4⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9696 : Outcome ⟨12, 7, 3, 6⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9697 : Outcome ⟨12, 7, 3, 8⟩ true :=
  Outcome.win (q := ⟨10, 7, 3, 4⟩) (by decide) node_7678

theorem node_9698 : Outcome ⟨12, 7, 3, 24⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 20⟩) (by decide) node_2033

theorem node_9699 : Outcome ⟨12, 8, 2, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 2⟩) (by decide) node_8745

theorem node_9700 : Outcome ⟨12, 8, 2, 12⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 2⟩) (by decide) node_8745

theorem node_9701 : Outcome ⟨12, 8, 2, 14⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 2⟩) (by decide) node_8745

theorem node_9702 : Outcome ⟨12, 9, 1, 2⟩ true :=
  Outcome.win (q := ⟨10, 9, 1, 4⟩) (by decide) node_7685

theorem node_9703 : Outcome ⟨12, 9, 1, 4⟩ true :=
  Outcome.win (q := ⟨10, 9, 1, 4⟩) (by decide) node_7685

theorem node_9704 : Outcome ⟨12, 10, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9705 : Outcome ⟨12, 10, 0, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9706 : Outcome ⟨12, 10, 0, 10⟩ true :=
  Outcome.win (q := ⟨10, 10, 0, 4⟩) (by decide) node_7689

theorem node_9707 : Outcome ⟨13, 0, 9, 2⟩ true :=
  Outcome.win (q := ⟨12, 0, 9, 2⟩) (by decide) node_8710

theorem node_9708 : Outcome ⟨13, 0, 9, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 8⟩) (by decide) node_5823

theorem node_9709 : Outcome ⟨13, 0, 9, 14⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 8⟩) (by decide) node_5823

theorem node_9710 : Outcome ⟨13, 1, 8, 2⟩ true :=
  Outcome.win (q := ⟨13, 1, 6, 4⟩) (by decide) node_7763

theorem node_9711 : Outcome ⟨13, 1, 8, 18⟩ true :=
  Outcome.win (q := ⟨13, 1, 6, 4⟩) (by decide) node_7763

theorem node_9712 : Outcome ⟨13, 2, 7, 2⟩ true :=
  Outcome.win (q := ⟨12, 2, 7, 2⟩) (by decide) node_8724

theorem node_9713 : Outcome ⟨13, 2, 7, 8⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 10⟩) (by decide) node_5251

theorem node_9714 : Outcome ⟨13, 2, 7, 10⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 20⟩) (by decide) node_2074

theorem node_9715 : Outcome ⟨13, 2, 7, 14⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 20⟩) (by decide) node_2074

theorem node_9716 : Outcome ⟨13, 3, 6, 2⟩ true :=
  Outcome.win (q := ⟨13, 1, 6, 4⟩) (by decide) node_7763

theorem node_9717 : Outcome ⟨13, 3, 6, 8⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 6⟩) (by decide) node_6853

theorem node_9718 : Outcome ⟨13, 3, 6, 22⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 24⟩) (by decide) node_1230

theorem node_9719 : Outcome ⟨13, 4, 5, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 5, 2⟩) (by decide) node_8734

theorem node_9720 : Outcome ⟨13, 4, 5, 8⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9721 : Outcome ⟨13, 4, 5, 14⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9722 : Outcome ⟨13, 5, 4, 2⟩ true :=
  Outcome.win (q := ⟨12, 5, 4, 2⟩) (by decide) node_8738

theorem node_9723 : Outcome ⟨13, 5, 4, 8⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9724 : Outcome ⟨13, 5, 4, 14⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9725 : Outcome ⟨13, 6, 3, 2⟩ true :=
  Outcome.win (q := ⟨13, 6, 1, 4⟩) (by decide) node_7780

theorem node_9726 : Outcome ⟨13, 6, 3, 8⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 6⟩) (by decide) node_6853

theorem node_9727 : Outcome ⟨13, 6, 3, 22⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 24⟩) (by decide) node_1258

theorem node_9728 : Outcome ⟨13, 7, 2, 2⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 2⟩) (by decide) node_8745

theorem node_9729 : Outcome ⟨13, 7, 2, 8⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 10⟩) (by decide) node_5251

theorem node_9730 : Outcome ⟨13, 7, 2, 10⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 20⟩) (by decide) node_2105

theorem node_9731 : Outcome ⟨13, 7, 2, 14⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 20⟩) (by decide) node_2105

theorem node_9732 : Outcome ⟨13, 8, 1, 2⟩ true :=
  Outcome.win (q := ⟨13, 6, 1, 4⟩) (by decide) node_7780

theorem node_9733 : Outcome ⟨13, 8, 1, 18⟩ true :=
  Outcome.win (q := ⟨13, 6, 1, 4⟩) (by decide) node_7780

theorem node_9734 : Outcome ⟨13, 9, 0, 2⟩ true :=
  Outcome.win (q := ⟨12, 9, 0, 2⟩) (by decide) node_8762

theorem node_9735 : Outcome ⟨13, 9, 0, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 8⟩) (by decide) node_5873

theorem node_9736 : Outcome ⟨13, 9, 0, 14⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 8⟩) (by decide) node_5873

theorem node_9737 : Outcome ⟨14, 0, 8, 2⟩ true :=
  Outcome.win (q := ⟨14, 0, 6, 4⟩) (by decide) node_7789

theorem node_9738 : Outcome ⟨14, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 6, 4⟩) (by decide) node_7789

theorem node_9739 : Outcome ⟨14, 0, 8, 12⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 12⟩) (by decide) node_4395

theorem node_9740 : Outcome ⟨14, 1, 7, 6⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 6⟩) (by decide) node_6743

theorem node_9741 : Outcome ⟨14, 2, 6, 2⟩ true :=
  Outcome.win (q := ⟨14, 0, 6, 4⟩) (by decide) node_7789

theorem node_9742 : Outcome ⟨14, 2, 6, 4⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9743 : Outcome ⟨14, 2, 6, 6⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9744 : Outcome ⟨14, 2, 6, 12⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9745 : Outcome ⟨14, 2, 6, 22⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 6⟩) (by decide) node_6753

theorem node_9746 : Outcome ⟨14, 3, 5, 2⟩ true :=
  Outcome.win (q := ⟨14, 1, 5, 4⟩) (by decide) node_7794

theorem node_9747 : Outcome ⟨14, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9748 : Outcome ⟨14, 3, 5, 12⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9749 : Outcome ⟨14, 3, 5, 24⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 6⟩) (by decide) node_6762

theorem node_9750 : Outcome ⟨14, 4, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 4⟩) (by decide) node_7798

theorem node_9751 : Outcome ⟨14, 4, 4, 6⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 4⟩) (by decide) node_7798

theorem node_9752 : Outcome ⟨14, 4, 4, 8⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 4⟩) (by decide) node_7798

theorem node_9753 : Outcome ⟨14, 4, 4, 30⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 28⟩) (by decide) node_712

theorem node_9754 : Outcome ⟨14, 5, 3, 2⟩ true :=
  Outcome.win (q := ⟨14, 5, 1, 4⟩) (by decide) node_7817

theorem node_9755 : Outcome ⟨14, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 6⟩) (by decide) node_6776

theorem node_9756 : Outcome ⟨14, 5, 3, 12⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 6⟩) (by decide) node_6776

theorem node_9757 : Outcome ⟨14, 5, 3, 24⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 6⟩) (by decide) node_6776

theorem node_9758 : Outcome ⟨14, 6, 2, 2⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 4⟩) (by decide) node_7809

theorem node_9759 : Outcome ⟨14, 6, 2, 4⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 6⟩) (by decide) node_6787

theorem node_9760 : Outcome ⟨14, 6, 2, 6⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 6⟩) (by decide) node_6787

theorem node_9761 : Outcome ⟨14, 6, 2, 12⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 6⟩) (by decide) node_6787

theorem node_9762 : Outcome ⟨14, 6, 2, 22⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 6⟩) (by decide) node_6787

theorem node_9763 : Outcome ⟨14, 7, 1, 6⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 6⟩) (by decide) node_6796

theorem node_9764 : Outcome ⟨14, 8, 0, 2⟩ true :=
  Outcome.win (q := ⟨14, 6, 0, 4⟩) (by decide) node_7821

theorem node_9765 : Outcome ⟨14, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨14, 6, 0, 4⟩) (by decide) node_7821

theorem node_9766 : Outcome ⟨14, 8, 0, 12⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 12⟩) (by decide) node_4436

theorem node_9767 : Outcome ⟨15, 0, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 7, 2⟩, ⟨13, 0, 7, 4⟩, ⟨15, 0, 6, 2⟩, ⟨15, 0, 5, 4⟩]
  exact AllWinning.cons node_8796 (AllWinning.cons node_7759 (AllWinning.cons node_8822 (AllWinning.cons node_7826 (AllWinning.nil))))

theorem node_9768 : Outcome ⟨15, 0, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 0, 7, 2⟩, ⟨13, 0, 7, 4⟩, ⟨12, 0, 7, 6⟩, ⟨11, 0, 7, 8⟩, ⟨15, 0, 6, 2⟩, ⟨15, 0, 5, 4⟩, ⟨15, 0, 4, 6⟩, ⟨15, 0, 3, 8⟩]
  exact AllWinning.cons node_8796 (AllWinning.cons node_7759 (AllWinning.cons node_6809 (AllWinning.cons node_5913 (AllWinning.cons node_8822 (AllWinning.cons node_7826 (AllWinning.cons node_6891 (AllWinning.cons node_5998 (AllWinning.nil))))))))

theorem node_9769 : Outcome ⟨15, 0, 7, 6⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 10⟩) (by decide) node_5285

theorem node_9770 : Outcome ⟨15, 0, 7, 16⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 16⟩) (by decide) node_3168

theorem node_9771 : Outcome ⟨15, 0, 7, 24⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 16⟩) (by decide) node_3168

theorem node_9772 : Outcome ⟨15, 1, 6, 2⟩ true :=
  Outcome.win (q := ⟨13, 1, 6, 4⟩) (by decide) node_7763

theorem node_9773 : Outcome ⟨15, 1, 6, 6⟩ true :=
  Outcome.win (q := ⟨13, 1, 6, 4⟩) (by decide) node_7763

theorem node_9774 : Outcome ⟨15, 1, 6, 10⟩ true :=
  Outcome.win (q := ⟨13, 1, 6, 4⟩) (by decide) node_7763

theorem node_9775 : Outcome ⟨15, 1, 6, 20⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 24⟩) (by decide) node_1330

theorem node_9776 : Outcome ⟨15, 2, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 2, 5, 2⟩, ⟨13, 2, 5, 4⟩, ⟨15, 1, 5, 2⟩, ⟨15, 0, 5, 4⟩, ⟨15, 2, 4, 2⟩, ⟨15, 2, 3, 4⟩]
  exact AllWinning.cons node_8803 (AllWinning.cons node_7767 (AllWinning.cons node_8826 (AllWinning.cons node_7826 (AllWinning.cons node_8831 (AllWinning.cons node_7837 (AllWinning.nil))))))

theorem node_9777 : Outcome ⟨15, 2, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 2, 5, 2⟩, ⟨13, 2, 5, 4⟩, ⟨12, 2, 5, 6⟩, ⟨11, 2, 5, 8⟩, ⟨15, 1, 5, 2⟩, ⟨15, 0, 5, 4⟩, ⟨15, 2, 4, 2⟩, ⟨15, 2, 3, 4⟩, ⟨15, 2, 2, 6⟩, ⟨15, 2, 1, 8⟩]
  exact AllWinning.cons node_8803 (AllWinning.cons node_7767 (AllWinning.cons node_6817 (AllWinning.cons node_5918 (AllWinning.cons node_8826 (AllWinning.cons node_7826 (AllWinning.cons node_8831 (AllWinning.cons node_7837 (AllWinning.cons node_6898 (AllWinning.cons node_6006 (AllWinning.nil))))))))))

theorem node_9778 : Outcome ⟨15, 2, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 10⟩) (by decide) node_5156

theorem node_9779 : Outcome ⟨15, 2, 5, 12⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 10⟩) (by decide) node_5156

theorem node_9780 : Outcome ⟨15, 3, 4, 4⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9781 : Outcome ⟨15, 3, 4, 6⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9782 : Outcome ⟨15, 3, 4, 28⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9783 : Outcome ⟨15, 4, 3, 4⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9784 : Outcome ⟨15, 4, 3, 6⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9785 : Outcome ⟨15, 4, 3, 28⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9786 : Outcome ⟨15, 5, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 5, 2, 2⟩, ⟨13, 5, 2, 4⟩, ⟨15, 4, 2, 2⟩, ⟨15, 3, 2, 4⟩, ⟨15, 5, 1, 2⟩, ⟨15, 5, 0, 4⟩]
  exact AllWinning.cons node_8813 (AllWinning.cons node_7776 (AllWinning.cons node_8837 (AllWinning.cons node_7841 (AllWinning.cons node_8840 (AllWinning.cons node_7852 (AllWinning.nil))))))

end RQ9F1
