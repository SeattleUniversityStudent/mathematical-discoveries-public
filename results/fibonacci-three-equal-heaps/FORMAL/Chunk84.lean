import Chunk83
set_option autoImplicit false
namespace RQ9F1

theorem node_18398 : Outcome ⟨11, 13, 7, 6⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 4⟩) (by decide) node_16451

theorem node_18399 : Outcome ⟨11, 13, 7, 14⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 24⟩) (by decide) node_6750

theorem node_18400 : Outcome ⟨11, 14, 6, 2⟩ true :=
  Outcome.win (q := ⟨11, 12, 6, 4⟩) (by decide) node_16582

theorem node_18401 : Outcome ⟨11, 14, 6, 4⟩ true :=
  Outcome.win (q := ⟨11, 12, 6, 4⟩) (by decide) node_16582

theorem node_18402 : Outcome ⟨11, 15, 5, 2⟩ true :=
  Outcome.win (q := ⟨11, 15, 4, 2⟩) (by decide) node_17501

theorem node_18403 : Outcome ⟨11, 15, 5, 4⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 6⟩) (by decide) node_15370

theorem node_18404 : Outcome ⟨11, 15, 5, 8⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 6⟩) (by decide) node_15370

theorem node_18405 : Outcome ⟨11, 16, 4, 2⟩ true :=
  Outcome.win (q := ⟨9, 16, 4, 4⟩) (by decide) node_16466

theorem node_18406 : Outcome ⟨11, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨9, 16, 4, 4⟩) (by decide) node_16466

theorem node_18407 : Outcome ⟨11, 16, 4, 6⟩ true :=
  Outcome.win (q := ⟨9, 16, 4, 4⟩) (by decide) node_16466

theorem node_18408 : Outcome ⟨11, 17, 3, 4⟩ true :=
  Outcome.win (q := ⟨9, 17, 3, 4⟩) (by decide) node_16474

theorem node_18409 : Outcome ⟨11, 17, 3, 6⟩ true :=
  Outcome.win (q := ⟨9, 17, 3, 4⟩) (by decide) node_16474

theorem node_18410 : Outcome ⟨11, 18, 2, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 2, 2⟩) (by decide) node_17507

theorem node_18411 : Outcome ⟨11, 18, 2, 4⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 8⟩) (by decide) node_14386

theorem node_18412 : Outcome ⟨11, 18, 2, 10⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 8⟩) (by decide) node_14386

theorem node_18413 : Outcome ⟨11, 19, 1, 2⟩ true :=
  Outcome.win (q := ⟨9, 19, 1, 4⟩) (by decide) node_16480

theorem node_18414 : Outcome ⟨11, 19, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 19, 1, 4⟩) (by decide) node_16480

theorem node_18415 : Outcome ⟨11, 20, 0, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 0, 2⟩) (by decide) node_17513

theorem node_18416 : Outcome ⟨11, 20, 0, 8⟩ true :=
  Outcome.win (q := ⟨7, 20, 0, 8⟩) (by decide) node_14396

theorem node_18417 : Outcome ⟨12, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 0, 17, 4⟩) (by decide) node_16602

theorem node_18418 : Outcome ⟨12, 0, 19, 4⟩ true :=
  Outcome.win (q := ⟨12, 0, 17, 4⟩) (by decide) node_16602

theorem node_18419 : Outcome ⟨12, 0, 19, 14⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 14⟩) (by decide) node_11715

theorem node_18420 : Outcome ⟨12, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 4⟩) (by decide) node_16606

theorem node_18421 : Outcome ⟨12, 1, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 4⟩) (by decide) node_16606

theorem node_18422 : Outcome ⟨12, 1, 18, 8⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 4⟩) (by decide) node_16606

theorem node_18423 : Outcome ⟨12, 3, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 4⟩) (by decide) node_16606

theorem node_18424 : Outcome ⟨12, 3, 16, 6⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 8⟩) (by decide) node_14410

theorem node_18425 : Outcome ⟨12, 3, 16, 8⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 14⟩) (by decide) node_11731

theorem node_18426 : Outcome ⟨12, 4, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18427 : Outcome ⟨12, 4, 15, 6⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18428 : Outcome ⟨12, 5, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 5, 14, 2⟩, ⟨10, 5, 14, 4⟩, ⟨12, 4, 14, 2⟩, ⟨12, 3, 14, 4⟩, ⟨12, 5, 13, 2⟩, ⟨12, 5, 12, 4⟩]
  exact AllWinning.cons node_17480 (AllWinning.cons node_16497 (AllWinning.cons node_17530 (AllWinning.cons node_16612 (AllWinning.cons node_17534 (AllWinning.cons node_16621 (AllWinning.nil))))))

theorem node_18429 : Outcome ⟨12, 5, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 8⟩) (by decide) node_14640

theorem node_18430 : Outcome ⟨12, 5, 14, 6⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 8⟩) (by decide) node_14640

theorem node_18431 : Outcome ⟨12, 5, 14, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 8⟩) (by decide) node_14640

theorem node_18432 : Outcome ⟨12, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18433 : Outcome ⟨12, 6, 13, 6⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18434 : Outcome ⟨12, 7, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 7, 12, 2⟩, ⟨10, 7, 12, 4⟩, ⟨12, 6, 12, 2⟩, ⟨12, 5, 12, 4⟩, ⟨12, 7, 11, 2⟩, ⟨12, 7, 10, 4⟩]
  exact AllWinning.cons node_17484 (AllWinning.cons node_16503 (AllWinning.cons node_17537 (AllWinning.cons node_16621 (AllWinning.cons node_17540 (AllWinning.cons node_16628 (AllWinning.nil))))))

theorem node_18435 : Outcome ⟨12, 7, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 7, 12, 2⟩, ⟨10, 7, 12, 4⟩, ⟨9, 7, 12, 6⟩, ⟨8, 7, 12, 8⟩, ⟨12, 6, 12, 2⟩, ⟨12, 5, 12, 4⟩, ⟨12, 4, 12, 6⟩, ⟨12, 3, 12, 8⟩, ⟨12, 7, 11, 2⟩, ⟨12, 7, 10, 4⟩, ⟨12, 7, 9, 6⟩, ⟨12, 7, 8, 8⟩]
  exact AllWinning.cons node_17484 (AllWinning.cons node_16503 (AllWinning.cons node_15411 (AllWinning.cons node_14422 (AllWinning.cons node_17537 (AllWinning.cons node_16621 (AllWinning.cons node_15575 (AllWinning.cons node_14635 (AllWinning.cons node_17540 (AllWinning.cons node_16628 (AllWinning.cons node_15581 (AllWinning.cons node_14647 (AllWinning.nil))))))))))))

theorem node_18436 : Outcome ⟨12, 7, 12, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 10⟩) (by decide) node_13385

theorem node_18437 : Outcome ⟨12, 7, 12, 8⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 14⟩) (by decide) node_11715

theorem node_18438 : Outcome ⟨12, 8, 11, 2⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 4⟩) (by decide) node_16506

theorem node_18439 : Outcome ⟨12, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18440 : Outcome ⟨12, 8, 11, 6⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18441 : Outcome ⟨12, 8, 11, 8⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18442 : Outcome ⟨12, 8, 11, 10⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 20⟩) (by decide) node_8759

theorem node_18443 : Outcome ⟨12, 9, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 9, 10, 2⟩, ⟨10, 9, 10, 4⟩, ⟨12, 8, 10, 2⟩, ⟨12, 7, 10, 4⟩, ⟨12, 9, 9, 2⟩, ⟨12, 9, 8, 4⟩]
  exact AllWinning.cons node_17490 (AllWinning.cons node_16511 (AllWinning.cons node_17543 (AllWinning.cons node_16628 (AllWinning.cons node_17545 (AllWinning.cons node_16631 (AllWinning.nil))))))

theorem node_18444 : Outcome ⟨12, 9, 10, 4⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 8⟩) (by decide) node_14640

theorem node_18445 : Outcome ⟨12, 9, 10, 6⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 8⟩) (by decide) node_14640

theorem node_18446 : Outcome ⟨12, 9, 10, 8⟩ true :=
  Outcome.win (q := ⟨12, 9, 3, 14⟩) (by decide) node_11761

theorem node_18447 : Outcome ⟨12, 10, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 10, 9, 2⟩, ⟨10, 10, 9, 4⟩, ⟨12, 9, 9, 2⟩, ⟨12, 8, 9, 4⟩, ⟨12, 10, 8, 2⟩, ⟨12, 10, 7, 4⟩]
  exact AllWinning.cons node_17491 (AllWinning.cons node_16514 (AllWinning.cons node_17545 (AllWinning.cons node_16630 (AllWinning.cons node_17548 (AllWinning.cons node_16632 (AllWinning.nil))))))

theorem node_18448 : Outcome ⟨12, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 8⟩) (by decide) node_14657

theorem node_18449 : Outcome ⟨12, 10, 9, 6⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 8⟩) (by decide) node_14657

theorem node_18450 : Outcome ⟨12, 10, 9, 8⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 14⟩) (by decide) node_11731

theorem node_18451 : Outcome ⟨12, 11, 8, 2⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 4⟩) (by decide) node_16518

theorem node_18452 : Outcome ⟨12, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18453 : Outcome ⟨12, 11, 8, 6⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18454 : Outcome ⟨12, 11, 8, 8⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18455 : Outcome ⟨12, 12, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 7, 2⟩, ⟨10, 12, 7, 4⟩, ⟨12, 11, 7, 2⟩, ⟨12, 10, 7, 4⟩, ⟨12, 12, 6, 2⟩, ⟨12, 12, 5, 4⟩]
  exact AllWinning.cons node_17494 (AllWinning.cons node_16523 (AllWinning.cons node_17550 (AllWinning.cons node_16632 (AllWinning.cons node_17553 (AllWinning.cons node_16639 (AllWinning.nil))))))

theorem node_18456 : Outcome ⟨12, 12, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 7, 2⟩, ⟨10, 12, 7, 4⟩, ⟨9, 12, 7, 6⟩, ⟨8, 12, 7, 8⟩, ⟨12, 11, 7, 2⟩, ⟨12, 10, 7, 4⟩, ⟨12, 9, 7, 6⟩, ⟨12, 8, 7, 8⟩, ⟨12, 12, 6, 2⟩, ⟨12, 12, 5, 4⟩, ⟨12, 12, 4, 6⟩, ⟨12, 12, 3, 8⟩]
  exact AllWinning.cons node_17494 (AllWinning.cons node_16523 (AllWinning.cons node_15424 (AllWinning.cons node_14434 (AllWinning.cons node_17550 (AllWinning.cons node_16632 (AllWinning.cons node_15588 (AllWinning.cons node_14650 (AllWinning.cons node_17553 (AllWinning.cons node_16639 (AllWinning.cons node_15595 (AllWinning.cons node_14664 (AllWinning.nil))))))))))))

theorem node_18457 : Outcome ⟨12, 12, 7, 6⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 10⟩) (by decide) node_13405

theorem node_18458 : Outcome ⟨12, 12, 7, 8⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 14⟩) (by decide) node_11776

theorem node_18459 : Outcome ⟨12, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 11, 6, 4⟩) (by decide) node_16635

theorem node_18460 : Outcome ⟨12, 13, 6, 6⟩ true :=
  Outcome.win (q := ⟨12, 11, 6, 4⟩) (by decide) node_16635

theorem node_18461 : Outcome ⟨12, 14, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 14, 5, 2⟩, ⟨10, 14, 5, 4⟩, ⟨12, 13, 5, 2⟩, ⟨12, 12, 5, 4⟩, ⟨12, 14, 4, 2⟩, ⟨12, 14, 3, 4⟩]
  exact AllWinning.cons node_17499 (AllWinning.cons node_16528 (AllWinning.cons node_17556 (AllWinning.cons node_16639 (AllWinning.cons node_17559 (AllWinning.cons node_16648 (AllWinning.nil))))))

theorem node_18462 : Outcome ⟨12, 14, 5, 4⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 8⟩) (by decide) node_14657

theorem node_18463 : Outcome ⟨12, 14, 5, 6⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 8⟩) (by decide) node_14657

theorem node_18464 : Outcome ⟨12, 14, 5, 8⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 8⟩) (by decide) node_14657

theorem node_18465 : Outcome ⟨12, 15, 4, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 4⟩) (by decide) node_16642

theorem node_18466 : Outcome ⟨12, 15, 4, 6⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 4⟩) (by decide) node_16642

theorem node_18467 : Outcome ⟨12, 16, 3, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 4⟩) (by decide) node_16654

theorem node_18468 : Outcome ⟨12, 16, 3, 6⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 8⟩) (by decide) node_14446

theorem node_18469 : Outcome ⟨12, 16, 3, 8⟩ true :=
  Outcome.win (q := ⟨12, 9, 3, 14⟩) (by decide) node_11761

theorem node_18470 : Outcome ⟨12, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨12, 17, 0, 4⟩) (by decide) node_16658

theorem node_18471 : Outcome ⟨12, 18, 1, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 4⟩) (by decide) node_16654

theorem node_18472 : Outcome ⟨12, 18, 1, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 4⟩) (by decide) node_16654

theorem node_18473 : Outcome ⟨12, 18, 1, 8⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 4⟩) (by decide) node_16654

theorem node_18474 : Outcome ⟨12, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨12, 17, 0, 4⟩) (by decide) node_16658

theorem node_18475 : Outcome ⟨12, 19, 0, 4⟩ true :=
  Outcome.win (q := ⟨12, 17, 0, 4⟩) (by decide) node_16658

theorem node_18476 : Outcome ⟨12, 19, 0, 14⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 14⟩) (by decide) node_11776

theorem node_18477 : Outcome ⟨13, 0, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 18, 2⟩, ⟨11, 0, 18, 4⟩, ⟨13, 0, 17, 2⟩, ⟨13, 0, 16, 4⟩]
  exact AllWinning.cons node_17517 (AllWinning.cons node_16544 (AllWinning.cons node_17576 (AllWinning.cons node_16661 (AllWinning.nil))))

theorem node_18478 : Outcome ⟨13, 0, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 18, 2⟩, ⟨11, 0, 18, 4⟩, ⟨10, 0, 18, 6⟩, ⟨9, 0, 18, 8⟩, ⟨13, 0, 17, 2⟩, ⟨13, 0, 16, 4⟩, ⟨13, 0, 15, 6⟩, ⟨13, 0, 14, 8⟩]
  exact AllWinning.cons node_17517 (AllWinning.cons node_16544 (AllWinning.cons node_15450 (AllWinning.cons node_14460 (AllWinning.cons node_17576 (AllWinning.cons node_16661 (AllWinning.cons node_15613 (AllWinning.cons node_14675 (AllWinning.nil))))))))

theorem node_18479 : Outcome ⟨13, 0, 18, 14⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 10⟩) (by decide) node_13707

theorem node_18480 : Outcome ⟨13, 1, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 17, 2⟩, ⟨11, 1, 17, 4⟩, ⟨13, 0, 17, 2⟩, ⟨13, 1, 16, 2⟩, ⟨13, 1, 15, 4⟩]
  exact AllWinning.cons node_17520 (AllWinning.cons node_16547 (AllWinning.cons node_17576 (AllWinning.cons node_17578 (AllWinning.cons node_16664 (AllWinning.nil)))))

theorem node_18481 : Outcome ⟨13, 1, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 17, 2⟩, ⟨11, 1, 17, 4⟩, ⟨10, 1, 17, 6⟩, ⟨9, 1, 17, 8⟩, ⟨13, 0, 17, 2⟩, ⟨13, 1, 16, 2⟩, ⟨13, 1, 15, 4⟩, ⟨13, 1, 14, 6⟩, ⟨13, 1, 13, 8⟩]
  exact AllWinning.cons node_17520 (AllWinning.cons node_16547 (AllWinning.cons node_15453 (AllWinning.cons node_14463 (AllWinning.cons node_17576 (AllWinning.cons node_17578 (AllWinning.cons node_16664 (AllWinning.cons node_15616 (AllWinning.cons node_14678 (AllWinning.nil)))))))))

theorem node_18482 : Outcome ⟨13, 1, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 17, 2⟩, ⟨11, 1, 17, 4⟩, ⟨10, 1, 17, 6⟩, ⟨9, 1, 17, 8⟩, ⟨8, 1, 17, 10⟩, ⟨7, 1, 17, 12⟩, ⟨13, 0, 17, 2⟩, ⟨13, 1, 16, 2⟩, ⟨13, 1, 15, 4⟩, ⟨13, 1, 14, 6⟩, ⟨13, 1, 13, 8⟩, ⟨13, 1, 12, 10⟩, ⟨13, 1, 11, 12⟩]
  exact AllWinning.cons node_17520 (AllWinning.cons node_16547 (AllWinning.cons node_15453 (AllWinning.cons node_14463 (AllWinning.cons node_13432 (AllWinning.cons node_12425 (AllWinning.cons node_17576 (AllWinning.cons node_17578 (AllWinning.cons node_16664 (AllWinning.cons node_15616 (AllWinning.cons node_14678 (AllWinning.cons node_13714 (AllWinning.cons node_12749 (AllWinning.nil)))))))))))))

theorem node_18483 : Outcome ⟨13, 1, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 17, 2⟩, ⟨11, 1, 17, 4⟩, ⟨10, 1, 17, 6⟩, ⟨9, 1, 17, 8⟩, ⟨8, 1, 17, 10⟩, ⟨7, 1, 17, 12⟩, ⟨6, 1, 17, 14⟩, ⟨5, 1, 17, 16⟩, ⟨13, 0, 17, 2⟩, ⟨13, 1, 16, 2⟩, ⟨13, 1, 15, 4⟩, ⟨13, 1, 14, 6⟩, ⟨13, 1, 13, 8⟩, ⟨13, 1, 12, 10⟩, ⟨13, 1, 11, 12⟩, ⟨13, 1, 10, 14⟩, ⟨13, 1, 9, 16⟩]
  exact AllWinning.cons node_17520 (AllWinning.cons node_16547 (AllWinning.cons node_15453 (AllWinning.cons node_14463 (AllWinning.cons node_13432 (AllWinning.cons node_12425 (AllWinning.cons node_11368 (AllWinning.cons node_10257 (AllWinning.cons node_17576 (AllWinning.cons node_17578 (AllWinning.cons node_16664 (AllWinning.cons node_15616 (AllWinning.cons node_14678 (AllWinning.cons node_13714 (AllWinning.cons node_12749 (AllWinning.cons node_11783 (AllWinning.cons node_10756 (AllWinning.nil)))))))))))))))))

theorem node_18484 : Outcome ⟨13, 1, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 17, 2⟩, ⟨11, 1, 17, 4⟩, ⟨10, 1, 17, 6⟩, ⟨9, 1, 17, 8⟩, ⟨8, 1, 17, 10⟩, ⟨7, 1, 17, 12⟩, ⟨6, 1, 17, 14⟩, ⟨5, 1, 17, 16⟩, ⟨4, 1, 17, 18⟩, ⟨3, 1, 17, 20⟩, ⟨13, 0, 17, 2⟩, ⟨13, 1, 16, 2⟩, ⟨13, 1, 15, 4⟩, ⟨13, 1, 14, 6⟩, ⟨13, 1, 13, 8⟩, ⟨13, 1, 12, 10⟩, ⟨13, 1, 11, 12⟩, ⟨13, 1, 10, 14⟩, ⟨13, 1, 9, 16⟩, ⟨13, 1, 8, 18⟩, ⟨13, 1, 7, 20⟩]
  exact AllWinning.cons node_17520 (AllWinning.cons node_16547 (AllWinning.cons node_15453 (AllWinning.cons node_14463 (AllWinning.cons node_13432 (AllWinning.cons node_12425 (AllWinning.cons node_11368 (AllWinning.cons node_10257 (AllWinning.cons node_9204 (AllWinning.cons node_8152 (AllWinning.cons node_17576 (AllWinning.cons node_17578 (AllWinning.cons node_16664 (AllWinning.cons node_15616 (AllWinning.cons node_14678 (AllWinning.cons node_13714 (AllWinning.cons node_12749 (AllWinning.cons node_11783 (AllWinning.cons node_10756 (AllWinning.cons node_9711 (AllWinning.cons node_8771 (AllWinning.nil)))))))))))))))))))))

theorem node_18485 : Outcome ⟨13, 1, 17, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 17, 2⟩, ⟨11, 1, 17, 4⟩, ⟨10, 1, 17, 6⟩, ⟨9, 1, 17, 8⟩, ⟨8, 1, 17, 10⟩, ⟨7, 1, 17, 12⟩, ⟨6, 1, 17, 14⟩, ⟨5, 1, 17, 16⟩, ⟨4, 1, 17, 18⟩, ⟨3, 1, 17, 20⟩, ⟨2, 1, 17, 22⟩, ⟨1, 1, 17, 24⟩, ⟨0, 1, 17, 26⟩, ⟨13, 0, 17, 2⟩, ⟨13, 1, 16, 2⟩, ⟨13, 1, 15, 4⟩, ⟨13, 1, 14, 6⟩, ⟨13, 1, 13, 8⟩, ⟨13, 1, 12, 10⟩, ⟨13, 1, 11, 12⟩, ⟨13, 1, 10, 14⟩, ⟨13, 1, 9, 16⟩, ⟨13, 1, 8, 18⟩, ⟨13, 1, 7, 20⟩, ⟨13, 1, 6, 22⟩, ⟨13, 1, 5, 24⟩, ⟨13, 1, 4, 26⟩, ⟨13, 1, 3, 28⟩]
  exact AllWinning.cons node_17520 (AllWinning.cons node_16547 (AllWinning.cons node_15453 (AllWinning.cons node_14463 (AllWinning.cons node_13432 (AllWinning.cons node_12425 (AllWinning.cons node_11368 (AllWinning.cons node_10257 (AllWinning.cons node_9204 (AllWinning.cons node_8152 (AllWinning.cons node_7122 (AllWinning.cons node_6118 (AllWinning.cons node_5316 (AllWinning.cons node_17576 (AllWinning.cons node_17578 (AllWinning.cons node_16664 (AllWinning.cons node_15616 (AllWinning.cons node_14678 (AllWinning.cons node_13714 (AllWinning.cons node_12749 (AllWinning.cons node_11783 (AllWinning.cons node_10756 (AllWinning.cons node_9711 (AllWinning.cons node_8771 (AllWinning.cons node_7765 (AllWinning.cons node_6847 (AllWinning.cons node_5962 (AllWinning.cons node_5246 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_18486 : Outcome ⟨13, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨13, 2, 15, 2⟩) (by decide) node_17580

theorem node_18487 : Outcome ⟨13, 2, 16, 6⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 6⟩) (by decide) node_15456

theorem node_18488 : Outcome ⟨13, 2, 16, 10⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 6⟩) (by decide) node_15456

theorem node_18489 : Outcome ⟨13, 3, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 2⟩) (by decide) node_17525

theorem node_18490 : Outcome ⟨13, 3, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 2⟩) (by decide) node_17525

theorem node_18491 : Outcome ⟨13, 3, 15, 10⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 12⟩) (by decide) node_12435

theorem node_18492 : Outcome ⟨13, 3, 15, 12⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 12⟩) (by decide) node_12435

theorem node_18493 : Outcome ⟨13, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 4⟩) (by decide) node_16673

theorem node_18494 : Outcome ⟨13, 4, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 4⟩) (by decide) node_16673

theorem node_18495 : Outcome ⟨13, 4, 14, 6⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 4⟩) (by decide) node_16673

theorem node_18496 : Outcome ⟨13, 4, 14, 12⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 4⟩) (by decide) node_16673

theorem node_18497 : Outcome ⟨13, 5, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 13, 2⟩, ⟨11, 5, 13, 4⟩, ⟨13, 4, 13, 2⟩, ⟨13, 3, 13, 4⟩, ⟨13, 5, 12, 2⟩, ⟨13, 5, 11, 4⟩]
  exact AllWinning.cons node_17534 (AllWinning.cons node_16557 (AllWinning.cons node_17587 (AllWinning.cons node_16668 (AllWinning.cons node_17591 (AllWinning.cons node_16682 (AllWinning.nil))))))

theorem node_18498 : Outcome ⟨13, 5, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 13, 2⟩, ⟨11, 5, 13, 4⟩, ⟨10, 5, 13, 6⟩, ⟨9, 5, 13, 8⟩, ⟨13, 4, 13, 2⟩, ⟨13, 3, 13, 4⟩, ⟨13, 2, 13, 6⟩, ⟨13, 1, 13, 8⟩, ⟨13, 5, 12, 2⟩, ⟨13, 5, 11, 4⟩, ⟨13, 5, 10, 6⟩, ⟨13, 5, 9, 8⟩]
  exact AllWinning.cons node_17534 (AllWinning.cons node_16557 (AllWinning.cons node_15466 (AllWinning.cons node_14477 (AllWinning.cons node_17587 (AllWinning.cons node_16668 (AllWinning.cons node_15619 (AllWinning.cons node_14678 (AllWinning.cons node_17591 (AllWinning.cons node_16682 (AllWinning.cons node_15629 (AllWinning.cons node_14688 (AllWinning.nil))))))))))))

theorem node_18499 : Outcome ⟨13, 5, 13, 6⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 10⟩) (by decide) node_13707

theorem node_18500 : Outcome ⟨13, 5, 13, 16⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 10⟩) (by decide) node_13707

theorem node_18501 : Outcome ⟨13, 6, 12, 4⟩ true :=
  Outcome.win (q := ⟨11, 6, 12, 4⟩) (by decide) node_16559

theorem node_18502 : Outcome ⟨13, 6, 12, 6⟩ true :=
  Outcome.win (q := ⟨11, 6, 12, 4⟩) (by decide) node_16559

theorem node_18503 : Outcome ⟨13, 7, 11, 2⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 4⟩) (by decide) node_16687

theorem node_18504 : Outcome ⟨13, 7, 11, 6⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 4⟩) (by decide) node_16687

theorem node_18505 : Outcome ⟨13, 7, 11, 14⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 24⟩) (by decide) node_6148

theorem node_18506 : Outcome ⟨13, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 4⟩) (by decide) node_16566

theorem node_18507 : Outcome ⟨13, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 4⟩) (by decide) node_16566

theorem node_18508 : Outcome ⟨13, 8, 10, 6⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 10⟩) (by decide) node_13723

theorem node_18509 : Outcome ⟨13, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 4⟩) (by decide) node_16687

theorem node_18510 : Outcome ⟨13, 9, 9, 6⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 4⟩) (by decide) node_16687

theorem node_18511 : Outcome ⟨13, 9, 9, 12⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 4⟩) (by decide) node_16687

theorem node_18512 : Outcome ⟨13, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 4⟩) (by decide) node_16574

theorem node_18513 : Outcome ⟨13, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 4⟩) (by decide) node_16574

theorem node_18514 : Outcome ⟨13, 10, 8, 6⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 10⟩) (by decide) node_13749

theorem node_18515 : Outcome ⟨13, 11, 7, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 4⟩) (by decide) node_16698

theorem node_18516 : Outcome ⟨13, 11, 7, 6⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 4⟩) (by decide) node_16698

theorem node_18517 : Outcome ⟨13, 11, 7, 14⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 24⟩) (by decide) node_6173

theorem node_18518 : Outcome ⟨13, 12, 6, 4⟩ true :=
  Outcome.win (q := ⟨11, 12, 6, 4⟩) (by decide) node_16582

theorem node_18519 : Outcome ⟨13, 12, 6, 6⟩ true :=
  Outcome.win (q := ⟨11, 12, 6, 4⟩) (by decide) node_16582

theorem node_18520 : Outcome ⟨13, 13, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 5, 2⟩, ⟨11, 13, 5, 4⟩, ⟨13, 12, 5, 2⟩, ⟨13, 11, 5, 4⟩, ⟨13, 13, 4, 2⟩, ⟨13, 13, 3, 4⟩]
  exact AllWinning.cons node_17556 (AllWinning.cons node_16586 (AllWinning.cons node_17612 (AllWinning.cons node_16708 (AllWinning.cons node_17615 (AllWinning.cons node_16717 (AllWinning.nil))))))

theorem node_18521 : Outcome ⟨13, 13, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 5, 2⟩, ⟨11, 13, 5, 4⟩, ⟨10, 13, 5, 6⟩, ⟨9, 13, 5, 8⟩, ⟨13, 12, 5, 2⟩, ⟨13, 11, 5, 4⟩, ⟨13, 10, 5, 6⟩, ⟨13, 9, 5, 8⟩, ⟨13, 13, 4, 2⟩, ⟨13, 13, 3, 4⟩, ⟨13, 13, 2, 6⟩, ⟨13, 13, 1, 8⟩]
  exact AllWinning.cons node_17556 (AllWinning.cons node_16586 (AllWinning.cons node_15488 (AllWinning.cons node_14497 (AllWinning.cons node_17612 (AllWinning.cons node_16708 (AllWinning.cons node_15644 (AllWinning.cons node_14697 (AllWinning.cons node_17615 (AllWinning.cons node_16717 (AllWinning.cons node_15654 (AllWinning.cons node_14705 (AllWinning.nil))))))))))))

theorem node_18522 : Outcome ⟨13, 13, 5, 6⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 10⟩) (by decide) node_13765

theorem node_18523 : Outcome ⟨13, 13, 5, 16⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 10⟩) (by decide) node_13765

theorem node_18524 : Outcome ⟨13, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 4⟩) (by decide) node_16710

theorem node_18525 : Outcome ⟨13, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 4⟩) (by decide) node_16710

theorem node_18526 : Outcome ⟨13, 14, 4, 6⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 4⟩) (by decide) node_16710

theorem node_18527 : Outcome ⟨13, 14, 4, 12⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 4⟩) (by decide) node_16710

theorem node_18528 : Outcome ⟨13, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 2⟩) (by decide) node_17563

theorem node_18529 : Outcome ⟨13, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 2⟩) (by decide) node_17563

theorem node_18530 : Outcome ⟨13, 15, 3, 10⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 12⟩) (by decide) node_12474

theorem node_18531 : Outcome ⟨13, 15, 3, 12⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 12⟩) (by decide) node_12474

theorem node_18532 : Outcome ⟨13, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 2, 2⟩) (by decide) node_17623

theorem node_18533 : Outcome ⟨13, 16, 2, 6⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 6⟩) (by decide) node_15499

theorem node_18534 : Outcome ⟨13, 16, 2, 10⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 6⟩) (by decide) node_15499

theorem node_18535 : Outcome ⟨13, 17, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 1, 2⟩, ⟨11, 17, 1, 4⟩, ⟨13, 16, 1, 2⟩, ⟨13, 15, 1, 4⟩, ⟨13, 17, 0, 2⟩]
  exact AllWinning.cons node_17571 (AllWinning.cons node_16597 (AllWinning.cons node_17626 (AllWinning.cons node_16724 (AllWinning.cons node_17628 (AllWinning.nil)))))

theorem node_18536 : Outcome ⟨13, 17, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 1, 2⟩, ⟨11, 17, 1, 4⟩, ⟨10, 17, 1, 6⟩, ⟨9, 17, 1, 8⟩, ⟨13, 16, 1, 2⟩, ⟨13, 15, 1, 4⟩, ⟨13, 14, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨13, 17, 0, 2⟩]
  exact AllWinning.cons node_17571 (AllWinning.cons node_16597 (AllWinning.cons node_15502 (AllWinning.cons node_14509 (AllWinning.cons node_17626 (AllWinning.cons node_16724 (AllWinning.cons node_15658 (AllWinning.cons node_14705 (AllWinning.cons node_17628 (AllWinning.nil)))))))))

theorem node_18537 : Outcome ⟨13, 17, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 1, 2⟩, ⟨11, 17, 1, 4⟩, ⟨10, 17, 1, 6⟩, ⟨9, 17, 1, 8⟩, ⟨8, 17, 1, 10⟩, ⟨7, 17, 1, 12⟩, ⟨13, 16, 1, 2⟩, ⟨13, 15, 1, 4⟩, ⟨13, 14, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨13, 12, 1, 10⟩, ⟨13, 11, 1, 12⟩, ⟨13, 17, 0, 2⟩]
  exact AllWinning.cons node_17571 (AllWinning.cons node_16597 (AllWinning.cons node_15502 (AllWinning.cons node_14509 (AllWinning.cons node_13484 (AllWinning.cons node_12483 (AllWinning.cons node_17626 (AllWinning.cons node_16724 (AllWinning.cons node_15658 (AllWinning.cons node_14705 (AllWinning.cons node_13759 (AllWinning.cons node_12771 (AllWinning.cons node_17628 (AllWinning.nil)))))))))))))

theorem node_18538 : Outcome ⟨13, 17, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 1, 2⟩, ⟨11, 17, 1, 4⟩, ⟨10, 17, 1, 6⟩, ⟨9, 17, 1, 8⟩, ⟨8, 17, 1, 10⟩, ⟨7, 17, 1, 12⟩, ⟨6, 17, 1, 14⟩, ⟨5, 17, 1, 16⟩, ⟨13, 16, 1, 2⟩, ⟨13, 15, 1, 4⟩, ⟨13, 14, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨13, 12, 1, 10⟩, ⟨13, 11, 1, 12⟩, ⟨13, 10, 1, 14⟩, ⟨13, 9, 1, 16⟩, ⟨13, 17, 0, 2⟩]
  exact AllWinning.cons node_17571 (AllWinning.cons node_16597 (AllWinning.cons node_15502 (AllWinning.cons node_14509 (AllWinning.cons node_13484 (AllWinning.cons node_12483 (AllWinning.cons node_11424 (AllWinning.cons node_10328 (AllWinning.cons node_17626 (AllWinning.cons node_16724 (AllWinning.cons node_15658 (AllWinning.cons node_14705 (AllWinning.cons node_13759 (AllWinning.cons node_12771 (AllWinning.cons node_11804 (AllWinning.cons node_10789 (AllWinning.cons node_17628 (AllWinning.nil)))))))))))))))))

theorem node_18539 : Outcome ⟨13, 17, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 1, 2⟩, ⟨11, 17, 1, 4⟩, ⟨10, 17, 1, 6⟩, ⟨9, 17, 1, 8⟩, ⟨8, 17, 1, 10⟩, ⟨7, 17, 1, 12⟩, ⟨6, 17, 1, 14⟩, ⟨5, 17, 1, 16⟩, ⟨4, 17, 1, 18⟩, ⟨3, 17, 1, 20⟩, ⟨13, 16, 1, 2⟩, ⟨13, 15, 1, 4⟩, ⟨13, 14, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨13, 12, 1, 10⟩, ⟨13, 11, 1, 12⟩, ⟨13, 10, 1, 14⟩, ⟨13, 9, 1, 16⟩, ⟨13, 8, 1, 18⟩, ⟨13, 7, 1, 20⟩, ⟨13, 17, 0, 2⟩]
  exact AllWinning.cons node_17571 (AllWinning.cons node_16597 (AllWinning.cons node_15502 (AllWinning.cons node_14509 (AllWinning.cons node_13484 (AllWinning.cons node_12483 (AllWinning.cons node_11424 (AllWinning.cons node_10328 (AllWinning.cons node_9267 (AllWinning.cons node_8215 (AllWinning.cons node_17626 (AllWinning.cons node_16724 (AllWinning.cons node_15658 (AllWinning.cons node_14705 (AllWinning.cons node_13759 (AllWinning.cons node_12771 (AllWinning.cons node_11804 (AllWinning.cons node_10789 (AllWinning.cons node_9733 (AllWinning.cons node_8792 (AllWinning.cons node_17628 (AllWinning.nil)))))))))))))))))))))

theorem node_18540 : Outcome ⟨13, 17, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 1, 2⟩, ⟨11, 17, 1, 4⟩, ⟨10, 17, 1, 6⟩, ⟨9, 17, 1, 8⟩, ⟨8, 17, 1, 10⟩, ⟨7, 17, 1, 12⟩, ⟨6, 17, 1, 14⟩, ⟨5, 17, 1, 16⟩, ⟨4, 17, 1, 18⟩, ⟨3, 17, 1, 20⟩, ⟨2, 17, 1, 22⟩, ⟨1, 17, 1, 24⟩, ⟨0, 17, 1, 26⟩, ⟨13, 16, 1, 2⟩, ⟨13, 15, 1, 4⟩, ⟨13, 14, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨13, 12, 1, 10⟩, ⟨13, 11, 1, 12⟩, ⟨13, 10, 1, 14⟩, ⟨13, 9, 1, 16⟩, ⟨13, 8, 1, 18⟩, ⟨13, 7, 1, 20⟩, ⟨13, 6, 1, 22⟩, ⟨13, 5, 1, 24⟩, ⟨13, 4, 1, 26⟩, ⟨13, 3, 1, 28⟩, ⟨13, 17, 0, 2⟩]
  exact AllWinning.cons node_17571 (AllWinning.cons node_16597 (AllWinning.cons node_15502 (AllWinning.cons node_14509 (AllWinning.cons node_13484 (AllWinning.cons node_12483 (AllWinning.cons node_11424 (AllWinning.cons node_10328 (AllWinning.cons node_9267 (AllWinning.cons node_8215 (AllWinning.cons node_7195 (AllWinning.cons node_6193 (AllWinning.cons node_5385 (AllWinning.cons node_17626 (AllWinning.cons node_16724 (AllWinning.cons node_15658 (AllWinning.cons node_14705 (AllWinning.cons node_13759 (AllWinning.cons node_12771 (AllWinning.cons node_11804 (AllWinning.cons node_10789 (AllWinning.cons node_9733 (AllWinning.cons node_8792 (AllWinning.cons node_7782 (AllWinning.cons node_6863 (AllWinning.cons node_5972 (AllWinning.cons node_5258 (AllWinning.cons node_17628 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_18541 : Outcome ⟨13, 18, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 0, 2⟩, ⟨11, 18, 0, 4⟩, ⟨13, 17, 0, 2⟩, ⟨13, 16, 0, 4⟩]
  exact AllWinning.cons node_17573 (AllWinning.cons node_16599 (AllWinning.cons node_17628 (AllWinning.cons node_16726 (AllWinning.nil))))

theorem node_18542 : Outcome ⟨13, 18, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 0, 2⟩, ⟨11, 18, 0, 4⟩, ⟨10, 18, 0, 6⟩, ⟨9, 18, 0, 8⟩, ⟨13, 17, 0, 2⟩, ⟨13, 16, 0, 4⟩, ⟨13, 15, 0, 6⟩, ⟨13, 14, 0, 8⟩]
  exact AllWinning.cons node_17573 (AllWinning.cons node_16599 (AllWinning.cons node_15506 (AllWinning.cons node_14512 (AllWinning.cons node_17628 (AllWinning.cons node_16726 (AllWinning.cons node_15661 (AllWinning.cons node_14708 (AllWinning.nil))))))))

theorem node_18543 : Outcome ⟨13, 18, 0, 14⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 10⟩) (by decide) node_13765

theorem node_18544 : Outcome ⟨14, 0, 17, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18545 : Outcome ⟨14, 0, 17, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18546 : Outcome ⟨14, 1, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 4⟩) (by decide) node_16606

theorem node_18547 : Outcome ⟨14, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 16, 4⟩) (by decide) node_16606

theorem node_18548 : Outcome ⟨14, 1, 16, 6⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 12⟩) (by decide) node_12781

theorem node_18549 : Outcome ⟨14, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨13, 2, 15, 2⟩) (by decide) node_17580

theorem node_18550 : Outcome ⟨14, 2, 15, 12⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 10⟩) (by decide) node_13499

theorem node_18551 : Outcome ⟨14, 3, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 14, 2⟩, ⟨12, 3, 14, 4⟩, ⟨14, 2, 14, 2⟩, ⟨14, 1, 14, 4⟩, ⟨14, 3, 13, 2⟩, ⟨14, 3, 12, 4⟩]
  exact AllWinning.cons node_17583 (AllWinning.cons node_16612 (AllWinning.cons node_17637 (AllWinning.cons node_16732 (AllWinning.cons node_17642 (AllWinning.cons node_16738 (AllWinning.nil))))))

theorem node_18552 : Outcome ⟨14, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18553 : Outcome ⟨14, 3, 14, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18554 : Outcome ⟨14, 3, 14, 12⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18555 : Outcome ⟨14, 3, 14, 22⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18556 : Outcome ⟨14, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18557 : Outcome ⟨14, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18558 : Outcome ⟨14, 4, 13, 6⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18559 : Outcome ⟨14, 4, 13, 12⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 4⟩) (by decide) node_16616

theorem node_18560 : Outcome ⟨14, 5, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 5, 12, 2⟩, ⟨12, 5, 12, 4⟩, ⟨14, 4, 12, 2⟩, ⟨14, 3, 12, 4⟩, ⟨14, 5, 11, 2⟩, ⟨14, 5, 10, 4⟩]
  exact AllWinning.cons node_17591 (AllWinning.cons node_16621 (AllWinning.cons node_17646 (AllWinning.cons node_16738 (AllWinning.cons node_17650 (AllWinning.cons node_16743 (AllWinning.nil))))))

theorem node_18561 : Outcome ⟨14, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 8⟩) (by decide) node_14531

theorem node_18562 : Outcome ⟨14, 5, 12, 6⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 8⟩) (by decide) node_14531

theorem node_18563 : Outcome ⟨14, 5, 12, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 8⟩) (by decide) node_14531

theorem node_18564 : Outcome ⟨14, 6, 11, 2⟩ true :=
  Outcome.win (q := ⟨12, 6, 11, 4⟩) (by decide) node_16624

theorem node_18565 : Outcome ⟨14, 6, 11, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 11, 4⟩) (by decide) node_16624

theorem node_18566 : Outcome ⟨14, 7, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 7, 10, 2⟩, ⟨12, 7, 10, 4⟩, ⟨14, 6, 10, 2⟩, ⟨14, 5, 10, 4⟩, ⟨14, 7, 9, 2⟩, ⟨14, 7, 8, 4⟩]
  exact AllWinning.cons node_17596 (AllWinning.cons node_16628 (AllWinning.cons node_17652 (AllWinning.cons node_16743 (AllWinning.cons node_17655 (AllWinning.cons node_16751 (AllWinning.nil))))))

theorem node_18567 : Outcome ⟨14, 7, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 7, 10, 2⟩, ⟨12, 7, 10, 4⟩, ⟨11, 7, 10, 6⟩, ⟨10, 7, 10, 8⟩, ⟨14, 6, 10, 2⟩, ⟨14, 5, 10, 4⟩, ⟨14, 4, 10, 6⟩, ⟨14, 3, 10, 8⟩, ⟨14, 7, 9, 2⟩, ⟨14, 7, 8, 4⟩, ⟨14, 7, 7, 6⟩, ⟨14, 7, 6, 8⟩]
  exact AllWinning.cons node_17596 (AllWinning.cons node_16628 (AllWinning.cons node_15529 (AllWinning.cons node_14539 (AllWinning.cons node_17652 (AllWinning.cons node_16743 (AllWinning.cons node_15687 (AllWinning.cons node_14719 (AllWinning.cons node_17655 (AllWinning.cons node_16751 (AllWinning.cons node_15697 (AllWinning.cons node_14732 (AllWinning.nil))))))))))))

theorem node_18568 : Outcome ⟨14, 7, 10, 6⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 12⟩) (by decide) node_12781

theorem node_18569 : Outcome ⟨14, 8, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 8, 9, 2⟩, ⟨12, 8, 9, 4⟩, ⟨14, 7, 9, 2⟩, ⟨14, 6, 9, 4⟩, ⟨14, 8, 8, 2⟩, ⟨14, 8, 7, 4⟩]
  exact AllWinning.cons node_17600 (AllWinning.cons node_16630 (AllWinning.cons node_17655 (AllWinning.cons node_16747 (AllWinning.cons node_17658 (AllWinning.cons node_16753 (AllWinning.nil))))))

theorem node_18570 : Outcome ⟨14, 8, 9, 6⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 6⟩) (by decide) node_15691

theorem node_18571 : Outcome ⟨14, 8, 9, 12⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 6⟩) (by decide) node_15691

theorem node_18572 : Outcome ⟨14, 9, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 8, 2⟩, ⟨12, 9, 8, 4⟩, ⟨14, 8, 8, 2⟩, ⟨14, 7, 8, 4⟩, ⟨14, 9, 7, 2⟩, ⟨14, 9, 6, 4⟩]
  exact AllWinning.cons node_17603 (AllWinning.cons node_16631 (AllWinning.cons node_17658 (AllWinning.cons node_16751 (AllWinning.cons node_17661 (AllWinning.cons node_16756 (AllWinning.nil))))))

theorem node_18573 : Outcome ⟨14, 9, 8, 6⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 6⟩) (by decide) node_15703

theorem node_18574 : Outcome ⟨14, 9, 8, 12⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 6⟩) (by decide) node_15703

theorem node_18575 : Outcome ⟨14, 10, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 10, 7, 2⟩, ⟨12, 10, 7, 4⟩, ⟨14, 9, 7, 2⟩, ⟨14, 8, 7, 4⟩, ⟨14, 10, 6, 2⟩, ⟨14, 10, 5, 4⟩]
  exact AllWinning.cons node_17606 (AllWinning.cons node_16632 (AllWinning.cons node_17661 (AllWinning.cons node_16753 (AllWinning.cons node_17664 (AllWinning.cons node_16760 (AllWinning.nil))))))

theorem node_18576 : Outcome ⟨14, 10, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 10, 7, 2⟩, ⟨12, 10, 7, 4⟩, ⟨11, 10, 7, 6⟩, ⟨10, 10, 7, 8⟩, ⟨14, 9, 7, 2⟩, ⟨14, 8, 7, 4⟩, ⟨14, 7, 7, 6⟩, ⟨14, 6, 7, 8⟩, ⟨14, 10, 6, 2⟩, ⟨14, 10, 5, 4⟩, ⟨14, 10, 4, 6⟩, ⟨14, 10, 3, 8⟩]
  exact AllWinning.cons node_17606 (AllWinning.cons node_16632 (AllWinning.cons node_15536 (AllWinning.cons node_14546 (AllWinning.cons node_17661 (AllWinning.cons node_16753 (AllWinning.cons node_15697 (AllWinning.cons node_14727 (AllWinning.cons node_17664 (AllWinning.cons node_16760 (AllWinning.cons node_15707 (AllWinning.cons node_14740 (AllWinning.nil))))))))))))

theorem node_18577 : Outcome ⟨14, 10, 7, 6⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 12⟩) (by decide) node_12814

theorem node_18578 : Outcome ⟨14, 11, 6, 2⟩ true :=
  Outcome.win (q := ⟨12, 11, 6, 4⟩) (by decide) node_16635

theorem node_18579 : Outcome ⟨14, 11, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 11, 6, 4⟩) (by decide) node_16635

theorem node_18580 : Outcome ⟨14, 12, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 12, 5, 2⟩, ⟨12, 12, 5, 4⟩, ⟨14, 11, 5, 2⟩, ⟨14, 10, 5, 4⟩, ⟨14, 12, 4, 2⟩, ⟨14, 12, 3, 4⟩]
  exact AllWinning.cons node_17612 (AllWinning.cons node_16639 (AllWinning.cons node_17667 (AllWinning.cons node_16760 (AllWinning.cons node_17669 (AllWinning.cons node_16767 (AllWinning.nil))))))

theorem node_18581 : Outcome ⟨14, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 8⟩) (by decide) node_14555

theorem node_18582 : Outcome ⟨14, 12, 5, 6⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 8⟩) (by decide) node_14555

theorem node_18583 : Outcome ⟨14, 12, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 8⟩) (by decide) node_14555

theorem node_18584 : Outcome ⟨14, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 4⟩) (by decide) node_16642

theorem node_18585 : Outcome ⟨14, 13, 4, 4⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 4⟩) (by decide) node_16642

theorem node_18586 : Outcome ⟨14, 13, 4, 6⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 4⟩) (by decide) node_16642

theorem node_18587 : Outcome ⟨14, 13, 4, 12⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 4⟩) (by decide) node_16642

theorem node_18588 : Outcome ⟨14, 14, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 3, 2⟩, ⟨12, 14, 3, 4⟩, ⟨14, 13, 3, 2⟩, ⟨14, 12, 3, 4⟩, ⟨14, 14, 2, 2⟩, ⟨14, 14, 1, 4⟩]
  exact AllWinning.cons node_17619 (AllWinning.cons node_16648 (AllWinning.cons node_17673 (AllWinning.cons node_16767 (AllWinning.cons node_17677 (AllWinning.cons node_16772 (AllWinning.nil))))))

theorem node_18589 : Outcome ⟨14, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18590 : Outcome ⟨14, 14, 3, 6⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18591 : Outcome ⟨14, 14, 3, 12⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18592 : Outcome ⟨14, 14, 3, 22⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18593 : Outcome ⟨14, 15, 2, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 2, 2⟩) (by decide) node_17623

theorem node_18594 : Outcome ⟨14, 15, 2, 12⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 10⟩) (by decide) node_13536

theorem node_18595 : Outcome ⟨14, 16, 1, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 4⟩) (by decide) node_16654

theorem node_18596 : Outcome ⟨14, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 1, 4⟩) (by decide) node_16654

theorem node_18597 : Outcome ⟨14, 16, 1, 6⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 12⟩) (by decide) node_12814

theorem node_18598 : Outcome ⟨14, 17, 0, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18599 : Outcome ⟨14, 17, 0, 6⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18600 : Outcome ⟨15, 0, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 2⟩) (by decide) node_17689

theorem node_18601 : Outcome ⟨15, 0, 16, 8⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 2⟩) (by decide) node_17689

theorem node_18602 : Outcome ⟨15, 1, 15, 2⟩ true :=
  Outcome.win (q := ⟨14, 1, 15, 2⟩) (by decide) node_17633

theorem node_18603 : Outcome ⟨15, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 1, 15, 2⟩) (by decide) node_17633

theorem node_18604 : Outcome ⟨15, 1, 15, 8⟩ true :=
  Outcome.win (q := ⟨14, 1, 15, 2⟩) (by decide) node_17633

theorem node_18605 : Outcome ⟨15, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 1, 14, 2⟩) (by decide) node_17695

theorem node_18606 : Outcome ⟨15, 2, 14, 12⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 10⟩) (by decide) node_13807

theorem node_18607 : Outcome ⟨15, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 13, 2⟩) (by decide) node_17699

theorem node_18608 : Outcome ⟨15, 3, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 13, 2⟩) (by decide) node_17699

theorem node_18609 : Outcome ⟨15, 3, 13, 10⟩ true :=
  Outcome.win (q := ⟨15, 3, 7, 12⟩) (by decide) node_12837

theorem node_18610 : Outcome ⟨15, 3, 13, 12⟩ true :=
  Outcome.win (q := ⟨15, 3, 7, 12⟩) (by decide) node_12837

theorem node_18611 : Outcome ⟨15, 4, 12, 2⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 4⟩) (by decide) node_16673

theorem node_18612 : Outcome ⟨15, 4, 12, 6⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 4⟩) (by decide) node_16673

theorem node_18613 : Outcome ⟨15, 4, 12, 10⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 4⟩) (by decide) node_16673

theorem node_18614 : Outcome ⟨15, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨15, 4, 11, 2⟩) (by decide) node_17705

theorem node_18615 : Outcome ⟨15, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 6⟩) (by decide) node_15746

theorem node_18616 : Outcome ⟨15, 5, 11, 8⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 6⟩) (by decide) node_15746

theorem node_18617 : Outcome ⟨15, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨15, 6, 9, 2⟩) (by decide) node_17711

theorem node_18618 : Outcome ⟨15, 6, 10, 4⟩ true :=
  Outcome.win (q := ⟨15, 6, 9, 2⟩) (by decide) node_17711

theorem node_18619 : Outcome ⟨15, 6, 10, 6⟩ true :=
  Outcome.win (q := ⟨15, 6, 9, 2⟩) (by decide) node_17711

theorem node_18620 : Outcome ⟨15, 7, 9, 2⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 4⟩) (by decide) node_16687

theorem node_18621 : Outcome ⟨15, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 4⟩) (by decide) node_16687

theorem node_18622 : Outcome ⟨15, 7, 9, 6⟩ true :=
  Outcome.win (q := ⟨15, 7, 3, 12⟩) (by decide) node_12852

theorem node_18623 : Outcome ⟨15, 7, 9, 12⟩ true :=
  Outcome.win (q := ⟨15, 7, 3, 12⟩) (by decide) node_12852

theorem node_18624 : Outcome ⟨15, 8, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 8, 8, 2⟩, ⟨13, 8, 8, 4⟩, ⟨15, 7, 8, 2⟩, ⟨15, 6, 8, 4⟩, ⟨15, 8, 7, 2⟩, ⟨15, 8, 6, 4⟩]
  exact AllWinning.cons node_17658 (AllWinning.cons node_16695 (AllWinning.cons node_17714 (AllWinning.cons node_16794 (AllWinning.cons node_17718 (AllWinning.cons node_16799 (AllWinning.nil))))))

theorem node_18625 : Outcome ⟨15, 8, 8, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18626 : Outcome ⟨15, 8, 8, 6⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18627 : Outcome ⟨15, 8, 8, 12⟩ true :=
  Outcome.win (q := ⟨12, 8, 8, 6⟩) (by decide) node_15585

theorem node_18628 : Outcome ⟨15, 9, 7, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 4⟩) (by decide) node_16698

theorem node_18629 : Outcome ⟨15, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 4⟩) (by decide) node_16698

theorem node_18630 : Outcome ⟨15, 9, 7, 6⟩ true :=
  Outcome.win (q := ⟨15, 3, 7, 12⟩) (by decide) node_12837

theorem node_18631 : Outcome ⟨15, 9, 7, 12⟩ true :=
  Outcome.win (q := ⟨15, 3, 7, 12⟩) (by decide) node_12837

theorem node_18632 : Outcome ⟨15, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨15, 9, 6, 2⟩) (by decide) node_17722

theorem node_18633 : Outcome ⟨15, 10, 6, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 6, 2⟩) (by decide) node_17722

theorem node_18634 : Outcome ⟨15, 10, 6, 6⟩ true :=
  Outcome.win (q := ⟨15, 9, 6, 2⟩) (by decide) node_17722

theorem node_18635 : Outcome ⟨15, 11, 5, 2⟩ true :=
  Outcome.win (q := ⟨15, 11, 4, 2⟩) (by decide) node_17727

theorem node_18636 : Outcome ⟨15, 11, 5, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 6⟩) (by decide) node_15763

theorem node_18637 : Outcome ⟨15, 11, 5, 8⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 6⟩) (by decide) node_15763

theorem node_18638 : Outcome ⟨15, 12, 4, 2⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 4⟩) (by decide) node_16710

theorem node_18639 : Outcome ⟨15, 12, 4, 6⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 4⟩) (by decide) node_16710

theorem node_18640 : Outcome ⟨15, 12, 4, 10⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 4⟩) (by decide) node_16710

theorem node_18641 : Outcome ⟨15, 13, 3, 2⟩ true :=
  Outcome.win (q := ⟨15, 12, 3, 2⟩) (by decide) node_17731

theorem node_18642 : Outcome ⟨15, 13, 3, 4⟩ true :=
  Outcome.win (q := ⟨15, 12, 3, 2⟩) (by decide) node_17731

theorem node_18643 : Outcome ⟨15, 13, 3, 10⟩ true :=
  Outcome.win (q := ⟨15, 7, 3, 12⟩) (by decide) node_12852

theorem node_18644 : Outcome ⟨15, 13, 3, 12⟩ true :=
  Outcome.win (q := ⟨15, 7, 3, 12⟩) (by decide) node_12852

theorem node_18645 : Outcome ⟨15, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 2, 2⟩) (by decide) node_17735

theorem node_18646 : Outcome ⟨15, 14, 2, 12⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 10⟩) (by decide) node_13831

theorem node_18647 : Outcome ⟨15, 15, 1, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 1, 2⟩) (by decide) node_17682

theorem node_18648 : Outcome ⟨15, 15, 1, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 1, 2⟩) (by decide) node_17682

theorem node_18649 : Outcome ⟨15, 15, 1, 8⟩ true :=
  Outcome.win (q := ⟨14, 15, 1, 2⟩) (by decide) node_17682

theorem node_18650 : Outcome ⟨15, 16, 0, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 2⟩) (by decide) node_17741

theorem node_18651 : Outcome ⟨15, 16, 0, 8⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 2⟩) (by decide) node_17741

theorem node_18652 : Outcome ⟨16, 0, 15, 2⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 2⟩) (by decide) node_17689

theorem node_18653 : Outcome ⟨16, 1, 14, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 4⟩) (by decide) node_16820

theorem node_18654 : Outcome ⟨16, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 4⟩) (by decide) node_16820

theorem node_18655 : Outcome ⟨16, 1, 14, 6⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 12⟩) (by decide) node_12601

theorem node_18656 : Outcome ⟨16, 1, 14, 18⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 12⟩) (by decide) node_12601

theorem node_18657 : Outcome ⟨16, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 13, 2⟩) (by decide) node_17699

theorem node_18658 : Outcome ⟨16, 2, 13, 6⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 6⟩) (by decide) node_15793

theorem node_18659 : Outcome ⟨16, 2, 13, 10⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 6⟩) (by decide) node_15793

theorem node_18660 : Outcome ⟨16, 3, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 4⟩) (by decide) node_16820

theorem node_18661 : Outcome ⟨16, 3, 12, 6⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 8⟩) (by decide) node_14800

theorem node_18662 : Outcome ⟨16, 4, 11, 2⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18663 : Outcome ⟨16, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18664 : Outcome ⟨16, 4, 11, 6⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18665 : Outcome ⟨16, 5, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 5, 10, 2⟩, ⟨14, 5, 10, 4⟩, ⟨16, 4, 10, 2⟩, ⟨16, 3, 10, 4⟩, ⟨16, 5, 9, 2⟩, ⟨16, 5, 8, 4⟩]
  exact AllWinning.cons node_17709 (AllWinning.cons node_16743 (AllWinning.cons node_17759 (AllWinning.cons node_16826 (AllWinning.cons node_17763 (AllWinning.cons node_16836 (AllWinning.nil))))))

theorem node_18666 : Outcome ⟨16, 5, 10, 6⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 8⟩) (by decide) node_14640

theorem node_18667 : Outcome ⟨16, 5, 10, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 10, 8⟩) (by decide) node_14640

theorem node_18668 : Outcome ⟨16, 5, 10, 18⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 28⟩) (by decide) node_4755

theorem node_18669 : Outcome ⟨16, 6, 9, 2⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18670 : Outcome ⟨16, 6, 9, 6⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18671 : Outcome ⟨16, 6, 9, 8⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18672 : Outcome ⟨16, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨16, 7, 6, 4⟩) (by decide) node_16842

theorem node_18673 : Outcome ⟨16, 7, 8, 6⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 8⟩) (by decide) node_14800

theorem node_18674 : Outcome ⟨16, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨16, 6, 7, 4⟩) (by decide) node_16838

theorem node_18675 : Outcome ⟨16, 8, 7, 6⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 8⟩) (by decide) node_14818

theorem node_18676 : Outcome ⟨16, 9, 6, 2⟩ true :=
  Outcome.win (q := ⟨16, 7, 6, 4⟩) (by decide) node_16842

theorem node_18677 : Outcome ⟨16, 9, 6, 6⟩ true :=
  Outcome.win (q := ⟨16, 7, 6, 4⟩) (by decide) node_16842

theorem node_18678 : Outcome ⟨16, 9, 6, 8⟩ true :=
  Outcome.win (q := ⟨16, 7, 6, 4⟩) (by decide) node_16842

theorem node_18679 : Outcome ⟨16, 10, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 10, 5, 2⟩, ⟨14, 10, 5, 4⟩, ⟨16, 9, 5, 2⟩, ⟨16, 8, 5, 4⟩, ⟨16, 10, 4, 2⟩, ⟨16, 10, 3, 4⟩]
  exact AllWinning.cons node_17725 (AllWinning.cons node_16760 (AllWinning.cons node_17769 (AllWinning.cons node_16845 (AllWinning.cons node_17771 (AllWinning.cons node_16854 (AllWinning.nil))))))

theorem node_18680 : Outcome ⟨16, 10, 5, 6⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 8⟩) (by decide) node_14657

theorem node_18681 : Outcome ⟨16, 10, 5, 8⟩ true :=
  Outcome.win (q := ⟨12, 10, 5, 8⟩) (by decide) node_14657

theorem node_18682 : Outcome ⟨16, 10, 5, 18⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 28⟩) (by decide) node_4784

theorem node_18683 : Outcome ⟨16, 11, 4, 2⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 4⟩) (by decide) node_16847

theorem node_18684 : Outcome ⟨16, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 4⟩) (by decide) node_16847

theorem node_18685 : Outcome ⟨16, 11, 4, 6⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 4⟩) (by decide) node_16847

theorem node_18686 : Outcome ⟨16, 12, 3, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 4⟩) (by decide) node_16860

theorem node_18687 : Outcome ⟨16, 12, 3, 6⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 8⟩) (by decide) node_14818

theorem node_18688 : Outcome ⟨16, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 2, 2⟩) (by decide) node_17735

theorem node_18689 : Outcome ⟨16, 13, 2, 6⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 6⟩) (by decide) node_15811

theorem node_18690 : Outcome ⟨16, 13, 2, 10⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 6⟩) (by decide) node_15811

theorem node_18691 : Outcome ⟨16, 14, 1, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 4⟩) (by decide) node_16860

theorem node_18692 : Outcome ⟨16, 14, 1, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 4⟩) (by decide) node_16860

theorem node_18693 : Outcome ⟨16, 14, 1, 6⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 12⟩) (by decide) node_12644

theorem node_18694 : Outcome ⟨16, 14, 1, 18⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 12⟩) (by decide) node_12644

end RQ9F1
