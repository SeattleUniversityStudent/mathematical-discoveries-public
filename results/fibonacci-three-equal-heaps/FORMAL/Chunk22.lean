import Chunk21
set_option autoImplicit false
namespace RQ9F1

theorem node_5402 : Outcome ⟨1, 3, 14, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 16⟩) (by decide) node_1226

theorem node_5403 : Outcome ⟨1, 3, 14, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 16⟩) (by decide) node_1226

theorem node_5404 : Outcome ⟨1, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 6⟩) (by decide) node_3394

theorem node_5405 : Outcome ⟨1, 4, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 6⟩) (by decide) node_3394

theorem node_5406 : Outcome ⟨1, 4, 13, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 6⟩) (by decide) node_3394

theorem node_5407 : Outcome ⟨1, 4, 13, 22⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 22⟩) (by decide) node_535

theorem node_5408 : Outcome ⟨1, 4, 13, 26⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 22⟩) (by decide) node_535

theorem node_5409 : Outcome ⟨1, 5, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 12, 2⟩, ⟨1, 4, 12, 2⟩, ⟨1, 3, 12, 4⟩, ⟨1, 5, 11, 2⟩, ⟨1, 5, 10, 4⟩]
  exact AllWinning.cons node_4591 (AllWinning.cons node_4666 (AllWinning.cons node_4009 (AllWinning.cons node_4671 (AllWinning.cons node_4016 (AllWinning.nil)))))

theorem node_5410 : Outcome ⟨1, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 6⟩) (by decide) node_3400

theorem node_5411 : Outcome ⟨1, 5, 12, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 6⟩) (by decide) node_3400

theorem node_5412 : Outcome ⟨1, 6, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 11, 2⟩) (by decide) node_4596

theorem node_5413 : Outcome ⟨1, 6, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 11, 2⟩) (by decide) node_4596

theorem node_5414 : Outcome ⟨1, 6, 11, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 16⟩) (by decide) node_1254

theorem node_5415 : Outcome ⟨1, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 10, 2⟩) (by decide) node_4601

theorem node_5416 : Outcome ⟨1, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 6⟩) (by decide) node_3409

theorem node_5417 : Outcome ⟨1, 7, 10, 14⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 6⟩) (by decide) node_3409

theorem node_5418 : Outcome ⟨1, 8, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 9, 2⟩, ⟨1, 7, 9, 2⟩, ⟨1, 6, 9, 4⟩, ⟨1, 8, 8, 2⟩, ⟨1, 8, 7, 4⟩]
  exact AllWinning.cons node_4605 (AllWinning.cons node_4677 (AllWinning.cons node_4019 (AllWinning.cons node_4682 (AllWinning.cons node_4027 (AllWinning.nil)))))

theorem node_5419 : Outcome ⟨1, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 6⟩) (by decide) node_3414

theorem node_5420 : Outcome ⟨1, 8, 9, 6⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 6⟩) (by decide) node_3414

theorem node_5421 : Outcome ⟨1, 8, 9, 10⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 6⟩) (by decide) node_3414

theorem node_5422 : Outcome ⟨1, 9, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 8, 2⟩, ⟨1, 8, 8, 2⟩, ⟨1, 7, 8, 4⟩, ⟨1, 9, 7, 2⟩, ⟨1, 9, 6, 4⟩]
  exact AllWinning.cons node_4608 (AllWinning.cons node_4682 (AllWinning.cons node_4023 (AllWinning.cons node_4685 (AllWinning.cons node_4030 (AllWinning.nil)))))

theorem node_5423 : Outcome ⟨1, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5424 : Outcome ⟨1, 9, 8, 6⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5425 : Outcome ⟨1, 9, 8, 10⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5426 : Outcome ⟨1, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 10, 7, 2⟩) (by decide) node_4611

theorem node_5427 : Outcome ⟨1, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 6⟩) (by decide) node_3452

theorem node_5428 : Outcome ⟨1, 10, 7, 14⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 6⟩) (by decide) node_3452

theorem node_5429 : Outcome ⟨1, 11, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 6, 2⟩) (by decide) node_4615

theorem node_5430 : Outcome ⟨1, 11, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 6, 2⟩) (by decide) node_4615

theorem node_5431 : Outcome ⟨1, 11, 6, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 16⟩) (by decide) node_1226

theorem node_5432 : Outcome ⟨1, 12, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 5, 2⟩, ⟨1, 11, 5, 2⟩, ⟨1, 10, 5, 4⟩, ⟨1, 12, 4, 2⟩, ⟨1, 12, 3, 4⟩]
  exact AllWinning.cons node_4620 (AllWinning.cons node_4693 (AllWinning.cons node_4034 (AllWinning.cons node_4696 (AllWinning.cons node_4040 (AllWinning.nil)))))

theorem node_5433 : Outcome ⟨1, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5434 : Outcome ⟨1, 12, 5, 6⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5435 : Outcome ⟨1, 13, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 4, 2⟩, ⟨1, 12, 4, 2⟩, ⟨1, 11, 4, 4⟩, ⟨1, 13, 3, 2⟩, ⟨1, 13, 2, 4⟩]
  exact AllWinning.cons node_4625 (AllWinning.cons node_4696 (AllWinning.cons node_4037 (AllWinning.cons node_4701 (AllWinning.cons node_4045 (AllWinning.nil)))))

theorem node_5436 : Outcome ⟨1, 13, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 6⟩) (by decide) node_3452

theorem node_5437 : Outcome ⟨1, 13, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 6⟩) (by decide) node_3452

theorem node_5438 : Outcome ⟨1, 13, 4, 10⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 6⟩) (by decide) node_3452

theorem node_5439 : Outcome ⟨1, 13, 4, 22⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 22⟩) (by decide) node_514

theorem node_5440 : Outcome ⟨1, 13, 4, 26⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 22⟩) (by decide) node_514

theorem node_5441 : Outcome ⟨1, 14, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 3, 2⟩, ⟨1, 13, 3, 2⟩, ⟨1, 12, 3, 4⟩, ⟨1, 14, 2, 2⟩, ⟨1, 14, 1, 4⟩]
  exact AllWinning.cons node_4629 (AllWinning.cons node_4701 (AllWinning.cons node_4040 (AllWinning.cons node_4707 (AllWinning.cons node_4047 (AllWinning.nil)))))

theorem node_5442 : Outcome ⟨1, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 6⟩) (by decide) node_3472

theorem node_5443 : Outcome ⟨1, 14, 3, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 16⟩) (by decide) node_1254

theorem node_5444 : Outcome ⟨1, 14, 3, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 16⟩) (by decide) node_1254

theorem node_5445 : Outcome ⟨1, 15, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 6⟩) (by decide) node_3460

theorem node_5446 : Outcome ⟨1, 15, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 6⟩) (by decide) node_3460

theorem node_5447 : Outcome ⟨1, 15, 2, 16⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 22⟩) (by decide) node_535

theorem node_5448 : Outcome ⟨1, 15, 2, 28⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 22⟩) (by decide) node_535

theorem node_5449 : Outcome ⟨1, 16, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 1, 2⟩, ⟨1, 15, 1, 2⟩, ⟨1, 14, 1, 4⟩, ⟨1, 16, 0, 2⟩]
  exact AllWinning.cons node_4641 (AllWinning.cons node_4711 (AllWinning.cons node_4047 (AllWinning.cons node_4714 (AllWinning.nil))))

theorem node_5450 : Outcome ⟨1, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 6⟩) (by decide) node_3466

theorem node_5451 : Outcome ⟨1, 16, 1, 10⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 6⟩) (by decide) node_3466

theorem node_5452 : Outcome ⟨1, 16, 1, 28⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 32⟩) (by decide) node_69

theorem node_5453 : Outcome ⟨1, 17, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 6⟩) (by decide) node_3472

theorem node_5454 : Outcome ⟨1, 17, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 6⟩) (by decide) node_3472

theorem node_5455 : Outcome ⟨1, 17, 0, 26⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 32⟩) (by decide) node_86

theorem node_5456 : Outcome ⟨2, 0, 16, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 2⟩) (by decide) node_4719

theorem node_5457 : Outcome ⟨2, 0, 16, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 2⟩) (by decide) node_4719

theorem node_5458 : Outcome ⟨2, 0, 16, 20⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 28⟩) (by decide) node_196

theorem node_5459 : Outcome ⟨2, 0, 16, 28⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 28⟩) (by decide) node_196

theorem node_5460 : Outcome ⟨2, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 6⟩) (by decide) node_3483

theorem node_5461 : Outcome ⟨2, 1, 15, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 6⟩) (by decide) node_3483

theorem node_5462 : Outcome ⟨2, 1, 15, 16⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 22⟩) (by decide) node_565

theorem node_5463 : Outcome ⟨2, 1, 15, 28⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 22⟩) (by decide) node_565

theorem node_5464 : Outcome ⟨2, 2, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 2⟩) (by decide) node_4730

theorem node_5465 : Outcome ⟨2, 2, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 2⟩) (by decide) node_4730

theorem node_5466 : Outcome ⟨2, 2, 14, 20⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 28⟩) (by decide) node_217

theorem node_5467 : Outcome ⟨2, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 2⟩) (by decide) node_4730

theorem node_5468 : Outcome ⟨2, 3, 13, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5469 : Outcome ⟨2, 3, 13, 16⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5470 : Outcome ⟨2, 4, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 4, 12, 4⟩) (by decide) node_3942

theorem node_5471 : Outcome ⟨2, 4, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 6⟩) (by decide) node_3483

theorem node_5472 : Outcome ⟨2, 4, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 6⟩) (by decide) node_3483

theorem node_5473 : Outcome ⟨2, 4, 12, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 22⟩) (by decide) node_587

theorem node_5474 : Outcome ⟨2, 4, 12, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 22⟩) (by decide) node_587

theorem node_5475 : Outcome ⟨2, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5476 : Outcome ⟨2, 5, 11, 8⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5477 : Outcome ⟨2, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5478 : Outcome ⟨2, 6, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5479 : Outcome ⟨2, 6, 10, 20⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5480 : Outcome ⟨2, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 6⟩) (by decide) node_3495

theorem node_5481 : Outcome ⟨2, 7, 9, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5482 : Outcome ⟨2, 7, 9, 16⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5483 : Outcome ⟨2, 7, 9, 18⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5484 : Outcome ⟨2, 7, 9, 22⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5485 : Outcome ⟨2, 8, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 4⟩) (by decide) node_3959

theorem node_5486 : Outcome ⟨2, 8, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 4⟩) (by decide) node_3959

theorem node_5487 : Outcome ⟨2, 8, 8, 12⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 4⟩) (by decide) node_3959

theorem node_5488 : Outcome ⟨2, 8, 8, 22⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 4⟩) (by decide) node_3959

theorem node_5489 : Outcome ⟨2, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 6⟩) (by decide) node_3517

theorem node_5490 : Outcome ⟨2, 9, 7, 6⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5491 : Outcome ⟨2, 9, 7, 16⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5492 : Outcome ⟨2, 9, 7, 18⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5493 : Outcome ⟨2, 9, 7, 22⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5494 : Outcome ⟨2, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5495 : Outcome ⟨2, 10, 6, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5496 : Outcome ⟨2, 10, 6, 20⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5497 : Outcome ⟨2, 11, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5498 : Outcome ⟨2, 11, 5, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5499 : Outcome ⟨2, 12, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 4, 4⟩) (by decide) node_3983

theorem node_5500 : Outcome ⟨2, 12, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 6⟩) (by decide) node_3517

theorem node_5501 : Outcome ⟨2, 12, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 6⟩) (by decide) node_3517

theorem node_5502 : Outcome ⟨2, 12, 4, 20⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 22⟩) (by decide) node_565

theorem node_5503 : Outcome ⟨2, 12, 4, 22⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 22⟩) (by decide) node_565

theorem node_5504 : Outcome ⟨2, 13, 3, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 2⟩) (by decide) node_4792

theorem node_5505 : Outcome ⟨2, 13, 3, 14⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5506 : Outcome ⟨2, 13, 3, 16⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5507 : Outcome ⟨2, 14, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 2⟩) (by decide) node_4792

theorem node_5508 : Outcome ⟨2, 14, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 2⟩) (by decide) node_4792

theorem node_5509 : Outcome ⟨2, 14, 2, 20⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 28⟩) (by decide) node_196

theorem node_5510 : Outcome ⟨2, 15, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 6⟩) (by decide) node_3529

theorem node_5511 : Outcome ⟨2, 15, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 6⟩) (by decide) node_3529

theorem node_5512 : Outcome ⟨2, 15, 1, 16⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 22⟩) (by decide) node_587

theorem node_5513 : Outcome ⟨2, 15, 1, 28⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 22⟩) (by decide) node_587

theorem node_5514 : Outcome ⟨2, 16, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 2⟩) (by decide) node_4802

theorem node_5515 : Outcome ⟨2, 16, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 2⟩) (by decide) node_4802

theorem node_5516 : Outcome ⟨2, 16, 0, 20⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 28⟩) (by decide) node_217

theorem node_5517 : Outcome ⟨2, 16, 0, 28⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 28⟩) (by decide) node_217

theorem node_5518 : Outcome ⟨3, 0, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 2⟩) (by decide) node_4719

theorem node_5519 : Outcome ⟨3, 0, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 2⟩) (by decide) node_4719

theorem node_5520 : Outcome ⟨3, 0, 15, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 2⟩) (by decide) node_4719

theorem node_5521 : Outcome ⟨3, 0, 15, 14⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 24⟩) (by decide) node_414

theorem node_5522 : Outcome ⟨3, 0, 15, 24⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 24⟩) (by decide) node_414

theorem node_5523 : Outcome ⟨3, 1, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 14, 2⟩, ⟨1, 1, 14, 4⟩, ⟨3, 0, 14, 2⟩, ⟨3, 1, 13, 2⟩, ⟨3, 1, 12, 4⟩]
  exact AllWinning.cons node_4726 (AllWinning.cons node_4004 (AllWinning.cons node_4809 (AllWinning.cons node_4814 (AllWinning.cons node_4101 (AllWinning.nil)))))

theorem node_5524 : Outcome ⟨3, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 6⟩) (by decide) node_3323

theorem node_5525 : Outcome ⟨3, 1, 14, 10⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 16⟩) (by decide) node_1326

theorem node_5526 : Outcome ⟨3, 1, 14, 14⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 16⟩) (by decide) node_1326

theorem node_5527 : Outcome ⟨3, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 2⟩) (by decide) node_4730

theorem node_5528 : Outcome ⟨3, 2, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 2⟩) (by decide) node_4730

theorem node_5529 : Outcome ⟨3, 2, 13, 14⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5530 : Outcome ⟨3, 2, 13, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5531 : Outcome ⟨3, 3, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 11, 2⟩) (by decide) node_4825

theorem node_5532 : Outcome ⟨3, 3, 12, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 24⟩) (by decide) node_437

theorem node_5533 : Outcome ⟨3, 4, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 11, 2⟩) (by decide) node_4825

theorem node_5534 : Outcome ⟨3, 5, 10, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5535 : Outcome ⟨3, 5, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5536 : Outcome ⟨3, 5, 10, 16⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 2⟩) (by decide) node_4743

theorem node_5537 : Outcome ⟨3, 6, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 9, 2⟩, ⟨1, 6, 9, 4⟩, ⟨3, 5, 9, 2⟩, ⟨3, 4, 9, 4⟩, ⟨3, 6, 8, 2⟩, ⟨3, 6, 7, 4⟩]
  exact AllWinning.cons node_4756 (AllWinning.cons node_4019 (AllWinning.cons node_4830 (AllWinning.cons node_4112 (AllWinning.cons node_4834 (AllWinning.cons node_4119 (AllWinning.nil))))))

theorem node_5538 : Outcome ⟨3, 6, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 9, 2⟩, ⟨1, 6, 9, 4⟩, ⟨0, 6, 9, 6⟩, ⟨3, 5, 9, 2⟩, ⟨3, 4, 9, 4⟩, ⟨3, 3, 9, 6⟩, ⟨3, 2, 9, 8⟩, ⟨3, 6, 8, 2⟩, ⟨3, 6, 7, 4⟩, ⟨3, 6, 6, 6⟩, ⟨3, 6, 5, 8⟩]
  exact AllWinning.cons node_4756 (AllWinning.cons node_4019 (AllWinning.cons node_3346 (AllWinning.cons node_4830 (AllWinning.cons node_4112 (AllWinning.cons node_3548 (AllWinning.cons node_3002 (AllWinning.cons node_4834 (AllWinning.cons node_4119 (AllWinning.cons node_3558 (AllWinning.cons node_3019 (AllWinning.nil)))))))))))

theorem node_5539 : Outcome ⟨3, 6, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 9, 2⟩, ⟨1, 6, 9, 4⟩, ⟨0, 6, 9, 6⟩, ⟨3, 5, 9, 2⟩, ⟨3, 4, 9, 4⟩, ⟨3, 3, 9, 6⟩, ⟨3, 2, 9, 8⟩, ⟨3, 1, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨3, 6, 8, 2⟩, ⟨3, 6, 7, 4⟩, ⟨3, 6, 6, 6⟩, ⟨3, 6, 5, 8⟩, ⟨3, 6, 4, 10⟩, ⟨3, 6, 3, 12⟩]
  exact AllWinning.cons node_4756 (AllWinning.cons node_4019 (AllWinning.cons node_3346 (AllWinning.cons node_4830 (AllWinning.cons node_4112 (AllWinning.cons node_3548 (AllWinning.cons node_3002 (AllWinning.cons node_2536 (AllWinning.cons node_2056 (AllWinning.cons node_4834 (AllWinning.cons node_4119 (AllWinning.cons node_3558 (AllWinning.cons node_3019 (AllWinning.cons node_2557 (AllWinning.cons node_2093 (AllWinning.nil)))))))))))))))

theorem node_5540 : Outcome ⟨3, 6, 9, 10⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 16⟩) (by decide) node_1357

theorem node_5541 : Outcome ⟨3, 6, 9, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 16⟩) (by decide) node_1357

theorem node_5542 : Outcome ⟨3, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨2, 7, 8, 2⟩) (by decide) node_4759

theorem node_5543 : Outcome ⟨3, 7, 8, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 8, 2⟩) (by decide) node_4759

theorem node_5544 : Outcome ⟨3, 7, 8, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5545 : Outcome ⟨3, 7, 8, 14⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5546 : Outcome ⟨3, 7, 8, 18⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5547 : Outcome ⟨3, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨2, 8, 7, 2⟩) (by decide) node_4764

theorem node_5548 : Outcome ⟨3, 8, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 8, 7, 2⟩) (by decide) node_4764

theorem node_5549 : Outcome ⟨3, 8, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5550 : Outcome ⟨3, 8, 7, 14⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5551 : Outcome ⟨3, 8, 7, 18⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5552 : Outcome ⟨3, 9, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 6, 2⟩, ⟨1, 9, 6, 4⟩, ⟨3, 8, 6, 2⟩, ⟨3, 7, 6, 4⟩, ⟨3, 9, 5, 2⟩, ⟨3, 9, 4, 4⟩]
  exact AllWinning.cons node_4769 (AllWinning.cons node_4030 (AllWinning.cons node_4844 (AllWinning.cons node_4124 (AllWinning.cons node_4849 (AllWinning.cons node_4133 (AllWinning.nil))))))

theorem node_5553 : Outcome ⟨3, 9, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 6, 2⟩, ⟨1, 9, 6, 4⟩, ⟨0, 9, 6, 6⟩, ⟨3, 8, 6, 2⟩, ⟨3, 7, 6, 4⟩, ⟨3, 6, 6, 6⟩, ⟨3, 5, 6, 8⟩, ⟨3, 9, 5, 2⟩, ⟨3, 9, 4, 4⟩, ⟨3, 9, 3, 6⟩, ⟨3, 9, 2, 8⟩]
  exact AllWinning.cons node_4769 (AllWinning.cons node_4030 (AllWinning.cons node_3356 (AllWinning.cons node_4844 (AllWinning.cons node_4124 (AllWinning.cons node_3558 (AllWinning.cons node_3015 (AllWinning.cons node_4849 (AllWinning.cons node_4133 (AllWinning.cons node_3569 (AllWinning.cons node_3031 (AllWinning.nil)))))))))))

theorem node_5554 : Outcome ⟨3, 9, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 6, 2⟩, ⟨1, 9, 6, 4⟩, ⟨0, 9, 6, 6⟩, ⟨3, 8, 6, 2⟩, ⟨3, 7, 6, 4⟩, ⟨3, 6, 6, 6⟩, ⟨3, 5, 6, 8⟩, ⟨3, 4, 6, 10⟩, ⟨3, 3, 6, 12⟩, ⟨3, 9, 5, 2⟩, ⟨3, 9, 4, 4⟩, ⟨3, 9, 3, 6⟩, ⟨3, 9, 2, 8⟩, ⟨3, 9, 1, 10⟩, ⟨3, 9, 0, 12⟩]
  exact AllWinning.cons node_4769 (AllWinning.cons node_4030 (AllWinning.cons node_3356 (AllWinning.cons node_4844 (AllWinning.cons node_4124 (AllWinning.cons node_3558 (AllWinning.cons node_3015 (AllWinning.cons node_2548 (AllWinning.cons node_2081 (AllWinning.cons node_4849 (AllWinning.cons node_4133 (AllWinning.cons node_3569 (AllWinning.cons node_3031 (AllWinning.cons node_2570 (AllWinning.cons node_2119 (AllWinning.nil)))))))))))))))

theorem node_5555 : Outcome ⟨3, 9, 6, 10⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 16⟩) (by decide) node_1326

theorem node_5556 : Outcome ⟨3, 9, 6, 12⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 16⟩) (by decide) node_1326

theorem node_5557 : Outcome ⟨3, 10, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5558 : Outcome ⟨3, 10, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5559 : Outcome ⟨3, 10, 5, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 2⟩) (by decide) node_4772

theorem node_5560 : Outcome ⟨3, 11, 4, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 3, 2⟩) (by decide) node_4856

theorem node_5561 : Outcome ⟨3, 12, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 3, 2⟩) (by decide) node_4856

theorem node_5562 : Outcome ⟨3, 12, 3, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 24⟩) (by decide) node_414

theorem node_5563 : Outcome ⟨3, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 2⟩) (by decide) node_4792

theorem node_5564 : Outcome ⟨3, 13, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 2⟩) (by decide) node_4792

theorem node_5565 : Outcome ⟨3, 13, 2, 14⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5566 : Outcome ⟨3, 13, 2, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5567 : Outcome ⟨3, 14, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 1, 2⟩, ⟨1, 14, 1, 4⟩, ⟨3, 13, 1, 2⟩, ⟨3, 12, 1, 4⟩, ⟨3, 14, 0, 2⟩]
  exact AllWinning.cons node_4798 (AllWinning.cons node_4047 (AllWinning.cons node_4863 (AllWinning.cons node_4143 (AllWinning.cons node_4869 (AllWinning.nil)))))

theorem node_5568 : Outcome ⟨3, 14, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 6⟩) (by decide) node_3375

theorem node_5569 : Outcome ⟨3, 14, 1, 10⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 16⟩) (by decide) node_1357

theorem node_5570 : Outcome ⟨3, 14, 1, 14⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 16⟩) (by decide) node_1357

theorem node_5571 : Outcome ⟨3, 15, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 2⟩) (by decide) node_4802

theorem node_5572 : Outcome ⟨3, 15, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 2⟩) (by decide) node_4802

theorem node_5573 : Outcome ⟨3, 15, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 2⟩) (by decide) node_4802

theorem node_5574 : Outcome ⟨3, 15, 0, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 24⟩) (by decide) node_437

theorem node_5575 : Outcome ⟨3, 15, 0, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 24⟩) (by decide) node_437

theorem node_5576 : Outcome ⟨4, 0, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 6⟩) (by decide) node_3386

theorem node_5577 : Outcome ⟨4, 0, 14, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 6⟩) (by decide) node_3386

theorem node_5578 : Outcome ⟨4, 0, 14, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 20⟩) (by decide) node_829

theorem node_5579 : Outcome ⟨4, 1, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 13, 2⟩, ⟨2, 1, 13, 4⟩, ⟨4, 0, 13, 2⟩, ⟨4, 1, 12, 2⟩, ⟨4, 1, 11, 4⟩]
  exact AllWinning.cons node_4814 (AllWinning.cons node_4056 (AllWinning.cons node_4874 (AllWinning.cons node_4878 (AllWinning.cons node_4156 (AllWinning.nil)))))

theorem node_5580 : Outcome ⟨4, 1, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 6⟩) (by decide) node_3394

theorem node_5581 : Outcome ⟨4, 1, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 6⟩) (by decide) node_3394

theorem node_5582 : Outcome ⟨4, 1, 13, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 6⟩) (by decide) node_3394

theorem node_5583 : Outcome ⟨4, 1, 13, 22⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 22⟩) (by decide) node_626

theorem node_5584 : Outcome ⟨4, 1, 13, 26⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 22⟩) (by decide) node_626

theorem node_5585 : Outcome ⟨4, 2, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 4⟩) (by decide) node_4151

theorem node_5586 : Outcome ⟨4, 2, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 6⟩) (by decide) node_3400

theorem node_5587 : Outcome ⟨4, 2, 12, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 6⟩) (by decide) node_3400

theorem node_5588 : Outcome ⟨4, 2, 12, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 22⟩) (by decide) node_644

theorem node_5589 : Outcome ⟨4, 2, 12, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 22⟩) (by decide) node_644

theorem node_5590 : Outcome ⟨4, 3, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 11, 2⟩) (by decide) node_4825

theorem node_5591 : Outcome ⟨4, 3, 11, 30⟩ true :=
  Outcome.win (q := ⟨3, 3, 11, 2⟩) (by decide) node_4825

theorem node_5592 : Outcome ⟨4, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 4⟩) (by decide) node_4166

theorem node_5593 : Outcome ⟨4, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 6⟩) (by decide) node_3409

theorem node_5594 : Outcome ⟨4, 4, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 6⟩) (by decide) node_3409

theorem node_5595 : Outcome ⟨4, 5, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 6⟩) (by decide) node_3414

theorem node_5596 : Outcome ⟨4, 5, 9, 6⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 6⟩) (by decide) node_3414

theorem node_5597 : Outcome ⟨4, 5, 9, 20⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 6⟩) (by decide) node_3414

theorem node_5598 : Outcome ⟨4, 5, 9, 22⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 6⟩) (by decide) node_3414

theorem node_5599 : Outcome ⟨4, 6, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 4⟩) (by decide) node_4166

theorem node_5600 : Outcome ⟨4, 6, 8, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 4⟩) (by decide) node_4166

theorem node_5601 : Outcome ⟨4, 6, 8, 22⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 4⟩) (by decide) node_4166

theorem node_5602 : Outcome ⟨4, 7, 7, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 4⟩) (by decide) node_4171

theorem node_5603 : Outcome ⟨4, 7, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 8⟩) (by decide) node_2852

theorem node_5604 : Outcome ⟨4, 7, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 8⟩) (by decide) node_2852

theorem node_5605 : Outcome ⟨4, 7, 7, 16⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 8⟩) (by decide) node_2852

theorem node_5606 : Outcome ⟨4, 8, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 4⟩) (by decide) node_4201

theorem node_5607 : Outcome ⟨4, 8, 6, 6⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 4⟩) (by decide) node_4201

theorem node_5608 : Outcome ⟨4, 8, 6, 22⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 4⟩) (by decide) node_4201

theorem node_5609 : Outcome ⟨4, 9, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5610 : Outcome ⟨4, 9, 5, 6⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5611 : Outcome ⟨4, 9, 5, 20⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5612 : Outcome ⟨4, 9, 5, 22⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 6⟩) (by decide) node_3438

theorem node_5613 : Outcome ⟨4, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 4⟩) (by decide) node_4201

theorem node_5614 : Outcome ⟨4, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 6⟩) (by decide) node_3452

theorem node_5615 : Outcome ⟨4, 10, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 6⟩) (by decide) node_3452

theorem node_5616 : Outcome ⟨4, 11, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 3, 2⟩) (by decide) node_4856

theorem node_5617 : Outcome ⟨4, 11, 3, 30⟩ true :=
  Outcome.win (q := ⟨3, 11, 3, 2⟩) (by decide) node_4856

theorem node_5618 : Outcome ⟨4, 12, 2, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 4⟩) (by decide) node_4215

theorem node_5619 : Outcome ⟨4, 12, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 6⟩) (by decide) node_3460

theorem node_5620 : Outcome ⟨4, 12, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 6⟩) (by decide) node_3460

theorem node_5621 : Outcome ⟨4, 12, 2, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 22⟩) (by decide) node_626

theorem node_5622 : Outcome ⟨4, 12, 2, 22⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 22⟩) (by decide) node_626

theorem node_5623 : Outcome ⟨4, 13, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 1, 2⟩, ⟨2, 13, 1, 4⟩, ⟨4, 12, 1, 2⟩, ⟨4, 11, 1, 4⟩, ⟨4, 13, 0, 2⟩]
  exact AllWinning.cons node_4863 (AllWinning.cons node_4093 (AllWinning.cons node_4913 (AllWinning.cons node_4210 (AllWinning.cons node_4918 (AllWinning.nil)))))

theorem node_5624 : Outcome ⟨4, 13, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 6⟩) (by decide) node_3466

theorem node_5625 : Outcome ⟨4, 13, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 6⟩) (by decide) node_3466

theorem node_5626 : Outcome ⟨4, 13, 1, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 22⟩) (by decide) node_644

theorem node_5627 : Outcome ⟨4, 13, 1, 26⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 22⟩) (by decide) node_644

theorem node_5628 : Outcome ⟨4, 14, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 6⟩) (by decide) node_3472

theorem node_5629 : Outcome ⟨4, 14, 0, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 6⟩) (by decide) node_3472

theorem node_5630 : Outcome ⟨4, 14, 0, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 20⟩) (by decide) node_855

theorem node_5631 : Outcome ⟨5, 0, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 13, 2⟩, ⟨3, 0, 13, 4⟩, ⟨5, 0, 12, 2⟩, ⟨5, 0, 11, 4⟩]
  exact AllWinning.cons node_4874 (AllWinning.cons node_4098 (AllWinning.cons node_4922 (AllWinning.cons node_4221 (AllWinning.nil))))

theorem node_5632 : Outcome ⟨5, 0, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 13, 2⟩, ⟨3, 0, 13, 4⟩, ⟨2, 0, 13, 6⟩, ⟨1, 0, 13, 8⟩, ⟨5, 0, 12, 2⟩, ⟨5, 0, 11, 4⟩, ⟨5, 0, 10, 6⟩, ⟨5, 0, 9, 8⟩]
  exact AllWinning.cons node_4874 (AllWinning.cons node_4098 (AllWinning.cons node_3479 (AllWinning.cons node_2891 (AllWinning.cons node_4922 (AllWinning.cons node_4221 (AllWinning.cons node_3631 (AllWinning.cons node_3085 (AllWinning.nil))))))))

theorem node_5633 : Outcome ⟨5, 0, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 10⟩) (by decide) node_2364

theorem node_5634 : Outcome ⟨5, 0, 13, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 16⟩) (by decide) node_1411

theorem node_5635 : Outcome ⟨5, 0, 13, 16⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 16⟩) (by decide) node_1411

theorem node_5636 : Outcome ⟨5, 1, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 12, 2⟩, ⟨3, 1, 12, 4⟩, ⟨5, 0, 12, 2⟩, ⟨5, 1, 11, 2⟩, ⟨5, 1, 10, 4⟩]
  exact AllWinning.cons node_4878 (AllWinning.cons node_4101 (AllWinning.cons node_4922 (AllWinning.cons node_4927 (AllWinning.cons node_4226 (AllWinning.nil)))))

theorem node_5637 : Outcome ⟨5, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 6⟩) (by decide) node_3483

theorem node_5638 : Outcome ⟨5, 1, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 6⟩) (by decide) node_3483

theorem node_5639 : Outcome ⟨5, 2, 11, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5640 : Outcome ⟨5, 2, 11, 8⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5641 : Outcome ⟨5, 3, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5642 : Outcome ⟨5, 3, 10, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5643 : Outcome ⟨5, 3, 10, 16⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5644 : Outcome ⟨5, 4, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 6⟩) (by decide) node_3495

theorem node_5645 : Outcome ⟨5, 4, 9, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 6⟩) (by decide) node_3495

theorem node_5646 : Outcome ⟨5, 4, 9, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 6⟩) (by decide) node_3495

theorem node_5647 : Outcome ⟨5, 4, 9, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 9, 6⟩) (by decide) node_3495

theorem node_5648 : Outcome ⟨5, 5, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 8, 2⟩, ⟨3, 5, 8, 4⟩, ⟨5, 4, 8, 2⟩, ⟨5, 3, 8, 4⟩, ⟨5, 5, 7, 2⟩, ⟨5, 5, 6, 4⟩]
  exact AllWinning.cons node_4892 (AllWinning.cons node_4115 (AllWinning.cons node_4946 (AllWinning.cons node_4232 (AllWinning.cons node_4950 (AllWinning.cons node_4249 (AllWinning.nil))))))

theorem node_5649 : Outcome ⟨5, 5, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 8, 2⟩, ⟨3, 5, 8, 4⟩, ⟨2, 5, 8, 6⟩, ⟨1, 5, 8, 8⟩, ⟨5, 4, 8, 2⟩, ⟨5, 3, 8, 4⟩, ⟨5, 2, 8, 6⟩, ⟨5, 1, 8, 8⟩, ⟨5, 5, 7, 2⟩, ⟨5, 5, 6, 4⟩, ⟨5, 5, 5, 6⟩, ⟨5, 5, 4, 8⟩]
  exact AllWinning.cons node_4892 (AllWinning.cons node_4115 (AllWinning.cons node_3500 (AllWinning.cons node_2907 (AllWinning.cons node_4946 (AllWinning.cons node_4232 (AllWinning.cons node_3647 (AllWinning.cons node_3088 (AllWinning.cons node_4950 (AllWinning.cons node_4249 (AllWinning.cons node_3659 (AllWinning.cons node_3106 (AllWinning.nil))))))))))))

theorem node_5650 : Outcome ⟨5, 5, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 8, 2⟩, ⟨3, 5, 8, 4⟩, ⟨2, 5, 8, 6⟩, ⟨1, 5, 8, 8⟩, ⟨0, 5, 8, 10⟩, ⟨5, 4, 8, 2⟩, ⟨5, 3, 8, 4⟩, ⟨5, 2, 8, 6⟩, ⟨5, 1, 8, 8⟩, ⟨5, 0, 8, 10⟩, ⟨5, 5, 7, 2⟩, ⟨5, 5, 6, 4⟩, ⟨5, 5, 5, 6⟩, ⟨5, 5, 4, 8⟩, ⟨5, 5, 3, 10⟩, ⟨5, 5, 2, 12⟩]
  exact AllWinning.cons node_4892 (AllWinning.cons node_4115 (AllWinning.cons node_3500 (AllWinning.cons node_2907 (AllWinning.cons node_2390 (AllWinning.cons node_4946 (AllWinning.cons node_4232 (AllWinning.cons node_3647 (AllWinning.cons node_3088 (AllWinning.cons node_2631 (AllWinning.cons node_4950 (AllWinning.cons node_4249 (AllWinning.cons node_3659 (AllWinning.cons node_3106 (AllWinning.cons node_2651 (AllWinning.cons node_2182 (AllWinning.nil))))))))))))))))

theorem node_5651 : Outcome ⟨5, 5, 8, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 16⟩) (by decide) node_1445

theorem node_5652 : Outcome ⟨5, 5, 8, 20⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 16⟩) (by decide) node_1445

theorem node_5653 : Outcome ⟨5, 6, 7, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 4⟩) (by decide) node_4237

theorem node_5654 : Outcome ⟨5, 6, 7, 6⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 4⟩) (by decide) node_4237

theorem node_5655 : Outcome ⟨5, 6, 7, 22⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 4⟩) (by decide) node_4237

theorem node_5656 : Outcome ⟨5, 7, 6, 2⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 4⟩) (by decide) node_4254

theorem node_5657 : Outcome ⟨5, 7, 6, 6⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 4⟩) (by decide) node_4254

theorem node_5658 : Outcome ⟨5, 7, 6, 22⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 4⟩) (by decide) node_4254

theorem node_5659 : Outcome ⟨5, 8, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 5, 2⟩, ⟨3, 8, 5, 4⟩, ⟨5, 7, 5, 2⟩, ⟨5, 6, 5, 4⟩, ⟨5, 8, 4, 2⟩, ⟨5, 8, 3, 4⟩]
  exact AllWinning.cons node_4900 (AllWinning.cons node_4129 (AllWinning.cons node_4956 (AllWinning.cons node_4251 (AllWinning.cons node_4960 (AllWinning.cons node_4266 (AllWinning.nil))))))

theorem node_5660 : Outcome ⟨5, 8, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 5, 2⟩, ⟨3, 8, 5, 4⟩, ⟨2, 8, 5, 6⟩, ⟨1, 8, 5, 8⟩, ⟨5, 7, 5, 2⟩, ⟨5, 6, 5, 4⟩, ⟨5, 5, 5, 6⟩, ⟨5, 4, 5, 8⟩, ⟨5, 8, 4, 2⟩, ⟨5, 8, 3, 4⟩, ⟨5, 8, 2, 6⟩, ⟨5, 8, 1, 8⟩]
  exact AllWinning.cons node_4900 (AllWinning.cons node_4129 (AllWinning.cons node_3512 (AllWinning.cons node_2919 (AllWinning.cons node_4956 (AllWinning.cons node_4251 (AllWinning.cons node_3659 (AllWinning.cons node_3102 (AllWinning.cons node_4960 (AllWinning.cons node_4266 (AllWinning.cons node_3669 (AllWinning.cons node_3118 (AllWinning.nil))))))))))))

theorem node_5661 : Outcome ⟨5, 8, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 5, 2⟩, ⟨3, 8, 5, 4⟩, ⟨2, 8, 5, 6⟩, ⟨1, 8, 5, 8⟩, ⟨0, 8, 5, 10⟩, ⟨5, 7, 5, 2⟩, ⟨5, 6, 5, 4⟩, ⟨5, 5, 5, 6⟩, ⟨5, 4, 5, 8⟩, ⟨5, 3, 5, 10⟩, ⟨5, 2, 5, 12⟩, ⟨5, 8, 4, 2⟩, ⟨5, 8, 3, 4⟩, ⟨5, 8, 2, 6⟩, ⟨5, 8, 1, 8⟩, ⟨5, 8, 0, 10⟩]
  exact AllWinning.cons node_4900 (AllWinning.cons node_4129 (AllWinning.cons node_3512 (AllWinning.cons node_2919 (AllWinning.cons node_2402 (AllWinning.cons node_4956 (AllWinning.cons node_4251 (AllWinning.cons node_3659 (AllWinning.cons node_3102 (AllWinning.cons node_2643 (AllWinning.cons node_2170 (AllWinning.cons node_4960 (AllWinning.cons node_4266 (AllWinning.cons node_3669 (AllWinning.cons node_3118 (AllWinning.cons node_2664 (AllWinning.nil))))))))))))))))

theorem node_5662 : Outcome ⟨5, 8, 5, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 16⟩) (by decide) node_1411

theorem node_5663 : Outcome ⟨5, 8, 5, 20⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 16⟩) (by decide) node_1411

theorem node_5664 : Outcome ⟨5, 9, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 6⟩) (by decide) node_3517

theorem node_5665 : Outcome ⟨5, 9, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 6⟩) (by decide) node_3517

theorem node_5666 : Outcome ⟨5, 9, 4, 20⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 6⟩) (by decide) node_3517

theorem node_5667 : Outcome ⟨5, 9, 4, 22⟩ true :=
  Outcome.win (q := ⟨2, 9, 4, 6⟩) (by decide) node_3517

theorem node_5668 : Outcome ⟨5, 10, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5669 : Outcome ⟨5, 10, 3, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5670 : Outcome ⟨5, 10, 3, 16⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5671 : Outcome ⟨5, 11, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5672 : Outcome ⟨5, 11, 2, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5673 : Outcome ⟨5, 12, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 1, 2⟩, ⟨3, 12, 1, 4⟩, ⟨5, 11, 1, 2⟩, ⟨5, 10, 1, 4⟩, ⟨5, 12, 0, 2⟩]
  exact AllWinning.cons node_4913 (AllWinning.cons node_4143 (AllWinning.cons node_4980 (AllWinning.cons node_4274 (AllWinning.cons node_4983 (AllWinning.nil)))))

theorem node_5674 : Outcome ⟨5, 12, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 6⟩) (by decide) node_3529

theorem node_5675 : Outcome ⟨5, 12, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 1, 6⟩) (by decide) node_3529

theorem node_5676 : Outcome ⟨5, 13, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 0, 2⟩, ⟨3, 13, 0, 4⟩, ⟨5, 12, 0, 2⟩, ⟨5, 11, 0, 4⟩]
  exact AllWinning.cons node_4918 (AllWinning.cons node_4147 (AllWinning.cons node_4983 (AllWinning.cons node_4278 (AllWinning.nil))))

theorem node_5677 : Outcome ⟨5, 13, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 0, 2⟩, ⟨3, 13, 0, 4⟩, ⟨2, 13, 0, 6⟩, ⟨1, 13, 0, 8⟩, ⟨5, 12, 0, 2⟩, ⟨5, 11, 0, 4⟩, ⟨5, 10, 0, 6⟩, ⟨5, 9, 0, 8⟩]
  exact AllWinning.cons node_4918 (AllWinning.cons node_4147 (AllWinning.cons node_3534 (AllWinning.cons node_2936 (AllWinning.cons node_4983 (AllWinning.cons node_4278 (AllWinning.cons node_3685 (AllWinning.cons node_3122 (AllWinning.nil))))))))

theorem node_5678 : Outcome ⟨5, 13, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 10⟩) (by decide) node_2428

theorem node_5679 : Outcome ⟨5, 13, 0, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 16⟩) (by decide) node_1445

theorem node_5680 : Outcome ⟨5, 13, 0, 16⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 16⟩) (by decide) node_1445

theorem node_5681 : Outcome ⟨6, 0, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 4⟩) (by decide) node_4151

theorem node_5682 : Outcome ⟨6, 0, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 4⟩) (by decide) node_4151

theorem node_5683 : Outcome ⟨6, 0, 12, 12⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 12⟩) (by decide) node_2196

theorem node_5684 : Outcome ⟨6, 0, 12, 14⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 12⟩) (by decide) node_2196

theorem node_5685 : Outcome ⟨6, 0, 12, 32⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 12⟩) (by decide) node_2196

theorem node_5686 : Outcome ⟨6, 1, 11, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 11, 2⟩) (by decide) node_4988

theorem node_5687 : Outcome ⟨6, 1, 11, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 11, 2⟩) (by decide) node_4988

theorem node_5688 : Outcome ⟨6, 1, 11, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 16⟩) (by decide) node_1462

theorem node_5689 : Outcome ⟨6, 2, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5690 : Outcome ⟨6, 2, 10, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5691 : Outcome ⟨6, 2, 10, 20⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 2⟩) (by decide) node_4930

theorem node_5692 : Outcome ⟨6, 3, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 9, 2⟩, ⟨4, 3, 9, 4⟩, ⟨6, 2, 9, 2⟩, ⟨6, 1, 9, 4⟩, ⟨6, 3, 8, 2⟩, ⟨6, 3, 7, 4⟩]
  exact AllWinning.cons node_4942 (AllWinning.cons node_4162 (AllWinning.cons node_4996 (AllWinning.cons node_4285 (AllWinning.cons node_4999 (AllWinning.cons node_4293 (AllWinning.nil))))))

theorem node_5693 : Outcome ⟨6, 3, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 9, 2⟩, ⟨4, 3, 9, 4⟩, ⟨3, 3, 9, 6⟩, ⟨2, 3, 9, 8⟩, ⟨6, 2, 9, 2⟩, ⟨6, 1, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨6, 3, 8, 2⟩, ⟨6, 3, 7, 4⟩, ⟨6, 3, 6, 6⟩, ⟨6, 3, 5, 8⟩]
  exact AllWinning.cons node_4942 (AllWinning.cons node_4162 (AllWinning.cons node_3548 (AllWinning.cons node_2950 (AllWinning.cons node_4996 (AllWinning.cons node_4285 (AllWinning.cons node_3689 (AllWinning.cons node_4999 (AllWinning.cons node_4293 (AllWinning.cons node_3701 (AllWinning.cons node_3138 (AllWinning.nil)))))))))))

theorem node_5694 : Outcome ⟨6, 3, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 9, 2⟩, ⟨4, 3, 9, 4⟩, ⟨3, 3, 9, 6⟩, ⟨2, 3, 9, 8⟩, ⟨1, 3, 9, 10⟩, ⟨0, 3, 9, 12⟩, ⟨6, 2, 9, 2⟩, ⟨6, 1, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨6, 3, 8, 2⟩, ⟨6, 3, 7, 4⟩, ⟨6, 3, 6, 6⟩, ⟨6, 3, 5, 8⟩, ⟨6, 3, 4, 10⟩, ⟨6, 3, 3, 12⟩]
  exact AllWinning.cons node_4942 (AllWinning.cons node_4162 (AllWinning.cons node_3548 (AllWinning.cons node_2950 (AllWinning.cons node_2444 (AllWinning.cons node_1879 (AllWinning.cons node_4996 (AllWinning.cons node_4285 (AllWinning.cons node_3689 (AllWinning.cons node_4999 (AllWinning.cons node_4293 (AllWinning.cons node_3701 (AllWinning.cons node_3138 (AllWinning.cons node_2677 (AllWinning.cons node_2214 (AllWinning.nil)))))))))))))))

theorem node_5695 : Outcome ⟨6, 3, 9, 10⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 16⟩) (by decide) node_1482

theorem node_5696 : Outcome ⟨6, 3, 9, 12⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 16⟩) (by decide) node_1482

theorem node_5697 : Outcome ⟨6, 4, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 4⟩) (by decide) node_4166

theorem node_5698 : Outcome ⟨6, 4, 8, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 4⟩) (by decide) node_4166

theorem node_5699 : Outcome ⟨6, 5, 7, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 4⟩) (by decide) node_4171

theorem node_5700 : Outcome ⟨6, 5, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 4⟩) (by decide) node_4171

theorem node_5701 : Outcome ⟨6, 5, 7, 22⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 4⟩) (by decide) node_4171

theorem node_5702 : Outcome ⟨6, 6, 6, 1⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 6, 2⟩, ⟨6, 5, 6, 2⟩, ⟨6, 6, 5, 2⟩]
  exact AllWinning.cons node_4954 (AllWinning.cons node_5006 (AllWinning.cons node_5009 (AllWinning.nil)))

theorem node_5703 : Outcome ⟨6, 6, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 6, 2⟩, ⟨4, 6, 6, 4⟩, ⟨6, 5, 6, 2⟩, ⟨6, 4, 6, 4⟩, ⟨6, 6, 5, 2⟩, ⟨6, 6, 4, 4⟩]
  exact AllWinning.cons node_4954 (AllWinning.cons node_4184 (AllWinning.cons node_5006 (AllWinning.cons node_4299 (AllWinning.cons node_5009 (AllWinning.cons node_4306 (AllWinning.nil))))))

theorem node_5704 : Outcome ⟨6, 6, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 6, 2⟩, ⟨4, 6, 6, 4⟩, ⟨3, 6, 6, 6⟩, ⟨2, 6, 6, 8⟩, ⟨6, 5, 6, 2⟩, ⟨6, 4, 6, 4⟩, ⟨6, 3, 6, 6⟩, ⟨6, 2, 6, 8⟩, ⟨6, 6, 5, 2⟩, ⟨6, 6, 4, 4⟩, ⟨6, 6, 3, 6⟩, ⟨6, 6, 2, 8⟩]
  exact AllWinning.cons node_4954 (AllWinning.cons node_4184 (AllWinning.cons node_3558 (AllWinning.cons node_2963 (AllWinning.cons node_5006 (AllWinning.cons node_4299 (AllWinning.cons node_3701 (AllWinning.cons node_3133 (AllWinning.cons node_5009 (AllWinning.cons node_4306 (AllWinning.cons node_3710 (AllWinning.cons node_3150 (AllWinning.nil))))))))))))

theorem node_5705 : Outcome ⟨6, 6, 6, 12⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 12⟩) (by decide) node_1894

theorem node_5706 : Outcome ⟨6, 6, 6, 28⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 12⟩) (by decide) node_1894

theorem node_5707 : Outcome ⟨6, 7, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 4⟩) (by decide) node_4188

theorem node_5708 : Outcome ⟨6, 7, 5, 6⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 4⟩) (by decide) node_4188

theorem node_5709 : Outcome ⟨6, 7, 5, 22⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 4⟩) (by decide) node_4188

theorem node_5710 : Outcome ⟨6, 8, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 4⟩) (by decide) node_4201

theorem node_5711 : Outcome ⟨6, 8, 4, 6⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 4⟩) (by decide) node_4201

theorem node_5712 : Outcome ⟨6, 8, 4, 22⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 4⟩) (by decide) node_4201

theorem node_5713 : Outcome ⟨6, 9, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 3, 2⟩, ⟨4, 9, 3, 4⟩, ⟨6, 8, 3, 2⟩, ⟨6, 7, 3, 4⟩, ⟨6, 9, 2, 2⟩, ⟨6, 9, 1, 4⟩]
  exact AllWinning.cons node_4964 (AllWinning.cons node_4205 (AllWinning.cons node_5014 (AllWinning.cons node_4311 (AllWinning.cons node_5019 (AllWinning.cons node_4320 (AllWinning.nil))))))

theorem node_5714 : Outcome ⟨6, 9, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 3, 2⟩, ⟨4, 9, 3, 4⟩, ⟨3, 9, 3, 6⟩, ⟨2, 9, 3, 8⟩, ⟨6, 8, 3, 2⟩, ⟨6, 7, 3, 4⟩, ⟨6, 6, 3, 6⟩, ⟨6, 5, 3, 8⟩, ⟨6, 9, 2, 2⟩, ⟨6, 9, 1, 4⟩, ⟨6, 9, 0, 6⟩]
  exact AllWinning.cons node_4964 (AllWinning.cons node_4205 (AllWinning.cons node_3569 (AllWinning.cons node_2976 (AllWinning.cons node_5014 (AllWinning.cons node_4311 (AllWinning.cons node_3710 (AllWinning.cons node_3145 (AllWinning.cons node_5019 (AllWinning.cons node_4320 (AllWinning.cons node_3724 (AllWinning.nil)))))))))))

theorem node_5715 : Outcome ⟨6, 9, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 3, 2⟩, ⟨4, 9, 3, 4⟩, ⟨3, 9, 3, 6⟩, ⟨2, 9, 3, 8⟩, ⟨1, 9, 3, 10⟩, ⟨0, 9, 3, 12⟩, ⟨6, 8, 3, 2⟩, ⟨6, 7, 3, 4⟩, ⟨6, 6, 3, 6⟩, ⟨6, 5, 3, 8⟩, ⟨6, 4, 3, 10⟩, ⟨6, 3, 3, 12⟩, ⟨6, 9, 2, 2⟩, ⟨6, 9, 1, 4⟩, ⟨6, 9, 0, 6⟩]
  exact AllWinning.cons node_4964 (AllWinning.cons node_4205 (AllWinning.cons node_3569 (AllWinning.cons node_2976 (AllWinning.cons node_2466 (AllWinning.cons node_1912 (AllWinning.cons node_5014 (AllWinning.cons node_4311 (AllWinning.cons node_3710 (AllWinning.cons node_3145 (AllWinning.cons node_2681 (AllWinning.cons node_2214 (AllWinning.cons node_5019 (AllWinning.cons node_4320 (AllWinning.cons node_3724 (AllWinning.nil)))))))))))))))

theorem node_5716 : Outcome ⟨6, 9, 3, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 16⟩) (by decide) node_1462

theorem node_5717 : Outcome ⟨6, 9, 3, 12⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 16⟩) (by decide) node_1462

theorem node_5718 : Outcome ⟨6, 10, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5719 : Outcome ⟨6, 10, 2, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5720 : Outcome ⟨6, 10, 2, 20⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 2⟩) (by decide) node_4968

theorem node_5721 : Outcome ⟨6, 11, 1, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 0, 2⟩) (by decide) node_5025

theorem node_5722 : Outcome ⟨6, 11, 1, 4⟩ true :=
  Outcome.win (q := ⟨6, 11, 0, 2⟩) (by decide) node_5025

theorem node_5723 : Outcome ⟨6, 11, 1, 10⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 16⟩) (by decide) node_1482

theorem node_5724 : Outcome ⟨6, 12, 0, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 4⟩) (by decide) node_4215

theorem node_5725 : Outcome ⟨6, 12, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 4⟩) (by decide) node_4215

theorem node_5726 : Outcome ⟨6, 12, 0, 12⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 12⟩) (by decide) node_2230

theorem node_5727 : Outcome ⟨6, 12, 0, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 12⟩) (by decide) node_2230

theorem node_5728 : Outcome ⟨6, 12, 0, 32⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 12⟩) (by decide) node_2230

theorem node_5729 : Outcome ⟨7, 0, 11, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 11, 2⟩) (by decide) node_4988

theorem node_5730 : Outcome ⟨7, 0, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 8⟩) (by decide) node_3164

theorem node_5731 : Outcome ⟨7, 0, 11, 18⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 8⟩) (by decide) node_3164

theorem node_5732 : Outcome ⟨7, 1, 10, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 10, 2⟩) (by decide) node_5030

theorem node_5733 : Outcome ⟨7, 1, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 10, 6⟩) (by decide) node_3590

theorem node_5734 : Outcome ⟨7, 1, 10, 14⟩ true :=
  Outcome.win (q := ⟨4, 1, 10, 6⟩) (by decide) node_3590

theorem node_5735 : Outcome ⟨7, 2, 9, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 9, 6⟩) (by decide) node_3595

theorem node_5736 : Outcome ⟨7, 2, 9, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5737 : Outcome ⟨7, 2, 9, 16⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5738 : Outcome ⟨7, 2, 9, 18⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5739 : Outcome ⟨7, 2, 9, 22⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5740 : Outcome ⟨7, 3, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 8, 2⟩) (by decide) node_5039

theorem node_5741 : Outcome ⟨7, 3, 8, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 8, 2⟩) (by decide) node_5039

theorem node_5742 : Outcome ⟨7, 3, 8, 6⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5743 : Outcome ⟨7, 3, 8, 14⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5744 : Outcome ⟨7, 3, 8, 18⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5745 : Outcome ⟨7, 4, 7, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 4⟩) (by decide) node_4237

theorem node_5746 : Outcome ⟨7, 4, 7, 4⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 8⟩) (by decide) node_3164

theorem node_5747 : Outcome ⟨7, 4, 7, 6⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 8⟩) (by decide) node_3164

theorem node_5748 : Outcome ⟨7, 4, 7, 16⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 8⟩) (by decide) node_3164

theorem node_5749 : Outcome ⟨7, 5, 6, 2⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 4⟩) (by decide) node_4359

theorem node_5750 : Outcome ⟨7, 5, 6, 6⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 4⟩) (by decide) node_4359

theorem node_5751 : Outcome ⟨7, 5, 6, 22⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 4⟩) (by decide) node_4359

theorem node_5752 : Outcome ⟨7, 6, 5, 2⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 4⟩) (by decide) node_4344

theorem node_5753 : Outcome ⟨7, 6, 5, 6⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 4⟩) (by decide) node_4344

theorem node_5754 : Outcome ⟨7, 6, 5, 22⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 4⟩) (by decide) node_4344

end RQ9F1
