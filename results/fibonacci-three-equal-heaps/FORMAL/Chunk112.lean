import Chunk111
set_option autoImplicit false
namespace RQ9F1

theorem node_23455 : Outcome ⟨4, 18, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 17, 2⟩, ⟨2, 18, 17, 4⟩, ⟨4, 17, 17, 2⟩, ⟨4, 16, 17, 4⟩, ⟨4, 18, 16, 2⟩, ⟨4, 18, 15, 4⟩]
  exact AllWinning.cons node_22982 (AllWinning.cons node_22419 (AllWinning.cons node_22991 (AllWinning.cons node_22443 (AllWinning.cons node_22993 (AllWinning.cons node_22447 (AllWinning.nil))))))

theorem node_23456 : Outcome ⟨4, 18, 17, 4⟩ true :=
  Outcome.win (q := ⟨4, 15, 17, 6⟩) (by decide) node_21859

theorem node_23457 : Outcome ⟨4, 19, 16, 2⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 4⟩) (by decide) node_22449

theorem node_23458 : Outcome ⟨4, 19, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 4⟩) (by decide) node_22449

theorem node_23459 : Outcome ⟨4, 20, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 20, 13, 4⟩) (by decide) node_22454

theorem node_23460 : Outcome ⟨4, 20, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 17, 15, 6⟩) (by decide) node_21864

theorem node_23461 : Outcome ⟨5, 14, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 20, 2⟩, ⟨3, 14, 20, 4⟩, ⟨5, 13, 20, 2⟩, ⟨5, 12, 20, 4⟩, ⟨5, 14, 19, 2⟩, ⟨5, 14, 18, 4⟩]
  exact AllWinning.cons node_22986 (AllWinning.cons node_22422 (AllWinning.cons node_22998 (AllWinning.cons node_22457 (AllWinning.cons node_22999 (AllWinning.cons node_22463 (AllWinning.nil))))))

theorem node_23462 : Outcome ⟨5, 15, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 19, 2⟩, ⟨3, 15, 19, 4⟩, ⟨5, 14, 19, 2⟩, ⟨5, 13, 19, 4⟩, ⟨5, 15, 18, 2⟩, ⟨5, 15, 17, 4⟩]
  exact AllWinning.cons node_22988 (AllWinning.cons node_22424 (AllWinning.cons node_22999 (AllWinning.cons node_22460 (AllWinning.cons node_23002 (AllWinning.cons node_22465 (AllWinning.nil))))))

theorem node_23463 : Outcome ⟨5, 15, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 19, 2⟩, ⟨3, 15, 19, 4⟩, ⟨2, 15, 19, 6⟩, ⟨1, 15, 19, 8⟩, ⟨5, 14, 19, 2⟩, ⟨5, 13, 19, 4⟩, ⟨5, 12, 19, 6⟩, ⟨5, 11, 19, 8⟩, ⟨5, 15, 18, 2⟩, ⟨5, 15, 17, 4⟩, ⟨5, 15, 16, 6⟩, ⟨5, 15, 15, 8⟩]
  exact AllWinning.cons node_22988 (AllWinning.cons node_22424 (AllWinning.cons node_21803 (AllWinning.cons node_21204 (AllWinning.cons node_22999 (AllWinning.cons node_22460 (AllWinning.cons node_21876 (AllWinning.cons node_21278 (AllWinning.cons node_23002 (AllWinning.cons node_22465 (AllWinning.cons node_21883 (AllWinning.cons node_21292 (AllWinning.nil))))))))))))

theorem node_23464 : Outcome ⟨5, 15, 19, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 10⟩) (by decide) node_20520

theorem node_23465 : Outcome ⟨5, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 12, 18, 8⟩) (by decide) node_21282

theorem node_23466 : Outcome ⟨5, 17, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 17, 2⟩, ⟨3, 17, 17, 4⟩, ⟨5, 16, 17, 2⟩, ⟨5, 15, 17, 4⟩, ⟨5, 17, 16, 2⟩, ⟨5, 17, 15, 4⟩]
  exact AllWinning.cons node_22991 (AllWinning.cons node_22426 (AllWinning.cons node_23005 (AllWinning.cons node_22465 (AllWinning.cons node_23007 (AllWinning.cons node_22470 (AllWinning.nil))))))

theorem node_23467 : Outcome ⟨5, 17, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 17, 2⟩, ⟨3, 17, 17, 4⟩, ⟨2, 17, 17, 6⟩, ⟨1, 17, 17, 8⟩, ⟨5, 16, 17, 2⟩, ⟨5, 15, 17, 4⟩, ⟨5, 14, 17, 6⟩, ⟨5, 13, 17, 8⟩, ⟨5, 17, 16, 2⟩, ⟨5, 17, 15, 4⟩, ⟨5, 17, 14, 6⟩, ⟨5, 17, 13, 8⟩]
  exact AllWinning.cons node_22991 (AllWinning.cons node_22426 (AllWinning.cons node_21812 (AllWinning.cons node_21209 (AllWinning.cons node_23005 (AllWinning.cons node_22465 (AllWinning.cons node_21880 (AllWinning.cons node_21287 (AllWinning.cons node_23007 (AllWinning.cons node_22470 (AllWinning.cons node_21888 (AllWinning.cons node_21298 (AllWinning.nil))))))))))))

theorem node_23468 : Outcome ⟨5, 17, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 17, 17, 10⟩) (by decide) node_20413

theorem node_23469 : Outcome ⟨5, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 12, 8⟩) (by decide) node_21302

theorem node_23470 : Outcome ⟨5, 19, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 15, 2⟩, ⟨3, 19, 15, 4⟩, ⟨5, 18, 15, 2⟩, ⟨5, 17, 15, 4⟩, ⟨5, 19, 14, 2⟩, ⟨5, 19, 13, 4⟩]
  exact AllWinning.cons node_22995 (AllWinning.cons node_22430 (AllWinning.cons node_23009 (AllWinning.cons node_22470 (AllWinning.cons node_23012 (AllWinning.cons node_22475 (AllWinning.nil))))))

theorem node_23471 : Outcome ⟨5, 19, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 15, 2⟩, ⟨3, 19, 15, 4⟩, ⟨2, 19, 15, 6⟩, ⟨1, 19, 15, 8⟩, ⟨5, 18, 15, 2⟩, ⟨5, 17, 15, 4⟩, ⟨5, 16, 15, 6⟩, ⟨5, 15, 15, 8⟩, ⟨5, 19, 14, 2⟩, ⟨5, 19, 13, 4⟩, ⟨5, 19, 12, 6⟩, ⟨5, 19, 11, 8⟩]
  exact AllWinning.cons node_22995 (AllWinning.cons node_22430 (AllWinning.cons node_21822 (AllWinning.cons node_21215 (AllWinning.cons node_23009 (AllWinning.cons node_22470 (AllWinning.cons node_21886 (AllWinning.cons node_21292 (AllWinning.cons node_23012 (AllWinning.cons node_22475 (AllWinning.cons node_21894 (AllWinning.cons node_21307 (AllWinning.nil))))))))))))

theorem node_23472 : Outcome ⟨5, 19, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 10⟩) (by decide) node_20542

theorem node_23473 : Outcome ⟨5, 20, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 14, 2⟩, ⟨3, 20, 14, 4⟩, ⟨5, 19, 14, 2⟩, ⟨5, 18, 14, 4⟩, ⟨5, 20, 13, 2⟩, ⟨5, 20, 12, 4⟩]
  exact AllWinning.cons node_22996 (AllWinning.cons node_22431 (AllWinning.cons node_23012 (AllWinning.cons node_22472 (AllWinning.cons node_23015 (AllWinning.cons node_22478 (AllWinning.nil))))))

theorem node_23474 : Outcome ⟨6, 13, 20, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 20, 4⟩) (by decide) node_22434

theorem node_23475 : Outcome ⟨6, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 4⟩) (by decide) node_22437

theorem node_23476 : Outcome ⟨6, 14, 19, 6⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 12⟩) (by decide) node_19875

theorem node_23477 : Outcome ⟨6, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 6⟩) (by decide) node_21828

theorem node_23478 : Outcome ⟨6, 15, 18, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 18, 10⟩) (by decide) node_20553

theorem node_23479 : Outcome ⟨6, 16, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 17, 2⟩, ⟨4, 16, 17, 4⟩, ⟨6, 15, 17, 2⟩, ⟨6, 14, 17, 4⟩, ⟨6, 16, 16, 2⟩, ⟨6, 16, 15, 4⟩]
  exact AllWinning.cons node_23005 (AllWinning.cons node_22443 (AllWinning.cons node_23023 (AllWinning.cons node_22487 (AllWinning.cons node_23025 (AllWinning.cons node_22492 (AllWinning.nil))))))

theorem node_23480 : Outcome ⟨6, 16, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 17, 2⟩, ⟨4, 16, 17, 4⟩, ⟨3, 16, 17, 6⟩, ⟨2, 16, 17, 8⟩, ⟨6, 15, 17, 2⟩, ⟨6, 14, 17, 4⟩, ⟨6, 13, 17, 6⟩, ⟨6, 12, 17, 8⟩, ⟨6, 16, 16, 2⟩, ⟨6, 16, 15, 4⟩, ⟨6, 16, 14, 6⟩, ⟨6, 16, 13, 8⟩]
  exact AllWinning.cons node_23005 (AllWinning.cons node_22443 (AllWinning.cons node_21834 (AllWinning.cons node_21226 (AllWinning.cons node_23023 (AllWinning.cons node_22487 (AllWinning.cons node_21906 (AllWinning.cons node_21315 (AllWinning.cons node_23025 (AllWinning.cons node_22492 (AllWinning.cons node_21916 (AllWinning.cons node_21327 (AllWinning.nil))))))))))))

theorem node_23481 : Outcome ⟨6, 16, 17, 6⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 10⟩) (by decide) node_20576

theorem node_23482 : Outcome ⟨6, 17, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 17, 16, 2⟩, ⟨4, 17, 16, 4⟩, ⟨6, 16, 16, 2⟩, ⟨6, 15, 16, 4⟩, ⟨6, 17, 15, 2⟩, ⟨6, 17, 14, 4⟩]
  exact AllWinning.cons node_23007 (AllWinning.cons node_22445 (AllWinning.cons node_23025 (AllWinning.cons node_22489 (AllWinning.cons node_23028 (AllWinning.cons node_22496 (AllWinning.nil))))))

theorem node_23483 : Outcome ⟨6, 17, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 17, 16, 2⟩, ⟨4, 17, 16, 4⟩, ⟨3, 17, 16, 6⟩, ⟨2, 17, 16, 8⟩, ⟨6, 16, 16, 2⟩, ⟨6, 15, 16, 4⟩, ⟨6, 14, 16, 6⟩, ⟨6, 13, 16, 8⟩, ⟨6, 17, 15, 2⟩, ⟨6, 17, 14, 4⟩, ⟨6, 17, 13, 6⟩, ⟨6, 17, 12, 8⟩]
  exact AllWinning.cons node_23007 (AllWinning.cons node_22445 (AllWinning.cons node_21837 (AllWinning.cons node_21230 (AllWinning.cons node_23025 (AllWinning.cons node_22489 (AllWinning.cons node_21910 (AllWinning.cons node_21318 (AllWinning.cons node_23028 (AllWinning.cons node_22496 (AllWinning.cons node_21919 (AllWinning.cons node_21330 (AllWinning.nil))))))))))))

theorem node_23484 : Outcome ⟨6, 17, 16, 6⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 10⟩) (by decide) node_20560

theorem node_23485 : Outcome ⟨6, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 6⟩) (by decide) node_21841

theorem node_23486 : Outcome ⟨6, 18, 15, 6⟩ true :=
  Outcome.win (q := ⟨6, 18, 10, 10⟩) (by decide) node_20585

theorem node_23487 : Outcome ⟨6, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 4⟩) (by decide) node_22449

theorem node_23488 : Outcome ⟨6, 19, 14, 6⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 12⟩) (by decide) node_19868

theorem node_23489 : Outcome ⟨6, 20, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 20, 13, 4⟩) (by decide) node_22454

theorem node_23490 : Outcome ⟨7, 12, 20, 2⟩ true :=
  Outcome.win (q := ⟨6, 12, 20, 2⟩) (by decide) node_23016

theorem node_23491 : Outcome ⟨7, 12, 20, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 10⟩) (by decide) node_20611

theorem node_23492 : Outcome ⟨7, 13, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 19, 2⟩) (by decide) node_23040

theorem node_23493 : Outcome ⟨7, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 18, 2⟩) (by decide) node_23020

theorem node_23494 : Outcome ⟨7, 14, 18, 4⟩ true :=
  Outcome.win (q := ⟨6, 14, 18, 2⟩) (by decide) node_23020

theorem node_23495 : Outcome ⟨7, 14, 18, 10⟩ true :=
  Outcome.win (q := ⟨6, 14, 18, 2⟩) (by decide) node_23020

theorem node_23496 : Outcome ⟨7, 16, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 16, 4⟩) (by decide) node_22467

theorem node_23497 : Outcome ⟨7, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨5, 16, 16, 4⟩) (by decide) node_22467

theorem node_23498 : Outcome ⟨7, 16, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 14⟩) (by decide) node_18818

theorem node_23499 : Outcome ⟨7, 16, 16, 12⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 14⟩) (by decide) node_18818

theorem node_23500 : Outcome ⟨7, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨6, 18, 14, 2⟩) (by decide) node_23030

theorem node_23501 : Outcome ⟨7, 18, 14, 4⟩ true :=
  Outcome.win (q := ⟨6, 18, 14, 2⟩) (by decide) node_23030

theorem node_23502 : Outcome ⟨7, 18, 14, 10⟩ true :=
  Outcome.win (q := ⟨6, 18, 14, 2⟩) (by decide) node_23030

theorem node_23503 : Outcome ⟨7, 19, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 13, 2⟩) (by decide) node_23055

theorem node_23504 : Outcome ⟨7, 20, 12, 2⟩ true :=
  Outcome.win (q := ⟨6, 20, 12, 2⟩) (by decide) node_23034

theorem node_23505 : Outcome ⟨7, 20, 12, 8⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 10⟩) (by decide) node_20622

theorem node_23506 : Outcome ⟨8, 11, 20, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 20, 2⟩) (by decide) node_23037

theorem node_23507 : Outcome ⟨8, 11, 20, 6⟩ true :=
  Outcome.win (q := ⟨8, 7, 20, 8⟩) (by decide) node_21364

theorem node_23508 : Outcome ⟨8, 12, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 19, 2⟩) (by decide) node_23040

theorem node_23509 : Outcome ⟨8, 12, 19, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 19, 2⟩) (by decide) node_23040

theorem node_23510 : Outcome ⟨8, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨7, 13, 18, 2⟩) (by decide) node_23043

theorem node_23511 : Outcome ⟨8, 13, 18, 10⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 10⟩) (by decide) node_20649

theorem node_23512 : Outcome ⟨8, 14, 17, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 4⟩) (by decide) node_22540

theorem node_23513 : Outcome ⟨8, 14, 17, 6⟩ true :=
  Outcome.win (q := ⟨3, 14, 17, 10⟩) (by decide) node_20473

theorem node_23514 : Outcome ⟨8, 15, 16, 2⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 4⟩) (by decide) node_22545

theorem node_23515 : Outcome ⟨8, 15, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 14⟩) (by decide) node_18850

theorem node_23516 : Outcome ⟨8, 16, 15, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 4⟩) (by decide) node_22540

theorem node_23517 : Outcome ⟨8, 16, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 14⟩) (by decide) node_18857

theorem node_23518 : Outcome ⟨8, 17, 14, 2⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 4⟩) (by decide) node_22545

theorem node_23519 : Outcome ⟨8, 17, 14, 6⟩ true :=
  Outcome.win (q := ⟨3, 17, 14, 10⟩) (by decide) node_20480

theorem node_23520 : Outcome ⟨8, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 13, 2⟩) (by decide) node_23055

theorem node_23521 : Outcome ⟨8, 18, 13, 10⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 10⟩) (by decide) node_20678

theorem node_23522 : Outcome ⟨8, 19, 12, 2⟩ true :=
  Outcome.win (q := ⟨7, 19, 12, 2⟩) (by decide) node_23059

theorem node_23523 : Outcome ⟨8, 19, 12, 8⟩ true :=
  Outcome.win (q := ⟨7, 19, 12, 2⟩) (by decide) node_23059

theorem node_23524 : Outcome ⟨8, 20, 11, 2⟩ true :=
  Outcome.win (q := ⟨7, 20, 11, 2⟩) (by decide) node_23062

theorem node_23525 : Outcome ⟨8, 20, 11, 6⟩ true :=
  Outcome.win (q := ⟨8, 20, 7, 8⟩) (by decide) node_21390

theorem node_23526 : Outcome ⟨9, 10, 20, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 2⟩) (by decide) node_23082

theorem node_23527 : Outcome ⟨9, 10, 20, 16⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 2⟩) (by decide) node_23082

theorem node_23528 : Outcome ⟨9, 11, 19, 2⟩ true :=
  Outcome.win (q := ⟨9, 11, 18, 2⟩) (by decide) node_23090

theorem node_23529 : Outcome ⟨9, 11, 19, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 12⟩) (by decide) node_19769

theorem node_23530 : Outcome ⟨9, 12, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 18, 2⟩) (by decide) node_23067

theorem node_23531 : Outcome ⟨9, 12, 18, 6⟩ true :=
  Outcome.win (q := ⟨5, 12, 18, 8⟩) (by decide) node_21282

theorem node_23532 : Outcome ⟨9, 12, 18, 10⟩ true :=
  Outcome.win (q := ⟨5, 12, 18, 8⟩) (by decide) node_21282

theorem node_23533 : Outcome ⟨9, 12, 18, 16⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 30⟩) (by decide) node_11602

theorem node_23534 : Outcome ⟨9, 13, 17, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 4⟩) (by decide) node_22571

theorem node_23535 : Outcome ⟨9, 13, 17, 6⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 4⟩) (by decide) node_22571

theorem node_23536 : Outcome ⟨9, 14, 16, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 4⟩) (by decide) node_22575

theorem node_23537 : Outcome ⟨9, 14, 16, 6⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 4⟩) (by decide) node_22575

theorem node_23538 : Outcome ⟨9, 15, 15, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 4⟩) (by decide) node_22571

theorem node_23539 : Outcome ⟨9, 15, 15, 6⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 4⟩) (by decide) node_22571

theorem node_23540 : Outcome ⟨9, 16, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 4⟩) (by decide) node_22575

theorem node_23541 : Outcome ⟨9, 16, 14, 6⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 4⟩) (by decide) node_22575

theorem node_23542 : Outcome ⟨9, 17, 13, 2⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 4⟩) (by decide) node_22580

theorem node_23543 : Outcome ⟨9, 17, 13, 6⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 4⟩) (by decide) node_22580

theorem node_23544 : Outcome ⟨9, 18, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 18, 12, 2⟩) (by decide) node_23077

theorem node_23545 : Outcome ⟨9, 18, 12, 6⟩ true :=
  Outcome.win (q := ⟨5, 18, 12, 8⟩) (by decide) node_21302

theorem node_23546 : Outcome ⟨9, 18, 12, 10⟩ true :=
  Outcome.win (q := ⟨5, 18, 12, 8⟩) (by decide) node_21302

theorem node_23547 : Outcome ⟨9, 18, 12, 16⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 30⟩) (by decide) node_11569

theorem node_23548 : Outcome ⟨9, 19, 11, 2⟩ true :=
  Outcome.win (q := ⟨9, 18, 11, 2⟩) (by decide) node_23107

theorem node_23549 : Outcome ⟨9, 19, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 12⟩) (by decide) node_19787

theorem node_23550 : Outcome ⟨9, 20, 10, 2⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 2⟩) (by decide) node_23112

theorem node_23551 : Outcome ⟨9, 20, 10, 16⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 2⟩) (by decide) node_23112

theorem node_23552 : Outcome ⟨10, 9, 20, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 2⟩) (by decide) node_23082

theorem node_23553 : Outcome ⟨10, 10, 19, 2⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 4⟩) (by decide) node_22597

theorem node_23554 : Outcome ⟨10, 11, 18, 2⟩ true :=
  Outcome.win (q := ⟨9, 11, 18, 2⟩) (by decide) node_23090

theorem node_23555 : Outcome ⟨10, 12, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 4⟩) (by decide) node_22597

theorem node_23556 : Outcome ⟨10, 12, 17, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 4⟩) (by decide) node_22597

theorem node_23557 : Outcome ⟨10, 13, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 12, 16, 2⟩) (by decide) node_23124

theorem node_23558 : Outcome ⟨10, 13, 16, 12⟩ true :=
  Outcome.win (q := ⟨10, 12, 16, 2⟩) (by decide) node_23124

theorem node_23559 : Outcome ⟨10, 14, 15, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 4⟩) (by decide) node_22540

theorem node_23560 : Outcome ⟨10, 14, 15, 6⟩ true :=
  Outcome.win (q := ⟨8, 14, 15, 4⟩) (by decide) node_22540

theorem node_23561 : Outcome ⟨10, 15, 14, 2⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 4⟩) (by decide) node_22545

theorem node_23562 : Outcome ⟨10, 15, 14, 6⟩ true :=
  Outcome.win (q := ⟨8, 15, 14, 4⟩) (by decide) node_22545

theorem node_23563 : Outcome ⟨10, 16, 13, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 12, 2⟩) (by decide) node_23133

theorem node_23564 : Outcome ⟨10, 16, 13, 12⟩ true :=
  Outcome.win (q := ⟨10, 16, 12, 2⟩) (by decide) node_23133

theorem node_23565 : Outcome ⟨10, 17, 12, 2⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 4⟩) (by decide) node_22616

theorem node_23566 : Outcome ⟨10, 17, 12, 6⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 4⟩) (by decide) node_22616

theorem node_23567 : Outcome ⟨10, 18, 11, 2⟩ true :=
  Outcome.win (q := ⟨9, 18, 11, 2⟩) (by decide) node_23107

theorem node_23568 : Outcome ⟨10, 19, 10, 2⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 4⟩) (by decide) node_22616

theorem node_23569 : Outcome ⟨10, 20, 9, 2⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 2⟩) (by decide) node_23112

theorem node_23570 : Outcome ⟨11, 8, 20, 2⟩ true :=
  Outcome.win (q := ⟨11, 7, 20, 2⟩) (by decide) node_23142

theorem node_23571 : Outcome ⟨11, 8, 20, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 20, 8⟩) (by decide) node_21338

theorem node_23572 : Outcome ⟨11, 9, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 18, 2⟩) (by decide) node_23145

theorem node_23573 : Outcome ⟨11, 9, 19, 6⟩ true :=
  Outcome.win (q := ⟨11, 3, 19, 12⟩) (by decide) node_20041

theorem node_23574 : Outcome ⟨11, 10, 18, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 18, 2⟩) (by decide) node_23145

theorem node_23575 : Outcome ⟨11, 11, 17, 6⟩ true :=
  Outcome.win (q := ⟨8, 11, 17, 6⟩) (by decide) node_21960

theorem node_23576 : Outcome ⟨11, 12, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 12, 16, 2⟩) (by decide) node_23124

theorem node_23577 : Outcome ⟨11, 12, 16, 8⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 10⟩) (by decide) node_20560

theorem node_23578 : Outcome ⟨11, 13, 15, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 4⟩) (by decide) node_22571

theorem node_23579 : Outcome ⟨11, 13, 15, 6⟩ true :=
  Outcome.win (q := ⟨9, 13, 15, 4⟩) (by decide) node_22571

theorem node_23580 : Outcome ⟨11, 14, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 4⟩) (by decide) node_22575

theorem node_23581 : Outcome ⟨11, 14, 14, 6⟩ true :=
  Outcome.win (q := ⟨9, 14, 14, 4⟩) (by decide) node_22575

theorem node_23582 : Outcome ⟨11, 15, 13, 2⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 4⟩) (by decide) node_22580

theorem node_23583 : Outcome ⟨11, 15, 13, 6⟩ true :=
  Outcome.win (q := ⟨9, 15, 13, 4⟩) (by decide) node_22580

theorem node_23584 : Outcome ⟨11, 16, 12, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 12, 2⟩) (by decide) node_23133

theorem node_23585 : Outcome ⟨11, 16, 12, 8⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 10⟩) (by decide) node_20576

theorem node_23586 : Outcome ⟨11, 17, 11, 6⟩ true :=
  Outcome.win (q := ⟨8, 17, 11, 6⟩) (by decide) node_21980

theorem node_23587 : Outcome ⟨11, 18, 10, 2⟩ true :=
  Outcome.win (q := ⟨11, 18, 9, 2⟩) (by decide) node_23167

theorem node_23588 : Outcome ⟨11, 19, 9, 2⟩ true :=
  Outcome.win (q := ⟨11, 18, 9, 2⟩) (by decide) node_23167

theorem node_23589 : Outcome ⟨11, 19, 9, 6⟩ true :=
  Outcome.win (q := ⟨11, 19, 3, 12⟩) (by decide) node_20082

theorem node_23590 : Outcome ⟨11, 20, 8, 2⟩ true :=
  Outcome.win (q := ⟨11, 20, 7, 2⟩) (by decide) node_23169

theorem node_23591 : Outcome ⟨11, 20, 8, 6⟩ true :=
  Outcome.win (q := ⟨7, 20, 8, 8⟩) (by decide) node_21358

theorem node_23592 : Outcome ⟨12, 7, 20, 2⟩ true :=
  Outcome.win (q := ⟨11, 7, 20, 2⟩) (by decide) node_23142

theorem node_23593 : Outcome ⟨12, 8, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 7, 19, 2⟩) (by decide) node_23173

theorem node_23594 : Outcome ⟨12, 8, 19, 8⟩ true :=
  Outcome.win (q := ⟨12, 7, 19, 2⟩) (by decide) node_23173

theorem node_23595 : Outcome ⟨12, 9, 18, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 18, 2⟩) (by decide) node_23145

theorem node_23596 : Outcome ⟨12, 9, 18, 6⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 8⟩) (by decide) node_21498

theorem node_23597 : Outcome ⟨12, 9, 18, 10⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 8⟩) (by decide) node_21498

theorem node_23598 : Outcome ⟨12, 10, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 4⟩) (by decide) node_22597

theorem node_23599 : Outcome ⟨12, 10, 17, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 4⟩) (by decide) node_22597

theorem node_23600 : Outcome ⟨12, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨11, 11, 16, 2⟩) (by decide) node_23149

theorem node_23601 : Outcome ⟨12, 11, 16, 8⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 10⟩) (by decide) node_20603

theorem node_23602 : Outcome ⟨12, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨11, 12, 15, 2⟩) (by decide) node_23152

theorem node_23603 : Outcome ⟨12, 12, 15, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 10⟩) (by decide) node_20611

theorem node_23604 : Outcome ⟨12, 13, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 12, 14, 2⟩) (by decide) node_23185

theorem node_23605 : Outcome ⟨12, 13, 14, 6⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 12⟩) (by decide) node_19868

theorem node_23606 : Outcome ⟨12, 13, 14, 10⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 20⟩) (by decide) node_16646

theorem node_23607 : Outcome ⟨12, 14, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 12, 2⟩) (by decide) node_23191

theorem node_23608 : Outcome ⟨12, 14, 13, 6⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 12⟩) (by decide) node_19875

theorem node_23609 : Outcome ⟨12, 14, 13, 10⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 20⟩) (by decide) node_16620

theorem node_23610 : Outcome ⟨12, 15, 12, 2⟩ true :=
  Outcome.win (q := ⟨11, 15, 12, 2⟩) (by decide) node_23159

theorem node_23611 : Outcome ⟨12, 15, 12, 8⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 10⟩) (by decide) node_20622

theorem node_23612 : Outcome ⟨12, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 11, 2⟩) (by decide) node_23162

theorem node_23613 : Outcome ⟨12, 16, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 10⟩) (by decide) node_20629

theorem node_23614 : Outcome ⟨12, 17, 10, 2⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 4⟩) (by decide) node_22616

theorem node_23615 : Outcome ⟨12, 17, 10, 6⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 4⟩) (by decide) node_22616

theorem node_23616 : Outcome ⟨12, 18, 9, 2⟩ true :=
  Outcome.win (q := ⟨11, 18, 9, 2⟩) (by decide) node_23167

theorem node_23617 : Outcome ⟨12, 18, 9, 10⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 8⟩) (by decide) node_21529

theorem node_23618 : Outcome ⟨12, 19, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 8, 2⟩) (by decide) node_23202

theorem node_23619 : Outcome ⟨12, 19, 8, 8⟩ true :=
  Outcome.win (q := ⟨12, 18, 8, 2⟩) (by decide) node_23202

theorem node_23620 : Outcome ⟨12, 20, 7, 2⟩ true :=
  Outcome.win (q := ⟨11, 20, 7, 2⟩) (by decide) node_23169

theorem node_23621 : Outcome ⟨13, 6, 20, 4⟩ true :=
  Outcome.win (q := ⟨13, 4, 20, 4⟩) (by decide) node_22694

theorem node_23622 : Outcome ⟨13, 6, 20, 18⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 14⟩) (by decide) node_19002

theorem node_23623 : Outcome ⟨13, 7, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 7, 19, 2⟩) (by decide) node_23173

theorem node_23624 : Outcome ⟨13, 8, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 18, 2⟩) (by decide) node_23175

theorem node_23625 : Outcome ⟨13, 8, 18, 10⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 10⟩) (by decide) node_20649

theorem node_23626 : Outcome ⟨13, 9, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 4⟩) (by decide) node_22707

theorem node_23627 : Outcome ⟨13, 9, 17, 6⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 4⟩) (by decide) node_22707

theorem node_23628 : Outcome ⟨13, 10, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 10, 16, 2⟩) (by decide) node_23180

theorem node_23629 : Outcome ⟨13, 10, 16, 12⟩ true :=
  Outcome.win (q := ⟨12, 10, 16, 2⟩) (by decide) node_23180

theorem node_23630 : Outcome ⟨13, 11, 15, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 4⟩) (by decide) node_22707

theorem node_23631 : Outcome ⟨13, 11, 15, 6⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 4⟩) (by decide) node_22707

theorem node_23632 : Outcome ⟨13, 12, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 12, 14, 2⟩) (by decide) node_23185

theorem node_23633 : Outcome ⟨13, 12, 14, 6⟩ true :=
  Outcome.win (q := ⟨13, 6, 14, 12⟩) (by decide) node_20143

theorem node_23634 : Outcome ⟨13, 12, 14, 10⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 20⟩) (by decide) node_16715

theorem node_23635 : Outcome ⟨13, 13, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 13, 2⟩, ⟨11, 13, 13, 4⟩, ⟨13, 12, 13, 2⟩, ⟨13, 11, 13, 4⟩, ⟨13, 13, 12, 2⟩, ⟨13, 13, 11, 4⟩]
  exact AllWinning.cons node_23189 (AllWinning.cons node_22638 (AllWinning.cons node_23225 (AllWinning.cons node_22714 (AllWinning.cons node_23228 (AllWinning.cons node_22720 (AllWinning.nil))))))

theorem node_23636 : Outcome ⟨13, 13, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 13, 2⟩, ⟨11, 13, 13, 4⟩, ⟨10, 13, 13, 6⟩, ⟨9, 13, 13, 8⟩, ⟨13, 12, 13, 2⟩, ⟨13, 11, 13, 4⟩, ⟨13, 10, 13, 6⟩, ⟨13, 9, 13, 8⟩, ⟨13, 13, 12, 2⟩, ⟨13, 13, 11, 4⟩, ⟨13, 13, 10, 6⟩, ⟨13, 13, 9, 8⟩]
  exact AllWinning.cons node_23189 (AllWinning.cons node_22638 (AllWinning.cons node_22030 (AllWinning.cons node_21409 (AllWinning.cons node_23225 (AllWinning.cons node_22714 (AllWinning.cons node_22148 (AllWinning.cons node_21555 (AllWinning.cons node_23228 (AllWinning.cons node_22720 (AllWinning.cons node_22158 (AllWinning.cons node_21561 (AllWinning.nil))))))))))))

theorem node_23637 : Outcome ⟨13, 13, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 13, 2⟩, ⟨11, 13, 13, 4⟩, ⟨10, 13, 13, 6⟩, ⟨9, 13, 13, 8⟩, ⟨8, 13, 13, 10⟩, ⟨7, 13, 13, 12⟩, ⟨13, 12, 13, 2⟩, ⟨13, 11, 13, 4⟩, ⟨13, 10, 13, 6⟩, ⟨13, 9, 13, 8⟩, ⟨13, 8, 13, 10⟩, ⟨13, 7, 13, 12⟩, ⟨13, 13, 12, 2⟩, ⟨13, 13, 11, 4⟩, ⟨13, 13, 10, 6⟩, ⟨13, 13, 9, 8⟩, ⟨13, 13, 8, 10⟩, ⟨13, 13, 7, 12⟩]
  exact AllWinning.cons node_23189 (AllWinning.cons node_22638 (AllWinning.cons node_22030 (AllWinning.cons node_21409 (AllWinning.cons node_20664 (AllWinning.cons node_19901 (AllWinning.cons node_23225 (AllWinning.cons node_22714 (AllWinning.cons node_22148 (AllWinning.cons node_21555 (AllWinning.cons node_20896 (AllWinning.cons node_20147 (AllWinning.cons node_23228 (AllWinning.cons node_22720 (AllWinning.cons node_22158 (AllWinning.cons node_21561 (AllWinning.cons node_20912 (AllWinning.cons node_20164 (AllWinning.nil))))))))))))))))))

theorem node_23638 : Outcome ⟨13, 13, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 13, 2⟩, ⟨11, 13, 13, 4⟩, ⟨10, 13, 13, 6⟩, ⟨9, 13, 13, 8⟩, ⟨8, 13, 13, 10⟩, ⟨7, 13, 13, 12⟩, ⟨6, 13, 13, 14⟩, ⟨5, 13, 13, 16⟩, ⟨13, 12, 13, 2⟩, ⟨13, 11, 13, 4⟩, ⟨13, 10, 13, 6⟩, ⟨13, 9, 13, 8⟩, ⟨13, 8, 13, 10⟩, ⟨13, 7, 13, 12⟩, ⟨13, 6, 13, 14⟩, ⟨13, 5, 13, 16⟩, ⟨13, 13, 12, 2⟩, ⟨13, 13, 11, 4⟩, ⟨13, 13, 10, 6⟩, ⟨13, 13, 9, 8⟩, ⟨13, 13, 8, 10⟩, ⟨13, 13, 7, 12⟩, ⟨13, 13, 6, 14⟩, ⟨13, 13, 5, 16⟩]
  exact AllWinning.cons node_23189 (AllWinning.cons node_22638 (AllWinning.cons node_22030 (AllWinning.cons node_21409 (AllWinning.cons node_20664 (AllWinning.cons node_19901 (AllWinning.cons node_19025 (AllWinning.cons node_18078 (AllWinning.cons node_23225 (AllWinning.cons node_22714 (AllWinning.cons node_22148 (AllWinning.cons node_21555 (AllWinning.cons node_20896 (AllWinning.cons node_20147 (AllWinning.cons node_19370 (AllWinning.cons node_18500 (AllWinning.cons node_23228 (AllWinning.cons node_22720 (AllWinning.cons node_22158 (AllWinning.cons node_21561 (AllWinning.cons node_20912 (AllWinning.cons node_20164 (AllWinning.cons node_19393 (AllWinning.cons node_18523 (AllWinning.nil))))))))))))))))))))))))

theorem node_23639 : Outcome ⟨13, 13, 13, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 13, 2⟩, ⟨11, 13, 13, 4⟩, ⟨10, 13, 13, 6⟩, ⟨9, 13, 13, 8⟩, ⟨8, 13, 13, 10⟩, ⟨7, 13, 13, 12⟩, ⟨6, 13, 13, 14⟩, ⟨5, 13, 13, 16⟩, ⟨4, 13, 13, 18⟩, ⟨3, 13, 13, 20⟩, ⟨13, 12, 13, 2⟩, ⟨13, 11, 13, 4⟩, ⟨13, 10, 13, 6⟩, ⟨13, 9, 13, 8⟩, ⟨13, 8, 13, 10⟩, ⟨13, 7, 13, 12⟩, ⟨13, 6, 13, 14⟩, ⟨13, 5, 13, 16⟩, ⟨13, 4, 13, 18⟩, ⟨13, 3, 13, 20⟩, ⟨13, 13, 12, 2⟩, ⟨13, 13, 11, 4⟩, ⟨13, 13, 10, 6⟩, ⟨13, 13, 9, 8⟩, ⟨13, 13, 8, 10⟩, ⟨13, 13, 7, 12⟩, ⟨13, 13, 6, 14⟩, ⟨13, 13, 5, 16⟩, ⟨13, 13, 4, 18⟩, ⟨13, 13, 3, 20⟩]
  exact AllWinning.cons node_23189 (AllWinning.cons node_22638 (AllWinning.cons node_22030 (AllWinning.cons node_21409 (AllWinning.cons node_20664 (AllWinning.cons node_19901 (AllWinning.cons node_19025 (AllWinning.cons node_18078 (AllWinning.cons node_17150 (AllWinning.cons node_16048 (AllWinning.cons node_23225 (AllWinning.cons node_22714 (AllWinning.cons node_22148 (AllWinning.cons node_21555 (AllWinning.cons node_20896 (AllWinning.cons node_20147 (AllWinning.cons node_19370 (AllWinning.cons node_18500 (AllWinning.cons node_17590 (AllWinning.cons node_16671 (AllWinning.cons node_23228 (AllWinning.cons node_22720 (AllWinning.cons node_22158 (AllWinning.cons node_21561 (AllWinning.cons node_20912 (AllWinning.cons node_20164 (AllWinning.cons node_19393 (AllWinning.cons node_18523 (AllWinning.cons node_17618 (AllWinning.cons node_16720 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_23640 : Outcome ⟨13, 13, 13, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 13, 13, 2⟩, ⟨11, 13, 13, 4⟩, ⟨10, 13, 13, 6⟩, ⟨9, 13, 13, 8⟩, ⟨8, 13, 13, 10⟩, ⟨7, 13, 13, 12⟩, ⟨6, 13, 13, 14⟩, ⟨5, 13, 13, 16⟩, ⟨4, 13, 13, 18⟩, ⟨3, 13, 13, 20⟩, ⟨2, 13, 13, 22⟩, ⟨1, 13, 13, 24⟩, ⟨13, 12, 13, 2⟩, ⟨13, 11, 13, 4⟩, ⟨13, 10, 13, 6⟩, ⟨13, 9, 13, 8⟩, ⟨13, 8, 13, 10⟩, ⟨13, 7, 13, 12⟩, ⟨13, 6, 13, 14⟩, ⟨13, 5, 13, 16⟩, ⟨13, 4, 13, 18⟩, ⟨13, 3, 13, 20⟩, ⟨13, 2, 13, 22⟩, ⟨13, 1, 13, 24⟩, ⟨13, 13, 12, 2⟩, ⟨13, 13, 11, 4⟩, ⟨13, 13, 10, 6⟩, ⟨13, 13, 9, 8⟩, ⟨13, 13, 8, 10⟩, ⟨13, 13, 7, 12⟩, ⟨13, 13, 6, 14⟩, ⟨13, 13, 5, 16⟩, ⟨13, 13, 4, 18⟩, ⟨13, 13, 3, 20⟩, ⟨13, 13, 2, 22⟩, ⟨13, 13, 1, 24⟩]
  exact AllWinning.cons node_23189 (AllWinning.cons node_22638 (AllWinning.cons node_22030 (AllWinning.cons node_21409 (AllWinning.cons node_20664 (AllWinning.cons node_19901 (AllWinning.cons node_19025 (AllWinning.cons node_18078 (AllWinning.cons node_17150 (AllWinning.cons node_16048 (AllWinning.cons node_15038 (AllWinning.cons node_14025 (AllWinning.cons node_23225 (AllWinning.cons node_22714 (AllWinning.cons node_22148 (AllWinning.cons node_21555 (AllWinning.cons node_20896 (AllWinning.cons node_20147 (AllWinning.cons node_19370 (AllWinning.cons node_18500 (AllWinning.cons node_17590 (AllWinning.cons node_16671 (AllWinning.cons node_15621 (AllWinning.cons node_14679 (AllWinning.cons node_23228 (AllWinning.cons node_22720 (AllWinning.cons node_22158 (AllWinning.cons node_21561 (AllWinning.cons node_20912 (AllWinning.cons node_20164 (AllWinning.cons node_19393 (AllWinning.cons node_18523 (AllWinning.cons node_17618 (AllWinning.cons node_16720 (AllWinning.cons node_15656 (AllWinning.cons node_14706 (AllWinning.nil))))))))))))))))))))))))))))))))))))

theorem node_23641 : Outcome ⟨13, 14, 12, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 12, 2⟩) (by decide) node_23191

theorem node_23642 : Outcome ⟨13, 14, 12, 6⟩ true :=
  Outcome.win (q := ⟨13, 14, 6, 12⟩) (by decide) node_20169

theorem node_23643 : Outcome ⟨13, 14, 12, 10⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 20⟩) (by decide) node_16680

theorem node_23644 : Outcome ⟨13, 15, 11, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 4⟩) (by decide) node_22726

theorem node_23645 : Outcome ⟨13, 15, 11, 6⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 4⟩) (by decide) node_22726

theorem node_23646 : Outcome ⟨13, 15, 11, 18⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 4⟩) (by decide) node_22726

theorem node_23647 : Outcome ⟨13, 16, 10, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 10, 2⟩) (by decide) node_23197

theorem node_23648 : Outcome ⟨13, 16, 10, 12⟩ true :=
  Outcome.win (q := ⟨12, 16, 10, 2⟩) (by decide) node_23197

theorem node_23649 : Outcome ⟨13, 17, 9, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 4⟩) (by decide) node_22726

theorem node_23650 : Outcome ⟨13, 17, 9, 6⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 4⟩) (by decide) node_22726

theorem node_23651 : Outcome ⟨13, 18, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 8, 2⟩) (by decide) node_23202

theorem node_23652 : Outcome ⟨13, 18, 8, 10⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 10⟩) (by decide) node_20678

theorem node_23653 : Outcome ⟨13, 19, 7, 2⟩ true :=
  Outcome.win (q := ⟨12, 19, 7, 2⟩) (by decide) node_23205

theorem node_23654 : Outcome ⟨13, 20, 6, 4⟩ true :=
  Outcome.win (q := ⟨13, 20, 4, 4⟩) (by decide) node_22739

theorem node_23655 : Outcome ⟨14, 5, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 5, 20, 2⟩, ⟨12, 5, 20, 4⟩, ⟨14, 4, 20, 2⟩, ⟨14, 3, 20, 4⟩, ⟨14, 5, 19, 2⟩, ⟨14, 5, 18, 4⟩]
  exact AllWinning.cons node_23209 (AllWinning.cons node_22654 (AllWinning.cons node_23247 (AllWinning.cons node_22741 (AllWinning.cons node_23248 (AllWinning.cons node_22746 (AllWinning.nil))))))

theorem node_23656 : Outcome ⟨14, 6, 19, 6⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 12⟩) (by decide) node_20204

theorem node_23657 : Outcome ⟨14, 7, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 7, 18, 2⟩) (by decide) node_23212

theorem node_23658 : Outcome ⟨14, 7, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 7, 18, 2⟩) (by decide) node_23212

theorem node_23659 : Outcome ⟨14, 7, 18, 10⟩ true :=
  Outcome.win (q := ⟨13, 7, 18, 2⟩) (by decide) node_23212

theorem node_23660 : Outcome ⟨14, 8, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 8, 15, 4⟩) (by decide) node_22754

theorem node_23661 : Outcome ⟨14, 8, 17, 6⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 10⟩) (by decide) node_20939

theorem node_23662 : Outcome ⟨14, 9, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 4⟩) (by decide) node_22759

theorem node_23663 : Outcome ⟨14, 9, 16, 6⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 4⟩) (by decide) node_22759

theorem node_23664 : Outcome ⟨14, 10, 15, 2⟩ true :=
  Outcome.win (q := ⟨14, 8, 15, 4⟩) (by decide) node_22754

theorem node_23665 : Outcome ⟨14, 10, 15, 6⟩ true :=
  Outcome.win (q := ⟨14, 8, 15, 4⟩) (by decide) node_22754

theorem node_23666 : Outcome ⟨14, 11, 14, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 4⟩) (by decide) node_22759

theorem node_23667 : Outcome ⟨14, 11, 14, 6⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 4⟩) (by decide) node_22759

theorem node_23668 : Outcome ⟨14, 12, 13, 2⟩ true :=
  Outcome.win (q := ⟨14, 12, 12, 2⟩) (by decide) node_23261

theorem node_23669 : Outcome ⟨14, 12, 13, 6⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 12⟩) (by decide) node_20204

theorem node_23670 : Outcome ⟨14, 12, 13, 10⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 20⟩) (by decide) node_16109

theorem node_23671 : Outcome ⟨14, 13, 12, 2⟩ true :=
  Outcome.win (q := ⟨14, 12, 12, 2⟩) (by decide) node_23261

theorem node_23672 : Outcome ⟨14, 13, 12, 6⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 12⟩) (by decide) node_20224

theorem node_23673 : Outcome ⟨14, 13, 12, 10⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 20⟩) (by decide) node_16119

theorem node_23674 : Outcome ⟨14, 14, 11, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 4⟩) (by decide) node_22776

theorem node_23675 : Outcome ⟨14, 14, 11, 6⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 4⟩) (by decide) node_22776

theorem node_23676 : Outcome ⟨14, 15, 10, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 8, 4⟩) (by decide) node_22781

theorem node_23677 : Outcome ⟨14, 15, 10, 6⟩ true :=
  Outcome.win (q := ⟨14, 15, 8, 4⟩) (by decide) node_22781

theorem node_23678 : Outcome ⟨14, 16, 9, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 4⟩) (by decide) node_22776

theorem node_23679 : Outcome ⟨14, 16, 9, 6⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 4⟩) (by decide) node_22776

theorem node_23680 : Outcome ⟨14, 17, 8, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 8, 4⟩) (by decide) node_22781

theorem node_23681 : Outcome ⟨14, 17, 8, 6⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 10⟩) (by decide) node_20976

theorem node_23682 : Outcome ⟨14, 18, 7, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 7, 2⟩) (by decide) node_23241

theorem node_23683 : Outcome ⟨14, 18, 7, 4⟩ true :=
  Outcome.win (q := ⟨13, 18, 7, 2⟩) (by decide) node_23241

theorem node_23684 : Outcome ⟨14, 18, 7, 10⟩ true :=
  Outcome.win (q := ⟨13, 18, 7, 2⟩) (by decide) node_23241

theorem node_23685 : Outcome ⟨14, 19, 6, 6⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 12⟩) (by decide) node_20224

theorem node_23686 : Outcome ⟨14, 20, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 20, 5, 2⟩, ⟨12, 20, 5, 4⟩, ⟨14, 19, 5, 2⟩, ⟨14, 18, 5, 4⟩, ⟨14, 20, 4, 2⟩, ⟨14, 20, 3, 4⟩]
  exact AllWinning.cons node_23246 (AllWinning.cons node_22692 (AllWinning.cons node_23275 (AllWinning.cons node_22789 (AllWinning.cons node_23277 (AllWinning.cons node_22796 (AllWinning.nil))))))

theorem node_23687 : Outcome ⟨15, 4, 20, 4⟩ true :=
  Outcome.win (q := ⟨15, 4, 17, 6⟩) (by decide) node_22229

theorem node_23688 : Outcome ⟨15, 5, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 5, 19, 2⟩, ⟨13, 5, 19, 4⟩, ⟨15, 4, 19, 2⟩, ⟨15, 3, 19, 4⟩, ⟨15, 5, 18, 2⟩, ⟨15, 5, 17, 4⟩]
  exact AllWinning.cons node_23248 (AllWinning.cons node_22697 (AllWinning.cons node_23279 (AllWinning.cons node_22799 (AllWinning.cons node_23280 (AllWinning.cons node_22801 (AllWinning.nil))))))

theorem node_23689 : Outcome ⟨15, 5, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 5, 19, 2⟩, ⟨13, 5, 19, 4⟩, ⟨12, 5, 19, 6⟩, ⟨11, 5, 19, 8⟩, ⟨15, 4, 19, 2⟩, ⟨15, 3, 19, 4⟩, ⟨15, 2, 19, 6⟩, ⟨15, 1, 19, 8⟩, ⟨15, 5, 18, 2⟩, ⟨15, 5, 17, 4⟩, ⟨15, 5, 16, 6⟩, ⟨15, 5, 15, 8⟩]
  exact AllWinning.cons node_23248 (AllWinning.cons node_22697 (AllWinning.cons node_22088 (AllWinning.cons node_21456 (AllWinning.cons node_23279 (AllWinning.cons node_22799 (AllWinning.cons node_22218 (AllWinning.cons node_21622 (AllWinning.cons node_23280 (AllWinning.cons node_22801 (AllWinning.cons node_22231 (AllWinning.cons node_21630 (AllWinning.nil))))))))))))

theorem node_23690 : Outcome ⟨15, 5, 19, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 10⟩) (by decide) node_20735

theorem node_23691 : Outcome ⟨15, 6, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 6⟩) (by decide) node_22221

theorem node_23692 : Outcome ⟨15, 6, 18, 6⟩ true :=
  Outcome.win (q := ⟨10, 6, 18, 10⟩) (by decide) node_20741

theorem node_23693 : Outcome ⟨15, 7, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 7, 17, 2⟩, ⟨13, 7, 17, 4⟩, ⟨15, 6, 17, 2⟩, ⟨15, 5, 17, 4⟩, ⟨15, 7, 16, 2⟩, ⟨15, 7, 15, 4⟩]
  exact AllWinning.cons node_23252 (AllWinning.cons node_22701 (AllWinning.cons node_23283 (AllWinning.cons node_22801 (AllWinning.cons node_23285 (AllWinning.cons node_22806 (AllWinning.nil))))))

theorem node_23694 : Outcome ⟨15, 8, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 8, 14, 4⟩) (by decide) node_22809

theorem node_23695 : Outcome ⟨15, 8, 16, 8⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 14⟩) (by decide) node_19463

theorem node_23696 : Outcome ⟨15, 9, 15, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 4⟩) (by decide) node_22707

theorem node_23697 : Outcome ⟨15, 9, 15, 6⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 4⟩) (by decide) node_22707

theorem node_23698 : Outcome ⟨15, 10, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 8, 14, 4⟩) (by decide) node_22809

theorem node_23699 : Outcome ⟨15, 10, 14, 6⟩ true :=
  Outcome.win (q := ⟨15, 8, 14, 4⟩) (by decide) node_22809

theorem node_23700 : Outcome ⟨15, 11, 13, 2⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 4⟩) (by decide) node_22814

theorem node_23701 : Outcome ⟨15, 11, 13, 6⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 4⟩) (by decide) node_22814

theorem node_23702 : Outcome ⟨15, 12, 12, 2⟩ true :=
  Outcome.win (q := ⟨14, 12, 12, 2⟩) (by decide) node_23261

theorem node_23703 : Outcome ⟨15, 12, 12, 8⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 10⟩) (by decide) node_21004

theorem node_23704 : Outcome ⟨15, 13, 11, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 4⟩) (by decide) node_22825

theorem node_23705 : Outcome ⟨15, 13, 11, 6⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 4⟩) (by decide) node_22825

theorem node_23706 : Outcome ⟨15, 14, 10, 2⟩ true :=
  Outcome.win (q := ⟨15, 14, 8, 4⟩) (by decide) node_22829

theorem node_23707 : Outcome ⟨15, 14, 10, 6⟩ true :=
  Outcome.win (q := ⟨15, 14, 8, 4⟩) (by decide) node_22829

theorem node_23708 : Outcome ⟨15, 15, 9, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 4⟩) (by decide) node_22726

theorem node_23709 : Outcome ⟨15, 16, 8, 2⟩ true :=
  Outcome.win (q := ⟨15, 14, 8, 4⟩) (by decide) node_22829

theorem node_23710 : Outcome ⟨15, 16, 8, 8⟩ true :=
  Outcome.win (q := ⟨15, 16, 1, 14⟩) (by decide) node_19521

theorem node_23711 : Outcome ⟨15, 17, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 17, 7, 2⟩, ⟨13, 17, 7, 4⟩, ⟨15, 16, 7, 2⟩, ⟨15, 15, 7, 4⟩, ⟨15, 17, 6, 2⟩, ⟨15, 17, 5, 4⟩]
  exact AllWinning.cons node_23271 (AllWinning.cons node_22733 (AllWinning.cons node_23304 (AllWinning.cons node_22833 (AllWinning.cons node_23307 (AllWinning.cons node_22839 (AllWinning.nil))))))

theorem node_23712 : Outcome ⟨15, 18, 6, 4⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 6⟩) (by decide) node_22268

theorem node_23713 : Outcome ⟨15, 19, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 19, 5, 2⟩, ⟨13, 19, 5, 4⟩, ⟨15, 18, 5, 2⟩, ⟨15, 17, 5, 4⟩, ⟨15, 19, 4, 2⟩, ⟨15, 19, 3, 4⟩]
  exact AllWinning.cons node_23275 (AllWinning.cons node_22737 (AllWinning.cons node_23309 (AllWinning.cons node_22839 (AllWinning.cons node_23311 (AllWinning.cons node_22842 (AllWinning.nil))))))

theorem node_23714 : Outcome ⟨15, 19, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 10⟩) (by decide) node_20778

theorem node_23715 : Outcome ⟨15, 20, 4, 4⟩ true :=
  Outcome.win (q := ⟨15, 17, 4, 6⟩) (by decide) node_22265

theorem node_23716 : Outcome ⟨16, 4, 19, 4⟩ true :=
  Outcome.win (q := ⟨14, 4, 19, 4⟩) (by decide) node_22742

theorem node_23717 : Outcome ⟨16, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 8⟩) (by decide) node_21498

theorem node_23718 : Outcome ⟨16, 6, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 17, 2⟩, ⟨14, 6, 17, 4⟩, ⟨16, 5, 17, 2⟩, ⟨16, 4, 17, 4⟩, ⟨16, 6, 16, 2⟩, ⟨16, 6, 15, 4⟩]
  exact AllWinning.cons node_23283 (AllWinning.cons node_22749 (AllWinning.cons node_23315 (AllWinning.cons node_22846 (AllWinning.cons node_23316 (AllWinning.cons node_22851 (AllWinning.nil))))))

theorem node_23719 : Outcome ⟨16, 6, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 17, 2⟩, ⟨14, 6, 17, 4⟩, ⟨13, 6, 17, 6⟩, ⟨12, 6, 17, 8⟩, ⟨16, 5, 17, 2⟩, ⟨16, 4, 17, 4⟩, ⟨16, 3, 17, 6⟩, ⟨16, 2, 17, 8⟩, ⟨16, 6, 16, 2⟩, ⟨16, 6, 15, 4⟩, ⟨16, 6, 14, 6⟩, ⟨16, 6, 13, 8⟩]
  exact AllWinning.cons node_23283 (AllWinning.cons node_22749 (AllWinning.cons node_22137 (AllWinning.cons node_21502 (AllWinning.cons node_23315 (AllWinning.cons node_22846 (AllWinning.cons node_22282 (AllWinning.cons node_21669 (AllWinning.cons node_23316 (AllWinning.cons node_22851 (AllWinning.cons node_22287 (AllWinning.cons node_21677 (AllWinning.nil))))))))))))

theorem node_23720 : Outcome ⟨16, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨16, 5, 16, 4⟩) (by decide) node_22848

theorem node_23721 : Outcome ⟨16, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨16, 5, 16, 4⟩) (by decide) node_22848

theorem node_23722 : Outcome ⟨16, 7, 16, 12⟩ true :=
  Outcome.win (q := ⟨16, 0, 16, 14⟩) (by decide) node_19533

theorem node_23723 : Outcome ⟨16, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨14, 8, 15, 4⟩) (by decide) node_22754

theorem node_23724 : Outcome ⟨16, 8, 15, 8⟩ true :=
  Outcome.win (q := ⟨16, 1, 15, 14⟩) (by decide) node_19538

theorem node_23725 : Outcome ⟨16, 9, 14, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 4⟩) (by decide) node_22759

theorem node_23726 : Outcome ⟨16, 10, 13, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 12, 2⟩) (by decide) node_23324

theorem node_23727 : Outcome ⟨16, 10, 13, 12⟩ true :=
  Outcome.win (q := ⟨16, 10, 12, 2⟩) (by decide) node_23324

theorem node_23728 : Outcome ⟨16, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨15, 11, 12, 2⟩) (by decide) node_23293

theorem node_23729 : Outcome ⟨16, 11, 12, 8⟩ true :=
  Outcome.win (q := ⟨16, 6, 12, 10⟩) (by decide) node_21058

theorem node_23730 : Outcome ⟨16, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨15, 12, 11, 2⟩) (by decide) node_23296

theorem node_23731 : Outcome ⟨16, 12, 11, 8⟩ true :=
  Outcome.win (q := ⟨16, 7, 11, 10⟩) (by decide) node_21065

theorem node_23732 : Outcome ⟨16, 13, 10, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 10, 2⟩) (by decide) node_23328

theorem node_23733 : Outcome ⟨16, 13, 10, 12⟩ true :=
  Outcome.win (q := ⟨16, 12, 10, 2⟩) (by decide) node_23328

theorem node_23734 : Outcome ⟨16, 14, 9, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 4⟩) (by decide) node_22776

theorem node_23735 : Outcome ⟨16, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 8, 4⟩) (by decide) node_22781

theorem node_23736 : Outcome ⟨16, 15, 8, 8⟩ true :=
  Outcome.win (q := ⟨16, 15, 1, 14⟩) (by decide) node_19576

theorem node_23737 : Outcome ⟨16, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 5, 4⟩) (by decide) node_22873

theorem node_23738 : Outcome ⟨16, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨16, 16, 5, 4⟩) (by decide) node_22873

theorem node_23739 : Outcome ⟨16, 16, 7, 12⟩ true :=
  Outcome.win (q := ⟨16, 16, 0, 14⟩) (by decide) node_19585

theorem node_23740 : Outcome ⟨16, 17, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 17, 6, 2⟩, ⟨14, 17, 6, 4⟩, ⟨16, 16, 6, 2⟩, ⟨16, 15, 6, 4⟩, ⟨16, 17, 5, 2⟩, ⟨16, 17, 4, 4⟩]
  exact AllWinning.cons node_23307 (AllWinning.cons node_22787 (AllWinning.cons node_23337 (AllWinning.cons node_22870 (AllWinning.cons node_23340 (AllWinning.cons node_22876 (AllWinning.nil))))))

theorem node_23741 : Outcome ⟨16, 17, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 17, 6, 2⟩, ⟨14, 17, 6, 4⟩, ⟨13, 17, 6, 6⟩, ⟨12, 17, 6, 8⟩, ⟨16, 16, 6, 2⟩, ⟨16, 15, 6, 4⟩, ⟨16, 14, 6, 6⟩, ⟨16, 13, 6, 8⟩, ⟨16, 17, 5, 2⟩, ⟨16, 17, 4, 4⟩, ⟨16, 17, 3, 6⟩, ⟨16, 17, 2, 8⟩]
  exact AllWinning.cons node_23307 (AllWinning.cons node_22787 (AllWinning.cons node_22168 (AllWinning.cons node_21525 (AllWinning.cons node_23337 (AllWinning.cons node_22870 (AllWinning.cons node_22306 (AllWinning.cons node_21689 (AllWinning.cons node_23340 (AllWinning.cons node_22876 (AllWinning.cons node_22312 (AllWinning.cons node_21698 (AllWinning.nil))))))))))))

theorem node_23742 : Outcome ⟨16, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 8⟩) (by decide) node_21529

theorem node_23743 : Outcome ⟨16, 19, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 19, 4, 4⟩) (by decide) node_22792

theorem node_23744 : Outcome ⟨17, 4, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 4, 18, 2⟩, ⟨15, 4, 18, 4⟩, ⟨17, 3, 18, 2⟩, ⟨17, 2, 18, 4⟩, ⟨17, 4, 17, 2⟩, ⟨17, 4, 16, 4⟩]
  exact AllWinning.cons node_23314 (AllWinning.cons node_22800 (AllWinning.cons node_23345 (AllWinning.cons node_22881 (AllWinning.cons node_23346 (AllWinning.cons node_22883 (AllWinning.nil))))))

theorem node_23745 : Outcome ⟨17, 5, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 5, 17, 2⟩, ⟨15, 5, 17, 4⟩, ⟨17, 4, 17, 2⟩, ⟨17, 3, 17, 4⟩, ⟨17, 5, 16, 2⟩, ⟨17, 5, 15, 4⟩]
  exact AllWinning.cons node_23315 (AllWinning.cons node_22801 (AllWinning.cons node_23346 (AllWinning.cons node_22882 (AllWinning.cons node_23348 (AllWinning.cons node_22885 (AllWinning.nil))))))

theorem node_23746 : Outcome ⟨17, 5, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 5, 17, 2⟩, ⟨15, 5, 17, 4⟩, ⟨14, 5, 17, 6⟩, ⟨13, 5, 17, 8⟩, ⟨17, 4, 17, 2⟩, ⟨17, 3, 17, 4⟩, ⟨17, 2, 17, 6⟩, ⟨17, 1, 17, 8⟩, ⟨17, 5, 16, 2⟩, ⟨17, 5, 15, 4⟩, ⟨17, 5, 14, 6⟩, ⟨17, 5, 13, 8⟩]
  exact AllWinning.cons node_23315 (AllWinning.cons node_22801 (AllWinning.cons node_22180 (AllWinning.cons node_21544 (AllWinning.cons node_23346 (AllWinning.cons node_22882 (AllWinning.cons node_22321 (AllWinning.cons node_21703 (AllWinning.cons node_23348 (AllWinning.cons node_22885 (AllWinning.cons node_22326 (AllWinning.cons node_21712 (AllWinning.nil))))))))))))

theorem node_23747 : Outcome ⟨17, 5, 17, 6⟩ true :=
  Outcome.win (q := ⟨17, 0, 17, 10⟩) (by decide) node_21098

theorem node_23748 : Outcome ⟨17, 6, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 16, 2⟩, ⟨15, 6, 16, 4⟩, ⟨17, 5, 16, 2⟩, ⟨17, 4, 16, 4⟩, ⟨17, 6, 15, 2⟩, ⟨17, 6, 14, 4⟩]
  exact AllWinning.cons node_23316 (AllWinning.cons node_22803 (AllWinning.cons node_23348 (AllWinning.cons node_22883 (AllWinning.cons node_23350 (AllWinning.cons node_22887 (AllWinning.nil))))))

theorem node_23749 : Outcome ⟨17, 6, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 16, 2⟩, ⟨15, 6, 16, 4⟩, ⟨14, 6, 16, 6⟩, ⟨13, 6, 16, 8⟩, ⟨17, 5, 16, 2⟩, ⟨17, 4, 16, 4⟩, ⟨17, 3, 16, 6⟩, ⟨17, 2, 16, 8⟩, ⟨17, 6, 15, 2⟩, ⟨17, 6, 14, 4⟩, ⟨17, 6, 13, 6⟩, ⟨17, 6, 12, 8⟩]
  exact AllWinning.cons node_23316 (AllWinning.cons node_22803 (AllWinning.cons node_22183 (AllWinning.cons node_21547 (AllWinning.cons node_23348 (AllWinning.cons node_22883 (AllWinning.cons node_22322 (AllWinning.cons node_21706 (AllWinning.cons node_23350 (AllWinning.cons node_22887 (AllWinning.cons node_22328 (AllWinning.cons node_21715 (AllWinning.nil))))))))))))

theorem node_23750 : Outcome ⟨17, 6, 16, 6⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 10⟩) (by decide) node_20834

theorem node_23751 : Outcome ⟨17, 8, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 8, 14, 4⟩) (by decide) node_22809

theorem node_23752 : Outcome ⟨17, 8, 14, 6⟩ true :=
  Outcome.win (q := ⟨17, 3, 14, 10⟩) (by decide) node_21105

theorem node_23753 : Outcome ⟨17, 9, 13, 6⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 4⟩) (by decide) node_22814

theorem node_23754 : Outcome ⟨17, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨17, 10, 10, 4⟩) (by decide) node_22893

theorem node_23755 : Outcome ⟨17, 10, 12, 6⟩ true :=
  Outcome.win (q := ⟨17, 10, 10, 4⟩) (by decide) node_22893

theorem node_23756 : Outcome ⟨17, 11, 11, 6⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 6⟩) (by decide) node_22333

theorem node_23757 : Outcome ⟨17, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨17, 10, 10, 4⟩) (by decide) node_22893

theorem node_23758 : Outcome ⟨17, 12, 10, 6⟩ true :=
  Outcome.win (q := ⟨17, 10, 10, 4⟩) (by decide) node_22893

theorem node_23759 : Outcome ⟨17, 13, 9, 6⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 4⟩) (by decide) node_22825

theorem node_23760 : Outcome ⟨17, 14, 8, 2⟩ true :=
  Outcome.win (q := ⟨15, 14, 8, 4⟩) (by decide) node_22829

theorem node_23761 : Outcome ⟨17, 14, 8, 6⟩ true :=
  Outcome.win (q := ⟨17, 14, 3, 10⟩) (by decide) node_21129

end RQ9F1
