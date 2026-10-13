import Chunk121
set_option autoImplicit false
namespace RQ9F1

theorem node_25621 : Outcome ⟨13, 17, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 17, 2⟩, ⟨11, 17, 17, 4⟩, ⟨10, 17, 17, 6⟩, ⟨9, 17, 17, 8⟩, ⟨13, 16, 17, 2⟩, ⟨13, 15, 17, 4⟩, ⟨13, 14, 17, 6⟩, ⟨13, 13, 17, 8⟩, ⟨13, 17, 16, 2⟩, ⟨13, 17, 15, 4⟩, ⟨13, 17, 14, 6⟩, ⟨13, 17, 13, 8⟩]
  exact AllWinning.cons node_25496 (AllWinning.cons node_25322 (AllWinning.cons node_25116 (AllWinning.cons node_24876 (AllWinning.cons node_25507 (AllWinning.cons node_25351 (AllWinning.cons node_25168 (AllWinning.cons node_24938 (AllWinning.cons node_25508 (AllWinning.cons node_25358 (AllWinning.cons node_25175 (AllWinning.cons node_24947 (AllWinning.nil))))))))))))

theorem node_25622 : Outcome ⟨13, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 4⟩) (by decide) node_25354

theorem node_25623 : Outcome ⟨13, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 19, 15, 2⟩) (by decide) node_25500

theorem node_25624 : Outcome ⟨13, 19, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 19, 15, 2⟩) (by decide) node_25500

theorem node_25625 : Outcome ⟨13, 19, 15, 8⟩ true :=
  Outcome.win (q := ⟨12, 19, 15, 2⟩) (by decide) node_25500

theorem node_25626 : Outcome ⟨13, 20, 14, 2⟩ true :=
  Outcome.win (q := ⟨13, 19, 14, 2⟩) (by decide) node_25512

theorem node_25627 : Outcome ⟨14, 13, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 13, 19, 2⟩) (by decide) node_25514

theorem node_25628 : Outcome ⟨14, 15, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 15, 18, 2⟩, ⟨12, 15, 18, 4⟩, ⟨14, 14, 18, 2⟩, ⟨14, 13, 18, 4⟩, ⟨14, 15, 17, 2⟩, ⟨14, 15, 16, 4⟩]
  exact AllWinning.cons node_25504 (AllWinning.cons node_25333 (AllWinning.cons node_25516 (AllWinning.cons node_25369 (AllWinning.cons node_25517 (AllWinning.cons node_25372 (AllWinning.nil))))))

theorem node_25629 : Outcome ⟨14, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨14, 12, 18, 6⟩) (by decide) node_25184

theorem node_25630 : Outcome ⟨14, 16, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 17, 2⟩, ⟨12, 16, 17, 4⟩, ⟨14, 15, 17, 2⟩, ⟨14, 14, 17, 4⟩, ⟨14, 16, 16, 2⟩, ⟨14, 16, 15, 4⟩]
  exact AllWinning.cons node_25507 (AllWinning.cons node_25335 (AllWinning.cons node_25517 (AllWinning.cons node_25371 (AllWinning.cons node_25518 (AllWinning.cons node_25373 (AllWinning.nil))))))

theorem node_25631 : Outcome ⟨14, 16, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 17, 2⟩, ⟨12, 16, 17, 4⟩, ⟨11, 16, 17, 6⟩, ⟨10, 16, 17, 8⟩, ⟨14, 15, 17, 2⟩, ⟨14, 14, 17, 4⟩, ⟨14, 13, 17, 6⟩, ⟨14, 12, 17, 8⟩, ⟨14, 16, 16, 2⟩, ⟨14, 16, 15, 4⟩, ⟨14, 16, 14, 6⟩, ⟨14, 16, 13, 8⟩]
  exact AllWinning.cons node_25507 (AllWinning.cons node_25335 (AllWinning.cons node_25133 (AllWinning.cons node_24892 (AllWinning.cons node_25517 (AllWinning.cons node_25371 (AllWinning.cons node_25188 (AllWinning.cons node_24957 (AllWinning.cons node_25518 (AllWinning.cons node_25373 (AllWinning.cons node_25193 (AllWinning.cons node_24963 (AllWinning.nil))))))))))))

theorem node_25632 : Outcome ⟨14, 16, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 17, 2⟩, ⟨12, 16, 17, 4⟩, ⟨11, 16, 17, 6⟩, ⟨10, 16, 17, 8⟩, ⟨9, 16, 17, 10⟩, ⟨8, 16, 17, 12⟩, ⟨14, 15, 17, 2⟩, ⟨14, 14, 17, 4⟩, ⟨14, 13, 17, 6⟩, ⟨14, 12, 17, 8⟩, ⟨14, 11, 17, 10⟩, ⟨14, 10, 17, 12⟩, ⟨14, 16, 16, 2⟩, ⟨14, 16, 15, 4⟩, ⟨14, 16, 14, 6⟩, ⟨14, 16, 13, 8⟩, ⟨14, 16, 12, 10⟩, ⟨14, 16, 11, 12⟩]
  exact AllWinning.cons node_25507 (AllWinning.cons node_25335 (AllWinning.cons node_25133 (AllWinning.cons node_24892 (AllWinning.cons node_24587 (AllWinning.cons node_24294 (AllWinning.cons node_25517 (AllWinning.cons node_25371 (AllWinning.cons node_25188 (AllWinning.cons node_24957 (AllWinning.cons node_24690 (AllWinning.cons node_24397 (AllWinning.cons node_25518 (AllWinning.cons node_25373 (AllWinning.cons node_25193 (AllWinning.cons node_24963 (AllWinning.cons node_24704 (AllWinning.cons node_24411 (AllWinning.nil))))))))))))))))))

theorem node_25633 : Outcome ⟨14, 17, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 16, 2⟩, ⟨12, 17, 16, 4⟩, ⟨14, 16, 16, 2⟩, ⟨14, 15, 16, 4⟩, ⟨14, 17, 15, 2⟩, ⟨14, 17, 14, 4⟩]
  exact AllWinning.cons node_25508 (AllWinning.cons node_25337 (AllWinning.cons node_25518 (AllWinning.cons node_25372 (AllWinning.cons node_25519 (AllWinning.cons node_25375 (AllWinning.nil))))))

theorem node_25634 : Outcome ⟨14, 17, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 16, 2⟩, ⟨12, 17, 16, 4⟩, ⟨11, 17, 16, 6⟩, ⟨10, 17, 16, 8⟩, ⟨14, 16, 16, 2⟩, ⟨14, 15, 16, 4⟩, ⟨14, 14, 16, 6⟩, ⟨14, 13, 16, 8⟩, ⟨14, 17, 15, 2⟩, ⟨14, 17, 14, 4⟩, ⟨14, 17, 13, 6⟩, ⟨14, 17, 12, 8⟩]
  exact AllWinning.cons node_25508 (AllWinning.cons node_25337 (AllWinning.cons node_25137 (AllWinning.cons node_24894 (AllWinning.cons node_25518 (AllWinning.cons node_25372 (AllWinning.cons node_25190 (AllWinning.cons node_24959 (AllWinning.cons node_25519 (AllWinning.cons node_25375 (AllWinning.cons node_25196 (AllWinning.cons node_24966 (AllWinning.nil))))))))))))

theorem node_25635 : Outcome ⟨14, 17, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 16, 2⟩, ⟨12, 17, 16, 4⟩, ⟨11, 17, 16, 6⟩, ⟨10, 17, 16, 8⟩, ⟨9, 17, 16, 10⟩, ⟨8, 17, 16, 12⟩, ⟨14, 16, 16, 2⟩, ⟨14, 15, 16, 4⟩, ⟨14, 14, 16, 6⟩, ⟨14, 13, 16, 8⟩, ⟨14, 12, 16, 10⟩, ⟨14, 11, 16, 12⟩, ⟨14, 17, 15, 2⟩, ⟨14, 17, 14, 4⟩, ⟨14, 17, 13, 6⟩, ⟨14, 17, 12, 8⟩, ⟨14, 17, 11, 10⟩, ⟨14, 17, 10, 12⟩]
  exact AllWinning.cons node_25508 (AllWinning.cons node_25337 (AllWinning.cons node_25137 (AllWinning.cons node_24894 (AllWinning.cons node_24592 (AllWinning.cons node_24296 (AllWinning.cons node_25518 (AllWinning.cons node_25372 (AllWinning.cons node_25190 (AllWinning.cons node_24959 (AllWinning.cons node_24693 (AllWinning.cons node_24400 (AllWinning.cons node_25519 (AllWinning.cons node_25375 (AllWinning.cons node_25196 (AllWinning.cons node_24966 (AllWinning.cons node_24708 (AllWinning.cons node_24413 (AllWinning.nil))))))))))))))))))

theorem node_25636 : Outcome ⟨14, 18, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 15, 2⟩, ⟨12, 18, 15, 4⟩, ⟨14, 17, 15, 2⟩, ⟨14, 16, 15, 4⟩, ⟨14, 18, 14, 2⟩, ⟨14, 18, 13, 4⟩]
  exact AllWinning.cons node_25509 (AllWinning.cons node_25340 (AllWinning.cons node_25519 (AllWinning.cons node_25373 (AllWinning.cons node_25520 (AllWinning.cons node_25377 (AllWinning.nil))))))

theorem node_25637 : Outcome ⟨14, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 18, 12, 6⟩) (by decide) node_25198

theorem node_25638 : Outcome ⟨14, 20, 13, 2⟩ true :=
  Outcome.win (q := ⟨14, 19, 13, 2⟩) (by decide) node_25521

theorem node_25639 : Outcome ⟨15, 12, 20, 2⟩ true :=
  Outcome.win (q := ⟨15, 11, 20, 2⟩) (by decide) node_25523

theorem node_25640 : Outcome ⟨15, 13, 19, 2⟩ true :=
  Outcome.win (q := ⟨14, 13, 19, 2⟩) (by decide) node_25514

theorem node_25641 : Outcome ⟨15, 13, 19, 4⟩ true :=
  Outcome.win (q := ⟨14, 13, 19, 2⟩) (by decide) node_25514

theorem node_25642 : Outcome ⟨15, 13, 19, 8⟩ true :=
  Outcome.win (q := ⟨14, 13, 19, 2⟩) (by decide) node_25514

theorem node_25643 : Outcome ⟨15, 14, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 18, 2⟩, ⟨13, 14, 18, 4⟩, ⟨15, 13, 18, 2⟩, ⟨15, 12, 18, 4⟩, ⟨15, 14, 17, 2⟩, ⟨15, 14, 16, 4⟩]
  exact AllWinning.cons node_25516 (AllWinning.cons node_25348 (AllWinning.cons node_25525 (AllWinning.cons node_25382 (AllWinning.cons node_25528 (AllWinning.cons node_25387 (AllWinning.nil))))))

theorem node_25644 : Outcome ⟨15, 14, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 18, 6⟩) (by decide) node_25148

theorem node_25645 : Outcome ⟨15, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 15, 4⟩) (by decide) node_25389

theorem node_25646 : Outcome ⟨15, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨15, 12, 16, 8⟩) (by decide) node_24976

theorem node_25647 : Outcome ⟨15, 16, 16, 8⟩ true :=
  Outcome.win (q := ⟨15, 12, 16, 8⟩) (by decide) node_24976

theorem node_25648 : Outcome ⟨15, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 15, 4⟩) (by decide) node_25389

theorem node_25649 : Outcome ⟨15, 18, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 14, 2⟩, ⟨13, 18, 14, 4⟩, ⟨15, 17, 14, 2⟩, ⟨15, 16, 14, 4⟩, ⟨15, 18, 13, 2⟩, ⟨15, 18, 12, 4⟩]
  exact AllWinning.cons node_25520 (AllWinning.cons node_25361 (AllWinning.cons node_25531 (AllWinning.cons node_25390 (AllWinning.cons node_25532 (AllWinning.cons node_25396 (AllWinning.nil))))))

theorem node_25650 : Outcome ⟨15, 18, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 14, 6⟩) (by decide) node_25157

theorem node_25651 : Outcome ⟨15, 19, 13, 2⟩ true :=
  Outcome.win (q := ⟨14, 19, 13, 2⟩) (by decide) node_25521

theorem node_25652 : Outcome ⟨15, 19, 13, 4⟩ true :=
  Outcome.win (q := ⟨14, 19, 13, 2⟩) (by decide) node_25521

theorem node_25653 : Outcome ⟨15, 19, 13, 8⟩ true :=
  Outcome.win (q := ⟨14, 19, 13, 2⟩) (by decide) node_25521

theorem node_25654 : Outcome ⟨15, 20, 12, 2⟩ true :=
  Outcome.win (q := ⟨15, 19, 12, 2⟩) (by decide) node_25535

theorem node_25655 : Outcome ⟨16, 12, 19, 8⟩ true :=
  Outcome.win (q := ⟨12, 12, 19, 8⟩) (by decide) node_24913

theorem node_25656 : Outcome ⟨16, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨16, 13, 16, 4⟩) (by decide) node_25405

theorem node_25657 : Outcome ⟨16, 14, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 14, 17, 2⟩, ⟨14, 14, 17, 4⟩, ⟨16, 13, 17, 2⟩, ⟨16, 12, 17, 4⟩, ⟨16, 14, 16, 2⟩, ⟨16, 14, 15, 4⟩]
  exact AllWinning.cons node_25528 (AllWinning.cons node_25371 (AllWinning.cons node_25542 (AllWinning.cons node_25403 (AllWinning.cons node_25543 (AllWinning.cons node_25408 (AllWinning.nil))))))

theorem node_25658 : Outcome ⟨16, 15, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 8⟩) (by decide) node_24920

theorem node_25659 : Outcome ⟨16, 15, 16, 8⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 8⟩) (by decide) node_24920

theorem node_25660 : Outcome ⟨16, 16, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 8⟩) (by decide) node_24923

theorem node_25661 : Outcome ⟨16, 16, 15, 8⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 8⟩) (by decide) node_24923

theorem node_25662 : Outcome ⟨16, 17, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 17, 14, 2⟩, ⟨14, 17, 14, 4⟩, ⟨16, 16, 14, 2⟩, ⟨16, 15, 14, 4⟩, ⟨16, 17, 13, 2⟩, ⟨16, 17, 12, 4⟩]
  exact AllWinning.cons node_25531 (AllWinning.cons node_25375 (AllWinning.cons node_25545 (AllWinning.cons node_25410 (AllWinning.cons node_25546 (AllWinning.cons node_25416 (AllWinning.nil))))))

theorem node_25663 : Outcome ⟨16, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨16, 16, 13, 4⟩) (by decide) node_25413

theorem node_25664 : Outcome ⟨16, 19, 12, 8⟩ true :=
  Outcome.win (q := ⟨12, 19, 12, 8⟩) (by decide) node_24929

theorem node_25665 : Outcome ⟨17, 11, 19, 4⟩ true :=
  Outcome.win (q := ⟨16, 11, 19, 2⟩) (by decide) node_25537

theorem node_25666 : Outcome ⟨17, 12, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 12, 18, 2⟩, ⟨15, 12, 18, 4⟩, ⟨17, 11, 18, 2⟩, ⟨17, 10, 18, 4⟩, ⟨17, 12, 17, 2⟩, ⟨17, 12, 16, 4⟩]
  exact AllWinning.cons node_25540 (AllWinning.cons node_25382 (AllWinning.cons node_25552 (AllWinning.cons node_25420 (AllWinning.cons node_25553 (AllWinning.cons node_25423 (AllWinning.nil))))))

theorem node_25667 : Outcome ⟨17, 13, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 17, 2⟩, ⟨15, 13, 17, 4⟩, ⟨17, 12, 17, 2⟩, ⟨17, 11, 17, 4⟩, ⟨17, 13, 16, 2⟩, ⟨17, 13, 15, 4⟩]
  exact AllWinning.cons node_25542 (AllWinning.cons node_25385 (AllWinning.cons node_25553 (AllWinning.cons node_25422 (AllWinning.cons node_25554 (AllWinning.cons node_25425 (AllWinning.nil))))))

theorem node_25668 : Outcome ⟨17, 13, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 17, 2⟩, ⟨15, 13, 17, 4⟩, ⟨14, 13, 17, 6⟩, ⟨13, 13, 17, 8⟩, ⟨17, 12, 17, 2⟩, ⟨17, 11, 17, 4⟩, ⟨17, 10, 17, 6⟩, ⟨17, 9, 17, 8⟩, ⟨17, 13, 16, 2⟩, ⟨17, 13, 15, 4⟩, ⟨17, 13, 14, 6⟩, ⟨17, 13, 13, 8⟩]
  exact AllWinning.cons node_25542 (AllWinning.cons node_25385 (AllWinning.cons node_25188 (AllWinning.cons node_24938 (AllWinning.cons node_25553 (AllWinning.cons node_25422 (AllWinning.cons node_25240 (AllWinning.cons node_25014 (AllWinning.cons node_25554 (AllWinning.cons node_25425 (AllWinning.cons node_25247 (AllWinning.cons node_25023 (AllWinning.nil))))))))))))

theorem node_25669 : Outcome ⟨17, 14, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 14, 16, 2⟩, ⟨15, 14, 16, 4⟩, ⟨17, 13, 16, 2⟩, ⟨17, 12, 16, 4⟩, ⟨17, 14, 15, 2⟩, ⟨17, 14, 14, 4⟩]
  exact AllWinning.cons node_25543 (AllWinning.cons node_25387 (AllWinning.cons node_25554 (AllWinning.cons node_25423 (AllWinning.cons node_25555 (AllWinning.cons node_25427 (AllWinning.nil))))))

theorem node_25670 : Outcome ⟨17, 14, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 14, 16, 2⟩, ⟨15, 14, 16, 4⟩, ⟨14, 14, 16, 6⟩, ⟨13, 14, 16, 8⟩, ⟨17, 13, 16, 2⟩, ⟨17, 12, 16, 4⟩, ⟨17, 11, 16, 6⟩, ⟨17, 10, 16, 8⟩, ⟨17, 14, 15, 2⟩, ⟨17, 14, 14, 4⟩, ⟨17, 14, 13, 6⟩, ⟨17, 14, 12, 8⟩]
  exact AllWinning.cons node_25543 (AllWinning.cons node_25387 (AllWinning.cons node_25190 (AllWinning.cons node_24940 (AllWinning.cons node_25554 (AllWinning.cons node_25423 (AllWinning.cons node_25243 (AllWinning.cons node_25016 (AllWinning.cons node_25555 (AllWinning.cons node_25427 (AllWinning.cons node_25250 (AllWinning.cons node_25026 (AllWinning.nil))))))))))))

theorem node_25671 : Outcome ⟨17, 16, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 16, 14, 2⟩, ⟨15, 16, 14, 4⟩, ⟨17, 15, 14, 2⟩, ⟨17, 14, 14, 4⟩, ⟨17, 16, 13, 2⟩, ⟨17, 16, 12, 4⟩]
  exact AllWinning.cons node_25545 (AllWinning.cons node_25390 (AllWinning.cons node_25556 (AllWinning.cons node_25427 (AllWinning.cons node_25557 (AllWinning.cons node_25429 (AllWinning.nil))))))

theorem node_25672 : Outcome ⟨17, 16, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 16, 14, 2⟩, ⟨15, 16, 14, 4⟩, ⟨14, 16, 14, 6⟩, ⟨13, 16, 14, 8⟩, ⟨17, 15, 14, 2⟩, ⟨17, 14, 14, 4⟩, ⟨17, 13, 14, 6⟩, ⟨17, 12, 14, 8⟩, ⟨17, 16, 13, 2⟩, ⟨17, 16, 12, 4⟩, ⟨17, 16, 11, 6⟩, ⟨17, 16, 10, 8⟩]
  exact AllWinning.cons node_25545 (AllWinning.cons node_25390 (AllWinning.cons node_25193 (AllWinning.cons node_24944 (AllWinning.cons node_25556 (AllWinning.cons node_25427 (AllWinning.cons node_25247 (AllWinning.cons node_25020 (AllWinning.cons node_25557 (AllWinning.cons node_25429 (AllWinning.cons node_25253 (AllWinning.cons node_25029 (AllWinning.nil))))))))))))

theorem node_25673 : Outcome ⟨17, 17, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 13, 2⟩, ⟨15, 17, 13, 4⟩, ⟨17, 16, 13, 2⟩, ⟨17, 15, 13, 4⟩, ⟨17, 17, 12, 2⟩, ⟨17, 17, 11, 4⟩]
  exact AllWinning.cons node_25546 (AllWinning.cons node_25393 (AllWinning.cons node_25557 (AllWinning.cons node_25428 (AllWinning.cons node_25558 (AllWinning.cons node_25431 (AllWinning.nil))))))

theorem node_25674 : Outcome ⟨17, 17, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 13, 2⟩, ⟨15, 17, 13, 4⟩, ⟨14, 17, 13, 6⟩, ⟨13, 17, 13, 8⟩, ⟨17, 16, 13, 2⟩, ⟨17, 15, 13, 4⟩, ⟨17, 14, 13, 6⟩, ⟨17, 13, 13, 8⟩, ⟨17, 17, 12, 2⟩, ⟨17, 17, 11, 4⟩, ⟨17, 17, 10, 6⟩, ⟨17, 17, 9, 8⟩]
  exact AllWinning.cons node_25546 (AllWinning.cons node_25393 (AllWinning.cons node_25196 (AllWinning.cons node_24947 (AllWinning.cons node_25557 (AllWinning.cons node_25428 (AllWinning.cons node_25250 (AllWinning.cons node_25023 (AllWinning.cons node_25558 (AllWinning.cons node_25431 (AllWinning.cons node_25255 (AllWinning.cons node_25031 (AllWinning.nil))))))))))))

theorem node_25675 : Outcome ⟨17, 18, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 18, 12, 2⟩, ⟨15, 18, 12, 4⟩, ⟨17, 17, 12, 2⟩, ⟨17, 16, 12, 4⟩, ⟨17, 18, 11, 2⟩, ⟨17, 18, 10, 4⟩]
  exact AllWinning.cons node_25547 (AllWinning.cons node_25396 (AllWinning.cons node_25558 (AllWinning.cons node_25429 (AllWinning.cons node_25559 (AllWinning.cons node_25432 (AllWinning.nil))))))

theorem node_25676 : Outcome ⟨17, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨16, 19, 11, 2⟩) (by decide) node_25549

theorem node_25677 : Outcome ⟨18, 11, 18, 4⟩ true :=
  Outcome.win (q := ⟨18, 8, 18, 6⟩) (by decide) node_25259

theorem node_25678 : Outcome ⟨18, 13, 16, 4⟩ true :=
  Outcome.win (q := ⟨16, 13, 16, 4⟩) (by decide) node_25405

theorem node_25679 : Outcome ⟨18, 14, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 14, 15, 2⟩, ⟨16, 14, 15, 4⟩, ⟨18, 13, 15, 2⟩, ⟨18, 12, 15, 4⟩, ⟨18, 14, 14, 2⟩, ⟨18, 14, 13, 4⟩]
  exact AllWinning.cons node_25555 (AllWinning.cons node_25408 (AllWinning.cons node_25560 (AllWinning.cons node_25436 (AllWinning.cons node_25561 (AllWinning.cons node_25438 (AllWinning.nil))))))

theorem node_25680 : Outcome ⟨18, 14, 15, 4⟩ true :=
  Outcome.win (q := ⟨18, 14, 12, 6⟩) (by decide) node_25265

theorem node_25681 : Outcome ⟨18, 15, 14, 4⟩ true :=
  Outcome.win (q := ⟨18, 12, 14, 6⟩) (by decide) node_25262

theorem node_25682 : Outcome ⟨18, 16, 13, 4⟩ true :=
  Outcome.win (q := ⟨16, 16, 13, 4⟩) (by decide) node_25413

theorem node_25683 : Outcome ⟨18, 18, 11, 4⟩ true :=
  Outcome.win (q := ⟨18, 18, 8, 6⟩) (by decide) node_25268

theorem node_25684 : Outcome ⟨19, 9, 19, 4⟩ true :=
  Outcome.win (q := ⟨19, 8, 19, 2⟩) (by decide) node_25562

theorem node_25685 : Outcome ⟨19, 9, 19, 8⟩ true :=
  Outcome.win (q := ⟨19, 8, 19, 2⟩) (by decide) node_25562

theorem node_25686 : Outcome ⟨19, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨19, 11, 16, 2⟩) (by decide) node_25565

theorem node_25687 : Outcome ⟨19, 12, 16, 8⟩ true :=
  Outcome.win (q := ⟨15, 12, 16, 8⟩) (by decide) node_24976

theorem node_25688 : Outcome ⟨19, 13, 15, 8⟩ true :=
  Outcome.win (q := ⟨19, 12, 15, 2⟩) (by decide) node_25568

theorem node_25689 : Outcome ⟨19, 15, 13, 8⟩ true :=
  Outcome.win (q := ⟨19, 14, 13, 2⟩) (by decide) node_25570

theorem node_25690 : Outcome ⟨19, 16, 12, 8⟩ true :=
  Outcome.win (q := ⟨15, 16, 12, 8⟩) (by decide) node_24985

theorem node_25691 : Outcome ⟨19, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨19, 16, 11, 2⟩) (by decide) node_25572

theorem node_25692 : Outcome ⟨19, 19, 9, 4⟩ true :=
  Outcome.win (q := ⟨19, 19, 8, 2⟩) (by decide) node_25575

theorem node_25693 : Outcome ⟨19, 19, 9, 8⟩ true :=
  Outcome.win (q := ⟨19, 19, 8, 2⟩) (by decide) node_25575

theorem node_25694 : Outcome ⟨8, 20, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 20, 20, 2⟩, ⟨6, 20, 20, 4⟩, ⟨5, 20, 20, 6⟩, ⟨4, 20, 20, 8⟩, ⟨8, 19, 20, 2⟩, ⟨8, 18, 20, 4⟩, ⟨8, 17, 20, 6⟩, ⟨8, 16, 20, 8⟩, ⟨8, 20, 19, 2⟩, ⟨8, 20, 18, 4⟩, ⟨8, 20, 17, 6⟩, ⟨8, 20, 16, 8⟩]
  exact AllWinning.cons node_25578 (AllWinning.cons node_25455 (AllWinning.cons node_25283 (AllWinning.cons node_25062 (AllWinning.cons node_25579 (AllWinning.cons node_25457 (AllWinning.cons node_25288 (AllWinning.cons node_25080 (AllWinning.cons node_25581 (AllWinning.cons node_25462 (AllWinning.cons node_25294 (AllWinning.cons node_25091 (AllWinning.nil))))))))))))

theorem node_25695 : Outcome ⟨8, 20, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 20, 20, 2⟩, ⟨6, 20, 20, 4⟩, ⟨5, 20, 20, 6⟩, ⟨4, 20, 20, 8⟩, ⟨3, 20, 20, 10⟩, ⟨2, 20, 20, 12⟩, ⟨8, 19, 20, 2⟩, ⟨8, 18, 20, 4⟩, ⟨8, 17, 20, 6⟩, ⟨8, 16, 20, 8⟩, ⟨8, 15, 20, 10⟩, ⟨8, 14, 20, 12⟩, ⟨8, 20, 19, 2⟩, ⟨8, 20, 18, 4⟩, ⟨8, 20, 17, 6⟩, ⟨8, 20, 16, 8⟩, ⟨8, 20, 15, 10⟩, ⟨8, 20, 14, 12⟩]
  exact AllWinning.cons node_25578 (AllWinning.cons node_25455 (AllWinning.cons node_25283 (AllWinning.cons node_25062 (AllWinning.cons node_24826 (AllWinning.cons node_24527 (AllWinning.cons node_25579 (AllWinning.cons node_25457 (AllWinning.cons node_25288 (AllWinning.cons node_25080 (AllWinning.cons node_24859 (AllWinning.cons node_24560 (AllWinning.cons node_25581 (AllWinning.cons node_25462 (AllWinning.cons node_25294 (AllWinning.cons node_25091 (AllWinning.cons node_24867 (AllWinning.cons node_24573 (AllWinning.nil))))))))))))))))))

theorem node_25696 : Outcome ⟨9, 19, 20, 6⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 2⟩) (by decide) node_25583

theorem node_25697 : Outcome ⟨9, 20, 19, 6⟩ true :=
  Outcome.win (q := ⟨9, 20, 18, 2⟩) (by decide) node_25589

theorem node_25698 : Outcome ⟨10, 18, 20, 8⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 2⟩) (by decide) node_25583

theorem node_25699 : Outcome ⟨10, 19, 19, 2⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 4⟩) (by decide) node_25459

theorem node_25700 : Outcome ⟨10, 19, 19, 6⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 4⟩) (by decide) node_25459

theorem node_25701 : Outcome ⟨10, 20, 18, 8⟩ true :=
  Outcome.win (q := ⟨9, 20, 18, 2⟩) (by decide) node_25589

theorem node_25702 : Outcome ⟨11, 17, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 20, 2⟩, ⟨9, 17, 20, 4⟩, ⟨11, 16, 20, 2⟩, ⟨11, 15, 20, 4⟩, ⟨11, 17, 19, 2⟩, ⟨11, 17, 18, 4⟩]
  exact AllWinning.cons node_25593 (AllWinning.cons node_25464 (AllWinning.cons node_25597 (AllWinning.cons node_25478 (AllWinning.cons node_25598 (AllWinning.cons node_25483 (AllWinning.nil))))))

theorem node_25703 : Outcome ⟨11, 17, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 20, 2⟩, ⟨9, 17, 20, 4⟩, ⟨8, 17, 20, 6⟩, ⟨7, 17, 20, 8⟩, ⟨11, 16, 20, 2⟩, ⟨11, 15, 20, 4⟩, ⟨11, 14, 20, 6⟩, ⟨11, 13, 20, 8⟩, ⟨11, 17, 19, 2⟩, ⟨11, 17, 18, 4⟩, ⟨11, 17, 17, 6⟩, ⟨11, 17, 16, 8⟩]
  exact AllWinning.cons node_25593 (AllWinning.cons node_25464 (AllWinning.cons node_25288 (AllWinning.cons node_25069 (AllWinning.cons node_25597 (AllWinning.cons node_25478 (AllWinning.cons node_25316 (AllWinning.cons node_25127 (AllWinning.cons node_25598 (AllWinning.cons node_25483 (AllWinning.cons node_25323 (AllWinning.cons node_25138 (AllWinning.nil))))))))))))

theorem node_25704 : Outcome ⟨11, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 19, 4⟩) (by decide) node_25480

theorem node_25705 : Outcome ⟨11, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 16, 4⟩) (by decide) node_25487

theorem node_25706 : Outcome ⟨11, 20, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 20, 17, 2⟩, ⟨9, 20, 17, 4⟩, ⟨11, 19, 17, 2⟩, ⟨11, 18, 17, 4⟩, ⟨11, 20, 16, 2⟩, ⟨11, 20, 15, 4⟩]
  exact AllWinning.cons node_25596 (AllWinning.cons node_25468 (AllWinning.cons node_25602 (AllWinning.cons node_25485 (AllWinning.cons node_25604 (AllWinning.cons node_25490 (AllWinning.nil))))))

theorem node_25707 : Outcome ⟨11, 20, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 20, 17, 2⟩, ⟨9, 20, 17, 4⟩, ⟨8, 20, 17, 6⟩, ⟨7, 20, 17, 8⟩, ⟨11, 19, 17, 2⟩, ⟨11, 18, 17, 4⟩, ⟨11, 17, 17, 6⟩, ⟨11, 16, 17, 8⟩, ⟨11, 20, 16, 2⟩, ⟨11, 20, 15, 4⟩, ⟨11, 20, 14, 6⟩, ⟨11, 20, 13, 8⟩]
  exact AllWinning.cons node_25596 (AllWinning.cons node_25468 (AllWinning.cons node_25294 (AllWinning.cons node_25077 (AllWinning.cons node_25602 (AllWinning.cons node_25485 (AllWinning.cons node_25323 (AllWinning.cons node_25134 (AllWinning.cons node_25604 (AllWinning.cons node_25490 (AllWinning.cons node_25329 (AllWinning.cons node_25143 (AllWinning.nil))))))))))))

theorem node_25708 : Outcome ⟨12, 16, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 20, 2⟩, ⟨10, 16, 20, 4⟩, ⟨9, 16, 20, 6⟩, ⟨8, 16, 20, 8⟩, ⟨12, 15, 20, 2⟩, ⟨12, 14, 20, 4⟩, ⟨12, 13, 20, 6⟩, ⟨12, 12, 20, 8⟩, ⟨12, 16, 19, 2⟩, ⟨12, 16, 18, 4⟩, ⟨12, 16, 17, 6⟩, ⟨12, 16, 16, 8⟩]
  exact AllWinning.cons node_25597 (AllWinning.cons node_25470 (AllWinning.cons node_25297 (AllWinning.cons node_25080 (AllWinning.cons node_25605 (AllWinning.cons node_25491 (AllWinning.cons node_25330 (AllWinning.cons node_25144 (AllWinning.cons node_25607 (AllWinning.cons node_25494 (AllWinning.cons node_25336 (AllWinning.cons node_25152 (AllWinning.nil))))))))))))

theorem node_25709 : Outcome ⟨12, 16, 20, 6⟩ true :=
  Outcome.win (q := ⟨7, 16, 20, 10⟩) (by decide) node_24845

theorem node_25710 : Outcome ⟨12, 17, 19, 4⟩ true :=
  Outcome.win (q := ⟨12, 17, 18, 2⟩) (by decide) node_25609

theorem node_25711 : Outcome ⟨12, 17, 19, 6⟩ true :=
  Outcome.win (q := ⟨12, 12, 19, 10⟩) (by decide) node_24914

theorem node_25712 : Outcome ⟨12, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨11, 18, 18, 2⟩) (by decide) node_25600

theorem node_25713 : Outcome ⟨12, 19, 17, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 17, 2⟩) (by decide) node_25610

theorem node_25714 : Outcome ⟨12, 19, 17, 6⟩ true :=
  Outcome.win (q := ⟨12, 19, 12, 10⟩) (by decide) node_24930

theorem node_25715 : Outcome ⟨12, 20, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 20, 16, 2⟩, ⟨10, 20, 16, 4⟩, ⟨9, 20, 16, 6⟩, ⟨8, 20, 16, 8⟩, ⟨12, 19, 16, 2⟩, ⟨12, 18, 16, 4⟩, ⟨12, 17, 16, 6⟩, ⟨12, 16, 16, 8⟩, ⟨12, 20, 15, 2⟩, ⟨12, 20, 14, 4⟩, ⟨12, 20, 13, 6⟩, ⟨12, 20, 12, 8⟩]
  exact AllWinning.cons node_25604 (AllWinning.cons node_25476 (AllWinning.cons node_25304 (AllWinning.cons node_25091 (AllWinning.cons node_25611 (AllWinning.cons node_25498 (AllWinning.cons node_25338 (AllWinning.cons node_25152 (AllWinning.cons node_25613 (AllWinning.cons node_25501 (AllWinning.cons node_25343 (AllWinning.cons node_25159 (AllWinning.nil))))))))))))

theorem node_25716 : Outcome ⟨12, 20, 16, 6⟩ true :=
  Outcome.win (q := ⟨7, 20, 16, 10⟩) (by decide) node_24856

theorem node_25717 : Outcome ⟨13, 15, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 20, 2⟩, ⟨11, 15, 20, 4⟩, ⟨13, 14, 20, 2⟩, ⟨13, 13, 20, 4⟩, ⟨13, 15, 19, 2⟩, ⟨13, 15, 18, 4⟩]
  exact AllWinning.cons node_25605 (AllWinning.cons node_25478 (AllWinning.cons node_25615 (AllWinning.cons node_25502 (AllWinning.cons node_25616 (AllWinning.cons node_25505 (AllWinning.nil))))))

theorem node_25718 : Outcome ⟨13, 15, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 20, 2⟩, ⟨11, 15, 20, 4⟩, ⟨10, 15, 20, 6⟩, ⟨9, 15, 20, 8⟩, ⟨13, 14, 20, 2⟩, ⟨13, 13, 20, 4⟩, ⟨13, 12, 20, 6⟩, ⟨13, 11, 20, 8⟩, ⟨13, 15, 19, 2⟩, ⟨13, 15, 18, 4⟩, ⟨13, 15, 17, 6⟩, ⟨13, 15, 16, 8⟩]
  exact AllWinning.cons node_25605 (AllWinning.cons node_25478 (AllWinning.cons node_25306 (AllWinning.cons node_25094 (AllWinning.cons node_25615 (AllWinning.cons node_25502 (AllWinning.cons node_25344 (AllWinning.cons node_25161 (AllWinning.cons node_25616 (AllWinning.cons node_25505 (AllWinning.cons node_25352 (AllWinning.cons node_25170 (AllWinning.nil))))))))))))

theorem node_25719 : Outcome ⟨13, 15, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 20, 2⟩, ⟨11, 15, 20, 4⟩, ⟨10, 15, 20, 6⟩, ⟨9, 15, 20, 8⟩, ⟨8, 15, 20, 10⟩, ⟨7, 15, 20, 12⟩, ⟨6, 15, 20, 14⟩, ⟨5, 15, 20, 16⟩, ⟨13, 14, 20, 2⟩, ⟨13, 13, 20, 4⟩, ⟨13, 12, 20, 6⟩, ⟨13, 11, 20, 8⟩, ⟨13, 10, 20, 10⟩, ⟨13, 9, 20, 12⟩, ⟨13, 8, 20, 14⟩, ⟨13, 7, 20, 16⟩, ⟨13, 15, 19, 2⟩, ⟨13, 15, 18, 4⟩, ⟨13, 15, 17, 6⟩, ⟨13, 15, 16, 8⟩, ⟨13, 15, 15, 10⟩, ⟨13, 15, 14, 12⟩, ⟨13, 15, 13, 14⟩, ⟨13, 15, 12, 16⟩]
  exact AllWinning.cons node_25605 (AllWinning.cons node_25478 (AllWinning.cons node_25306 (AllWinning.cons node_25094 (AllWinning.cons node_24859 (AllWinning.cons node_24548 (AllWinning.cons node_24261 (AllWinning.cons node_23840 (AllWinning.cons node_25615 (AllWinning.cons node_25502 (AllWinning.cons node_25344 (AllWinning.cons node_25161 (AllWinning.cons node_24932 (AllWinning.cons node_24656 (AllWinning.cons node_24371 (AllWinning.cons node_24010 (AllWinning.cons node_25616 (AllWinning.cons node_25505 (AllWinning.cons node_25352 (AllWinning.cons node_25170 (AllWinning.cons node_24942 (AllWinning.cons node_24673 (AllWinning.cons node_24384 (AllWinning.cons node_24034 (AllWinning.nil))))))))))))))))))))))))

theorem node_25720 : Outcome ⟨13, 15, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 20, 2⟩, ⟨11, 15, 20, 4⟩, ⟨10, 15, 20, 6⟩, ⟨9, 15, 20, 8⟩, ⟨8, 15, 20, 10⟩, ⟨7, 15, 20, 12⟩, ⟨6, 15, 20, 14⟩, ⟨5, 15, 20, 16⟩, ⟨4, 15, 20, 18⟩, ⟨3, 15, 20, 20⟩, ⟨13, 14, 20, 2⟩, ⟨13, 13, 20, 4⟩, ⟨13, 12, 20, 6⟩, ⟨13, 11, 20, 8⟩, ⟨13, 10, 20, 10⟩, ⟨13, 9, 20, 12⟩, ⟨13, 8, 20, 14⟩, ⟨13, 7, 20, 16⟩, ⟨13, 6, 20, 18⟩, ⟨13, 5, 20, 20⟩, ⟨13, 15, 19, 2⟩, ⟨13, 15, 18, 4⟩, ⟨13, 15, 17, 6⟩, ⟨13, 15, 16, 8⟩, ⟨13, 15, 15, 10⟩, ⟨13, 15, 14, 12⟩, ⟨13, 15, 13, 14⟩, ⟨13, 15, 12, 16⟩, ⟨13, 15, 11, 18⟩, ⟨13, 15, 10, 20⟩]
  exact AllWinning.cons node_25605 (AllWinning.cons node_25478 (AllWinning.cons node_25306 (AllWinning.cons node_25094 (AllWinning.cons node_24859 (AllWinning.cons node_24548 (AllWinning.cons node_24261 (AllWinning.cons node_23840 (AllWinning.cons node_23450 (AllWinning.cons node_22979 (AllWinning.cons node_25615 (AllWinning.cons node_25502 (AllWinning.cons node_25344 (AllWinning.cons node_25161 (AllWinning.cons node_24932 (AllWinning.cons node_24656 (AllWinning.cons node_24371 (AllWinning.cons node_24010 (AllWinning.cons node_23622 (AllWinning.cons node_23210 (AllWinning.cons node_25616 (AllWinning.cons node_25505 (AllWinning.cons node_25352 (AllWinning.cons node_25170 (AllWinning.cons node_24942 (AllWinning.cons node_24673 (AllWinning.cons node_24384 (AllWinning.cons node_24034 (AllWinning.cons node_23646 (AllWinning.cons node_23235 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_25721 : Outcome ⟨13, 16, 19, 6⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 6⟩) (by decide) node_25355

theorem node_25722 : Outcome ⟨13, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 17, 18, 2⟩) (by decide) node_25609

theorem node_25723 : Outcome ⟨13, 17, 18, 8⟩ true :=
  Outcome.win (q := ⟨12, 17, 18, 2⟩) (by decide) node_25609

theorem node_25724 : Outcome ⟨13, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 17, 2⟩) (by decide) node_25610

theorem node_25725 : Outcome ⟨13, 18, 17, 8⟩ true :=
  Outcome.win (q := ⟨12, 18, 17, 2⟩) (by decide) node_25610

theorem node_25726 : Outcome ⟨13, 19, 16, 6⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 6⟩) (by decide) node_25355

theorem node_25727 : Outcome ⟨13, 20, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 20, 15, 2⟩, ⟨11, 20, 15, 4⟩, ⟨13, 19, 15, 2⟩, ⟨13, 18, 15, 4⟩, ⟨13, 20, 14, 2⟩, ⟨13, 20, 13, 4⟩]
  exact AllWinning.cons node_25613 (AllWinning.cons node_25490 (AllWinning.cons node_25623 (AllWinning.cons node_25510 (AllWinning.cons node_25626 (AllWinning.cons node_25513 (AllWinning.nil))))))

theorem node_25728 : Outcome ⟨13, 20, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 20, 15, 2⟩, ⟨11, 20, 15, 4⟩, ⟨10, 20, 15, 6⟩, ⟨9, 20, 15, 8⟩, ⟨13, 19, 15, 2⟩, ⟨13, 18, 15, 4⟩, ⟨13, 17, 15, 6⟩, ⟨13, 16, 15, 8⟩, ⟨13, 20, 14, 2⟩, ⟨13, 20, 13, 4⟩, ⟨13, 20, 12, 6⟩, ⟨13, 20, 11, 8⟩]
  exact AllWinning.cons node_25613 (AllWinning.cons node_25490 (AllWinning.cons node_25314 (AllWinning.cons node_25105 (AllWinning.cons node_25623 (AllWinning.cons node_25510 (AllWinning.cons node_25359 (AllWinning.cons node_25172 (AllWinning.cons node_25626 (AllWinning.cons node_25513 (AllWinning.cons node_25365 (AllWinning.cons node_25180 (AllWinning.nil))))))))))))

theorem node_25729 : Outcome ⟨13, 20, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 20, 15, 2⟩, ⟨11, 20, 15, 4⟩, ⟨10, 20, 15, 6⟩, ⟨9, 20, 15, 8⟩, ⟨8, 20, 15, 10⟩, ⟨7, 20, 15, 12⟩, ⟨6, 20, 15, 14⟩, ⟨5, 20, 15, 16⟩, ⟨13, 19, 15, 2⟩, ⟨13, 18, 15, 4⟩, ⟨13, 17, 15, 6⟩, ⟨13, 16, 15, 8⟩, ⟨13, 15, 15, 10⟩, ⟨13, 14, 15, 12⟩, ⟨13, 13, 15, 14⟩, ⟨13, 12, 15, 16⟩, ⟨13, 20, 14, 2⟩, ⟨13, 20, 13, 4⟩, ⟨13, 20, 12, 6⟩, ⟨13, 20, 11, 8⟩, ⟨13, 20, 10, 10⟩, ⟨13, 20, 9, 12⟩, ⟨13, 20, 8, 14⟩, ⟨13, 20, 7, 16⟩]
  exact AllWinning.cons node_25613 (AllWinning.cons node_25490 (AllWinning.cons node_25314 (AllWinning.cons node_25105 (AllWinning.cons node_24867 (AllWinning.cons node_24558 (AllWinning.cons node_24272 (AllWinning.cons node_23848 (AllWinning.cons node_25623 (AllWinning.cons node_25510 (AllWinning.cons node_25359 (AllWinning.cons node_25172 (AllWinning.cons node_24942 (AllWinning.cons node_24668 (AllWinning.cons node_24380 (AllWinning.cons node_24026 (AllWinning.cons node_25626 (AllWinning.cons node_25513 (AllWinning.cons node_25365 (AllWinning.cons node_25180 (AllWinning.cons node_24951 (AllWinning.cons node_24682 (AllWinning.cons node_24392 (AllWinning.cons node_24048 (AllWinning.nil))))))))))))))))))))))))

theorem node_25730 : Outcome ⟨14, 14, 20, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 14, 12⟩) (by decide) node_24699

theorem node_25731 : Outcome ⟨14, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 18, 2⟩) (by decide) node_25628

theorem node_25732 : Outcome ⟨14, 15, 19, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 18, 2⟩) (by decide) node_25628

theorem node_25733 : Outcome ⟨14, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 18, 2⟩) (by decide) node_25628

theorem node_25734 : Outcome ⟨14, 16, 18, 8⟩ true :=
  Outcome.win (q := ⟨14, 12, 18, 8⟩) (by decide) node_25185

theorem node_25735 : Outcome ⟨14, 17, 17, 4⟩ true :=
  Outcome.win (q := ⟨13, 17, 17, 2⟩) (by decide) node_25620

theorem node_25736 : Outcome ⟨14, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 2⟩) (by decide) node_25633

theorem node_25737 : Outcome ⟨14, 18, 16, 8⟩ true :=
  Outcome.win (q := ⟨14, 18, 12, 8⟩) (by decide) node_25199

theorem node_25738 : Outcome ⟨14, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨14, 18, 15, 2⟩) (by decide) node_25636

theorem node_25739 : Outcome ⟨14, 19, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 18, 15, 2⟩) (by decide) node_25636

theorem node_25740 : Outcome ⟨14, 20, 14, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 14, 12⟩) (by decide) node_24699

theorem node_25741 : Outcome ⟨15, 13, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 20, 2⟩, ⟨13, 13, 20, 4⟩, ⟨12, 13, 20, 6⟩, ⟨11, 13, 20, 8⟩, ⟨10, 13, 20, 10⟩, ⟨9, 13, 20, 12⟩, ⟨8, 13, 20, 14⟩, ⟨7, 13, 20, 16⟩, ⟨15, 12, 20, 2⟩, ⟨15, 11, 20, 4⟩, ⟨15, 10, 20, 6⟩, ⟨15, 9, 20, 8⟩, ⟨15, 8, 20, 10⟩, ⟨15, 7, 20, 12⟩, ⟨15, 6, 20, 14⟩, ⟨15, 5, 20, 16⟩, ⟨15, 13, 19, 2⟩, ⟨15, 13, 18, 4⟩, ⟨15, 13, 17, 6⟩, ⟨15, 13, 16, 8⟩, ⟨15, 13, 15, 10⟩, ⟨15, 13, 14, 12⟩, ⟨15, 13, 13, 14⟩, ⟨15, 13, 12, 16⟩]
  exact AllWinning.cons node_25627 (AllWinning.cons node_25502 (AllWinning.cons node_25330 (AllWinning.cons node_25127 (AllWinning.cons node_24885 (AllWinning.cons node_24576 (AllWinning.cons node_24287 (AllWinning.cons node_23860 (AllWinning.cons node_25639 (AllWinning.cons node_25524 (AllWinning.cons node_25380 (AllWinning.cons node_25202 (AllWinning.cons node_24969 (AllWinning.cons node_24712 (AllWinning.cons node_24420 (AllWinning.cons node_24078 (AllWinning.cons node_25640 (AllWinning.cons node_25526 (AllWinning.cons node_25386 (AllWinning.cons node_25208 (AllWinning.cons node_24979 (AllWinning.cons node_24727 (AllWinning.cons node_24433 (AllWinning.cons node_24100 (AllWinning.nil))))))))))))))))))))))))

theorem node_25742 : Outcome ⟨15, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 14, 18, 2⟩) (by decide) node_25643

theorem node_25743 : Outcome ⟨15, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 18, 2⟩) (by decide) node_25628

theorem node_25744 : Outcome ⟨15, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 17, 2⟩) (by decide) node_25630

theorem node_25745 : Outcome ⟨15, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 2⟩) (by decide) node_25633

theorem node_25746 : Outcome ⟨15, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨14, 18, 15, 2⟩) (by decide) node_25636

theorem node_25747 : Outcome ⟨15, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 14, 2⟩) (by decide) node_25649

theorem node_25748 : Outcome ⟨15, 20, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 20, 13, 2⟩, ⟨13, 20, 13, 4⟩, ⟨12, 20, 13, 6⟩, ⟨11, 20, 13, 8⟩, ⟨10, 20, 13, 10⟩, ⟨9, 20, 13, 12⟩, ⟨8, 20, 13, 14⟩, ⟨7, 20, 13, 16⟩, ⟨15, 19, 13, 2⟩, ⟨15, 18, 13, 4⟩, ⟨15, 17, 13, 6⟩, ⟨15, 16, 13, 8⟩, ⟨15, 15, 13, 10⟩, ⟨15, 14, 13, 12⟩, ⟨15, 13, 13, 14⟩, ⟨15, 12, 13, 16⟩, ⟨15, 20, 12, 2⟩, ⟨15, 20, 11, 4⟩, ⟨15, 20, 10, 6⟩, ⟨15, 20, 9, 8⟩, ⟨15, 20, 8, 10⟩, ⟨15, 20, 7, 12⟩, ⟨15, 20, 6, 14⟩, ⟨15, 20, 5, 16⟩]
  exact AllWinning.cons node_25638 (AllWinning.cons node_25513 (AllWinning.cons node_25343 (AllWinning.cons node_25143 (AllWinning.cons node_24901 (AllWinning.cons node_24601 (AllWinning.cons node_24303 (AllWinning.cons node_23881 (AllWinning.cons node_25651 (AllWinning.cons node_25533 (AllWinning.cons node_25394 (AllWinning.cons node_25213 (AllWinning.cons node_24982 (AllWinning.cons node_24731 (AllWinning.cons node_24433 (AllWinning.cons node_24096 (AllWinning.cons node_25654 (AllWinning.cons node_25536 (AllWinning.cons node_25399 (AllWinning.cons node_25220 (AllWinning.cons node_24991 (AllWinning.cons node_24742 (AllWinning.cons node_24446 (AllWinning.cons node_24115 (AllWinning.nil))))))))))))))))))))))))

theorem node_25749 : Outcome ⟨16, 13, 19, 6⟩ true :=
  Outcome.win (q := ⟨16, 13, 16, 6⟩) (by decide) node_25406

theorem node_25750 : Outcome ⟨16, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨15, 14, 18, 2⟩) (by decide) node_25643

theorem node_25751 : Outcome ⟨16, 15, 17, 2⟩ true :=
  Outcome.win (q := ⟨16, 14, 17, 2⟩) (by decide) node_25657

theorem node_25752 : Outcome ⟨16, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨16, 14, 17, 2⟩) (by decide) node_25657

theorem node_25753 : Outcome ⟨16, 16, 16, 6⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 6⟩) (by decide) node_25355

theorem node_25754 : Outcome ⟨16, 17, 15, 2⟩ true :=
  Outcome.win (q := ⟨16, 17, 14, 2⟩) (by decide) node_25662

theorem node_25755 : Outcome ⟨16, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨16, 17, 14, 2⟩) (by decide) node_25662

theorem node_25756 : Outcome ⟨16, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 14, 2⟩) (by decide) node_25649

theorem node_25757 : Outcome ⟨16, 19, 13, 6⟩ true :=
  Outcome.win (q := ⟨16, 16, 13, 6⟩) (by decide) node_25414

theorem node_25758 : Outcome ⟨17, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨17, 12, 18, 2⟩) (by decide) node_25666

theorem node_25759 : Outcome ⟨17, 13, 18, 8⟩ true :=
  Outcome.win (q := ⟨17, 12, 18, 2⟩) (by decide) node_25666

theorem node_25760 : Outcome ⟨17, 14, 17, 8⟩ true :=
  Outcome.win (q := ⟨16, 14, 17, 2⟩) (by decide) node_25657

theorem node_25761 : Outcome ⟨17, 15, 16, 2⟩ true :=
  Outcome.win (q := ⟨17, 14, 16, 2⟩) (by decide) node_25669

theorem node_25762 : Outcome ⟨17, 16, 15, 2⟩ true :=
  Outcome.win (q := ⟨17, 16, 14, 2⟩) (by decide) node_25671

theorem node_25763 : Outcome ⟨17, 17, 14, 8⟩ true :=
  Outcome.win (q := ⟨16, 17, 14, 2⟩) (by decide) node_25662

theorem node_25764 : Outcome ⟨17, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 13, 2⟩) (by decide) node_25673

theorem node_25765 : Outcome ⟨17, 18, 13, 8⟩ true :=
  Outcome.win (q := ⟨17, 17, 13, 2⟩) (by decide) node_25673

theorem node_25766 : Outcome ⟨18, 11, 19, 2⟩ true :=
  Outcome.win (q := ⟨16, 11, 19, 4⟩) (by decide) node_25538

theorem node_25767 : Outcome ⟨18, 12, 18, 2⟩ true :=
  Outcome.win (q := ⟨17, 12, 18, 2⟩) (by decide) node_25666

theorem node_25768 : Outcome ⟨18, 13, 17, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 17, 2⟩) (by decide) node_25667

theorem node_25769 : Outcome ⟨18, 14, 16, 2⟩ true :=
  Outcome.win (q := ⟨17, 14, 16, 2⟩) (by decide) node_25669

theorem node_25770 : Outcome ⟨18, 15, 15, 2⟩ true :=
  Outcome.win (q := ⟨18, 14, 15, 2⟩) (by decide) node_25679

theorem node_25771 : Outcome ⟨18, 16, 14, 2⟩ true :=
  Outcome.win (q := ⟨17, 16, 14, 2⟩) (by decide) node_25671

theorem node_25772 : Outcome ⟨18, 17, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 13, 2⟩) (by decide) node_25673

theorem node_25773 : Outcome ⟨18, 18, 12, 2⟩ true :=
  Outcome.win (q := ⟨17, 18, 12, 2⟩) (by decide) node_25675

theorem node_25774 : Outcome ⟨18, 19, 11, 2⟩ true :=
  Outcome.win (q := ⟨16, 19, 11, 4⟩) (by decide) node_25550

theorem node_25775 : Outcome ⟨19, 10, 19, 2⟩ true :=
  Outcome.win (q := ⟨19, 8, 19, 4⟩) (by decide) node_25563

theorem node_25776 : Outcome ⟨19, 10, 19, 6⟩ true :=
  Outcome.win (q := ⟨19, 8, 19, 4⟩) (by decide) node_25563

theorem node_25777 : Outcome ⟨19, 11, 18, 2⟩ true :=
  Outcome.win (q := ⟨19, 11, 16, 4⟩) (by decide) node_25566

theorem node_25778 : Outcome ⟨19, 13, 16, 6⟩ true :=
  Outcome.win (q := ⟨16, 13, 16, 6⟩) (by decide) node_25406

theorem node_25779 : Outcome ⟨19, 16, 13, 6⟩ true :=
  Outcome.win (q := ⟨16, 16, 13, 6⟩) (by decide) node_25414

theorem node_25780 : Outcome ⟨19, 18, 11, 2⟩ true :=
  Outcome.win (q := ⟨19, 16, 11, 4⟩) (by decide) node_25573

theorem node_25781 : Outcome ⟨19, 19, 10, 2⟩ true :=
  Outcome.win (q := ⟨19, 19, 8, 4⟩) (by decide) node_25576

theorem node_25782 : Outcome ⟨19, 19, 10, 6⟩ true :=
  Outcome.win (q := ⟨19, 19, 8, 4⟩) (by decide) node_25576

theorem node_25783 : Outcome ⟨9, 20, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 4⟩) (by decide) node_25584

theorem node_25784 : Outcome ⟨9, 20, 20, 8⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 4⟩) (by decide) node_25584

theorem node_25785 : Outcome ⟨10, 19, 20, 4⟩ true :=
  Outcome.win (q := ⟨10, 19, 18, 4⟩) (by decide) node_25595

theorem node_25786 : Outcome ⟨10, 20, 19, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 19, 4⟩) (by decide) node_25594

theorem node_25787 : Outcome ⟨11, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 4⟩) (by decide) node_25584

theorem node_25788 : Outcome ⟨11, 18, 20, 6⟩ true :=
  Outcome.win (q := ⟨9, 18, 20, 4⟩) (by decide) node_25584

theorem node_25789 : Outcome ⟨11, 19, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 19, 2⟩, ⟨9, 19, 19, 4⟩, ⟨11, 18, 19, 2⟩, ⟨11, 17, 19, 4⟩, ⟨11, 19, 18, 2⟩, ⟨11, 19, 17, 4⟩]
  exact AllWinning.cons node_25699 (AllWinning.cons node_25587 (AllWinning.cons node_25704 (AllWinning.cons node_25599 (AllWinning.cons node_25705 (AllWinning.cons node_25603 (AllWinning.nil))))))

theorem node_25790 : Outcome ⟨11, 19, 19, 4⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 6⟩) (by decide) node_25460

theorem node_25791 : Outcome ⟨11, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨9, 20, 18, 4⟩) (by decide) node_25590

theorem node_25792 : Outcome ⟨11, 20, 18, 6⟩ true :=
  Outcome.win (q := ⟨9, 20, 18, 4⟩) (by decide) node_25590

theorem node_25793 : Outcome ⟨12, 17, 20, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 20, 2⟩) (by decide) node_25702

theorem node_25794 : Outcome ⟨12, 18, 19, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 19, 4⟩) (by decide) node_25594

theorem node_25795 : Outcome ⟨12, 19, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 19, 18, 4⟩) (by decide) node_25595

theorem node_25796 : Outcome ⟨12, 20, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 20, 17, 2⟩) (by decide) node_25706

theorem node_25797 : Outcome ⟨13, 16, 20, 8⟩ true :=
  Outcome.win (q := ⟨7, 16, 20, 12⟩) (by decide) node_24846

theorem node_25798 : Outcome ⟨13, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 17, 4⟩) (by decide) node_25621

theorem node_25799 : Outcome ⟨13, 17, 19, 4⟩ true :=
  Outcome.win (q := ⟨13, 17, 17, 4⟩) (by decide) node_25621

theorem node_25800 : Outcome ⟨13, 18, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 18, 2⟩, ⟨11, 18, 18, 4⟩, ⟨13, 17, 18, 2⟩, ⟨13, 16, 18, 4⟩, ⟨13, 18, 17, 2⟩, ⟨13, 18, 16, 4⟩]
  exact AllWinning.cons node_25712 (AllWinning.cons node_25601 (AllWinning.cons node_25722 (AllWinning.cons node_25619 (AllWinning.cons node_25724 (AllWinning.cons node_25622 (AllWinning.nil))))))

theorem node_25801 : Outcome ⟨13, 18, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 18, 2⟩, ⟨11, 18, 18, 4⟩, ⟨10, 18, 18, 6⟩, ⟨9, 18, 18, 8⟩, ⟨13, 17, 18, 2⟩, ⟨13, 16, 18, 4⟩, ⟨13, 15, 18, 6⟩, ⟨13, 14, 18, 8⟩, ⟨13, 18, 17, 2⟩, ⟨13, 18, 16, 4⟩, ⟨13, 18, 15, 6⟩, ⟨13, 18, 14, 8⟩]
  exact AllWinning.cons node_25712 (AllWinning.cons node_25601 (AllWinning.cons node_25473 (AllWinning.cons node_25300 (AllWinning.cons node_25722 (AllWinning.cons node_25619 (AllWinning.cons node_25506 (AllWinning.cons node_25349 (AllWinning.cons node_25724 (AllWinning.cons node_25622 (AllWinning.cons node_25511 (AllWinning.cons node_25362 (AllWinning.nil))))))))))))

theorem node_25802 : Outcome ⟨13, 18, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 18, 2⟩, ⟨11, 18, 18, 4⟩, ⟨10, 18, 18, 6⟩, ⟨9, 18, 18, 8⟩, ⟨8, 18, 18, 10⟩, ⟨7, 18, 18, 12⟩, ⟨13, 17, 18, 2⟩, ⟨13, 16, 18, 4⟩, ⟨13, 15, 18, 6⟩, ⟨13, 14, 18, 8⟩, ⟨13, 13, 18, 10⟩, ⟨13, 12, 18, 12⟩, ⟨13, 18, 17, 2⟩, ⟨13, 18, 16, 4⟩, ⟨13, 18, 15, 6⟩, ⟨13, 18, 14, 8⟩, ⟨13, 18, 13, 10⟩, ⟨13, 18, 12, 12⟩]
  exact AllWinning.cons node_25712 (AllWinning.cons node_25601 (AllWinning.cons node_25473 (AllWinning.cons node_25300 (AllWinning.cons node_25086 (AllWinning.cons node_24850 (AllWinning.cons node_25722 (AllWinning.cons node_25619 (AllWinning.cons node_25506 (AllWinning.cons node_25349 (AllWinning.cons node_25165 (AllWinning.cons node_24935 (AllWinning.cons node_25724 (AllWinning.cons node_25622 (AllWinning.cons node_25511 (AllWinning.cons node_25362 (AllWinning.cons node_25178 (AllWinning.cons node_24949 (AllWinning.nil))))))))))))))))))

theorem node_25803 : Outcome ⟨13, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 17, 4⟩) (by decide) node_25621

theorem node_25804 : Outcome ⟨13, 19, 17, 4⟩ true :=
  Outcome.win (q := ⟨13, 17, 17, 4⟩) (by decide) node_25621

theorem node_25805 : Outcome ⟨13, 20, 16, 8⟩ true :=
  Outcome.win (q := ⟨7, 20, 16, 12⟩) (by decide) node_24857

theorem node_25806 : Outcome ⟨14, 15, 20, 6⟩ true :=
  Outcome.win (q := ⟨13, 15, 20, 2⟩) (by decide) node_25717

theorem node_25807 : Outcome ⟨14, 16, 19, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 17, 4⟩) (by decide) node_25631

theorem node_25808 : Outcome ⟨14, 16, 19, 4⟩ true :=
  Outcome.win (q := ⟨11, 16, 19, 6⟩) (by decide) node_25481

theorem node_25809 : Outcome ⟨14, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 4⟩) (by decide) node_25634

theorem node_25810 : Outcome ⟨14, 17, 18, 6⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 4⟩) (by decide) node_25634

theorem node_25811 : Outcome ⟨14, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 17, 4⟩) (by decide) node_25631

theorem node_25812 : Outcome ⟨14, 18, 17, 6⟩ true :=
  Outcome.win (q := ⟨14, 16, 17, 4⟩) (by decide) node_25631

theorem node_25813 : Outcome ⟨14, 19, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 16, 4⟩) (by decide) node_25634

theorem node_25814 : Outcome ⟨14, 19, 16, 4⟩ true :=
  Outcome.win (q := ⟨11, 19, 16, 6⟩) (by decide) node_25488

theorem node_25815 : Outcome ⟨14, 20, 15, 6⟩ true :=
  Outcome.win (q := ⟨13, 20, 15, 2⟩) (by decide) node_25727

theorem node_25816 : Outcome ⟨15, 15, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 19, 2⟩, ⟨13, 15, 19, 4⟩, ⟨15, 14, 19, 2⟩, ⟨15, 13, 19, 4⟩, ⟨15, 15, 18, 2⟩, ⟨15, 15, 17, 4⟩]
  exact AllWinning.cons node_25731 (AllWinning.cons node_25617 (AllWinning.cons node_25742 (AllWinning.cons node_25641 (AllWinning.cons node_25743 (AllWinning.cons node_25645 (AllWinning.nil))))))

theorem node_25817 : Outcome ⟨15, 16, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 18, 2⟩, ⟨13, 16, 18, 4⟩, ⟨15, 15, 18, 2⟩, ⟨15, 14, 18, 4⟩, ⟨15, 16, 17, 2⟩, ⟨15, 16, 16, 4⟩]
  exact AllWinning.cons node_25733 (AllWinning.cons node_25619 (AllWinning.cons node_25743 (AllWinning.cons node_25644 (AllWinning.cons node_25744 (AllWinning.cons node_25646 (AllWinning.nil))))))

theorem node_25818 : Outcome ⟨15, 16, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 18, 2⟩, ⟨13, 16, 18, 4⟩, ⟨12, 16, 18, 6⟩, ⟨11, 16, 18, 8⟩, ⟨15, 15, 18, 2⟩, ⟨15, 14, 18, 4⟩, ⟨15, 13, 18, 6⟩, ⟨15, 12, 18, 8⟩, ⟨15, 16, 17, 2⟩, ⟨15, 16, 16, 4⟩, ⟨15, 16, 15, 6⟩, ⟨15, 16, 14, 8⟩]
  exact AllWinning.cons node_25733 (AllWinning.cons node_25619 (AllWinning.cons node_25495 (AllWinning.cons node_25320 (AllWinning.cons node_25743 (AllWinning.cons node_25644 (AllWinning.cons node_25527 (AllWinning.cons node_25383 (AllWinning.cons node_25744 (AllWinning.cons node_25646 (AllWinning.cons node_25530 (AllWinning.cons node_25391 (AllWinning.nil))))))))))))

theorem node_25819 : Outcome ⟨15, 16, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 18, 2⟩, ⟨13, 16, 18, 4⟩, ⟨12, 16, 18, 6⟩, ⟨11, 16, 18, 8⟩, ⟨10, 16, 18, 10⟩, ⟨9, 16, 18, 12⟩, ⟨15, 15, 18, 2⟩, ⟨15, 14, 18, 4⟩, ⟨15, 13, 18, 6⟩, ⟨15, 12, 18, 8⟩, ⟨15, 11, 18, 10⟩, ⟨15, 10, 18, 12⟩, ⟨15, 16, 17, 2⟩, ⟨15, 16, 16, 4⟩, ⟨15, 16, 15, 6⟩, ⟨15, 16, 14, 8⟩, ⟨15, 16, 13, 10⟩, ⟨15, 16, 12, 12⟩]
  exact AllWinning.cons node_25733 (AllWinning.cons node_25619 (AllWinning.cons node_25495 (AllWinning.cons node_25320 (AllWinning.cons node_25114 (AllWinning.cons node_24874 (AllWinning.cons node_25743 (AllWinning.cons node_25644 (AllWinning.cons node_25527 (AllWinning.cons node_25383 (AllWinning.cons node_25205 (AllWinning.cons node_24972 (AllWinning.cons node_25744 (AllWinning.cons node_25646 (AllWinning.cons node_25530 (AllWinning.cons node_25391 (AllWinning.cons node_25214 (AllWinning.cons node_24986 (AllWinning.nil))))))))))))))))))

theorem node_25820 : Outcome ⟨15, 16, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 18, 2⟩, ⟨13, 16, 18, 4⟩, ⟨12, 16, 18, 6⟩, ⟨11, 16, 18, 8⟩, ⟨10, 16, 18, 10⟩, ⟨9, 16, 18, 12⟩, ⟨8, 16, 18, 14⟩, ⟨7, 16, 18, 16⟩, ⟨15, 15, 18, 2⟩, ⟨15, 14, 18, 4⟩, ⟨15, 13, 18, 6⟩, ⟨15, 12, 18, 8⟩, ⟨15, 11, 18, 10⟩, ⟨15, 10, 18, 12⟩, ⟨15, 9, 18, 14⟩, ⟨15, 8, 18, 16⟩, ⟨15, 16, 17, 2⟩, ⟨15, 16, 16, 4⟩, ⟨15, 16, 15, 6⟩, ⟨15, 16, 14, 8⟩, ⟨15, 16, 13, 10⟩, ⟨15, 16, 12, 12⟩, ⟨15, 16, 11, 14⟩, ⟨15, 16, 10, 16⟩]
  exact AllWinning.cons node_25733 (AllWinning.cons node_25619 (AllWinning.cons node_25495 (AllWinning.cons node_25320 (AllWinning.cons node_25114 (AllWinning.cons node_24874 (AllWinning.cons node_24564 (AllWinning.cons node_24278 (AllWinning.cons node_25743 (AllWinning.cons node_25644 (AllWinning.cons node_25527 (AllWinning.cons node_25383 (AllWinning.cons node_25205 (AllWinning.cons node_24972 (AllWinning.cons node_24717 (AllWinning.cons node_24423 (AllWinning.cons node_25744 (AllWinning.cons node_25646 (AllWinning.cons node_25530 (AllWinning.cons node_25391 (AllWinning.cons node_25214 (AllWinning.cons node_24986 (AllWinning.cons node_24736 (AllWinning.cons node_24439 (AllWinning.nil))))))))))))))))))))))))

theorem node_25821 : Outcome ⟨15, 17, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 17, 4⟩) (by decide) node_25621

theorem node_25822 : Outcome ⟨15, 18, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 16, 2⟩, ⟨13, 18, 16, 4⟩, ⟨15, 17, 16, 2⟩, ⟨15, 16, 16, 4⟩, ⟨15, 18, 15, 2⟩, ⟨15, 18, 14, 4⟩]
  exact AllWinning.cons node_25736 (AllWinning.cons node_25622 (AllWinning.cons node_25745 (AllWinning.cons node_25646 (AllWinning.cons node_25746 (AllWinning.cons node_25650 (AllWinning.nil))))))

theorem node_25823 : Outcome ⟨15, 18, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 16, 2⟩, ⟨13, 18, 16, 4⟩, ⟨12, 18, 16, 6⟩, ⟨11, 18, 16, 8⟩, ⟨15, 17, 16, 2⟩, ⟨15, 16, 16, 4⟩, ⟨15, 15, 16, 6⟩, ⟨15, 14, 16, 8⟩, ⟨15, 18, 15, 2⟩, ⟨15, 18, 14, 4⟩, ⟨15, 18, 13, 6⟩, ⟨15, 18, 12, 8⟩]
  exact AllWinning.cons node_25736 (AllWinning.cons node_25622 (AllWinning.cons node_25499 (AllWinning.cons node_25326 (AllWinning.cons node_25745 (AllWinning.cons node_25646 (AllWinning.cons node_25529 (AllWinning.cons node_25388 (AllWinning.cons node_25746 (AllWinning.cons node_25650 (AllWinning.cons node_25534 (AllWinning.cons node_25397 (AllWinning.nil))))))))))))

end RQ9F1
