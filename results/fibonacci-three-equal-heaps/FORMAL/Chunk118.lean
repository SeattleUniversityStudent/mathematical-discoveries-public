import Chunk117
set_option autoImplicit false
namespace RQ9F1

theorem node_24734 : Outcome ⟨15, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨13, 16, 11, 4⟩) (by decide) node_24036

theorem node_24735 : Outcome ⟨15, 16, 11, 8⟩ true :=
  Outcome.win (q := ⟨13, 16, 11, 4⟩) (by decide) node_24036

theorem node_24736 : Outcome ⟨15, 16, 11, 14⟩ true :=
  Outcome.win (q := ⟨15, 16, 1, 20⟩) (by decide) node_19523

theorem node_24737 : Outcome ⟨15, 17, 10, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 10, 4⟩) (by decide) node_24104

theorem node_24738 : Outcome ⟨15, 18, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 9, 2⟩, ⟨13, 18, 9, 4⟩, ⟨15, 17, 9, 2⟩, ⟨15, 16, 9, 4⟩, ⟨15, 18, 8, 2⟩, ⟨15, 18, 7, 4⟩]
  exact AllWinning.cons node_24414 (AllWinning.cons node_24041 (AllWinning.cons node_24440 (AllWinning.cons node_24108 (AllWinning.cons node_24441 (AllWinning.cons node_24112 (AllWinning.nil))))))

theorem node_24739 : Outcome ⟨15, 18, 9, 14⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 12⟩) (by decide) node_22271

theorem node_24740 : Outcome ⟨15, 19, 8, 4⟩ true :=
  Outcome.win (q := ⟨13, 19, 8, 4⟩) (by decide) node_24044

theorem node_24741 : Outcome ⟨15, 19, 8, 8⟩ true :=
  Outcome.win (q := ⟨13, 19, 8, 4⟩) (by decide) node_24044

theorem node_24742 : Outcome ⟨15, 20, 7, 12⟩ true :=
  Outcome.win (q := ⟨15, 12, 7, 16⟩) (by decide) node_21024

theorem node_24743 : Outcome ⟨16, 7, 19, 4⟩ true :=
  Outcome.win (q := ⟨16, 7, 18, 2⟩) (by decide) node_24449

theorem node_24744 : Outcome ⟨16, 7, 19, 8⟩ true :=
  Outcome.win (q := ⟨16, 7, 18, 2⟩) (by decide) node_24449

theorem node_24745 : Outcome ⟨16, 8, 18, 4⟩ true :=
  Outcome.win (q := ⟨16, 8, 16, 4⟩) (by decide) node_24121

theorem node_24746 : Outcome ⟨16, 8, 18, 14⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 16⟩) (by decide) node_20651

theorem node_24747 : Outcome ⟨16, 9, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 9, 17, 2⟩, ⟨14, 9, 17, 4⟩, ⟨16, 8, 17, 2⟩, ⟨16, 7, 17, 4⟩, ⟨16, 9, 16, 2⟩, ⟨16, 9, 15, 4⟩]
  exact AllWinning.cons node_24424 (AllWinning.cons node_24053 (AllWinning.cons node_24451 (AllWinning.cons node_24120 (AllWinning.cons node_24452 (AllWinning.cons node_24125 (AllWinning.nil))))))

theorem node_24748 : Outcome ⟨16, 10, 16, 4⟩ true :=
  Outcome.win (q := ⟨14, 10, 16, 4⟩) (by decide) node_24055

theorem node_24749 : Outcome ⟨16, 10, 16, 6⟩ true :=
  Outcome.win (q := ⟨14, 10, 16, 4⟩) (by decide) node_24055

theorem node_24750 : Outcome ⟨16, 11, 15, 2⟩ true :=
  Outcome.win (q := ⟨16, 11, 13, 4⟩) (by decide) node_24132

theorem node_24751 : Outcome ⟨16, 11, 15, 8⟩ true :=
  Outcome.win (q := ⟨16, 11, 13, 4⟩) (by decide) node_24132

theorem node_24752 : Outcome ⟨16, 11, 15, 14⟩ true :=
  Outcome.win (q := ⟨16, 1, 15, 20⟩) (by decide) node_19540

theorem node_24753 : Outcome ⟨16, 12, 14, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 14, 4⟩) (by decide) node_24128

theorem node_24754 : Outcome ⟨16, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨16, 10, 14, 4⟩) (by decide) node_24128

theorem node_24755 : Outcome ⟨16, 13, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 6⟩) (by decide) node_23637

theorem node_24756 : Outcome ⟨16, 13, 13, 6⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 6⟩) (by decide) node_23637

theorem node_24757 : Outcome ⟨16, 14, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 12, 4⟩) (by decide) node_24136

theorem node_24758 : Outcome ⟨16, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 12, 4⟩) (by decide) node_24136

theorem node_24759 : Outcome ⟨16, 15, 11, 2⟩ true :=
  Outcome.win (q := ⟨16, 13, 11, 4⟩) (by decide) node_24139

theorem node_24760 : Outcome ⟨16, 15, 11, 8⟩ true :=
  Outcome.win (q := ⟨16, 13, 11, 4⟩) (by decide) node_24139

theorem node_24761 : Outcome ⟨16, 15, 11, 14⟩ true :=
  Outcome.win (q := ⟨16, 15, 1, 20⟩) (by decide) node_19578

theorem node_24762 : Outcome ⟨16, 16, 10, 4⟩ true :=
  Outcome.win (q := ⟨14, 16, 10, 4⟩) (by decide) node_24070

theorem node_24763 : Outcome ⟨16, 16, 10, 6⟩ true :=
  Outcome.win (q := ⟨14, 16, 10, 4⟩) (by decide) node_24070

theorem node_24764 : Outcome ⟨16, 17, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 17, 9, 2⟩, ⟨14, 17, 9, 4⟩, ⟨16, 16, 9, 2⟩, ⟨16, 15, 9, 4⟩, ⟨16, 17, 8, 2⟩, ⟨16, 17, 7, 4⟩]
  exact AllWinning.cons node_24440 (AllWinning.cons node_24072 (AllWinning.cons node_24468 (AllWinning.cons node_24147 (AllWinning.cons node_24470 (AllWinning.cons node_24153 (AllWinning.nil))))))

theorem node_24765 : Outcome ⟨16, 18, 8, 4⟩ true :=
  Outcome.win (q := ⟨16, 16, 8, 4⟩) (by decide) node_24149

theorem node_24766 : Outcome ⟨16, 18, 8, 14⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 16⟩) (by decide) node_20680

theorem node_24767 : Outcome ⟨16, 19, 7, 8⟩ true :=
  Outcome.win (q := ⟨16, 18, 7, 2⟩) (by decide) node_24471

theorem node_24768 : Outcome ⟨17, 6, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 19, 2⟩, ⟨15, 6, 19, 4⟩, ⟨17, 5, 19, 2⟩, ⟨17, 4, 19, 4⟩, ⟨17, 6, 18, 2⟩, ⟨17, 6, 17, 4⟩]
  exact AllWinning.cons node_24447 (AllWinning.cons node_24080 (AllWinning.cons node_24474 (AllWinning.cons node_24158 (AllWinning.cons node_24476 (AllWinning.cons node_24160 (AllWinning.nil))))))

theorem node_24769 : Outcome ⟨17, 8, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 8, 17, 2⟩, ⟨15, 8, 17, 4⟩, ⟨17, 7, 17, 2⟩, ⟨17, 6, 17, 4⟩, ⟨17, 8, 16, 2⟩, ⟨17, 8, 15, 4⟩]
  exact AllWinning.cons node_24451 (AllWinning.cons node_24083 (AllWinning.cons node_24477 (AllWinning.cons node_24160 (AllWinning.cons node_24478 (AllWinning.cons node_24163 (AllWinning.nil))))))

theorem node_24770 : Outcome ⟨17, 8, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 8, 17, 2⟩, ⟨15, 8, 17, 4⟩, ⟨14, 8, 17, 6⟩, ⟨13, 8, 17, 8⟩, ⟨17, 7, 17, 2⟩, ⟨17, 6, 17, 4⟩, ⟨17, 5, 17, 6⟩, ⟨17, 4, 17, 8⟩, ⟨17, 8, 16, 2⟩, ⟨17, 8, 15, 4⟩, ⟨17, 8, 14, 6⟩, ⟨17, 8, 13, 8⟩]
  exact AllWinning.cons node_24451 (AllWinning.cons node_24083 (AllWinning.cons node_23661 (AllWinning.cons node_23217 (AllWinning.cons node_24477 (AllWinning.cons node_24160 (AllWinning.cons node_23747 (AllWinning.cons node_23347 (AllWinning.cons node_24478 (AllWinning.cons node_24163 (AllWinning.cons node_23752 (AllWinning.cons node_23353 (AllWinning.nil))))))))))))

theorem node_24771 : Outcome ⟨17, 9, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 16, 2⟩, ⟨15, 9, 16, 4⟩, ⟨17, 8, 16, 2⟩, ⟨17, 7, 16, 4⟩, ⟨17, 9, 15, 2⟩, ⟨17, 9, 14, 4⟩]
  exact AllWinning.cons node_24452 (AllWinning.cons node_24085 (AllWinning.cons node_24478 (AllWinning.cons node_24162 (AllWinning.cons node_24479 (AllWinning.cons node_24164 (AllWinning.nil))))))

theorem node_24772 : Outcome ⟨17, 9, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 16, 2⟩, ⟨15, 9, 16, 4⟩, ⟨14, 9, 16, 6⟩, ⟨13, 9, 16, 8⟩, ⟨17, 8, 16, 2⟩, ⟨17, 7, 16, 4⟩, ⟨17, 6, 16, 6⟩, ⟨17, 5, 16, 8⟩, ⟨17, 9, 15, 2⟩, ⟨17, 9, 14, 4⟩, ⟨17, 9, 13, 6⟩, ⟨17, 9, 12, 8⟩]
  exact AllWinning.cons node_24452 (AllWinning.cons node_24085 (AllWinning.cons node_23663 (AllWinning.cons node_23219 (AllWinning.cons node_24478 (AllWinning.cons node_24162 (AllWinning.cons node_23750 (AllWinning.cons node_23349 (AllWinning.cons node_24479 (AllWinning.cons node_24164 (AllWinning.cons node_23753 (AllWinning.cons node_23356 (AllWinning.nil))))))))))))

theorem node_24773 : Outcome ⟨17, 9, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 16, 2⟩, ⟨15, 9, 16, 4⟩, ⟨14, 9, 16, 6⟩, ⟨13, 9, 16, 8⟩, ⟨12, 9, 16, 10⟩, ⟨11, 9, 16, 12⟩, ⟨17, 8, 16, 2⟩, ⟨17, 7, 16, 4⟩, ⟨17, 6, 16, 6⟩, ⟨17, 5, 16, 8⟩, ⟨17, 4, 16, 10⟩, ⟨17, 3, 16, 12⟩, ⟨17, 9, 15, 2⟩, ⟨17, 9, 14, 4⟩, ⟨17, 9, 13, 6⟩, ⟨17, 9, 12, 8⟩, ⟨17, 9, 11, 10⟩, ⟨17, 9, 10, 12⟩]
  exact AllWinning.cons node_24452 (AllWinning.cons node_24085 (AllWinning.cons node_23663 (AllWinning.cons node_23219 (AllWinning.cons node_22665 (AllWinning.cons node_22056 (AllWinning.cons node_24478 (AllWinning.cons node_24162 (AllWinning.cons node_23750 (AllWinning.cons node_23349 (AllWinning.cons node_22884 (AllWinning.cons node_22323 (AllWinning.cons node_24479 (AllWinning.cons node_24164 (AllWinning.cons node_23753 (AllWinning.cons node_23356 (AllWinning.cons node_22892 (AllWinning.cons node_22336 (AllWinning.nil))))))))))))))))))

theorem node_24774 : Outcome ⟨17, 10, 15, 4⟩ true :=
  Outcome.win (q := ⟨15, 10, 15, 4⟩) (by decide) node_24088

theorem node_24775 : Outcome ⟨17, 11, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 14, 2⟩, ⟨15, 11, 14, 4⟩, ⟨17, 10, 14, 2⟩, ⟨17, 9, 14, 4⟩, ⟨17, 11, 13, 2⟩, ⟨17, 11, 12, 4⟩]
  exact AllWinning.cons node_24456 (AllWinning.cons node_24092 (AllWinning.cons node_24480 (AllWinning.cons node_24164 (AllWinning.cons node_24481 (AllWinning.cons node_24166 (AllWinning.nil))))))

theorem node_24776 : Outcome ⟨17, 11, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 14, 2⟩, ⟨15, 11, 14, 4⟩, ⟨14, 11, 14, 6⟩, ⟨13, 11, 14, 8⟩, ⟨17, 10, 14, 2⟩, ⟨17, 9, 14, 4⟩, ⟨17, 8, 14, 6⟩, ⟨17, 7, 14, 8⟩, ⟨17, 11, 13, 2⟩, ⟨17, 11, 12, 4⟩, ⟨17, 11, 11, 6⟩, ⟨17, 11, 10, 8⟩]
  exact AllWinning.cons node_24456 (AllWinning.cons node_24092 (AllWinning.cons node_23667 (AllWinning.cons node_23224 (AllWinning.cons node_24480 (AllWinning.cons node_24164 (AllWinning.cons node_23752 (AllWinning.cons node_23351 (AllWinning.cons node_24481 (AllWinning.cons node_24166 (AllWinning.cons node_23756 (AllWinning.cons node_23360 (AllWinning.nil))))))))))))

theorem node_24777 : Outcome ⟨17, 12, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 12, 13, 2⟩, ⟨15, 12, 13, 4⟩, ⟨17, 11, 13, 2⟩, ⟨17, 10, 13, 4⟩, ⟨17, 12, 12, 2⟩, ⟨17, 12, 11, 4⟩]
  exact AllWinning.cons node_24458 (AllWinning.cons node_24094 (AllWinning.cons node_24481 (AllWinning.cons node_24165 (AllWinning.cons node_24482 (AllWinning.cons node_24167 (AllWinning.nil))))))

theorem node_24778 : Outcome ⟨17, 12, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 12, 13, 2⟩, ⟨15, 12, 13, 4⟩, ⟨14, 12, 13, 6⟩, ⟨13, 12, 13, 8⟩, ⟨17, 11, 13, 2⟩, ⟨17, 10, 13, 4⟩, ⟨17, 9, 13, 6⟩, ⟨17, 8, 13, 8⟩, ⟨17, 12, 12, 2⟩, ⟨17, 12, 11, 4⟩, ⟨17, 12, 10, 6⟩, ⟨17, 12, 9, 8⟩]
  exact AllWinning.cons node_24458 (AllWinning.cons node_24094 (AllWinning.cons node_23669 (AllWinning.cons node_23227 (AllWinning.cons node_24481 (AllWinning.cons node_24165 (AllWinning.cons node_23753 (AllWinning.cons node_23353 (AllWinning.cons node_24482 (AllWinning.cons node_24167 (AllWinning.cons node_23758 (AllWinning.cons node_23363 (AllWinning.nil))))))))))))

theorem node_24779 : Outcome ⟨17, 13, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 12, 2⟩, ⟨15, 13, 12, 4⟩, ⟨17, 12, 12, 2⟩, ⟨17, 11, 12, 4⟩, ⟨17, 13, 11, 2⟩, ⟨17, 13, 10, 4⟩]
  exact AllWinning.cons node_24461 (AllWinning.cons node_24098 (AllWinning.cons node_24482 (AllWinning.cons node_24166 (AllWinning.cons node_24484 (AllWinning.cons node_24168 (AllWinning.nil))))))

theorem node_24780 : Outcome ⟨17, 13, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 12, 2⟩, ⟨15, 13, 12, 4⟩, ⟨14, 13, 12, 6⟩, ⟨13, 13, 12, 8⟩, ⟨12, 13, 12, 10⟩, ⟨11, 13, 12, 12⟩, ⟨17, 12, 12, 2⟩, ⟨17, 11, 12, 4⟩, ⟨17, 10, 12, 6⟩, ⟨17, 9, 12, 8⟩, ⟨17, 8, 12, 10⟩, ⟨17, 7, 12, 12⟩, ⟨17, 13, 11, 2⟩, ⟨17, 13, 10, 4⟩, ⟨17, 13, 9, 6⟩, ⟨17, 13, 8, 8⟩, ⟨17, 13, 7, 10⟩, ⟨17, 13, 6, 12⟩]
  exact AllWinning.cons node_24461 (AllWinning.cons node_24098 (AllWinning.cons node_23672 (AllWinning.cons node_23230 (AllWinning.cons node_22677 (AllWinning.cons node_22068 (AllWinning.cons node_24482 (AllWinning.cons node_24166 (AllWinning.cons node_23755 (AllWinning.cons node_23356 (AllWinning.cons node_22890 (AllWinning.cons node_22330 (AllWinning.cons node_24484 (AllWinning.cons node_24168 (AllWinning.cons node_23759 (AllWinning.cons node_23365 (AllWinning.cons node_22900 (AllWinning.cons node_22344 (AllWinning.nil))))))))))))))))))

theorem node_24781 : Outcome ⟨17, 14, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 14, 11, 2⟩, ⟨15, 14, 11, 4⟩, ⟨17, 13, 11, 2⟩, ⟨17, 12, 11, 4⟩, ⟨17, 14, 10, 2⟩, ⟨17, 14, 9, 4⟩]
  exact AllWinning.cons node_24464 (AllWinning.cons node_24102 (AllWinning.cons node_24484 (AllWinning.cons node_24167 (AllWinning.cons node_24485 (AllWinning.cons node_24169 (AllWinning.nil))))))

theorem node_24782 : Outcome ⟨17, 14, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 14, 11, 2⟩, ⟨15, 14, 11, 4⟩, ⟨14, 14, 11, 6⟩, ⟨13, 14, 11, 8⟩, ⟨17, 13, 11, 2⟩, ⟨17, 12, 11, 4⟩, ⟨17, 11, 11, 6⟩, ⟨17, 10, 11, 8⟩, ⟨17, 14, 10, 2⟩, ⟨17, 14, 9, 4⟩, ⟨17, 14, 8, 6⟩, ⟨17, 14, 7, 8⟩]
  exact AllWinning.cons node_24464 (AllWinning.cons node_24102 (AllWinning.cons node_23675 (AllWinning.cons node_23232 (AllWinning.cons node_24484 (AllWinning.cons node_24167 (AllWinning.cons node_23756 (AllWinning.cons node_23358 (AllWinning.cons node_24485 (AllWinning.cons node_24169 (AllWinning.cons node_23761 (AllWinning.cons node_23367 (AllWinning.nil))))))))))))

theorem node_24783 : Outcome ⟨17, 15, 10, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 10, 4⟩) (by decide) node_24104

theorem node_24784 : Outcome ⟨17, 16, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 16, 9, 2⟩, ⟨15, 16, 9, 4⟩, ⟨17, 15, 9, 2⟩, ⟨17, 14, 9, 4⟩, ⟨17, 16, 8, 2⟩, ⟨17, 16, 7, 4⟩]
  exact AllWinning.cons node_24468 (AllWinning.cons node_24108 (AllWinning.cons node_24486 (AllWinning.cons node_24169 (AllWinning.cons node_24487 (AllWinning.cons node_24172 (AllWinning.nil))))))

theorem node_24785 : Outcome ⟨17, 16, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 16, 9, 2⟩, ⟨15, 16, 9, 4⟩, ⟨14, 16, 9, 6⟩, ⟨13, 16, 9, 8⟩, ⟨17, 15, 9, 2⟩, ⟨17, 14, 9, 4⟩, ⟨17, 13, 9, 6⟩, ⟨17, 12, 9, 8⟩, ⟨17, 16, 8, 2⟩, ⟨17, 16, 7, 4⟩, ⟨17, 16, 6, 6⟩, ⟨17, 16, 5, 8⟩]
  exact AllWinning.cons node_24468 (AllWinning.cons node_24108 (AllWinning.cons node_23679 (AllWinning.cons node_23237 (AllWinning.cons node_24486 (AllWinning.cons node_24169 (AllWinning.cons node_23759 (AllWinning.cons node_23363 (AllWinning.cons node_24487 (AllWinning.cons node_24172 (AllWinning.cons node_23765 (AllWinning.cons node_23370 (AllWinning.nil))))))))))))

theorem node_24786 : Outcome ⟨17, 17, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 8, 2⟩, ⟨15, 17, 8, 4⟩, ⟨17, 16, 8, 2⟩, ⟨17, 15, 8, 4⟩, ⟨17, 17, 7, 2⟩, ⟨17, 17, 6, 4⟩]
  exact AllWinning.cons node_24470 (AllWinning.cons node_24110 (AllWinning.cons node_24487 (AllWinning.cons node_24170 (AllWinning.cons node_24488 (AllWinning.cons node_24173 (AllWinning.nil))))))

theorem node_24787 : Outcome ⟨17, 17, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 8, 2⟩, ⟨15, 17, 8, 4⟩, ⟨14, 17, 8, 6⟩, ⟨13, 17, 8, 8⟩, ⟨17, 16, 8, 2⟩, ⟨17, 15, 8, 4⟩, ⟨17, 14, 8, 6⟩, ⟨17, 13, 8, 8⟩, ⟨17, 17, 7, 2⟩, ⟨17, 17, 6, 4⟩, ⟨17, 17, 5, 6⟩, ⟨17, 17, 4, 8⟩]
  exact AllWinning.cons node_24470 (AllWinning.cons node_24110 (AllWinning.cons node_23681 (AllWinning.cons node_23240 (AllWinning.cons node_24487 (AllWinning.cons node_24170 (AllWinning.cons node_23761 (AllWinning.cons node_23365 (AllWinning.cons node_24488 (AllWinning.cons node_24173 (AllWinning.cons node_23768 (AllWinning.cons node_23372 (AllWinning.nil))))))))))))

theorem node_24788 : Outcome ⟨18, 5, 19, 2⟩ true :=
  Outcome.win (q := ⟨18, 4, 19, 2⟩) (by decide) node_24490

theorem node_24789 : Outcome ⟨18, 5, 19, 4⟩ true :=
  Outcome.win (q := ⟨18, 1, 19, 8⟩) (by decide) node_23377

theorem node_24790 : Outcome ⟨18, 6, 18, 4⟩ true :=
  Outcome.win (q := ⟨18, 5, 18, 2⟩) (by decide) node_24491

theorem node_24791 : Outcome ⟨18, 7, 17, 4⟩ true :=
  Outcome.win (q := ⟨18, 7, 13, 8⟩) (by decide) node_23387

theorem node_24792 : Outcome ⟨18, 8, 16, 4⟩ true :=
  Outcome.win (q := ⟨16, 8, 16, 4⟩) (by decide) node_24121

theorem node_24793 : Outcome ⟨18, 9, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 9, 15, 2⟩, ⟨16, 9, 15, 4⟩, ⟨18, 8, 15, 2⟩, ⟨18, 7, 15, 4⟩, ⟨18, 9, 14, 2⟩, ⟨18, 9, 13, 4⟩]
  exact AllWinning.cons node_24479 (AllWinning.cons node_24125 (AllWinning.cons node_24495 (AllWinning.cons node_24182 (AllWinning.cons node_24497 (AllWinning.cons node_24185 (AllWinning.nil))))))

theorem node_24794 : Outcome ⟨18, 10, 14, 4⟩ true :=
  Outcome.win (q := ⟨16, 10, 14, 4⟩) (by decide) node_24128

theorem node_24795 : Outcome ⟨18, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨18, 7, 13, 8⟩) (by decide) node_23387

theorem node_24796 : Outcome ⟨18, 12, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 12, 4⟩) (by decide) node_24136

theorem node_24797 : Outcome ⟨18, 12, 12, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 12, 4⟩) (by decide) node_24136

theorem node_24798 : Outcome ⟨18, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨18, 13, 7, 8⟩) (by decide) node_23400

theorem node_24799 : Outcome ⟨18, 14, 10, 4⟩ true :=
  Outcome.win (q := ⟨16, 14, 10, 4⟩) (by decide) node_24143

theorem node_24800 : Outcome ⟨18, 15, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 15, 9, 2⟩, ⟨16, 15, 9, 4⟩, ⟨18, 14, 9, 2⟩, ⟨18, 13, 9, 4⟩, ⟨18, 15, 8, 2⟩, ⟨18, 15, 7, 4⟩]
  exact AllWinning.cons node_24486 (AllWinning.cons node_24147 (AllWinning.cons node_24503 (AllWinning.cons node_24191 (AllWinning.cons node_24505 (AllWinning.cons node_24196 (AllWinning.nil))))))

theorem node_24801 : Outcome ⟨18, 16, 8, 4⟩ true :=
  Outcome.win (q := ⟨16, 16, 8, 4⟩) (by decide) node_24149

theorem node_24802 : Outcome ⟨18, 18, 6, 4⟩ true :=
  Outcome.win (q := ⟨18, 18, 5, 2⟩) (by decide) node_24508

theorem node_24803 : Outcome ⟨18, 19, 5, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 5, 2⟩) (by decide) node_24508

theorem node_24804 : Outcome ⟨19, 4, 19, 2⟩ true :=
  Outcome.win (q := ⟨18, 4, 19, 2⟩) (by decide) node_24490

theorem node_24805 : Outcome ⟨19, 4, 19, 8⟩ true :=
  Outcome.win (q := ⟨14, 4, 19, 10⟩) (by decide) node_22744

theorem node_24806 : Outcome ⟨19, 5, 18, 2⟩ true :=
  Outcome.win (q := ⟨18, 5, 18, 2⟩) (by decide) node_24491

theorem node_24807 : Outcome ⟨19, 7, 16, 8⟩ true :=
  Outcome.win (q := ⟨18, 7, 16, 2⟩) (by decide) node_24494

theorem node_24808 : Outcome ⟨19, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨19, 8, 13, 4⟩) (by decide) node_24207

theorem node_24809 : Outcome ⟨19, 8, 15, 8⟩ true :=
  Outcome.win (q := ⟨19, 8, 13, 4⟩) (by decide) node_24207

theorem node_24810 : Outcome ⟨19, 9, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 9, 14, 2⟩, ⟨17, 9, 14, 4⟩, ⟨19, 8, 14, 2⟩, ⟨19, 7, 14, 4⟩, ⟨19, 9, 13, 2⟩, ⟨19, 9, 12, 4⟩]
  exact AllWinning.cons node_24497 (AllWinning.cons node_24164 (AllWinning.cons node_24515 (AllWinning.cons node_24205 (AllWinning.cons node_24516 (AllWinning.cons node_24210 (AllWinning.nil))))))

theorem node_24811 : Outcome ⟨19, 10, 13, 4⟩ true :=
  Outcome.win (q := ⟨19, 8, 13, 4⟩) (by decide) node_24207

theorem node_24812 : Outcome ⟨19, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨19, 11, 10, 4⟩) (by decide) node_24215

theorem node_24813 : Outcome ⟨19, 11, 12, 8⟩ true :=
  Outcome.win (q := ⟨19, 11, 10, 4⟩) (by decide) node_24215

theorem node_24814 : Outcome ⟨19, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨19, 10, 11, 4⟩) (by decide) node_24213

theorem node_24815 : Outcome ⟨19, 12, 11, 8⟩ true :=
  Outcome.win (q := ⟨19, 10, 11, 4⟩) (by decide) node_24213

theorem node_24816 : Outcome ⟨19, 13, 10, 4⟩ true :=
  Outcome.win (q := ⟨19, 11, 10, 4⟩) (by decide) node_24215

theorem node_24817 : Outcome ⟨19, 14, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 14, 9, 2⟩, ⟨17, 14, 9, 4⟩, ⟨19, 13, 9, 2⟩, ⟨19, 12, 9, 4⟩, ⟨19, 14, 8, 2⟩, ⟨19, 14, 7, 4⟩]
  exact AllWinning.cons node_24503 (AllWinning.cons node_24169 (AllWinning.cons node_24520 (AllWinning.cons node_24217 (AllWinning.cons node_24521 (AllWinning.cons node_24223 (AllWinning.nil))))))

theorem node_24818 : Outcome ⟨19, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨19, 13, 8, 4⟩) (by decide) node_24220

theorem node_24819 : Outcome ⟨19, 15, 8, 8⟩ true :=
  Outcome.win (q := ⟨19, 13, 8, 4⟩) (by decide) node_24220

theorem node_24820 : Outcome ⟨19, 16, 7, 8⟩ true :=
  Outcome.win (q := ⟨18, 16, 7, 2⟩) (by decide) node_24507

theorem node_24821 : Outcome ⟨19, 18, 5, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 5, 2⟩) (by decide) node_24508

theorem node_24822 : Outcome ⟨19, 19, 4, 2⟩ true :=
  Outcome.win (q := ⟨18, 19, 4, 2⟩) (by decide) node_24511

theorem node_24823 : Outcome ⟨19, 19, 4, 8⟩ true :=
  Outcome.win (q := ⟨14, 19, 4, 10⟩) (by decide) node_22794

theorem node_24824 : Outcome ⟨3, 20, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 20, 20, 2⟩, ⟨1, 20, 20, 4⟩, ⟨3, 19, 20, 2⟩, ⟨3, 18, 20, 4⟩, ⟨3, 20, 19, 2⟩, ⟨3, 20, 18, 4⟩]
  exact AllWinning.cons node_24525 (AllWinning.cons node_24227 (AllWinning.cons node_24528 (AllWinning.cons node_24231 (AllWinning.cons node_24529 (AllWinning.cons node_24236 (AllWinning.nil))))))

theorem node_24825 : Outcome ⟨3, 20, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 20, 20, 6⟩) (by decide) node_23811

theorem node_24826 : Outcome ⟨3, 20, 20, 10⟩ true :=
  Outcome.win (q := ⟨0, 20, 20, 6⟩) (by decide) node_23811

theorem node_24827 : Outcome ⟨4, 19, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 19, 20, 2⟩, ⟨2, 19, 20, 4⟩, ⟨4, 18, 20, 2⟩, ⟨4, 17, 20, 4⟩, ⟨4, 19, 19, 2⟩, ⟨4, 19, 18, 4⟩]
  exact AllWinning.cons node_24528 (AllWinning.cons node_24229 (AllWinning.cons node_24530 (AllWinning.cons node_24238 (AllWinning.cons node_24532 (AllWinning.cons node_24243 (AllWinning.nil))))))

theorem node_24828 : Outcome ⟨4, 20, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 20, 19, 2⟩, ⟨2, 20, 19, 4⟩, ⟨4, 19, 19, 2⟩, ⟨4, 18, 19, 4⟩, ⟨4, 20, 18, 2⟩, ⟨4, 20, 17, 4⟩]
  exact AllWinning.cons node_24529 (AllWinning.cons node_24230 (AllWinning.cons node_24532 (AllWinning.cons node_24240 (AllWinning.cons node_24534 (AllWinning.cons node_24245 (AllWinning.nil))))))

theorem node_24829 : Outcome ⟨5, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 18, 4⟩) (by decide) node_24251

theorem node_24830 : Outcome ⟨5, 18, 20, 8⟩ true :=
  Outcome.win (q := ⟨5, 18, 12, 16⟩) (by decide) node_21304

theorem node_24831 : Outcome ⟨5, 19, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 19, 2⟩, ⟨3, 19, 19, 4⟩, ⟨5, 18, 19, 2⟩, ⟨5, 17, 19, 4⟩, ⟨5, 19, 18, 2⟩, ⟨5, 19, 17, 4⟩]
  exact AllWinning.cons node_24532 (AllWinning.cons node_24234 (AllWinning.cons node_24537 (AllWinning.cons node_24249 (AllWinning.cons node_24539 (AllWinning.cons node_24254 (AllWinning.nil))))))

theorem node_24832 : Outcome ⟨5, 19, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 19, 2⟩, ⟨3, 19, 19, 4⟩, ⟨2, 19, 19, 6⟩, ⟨1, 19, 19, 8⟩, ⟨5, 18, 19, 2⟩, ⟨5, 17, 19, 4⟩, ⟨5, 16, 19, 6⟩, ⟨5, 15, 19, 8⟩, ⟨5, 19, 18, 2⟩, ⟨5, 19, 17, 4⟩, ⟨5, 19, 16, 6⟩, ⟨5, 19, 15, 8⟩]
  exact AllWinning.cons node_24532 (AllWinning.cons node_24234 (AllWinning.cons node_23817 (AllWinning.cons node_23428 (AllWinning.cons node_24537 (AllWinning.cons node_24249 (AllWinning.cons node_23841 (AllWinning.cons node_23464 (AllWinning.cons node_24539 (AllWinning.cons node_24254 (AllWinning.cons node_23845 (AllWinning.cons node_23472 (AllWinning.nil))))))))))))

theorem node_24833 : Outcome ⟨5, 19, 19, 6⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 10⟩) (by decide) node_22949

theorem node_24834 : Outcome ⟨5, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 18, 4⟩) (by decide) node_24251

theorem node_24835 : Outcome ⟨5, 20, 18, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 18, 16⟩) (by decide) node_21284

theorem node_24836 : Outcome ⟨6, 17, 20, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 20, 4⟩) (by decide) node_24258

theorem node_24837 : Outcome ⟨6, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 19, 2⟩) (by decide) node_24543

theorem node_24838 : Outcome ⟨6, 18, 19, 8⟩ true :=
  Outcome.win (q := ⟨1, 18, 19, 10⟩) (by decide) node_22955

theorem node_24839 : Outcome ⟨6, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨6, 19, 17, 2⟩) (by decide) node_24545

theorem node_24840 : Outcome ⟨6, 19, 18, 8⟩ true :=
  Outcome.win (q := ⟨1, 19, 18, 10⟩) (by decide) node_22960

theorem node_24841 : Outcome ⟨6, 20, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 20, 15, 4⟩) (by decide) node_24269

theorem node_24842 : Outcome ⟨7, 16, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 20, 2⟩, ⟨5, 16, 20, 4⟩, ⟨7, 15, 20, 2⟩, ⟨7, 14, 20, 4⟩, ⟨7, 16, 19, 2⟩, ⟨7, 16, 18, 4⟩]
  exact AllWinning.cons node_24542 (AllWinning.cons node_24246 (AllWinning.cons node_24547 (AllWinning.cons node_24273 (AllWinning.cons node_24549 (AllWinning.cons node_24276 (AllWinning.nil))))))

theorem node_24843 : Outcome ⟨7, 16, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 20, 2⟩, ⟨5, 16, 20, 4⟩, ⟨4, 16, 20, 6⟩, ⟨3, 16, 20, 8⟩, ⟨7, 15, 20, 2⟩, ⟨7, 14, 20, 4⟩, ⟨7, 13, 20, 6⟩, ⟨7, 12, 20, 8⟩, ⟨7, 16, 19, 2⟩, ⟨7, 16, 18, 4⟩, ⟨7, 16, 17, 6⟩, ⟨7, 16, 16, 8⟩]
  exact AllWinning.cons node_24542 (AllWinning.cons node_24246 (AllWinning.cons node_23830 (AllWinning.cons node_23438 (AllWinning.cons node_24547 (AllWinning.cons node_24273 (AllWinning.cons node_23859 (AllWinning.cons node_23491 (AllWinning.cons node_24549 (AllWinning.cons node_24276 (AllWinning.cons node_23869 (AllWinning.cons node_23498 (AllWinning.nil))))))))))))

theorem node_24844 : Outcome ⟨7, 16, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 20, 2⟩, ⟨5, 16, 20, 4⟩, ⟨4, 16, 20, 6⟩, ⟨3, 16, 20, 8⟩, ⟨2, 16, 20, 10⟩, ⟨1, 16, 20, 12⟩, ⟨7, 15, 20, 2⟩, ⟨7, 14, 20, 4⟩, ⟨7, 13, 20, 6⟩, ⟨7, 12, 20, 8⟩, ⟨7, 11, 20, 10⟩, ⟨7, 10, 20, 12⟩, ⟨7, 16, 19, 2⟩, ⟨7, 16, 18, 4⟩, ⟨7, 16, 17, 6⟩, ⟨7, 16, 16, 8⟩, ⟨7, 16, 15, 10⟩, ⟨7, 16, 14, 12⟩]
  exact AllWinning.cons node_24542 (AllWinning.cons node_24246 (AllWinning.cons node_23830 (AllWinning.cons node_23438 (AllWinning.cons node_22964 (AllWinning.cons node_22405 (AllWinning.cons node_24547 (AllWinning.cons node_24273 (AllWinning.cons node_23859 (AllWinning.cons node_23491 (AllWinning.cons node_23039 (AllWinning.cons node_22505 (AllWinning.cons node_24549 (AllWinning.cons node_24276 (AllWinning.cons node_23869 (AllWinning.cons node_23498 (AllWinning.cons node_23052 (AllWinning.cons node_22519 (AllWinning.nil))))))))))))))))))

theorem node_24845 : Outcome ⟨7, 16, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 20, 2⟩, ⟨5, 16, 20, 4⟩, ⟨4, 16, 20, 6⟩, ⟨3, 16, 20, 8⟩, ⟨2, 16, 20, 10⟩, ⟨1, 16, 20, 12⟩, ⟨0, 16, 20, 14⟩, ⟨7, 15, 20, 2⟩, ⟨7, 14, 20, 4⟩, ⟨7, 13, 20, 6⟩, ⟨7, 12, 20, 8⟩, ⟨7, 11, 20, 10⟩, ⟨7, 10, 20, 12⟩, ⟨7, 9, 20, 14⟩, ⟨7, 8, 20, 16⟩, ⟨7, 7, 20, 18⟩, ⟨7, 6, 20, 20⟩, ⟨7, 16, 19, 2⟩, ⟨7, 16, 18, 4⟩, ⟨7, 16, 17, 6⟩, ⟨7, 16, 16, 8⟩, ⟨7, 16, 15, 10⟩, ⟨7, 16, 14, 12⟩, ⟨7, 16, 13, 14⟩, ⟨7, 16, 12, 16⟩, ⟨7, 16, 11, 18⟩, ⟨7, 16, 10, 20⟩]
  exact AllWinning.cons node_24542 (AllWinning.cons node_24246 (AllWinning.cons node_23830 (AllWinning.cons node_23438 (AllWinning.cons node_22964 (AllWinning.cons node_22405 (AllWinning.cons node_21778 (AllWinning.cons node_24547 (AllWinning.cons node_24273 (AllWinning.cons node_23859 (AllWinning.cons node_23491 (AllWinning.cons node_23039 (AllWinning.cons node_22505 (AllWinning.cons node_21929 (AllWinning.cons node_21341 (AllWinning.cons node_20591 (AllWinning.cons node_19889 (AllWinning.cons node_24549 (AllWinning.cons node_24276 (AllWinning.cons node_23869 (AllWinning.cons node_23498 (AllWinning.cons node_23052 (AllWinning.cons node_22519 (AllWinning.cons node_21946 (AllWinning.cons node_21353 (AllWinning.cons node_20632 (AllWinning.cons node_19906 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_24846 : Outcome ⟨7, 16, 20, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 16, 20, 2⟩, ⟨5, 16, 20, 4⟩, ⟨4, 16, 20, 6⟩, ⟨3, 16, 20, 8⟩, ⟨2, 16, 20, 10⟩, ⟨1, 16, 20, 12⟩, ⟨0, 16, 20, 14⟩, ⟨7, 15, 20, 2⟩, ⟨7, 14, 20, 4⟩, ⟨7, 13, 20, 6⟩, ⟨7, 12, 20, 8⟩, ⟨7, 11, 20, 10⟩, ⟨7, 10, 20, 12⟩, ⟨7, 9, 20, 14⟩, ⟨7, 8, 20, 16⟩, ⟨7, 7, 20, 18⟩, ⟨7, 6, 20, 20⟩, ⟨7, 5, 20, 22⟩, ⟨7, 4, 20, 24⟩, ⟨7, 16, 19, 2⟩, ⟨7, 16, 18, 4⟩, ⟨7, 16, 17, 6⟩, ⟨7, 16, 16, 8⟩, ⟨7, 16, 15, 10⟩, ⟨7, 16, 14, 12⟩, ⟨7, 16, 13, 14⟩, ⟨7, 16, 12, 16⟩, ⟨7, 16, 11, 18⟩, ⟨7, 16, 10, 20⟩, ⟨7, 16, 9, 22⟩, ⟨7, 16, 8, 24⟩]
  exact AllWinning.cons node_24542 (AllWinning.cons node_24246 (AllWinning.cons node_23830 (AllWinning.cons node_23438 (AllWinning.cons node_22964 (AllWinning.cons node_22405 (AllWinning.cons node_21778 (AllWinning.cons node_24547 (AllWinning.cons node_24273 (AllWinning.cons node_23859 (AllWinning.cons node_23491 (AllWinning.cons node_23039 (AllWinning.cons node_22505 (AllWinning.cons node_21929 (AllWinning.cons node_21341 (AllWinning.cons node_20591 (AllWinning.cons node_19889 (AllWinning.cons node_19056 (AllWinning.cons node_18137 (AllWinning.cons node_24549 (AllWinning.cons node_24276 (AllWinning.cons node_23869 (AllWinning.cons node_23498 (AllWinning.cons node_23052 (AllWinning.cons node_22519 (AllWinning.cons node_21946 (AllWinning.cons node_21353 (AllWinning.cons node_20632 (AllWinning.cons node_19906 (AllWinning.cons node_19084 (AllWinning.cons node_18176 (AllWinning.nil)))))))))))))))))))))))))))))))

theorem node_24847 : Outcome ⟨7, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 19, 2⟩) (by decide) node_24543

theorem node_24848 : Outcome ⟨7, 17, 19, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 19, 2⟩) (by decide) node_24543

theorem node_24849 : Outcome ⟨7, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨5, 18, 18, 4⟩) (by decide) node_24251

theorem node_24850 : Outcome ⟨7, 18, 18, 12⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 14⟩) (by decide) node_21783

theorem node_24851 : Outcome ⟨7, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 19, 17, 2⟩) (by decide) node_24545

theorem node_24852 : Outcome ⟨7, 19, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 19, 17, 2⟩) (by decide) node_24545

theorem node_24853 : Outcome ⟨7, 20, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 16, 2⟩, ⟨5, 20, 16, 4⟩, ⟨7, 19, 16, 2⟩, ⟨7, 18, 16, 4⟩, ⟨7, 20, 15, 2⟩, ⟨7, 20, 14, 4⟩]
  exact AllWinning.cons node_24546 (AllWinning.cons node_24255 (AllWinning.cons node_24554 (AllWinning.cons node_24281 (AllWinning.cons node_24557 (AllWinning.cons node_24285 (AllWinning.nil))))))

theorem node_24854 : Outcome ⟨7, 20, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 16, 2⟩, ⟨5, 20, 16, 4⟩, ⟨4, 20, 16, 6⟩, ⟨3, 20, 16, 8⟩, ⟨7, 19, 16, 2⟩, ⟨7, 18, 16, 4⟩, ⟨7, 17, 16, 6⟩, ⟨7, 16, 16, 8⟩, ⟨7, 20, 15, 2⟩, ⟨7, 20, 14, 4⟩, ⟨7, 20, 13, 6⟩, ⟨7, 20, 12, 8⟩]
  exact AllWinning.cons node_24546 (AllWinning.cons node_24255 (AllWinning.cons node_23838 (AllWinning.cons node_23447 (AllWinning.cons node_24554 (AllWinning.cons node_24281 (AllWinning.cons node_23872 (AllWinning.cons node_23498 (AllWinning.cons node_24557 (AllWinning.cons node_24285 (AllWinning.cons node_23880 (AllWinning.cons node_23505 (AllWinning.nil))))))))))))

theorem node_24855 : Outcome ⟨7, 20, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 16, 2⟩, ⟨5, 20, 16, 4⟩, ⟨4, 20, 16, 6⟩, ⟨3, 20, 16, 8⟩, ⟨2, 20, 16, 10⟩, ⟨1, 20, 16, 12⟩, ⟨7, 19, 16, 2⟩, ⟨7, 18, 16, 4⟩, ⟨7, 17, 16, 6⟩, ⟨7, 16, 16, 8⟩, ⟨7, 15, 16, 10⟩, ⟨7, 14, 16, 12⟩, ⟨7, 20, 15, 2⟩, ⟨7, 20, 14, 4⟩, ⟨7, 20, 13, 6⟩, ⟨7, 20, 12, 8⟩, ⟨7, 20, 11, 10⟩, ⟨7, 20, 10, 12⟩]
  exact AllWinning.cons node_24546 (AllWinning.cons node_24255 (AllWinning.cons node_23838 (AllWinning.cons node_23447 (AllWinning.cons node_22976 (AllWinning.cons node_22413 (AllWinning.cons node_24554 (AllWinning.cons node_24281 (AllWinning.cons node_23872 (AllWinning.cons node_23498 (AllWinning.cons node_23050 (AllWinning.cons node_22515 (AllWinning.cons node_24557 (AllWinning.cons node_24285 (AllWinning.cons node_23880 (AllWinning.cons node_23505 (AllWinning.cons node_23064 (AllWinning.cons node_22528 (AllWinning.nil))))))))))))))))))

theorem node_24856 : Outcome ⟨7, 20, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 16, 2⟩, ⟨5, 20, 16, 4⟩, ⟨4, 20, 16, 6⟩, ⟨3, 20, 16, 8⟩, ⟨2, 20, 16, 10⟩, ⟨1, 20, 16, 12⟩, ⟨0, 20, 16, 14⟩, ⟨7, 19, 16, 2⟩, ⟨7, 18, 16, 4⟩, ⟨7, 17, 16, 6⟩, ⟨7, 16, 16, 8⟩, ⟨7, 15, 16, 10⟩, ⟨7, 14, 16, 12⟩, ⟨7, 13, 16, 14⟩, ⟨7, 12, 16, 16⟩, ⟨7, 11, 16, 18⟩, ⟨7, 10, 16, 20⟩, ⟨7, 20, 15, 2⟩, ⟨7, 20, 14, 4⟩, ⟨7, 20, 13, 6⟩, ⟨7, 20, 12, 8⟩, ⟨7, 20, 11, 10⟩, ⟨7, 20, 10, 12⟩, ⟨7, 20, 9, 14⟩, ⟨7, 20, 8, 16⟩, ⟨7, 20, 7, 18⟩, ⟨7, 20, 6, 20⟩]
  exact AllWinning.cons node_24546 (AllWinning.cons node_24255 (AllWinning.cons node_23838 (AllWinning.cons node_23447 (AllWinning.cons node_22976 (AllWinning.cons node_22413 (AllWinning.cons node_21788 (AllWinning.cons node_24554 (AllWinning.cons node_24281 (AllWinning.cons node_23872 (AllWinning.cons node_23498 (AllWinning.cons node_23050 (AllWinning.cons node_22515 (AllWinning.cons node_21938 (AllWinning.cons node_21345 (AllWinning.cons node_20606 (AllWinning.cons node_19896 (AllWinning.cons node_24557 (AllWinning.cons node_24285 (AllWinning.cons node_23880 (AllWinning.cons node_23505 (AllWinning.cons node_23064 (AllWinning.cons node_22528 (AllWinning.cons node_21953 (AllWinning.cons node_21361 (AllWinning.cons node_20641 (AllWinning.cons node_19913 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_24857 : Outcome ⟨7, 20, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 16, 2⟩, ⟨5, 20, 16, 4⟩, ⟨4, 20, 16, 6⟩, ⟨3, 20, 16, 8⟩, ⟨2, 20, 16, 10⟩, ⟨1, 20, 16, 12⟩, ⟨0, 20, 16, 14⟩, ⟨7, 19, 16, 2⟩, ⟨7, 18, 16, 4⟩, ⟨7, 17, 16, 6⟩, ⟨7, 16, 16, 8⟩, ⟨7, 15, 16, 10⟩, ⟨7, 14, 16, 12⟩, ⟨7, 13, 16, 14⟩, ⟨7, 12, 16, 16⟩, ⟨7, 11, 16, 18⟩, ⟨7, 10, 16, 20⟩, ⟨7, 9, 16, 22⟩, ⟨7, 8, 16, 24⟩, ⟨7, 20, 15, 2⟩, ⟨7, 20, 14, 4⟩, ⟨7, 20, 13, 6⟩, ⟨7, 20, 12, 8⟩, ⟨7, 20, 11, 10⟩, ⟨7, 20, 10, 12⟩, ⟨7, 20, 9, 14⟩, ⟨7, 20, 8, 16⟩, ⟨7, 20, 7, 18⟩, ⟨7, 20, 6, 20⟩, ⟨7, 20, 5, 22⟩, ⟨7, 20, 4, 24⟩]
  exact AllWinning.cons node_24546 (AllWinning.cons node_24255 (AllWinning.cons node_23838 (AllWinning.cons node_23447 (AllWinning.cons node_22976 (AllWinning.cons node_22413 (AllWinning.cons node_21788 (AllWinning.cons node_24554 (AllWinning.cons node_24281 (AllWinning.cons node_23872 (AllWinning.cons node_23498 (AllWinning.cons node_23050 (AllWinning.cons node_22515 (AllWinning.cons node_21938 (AllWinning.cons node_21345 (AllWinning.cons node_20606 (AllWinning.cons node_19896 (AllWinning.cons node_19069 (AllWinning.cons node_18148 (AllWinning.cons node_24557 (AllWinning.cons node_24285 (AllWinning.cons node_23880 (AllWinning.cons node_23505 (AllWinning.cons node_23064 (AllWinning.cons node_22528 (AllWinning.cons node_21953 (AllWinning.cons node_21361 (AllWinning.cons node_20641 (AllWinning.cons node_19913 (AllWinning.cons node_19098 (AllWinning.cons node_18188 (AllWinning.nil)))))))))))))))))))))))))))))))

theorem node_24858 : Outcome ⟨8, 15, 20, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 20, 4⟩) (by decide) node_24258

theorem node_24859 : Outcome ⟨8, 15, 20, 10⟩ true :=
  Outcome.win (q := ⟨6, 15, 20, 4⟩) (by decide) node_24258

theorem node_24860 : Outcome ⟨8, 16, 19, 6⟩ true :=
  Outcome.win (q := ⟨8, 13, 19, 6⟩) (by decide) node_23886

theorem node_24861 : Outcome ⟨8, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 2⟩) (by decide) node_24565

theorem node_24862 : Outcome ⟨8, 17, 18, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 2⟩) (by decide) node_24565

theorem node_24863 : Outcome ⟨8, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 2⟩) (by decide) node_24565

theorem node_24864 : Outcome ⟨8, 18, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 2⟩) (by decide) node_24565

theorem node_24865 : Outcome ⟨8, 19, 16, 6⟩ true :=
  Outcome.win (q := ⟨8, 16, 16, 6⟩) (by decide) node_23894

theorem node_24866 : Outcome ⟨8, 20, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 20, 15, 4⟩) (by decide) node_24269

theorem node_24867 : Outcome ⟨8, 20, 15, 10⟩ true :=
  Outcome.win (q := ⟨6, 20, 15, 4⟩) (by decide) node_24269

theorem node_24868 : Outcome ⟨9, 14, 20, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 20, 2⟩) (by decide) node_24574

theorem node_24869 : Outcome ⟨9, 14, 20, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 10⟩) (by decide) node_23086

theorem node_24870 : Outcome ⟨9, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 19, 2⟩) (by decide) node_24577

theorem node_24871 : Outcome ⟨9, 15, 19, 4⟩ true :=
  Outcome.win (q := ⟨9, 14, 19, 2⟩) (by decide) node_24577

theorem node_24872 : Outcome ⟨9, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨9, 15, 18, 2⟩) (by decide) node_24579

theorem node_24873 : Outcome ⟨9, 16, 18, 8⟩ true :=
  Outcome.win (q := ⟨2, 16, 18, 14⟩) (by decide) node_21809

theorem node_24874 : Outcome ⟨9, 16, 18, 12⟩ true :=
  Outcome.win (q := ⟨2, 16, 18, 14⟩) (by decide) node_21809

theorem node_24875 : Outcome ⟨9, 17, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 2⟩) (by decide) node_24565

theorem node_24876 : Outcome ⟨9, 17, 17, 8⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 2⟩) (by decide) node_24565

theorem node_24877 : Outcome ⟨9, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨9, 17, 16, 2⟩) (by decide) node_24588

theorem node_24878 : Outcome ⟨9, 18, 16, 8⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 14⟩) (by decide) node_21819

theorem node_24879 : Outcome ⟨9, 18, 16, 12⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 14⟩) (by decide) node_21819

theorem node_24880 : Outcome ⟨9, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨9, 18, 15, 2⟩) (by decide) node_24593

theorem node_24881 : Outcome ⟨9, 19, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 18, 15, 2⟩) (by decide) node_24593

theorem node_24882 : Outcome ⟨9, 20, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 19, 14, 2⟩) (by decide) node_24597

theorem node_24883 : Outcome ⟨9, 20, 14, 8⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 10⟩) (by decide) node_23116

theorem node_24884 : Outcome ⟨10, 13, 20, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 20, 2⟩) (by decide) node_24574

theorem node_24885 : Outcome ⟨10, 13, 20, 10⟩ true :=
  Outcome.win (q := ⟨9, 13, 20, 2⟩) (by decide) node_24574

theorem node_24886 : Outcome ⟨10, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 19, 2⟩) (by decide) node_24577

theorem node_24887 : Outcome ⟨10, 14, 19, 8⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 12⟩) (by decide) node_22441

theorem node_24888 : Outcome ⟨10, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨9, 15, 18, 2⟩) (by decide) node_24579

theorem node_24889 : Outcome ⟨10, 15, 18, 8⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 14⟩) (by decide) node_21832

theorem node_24890 : Outcome ⟨10, 15, 18, 12⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 14⟩) (by decide) node_21832

theorem node_24891 : Outcome ⟨10, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨9, 16, 17, 2⟩) (by decide) node_24583

theorem node_24892 : Outcome ⟨10, 16, 17, 8⟩ true :=
  Outcome.win (q := ⟨10, 10, 17, 12⟩) (by decide) node_22599

theorem node_24893 : Outcome ⟨10, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨9, 17, 16, 2⟩) (by decide) node_24588

theorem node_24894 : Outcome ⟨10, 17, 16, 8⟩ true :=
  Outcome.win (q := ⟨10, 17, 10, 12⟩) (by decide) node_22618

theorem node_24895 : Outcome ⟨10, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨9, 18, 15, 2⟩) (by decide) node_24593

theorem node_24896 : Outcome ⟨10, 18, 15, 8⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 14⟩) (by decide) node_21845

theorem node_24897 : Outcome ⟨10, 18, 15, 12⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 14⟩) (by decide) node_21845

theorem node_24898 : Outcome ⟨10, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 19, 14, 2⟩) (by decide) node_24597

theorem node_24899 : Outcome ⟨10, 19, 14, 8⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 12⟩) (by decide) node_22452

theorem node_24900 : Outcome ⟨10, 20, 13, 2⟩ true :=
  Outcome.win (q := ⟨9, 20, 13, 2⟩) (by decide) node_24599

theorem node_24901 : Outcome ⟨10, 20, 13, 10⟩ true :=
  Outcome.win (q := ⟨9, 20, 13, 2⟩) (by decide) node_24599

theorem node_24902 : Outcome ⟨11, 13, 19, 6⟩ true :=
  Outcome.win (q := ⟨8, 13, 19, 6⟩) (by decide) node_23886

theorem node_24903 : Outcome ⟨11, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨11, 14, 17, 2⟩) (by decide) node_24619

theorem node_24904 : Outcome ⟨11, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 14, 17, 2⟩) (by decide) node_24619

theorem node_24905 : Outcome ⟨11, 16, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 16, 2⟩, ⟨9, 16, 16, 4⟩, ⟨11, 15, 16, 2⟩, ⟨11, 14, 16, 4⟩, ⟨11, 16, 15, 2⟩, ⟨11, 16, 14, 4⟩]
  exact AllWinning.cons node_24606 (AllWinning.cons node_24312 (AllWinning.cons node_24622 (AllWinning.cons node_24337 (AllWinning.cons node_24624 (AllWinning.cons node_24341 (AllWinning.nil))))))

theorem node_24906 : Outcome ⟨11, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨8, 16, 16, 6⟩) (by decide) node_23894

theorem node_24907 : Outcome ⟨11, 16, 16, 6⟩ true :=
  Outcome.win (q := ⟨8, 16, 16, 6⟩) (by decide) node_23894

theorem node_24908 : Outcome ⟨11, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 14, 2⟩) (by decide) node_24626

theorem node_24909 : Outcome ⟨11, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 14, 2⟩) (by decide) node_24626

theorem node_24910 : Outcome ⟨11, 19, 13, 6⟩ true :=
  Outcome.win (q := ⟨8, 19, 13, 6⟩) (by decide) node_23901

theorem node_24911 : Outcome ⟨12, 12, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 19, 2⟩, ⟨10, 12, 19, 4⟩, ⟨12, 11, 19, 2⟩, ⟨12, 10, 19, 4⟩, ⟨12, 12, 18, 2⟩, ⟨12, 12, 17, 4⟩]
  exact AllWinning.cons node_24616 (AllWinning.cons node_24322 (AllWinning.cons node_24635 (AllWinning.cons node_24349 (AllWinning.cons node_24637 (AllWinning.cons node_24352 (AllWinning.nil))))))

theorem node_24912 : Outcome ⟨12, 12, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 19, 2⟩, ⟨10, 12, 19, 4⟩, ⟨9, 12, 19, 6⟩, ⟨8, 12, 19, 8⟩, ⟨12, 11, 19, 2⟩, ⟨12, 10, 19, 4⟩, ⟨12, 9, 19, 6⟩, ⟨12, 8, 19, 8⟩, ⟨12, 12, 18, 2⟩, ⟨12, 12, 17, 4⟩, ⟨12, 12, 16, 6⟩, ⟨12, 12, 15, 8⟩]
  exact AllWinning.cons node_24616 (AllWinning.cons node_24322 (AllWinning.cons node_23909 (AllWinning.cons node_23509 (AllWinning.cons node_24635 (AllWinning.cons node_24349 (AllWinning.cons node_23986 (AllWinning.cons node_23594 (AllWinning.cons node_24637 (AllWinning.cons node_24352 (AllWinning.cons node_23992 (AllWinning.cons node_23603 (AllWinning.nil))))))))))))

theorem node_24913 : Outcome ⟨12, 12, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 19, 2⟩, ⟨10, 12, 19, 4⟩, ⟨9, 12, 19, 6⟩, ⟨8, 12, 19, 8⟩, ⟨7, 12, 19, 10⟩, ⟨6, 12, 19, 12⟩, ⟨5, 12, 19, 14⟩, ⟨4, 12, 19, 16⟩, ⟨12, 11, 19, 2⟩, ⟨12, 10, 19, 4⟩, ⟨12, 9, 19, 6⟩, ⟨12, 8, 19, 8⟩, ⟨12, 7, 19, 10⟩, ⟨12, 6, 19, 12⟩, ⟨12, 5, 19, 14⟩, ⟨12, 4, 19, 16⟩, ⟨12, 12, 18, 2⟩, ⟨12, 12, 17, 4⟩, ⟨12, 12, 16, 6⟩, ⟨12, 12, 15, 8⟩, ⟨12, 12, 14, 10⟩, ⟨12, 12, 13, 12⟩, ⟨12, 12, 12, 14⟩, ⟨12, 12, 11, 16⟩]
  exact AllWinning.cons node_24616 (AllWinning.cons node_24322 (AllWinning.cons node_23909 (AllWinning.cons node_23509 (AllWinning.cons node_23042 (AllWinning.cons node_22484 (AllWinning.cons node_21877 (AllWinning.cons node_21259 (AllWinning.cons node_24635 (AllWinning.cons node_24349 (AllWinning.cons node_23986 (AllWinning.cons node_23594 (AllWinning.cons node_23174 (AllWinning.cons node_22657 (AllWinning.cons node_22089 (AllWinning.cons node_21494 (AllWinning.cons node_24637 (AllWinning.cons node_24352 (AllWinning.cons node_23992 (AllWinning.cons node_23603 (AllWinning.cons node_23187 (AllWinning.cons node_22674 (AllWinning.cons node_22109 (AllWinning.cons node_21515 (AllWinning.nil))))))))))))))))))))))))

theorem node_24914 : Outcome ⟨12, 12, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 12, 19, 2⟩, ⟨10, 12, 19, 4⟩, ⟨9, 12, 19, 6⟩, ⟨8, 12, 19, 8⟩, ⟨7, 12, 19, 10⟩, ⟨6, 12, 19, 12⟩, ⟨5, 12, 19, 14⟩, ⟨4, 12, 19, 16⟩, ⟨3, 12, 19, 18⟩, ⟨2, 12, 19, 20⟩, ⟨12, 11, 19, 2⟩, ⟨12, 10, 19, 4⟩, ⟨12, 9, 19, 6⟩, ⟨12, 8, 19, 8⟩, ⟨12, 7, 19, 10⟩, ⟨12, 6, 19, 12⟩, ⟨12, 5, 19, 14⟩, ⟨12, 4, 19, 16⟩, ⟨12, 3, 19, 18⟩, ⟨12, 2, 19, 20⟩, ⟨12, 12, 18, 2⟩, ⟨12, 12, 17, 4⟩, ⟨12, 12, 16, 6⟩, ⟨12, 12, 15, 8⟩, ⟨12, 12, 14, 10⟩, ⟨12, 12, 13, 12⟩, ⟨12, 12, 12, 14⟩, ⟨12, 12, 11, 16⟩, ⟨12, 12, 10, 18⟩, ⟨12, 12, 9, 20⟩]
  exact AllWinning.cons node_24616 (AllWinning.cons node_24322 (AllWinning.cons node_23909 (AllWinning.cons node_23509 (AllWinning.cons node_23042 (AllWinning.cons node_22484 (AllWinning.cons node_21877 (AllWinning.cons node_21259 (AllWinning.cons node_20466 (AllWinning.cons node_19743 (AllWinning.cons node_24635 (AllWinning.cons node_24349 (AllWinning.cons node_23986 (AllWinning.cons node_23594 (AllWinning.cons node_23174 (AllWinning.cons node_22657 (AllWinning.cons node_22089 (AllWinning.cons node_21494 (AllWinning.cons node_20826 (AllWinning.cons node_20088 (AllWinning.cons node_24637 (AllWinning.cons node_24352 (AllWinning.cons node_23992 (AllWinning.cons node_23603 (AllWinning.cons node_23187 (AllWinning.cons node_22674 (AllWinning.cons node_22109 (AllWinning.cons node_21515 (AllWinning.cons node_20851 (AllWinning.cons node_20109 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_24915 : Outcome ⟨12, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 17, 2⟩) (by decide) node_24639

theorem node_24916 : Outcome ⟨12, 14, 17, 2⟩ true :=
  Outcome.win (q := ⟨11, 14, 17, 2⟩) (by decide) node_24619

theorem node_24917 : Outcome ⟨12, 14, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 14, 17, 2⟩) (by decide) node_24619

theorem node_24918 : Outcome ⟨12, 15, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 15, 16, 2⟩, ⟨10, 15, 16, 4⟩, ⟨9, 15, 16, 6⟩, ⟨8, 15, 16, 8⟩, ⟨12, 14, 16, 2⟩, ⟨12, 13, 16, 4⟩, ⟨12, 12, 16, 6⟩, ⟨12, 11, 16, 8⟩, ⟨12, 15, 15, 2⟩, ⟨12, 15, 14, 4⟩, ⟨12, 15, 13, 6⟩, ⟨12, 15, 12, 8⟩]
  exact AllWinning.cons node_24622 (AllWinning.cons node_24325 (AllWinning.cons node_23916 (AllWinning.cons node_23515 (AllWinning.cons node_24642 (AllWinning.cons node_24354 (AllWinning.cons node_23992 (AllWinning.cons node_23601 (AllWinning.cons node_24644 (AllWinning.cons node_24360 (AllWinning.cons node_23999 (AllWinning.cons node_23611 (AllWinning.nil))))))))))))

theorem node_24919 : Outcome ⟨12, 15, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 15, 16, 2⟩, ⟨10, 15, 16, 4⟩, ⟨9, 15, 16, 6⟩, ⟨8, 15, 16, 8⟩, ⟨7, 15, 16, 10⟩, ⟨6, 15, 16, 12⟩, ⟨12, 14, 16, 2⟩, ⟨12, 13, 16, 4⟩, ⟨12, 12, 16, 6⟩, ⟨12, 11, 16, 8⟩, ⟨12, 10, 16, 10⟩, ⟨12, 9, 16, 12⟩, ⟨12, 15, 15, 2⟩, ⟨12, 15, 14, 4⟩, ⟨12, 15, 13, 6⟩, ⟨12, 15, 12, 8⟩, ⟨12, 15, 11, 10⟩, ⟨12, 15, 10, 12⟩]
  exact AllWinning.cons node_24622 (AllWinning.cons node_24325 (AllWinning.cons node_23916 (AllWinning.cons node_23515 (AllWinning.cons node_23050 (AllWinning.cons node_22491 (AllWinning.cons node_24642 (AllWinning.cons node_24354 (AllWinning.cons node_23992 (AllWinning.cons node_23601 (AllWinning.cons node_23182 (AllWinning.cons node_22666 (AllWinning.cons node_24644 (AllWinning.cons node_24360 (AllWinning.cons node_23999 (AllWinning.cons node_23611 (AllWinning.cons node_23196 (AllWinning.cons node_22682 (AllWinning.nil))))))))))))))))))

theorem node_24920 : Outcome ⟨12, 15, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 15, 16, 2⟩, ⟨10, 15, 16, 4⟩, ⟨9, 15, 16, 6⟩, ⟨8, 15, 16, 8⟩, ⟨7, 15, 16, 10⟩, ⟨6, 15, 16, 12⟩, ⟨5, 15, 16, 14⟩, ⟨4, 15, 16, 16⟩, ⟨12, 14, 16, 2⟩, ⟨12, 13, 16, 4⟩, ⟨12, 12, 16, 6⟩, ⟨12, 11, 16, 8⟩, ⟨12, 10, 16, 10⟩, ⟨12, 9, 16, 12⟩, ⟨12, 8, 16, 14⟩, ⟨12, 7, 16, 16⟩, ⟨12, 15, 15, 2⟩, ⟨12, 15, 14, 4⟩, ⟨12, 15, 13, 6⟩, ⟨12, 15, 12, 8⟩, ⟨12, 15, 11, 10⟩, ⟨12, 15, 10, 12⟩, ⟨12, 15, 9, 14⟩, ⟨12, 15, 8, 16⟩]
  exact AllWinning.cons node_24622 (AllWinning.cons node_24325 (AllWinning.cons node_23916 (AllWinning.cons node_23515 (AllWinning.cons node_23050 (AllWinning.cons node_22491 (AllWinning.cons node_21884 (AllWinning.cons node_21265 (AllWinning.cons node_24642 (AllWinning.cons node_24354 (AllWinning.cons node_23992 (AllWinning.cons node_23601 (AllWinning.cons node_23182 (AllWinning.cons node_22666 (AllWinning.cons node_22097 (AllWinning.cons node_21504 (AllWinning.cons node_24644 (AllWinning.cons node_24360 (AllWinning.cons node_23999 (AllWinning.cons node_23611 (AllWinning.cons node_23196 (AllWinning.cons node_22682 (AllWinning.cons node_22118 (AllWinning.cons node_21520 (AllWinning.nil))))))))))))))))))))))))

theorem node_24921 : Outcome ⟨12, 16, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 15, 2⟩, ⟨10, 16, 15, 4⟩, ⟨9, 16, 15, 6⟩, ⟨8, 16, 15, 8⟩, ⟨12, 15, 15, 2⟩, ⟨12, 14, 15, 4⟩, ⟨12, 13, 15, 6⟩, ⟨12, 12, 15, 8⟩, ⟨12, 16, 14, 2⟩, ⟨12, 16, 13, 4⟩, ⟨12, 16, 12, 6⟩, ⟨12, 16, 11, 8⟩]
  exact AllWinning.cons node_24624 (AllWinning.cons node_24326 (AllWinning.cons node_23919 (AllWinning.cons node_23517 (AllWinning.cons node_24644 (AllWinning.cons node_24357 (AllWinning.cons node_23994 (AllWinning.cons node_23603 (AllWinning.cons node_24646 (AllWinning.cons node_24363 (AllWinning.cons node_24002 (AllWinning.cons node_23613 (AllWinning.nil))))))))))))

theorem node_24922 : Outcome ⟨12, 16, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 15, 2⟩, ⟨10, 16, 15, 4⟩, ⟨9, 16, 15, 6⟩, ⟨8, 16, 15, 8⟩, ⟨7, 16, 15, 10⟩, ⟨6, 16, 15, 12⟩, ⟨12, 15, 15, 2⟩, ⟨12, 14, 15, 4⟩, ⟨12, 13, 15, 6⟩, ⟨12, 12, 15, 8⟩, ⟨12, 11, 15, 10⟩, ⟨12, 10, 15, 12⟩, ⟨12, 16, 14, 2⟩, ⟨12, 16, 13, 4⟩, ⟨12, 16, 12, 6⟩, ⟨12, 16, 11, 8⟩, ⟨12, 16, 10, 10⟩, ⟨12, 16, 9, 12⟩]
  exact AllWinning.cons node_24624 (AllWinning.cons node_24326 (AllWinning.cons node_23919 (AllWinning.cons node_23517 (AllWinning.cons node_23052 (AllWinning.cons node_22494 (AllWinning.cons node_24644 (AllWinning.cons node_24357 (AllWinning.cons node_23994 (AllWinning.cons node_23603 (AllWinning.cons node_23184 (AllWinning.cons node_22669 (AllWinning.cons node_24646 (AllWinning.cons node_24363 (AllWinning.cons node_24002 (AllWinning.cons node_23613 (AllWinning.cons node_23199 (AllWinning.cons node_22685 (AllWinning.nil))))))))))))))))))

theorem node_24923 : Outcome ⟨12, 16, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 15, 2⟩, ⟨10, 16, 15, 4⟩, ⟨9, 16, 15, 6⟩, ⟨8, 16, 15, 8⟩, ⟨7, 16, 15, 10⟩, ⟨6, 16, 15, 12⟩, ⟨5, 16, 15, 14⟩, ⟨4, 16, 15, 16⟩, ⟨12, 15, 15, 2⟩, ⟨12, 14, 15, 4⟩, ⟨12, 13, 15, 6⟩, ⟨12, 12, 15, 8⟩, ⟨12, 11, 15, 10⟩, ⟨12, 10, 15, 12⟩, ⟨12, 9, 15, 14⟩, ⟨12, 8, 15, 16⟩, ⟨12, 16, 14, 2⟩, ⟨12, 16, 13, 4⟩, ⟨12, 16, 12, 6⟩, ⟨12, 16, 11, 8⟩, ⟨12, 16, 10, 10⟩, ⟨12, 16, 9, 12⟩, ⟨12, 16, 8, 14⟩, ⟨12, 16, 7, 16⟩]
  exact AllWinning.cons node_24624 (AllWinning.cons node_24326 (AllWinning.cons node_23919 (AllWinning.cons node_23517 (AllWinning.cons node_23052 (AllWinning.cons node_22494 (AllWinning.cons node_21887 (AllWinning.cons node_21267 (AllWinning.cons node_24644 (AllWinning.cons node_24357 (AllWinning.cons node_23994 (AllWinning.cons node_23603 (AllWinning.cons node_23184 (AllWinning.cons node_22669 (AllWinning.cons node_22100 (AllWinning.cons node_21506 (AllWinning.cons node_24646 (AllWinning.cons node_24363 (AllWinning.cons node_24002 (AllWinning.cons node_23613 (AllWinning.cons node_23199 (AllWinning.cons node_22685 (AllWinning.cons node_22122 (AllWinning.cons node_21522 (AllWinning.nil))))))))))))))))))))))))

theorem node_24924 : Outcome ⟨12, 17, 14, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 14, 2⟩) (by decide) node_24626

theorem node_24925 : Outcome ⟨12, 17, 14, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 14, 2⟩) (by decide) node_24626

theorem node_24926 : Outcome ⟨12, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 17, 13, 2⟩) (by decide) node_24648

theorem node_24927 : Outcome ⟨12, 19, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 12, 2⟩, ⟨10, 19, 12, 4⟩, ⟨12, 18, 12, 2⟩, ⟨12, 17, 12, 4⟩, ⟨12, 19, 11, 2⟩, ⟨12, 19, 10, 4⟩]
  exact AllWinning.cons node_24630 (AllWinning.cons node_24329 (AllWinning.cons node_24651 (AllWinning.cons node_24366 (AllWinning.cons node_24653 (AllWinning.cons node_24368 (AllWinning.nil))))))

end RQ9F1
