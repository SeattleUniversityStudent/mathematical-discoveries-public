import Chunk89
set_option autoImplicit false
namespace RQ9F1

theorem node_19541 : Outcome ⟨16, 1, 15, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 15, 2⟩, ⟨14, 1, 15, 4⟩, ⟨13, 1, 15, 6⟩, ⟨12, 1, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨10, 1, 15, 12⟩, ⟨9, 1, 15, 14⟩, ⟨8, 1, 15, 16⟩, ⟨7, 1, 15, 18⟩, ⟨6, 1, 15, 20⟩, ⟨5, 1, 15, 22⟩, ⟨4, 1, 15, 24⟩, ⟨3, 1, 15, 26⟩, ⟨2, 1, 15, 28⟩, ⟨1, 1, 15, 30⟩, ⟨0, 1, 15, 32⟩, ⟨16, 0, 15, 2⟩, ⟨16, 1, 14, 2⟩, ⟨16, 1, 13, 4⟩, ⟨16, 1, 12, 6⟩, ⟨16, 1, 11, 8⟩, ⟨16, 1, 10, 10⟩, ⟨16, 1, 9, 12⟩, ⟨16, 1, 8, 14⟩, ⟨16, 1, 7, 16⟩, ⟨16, 1, 6, 18⟩, ⟨16, 1, 5, 20⟩, ⟨16, 1, 4, 22⟩, ⟨16, 1, 3, 24⟩, ⟨16, 1, 2, 26⟩, ⟨16, 1, 1, 28⟩, ⟨16, 1, 0, 30⟩]
  exact AllWinning.cons node_18602 (AllWinning.cons node_17634 (AllWinning.cons node_16665 (AllWinning.cons node_15563 (AllWinning.cons node_14581 (AllWinning.cons node_13551 (AllWinning.cons node_12552 (AllWinning.cons node_11503 (AllWinning.cons node_10423 (AllWinning.cons node_9344 (AllWinning.cons node_8294 (AllWinning.cons node_7276 (AllWinning.cons node_6283 (AllWinning.cons node_5463 (AllWinning.cons node_4655 (AllWinning.cons node_3934 (AllWinning.cons node_18652 (AllWinning.cons node_18653 (AllWinning.cons node_17752 (AllWinning.cons node_16821 (AllWinning.cons node_15789 (AllWinning.cons node_14793 (AllWinning.cons node_13843 (AllWinning.cons node_12872 (AllWinning.cons node_11873 (AllWinning.cons node_10880 (AllWinning.cons node_9806 (AllWinning.cons node_8854 (AllWinning.cons node_7864 (AllWinning.cons node_6919 (AllWinning.cons node_6020 (AllWinning.cons node_5307 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19542 : Outcome ⟨16, 2, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 2, 14, 2⟩, ⟨14, 2, 14, 4⟩, ⟨16, 1, 14, 2⟩, ⟨16, 0, 14, 4⟩, ⟨16, 2, 13, 2⟩, ⟨16, 2, 12, 4⟩]
  exact AllWinning.cons node_18605 (AllWinning.cons node_17638 (AllWinning.cons node_18653 (AllWinning.cons node_17747 (AllWinning.cons node_18657 (AllWinning.cons node_17753 (AllWinning.nil))))))

theorem node_19543 : Outcome ⟨16, 2, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 8⟩) (by decide) node_15567

theorem node_19544 : Outcome ⟨16, 2, 14, 8⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 8⟩) (by decide) node_15567

theorem node_19545 : Outcome ⟨16, 2, 14, 16⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 8⟩) (by decide) node_15567

theorem node_19546 : Outcome ⟨16, 3, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 13, 2⟩, ⟨14, 3, 13, 4⟩, ⟨13, 3, 13, 6⟩, ⟨12, 3, 13, 8⟩, ⟨16, 2, 13, 2⟩, ⟨16, 1, 13, 4⟩, ⟨16, 0, 13, 6⟩, ⟨16, 3, 12, 2⟩, ⟨16, 3, 11, 4⟩, ⟨16, 3, 10, 6⟩, ⟨16, 3, 9, 8⟩]
  exact AllWinning.cons node_18607 (AllWinning.cons node_17643 (AllWinning.cons node_16669 (AllWinning.cons node_15573 (AllWinning.cons node_18657 (AllWinning.cons node_17752 (AllWinning.cons node_16818 (AllWinning.cons node_18660 (AllWinning.cons node_17756 (AllWinning.cons node_16827 (AllWinning.cons node_15798 (AllWinning.nil)))))))))))

theorem node_19547 : Outcome ⟨16, 4, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 4, 12, 2⟩, ⟨14, 4, 12, 4⟩, ⟨16, 3, 12, 2⟩, ⟨16, 2, 12, 4⟩, ⟨16, 4, 11, 2⟩, ⟨16, 4, 10, 4⟩]
  exact AllWinning.cons node_18611 (AllWinning.cons node_17647 (AllWinning.cons node_18660 (AllWinning.cons node_17753 (AllWinning.cons node_18662 (AllWinning.cons node_17760 (AllWinning.nil))))))

theorem node_19548 : Outcome ⟨16, 4, 12, 4⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 6⟩) (by decide) node_16674

theorem node_19549 : Outcome ⟨16, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨16, 5, 10, 2⟩) (by decide) node_18665

theorem node_19550 : Outcome ⟨16, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨16, 5, 10, 2⟩) (by decide) node_18665

theorem node_19551 : Outcome ⟨16, 6, 10, 4⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 8⟩) (by decide) node_15794

theorem node_19552 : Outcome ⟨16, 6, 10, 6⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 8⟩) (by decide) node_15794

theorem node_19553 : Outcome ⟨16, 6, 10, 16⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 24⟩) (by decide) node_7303

theorem node_19554 : Outcome ⟨16, 7, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 7, 9, 2⟩, ⟨14, 7, 9, 4⟩, ⟨16, 6, 9, 2⟩, ⟨16, 5, 9, 4⟩, ⟨16, 7, 8, 2⟩, ⟨16, 7, 7, 4⟩]
  exact AllWinning.cons node_18620 (AllWinning.cons node_17656 (AllWinning.cons node_18669 (AllWinning.cons node_17764 (AllWinning.cons node_18672 (AllWinning.cons node_17766 (AllWinning.nil))))))

theorem node_19555 : Outcome ⟨16, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 6⟩) (by decide) node_16688

theorem node_19556 : Outcome ⟨16, 7, 9, 6⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 6⟩) (by decide) node_16688

theorem node_19557 : Outcome ⟨16, 8, 8, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 8, 2⟩) (by decide) node_18624

theorem node_19558 : Outcome ⟨16, 9, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 9, 7, 2⟩, ⟨14, 9, 7, 4⟩, ⟨16, 8, 7, 2⟩, ⟨16, 7, 7, 4⟩, ⟨16, 9, 6, 2⟩, ⟨16, 9, 5, 4⟩]
  exact AllWinning.cons node_18628 (AllWinning.cons node_17662 (AllWinning.cons node_18674 (AllWinning.cons node_17766 (AllWinning.cons node_18676 (AllWinning.cons node_17770 (AllWinning.nil))))))

theorem node_19559 : Outcome ⟨16, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 6⟩) (by decide) node_16699

theorem node_19560 : Outcome ⟨16, 9, 7, 6⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 6⟩) (by decide) node_16699

theorem node_19561 : Outcome ⟨16, 10, 6, 4⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 8⟩) (by decide) node_15812

theorem node_19562 : Outcome ⟨16, 10, 6, 6⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 8⟩) (by decide) node_15812

theorem node_19563 : Outcome ⟨16, 10, 6, 16⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 24⟩) (by decide) node_7323

theorem node_19564 : Outcome ⟨16, 11, 5, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 5, 2⟩) (by decide) node_18679

theorem node_19565 : Outcome ⟨16, 11, 5, 4⟩ true :=
  Outcome.win (q := ⟨16, 10, 5, 2⟩) (by decide) node_18679

theorem node_19566 : Outcome ⟨16, 12, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 12, 4, 2⟩, ⟨14, 12, 4, 4⟩, ⟨16, 11, 4, 2⟩, ⟨16, 10, 4, 4⟩, ⟨16, 12, 3, 2⟩, ⟨16, 12, 2, 4⟩]
  exact AllWinning.cons node_18638 (AllWinning.cons node_17670 (AllWinning.cons node_18683 (AllWinning.cons node_17772 (AllWinning.cons node_18686 (AllWinning.cons node_17778 (AllWinning.nil))))))

theorem node_19567 : Outcome ⟨16, 12, 4, 4⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 6⟩) (by decide) node_16711

theorem node_19568 : Outcome ⟨16, 13, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 3, 2⟩, ⟨14, 13, 3, 4⟩, ⟨16, 12, 3, 2⟩, ⟨16, 11, 3, 4⟩, ⟨16, 13, 2, 2⟩, ⟨16, 13, 1, 4⟩]
  exact AllWinning.cons node_18641 (AllWinning.cons node_17674 (AllWinning.cons node_18686 (AllWinning.cons node_17775 (AllWinning.cons node_18688 (AllWinning.cons node_17782 (AllWinning.nil))))))

theorem node_19569 : Outcome ⟨16, 13, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 3, 2⟩, ⟨14, 13, 3, 4⟩, ⟨13, 13, 3, 6⟩, ⟨12, 13, 3, 8⟩, ⟨16, 12, 3, 2⟩, ⟨16, 11, 3, 4⟩, ⟨16, 10, 3, 6⟩, ⟨16, 9, 3, 8⟩, ⟨16, 13, 2, 2⟩, ⟨16, 13, 1, 4⟩, ⟨16, 13, 0, 6⟩]
  exact AllWinning.cons node_18641 (AllWinning.cons node_17674 (AllWinning.cons node_16718 (AllWinning.cons node_15598 (AllWinning.cons node_18686 (AllWinning.cons node_17775 (AllWinning.cons node_16855 (AllWinning.cons node_15808 (AllWinning.cons node_18688 (AllWinning.cons node_17782 (AllWinning.cons node_16864 (AllWinning.nil)))))))))))

theorem node_19570 : Outcome ⟨16, 14, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 14, 2, 2⟩, ⟨14, 14, 2, 4⟩, ⟨16, 13, 2, 2⟩, ⟨16, 12, 2, 4⟩, ⟨16, 14, 1, 2⟩, ⟨16, 14, 0, 4⟩]
  exact AllWinning.cons node_18645 (AllWinning.cons node_17678 (AllWinning.cons node_18688 (AllWinning.cons node_17778 (AllWinning.cons node_18691 (AllWinning.cons node_17783 (AllWinning.nil))))))

theorem node_19571 : Outcome ⟨16, 14, 2, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 8⟩) (by decide) node_15601

theorem node_19572 : Outcome ⟨16, 14, 2, 8⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 8⟩) (by decide) node_15601

theorem node_19573 : Outcome ⟨16, 14, 2, 16⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 8⟩) (by decide) node_15601

theorem node_19574 : Outcome ⟨16, 15, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 1, 2⟩, ⟨14, 15, 1, 4⟩, ⟨13, 15, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨16, 14, 1, 2⟩, ⟨16, 13, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨16, 11, 1, 8⟩, ⟨16, 15, 0, 2⟩]
  exact AllWinning.cons node_18647 (AllWinning.cons node_17683 (AllWinning.cons node_16725 (AllWinning.cons node_15607 (AllWinning.cons node_18691 (AllWinning.cons node_17782 (AllWinning.cons node_16861 (AllWinning.cons node_15816 (AllWinning.cons node_18695 (AllWinning.nil)))))))))

theorem node_19575 : Outcome ⟨16, 15, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 1, 2⟩, ⟨14, 15, 1, 4⟩, ⟨13, 15, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨11, 15, 1, 10⟩, ⟨10, 15, 1, 12⟩, ⟨9, 15, 1, 14⟩, ⟨8, 15, 1, 16⟩, ⟨7, 15, 1, 18⟩, ⟨6, 15, 1, 20⟩, ⟨5, 15, 1, 22⟩, ⟨4, 15, 1, 24⟩, ⟨16, 14, 1, 2⟩, ⟨16, 13, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨16, 11, 1, 8⟩, ⟨16, 10, 1, 10⟩, ⟨16, 9, 1, 12⟩, ⟨16, 8, 1, 14⟩, ⟨16, 7, 1, 16⟩, ⟨16, 6, 1, 18⟩, ⟨16, 5, 1, 20⟩, ⟨16, 4, 1, 22⟩, ⟨16, 3, 1, 24⟩, ⟨16, 15, 0, 2⟩]
  exact AllWinning.cons node_18647 (AllWinning.cons node_17683 (AllWinning.cons node_16725 (AllWinning.cons node_15607 (AllWinning.cons node_14618 (AllWinning.cons node_13596 (AllWinning.cons node_12587 (AllWinning.cons node_11548 (AllWinning.cons node_10485 (AllWinning.cons node_9398 (AllWinning.cons node_8339 (AllWinning.cons node_7346 (AllWinning.cons node_18691 (AllWinning.cons node_17782 (AllWinning.cons node_16861 (AllWinning.cons node_15816 (AllWinning.cons node_14828 (AllWinning.cons node_13867 (AllWinning.cons node_12899 (AllWinning.cons node_11893 (AllWinning.cons node_10902 (AllWinning.cons node_9821 (AllWinning.cons node_8867 (AllWinning.cons node_7873 (AllWinning.cons node_18695 (AllWinning.nil)))))))))))))))))))))))))

theorem node_19576 : Outcome ⟨16, 15, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 1, 2⟩, ⟨14, 15, 1, 4⟩, ⟨13, 15, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨11, 15, 1, 10⟩, ⟨10, 15, 1, 12⟩, ⟨9, 15, 1, 14⟩, ⟨8, 15, 1, 16⟩, ⟨7, 15, 1, 18⟩, ⟨6, 15, 1, 20⟩, ⟨5, 15, 1, 22⟩, ⟨4, 15, 1, 24⟩, ⟨3, 15, 1, 26⟩, ⟨2, 15, 1, 28⟩, ⟨16, 14, 1, 2⟩, ⟨16, 13, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨16, 11, 1, 8⟩, ⟨16, 10, 1, 10⟩, ⟨16, 9, 1, 12⟩, ⟨16, 8, 1, 14⟩, ⟨16, 7, 1, 16⟩, ⟨16, 6, 1, 18⟩, ⟨16, 5, 1, 20⟩, ⟨16, 4, 1, 22⟩, ⟨16, 3, 1, 24⟩, ⟨16, 2, 1, 26⟩, ⟨16, 1, 1, 28⟩, ⟨16, 15, 0, 2⟩]
  exact AllWinning.cons node_18647 (AllWinning.cons node_17683 (AllWinning.cons node_16725 (AllWinning.cons node_15607 (AllWinning.cons node_14618 (AllWinning.cons node_13596 (AllWinning.cons node_12587 (AllWinning.cons node_11548 (AllWinning.cons node_10485 (AllWinning.cons node_9398 (AllWinning.cons node_8339 (AllWinning.cons node_7346 (AllWinning.cons node_6359 (AllWinning.cons node_5513 (AllWinning.cons node_18691 (AllWinning.cons node_17782 (AllWinning.cons node_16861 (AllWinning.cons node_15816 (AllWinning.cons node_14828 (AllWinning.cons node_13867 (AllWinning.cons node_12899 (AllWinning.cons node_11893 (AllWinning.cons node_10902 (AllWinning.cons node_9821 (AllWinning.cons node_8867 (AllWinning.cons node_7873 (AllWinning.cons node_6923 (AllWinning.cons node_6020 (AllWinning.cons node_18695 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19577 : Outcome ⟨16, 15, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 1, 2⟩, ⟨14, 15, 1, 4⟩, ⟨13, 15, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨11, 15, 1, 10⟩, ⟨10, 15, 1, 12⟩, ⟨9, 15, 1, 14⟩, ⟨8, 15, 1, 16⟩, ⟨7, 15, 1, 18⟩, ⟨6, 15, 1, 20⟩, ⟨5, 15, 1, 22⟩, ⟨4, 15, 1, 24⟩, ⟨3, 15, 1, 26⟩, ⟨2, 15, 1, 28⟩, ⟨1, 15, 1, 30⟩, ⟨0, 15, 1, 32⟩, ⟨16, 14, 1, 2⟩, ⟨16, 13, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨16, 11, 1, 8⟩, ⟨16, 10, 1, 10⟩, ⟨16, 9, 1, 12⟩, ⟨16, 8, 1, 14⟩, ⟨16, 7, 1, 16⟩, ⟨16, 6, 1, 18⟩, ⟨16, 5, 1, 20⟩, ⟨16, 4, 1, 22⟩, ⟨16, 3, 1, 24⟩, ⟨16, 2, 1, 26⟩, ⟨16, 1, 1, 28⟩, ⟨16, 0, 1, 30⟩, ⟨16, 15, 0, 2⟩]
  exact AllWinning.cons node_18647 (AllWinning.cons node_17683 (AllWinning.cons node_16725 (AllWinning.cons node_15607 (AllWinning.cons node_14618 (AllWinning.cons node_13596 (AllWinning.cons node_12587 (AllWinning.cons node_11548 (AllWinning.cons node_10485 (AllWinning.cons node_9398 (AllWinning.cons node_8339 (AllWinning.cons node_7346 (AllWinning.cons node_6359 (AllWinning.cons node_5513 (AllWinning.cons node_4713 (AllWinning.cons node_3997 (AllWinning.cons node_18691 (AllWinning.cons node_17782 (AllWinning.cons node_16861 (AllWinning.cons node_15816 (AllWinning.cons node_14828 (AllWinning.cons node_13867 (AllWinning.cons node_12899 (AllWinning.cons node_11893 (AllWinning.cons node_10902 (AllWinning.cons node_9821 (AllWinning.cons node_8867 (AllWinning.cons node_7873 (AllWinning.cons node_6923 (AllWinning.cons node_6020 (AllWinning.cons node_5302 (AllWinning.cons node_18695 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19578 : Outcome ⟨16, 15, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 1, 2⟩, ⟨14, 15, 1, 4⟩, ⟨13, 15, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨11, 15, 1, 10⟩, ⟨10, 15, 1, 12⟩, ⟨9, 15, 1, 14⟩, ⟨8, 15, 1, 16⟩, ⟨7, 15, 1, 18⟩, ⟨6, 15, 1, 20⟩, ⟨5, 15, 1, 22⟩, ⟨4, 15, 1, 24⟩, ⟨3, 15, 1, 26⟩, ⟨2, 15, 1, 28⟩, ⟨1, 15, 1, 30⟩, ⟨0, 15, 1, 32⟩, ⟨16, 14, 1, 2⟩, ⟨16, 13, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨16, 11, 1, 8⟩, ⟨16, 10, 1, 10⟩, ⟨16, 9, 1, 12⟩, ⟨16, 8, 1, 14⟩, ⟨16, 7, 1, 16⟩, ⟨16, 6, 1, 18⟩, ⟨16, 5, 1, 20⟩, ⟨16, 4, 1, 22⟩, ⟨16, 3, 1, 24⟩, ⟨16, 2, 1, 26⟩, ⟨16, 1, 1, 28⟩, ⟨16, 0, 1, 30⟩, ⟨16, 15, 0, 2⟩]
  exact AllWinning.cons node_18647 (AllWinning.cons node_17683 (AllWinning.cons node_16725 (AllWinning.cons node_15607 (AllWinning.cons node_14618 (AllWinning.cons node_13596 (AllWinning.cons node_12587 (AllWinning.cons node_11548 (AllWinning.cons node_10485 (AllWinning.cons node_9398 (AllWinning.cons node_8339 (AllWinning.cons node_7346 (AllWinning.cons node_6359 (AllWinning.cons node_5513 (AllWinning.cons node_4713 (AllWinning.cons node_3997 (AllWinning.cons node_18691 (AllWinning.cons node_17782 (AllWinning.cons node_16861 (AllWinning.cons node_15816 (AllWinning.cons node_14828 (AllWinning.cons node_13867 (AllWinning.cons node_12899 (AllWinning.cons node_11893 (AllWinning.cons node_10902 (AllWinning.cons node_9821 (AllWinning.cons node_8867 (AllWinning.cons node_7873 (AllWinning.cons node_6923 (AllWinning.cons node_6020 (AllWinning.cons node_5302 (AllWinning.cons node_18695 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19579 : Outcome ⟨16, 15, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 15, 1, 2⟩, ⟨14, 15, 1, 4⟩, ⟨13, 15, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨11, 15, 1, 10⟩, ⟨10, 15, 1, 12⟩, ⟨9, 15, 1, 14⟩, ⟨8, 15, 1, 16⟩, ⟨7, 15, 1, 18⟩, ⟨6, 15, 1, 20⟩, ⟨5, 15, 1, 22⟩, ⟨4, 15, 1, 24⟩, ⟨3, 15, 1, 26⟩, ⟨2, 15, 1, 28⟩, ⟨1, 15, 1, 30⟩, ⟨0, 15, 1, 32⟩, ⟨16, 14, 1, 2⟩, ⟨16, 13, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨16, 11, 1, 8⟩, ⟨16, 10, 1, 10⟩, ⟨16, 9, 1, 12⟩, ⟨16, 8, 1, 14⟩, ⟨16, 7, 1, 16⟩, ⟨16, 6, 1, 18⟩, ⟨16, 5, 1, 20⟩, ⟨16, 4, 1, 22⟩, ⟨16, 3, 1, 24⟩, ⟨16, 2, 1, 26⟩, ⟨16, 1, 1, 28⟩, ⟨16, 0, 1, 30⟩, ⟨16, 15, 0, 2⟩]
  exact AllWinning.cons node_18647 (AllWinning.cons node_17683 (AllWinning.cons node_16725 (AllWinning.cons node_15607 (AllWinning.cons node_14618 (AllWinning.cons node_13596 (AllWinning.cons node_12587 (AllWinning.cons node_11548 (AllWinning.cons node_10485 (AllWinning.cons node_9398 (AllWinning.cons node_8339 (AllWinning.cons node_7346 (AllWinning.cons node_6359 (AllWinning.cons node_5513 (AllWinning.cons node_4713 (AllWinning.cons node_3997 (AllWinning.cons node_18691 (AllWinning.cons node_17782 (AllWinning.cons node_16861 (AllWinning.cons node_15816 (AllWinning.cons node_14828 (AllWinning.cons node_13867 (AllWinning.cons node_12899 (AllWinning.cons node_11893 (AllWinning.cons node_10902 (AllWinning.cons node_9821 (AllWinning.cons node_8867 (AllWinning.cons node_7873 (AllWinning.cons node_6923 (AllWinning.cons node_6020 (AllWinning.cons node_5302 (AllWinning.cons node_18695 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19580 : Outcome ⟨16, 16, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 0, 2⟩, ⟨14, 16, 0, 4⟩, ⟨16, 15, 0, 2⟩, ⟨16, 14, 0, 4⟩]
  exact AllWinning.cons node_18650 (AllWinning.cons node_17686 (AllWinning.cons node_18695 (AllWinning.cons node_17783 (AllWinning.nil))))

theorem node_19581 : Outcome ⟨16, 16, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 0, 2⟩, ⟨14, 16, 0, 4⟩, ⟨13, 16, 0, 6⟩, ⟨12, 16, 0, 8⟩, ⟨16, 15, 0, 2⟩, ⟨16, 14, 0, 4⟩, ⟨16, 13, 0, 6⟩, ⟨16, 12, 0, 8⟩]
  exact AllWinning.cons node_18650 (AllWinning.cons node_17686 (AllWinning.cons node_16727 (AllWinning.cons node_15610 (AllWinning.cons node_18695 (AllWinning.cons node_17783 (AllWinning.cons node_16864 (AllWinning.cons node_15819 (AllWinning.nil))))))))

theorem node_19582 : Outcome ⟨16, 16, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 0, 2⟩, ⟨14, 16, 0, 4⟩, ⟨13, 16, 0, 6⟩, ⟨12, 16, 0, 8⟩, ⟨11, 16, 0, 10⟩, ⟨10, 16, 0, 12⟩, ⟨16, 15, 0, 2⟩, ⟨16, 14, 0, 4⟩, ⟨16, 13, 0, 6⟩, ⟨16, 12, 0, 8⟩, ⟨16, 11, 0, 10⟩, ⟨16, 10, 0, 12⟩]
  exact AllWinning.cons node_18650 (AllWinning.cons node_17686 (AllWinning.cons node_16727 (AllWinning.cons node_15610 (AllWinning.cons node_14622 (AllWinning.cons node_13599 (AllWinning.cons node_18695 (AllWinning.cons node_17783 (AllWinning.cons node_16864 (AllWinning.cons node_15819 (AllWinning.cons node_14832 (AllWinning.cons node_13870 (AllWinning.nil))))))))))))

theorem node_19583 : Outcome ⟨16, 16, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 0, 2⟩, ⟨14, 16, 0, 4⟩, ⟨13, 16, 0, 6⟩, ⟨12, 16, 0, 8⟩, ⟨11, 16, 0, 10⟩, ⟨10, 16, 0, 12⟩, ⟨9, 16, 0, 14⟩, ⟨8, 16, 0, 16⟩, ⟨7, 16, 0, 18⟩, ⟨6, 16, 0, 20⟩, ⟨16, 15, 0, 2⟩, ⟨16, 14, 0, 4⟩, ⟨16, 13, 0, 6⟩, ⟨16, 12, 0, 8⟩, ⟨16, 11, 0, 10⟩, ⟨16, 10, 0, 12⟩, ⟨16, 9, 0, 14⟩, ⟨16, 8, 0, 16⟩, ⟨16, 7, 0, 18⟩, ⟨16, 6, 0, 20⟩]
  exact AllWinning.cons node_18650 (AllWinning.cons node_17686 (AllWinning.cons node_16727 (AllWinning.cons node_15610 (AllWinning.cons node_14622 (AllWinning.cons node_13599 (AllWinning.cons node_12591 (AllWinning.cons node_11552 (AllWinning.cons node_10489 (AllWinning.cons node_9402 (AllWinning.cons node_18695 (AllWinning.cons node_17783 (AllWinning.cons node_16864 (AllWinning.cons node_15819 (AllWinning.cons node_14832 (AllWinning.cons node_13870 (AllWinning.cons node_12903 (AllWinning.cons node_11898 (AllWinning.cons node_10907 (AllWinning.cons node_9825 (AllWinning.nil))))))))))))))))))))

theorem node_19584 : Outcome ⟨16, 16, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 0, 2⟩, ⟨14, 16, 0, 4⟩, ⟨13, 16, 0, 6⟩, ⟨12, 16, 0, 8⟩, ⟨11, 16, 0, 10⟩, ⟨10, 16, 0, 12⟩, ⟨9, 16, 0, 14⟩, ⟨8, 16, 0, 16⟩, ⟨7, 16, 0, 18⟩, ⟨6, 16, 0, 20⟩, ⟨5, 16, 0, 22⟩, ⟨4, 16, 0, 24⟩, ⟨16, 15, 0, 2⟩, ⟨16, 14, 0, 4⟩, ⟨16, 13, 0, 6⟩, ⟨16, 12, 0, 8⟩, ⟨16, 11, 0, 10⟩, ⟨16, 10, 0, 12⟩, ⟨16, 9, 0, 14⟩, ⟨16, 8, 0, 16⟩, ⟨16, 7, 0, 18⟩, ⟨16, 6, 0, 20⟩, ⟨16, 5, 0, 22⟩, ⟨16, 4, 0, 24⟩]
  exact AllWinning.cons node_18650 (AllWinning.cons node_17686 (AllWinning.cons node_16727 (AllWinning.cons node_15610 (AllWinning.cons node_14622 (AllWinning.cons node_13599 (AllWinning.cons node_12591 (AllWinning.cons node_11552 (AllWinning.cons node_10489 (AllWinning.cons node_9402 (AllWinning.cons node_8342 (AllWinning.cons node_7350 (AllWinning.cons node_18695 (AllWinning.cons node_17783 (AllWinning.cons node_16864 (AllWinning.cons node_15819 (AllWinning.cons node_14832 (AllWinning.cons node_13870 (AllWinning.cons node_12903 (AllWinning.cons node_11898 (AllWinning.cons node_10907 (AllWinning.cons node_9825 (AllWinning.cons node_8870 (AllWinning.cons node_7877 (AllWinning.nil))))))))))))))))))))))))

theorem node_19585 : Outcome ⟨16, 16, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 0, 2⟩, ⟨14, 16, 0, 4⟩, ⟨13, 16, 0, 6⟩, ⟨12, 16, 0, 8⟩, ⟨11, 16, 0, 10⟩, ⟨10, 16, 0, 12⟩, ⟨9, 16, 0, 14⟩, ⟨8, 16, 0, 16⟩, ⟨7, 16, 0, 18⟩, ⟨6, 16, 0, 20⟩, ⟨5, 16, 0, 22⟩, ⟨4, 16, 0, 24⟩, ⟨3, 16, 0, 26⟩, ⟨2, 16, 0, 28⟩, ⟨16, 15, 0, 2⟩, ⟨16, 14, 0, 4⟩, ⟨16, 13, 0, 6⟩, ⟨16, 12, 0, 8⟩, ⟨16, 11, 0, 10⟩, ⟨16, 10, 0, 12⟩, ⟨16, 9, 0, 14⟩, ⟨16, 8, 0, 16⟩, ⟨16, 7, 0, 18⟩, ⟨16, 6, 0, 20⟩, ⟨16, 5, 0, 22⟩, ⟨16, 4, 0, 24⟩, ⟨16, 3, 0, 26⟩, ⟨16, 2, 0, 28⟩]
  exact AllWinning.cons node_18650 (AllWinning.cons node_17686 (AllWinning.cons node_16727 (AllWinning.cons node_15610 (AllWinning.cons node_14622 (AllWinning.cons node_13599 (AllWinning.cons node_12591 (AllWinning.cons node_11552 (AllWinning.cons node_10489 (AllWinning.cons node_9402 (AllWinning.cons node_8342 (AllWinning.cons node_7350 (AllWinning.cons node_6367 (AllWinning.cons node_5517 (AllWinning.cons node_18695 (AllWinning.cons node_17783 (AllWinning.cons node_16864 (AllWinning.cons node_15819 (AllWinning.cons node_14832 (AllWinning.cons node_13870 (AllWinning.cons node_12903 (AllWinning.cons node_11898 (AllWinning.cons node_10907 (AllWinning.cons node_9825 (AllWinning.cons node_8870 (AllWinning.cons node_7877 (AllWinning.cons node_6931 (AllWinning.cons node_6024 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_19586 : Outcome ⟨16, 16, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 0, 2⟩, ⟨14, 16, 0, 4⟩, ⟨13, 16, 0, 6⟩, ⟨12, 16, 0, 8⟩, ⟨11, 16, 0, 10⟩, ⟨10, 16, 0, 12⟩, ⟨9, 16, 0, 14⟩, ⟨8, 16, 0, 16⟩, ⟨7, 16, 0, 18⟩, ⟨6, 16, 0, 20⟩, ⟨5, 16, 0, 22⟩, ⟨4, 16, 0, 24⟩, ⟨3, 16, 0, 26⟩, ⟨2, 16, 0, 28⟩, ⟨1, 16, 0, 30⟩, ⟨0, 16, 0, 32⟩, ⟨16, 15, 0, 2⟩, ⟨16, 14, 0, 4⟩, ⟨16, 13, 0, 6⟩, ⟨16, 12, 0, 8⟩, ⟨16, 11, 0, 10⟩, ⟨16, 10, 0, 12⟩, ⟨16, 9, 0, 14⟩, ⟨16, 8, 0, 16⟩, ⟨16, 7, 0, 18⟩, ⟨16, 6, 0, 20⟩, ⟨16, 5, 0, 22⟩, ⟨16, 4, 0, 24⟩, ⟨16, 3, 0, 26⟩, ⟨16, 2, 0, 28⟩, ⟨16, 1, 0, 30⟩, ⟨16, 0, 0, 32⟩]
  exact AllWinning.cons node_18650 (AllWinning.cons node_17686 (AllWinning.cons node_16727 (AllWinning.cons node_15610 (AllWinning.cons node_14622 (AllWinning.cons node_13599 (AllWinning.cons node_12591 (AllWinning.cons node_11552 (AllWinning.cons node_10489 (AllWinning.cons node_9402 (AllWinning.cons node_8342 (AllWinning.cons node_7350 (AllWinning.cons node_6367 (AllWinning.cons node_5517 (AllWinning.cons node_4718 (AllWinning.cons node_4001 (AllWinning.cons node_18695 (AllWinning.cons node_17783 (AllWinning.cons node_16864 (AllWinning.cons node_15819 (AllWinning.cons node_14832 (AllWinning.cons node_13870 (AllWinning.cons node_12903 (AllWinning.cons node_11898 (AllWinning.cons node_10907 (AllWinning.cons node_9825 (AllWinning.cons node_8870 (AllWinning.cons node_7877 (AllWinning.cons node_6931 (AllWinning.cons node_6024 (AllWinning.cons node_5307 (AllWinning.cons node_4567 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19587 : Outcome ⟨17, 0, 15, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 4⟩) (by decide) node_17690

theorem node_19588 : Outcome ⟨17, 0, 15, 8⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 4⟩) (by decide) node_17690

theorem node_19589 : Outcome ⟨17, 1, 14, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 2⟩) (by decide) node_18698

theorem node_19590 : Outcome ⟨17, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 2⟩) (by decide) node_18698

theorem node_19591 : Outcome ⟨17, 2, 13, 4⟩ true :=
  Outcome.win (q := ⟨17, 2, 11, 4⟩) (by decide) node_17792

theorem node_19592 : Outcome ⟨17, 2, 13, 12⟩ true :=
  Outcome.win (q := ⟨17, 2, 11, 4⟩) (by decide) node_17792

theorem node_19593 : Outcome ⟨17, 3, 12, 4⟩ true :=
  Outcome.win (q := ⟨15, 3, 12, 4⟩) (by decide) node_17702

theorem node_19594 : Outcome ⟨17, 4, 11, 2⟩ true :=
  Outcome.win (q := ⟨17, 2, 11, 4⟩) (by decide) node_17792

theorem node_19595 : Outcome ⟨17, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 6⟩) (by decide) node_16878

theorem node_19596 : Outcome ⟨17, 4, 11, 8⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 6⟩) (by decide) node_16878

theorem node_19597 : Outcome ⟨17, 5, 10, 2⟩ true :=
  Outcome.win (q := ⟨16, 5, 10, 2⟩) (by decide) node_18665

theorem node_19598 : Outcome ⟨17, 5, 10, 4⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 6⟩) (by decide) node_16882

theorem node_19599 : Outcome ⟨17, 5, 10, 10⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 6⟩) (by decide) node_16882

theorem node_19600 : Outcome ⟨17, 6, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 9, 2⟩, ⟨15, 6, 9, 4⟩, ⟨17, 5, 9, 2⟩, ⟨17, 4, 9, 4⟩, ⟨17, 6, 8, 2⟩, ⟨17, 6, 7, 4⟩]
  exact AllWinning.cons node_18669 (AllWinning.cons node_17712 (AllWinning.cons node_18710 (AllWinning.cons node_17799 (AllWinning.cons node_18712 (AllWinning.cons node_17802 (AllWinning.nil))))))

theorem node_19601 : Outcome ⟨17, 6, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 9, 2⟩, ⟨15, 6, 9, 4⟩, ⟨14, 6, 9, 6⟩, ⟨13, 6, 9, 8⟩, ⟨17, 5, 9, 2⟩, ⟨17, 4, 9, 4⟩, ⟨17, 3, 9, 6⟩, ⟨17, 2, 9, 8⟩, ⟨17, 6, 8, 2⟩, ⟨17, 6, 7, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 6, 5, 8⟩]
  exact AllWinning.cons node_18669 (AllWinning.cons node_17712 (AllWinning.cons node_16748 (AllWinning.cons node_15634 (AllWinning.cons node_18710 (AllWinning.cons node_17799 (AllWinning.cons node_16874 (AllWinning.cons node_15828 (AllWinning.cons node_18712 (AllWinning.cons node_17802 (AllWinning.cons node_16888 (AllWinning.cons node_15835 (AllWinning.nil))))))))))))

theorem node_19602 : Outcome ⟨17, 6, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 9, 2⟩, ⟨15, 6, 9, 4⟩, ⟨14, 6, 9, 6⟩, ⟨13, 6, 9, 8⟩, ⟨12, 6, 9, 10⟩, ⟨11, 6, 9, 12⟩, ⟨17, 5, 9, 2⟩, ⟨17, 4, 9, 4⟩, ⟨17, 3, 9, 6⟩, ⟨17, 2, 9, 8⟩, ⟨17, 1, 9, 10⟩, ⟨17, 0, 9, 12⟩, ⟨17, 6, 8, 2⟩, ⟨17, 6, 7, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 6, 5, 8⟩, ⟨17, 6, 4, 10⟩, ⟨17, 6, 3, 12⟩]
  exact AllWinning.cons node_18669 (AllWinning.cons node_17712 (AllWinning.cons node_16748 (AllWinning.cons node_15634 (AllWinning.cons node_14644 (AllWinning.cons node_13622 (AllWinning.cons node_18710 (AllWinning.cons node_17799 (AllWinning.cons node_16874 (AllWinning.cons node_15828 (AllWinning.cons node_14840 (AllWinning.cons node_13874 (AllWinning.cons node_18712 (AllWinning.cons node_17802 (AllWinning.cons node_16888 (AllWinning.cons node_15835 (AllWinning.cons node_14850 (AllWinning.cons node_13894 (AllWinning.nil))))))))))))))))))

theorem node_19603 : Outcome ⟨17, 6, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 9, 2⟩, ⟨15, 6, 9, 4⟩, ⟨14, 6, 9, 6⟩, ⟨13, 6, 9, 8⟩, ⟨12, 6, 9, 10⟩, ⟨11, 6, 9, 12⟩, ⟨10, 6, 9, 14⟩, ⟨9, 6, 9, 16⟩, ⟨17, 5, 9, 2⟩, ⟨17, 4, 9, 4⟩, ⟨17, 3, 9, 6⟩, ⟨17, 2, 9, 8⟩, ⟨17, 1, 9, 10⟩, ⟨17, 0, 9, 12⟩, ⟨17, 6, 8, 2⟩, ⟨17, 6, 7, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 6, 5, 8⟩, ⟨17, 6, 4, 10⟩, ⟨17, 6, 3, 12⟩, ⟨17, 6, 2, 14⟩, ⟨17, 6, 1, 16⟩]
  exact AllWinning.cons node_18669 (AllWinning.cons node_17712 (AllWinning.cons node_16748 (AllWinning.cons node_15634 (AllWinning.cons node_14644 (AllWinning.cons node_13622 (AllWinning.cons node_12617 (AllWinning.cons node_11579 (AllWinning.cons node_18710 (AllWinning.cons node_17799 (AllWinning.cons node_16874 (AllWinning.cons node_15828 (AllWinning.cons node_14840 (AllWinning.cons node_13874 (AllWinning.cons node_18712 (AllWinning.cons node_17802 (AllWinning.cons node_16888 (AllWinning.cons node_15835 (AllWinning.cons node_14850 (AllWinning.cons node_13894 (AllWinning.cons node_12928 (AllWinning.cons node_11924 (AllWinning.nil))))))))))))))))))))))

theorem node_19604 : Outcome ⟨17, 6, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 6, 9, 2⟩, ⟨15, 6, 9, 4⟩, ⟨14, 6, 9, 6⟩, ⟨13, 6, 9, 8⟩, ⟨12, 6, 9, 10⟩, ⟨11, 6, 9, 12⟩, ⟨10, 6, 9, 14⟩, ⟨9, 6, 9, 16⟩, ⟨8, 6, 9, 18⟩, ⟨7, 6, 9, 20⟩, ⟨6, 6, 9, 22⟩, ⟨5, 6, 9, 24⟩, ⟨17, 5, 9, 2⟩, ⟨17, 4, 9, 4⟩, ⟨17, 3, 9, 6⟩, ⟨17, 2, 9, 8⟩, ⟨17, 1, 9, 10⟩, ⟨17, 0, 9, 12⟩, ⟨17, 6, 8, 2⟩, ⟨17, 6, 7, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 6, 5, 8⟩, ⟨17, 6, 4, 10⟩, ⟨17, 6, 3, 12⟩, ⟨17, 6, 2, 14⟩, ⟨17, 6, 1, 16⟩, ⟨17, 6, 0, 18⟩]
  exact AllWinning.cons node_18669 (AllWinning.cons node_17712 (AllWinning.cons node_16748 (AllWinning.cons node_15634 (AllWinning.cons node_14644 (AllWinning.cons node_13622 (AllWinning.cons node_12617 (AllWinning.cons node_11579 (AllWinning.cons node_10515 (AllWinning.cons node_9433 (AllWinning.cons node_8366 (AllWinning.cons node_7375 (AllWinning.cons node_18710 (AllWinning.cons node_17799 (AllWinning.cons node_16874 (AllWinning.cons node_15828 (AllWinning.cons node_14840 (AllWinning.cons node_13874 (AllWinning.cons node_18712 (AllWinning.cons node_17802 (AllWinning.cons node_16888 (AllWinning.cons node_15835 (AllWinning.cons node_14850 (AllWinning.cons node_13894 (AllWinning.cons node_12928 (AllWinning.cons node_11924 (AllWinning.cons node_10935 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_19605 : Outcome ⟨17, 7, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 7, 8, 2⟩, ⟨15, 7, 8, 4⟩, ⟨17, 6, 8, 2⟩, ⟨17, 5, 8, 4⟩, ⟨17, 7, 7, 2⟩, ⟨17, 7, 6, 4⟩]
  exact AllWinning.cons node_18672 (AllWinning.cons node_17715 (AllWinning.cons node_18712 (AllWinning.cons node_17801 (AllWinning.cons node_18713 (AllWinning.cons node_17804 (AllWinning.nil))))))

theorem node_19606 : Outcome ⟨17, 7, 8, 4⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 6⟩) (by decide) node_16878

theorem node_19607 : Outcome ⟨17, 7, 8, 8⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 6⟩) (by decide) node_16878

theorem node_19608 : Outcome ⟨17, 8, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 8, 7, 2⟩, ⟨15, 8, 7, 4⟩, ⟨17, 7, 7, 2⟩, ⟨17, 6, 7, 4⟩, ⟨17, 8, 6, 2⟩, ⟨17, 8, 5, 4⟩]
  exact AllWinning.cons node_18674 (AllWinning.cons node_17719 (AllWinning.cons node_18713 (AllWinning.cons node_17802 (AllWinning.cons node_18715 (AllWinning.cons node_17807 (AllWinning.nil))))))

theorem node_19609 : Outcome ⟨17, 8, 7, 4⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 6⟩) (by decide) node_16882

theorem node_19610 : Outcome ⟨17, 8, 7, 8⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 6⟩) (by decide) node_16882

theorem node_19611 : Outcome ⟨17, 9, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨17, 8, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨17, 9, 5, 2⟩, ⟨17, 9, 4, 4⟩]
  exact AllWinning.cons node_18676 (AllWinning.cons node_17723 (AllWinning.cons node_18715 (AllWinning.cons node_17804 (AllWinning.cons node_18717 (AllWinning.cons node_17809 (AllWinning.nil))))))

theorem node_19612 : Outcome ⟨17, 9, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨14, 9, 6, 6⟩, ⟨13, 9, 6, 8⟩, ⟨17, 8, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 5, 6, 8⟩, ⟨17, 9, 5, 2⟩, ⟨17, 9, 4, 4⟩, ⟨17, 9, 3, 6⟩, ⟨17, 9, 2, 8⟩]
  exact AllWinning.cons node_18676 (AllWinning.cons node_17723 (AllWinning.cons node_16757 (AllWinning.cons node_15642 (AllWinning.cons node_18715 (AllWinning.cons node_17804 (AllWinning.cons node_16888 (AllWinning.cons node_15833 (AllWinning.cons node_18717 (AllWinning.cons node_17809 (AllWinning.cons node_16901 (AllWinning.cons node_15841 (AllWinning.nil))))))))))))

theorem node_19613 : Outcome ⟨17, 9, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨14, 9, 6, 6⟩, ⟨13, 9, 6, 8⟩, ⟨12, 9, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨17, 8, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 5, 6, 8⟩, ⟨17, 4, 6, 10⟩, ⟨17, 3, 6, 12⟩, ⟨17, 9, 5, 2⟩, ⟨17, 9, 4, 4⟩, ⟨17, 9, 3, 6⟩, ⟨17, 9, 2, 8⟩, ⟨17, 9, 1, 10⟩, ⟨17, 9, 0, 12⟩]
  exact AllWinning.cons node_18676 (AllWinning.cons node_17723 (AllWinning.cons node_16757 (AllWinning.cons node_15642 (AllWinning.cons node_14653 (AllWinning.cons node_13633 (AllWinning.cons node_18715 (AllWinning.cons node_17804 (AllWinning.cons node_16888 (AllWinning.cons node_15833 (AllWinning.cons node_14846 (AllWinning.cons node_13884 (AllWinning.cons node_18717 (AllWinning.cons node_17809 (AllWinning.cons node_16901 (AllWinning.cons node_15841 (AllWinning.cons node_14857 (AllWinning.cons node_13905 (AllWinning.nil))))))))))))))))))

theorem node_19614 : Outcome ⟨17, 9, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨14, 9, 6, 6⟩, ⟨13, 9, 6, 8⟩, ⟨12, 9, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨10, 9, 6, 14⟩, ⟨9, 9, 6, 16⟩, ⟨17, 8, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 5, 6, 8⟩, ⟨17, 4, 6, 10⟩, ⟨17, 3, 6, 12⟩, ⟨17, 2, 6, 14⟩, ⟨17, 1, 6, 16⟩, ⟨17, 9, 5, 2⟩, ⟨17, 9, 4, 4⟩, ⟨17, 9, 3, 6⟩, ⟨17, 9, 2, 8⟩, ⟨17, 9, 1, 10⟩, ⟨17, 9, 0, 12⟩]
  exact AllWinning.cons node_18676 (AllWinning.cons node_17723 (AllWinning.cons node_16757 (AllWinning.cons node_15642 (AllWinning.cons node_14653 (AllWinning.cons node_13633 (AllWinning.cons node_12627 (AllWinning.cons node_11586 (AllWinning.cons node_18715 (AllWinning.cons node_17804 (AllWinning.cons node_16888 (AllWinning.cons node_15833 (AllWinning.cons node_14846 (AllWinning.cons node_13884 (AllWinning.cons node_12915 (AllWinning.cons node_11905 (AllWinning.cons node_18717 (AllWinning.cons node_17809 (AllWinning.cons node_16901 (AllWinning.cons node_15841 (AllWinning.cons node_14857 (AllWinning.cons node_13905 (AllWinning.nil))))))))))))))))))))))

theorem node_19615 : Outcome ⟨17, 9, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨14, 9, 6, 6⟩, ⟨13, 9, 6, 8⟩, ⟨12, 9, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨10, 9, 6, 14⟩, ⟨9, 9, 6, 16⟩, ⟨8, 9, 6, 18⟩, ⟨7, 9, 6, 20⟩, ⟨17, 8, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 5, 6, 8⟩, ⟨17, 4, 6, 10⟩, ⟨17, 3, 6, 12⟩, ⟨17, 2, 6, 14⟩, ⟨17, 1, 6, 16⟩, ⟨17, 0, 6, 18⟩, ⟨17, 9, 5, 2⟩, ⟨17, 9, 4, 4⟩, ⟨17, 9, 3, 6⟩, ⟨17, 9, 2, 8⟩, ⟨17, 9, 1, 10⟩, ⟨17, 9, 0, 12⟩]
  exact AllWinning.cons node_18676 (AllWinning.cons node_17723 (AllWinning.cons node_16757 (AllWinning.cons node_15642 (AllWinning.cons node_14653 (AllWinning.cons node_13633 (AllWinning.cons node_12627 (AllWinning.cons node_11586 (AllWinning.cons node_10528 (AllWinning.cons node_9442 (AllWinning.cons node_18715 (AllWinning.cons node_17804 (AllWinning.cons node_16888 (AllWinning.cons node_15833 (AllWinning.cons node_14846 (AllWinning.cons node_13884 (AllWinning.cons node_12915 (AllWinning.cons node_11905 (AllWinning.cons node_10911 (AllWinning.cons node_18717 (AllWinning.cons node_17809 (AllWinning.cons node_16901 (AllWinning.cons node_15841 (AllWinning.cons node_14857 (AllWinning.cons node_13905 (AllWinning.nil)))))))))))))))))))))))))

theorem node_19616 : Outcome ⟨17, 9, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨14, 9, 6, 6⟩, ⟨13, 9, 6, 8⟩, ⟨12, 9, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨10, 9, 6, 14⟩, ⟨9, 9, 6, 16⟩, ⟨8, 9, 6, 18⟩, ⟨7, 9, 6, 20⟩, ⟨6, 9, 6, 22⟩, ⟨5, 9, 6, 24⟩, ⟨17, 8, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨17, 6, 6, 6⟩, ⟨17, 5, 6, 8⟩, ⟨17, 4, 6, 10⟩, ⟨17, 3, 6, 12⟩, ⟨17, 2, 6, 14⟩, ⟨17, 1, 6, 16⟩, ⟨17, 0, 6, 18⟩, ⟨17, 9, 5, 2⟩, ⟨17, 9, 4, 4⟩, ⟨17, 9, 3, 6⟩, ⟨17, 9, 2, 8⟩, ⟨17, 9, 1, 10⟩, ⟨17, 9, 0, 12⟩]
  exact AllWinning.cons node_18676 (AllWinning.cons node_17723 (AllWinning.cons node_16757 (AllWinning.cons node_15642 (AllWinning.cons node_14653 (AllWinning.cons node_13633 (AllWinning.cons node_12627 (AllWinning.cons node_11586 (AllWinning.cons node_10528 (AllWinning.cons node_9442 (AllWinning.cons node_8394 (AllWinning.cons node_7388 (AllWinning.cons node_18715 (AllWinning.cons node_17804 (AllWinning.cons node_16888 (AllWinning.cons node_15833 (AllWinning.cons node_14846 (AllWinning.cons node_13884 (AllWinning.cons node_12915 (AllWinning.cons node_11905 (AllWinning.cons node_10911 (AllWinning.cons node_18717 (AllWinning.cons node_17809 (AllWinning.cons node_16901 (AllWinning.cons node_15841 (AllWinning.cons node_14857 (AllWinning.cons node_13905 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_19617 : Outcome ⟨17, 10, 5, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 5, 2⟩) (by decide) node_18679

theorem node_19618 : Outcome ⟨17, 10, 5, 4⟩ true :=
  Outcome.win (q := ⟨17, 7, 5, 6⟩) (by decide) node_16890

theorem node_19619 : Outcome ⟨17, 10, 5, 10⟩ true :=
  Outcome.win (q := ⟨17, 7, 5, 6⟩) (by decide) node_16890

theorem node_19620 : Outcome ⟨17, 11, 4, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 2, 4⟩) (by decide) node_17814

theorem node_19621 : Outcome ⟨17, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 6⟩) (by decide) node_16896

theorem node_19622 : Outcome ⟨17, 11, 4, 8⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 6⟩) (by decide) node_16896

theorem node_19623 : Outcome ⟨17, 12, 3, 4⟩ true :=
  Outcome.win (q := ⟨15, 12, 3, 4⟩) (by decide) node_17732

theorem node_19624 : Outcome ⟨17, 13, 2, 4⟩ true :=
  Outcome.win (q := ⟨17, 11, 2, 4⟩) (by decide) node_17814

theorem node_19625 : Outcome ⟨17, 13, 2, 12⟩ true :=
  Outcome.win (q := ⟨17, 11, 2, 4⟩) (by decide) node_17814

theorem node_19626 : Outcome ⟨17, 14, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 2⟩) (by decide) node_18724

theorem node_19627 : Outcome ⟨17, 14, 1, 4⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 2⟩) (by decide) node_18724

theorem node_19628 : Outcome ⟨17, 15, 0, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 4⟩) (by decide) node_17742

theorem node_19629 : Outcome ⟨17, 15, 0, 8⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 4⟩) (by decide) node_17742

theorem node_19630 : Outcome ⟨18, 0, 14, 2⟩ true :=
  Outcome.win (q := ⟨18, 0, 13, 2⟩) (by decide) node_18732

theorem node_19631 : Outcome ⟨18, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 2⟩) (by decide) node_18698

theorem node_19632 : Outcome ⟨18, 1, 13, 12⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 2⟩) (by decide) node_18698

theorem node_19633 : Outcome ⟨18, 2, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 2, 12, 2⟩, ⟨16, 2, 12, 4⟩, ⟨18, 1, 12, 2⟩, ⟨18, 0, 12, 4⟩, ⟨18, 2, 11, 2⟩, ⟨18, 2, 10, 4⟩]
  exact AllWinning.cons node_18704 (AllWinning.cons node_17753 (AllWinning.cons node_18735 (AllWinning.cons node_17822 (AllWinning.cons node_18739 (AllWinning.cons node_17827 (AllWinning.nil))))))

theorem node_19634 : Outcome ⟨18, 2, 12, 6⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 10⟩) (by decide) node_14871

theorem node_19635 : Outcome ⟨18, 2, 12, 8⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 10⟩) (by decide) node_14871

theorem node_19636 : Outcome ⟨18, 3, 11, 2⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 2⟩) (by decide) node_18742

theorem node_19637 : Outcome ⟨18, 3, 11, 8⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 2⟩) (by decide) node_18742

theorem node_19638 : Outcome ⟨18, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 2⟩) (by decide) node_18742

theorem node_19639 : Outcome ⟨18, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 2⟩) (by decide) node_18742

theorem node_19640 : Outcome ⟨18, 5, 9, 6⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 8⟩) (by decide) node_15692

theorem node_19641 : Outcome ⟨18, 6, 8, 4⟩ true :=
  Outcome.win (q := ⟨18, 5, 8, 2⟩) (by decide) node_18748

theorem node_19642 : Outcome ⟨18, 7, 7, 12⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 10⟩) (by decide) node_14871

theorem node_19643 : Outcome ⟨18, 8, 6, 4⟩ true :=
  Outcome.win (q := ⟨18, 8, 5, 2⟩) (by decide) node_18757

theorem node_19644 : Outcome ⟨18, 9, 5, 6⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 8⟩) (by decide) node_15704

theorem node_19645 : Outcome ⟨18, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 2⟩) (by decide) node_18762

theorem node_19646 : Outcome ⟨18, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 2⟩) (by decide) node_18762

theorem node_19647 : Outcome ⟨18, 11, 3, 2⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 2⟩) (by decide) node_18762

theorem node_19648 : Outcome ⟨18, 11, 3, 8⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 2⟩) (by decide) node_18762

theorem node_19649 : Outcome ⟨18, 12, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 12, 2, 2⟩, ⟨16, 12, 2, 4⟩, ⟨18, 11, 2, 2⟩, ⟨18, 10, 2, 4⟩, ⟨18, 12, 1, 2⟩, ⟨18, 12, 0, 4⟩]
  exact AllWinning.cons node_18723 (AllWinning.cons node_17778 (AllWinning.cons node_18766 (AllWinning.cons node_17848 (AllWinning.cons node_18769 (AllWinning.cons node_17853 (AllWinning.nil))))))

theorem node_19650 : Outcome ⟨18, 12, 2, 6⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 10⟩) (by decide) node_14892

theorem node_19651 : Outcome ⟨18, 12, 2, 8⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 10⟩) (by decide) node_14892

theorem node_19652 : Outcome ⟨18, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 2⟩) (by decide) node_18724

theorem node_19653 : Outcome ⟨18, 13, 1, 12⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 2⟩) (by decide) node_18724

theorem node_19654 : Outcome ⟨18, 14, 0, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 0, 2⟩) (by decide) node_18772

theorem node_19655 : Outcome ⟨19, 0, 13, 2⟩ true :=
  Outcome.win (q := ⟨19, 0, 11, 4⟩) (by decide) node_17855

theorem node_19656 : Outcome ⟨19, 0, 13, 4⟩ true :=
  Outcome.win (q := ⟨19, 0, 11, 4⟩) (by decide) node_17855

theorem node_19657 : Outcome ⟨19, 0, 13, 12⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 12⟩) (by decide) node_13708

theorem node_19658 : Outcome ⟨19, 0, 13, 16⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 12⟩) (by decide) node_13708

theorem node_19659 : Outcome ⟨19, 1, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 12, 2⟩, ⟨17, 1, 12, 4⟩, ⟨16, 1, 12, 6⟩, ⟨15, 1, 12, 8⟩, ⟨19, 0, 12, 2⟩, ⟨19, 1, 11, 2⟩, ⟨19, 1, 10, 4⟩, ⟨19, 1, 9, 6⟩, ⟨19, 1, 8, 8⟩]
  exact AllWinning.cons node_18735 (AllWinning.cons node_17790 (AllWinning.cons node_16821 (AllWinning.cons node_15735 (AllWinning.cons node_18775 (AllWinning.cons node_18778 (AllWinning.cons node_17858 (AllWinning.cons node_16942 (AllWinning.cons node_15881 (AllWinning.nil)))))))))

theorem node_19660 : Outcome ⟨19, 1, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 12, 2⟩, ⟨17, 1, 12, 4⟩, ⟨16, 1, 12, 6⟩, ⟨15, 1, 12, 8⟩, ⟨14, 1, 12, 10⟩, ⟨13, 1, 12, 12⟩, ⟨19, 0, 12, 2⟩, ⟨19, 1, 11, 2⟩, ⟨19, 1, 10, 4⟩, ⟨19, 1, 9, 6⟩, ⟨19, 1, 8, 8⟩, ⟨19, 1, 7, 10⟩, ⟨19, 1, 6, 12⟩]
  exact AllWinning.cons node_18735 (AllWinning.cons node_17790 (AllWinning.cons node_16821 (AllWinning.cons node_15735 (AllWinning.cons node_14715 (AllWinning.cons node_13715 (AllWinning.cons node_18775 (AllWinning.cons node_18778 (AllWinning.cons node_17858 (AllWinning.cons node_16942 (AllWinning.cons node_15881 (AllWinning.cons node_14904 (AllWinning.cons node_13932 (AllWinning.nil)))))))))))))

theorem node_19661 : Outcome ⟨19, 2, 11, 2⟩ true :=
  Outcome.win (q := ⟨17, 2, 11, 4⟩) (by decide) node_17792

theorem node_19662 : Outcome ⟨19, 2, 11, 4⟩ true :=
  Outcome.win (q := ⟨19, 2, 8, 6⟩) (by decide) node_16943

theorem node_19663 : Outcome ⟨19, 2, 11, 12⟩ true :=
  Outcome.win (q := ⟨19, 2, 8, 6⟩) (by decide) node_16943

theorem node_19664 : Outcome ⟨19, 3, 10, 2⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 2⟩) (by decide) node_18742

theorem node_19665 : Outcome ⟨19, 3, 10, 4⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 2⟩) (by decide) node_18742

theorem node_19666 : Outcome ⟨19, 4, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 4, 9, 2⟩, ⟨17, 4, 9, 4⟩, ⟨19, 3, 9, 2⟩, ⟨19, 2, 9, 4⟩, ⟨19, 4, 8, 2⟩, ⟨19, 4, 7, 4⟩]
  exact AllWinning.cons node_18746 (AllWinning.cons node_17799 (AllWinning.cons node_18781 (AllWinning.cons node_17860 (AllWinning.cons node_18783 (AllWinning.cons node_17863 (AllWinning.nil))))))

theorem node_19667 : Outcome ⟨19, 4, 9, 10⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 6⟩) (by decide) node_16830

theorem node_19668 : Outcome ⟨19, 5, 8, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 8⟩) (by decide) node_15747

theorem node_19669 : Outcome ⟨19, 5, 8, 16⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 8⟩) (by decide) node_15747

theorem node_19670 : Outcome ⟨19, 6, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 6, 7, 2⟩, ⟨17, 6, 7, 4⟩, ⟨16, 6, 7, 6⟩, ⟨15, 6, 7, 8⟩, ⟨14, 6, 7, 10⟩, ⟨13, 6, 7, 12⟩, ⟨12, 6, 7, 14⟩, ⟨11, 6, 7, 16⟩, ⟨19, 5, 7, 2⟩, ⟨19, 4, 7, 4⟩, ⟨19, 3, 7, 6⟩, ⟨19, 2, 7, 8⟩, ⟨19, 1, 7, 10⟩, ⟨19, 0, 7, 12⟩, ⟨19, 6, 6, 2⟩, ⟨19, 6, 5, 4⟩, ⟨19, 6, 4, 6⟩, ⟨19, 6, 3, 8⟩, ⟨19, 6, 2, 10⟩, ⟨19, 6, 1, 12⟩, ⟨19, 6, 0, 14⟩]
  exact AllWinning.cons node_18751 (AllWinning.cons node_17802 (AllWinning.cons node_16839 (AllWinning.cons node_15756 (AllWinning.cons node_14728 (AllWinning.cons node_13735 (AllWinning.cons node_12722 (AllWinning.cons node_11682 (AllWinning.cons node_18785 (AllWinning.cons node_17863 (AllWinning.cons node_16948 (AllWinning.cons node_15883 (AllWinning.cons node_14904 (AllWinning.cons node_13929 (AllWinning.cons node_18787 (AllWinning.cons node_17867 (AllWinning.cons node_16955 (AllWinning.cons node_15893 (AllWinning.cons node_14913 (AllWinning.cons node_13940 (AllWinning.cons node_12977 (AllWinning.nil)))))))))))))))))))))

theorem node_19671 : Outcome ⟨19, 6, 7, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 6, 7, 2⟩, ⟨17, 6, 7, 4⟩, ⟨16, 6, 7, 6⟩, ⟨15, 6, 7, 8⟩, ⟨14, 6, 7, 10⟩, ⟨13, 6, 7, 12⟩, ⟨12, 6, 7, 14⟩, ⟨11, 6, 7, 16⟩, ⟨10, 6, 7, 18⟩, ⟨9, 6, 7, 20⟩, ⟨19, 5, 7, 2⟩, ⟨19, 4, 7, 4⟩, ⟨19, 3, 7, 6⟩, ⟨19, 2, 7, 8⟩, ⟨19, 1, 7, 10⟩, ⟨19, 0, 7, 12⟩, ⟨19, 6, 6, 2⟩, ⟨19, 6, 5, 4⟩, ⟨19, 6, 4, 6⟩, ⟨19, 6, 3, 8⟩, ⟨19, 6, 2, 10⟩, ⟨19, 6, 1, 12⟩, ⟨19, 6, 0, 14⟩]
  exact AllWinning.cons node_18751 (AllWinning.cons node_17802 (AllWinning.cons node_16839 (AllWinning.cons node_15756 (AllWinning.cons node_14728 (AllWinning.cons node_13735 (AllWinning.cons node_12722 (AllWinning.cons node_11682 (AllWinning.cons node_10629 (AllWinning.cons node_9537 (AllWinning.cons node_18785 (AllWinning.cons node_17863 (AllWinning.cons node_16948 (AllWinning.cons node_15883 (AllWinning.cons node_14904 (AllWinning.cons node_13929 (AllWinning.cons node_18787 (AllWinning.cons node_17867 (AllWinning.cons node_16955 (AllWinning.cons node_15893 (AllWinning.cons node_14913 (AllWinning.cons node_13940 (AllWinning.cons node_12977 (AllWinning.nil)))))))))))))))))))))))

theorem node_19672 : Outcome ⟨19, 7, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 7, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨16, 7, 6, 6⟩, ⟨15, 7, 6, 8⟩, ⟨14, 7, 6, 10⟩, ⟨13, 7, 6, 12⟩, ⟨12, 7, 6, 14⟩, ⟨11, 7, 6, 16⟩, ⟨19, 6, 6, 2⟩, ⟨19, 5, 6, 4⟩, ⟨19, 4, 6, 6⟩, ⟨19, 3, 6, 8⟩, ⟨19, 2, 6, 10⟩, ⟨19, 1, 6, 12⟩, ⟨19, 0, 6, 14⟩, ⟨19, 7, 5, 2⟩, ⟨19, 7, 4, 4⟩, ⟨19, 7, 3, 6⟩, ⟨19, 7, 2, 8⟩, ⟨19, 7, 1, 10⟩, ⟨19, 7, 0, 12⟩]
  exact AllWinning.cons node_18754 (AllWinning.cons node_17804 (AllWinning.cons node_16843 (AllWinning.cons node_15760 (AllWinning.cons node_14733 (AllWinning.cons node_13740 (AllWinning.cons node_12726 (AllWinning.cons node_11686 (AllWinning.cons node_18787 (AllWinning.cons node_17865 (AllWinning.cons node_16951 (AllWinning.cons node_15885 (AllWinning.cons node_14906 (AllWinning.cons node_13932 (AllWinning.cons node_12959 (AllWinning.cons node_18788 (AllWinning.cons node_17869 (AllWinning.cons node_16957 (AllWinning.cons node_15895 (AllWinning.cons node_14915 (AllWinning.cons node_13942 (AllWinning.nil)))))))))))))))))))))

theorem node_19673 : Outcome ⟨19, 7, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 7, 6, 2⟩, ⟨17, 7, 6, 4⟩, ⟨16, 7, 6, 6⟩, ⟨15, 7, 6, 8⟩, ⟨14, 7, 6, 10⟩, ⟨13, 7, 6, 12⟩, ⟨12, 7, 6, 14⟩, ⟨11, 7, 6, 16⟩, ⟨10, 7, 6, 18⟩, ⟨9, 7, 6, 20⟩, ⟨19, 6, 6, 2⟩, ⟨19, 5, 6, 4⟩, ⟨19, 4, 6, 6⟩, ⟨19, 3, 6, 8⟩, ⟨19, 2, 6, 10⟩, ⟨19, 1, 6, 12⟩, ⟨19, 0, 6, 14⟩, ⟨19, 7, 5, 2⟩, ⟨19, 7, 4, 4⟩, ⟨19, 7, 3, 6⟩, ⟨19, 7, 2, 8⟩, ⟨19, 7, 1, 10⟩, ⟨19, 7, 0, 12⟩]
  exact AllWinning.cons node_18754 (AllWinning.cons node_17804 (AllWinning.cons node_16843 (AllWinning.cons node_15760 (AllWinning.cons node_14733 (AllWinning.cons node_13740 (AllWinning.cons node_12726 (AllWinning.cons node_11686 (AllWinning.cons node_10635 (AllWinning.cons node_9542 (AllWinning.cons node_18787 (AllWinning.cons node_17865 (AllWinning.cons node_16951 (AllWinning.cons node_15885 (AllWinning.cons node_14906 (AllWinning.cons node_13932 (AllWinning.cons node_12959 (AllWinning.cons node_18788 (AllWinning.cons node_17869 (AllWinning.cons node_16957 (AllWinning.cons node_15895 (AllWinning.cons node_14915 (AllWinning.cons node_13942 (AllWinning.nil)))))))))))))))))))))))

theorem node_19674 : Outcome ⟨19, 8, 5, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 8⟩) (by decide) node_15764

theorem node_19675 : Outcome ⟨19, 8, 5, 16⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 8⟩) (by decide) node_15764

theorem node_19676 : Outcome ⟨19, 9, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 9, 4, 2⟩, ⟨17, 9, 4, 4⟩, ⟨19, 8, 4, 2⟩, ⟨19, 7, 4, 4⟩, ⟨19, 9, 3, 2⟩, ⟨19, 9, 2, 4⟩]
  exact AllWinning.cons node_18760 (AllWinning.cons node_17809 (AllWinning.cons node_18790 (AllWinning.cons node_17869 (AllWinning.cons node_18792 (AllWinning.cons node_17872 (AllWinning.nil))))))

theorem node_19677 : Outcome ⟨19, 9, 4, 10⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 6⟩) (by decide) node_16848

theorem node_19678 : Outcome ⟨19, 10, 3, 2⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 2⟩) (by decide) node_18762

theorem node_19679 : Outcome ⟨19, 10, 3, 4⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 2⟩) (by decide) node_18762

theorem node_19680 : Outcome ⟨19, 11, 2, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 2, 4⟩) (by decide) node_17814

theorem node_19681 : Outcome ⟨19, 11, 2, 4⟩ true :=
  Outcome.win (q := ⟨19, 8, 2, 6⟩) (by decide) node_16959

theorem node_19682 : Outcome ⟨19, 11, 2, 12⟩ true :=
  Outcome.win (q := ⟨19, 8, 2, 6⟩) (by decide) node_16959

theorem node_19683 : Outcome ⟨19, 12, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 12, 1, 2⟩, ⟨17, 12, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨19, 11, 1, 2⟩, ⟨19, 10, 1, 4⟩, ⟨19, 9, 1, 6⟩, ⟨19, 8, 1, 8⟩, ⟨19, 12, 0, 2⟩]
  exact AllWinning.cons node_18769 (AllWinning.cons node_17818 (AllWinning.cons node_16861 (AllWinning.cons node_15781 (AllWinning.cons node_18795 (AllWinning.cons node_17874 (AllWinning.cons node_16965 (AllWinning.cons node_15897 (AllWinning.cons node_18797 (AllWinning.nil)))))))))

theorem node_19684 : Outcome ⟨19, 12, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 12, 1, 2⟩, ⟨17, 12, 1, 4⟩, ⟨16, 12, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨14, 12, 1, 10⟩, ⟨13, 12, 1, 12⟩, ⟨19, 11, 1, 2⟩, ⟨19, 10, 1, 4⟩, ⟨19, 9, 1, 6⟩, ⟨19, 8, 1, 8⟩, ⟨19, 7, 1, 10⟩, ⟨19, 6, 1, 12⟩, ⟨19, 12, 0, 2⟩]
  exact AllWinning.cons node_18769 (AllWinning.cons node_17818 (AllWinning.cons node_16861 (AllWinning.cons node_15781 (AllWinning.cons node_14746 (AllWinning.cons node_13760 (AllWinning.cons node_18795 (AllWinning.cons node_17874 (AllWinning.cons node_16965 (AllWinning.cons node_15897 (AllWinning.cons node_14915 (AllWinning.cons node_13940 (AllWinning.cons node_18797 (AllWinning.nil)))))))))))))

theorem node_19685 : Outcome ⟨19, 13, 0, 2⟩ true :=
  Outcome.win (q := ⟨19, 11, 0, 4⟩) (by decide) node_17876

theorem node_19686 : Outcome ⟨19, 13, 0, 4⟩ true :=
  Outcome.win (q := ⟨19, 11, 0, 4⟩) (by decide) node_17876

theorem node_19687 : Outcome ⟨19, 13, 0, 12⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 12⟩) (by decide) node_13766

theorem node_19688 : Outcome ⟨19, 13, 0, 16⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 12⟩) (by decide) node_13766

theorem node_19689 : Outcome ⟨0, 13, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 18, 4⟩) (by decide) node_17886

theorem node_19690 : Outcome ⟨0, 13, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 18, 4⟩) (by decide) node_17886

theorem node_19691 : Outcome ⟨0, 13, 20, 8⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 14⟩) (by decide) node_13007

theorem node_19692 : Outcome ⟨0, 13, 20, 14⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 14⟩) (by decide) node_13007

theorem node_19693 : Outcome ⟨0, 14, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 19, 2⟩, ⟨0, 12, 19, 4⟩, ⟨0, 14, 18, 2⟩, ⟨0, 14, 17, 4⟩]
  exact AllWinning.cons node_18803 (AllWinning.cons node_17883 (AllWinning.cons node_18807 (AllWinning.cons node_17889 (AllWinning.nil))))

end RQ9F1
