import Chunk84
set_option autoImplicit false
namespace RQ9F1

theorem node_18695 : Outcome ⟨16, 15, 0, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 2⟩) (by decide) node_17741

theorem node_18696 : Outcome ⟨17, 0, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18697 : Outcome ⟨17, 0, 14, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 6⟩) (by decide) node_15664

theorem node_18698 : Outcome ⟨17, 1, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 13, 2⟩, ⟨15, 1, 13, 4⟩, ⟨17, 0, 13, 2⟩, ⟨17, 1, 12, 2⟩, ⟨17, 1, 11, 4⟩]
  exact AllWinning.cons node_17751 (AllWinning.cons node_16782 (AllWinning.cons node_17787 (AllWinning.cons node_17789 (AllWinning.cons node_16869 (AllWinning.nil)))))

theorem node_18699 : Outcome ⟨17, 1, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 13, 2⟩, ⟨15, 1, 13, 4⟩, ⟨14, 1, 13, 6⟩, ⟨13, 1, 13, 8⟩, ⟨17, 0, 13, 2⟩, ⟨17, 1, 12, 2⟩, ⟨17, 1, 11, 4⟩, ⟨17, 1, 10, 6⟩, ⟨17, 1, 9, 8⟩]
  exact AllWinning.cons node_17751 (AllWinning.cons node_16782 (AllWinning.cons node_15673 (AllWinning.cons node_14678 (AllWinning.cons node_17787 (AllWinning.cons node_17789 (AllWinning.cons node_16869 (AllWinning.cons node_15824 (AllWinning.cons node_14839 (AllWinning.nil)))))))))

theorem node_18700 : Outcome ⟨17, 1, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 13, 2⟩, ⟨15, 1, 13, 4⟩, ⟨14, 1, 13, 6⟩, ⟨13, 1, 13, 8⟩, ⟨12, 1, 13, 10⟩, ⟨11, 1, 13, 12⟩, ⟨17, 0, 13, 2⟩, ⟨17, 1, 12, 2⟩, ⟨17, 1, 11, 4⟩, ⟨17, 1, 10, 6⟩, ⟨17, 1, 9, 8⟩, ⟨17, 1, 8, 10⟩, ⟨17, 1, 7, 12⟩]
  exact AllWinning.cons node_17751 (AllWinning.cons node_16782 (AllWinning.cons node_15673 (AllWinning.cons node_14678 (AllWinning.cons node_13659 (AllWinning.cons node_12656 (AllWinning.cons node_17787 (AllWinning.cons node_17789 (AllWinning.cons node_16869 (AllWinning.cons node_15824 (AllWinning.cons node_14839 (AllWinning.cons node_13878 (AllWinning.cons node_12910 (AllWinning.nil)))))))))))))

theorem node_18701 : Outcome ⟨17, 1, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 13, 2⟩, ⟨15, 1, 13, 4⟩, ⟨14, 1, 13, 6⟩, ⟨13, 1, 13, 8⟩, ⟨12, 1, 13, 10⟩, ⟨11, 1, 13, 12⟩, ⟨10, 1, 13, 14⟩, ⟨9, 1, 13, 16⟩, ⟨17, 0, 13, 2⟩, ⟨17, 1, 12, 2⟩, ⟨17, 1, 11, 4⟩, ⟨17, 1, 10, 6⟩, ⟨17, 1, 9, 8⟩, ⟨17, 1, 8, 10⟩, ⟨17, 1, 7, 12⟩, ⟨17, 1, 6, 14⟩, ⟨17, 1, 5, 16⟩]
  exact AllWinning.cons node_17751 (AllWinning.cons node_16782 (AllWinning.cons node_15673 (AllWinning.cons node_14678 (AllWinning.cons node_13659 (AllWinning.cons node_12656 (AllWinning.cons node_11614 (AllWinning.cons node_10560 (AllWinning.cons node_17787 (AllWinning.cons node_17789 (AllWinning.cons node_16869 (AllWinning.cons node_15824 (AllWinning.cons node_14839 (AllWinning.cons node_13878 (AllWinning.cons node_12910 (AllWinning.cons node_11904 (AllWinning.cons node_10916 (AllWinning.nil)))))))))))))))))

theorem node_18702 : Outcome ⟨17, 1, 13, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 13, 2⟩, ⟨15, 1, 13, 4⟩, ⟨14, 1, 13, 6⟩, ⟨13, 1, 13, 8⟩, ⟨12, 1, 13, 10⟩, ⟨11, 1, 13, 12⟩, ⟨10, 1, 13, 14⟩, ⟨9, 1, 13, 16⟩, ⟨8, 1, 13, 18⟩, ⟨7, 1, 13, 20⟩, ⟨17, 0, 13, 2⟩, ⟨17, 1, 12, 2⟩, ⟨17, 1, 11, 4⟩, ⟨17, 1, 10, 6⟩, ⟨17, 1, 9, 8⟩, ⟨17, 1, 8, 10⟩, ⟨17, 1, 7, 12⟩, ⟨17, 1, 6, 14⟩, ⟨17, 1, 5, 16⟩, ⟨17, 1, 4, 18⟩, ⟨17, 1, 3, 20⟩]
  exact AllWinning.cons node_17751 (AllWinning.cons node_16782 (AllWinning.cons node_15673 (AllWinning.cons node_14678 (AllWinning.cons node_13659 (AllWinning.cons node_12656 (AllWinning.cons node_11614 (AllWinning.cons node_10560 (AllWinning.cons node_9473 (AllWinning.cons node_8423 (AllWinning.cons node_17787 (AllWinning.cons node_17789 (AllWinning.cons node_16869 (AllWinning.cons node_15824 (AllWinning.cons node_14839 (AllWinning.cons node_13878 (AllWinning.cons node_12910 (AllWinning.cons node_11904 (AllWinning.cons node_10916 (AllWinning.cons node_9835 (AllWinning.cons node_8879 (AllWinning.nil)))))))))))))))))))))

theorem node_18703 : Outcome ⟨17, 1, 13, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 13, 2⟩, ⟨15, 1, 13, 4⟩, ⟨14, 1, 13, 6⟩, ⟨13, 1, 13, 8⟩, ⟨12, 1, 13, 10⟩, ⟨11, 1, 13, 12⟩, ⟨10, 1, 13, 14⟩, ⟨9, 1, 13, 16⟩, ⟨8, 1, 13, 18⟩, ⟨7, 1, 13, 20⟩, ⟨6, 1, 13, 22⟩, ⟨5, 1, 13, 24⟩, ⟨4, 1, 13, 26⟩, ⟨3, 1, 13, 28⟩, ⟨17, 0, 13, 2⟩, ⟨17, 1, 12, 2⟩, ⟨17, 1, 11, 4⟩, ⟨17, 1, 10, 6⟩, ⟨17, 1, 9, 8⟩, ⟨17, 1, 8, 10⟩, ⟨17, 1, 7, 12⟩, ⟨17, 1, 6, 14⟩, ⟨17, 1, 5, 16⟩, ⟨17, 1, 4, 18⟩, ⟨17, 1, 3, 20⟩, ⟨17, 1, 2, 22⟩, ⟨17, 1, 1, 24⟩, ⟨17, 1, 0, 26⟩]
  exact AllWinning.cons node_17751 (AllWinning.cons node_16782 (AllWinning.cons node_15673 (AllWinning.cons node_14678 (AllWinning.cons node_13659 (AllWinning.cons node_12656 (AllWinning.cons node_11614 (AllWinning.cons node_10560 (AllWinning.cons node_9473 (AllWinning.cons node_8423 (AllWinning.cons node_7417 (AllWinning.cons node_6427 (AllWinning.cons node_5584 (AllWinning.cons node_4819 (AllWinning.cons node_17787 (AllWinning.cons node_17789 (AllWinning.cons node_16869 (AllWinning.cons node_15824 (AllWinning.cons node_14839 (AllWinning.cons node_13878 (AllWinning.cons node_12910 (AllWinning.cons node_11904 (AllWinning.cons node_10916 (AllWinning.cons node_9835 (AllWinning.cons node_8879 (AllWinning.cons node_7885 (AllWinning.cons node_6935 (AllWinning.cons node_6032 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_18704 : Outcome ⟨17, 2, 12, 2⟩ true :=
  Outcome.win (q := ⟨17, 0, 12, 4⟩) (by decide) node_16866

theorem node_18705 : Outcome ⟨17, 3, 11, 4⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 4⟩) (by decide) node_16873

theorem node_18706 : Outcome ⟨17, 3, 11, 6⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 4⟩) (by decide) node_16873

theorem node_18707 : Outcome ⟨17, 3, 11, 10⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 4⟩) (by decide) node_16873

theorem node_18708 : Outcome ⟨17, 4, 10, 6⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 4⟩) (by decide) node_16877

theorem node_18709 : Outcome ⟨17, 4, 10, 12⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 22⟩) (by decide) node_7436

theorem node_18710 : Outcome ⟨17, 5, 9, 2⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 4⟩) (by decide) node_16873

theorem node_18711 : Outcome ⟨17, 5, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 6⟩) (by decide) node_15691

theorem node_18712 : Outcome ⟨17, 6, 8, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 4⟩) (by decide) node_16877

theorem node_18713 : Outcome ⟨17, 7, 7, 2⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 4⟩) (by decide) node_16881

theorem node_18714 : Outcome ⟨17, 7, 7, 6⟩ true :=
  Outcome.win (q := ⟨12, 7, 7, 10⟩) (by decide) node_13680

theorem node_18715 : Outcome ⟨17, 8, 6, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 6, 4⟩) (by decide) node_16887

theorem node_18716 : Outcome ⟨17, 8, 6, 10⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 20⟩) (by decide) node_8468

theorem node_18717 : Outcome ⟨17, 9, 5, 2⟩ true :=
  Outcome.win (q := ⟨17, 7, 5, 4⟩) (by decide) node_16889

theorem node_18718 : Outcome ⟨17, 9, 5, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 5, 6⟩) (by decide) node_15703

theorem node_18719 : Outcome ⟨17, 10, 4, 6⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 4⟩) (by decide) node_16895

theorem node_18720 : Outcome ⟨17, 10, 4, 12⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 22⟩) (by decide) node_7465

theorem node_18721 : Outcome ⟨17, 11, 3, 4⟩ true :=
  Outcome.win (q := ⟨17, 9, 3, 4⟩) (by decide) node_16900

theorem node_18722 : Outcome ⟨17, 11, 3, 6⟩ true :=
  Outcome.win (q := ⟨17, 9, 3, 4⟩) (by decide) node_16900

theorem node_18723 : Outcome ⟨17, 12, 2, 2⟩ true :=
  Outcome.win (q := ⟨17, 12, 0, 4⟩) (by decide) node_16908

theorem node_18724 : Outcome ⟨17, 13, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 1, 2⟩, ⟨15, 13, 1, 4⟩, ⟨17, 12, 1, 2⟩, ⟨17, 11, 1, 4⟩, ⟨17, 13, 0, 2⟩]
  exact AllWinning.cons node_17781 (AllWinning.cons node_16812 (AllWinning.cons node_17817 (AllWinning.cons node_16906 (AllWinning.cons node_17819 (AllWinning.nil)))))

theorem node_18725 : Outcome ⟨17, 13, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 1, 2⟩, ⟨15, 13, 1, 4⟩, ⟨14, 13, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨17, 12, 1, 2⟩, ⟨17, 11, 1, 4⟩, ⟨17, 10, 1, 6⟩, ⟨17, 9, 1, 8⟩, ⟨17, 13, 0, 2⟩]
  exact AllWinning.cons node_17781 (AllWinning.cons node_16812 (AllWinning.cons node_15720 (AllWinning.cons node_14705 (AllWinning.cons node_17817 (AllWinning.cons node_16906 (AllWinning.cons node_15842 (AllWinning.cons node_14856 (AllWinning.cons node_17819 (AllWinning.nil)))))))))

theorem node_18726 : Outcome ⟨17, 13, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 1, 2⟩, ⟨15, 13, 1, 4⟩, ⟨14, 13, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨12, 13, 1, 10⟩, ⟨11, 13, 1, 12⟩, ⟨17, 12, 1, 2⟩, ⟨17, 11, 1, 4⟩, ⟨17, 10, 1, 6⟩, ⟨17, 9, 1, 8⟩, ⟨17, 8, 1, 10⟩, ⟨17, 7, 1, 12⟩, ⟨17, 13, 0, 2⟩]
  exact AllWinning.cons node_17781 (AllWinning.cons node_16812 (AllWinning.cons node_15720 (AllWinning.cons node_14705 (AllWinning.cons node_13699 (AllWinning.cons node_12699 (AllWinning.cons node_17817 (AllWinning.cons node_16906 (AllWinning.cons node_15842 (AllWinning.cons node_14856 (AllWinning.cons node_13901 (AllWinning.cons node_12932 (AllWinning.cons node_17819 (AllWinning.nil)))))))))))))

theorem node_18727 : Outcome ⟨17, 13, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 1, 2⟩, ⟨15, 13, 1, 4⟩, ⟨14, 13, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨12, 13, 1, 10⟩, ⟨11, 13, 1, 12⟩, ⟨10, 13, 1, 14⟩, ⟨9, 13, 1, 16⟩, ⟨17, 12, 1, 2⟩, ⟨17, 11, 1, 4⟩, ⟨17, 10, 1, 6⟩, ⟨17, 9, 1, 8⟩, ⟨17, 8, 1, 10⟩, ⟨17, 7, 1, 12⟩, ⟨17, 6, 1, 14⟩, ⟨17, 5, 1, 16⟩, ⟨17, 13, 0, 2⟩]
  exact AllWinning.cons node_17781 (AllWinning.cons node_16812 (AllWinning.cons node_15720 (AllWinning.cons node_14705 (AllWinning.cons node_13699 (AllWinning.cons node_12699 (AllWinning.cons node_11654 (AllWinning.cons node_10597 (AllWinning.cons node_17817 (AllWinning.cons node_16906 (AllWinning.cons node_15842 (AllWinning.cons node_14856 (AllWinning.cons node_13901 (AllWinning.cons node_12932 (AllWinning.cons node_11923 (AllWinning.cons node_10932 (AllWinning.cons node_17819 (AllWinning.nil)))))))))))))))))

theorem node_18728 : Outcome ⟨17, 13, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 1, 2⟩, ⟨15, 13, 1, 4⟩, ⟨14, 13, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨12, 13, 1, 10⟩, ⟨11, 13, 1, 12⟩, ⟨10, 13, 1, 14⟩, ⟨9, 13, 1, 16⟩, ⟨8, 13, 1, 18⟩, ⟨7, 13, 1, 20⟩, ⟨17, 12, 1, 2⟩, ⟨17, 11, 1, 4⟩, ⟨17, 10, 1, 6⟩, ⟨17, 9, 1, 8⟩, ⟨17, 8, 1, 10⟩, ⟨17, 7, 1, 12⟩, ⟨17, 6, 1, 14⟩, ⟨17, 5, 1, 16⟩, ⟨17, 4, 1, 18⟩, ⟨17, 3, 1, 20⟩, ⟨17, 13, 0, 2⟩]
  exact AllWinning.cons node_17781 (AllWinning.cons node_16812 (AllWinning.cons node_15720 (AllWinning.cons node_14705 (AllWinning.cons node_13699 (AllWinning.cons node_12699 (AllWinning.cons node_11654 (AllWinning.cons node_10597 (AllWinning.cons node_9511 (AllWinning.cons node_8493 (AllWinning.cons node_17817 (AllWinning.cons node_16906 (AllWinning.cons node_15842 (AllWinning.cons node_14856 (AllWinning.cons node_13901 (AllWinning.cons node_12932 (AllWinning.cons node_11923 (AllWinning.cons node_10932 (AllWinning.cons node_9847 (AllWinning.cons node_8885 (AllWinning.cons node_17819 (AllWinning.nil)))))))))))))))))))))

theorem node_18729 : Outcome ⟨17, 13, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 1, 2⟩, ⟨15, 13, 1, 4⟩, ⟨14, 13, 1, 6⟩, ⟨13, 13, 1, 8⟩, ⟨12, 13, 1, 10⟩, ⟨11, 13, 1, 12⟩, ⟨10, 13, 1, 14⟩, ⟨9, 13, 1, 16⟩, ⟨8, 13, 1, 18⟩, ⟨7, 13, 1, 20⟩, ⟨6, 13, 1, 22⟩, ⟨5, 13, 1, 24⟩, ⟨4, 13, 1, 26⟩, ⟨3, 13, 1, 28⟩, ⟨17, 12, 1, 2⟩, ⟨17, 11, 1, 4⟩, ⟨17, 10, 1, 6⟩, ⟨17, 9, 1, 8⟩, ⟨17, 8, 1, 10⟩, ⟨17, 7, 1, 12⟩, ⟨17, 6, 1, 14⟩, ⟨17, 5, 1, 16⟩, ⟨17, 4, 1, 18⟩, ⟨17, 3, 1, 20⟩, ⟨17, 2, 1, 22⟩, ⟨17, 1, 1, 24⟩, ⟨17, 0, 1, 26⟩, ⟨17, 13, 0, 2⟩]
  exact AllWinning.cons node_17781 (AllWinning.cons node_16812 (AllWinning.cons node_15720 (AllWinning.cons node_14705 (AllWinning.cons node_13699 (AllWinning.cons node_12699 (AllWinning.cons node_11654 (AllWinning.cons node_10597 (AllWinning.cons node_9511 (AllWinning.cons node_8493 (AllWinning.cons node_7475 (AllWinning.cons node_6482 (AllWinning.cons node_5627 (AllWinning.cons node_4868 (AllWinning.cons node_17817 (AllWinning.cons node_16906 (AllWinning.cons node_15842 (AllWinning.cons node_14856 (AllWinning.cons node_13901 (AllWinning.cons node_12932 (AllWinning.cons node_11923 (AllWinning.cons node_10932 (AllWinning.cons node_9847 (AllWinning.cons node_8885 (AllWinning.cons node_7892 (AllWinning.cons node_6935 (AllWinning.cons node_6028 (AllWinning.cons node_17819 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_18730 : Outcome ⟨17, 14, 0, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18731 : Outcome ⟨17, 14, 0, 6⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 6⟩) (by decide) node_15724

theorem node_18732 : Outcome ⟨18, 0, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 13, 2⟩, ⟨16, 0, 13, 4⟩, ⟨18, 0, 12, 2⟩, ⟨18, 0, 11, 4⟩]
  exact AllWinning.cons node_17787 (AllWinning.cons node_16817 (AllWinning.cons node_17821 (AllWinning.cons node_16911 (AllWinning.nil))))

theorem node_18733 : Outcome ⟨18, 0, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 13, 2⟩, ⟨16, 0, 13, 4⟩, ⟨15, 0, 13, 6⟩, ⟨14, 0, 13, 8⟩, ⟨18, 0, 12, 2⟩, ⟨18, 0, 11, 4⟩, ⟨18, 0, 10, 6⟩, ⟨18, 0, 9, 8⟩]
  exact AllWinning.cons node_17787 (AllWinning.cons node_16817 (AllWinning.cons node_15732 (AllWinning.cons node_14711 (AllWinning.cons node_17821 (AllWinning.cons node_16911 (AllWinning.cons node_15849 (AllWinning.cons node_14863 (AllWinning.nil))))))))

theorem node_18734 : Outcome ⟨18, 0, 13, 14⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 10⟩) (by decide) node_13707

theorem node_18735 : Outcome ⟨18, 1, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 4⟩) (by decide) node_16820

theorem node_18736 : Outcome ⟨18, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 4⟩) (by decide) node_16820

theorem node_18737 : Outcome ⟨18, 1, 12, 8⟩ true :=
  Outcome.win (q := ⟨16, 1, 12, 4⟩) (by decide) node_16820

theorem node_18738 : Outcome ⟨18, 1, 12, 14⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 20⟩) (by decide) node_8510

theorem node_18739 : Outcome ⟨18, 2, 11, 2⟩ true :=
  Outcome.win (q := ⟨17, 2, 11, 2⟩) (by decide) node_17791

theorem node_18740 : Outcome ⟨18, 2, 11, 4⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 8⟩) (by decide) node_14870

theorem node_18741 : Outcome ⟨18, 2, 11, 10⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 8⟩) (by decide) node_14870

theorem node_18742 : Outcome ⟨18, 3, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 3, 10, 2⟩, ⟨16, 3, 10, 4⟩, ⟨18, 2, 10, 2⟩, ⟨18, 1, 10, 4⟩, ⟨18, 3, 9, 2⟩, ⟨18, 3, 8, 4⟩]
  exact AllWinning.cons node_17796 (AllWinning.cons node_16826 (AllWinning.cons node_17826 (AllWinning.cons node_16913 (AllWinning.cons node_17830 (AllWinning.cons node_16916 (AllWinning.nil))))))

theorem node_18743 : Outcome ⟨18, 3, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 3, 10, 2⟩, ⟨16, 3, 10, 4⟩, ⟨15, 3, 10, 6⟩, ⟨14, 3, 10, 8⟩, ⟨18, 2, 10, 2⟩, ⟨18, 1, 10, 4⟩, ⟨18, 0, 10, 6⟩, ⟨18, 3, 9, 2⟩, ⟨18, 3, 8, 4⟩, ⟨18, 3, 7, 6⟩, ⟨18, 3, 6, 8⟩]
  exact AllWinning.cons node_17796 (AllWinning.cons node_16826 (AllWinning.cons node_15740 (AllWinning.cons node_14719 (AllWinning.cons node_17826 (AllWinning.cons node_16913 (AllWinning.cons node_15849 (AllWinning.cons node_17830 (AllWinning.cons node_16916 (AllWinning.cons node_15856 (AllWinning.cons node_14875 (AllWinning.nil)))))))))))

theorem node_18744 : Outcome ⟨18, 3, 10, 6⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 10⟩) (by decide) node_13723

theorem node_18745 : Outcome ⟨18, 3, 10, 10⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 10⟩) (by decide) node_13723

theorem node_18746 : Outcome ⟨18, 4, 9, 2⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18747 : Outcome ⟨18, 4, 9, 4⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 4⟩) (by decide) node_16829

theorem node_18748 : Outcome ⟨18, 5, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 5, 8, 2⟩, ⟨16, 5, 8, 4⟩, ⟨18, 4, 8, 2⟩, ⟨18, 3, 8, 4⟩, ⟨18, 5, 7, 2⟩, ⟨18, 5, 6, 4⟩]
  exact AllWinning.cons node_17800 (AllWinning.cons node_16836 (AllWinning.cons node_17832 (AllWinning.cons node_16916 (AllWinning.cons node_17835 (AllWinning.cons node_16920 (AllWinning.nil))))))

theorem node_18749 : Outcome ⟨18, 5, 8, 6⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 6⟩) (by decide) node_15746

theorem node_18750 : Outcome ⟨18, 5, 8, 8⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 6⟩) (by decide) node_15746

theorem node_18751 : Outcome ⟨18, 6, 7, 2⟩ true :=
  Outcome.win (q := ⟨16, 6, 7, 4⟩) (by decide) node_16838

theorem node_18752 : Outcome ⟨18, 6, 7, 6⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 8⟩) (by decide) node_14870

theorem node_18753 : Outcome ⟨18, 6, 7, 14⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 20⟩) (by decide) node_8538

theorem node_18754 : Outcome ⟨18, 7, 6, 2⟩ true :=
  Outcome.win (q := ⟨16, 7, 6, 4⟩) (by decide) node_16842

theorem node_18755 : Outcome ⟨18, 7, 6, 6⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 8⟩) (by decide) node_14891

theorem node_18756 : Outcome ⟨18, 7, 6, 14⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 20⟩) (by decide) node_8550

theorem node_18757 : Outcome ⟨18, 8, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 8, 5, 2⟩, ⟨16, 8, 5, 4⟩, ⟨18, 7, 5, 2⟩, ⟨18, 6, 5, 4⟩, ⟨18, 8, 4, 2⟩, ⟨18, 8, 3, 4⟩]
  exact AllWinning.cons node_17806 (AllWinning.cons node_16845 (AllWinning.cons node_17839 (AllWinning.cons node_16923 (AllWinning.cons node_17842 (AllWinning.cons node_16927 (AllWinning.nil))))))

theorem node_18758 : Outcome ⟨18, 8, 5, 6⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 6⟩) (by decide) node_15763

theorem node_18759 : Outcome ⟨18, 8, 5, 8⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 6⟩) (by decide) node_15763

theorem node_18760 : Outcome ⟨18, 9, 4, 2⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 4⟩) (by decide) node_16847

theorem node_18761 : Outcome ⟨18, 9, 4, 4⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 4⟩) (by decide) node_16847

theorem node_18762 : Outcome ⟨18, 10, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 10, 3, 2⟩, ⟨16, 10, 3, 4⟩, ⟨18, 9, 3, 2⟩, ⟨18, 8, 3, 4⟩, ⟨18, 10, 2, 2⟩, ⟨18, 10, 1, 4⟩]
  exact AllWinning.cons node_17810 (AllWinning.cons node_16854 (AllWinning.cons node_17845 (AllWinning.cons node_16927 (AllWinning.cons node_17847 (AllWinning.cons node_16930 (AllWinning.nil))))))

theorem node_18763 : Outcome ⟨18, 10, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 10, 3, 2⟩, ⟨16, 10, 3, 4⟩, ⟨15, 10, 3, 6⟩, ⟨14, 10, 3, 8⟩, ⟨18, 9, 3, 2⟩, ⟨18, 8, 3, 4⟩, ⟨18, 7, 3, 6⟩, ⟨18, 6, 3, 8⟩, ⟨18, 10, 2, 2⟩, ⟨18, 10, 1, 4⟩, ⟨18, 10, 0, 6⟩]
  exact AllWinning.cons node_17810 (AllWinning.cons node_16854 (AllWinning.cons node_15775 (AllWinning.cons node_14740 (AllWinning.cons node_17845 (AllWinning.cons node_16927 (AllWinning.cons node_15867 (AllWinning.cons node_14885 (AllWinning.cons node_17847 (AllWinning.cons node_16930 (AllWinning.cons node_15875 (AllWinning.nil)))))))))))

theorem node_18764 : Outcome ⟨18, 10, 3, 6⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 10⟩) (by decide) node_13749

theorem node_18765 : Outcome ⟨18, 10, 3, 10⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 10⟩) (by decide) node_13749

theorem node_18766 : Outcome ⟨18, 11, 2, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 2, 2⟩) (by decide) node_17813

theorem node_18767 : Outcome ⟨18, 11, 2, 4⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 8⟩) (by decide) node_14891

theorem node_18768 : Outcome ⟨18, 11, 2, 10⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 8⟩) (by decide) node_14891

theorem node_18769 : Outcome ⟨18, 12, 1, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 4⟩) (by decide) node_16860

theorem node_18770 : Outcome ⟨18, 12, 1, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 4⟩) (by decide) node_16860

theorem node_18771 : Outcome ⟨18, 12, 1, 8⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 4⟩) (by decide) node_16860

theorem node_18772 : Outcome ⟨18, 13, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 0, 2⟩, ⟨16, 13, 0, 4⟩, ⟨18, 12, 0, 2⟩, ⟨18, 11, 0, 4⟩]
  exact AllWinning.cons node_17819 (AllWinning.cons node_16863 (AllWinning.cons node_17852 (AllWinning.cons node_16934 (AllWinning.nil))))

theorem node_18773 : Outcome ⟨18, 13, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 0, 2⟩, ⟨16, 13, 0, 4⟩, ⟨15, 13, 0, 6⟩, ⟨14, 13, 0, 8⟩, ⟨18, 12, 0, 2⟩, ⟨18, 11, 0, 4⟩, ⟨18, 10, 0, 6⟩, ⟨18, 9, 0, 8⟩]
  exact AllWinning.cons node_17819 (AllWinning.cons node_16863 (AllWinning.cons node_15784 (AllWinning.cons node_14748 (AllWinning.cons node_17852 (AllWinning.cons node_16934 (AllWinning.cons node_15875 (AllWinning.cons node_14899 (AllWinning.nil))))))))

theorem node_18774 : Outcome ⟨18, 13, 0, 14⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 10⟩) (by decide) node_13765

theorem node_18775 : Outcome ⟨19, 0, 12, 2⟩ true :=
  Outcome.win (q := ⟨17, 0, 12, 4⟩) (by decide) node_16866

theorem node_18776 : Outcome ⟨19, 0, 12, 4⟩ true :=
  Outcome.win (q := ⟨17, 0, 12, 4⟩) (by decide) node_16866

theorem node_18777 : Outcome ⟨19, 0, 12, 14⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 14⟩) (by decide) node_11715

theorem node_18778 : Outcome ⟨19, 1, 11, 2⟩ true :=
  Outcome.win (q := ⟨19, 1, 9, 4⟩) (by decide) node_16941

theorem node_18779 : Outcome ⟨19, 1, 11, 4⟩ true :=
  Outcome.win (q := ⟨19, 1, 9, 4⟩) (by decide) node_16941

theorem node_18780 : Outcome ⟨19, 2, 10, 6⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 6⟩) (by decide) node_15793

theorem node_18781 : Outcome ⟨19, 3, 9, 2⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 4⟩) (by decide) node_16873

theorem node_18782 : Outcome ⟨19, 3, 9, 4⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 4⟩) (by decide) node_16873

theorem node_18783 : Outcome ⟨19, 4, 8, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 4⟩) (by decide) node_16877

theorem node_18784 : Outcome ⟨19, 4, 8, 12⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 4⟩) (by decide) node_16877

theorem node_18785 : Outcome ⟨19, 5, 7, 2⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 4⟩) (by decide) node_16881

theorem node_18786 : Outcome ⟨19, 5, 7, 6⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 4⟩) (by decide) node_16881

theorem node_18787 : Outcome ⟨19, 6, 6, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 6, 4⟩) (by decide) node_16887

theorem node_18788 : Outcome ⟨19, 7, 5, 2⟩ true :=
  Outcome.win (q := ⟨17, 7, 5, 4⟩) (by decide) node_16889

theorem node_18789 : Outcome ⟨19, 7, 5, 6⟩ true :=
  Outcome.win (q := ⟨17, 7, 5, 4⟩) (by decide) node_16889

theorem node_18790 : Outcome ⟨19, 8, 4, 2⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 4⟩) (by decide) node_16895

theorem node_18791 : Outcome ⟨19, 8, 4, 12⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 4⟩) (by decide) node_16895

theorem node_18792 : Outcome ⟨19, 9, 3, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 3, 4⟩) (by decide) node_16900

theorem node_18793 : Outcome ⟨19, 9, 3, 4⟩ true :=
  Outcome.win (q := ⟨17, 9, 3, 4⟩) (by decide) node_16900

theorem node_18794 : Outcome ⟨19, 10, 2, 6⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 6⟩) (by decide) node_15811

theorem node_18795 : Outcome ⟨19, 11, 1, 2⟩ true :=
  Outcome.win (q := ⟨19, 9, 1, 4⟩) (by decide) node_16964

theorem node_18796 : Outcome ⟨19, 11, 1, 4⟩ true :=
  Outcome.win (q := ⟨19, 9, 1, 4⟩) (by decide) node_16964

theorem node_18797 : Outcome ⟨19, 12, 0, 2⟩ true :=
  Outcome.win (q := ⟨17, 12, 0, 4⟩) (by decide) node_16908

theorem node_18798 : Outcome ⟨19, 12, 0, 4⟩ true :=
  Outcome.win (q := ⟨17, 12, 0, 4⟩) (by decide) node_16908

theorem node_18799 : Outcome ⟨19, 12, 0, 14⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 14⟩) (by decide) node_11776

theorem node_18800 : Outcome ⟨0, 12, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 20, 2⟩, ⟨0, 10, 20, 4⟩, ⟨0, 9, 20, 6⟩, ⟨0, 8, 20, 8⟩, ⟨0, 12, 19, 2⟩, ⟨0, 12, 18, 4⟩, ⟨0, 12, 17, 6⟩, ⟨0, 12, 16, 8⟩]
  exact AllWinning.cons node_17879 (AllWinning.cons node_16971 (AllWinning.cons node_15902 (AllWinning.cons node_14919 (AllWinning.cons node_17882 (AllWinning.cons node_16979 (AllWinning.cons node_15914 (AllWinning.cons node_14933 (AllWinning.nil))))))))

theorem node_18801 : Outcome ⟨0, 12, 20, 6⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 10⟩) (by decide) node_13948

theorem node_18802 : Outcome ⟨0, 12, 20, 16⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 16⟩) (by decide) node_11006

theorem node_18803 : Outcome ⟨0, 13, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 19, 4⟩) (by decide) node_16975

theorem node_18804 : Outcome ⟨0, 13, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 19, 4⟩) (by decide) node_16975

theorem node_18805 : Outcome ⟨0, 13, 19, 12⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 12⟩) (by decide) node_13006

theorem node_18806 : Outcome ⟨0, 13, 19, 16⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 12⟩) (by decide) node_13006

theorem node_18807 : Outcome ⟨0, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 18, 2⟩) (by decide) node_17885

theorem node_18808 : Outcome ⟨0, 14, 18, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 8⟩) (by decide) node_14940

theorem node_18809 : Outcome ⟨0, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18810 : Outcome ⟨0, 15, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18811 : Outcome ⟨0, 15, 17, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18812 : Outcome ⟨0, 16, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.nil))))

theorem node_18813 : Outcome ⟨0, 16, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨0, 12, 16, 8⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩, ⟨0, 16, 13, 6⟩, ⟨0, 16, 12, 8⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_15917 (AllWinning.cons node_14933 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.cons node_15925 (AllWinning.cons node_14949 (AllWinning.nil))))))))

theorem node_18814 : Outcome ⟨0, 16, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨0, 12, 16, 8⟩, ⟨0, 11, 16, 10⟩, ⟨0, 10, 16, 12⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩, ⟨0, 16, 13, 6⟩, ⟨0, 16, 12, 8⟩, ⟨0, 16, 11, 10⟩, ⟨0, 16, 10, 12⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_15917 (AllWinning.cons node_14933 (AllWinning.cons node_13962 (AllWinning.cons node_12995 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.cons node_15925 (AllWinning.cons node_14949 (AllWinning.cons node_13979 (AllWinning.cons node_13016 (AllWinning.nil))))))))))))

theorem node_18815 : Outcome ⟨0, 16, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨0, 12, 16, 8⟩, ⟨0, 11, 16, 10⟩, ⟨0, 10, 16, 12⟩, ⟨0, 9, 16, 14⟩, ⟨0, 8, 16, 16⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩, ⟨0, 16, 13, 6⟩, ⟨0, 16, 12, 8⟩, ⟨0, 16, 11, 10⟩, ⟨0, 16, 10, 12⟩, ⟨0, 16, 9, 14⟩, ⟨0, 16, 8, 16⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_15917 (AllWinning.cons node_14933 (AllWinning.cons node_13962 (AllWinning.cons node_12995 (AllWinning.cons node_11976 (AllWinning.cons node_10991 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.cons node_15925 (AllWinning.cons node_14949 (AllWinning.cons node_13979 (AllWinning.cons node_13016 (AllWinning.cons node_11996 (AllWinning.cons node_11018 (AllWinning.nil))))))))))))))))

theorem node_18816 : Outcome ⟨0, 16, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨0, 12, 16, 8⟩, ⟨0, 11, 16, 10⟩, ⟨0, 10, 16, 12⟩, ⟨0, 9, 16, 14⟩, ⟨0, 8, 16, 16⟩, ⟨0, 7, 16, 18⟩, ⟨0, 6, 16, 20⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩, ⟨0, 16, 13, 6⟩, ⟨0, 16, 12, 8⟩, ⟨0, 16, 11, 10⟩, ⟨0, 16, 10, 12⟩, ⟨0, 16, 9, 14⟩, ⟨0, 16, 8, 16⟩, ⟨0, 16, 7, 18⟩, ⟨0, 16, 6, 20⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_15917 (AllWinning.cons node_14933 (AllWinning.cons node_13962 (AllWinning.cons node_12995 (AllWinning.cons node_11976 (AllWinning.cons node_10991 (AllWinning.cons node_9888 (AllWinning.cons node_8921 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.cons node_15925 (AllWinning.cons node_14949 (AllWinning.cons node_13979 (AllWinning.cons node_13016 (AllWinning.cons node_11996 (AllWinning.cons node_11018 (AllWinning.cons node_9916 (AllWinning.cons node_8965 (AllWinning.nil))))))))))))))))))))

theorem node_18817 : Outcome ⟨0, 16, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨0, 12, 16, 8⟩, ⟨0, 11, 16, 10⟩, ⟨0, 10, 16, 12⟩, ⟨0, 9, 16, 14⟩, ⟨0, 8, 16, 16⟩, ⟨0, 7, 16, 18⟩, ⟨0, 6, 16, 20⟩, ⟨0, 5, 16, 22⟩, ⟨0, 4, 16, 24⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩, ⟨0, 16, 13, 6⟩, ⟨0, 16, 12, 8⟩, ⟨0, 16, 11, 10⟩, ⟨0, 16, 10, 12⟩, ⟨0, 16, 9, 14⟩, ⟨0, 16, 8, 16⟩, ⟨0, 16, 7, 18⟩, ⟨0, 16, 6, 20⟩, ⟨0, 16, 5, 22⟩, ⟨0, 16, 4, 24⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_15917 (AllWinning.cons node_14933 (AllWinning.cons node_13962 (AllWinning.cons node_12995 (AllWinning.cons node_11976 (AllWinning.cons node_10991 (AllWinning.cons node_9888 (AllWinning.cons node_8921 (AllWinning.cons node_7924 (AllWinning.cons node_6960 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.cons node_15925 (AllWinning.cons node_14949 (AllWinning.cons node_13979 (AllWinning.cons node_13016 (AllWinning.cons node_11996 (AllWinning.cons node_11018 (AllWinning.cons node_9916 (AllWinning.cons node_8965 (AllWinning.cons node_7963 (AllWinning.cons node_7014 (AllWinning.nil))))))))))))))))))))))))

theorem node_18818 : Outcome ⟨0, 16, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨0, 12, 16, 8⟩, ⟨0, 11, 16, 10⟩, ⟨0, 10, 16, 12⟩, ⟨0, 9, 16, 14⟩, ⟨0, 8, 16, 16⟩, ⟨0, 7, 16, 18⟩, ⟨0, 6, 16, 20⟩, ⟨0, 5, 16, 22⟩, ⟨0, 4, 16, 24⟩, ⟨0, 3, 16, 26⟩, ⟨0, 2, 16, 28⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩, ⟨0, 16, 13, 6⟩, ⟨0, 16, 12, 8⟩, ⟨0, 16, 11, 10⟩, ⟨0, 16, 10, 12⟩, ⟨0, 16, 9, 14⟩, ⟨0, 16, 8, 16⟩, ⟨0, 16, 7, 18⟩, ⟨0, 16, 6, 20⟩, ⟨0, 16, 5, 22⟩, ⟨0, 16, 4, 24⟩, ⟨0, 16, 3, 26⟩, ⟨0, 16, 2, 28⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_15917 (AllWinning.cons node_14933 (AllWinning.cons node_13962 (AllWinning.cons node_12995 (AllWinning.cons node_11976 (AllWinning.cons node_10991 (AllWinning.cons node_9888 (AllWinning.cons node_8921 (AllWinning.cons node_7924 (AllWinning.cons node_6960 (AllWinning.cons node_6049 (AllWinning.cons node_5320 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.cons node_15925 (AllWinning.cons node_14949 (AllWinning.cons node_13979 (AllWinning.cons node_13016 (AllWinning.cons node_11996 (AllWinning.cons node_11018 (AllWinning.cons node_9916 (AllWinning.cons node_8965 (AllWinning.cons node_7963 (AllWinning.cons node_7014 (AllWinning.cons node_6107 (AllWinning.cons node_5381 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_18819 : Outcome ⟨0, 16, 16, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨0, 12, 16, 8⟩, ⟨0, 11, 16, 10⟩, ⟨0, 10, 16, 12⟩, ⟨0, 9, 16, 14⟩, ⟨0, 8, 16, 16⟩, ⟨0, 7, 16, 18⟩, ⟨0, 6, 16, 20⟩, ⟨0, 5, 16, 22⟩, ⟨0, 4, 16, 24⟩, ⟨0, 3, 16, 26⟩, ⟨0, 2, 16, 28⟩, ⟨0, 1, 16, 30⟩, ⟨0, 0, 16, 32⟩, ⟨0, 16, 15, 2⟩, ⟨0, 16, 14, 4⟩, ⟨0, 16, 13, 6⟩, ⟨0, 16, 12, 8⟩, ⟨0, 16, 11, 10⟩, ⟨0, 16, 10, 12⟩, ⟨0, 16, 9, 14⟩, ⟨0, 16, 8, 16⟩, ⟨0, 16, 7, 18⟩, ⟨0, 16, 6, 20⟩, ⟨0, 16, 5, 22⟩, ⟨0, 16, 4, 24⟩, ⟨0, 16, 3, 26⟩, ⟨0, 16, 2, 28⟩, ⟨0, 16, 1, 30⟩, ⟨0, 16, 0, 32⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_16984 (AllWinning.cons node_15917 (AllWinning.cons node_14933 (AllWinning.cons node_13962 (AllWinning.cons node_12995 (AllWinning.cons node_11976 (AllWinning.cons node_10991 (AllWinning.cons node_9888 (AllWinning.cons node_8921 (AllWinning.cons node_7924 (AllWinning.cons node_6960 (AllWinning.cons node_6049 (AllWinning.cons node_5320 (AllWinning.cons node_4574 (AllWinning.cons node_3930 (AllWinning.cons node_17893 (AllWinning.cons node_16994 (AllWinning.cons node_15925 (AllWinning.cons node_14949 (AllWinning.cons node_13979 (AllWinning.cons node_13016 (AllWinning.cons node_11996 (AllWinning.cons node_11018 (AllWinning.cons node_9916 (AllWinning.cons node_8965 (AllWinning.cons node_7963 (AllWinning.cons node_7014 (AllWinning.cons node_6107 (AllWinning.cons node_5381 (AllWinning.cons node_4645 (AllWinning.cons node_4001 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_18820 : Outcome ⟨0, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18821 : Outcome ⟨0, 17, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18822 : Outcome ⟨0, 17, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18823 : Outcome ⟨0, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 13, 2⟩) (by decide) node_17897

theorem node_18824 : Outcome ⟨0, 18, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 8⟩) (by decide) node_14940

theorem node_18825 : Outcome ⟨0, 19, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 11, 4⟩) (by decide) node_17005

theorem node_18826 : Outcome ⟨0, 19, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 19, 11, 4⟩) (by decide) node_17005

theorem node_18827 : Outcome ⟨0, 19, 13, 12⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 12⟩) (by decide) node_13006

theorem node_18828 : Outcome ⟨0, 19, 13, 16⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 12⟩) (by decide) node_13006

theorem node_18829 : Outcome ⟨0, 20, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 12, 2⟩, ⟨0, 18, 12, 4⟩, ⟨0, 17, 12, 6⟩, ⟨0, 16, 12, 8⟩, ⟨0, 20, 11, 2⟩, ⟨0, 20, 10, 4⟩, ⟨0, 20, 9, 6⟩, ⟨0, 20, 8, 8⟩]
  exact AllWinning.cons node_17901 (AllWinning.cons node_17001 (AllWinning.cons node_15928 (AllWinning.cons node_14949 (AllWinning.cons node_17904 (AllWinning.cons node_17009 (AllWinning.cons node_15939 (AllWinning.cons node_14962 (AllWinning.nil))))))))

theorem node_18830 : Outcome ⟨0, 20, 12, 6⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 10⟩) (by decide) node_13994

theorem node_18831 : Outcome ⟨0, 20, 12, 16⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 16⟩) (by decide) node_11006

theorem node_18832 : Outcome ⟨1, 11, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 20, 2⟩) (by decide) node_17907

theorem node_18833 : Outcome ⟨1, 12, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 19, 2⟩, ⟨1, 11, 19, 2⟩, ⟨1, 10, 19, 4⟩, ⟨1, 12, 18, 2⟩, ⟨1, 12, 17, 4⟩]
  exact AllWinning.cons node_17882 (AllWinning.cons node_17910 (AllWinning.cons node_17016 (AllWinning.cons node_17913 (AllWinning.cons node_17022 (AllWinning.nil)))))

theorem node_18834 : Outcome ⟨1, 12, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 19, 2⟩, ⟨1, 11, 19, 2⟩, ⟨1, 10, 19, 4⟩, ⟨1, 9, 19, 6⟩, ⟨1, 8, 19, 8⟩, ⟨1, 12, 18, 2⟩, ⟨1, 12, 17, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 12, 15, 8⟩]
  exact AllWinning.cons node_17882 (AllWinning.cons node_17910 (AllWinning.cons node_17016 (AllWinning.cons node_15945 (AllWinning.cons node_14967 (AllWinning.cons node_17913 (AllWinning.cons node_17022 (AllWinning.cons node_15955 (AllWinning.cons node_14980 (AllWinning.nil)))))))))

theorem node_18835 : Outcome ⟨1, 12, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 19, 2⟩, ⟨1, 11, 19, 2⟩, ⟨1, 10, 19, 4⟩, ⟨1, 9, 19, 6⟩, ⟨1, 8, 19, 8⟩, ⟨1, 7, 19, 10⟩, ⟨1, 6, 19, 12⟩, ⟨1, 12, 18, 2⟩, ⟨1, 12, 17, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 12, 14, 10⟩, ⟨1, 12, 13, 12⟩]
  exact AllWinning.cons node_17882 (AllWinning.cons node_17910 (AllWinning.cons node_17016 (AllWinning.cons node_15945 (AllWinning.cons node_14967 (AllWinning.cons node_13999 (AllWinning.cons node_13033 (AllWinning.cons node_17913 (AllWinning.cons node_17022 (AllWinning.cons node_15955 (AllWinning.cons node_14980 (AllWinning.cons node_14020 (AllWinning.cons node_13053 (AllWinning.nil)))))))))))))

theorem node_18836 : Outcome ⟨1, 12, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 19, 2⟩, ⟨1, 11, 19, 2⟩, ⟨1, 10, 19, 4⟩, ⟨1, 9, 19, 6⟩, ⟨1, 8, 19, 8⟩, ⟨1, 7, 19, 10⟩, ⟨1, 6, 19, 12⟩, ⟨1, 5, 19, 14⟩, ⟨1, 4, 19, 16⟩, ⟨1, 12, 18, 2⟩, ⟨1, 12, 17, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 12, 14, 10⟩, ⟨1, 12, 13, 12⟩, ⟨1, 12, 12, 14⟩, ⟨1, 12, 11, 16⟩]
  exact AllWinning.cons node_17882 (AllWinning.cons node_17910 (AllWinning.cons node_17016 (AllWinning.cons node_15945 (AllWinning.cons node_14967 (AllWinning.cons node_13999 (AllWinning.cons node_13033 (AllWinning.cons node_12016 (AllWinning.cons node_11035 (AllWinning.cons node_17913 (AllWinning.cons node_17022 (AllWinning.cons node_15955 (AllWinning.cons node_14980 (AllWinning.cons node_14020 (AllWinning.cons node_13053 (AllWinning.cons node_12048 (AllWinning.cons node_11064 (AllWinning.nil)))))))))))))))))

theorem node_18837 : Outcome ⟨1, 12, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 19, 2⟩, ⟨1, 11, 19, 2⟩, ⟨1, 10, 19, 4⟩, ⟨1, 9, 19, 6⟩, ⟨1, 8, 19, 8⟩, ⟨1, 7, 19, 10⟩, ⟨1, 6, 19, 12⟩, ⟨1, 5, 19, 14⟩, ⟨1, 4, 19, 16⟩, ⟨1, 3, 19, 18⟩, ⟨1, 2, 19, 20⟩, ⟨1, 12, 18, 2⟩, ⟨1, 12, 17, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 12, 14, 10⟩, ⟨1, 12, 13, 12⟩, ⟨1, 12, 12, 14⟩, ⟨1, 12, 11, 16⟩, ⟨1, 12, 10, 18⟩, ⟨1, 12, 9, 20⟩]
  exact AllWinning.cons node_17882 (AllWinning.cons node_17910 (AllWinning.cons node_17016 (AllWinning.cons node_15945 (AllWinning.cons node_14967 (AllWinning.cons node_13999 (AllWinning.cons node_13033 (AllWinning.cons node_12016 (AllWinning.cons node_11035 (AllWinning.cons node_9940 (AllWinning.cons node_8984 (AllWinning.cons node_17913 (AllWinning.cons node_17022 (AllWinning.cons node_15955 (AllWinning.cons node_14980 (AllWinning.cons node_14020 (AllWinning.cons node_13053 (AllWinning.cons node_12048 (AllWinning.cons node_11064 (AllWinning.cons node_9983 (AllWinning.cons node_9019 (AllWinning.nil)))))))))))))))))))))

theorem node_18838 : Outcome ⟨1, 12, 19, 12⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 22⟩) (by decide) node_8035

theorem node_18839 : Outcome ⟨1, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 18, 2⟩) (by decide) node_17885

theorem node_18840 : Outcome ⟨1, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 18, 2⟩) (by decide) node_17885

theorem node_18841 : Outcome ⟨1, 13, 18, 12⟩ true :=
  Outcome.win (q := ⟨0, 13, 18, 2⟩) (by decide) node_17885

theorem node_18842 : Outcome ⟨1, 14, 17, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 2⟩) (by decide) node_17917

theorem node_18843 : Outcome ⟨1, 14, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 2⟩) (by decide) node_17917

theorem node_18844 : Outcome ⟨1, 15, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨1, 14, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨1, 15, 15, 2⟩, ⟨1, 15, 14, 4⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_17923 (AllWinning.cons node_17024 (AllWinning.cons node_17927 (AllWinning.cons node_17030 (AllWinning.nil)))))

theorem node_18845 : Outcome ⟨1, 15, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨1, 14, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 11, 16, 8⟩, ⟨1, 15, 15, 2⟩, ⟨1, 15, 14, 4⟩, ⟨1, 15, 13, 6⟩, ⟨1, 15, 12, 8⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_17923 (AllWinning.cons node_17024 (AllWinning.cons node_15955 (AllWinning.cons node_14976 (AllWinning.cons node_17927 (AllWinning.cons node_17030 (AllWinning.cons node_15966 (AllWinning.cons node_14992 (AllWinning.nil)))))))))

theorem node_18846 : Outcome ⟨1, 15, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨1, 14, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 11, 16, 8⟩, ⟨1, 10, 16, 10⟩, ⟨1, 9, 16, 12⟩, ⟨1, 15, 15, 2⟩, ⟨1, 15, 14, 4⟩, ⟨1, 15, 13, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 15, 11, 10⟩, ⟨1, 15, 10, 12⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_17923 (AllWinning.cons node_17024 (AllWinning.cons node_15955 (AllWinning.cons node_14976 (AllWinning.cons node_14013 (AllWinning.cons node_13043 (AllWinning.cons node_17927 (AllWinning.cons node_17030 (AllWinning.cons node_15966 (AllWinning.cons node_14992 (AllWinning.cons node_14033 (AllWinning.cons node_13063 (AllWinning.nil)))))))))))))

theorem node_18847 : Outcome ⟨1, 15, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨1, 14, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 11, 16, 8⟩, ⟨1, 10, 16, 10⟩, ⟨1, 9, 16, 12⟩, ⟨1, 8, 16, 14⟩, ⟨1, 7, 16, 16⟩, ⟨1, 15, 15, 2⟩, ⟨1, 15, 14, 4⟩, ⟨1, 15, 13, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 15, 11, 10⟩, ⟨1, 15, 10, 12⟩, ⟨1, 15, 9, 14⟩, ⟨1, 15, 8, 16⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_17923 (AllWinning.cons node_17024 (AllWinning.cons node_15955 (AllWinning.cons node_14976 (AllWinning.cons node_14013 (AllWinning.cons node_13043 (AllWinning.cons node_12027 (AllWinning.cons node_11045 (AllWinning.cons node_17927 (AllWinning.cons node_17030 (AllWinning.cons node_15966 (AllWinning.cons node_14992 (AllWinning.cons node_14033 (AllWinning.cons node_13063 (AllWinning.cons node_12065 (AllWinning.cons node_11074 (AllWinning.nil)))))))))))))))))

theorem node_18848 : Outcome ⟨1, 15, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨1, 14, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 11, 16, 8⟩, ⟨1, 10, 16, 10⟩, ⟨1, 9, 16, 12⟩, ⟨1, 8, 16, 14⟩, ⟨1, 7, 16, 16⟩, ⟨1, 6, 16, 18⟩, ⟨1, 5, 16, 20⟩, ⟨1, 15, 15, 2⟩, ⟨1, 15, 14, 4⟩, ⟨1, 15, 13, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 15, 11, 10⟩, ⟨1, 15, 10, 12⟩, ⟨1, 15, 9, 14⟩, ⟨1, 15, 8, 16⟩, ⟨1, 15, 7, 18⟩, ⟨1, 15, 6, 20⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_17923 (AllWinning.cons node_17024 (AllWinning.cons node_15955 (AllWinning.cons node_14976 (AllWinning.cons node_14013 (AllWinning.cons node_13043 (AllWinning.cons node_12027 (AllWinning.cons node_11045 (AllWinning.cons node_9957 (AllWinning.cons node_8996 (AllWinning.cons node_17927 (AllWinning.cons node_17030 (AllWinning.cons node_15966 (AllWinning.cons node_14992 (AllWinning.cons node_14033 (AllWinning.cons node_13063 (AllWinning.cons node_12065 (AllWinning.cons node_11074 (AllWinning.cons node_9995 (AllWinning.cons node_9028 (AllWinning.nil)))))))))))))))))))))

theorem node_18849 : Outcome ⟨1, 15, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨1, 14, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 11, 16, 8⟩, ⟨1, 10, 16, 10⟩, ⟨1, 9, 16, 12⟩, ⟨1, 8, 16, 14⟩, ⟨1, 7, 16, 16⟩, ⟨1, 6, 16, 18⟩, ⟨1, 5, 16, 20⟩, ⟨1, 4, 16, 22⟩, ⟨1, 3, 16, 24⟩, ⟨1, 15, 15, 2⟩, ⟨1, 15, 14, 4⟩, ⟨1, 15, 13, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 15, 11, 10⟩, ⟨1, 15, 10, 12⟩, ⟨1, 15, 9, 14⟩, ⟨1, 15, 8, 16⟩, ⟨1, 15, 7, 18⟩, ⟨1, 15, 6, 20⟩, ⟨1, 15, 5, 22⟩, ⟨1, 15, 4, 24⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_17923 (AllWinning.cons node_17024 (AllWinning.cons node_15955 (AllWinning.cons node_14976 (AllWinning.cons node_14013 (AllWinning.cons node_13043 (AllWinning.cons node_12027 (AllWinning.cons node_11045 (AllWinning.cons node_9957 (AllWinning.cons node_8996 (AllWinning.cons node_7992 (AllWinning.cons node_7044 (AllWinning.cons node_17927 (AllWinning.cons node_17030 (AllWinning.cons node_15966 (AllWinning.cons node_14992 (AllWinning.cons node_14033 (AllWinning.cons node_13063 (AllWinning.cons node_12065 (AllWinning.cons node_11074 (AllWinning.cons node_9995 (AllWinning.cons node_9028 (AllWinning.cons node_8048 (AllWinning.cons node_7093 (AllWinning.nil)))))))))))))))))))))))))

theorem node_18850 : Outcome ⟨1, 15, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 16, 2⟩, ⟨1, 14, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨1, 12, 16, 6⟩, ⟨1, 11, 16, 8⟩, ⟨1, 10, 16, 10⟩, ⟨1, 9, 16, 12⟩, ⟨1, 8, 16, 14⟩, ⟨1, 7, 16, 16⟩, ⟨1, 6, 16, 18⟩, ⟨1, 5, 16, 20⟩, ⟨1, 4, 16, 22⟩, ⟨1, 3, 16, 24⟩, ⟨1, 2, 16, 26⟩, ⟨1, 1, 16, 28⟩, ⟨1, 15, 15, 2⟩, ⟨1, 15, 14, 4⟩, ⟨1, 15, 13, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 15, 11, 10⟩, ⟨1, 15, 10, 12⟩, ⟨1, 15, 9, 14⟩, ⟨1, 15, 8, 16⟩, ⟨1, 15, 7, 18⟩, ⟨1, 15, 6, 20⟩, ⟨1, 15, 5, 22⟩, ⟨1, 15, 4, 24⟩, ⟨1, 15, 3, 26⟩, ⟨1, 15, 2, 28⟩]
  exact AllWinning.cons node_17891 (AllWinning.cons node_17923 (AllWinning.cons node_17024 (AllWinning.cons node_15955 (AllWinning.cons node_14976 (AllWinning.cons node_14013 (AllWinning.cons node_13043 (AllWinning.cons node_12027 (AllWinning.cons node_11045 (AllWinning.cons node_9957 (AllWinning.cons node_8996 (AllWinning.cons node_7992 (AllWinning.cons node_7044 (AllWinning.cons node_6122 (AllWinning.cons node_5395 (AllWinning.cons node_17927 (AllWinning.cons node_17030 (AllWinning.cons node_15966 (AllWinning.cons node_14992 (AllWinning.cons node_14033 (AllWinning.cons node_13063 (AllWinning.cons node_12065 (AllWinning.cons node_11074 (AllWinning.cons node_9995 (AllWinning.cons node_9028 (AllWinning.cons node_8048 (AllWinning.cons node_7093 (AllWinning.cons node_6187 (AllWinning.cons node_5448 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_18851 : Outcome ⟨1, 16, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 15, 2⟩, ⟨1, 15, 15, 2⟩, ⟨1, 14, 15, 4⟩, ⟨1, 16, 14, 2⟩, ⟨1, 16, 13, 4⟩]
  exact AllWinning.cons node_17893 (AllWinning.cons node_17927 (AllWinning.cons node_17026 (AllWinning.cons node_17930 (AllWinning.cons node_17034 (AllWinning.nil)))))

theorem node_18852 : Outcome ⟨1, 16, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 15, 2⟩, ⟨1, 15, 15, 2⟩, ⟨1, 14, 15, 4⟩, ⟨1, 13, 15, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 16, 14, 2⟩, ⟨1, 16, 13, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 16, 11, 8⟩]
  exact AllWinning.cons node_17893 (AllWinning.cons node_17927 (AllWinning.cons node_17026 (AllWinning.cons node_15959 (AllWinning.cons node_14980 (AllWinning.cons node_17930 (AllWinning.cons node_17034 (AllWinning.cons node_15969 (AllWinning.cons node_14995 (AllWinning.nil)))))))))

theorem node_18853 : Outcome ⟨1, 16, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 15, 2⟩, ⟨1, 15, 15, 2⟩, ⟨1, 14, 15, 4⟩, ⟨1, 13, 15, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨1, 10, 15, 12⟩, ⟨1, 16, 14, 2⟩, ⟨1, 16, 13, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 16, 11, 8⟩, ⟨1, 16, 10, 10⟩, ⟨1, 16, 9, 12⟩]
  exact AllWinning.cons node_17893 (AllWinning.cons node_17927 (AllWinning.cons node_17026 (AllWinning.cons node_15959 (AllWinning.cons node_14980 (AllWinning.cons node_14017 (AllWinning.cons node_13046 (AllWinning.cons node_17930 (AllWinning.cons node_17034 (AllWinning.cons node_15969 (AllWinning.cons node_14995 (AllWinning.cons node_14037 (AllWinning.cons node_13066 (AllWinning.nil)))))))))))))

theorem node_18854 : Outcome ⟨1, 16, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 15, 2⟩, ⟨1, 15, 15, 2⟩, ⟨1, 14, 15, 4⟩, ⟨1, 13, 15, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨1, 10, 15, 12⟩, ⟨1, 9, 15, 14⟩, ⟨1, 8, 15, 16⟩, ⟨1, 16, 14, 2⟩, ⟨1, 16, 13, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 16, 11, 8⟩, ⟨1, 16, 10, 10⟩, ⟨1, 16, 9, 12⟩, ⟨1, 16, 8, 14⟩, ⟨1, 16, 7, 16⟩]
  exact AllWinning.cons node_17893 (AllWinning.cons node_17927 (AllWinning.cons node_17026 (AllWinning.cons node_15959 (AllWinning.cons node_14980 (AllWinning.cons node_14017 (AllWinning.cons node_13046 (AllWinning.cons node_12031 (AllWinning.cons node_11050 (AllWinning.cons node_17930 (AllWinning.cons node_17034 (AllWinning.cons node_15969 (AllWinning.cons node_14995 (AllWinning.cons node_14037 (AllWinning.cons node_13066 (AllWinning.cons node_12069 (AllWinning.cons node_11077 (AllWinning.nil)))))))))))))))))

theorem node_18855 : Outcome ⟨1, 16, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 15, 2⟩, ⟨1, 15, 15, 2⟩, ⟨1, 14, 15, 4⟩, ⟨1, 13, 15, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨1, 10, 15, 12⟩, ⟨1, 9, 15, 14⟩, ⟨1, 8, 15, 16⟩, ⟨1, 7, 15, 18⟩, ⟨1, 6, 15, 20⟩, ⟨1, 16, 14, 2⟩, ⟨1, 16, 13, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 16, 11, 8⟩, ⟨1, 16, 10, 10⟩, ⟨1, 16, 9, 12⟩, ⟨1, 16, 8, 14⟩, ⟨1, 16, 7, 16⟩, ⟨1, 16, 6, 18⟩, ⟨1, 16, 5, 20⟩]
  exact AllWinning.cons node_17893 (AllWinning.cons node_17927 (AllWinning.cons node_17026 (AllWinning.cons node_15959 (AllWinning.cons node_14980 (AllWinning.cons node_14017 (AllWinning.cons node_13046 (AllWinning.cons node_12031 (AllWinning.cons node_11050 (AllWinning.cons node_9962 (AllWinning.cons node_9001 (AllWinning.cons node_17930 (AllWinning.cons node_17034 (AllWinning.cons node_15969 (AllWinning.cons node_14995 (AllWinning.cons node_14037 (AllWinning.cons node_13066 (AllWinning.cons node_12069 (AllWinning.cons node_11077 (AllWinning.cons node_10003 (AllWinning.cons node_9031 (AllWinning.nil)))))))))))))))))))))

theorem node_18856 : Outcome ⟨1, 16, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 15, 2⟩, ⟨1, 15, 15, 2⟩, ⟨1, 14, 15, 4⟩, ⟨1, 13, 15, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨1, 10, 15, 12⟩, ⟨1, 9, 15, 14⟩, ⟨1, 8, 15, 16⟩, ⟨1, 7, 15, 18⟩, ⟨1, 6, 15, 20⟩, ⟨1, 5, 15, 22⟩, ⟨1, 4, 15, 24⟩, ⟨1, 16, 14, 2⟩, ⟨1, 16, 13, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 16, 11, 8⟩, ⟨1, 16, 10, 10⟩, ⟨1, 16, 9, 12⟩, ⟨1, 16, 8, 14⟩, ⟨1, 16, 7, 16⟩, ⟨1, 16, 6, 18⟩, ⟨1, 16, 5, 20⟩, ⟨1, 16, 4, 22⟩, ⟨1, 16, 3, 24⟩]
  exact AllWinning.cons node_17893 (AllWinning.cons node_17927 (AllWinning.cons node_17026 (AllWinning.cons node_15959 (AllWinning.cons node_14980 (AllWinning.cons node_14017 (AllWinning.cons node_13046 (AllWinning.cons node_12031 (AllWinning.cons node_11050 (AllWinning.cons node_9962 (AllWinning.cons node_9001 (AllWinning.cons node_7997 (AllWinning.cons node_7051 (AllWinning.cons node_17930 (AllWinning.cons node_17034 (AllWinning.cons node_15969 (AllWinning.cons node_14995 (AllWinning.cons node_14037 (AllWinning.cons node_13066 (AllWinning.cons node_12069 (AllWinning.cons node_11077 (AllWinning.cons node_10003 (AllWinning.cons node_9031 (AllWinning.cons node_8052 (AllWinning.cons node_7098 (AllWinning.nil)))))))))))))))))))))))))

theorem node_18857 : Outcome ⟨1, 16, 15, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 15, 2⟩, ⟨1, 15, 15, 2⟩, ⟨1, 14, 15, 4⟩, ⟨1, 13, 15, 6⟩, ⟨1, 12, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨1, 10, 15, 12⟩, ⟨1, 9, 15, 14⟩, ⟨1, 8, 15, 16⟩, ⟨1, 7, 15, 18⟩, ⟨1, 6, 15, 20⟩, ⟨1, 5, 15, 22⟩, ⟨1, 4, 15, 24⟩, ⟨1, 3, 15, 26⟩, ⟨1, 2, 15, 28⟩, ⟨1, 16, 14, 2⟩, ⟨1, 16, 13, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 16, 11, 8⟩, ⟨1, 16, 10, 10⟩, ⟨1, 16, 9, 12⟩, ⟨1, 16, 8, 14⟩, ⟨1, 16, 7, 16⟩, ⟨1, 16, 6, 18⟩, ⟨1, 16, 5, 20⟩, ⟨1, 16, 4, 22⟩, ⟨1, 16, 3, 24⟩, ⟨1, 16, 2, 26⟩, ⟨1, 16, 1, 28⟩]
  exact AllWinning.cons node_17893 (AllWinning.cons node_17927 (AllWinning.cons node_17026 (AllWinning.cons node_15959 (AllWinning.cons node_14980 (AllWinning.cons node_14017 (AllWinning.cons node_13046 (AllWinning.cons node_12031 (AllWinning.cons node_11050 (AllWinning.cons node_9962 (AllWinning.cons node_9001 (AllWinning.cons node_7997 (AllWinning.cons node_7051 (AllWinning.cons node_6126 (AllWinning.cons node_5399 (AllWinning.cons node_17930 (AllWinning.cons node_17034 (AllWinning.cons node_15969 (AllWinning.cons node_14995 (AllWinning.cons node_14037 (AllWinning.cons node_13066 (AllWinning.cons node_12069 (AllWinning.cons node_11077 (AllWinning.cons node_10003 (AllWinning.cons node_9031 (AllWinning.cons node_8052 (AllWinning.cons node_7098 (AllWinning.cons node_6191 (AllWinning.cons node_5452 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_18858 : Outcome ⟨1, 17, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 2⟩) (by decide) node_17934

end RQ9F1
