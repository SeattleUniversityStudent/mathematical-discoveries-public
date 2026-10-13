import Chunk45
set_option autoImplicit false
namespace RQ9F1

theorem node_10821 : Outcome ⟨14, 6, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 6, 3, 2⟩, ⟨12, 6, 3, 4⟩, ⟨11, 6, 3, 6⟩, ⟨10, 6, 3, 8⟩, ⟨9, 6, 3, 10⟩, ⟨8, 6, 3, 12⟩, ⟨7, 6, 3, 14⟩, ⟨6, 6, 3, 16⟩, ⟨14, 5, 3, 2⟩, ⟨14, 4, 3, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 2, 3, 8⟩, ⟨14, 1, 3, 10⟩, ⟨14, 0, 3, 12⟩, ⟨14, 6, 2, 2⟩, ⟨14, 6, 1, 4⟩, ⟨14, 6, 0, 6⟩]
  exact AllWinning.cons node_9725 (AllWinning.cons node_8742 (AllWinning.cons node_7720 (AllWinning.cons node_6723 (AllWinning.cons node_5859 (AllWinning.cons node_5102 (AllWinning.cons node_4377 (AllWinning.cons node_3711 (AllWinning.cons node_9754 (AllWinning.cons node_8809 (AllWinning.cons node_7806 (AllWinning.cons node_6876 (AllWinning.cons node_5983 (AllWinning.cons node_5266 (AllWinning.cons node_9758 (AllWinning.cons node_8815 (AllWinning.cons node_7822 (AllWinning.nil)))))))))))))))))

theorem node_10822 : Outcome ⟨14, 6, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 6, 3, 2⟩, ⟨12, 6, 3, 4⟩, ⟨11, 6, 3, 6⟩, ⟨10, 6, 3, 8⟩, ⟨9, 6, 3, 10⟩, ⟨8, 6, 3, 12⟩, ⟨7, 6, 3, 14⟩, ⟨6, 6, 3, 16⟩, ⟨5, 6, 3, 18⟩, ⟨4, 6, 3, 20⟩, ⟨14, 5, 3, 2⟩, ⟨14, 4, 3, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 2, 3, 8⟩, ⟨14, 1, 3, 10⟩, ⟨14, 0, 3, 12⟩, ⟨14, 6, 2, 2⟩, ⟨14, 6, 1, 4⟩, ⟨14, 6, 0, 6⟩]
  exact AllWinning.cons node_9725 (AllWinning.cons node_8742 (AllWinning.cons node_7720 (AllWinning.cons node_6723 (AllWinning.cons node_5859 (AllWinning.cons node_5102 (AllWinning.cons node_4377 (AllWinning.cons node_3711 (AllWinning.cons node_3111 (AllWinning.cons node_2610 (AllWinning.cons node_9754 (AllWinning.cons node_8809 (AllWinning.cons node_7806 (AllWinning.cons node_6876 (AllWinning.cons node_5983 (AllWinning.cons node_5266 (AllWinning.cons node_9758 (AllWinning.cons node_8815 (AllWinning.cons node_7822 (AllWinning.nil)))))))))))))))))))

theorem node_10823 : Outcome ⟨14, 6, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 6, 3, 2⟩, ⟨12, 6, 3, 4⟩, ⟨11, 6, 3, 6⟩, ⟨10, 6, 3, 8⟩, ⟨9, 6, 3, 10⟩, ⟨8, 6, 3, 12⟩, ⟨7, 6, 3, 14⟩, ⟨6, 6, 3, 16⟩, ⟨5, 6, 3, 18⟩, ⟨4, 6, 3, 20⟩, ⟨3, 6, 3, 22⟩, ⟨2, 6, 3, 24⟩, ⟨14, 5, 3, 2⟩, ⟨14, 4, 3, 4⟩, ⟨14, 3, 3, 6⟩, ⟨14, 2, 3, 8⟩, ⟨14, 1, 3, 10⟩, ⟨14, 0, 3, 12⟩, ⟨14, 6, 2, 2⟩, ⟨14, 6, 1, 4⟩, ⟨14, 6, 0, 6⟩]
  exact AllWinning.cons node_9725 (AllWinning.cons node_8742 (AllWinning.cons node_7720 (AllWinning.cons node_6723 (AllWinning.cons node_5859 (AllWinning.cons node_5102 (AllWinning.cons node_4377 (AllWinning.cons node_3711 (AllWinning.cons node_3111 (AllWinning.cons node_2610 (AllWinning.cons node_2095 (AllWinning.cons node_1663 (AllWinning.cons node_9754 (AllWinning.cons node_8809 (AllWinning.cons node_7806 (AllWinning.cons node_6876 (AllWinning.cons node_5983 (AllWinning.cons node_5266 (AllWinning.cons node_9758 (AllWinning.cons node_8815 (AllWinning.cons node_7822 (AllWinning.nil)))))))))))))))))))))

theorem node_10824 : Outcome ⟨14, 6, 3, 20⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 26⟩) (by decide) node_1259

theorem node_10825 : Outcome ⟨14, 6, 3, 22⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 26⟩) (by decide) node_1259

theorem node_10826 : Outcome ⟨14, 7, 2, 2⟩ true :=
  Outcome.win (q := ⟨12, 7, 2, 4⟩) (by decide) node_8746

theorem node_10827 : Outcome ⟨14, 7, 2, 4⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10828 : Outcome ⟨14, 7, 2, 8⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10829 : Outcome ⟨14, 7, 2, 10⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10830 : Outcome ⟨14, 8, 1, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10831 : Outcome ⟨14, 8, 1, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 4⟩) (by decide) node_8752

theorem node_10832 : Outcome ⟨14, 9, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 0, 2⟩, ⟨12, 9, 0, 4⟩, ⟨14, 8, 0, 2⟩, ⟨14, 7, 0, 4⟩]
  exact AllWinning.cons node_9734 (AllWinning.cons node_8763 (AllWinning.cons node_9764 (AllWinning.cons node_8819 (AllWinning.nil))))

theorem node_10833 : Outcome ⟨14, 9, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 9, 0, 2⟩, ⟨12, 9, 0, 4⟩, ⟨11, 9, 0, 6⟩, ⟨10, 9, 0, 8⟩, ⟨14, 8, 0, 2⟩, ⟨14, 7, 0, 4⟩, ⟨14, 6, 0, 6⟩, ⟨14, 5, 0, 8⟩]
  exact AllWinning.cons node_9734 (AllWinning.cons node_8763 (AllWinning.cons node_7733 (AllWinning.cons node_6736 (AllWinning.cons node_9764 (AllWinning.cons node_8819 (AllWinning.cons node_7822 (AllWinning.cons node_6887 (AllWinning.nil))))))))

theorem node_10834 : Outcome ⟨14, 9, 0, 6⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 10⟩) (by decide) node_5874

theorem node_10835 : Outcome ⟨14, 9, 0, 10⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 10⟩) (by decide) node_5874

theorem node_10836 : Outcome ⟨15, 0, 8, 2⟩ true :=
  Outcome.win (q := ⟨13, 0, 8, 4⟩) (by decide) node_8765

theorem node_10837 : Outcome ⟨15, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨13, 0, 8, 4⟩) (by decide) node_8765

theorem node_10838 : Outcome ⟨15, 0, 8, 10⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 14⟩) (by decide) node_4396

theorem node_10839 : Outcome ⟨15, 0, 8, 14⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 14⟩) (by decide) node_4396

theorem node_10840 : Outcome ⟨15, 1, 7, 4⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 8⟩) (by decide) node_6744

theorem node_10841 : Outcome ⟨15, 1, 7, 8⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 8⟩) (by decide) node_6744

theorem node_10842 : Outcome ⟨15, 1, 7, 18⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 8⟩) (by decide) node_6744

theorem node_10843 : Outcome ⟨15, 1, 7, 22⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 8⟩) (by decide) node_6744

theorem node_10844 : Outcome ⟨15, 2, 6, 4⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 8⟩) (by decide) node_6754

theorem node_10845 : Outcome ⟨15, 2, 6, 6⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 12⟩) (by decide) node_5296

theorem node_10846 : Outcome ⟨15, 2, 6, 18⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 12⟩) (by decide) node_5296

theorem node_10847 : Outcome ⟨15, 3, 5, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 5, 2⟩) (by decide) node_9776

theorem node_10848 : Outcome ⟨15, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 8⟩) (by decide) node_6763

theorem node_10849 : Outcome ⟨15, 3, 5, 10⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 8⟩) (by decide) node_6763

theorem node_10850 : Outcome ⟨15, 3, 5, 26⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 8⟩) (by decide) node_6763

theorem node_10851 : Outcome ⟨15, 4, 4, 2⟩ true :=
  Outcome.win (q := ⟨13, 4, 4, 4⟩) (by decide) node_8778

theorem node_10852 : Outcome ⟨15, 4, 4, 4⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 6⟩) (by decide) node_7832

theorem node_10853 : Outcome ⟨15, 4, 4, 6⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 6⟩) (by decide) node_7832

theorem node_10854 : Outcome ⟨15, 5, 3, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 2, 2⟩) (by decide) node_9786

theorem node_10855 : Outcome ⟨15, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 8⟩) (by decide) node_6777

theorem node_10856 : Outcome ⟨15, 5, 3, 10⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 8⟩) (by decide) node_6777

theorem node_10857 : Outcome ⟨15, 5, 3, 26⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 8⟩) (by decide) node_6777

theorem node_10858 : Outcome ⟨15, 6, 2, 4⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 8⟩) (by decide) node_6788

theorem node_10859 : Outcome ⟨15, 6, 2, 6⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 12⟩) (by decide) node_5286

theorem node_10860 : Outcome ⟨15, 6, 2, 18⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 12⟩) (by decide) node_5286

theorem node_10861 : Outcome ⟨15, 7, 1, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 8⟩) (by decide) node_6797

theorem node_10862 : Outcome ⟨15, 7, 1, 8⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 8⟩) (by decide) node_6797

theorem node_10863 : Outcome ⟨15, 7, 1, 18⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 8⟩) (by decide) node_6797

theorem node_10864 : Outcome ⟨15, 7, 1, 22⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 8⟩) (by decide) node_6797

theorem node_10865 : Outcome ⟨15, 8, 0, 2⟩ true :=
  Outcome.win (q := ⟨13, 8, 0, 4⟩) (by decide) node_8793

theorem node_10866 : Outcome ⟨15, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨13, 8, 0, 4⟩) (by decide) node_8793

theorem node_10867 : Outcome ⟨15, 8, 0, 10⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 14⟩) (by decide) node_4437

theorem node_10868 : Outcome ⟨15, 8, 0, 14⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 14⟩) (by decide) node_4437

theorem node_10869 : Outcome ⟨16, 0, 7, 2⟩ true :=
  Outcome.win (q := ⟨15, 0, 7, 2⟩) (by decide) node_9767

theorem node_10870 : Outcome ⟨16, 0, 7, 4⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 8⟩) (by decide) node_6911

theorem node_10871 : Outcome ⟨16, 0, 7, 8⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 8⟩) (by decide) node_6911

theorem node_10872 : Outcome ⟨16, 0, 7, 18⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 18⟩) (by decide) node_3169

theorem node_10873 : Outcome ⟨16, 0, 7, 22⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 18⟩) (by decide) node_3169

theorem node_10874 : Outcome ⟨16, 1, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨16, 0, 6, 2⟩, ⟨16, 1, 5, 2⟩, ⟨16, 1, 4, 4⟩]
  exact AllWinning.cons node_9772 (AllWinning.cons node_8800 (AllWinning.cons node_9799 (AllWinning.cons node_9804 (AllWinning.cons node_8852 (AllWinning.nil)))))

theorem node_10875 : Outcome ⟨16, 1, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨13, 1, 6, 6⟩, ⟨12, 1, 6, 8⟩, ⟨16, 0, 6, 2⟩, ⟨16, 1, 5, 2⟩, ⟨16, 1, 4, 4⟩, ⟨16, 1, 3, 6⟩, ⟨16, 1, 2, 8⟩]
  exact AllWinning.cons node_9772 (AllWinning.cons node_8800 (AllWinning.cons node_7764 (AllWinning.cons node_6814 (AllWinning.cons node_9799 (AllWinning.cons node_9804 (AllWinning.cons node_8852 (AllWinning.cons node_7861 (AllWinning.cons node_6917 (AllWinning.nil)))))))))

theorem node_10876 : Outcome ⟨16, 1, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨13, 1, 6, 6⟩, ⟨12, 1, 6, 8⟩, ⟨11, 1, 6, 10⟩, ⟨10, 1, 6, 12⟩, ⟨16, 0, 6, 2⟩, ⟨16, 1, 5, 2⟩, ⟨16, 1, 4, 4⟩, ⟨16, 1, 3, 6⟩, ⟨16, 1, 2, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 1, 0, 12⟩]
  exact AllWinning.cons node_9772 (AllWinning.cons node_8800 (AllWinning.cons node_7764 (AllWinning.cons node_6814 (AllWinning.cons node_5916 (AllWinning.cons node_5150 (AllWinning.cons node_9799 (AllWinning.cons node_9804 (AllWinning.cons node_8852 (AllWinning.cons node_7861 (AllWinning.cons node_6917 (AllWinning.cons node_6019 (AllWinning.cons node_5306 (AllWinning.nil)))))))))))))

theorem node_10877 : Outcome ⟨16, 1, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨13, 1, 6, 6⟩, ⟨12, 1, 6, 8⟩, ⟨11, 1, 6, 10⟩, ⟨10, 1, 6, 12⟩, ⟨9, 1, 6, 14⟩, ⟨8, 1, 6, 16⟩, ⟨16, 0, 6, 2⟩, ⟨16, 1, 5, 2⟩, ⟨16, 1, 4, 4⟩, ⟨16, 1, 3, 6⟩, ⟨16, 1, 2, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 1, 0, 12⟩]
  exact AllWinning.cons node_9772 (AllWinning.cons node_8800 (AllWinning.cons node_7764 (AllWinning.cons node_6814 (AllWinning.cons node_5916 (AllWinning.cons node_5150 (AllWinning.cons node_4449 (AllWinning.cons node_3766 (AllWinning.cons node_9799 (AllWinning.cons node_9804 (AllWinning.cons node_8852 (AllWinning.cons node_7861 (AllWinning.cons node_6917 (AllWinning.cons node_6019 (AllWinning.cons node_5306 (AllWinning.nil)))))))))))))))

theorem node_10878 : Outcome ⟨16, 1, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨13, 1, 6, 6⟩, ⟨12, 1, 6, 8⟩, ⟨11, 1, 6, 10⟩, ⟨10, 1, 6, 12⟩, ⟨9, 1, 6, 14⟩, ⟨8, 1, 6, 16⟩, ⟨7, 1, 6, 18⟩, ⟨6, 1, 6, 20⟩, ⟨16, 0, 6, 2⟩, ⟨16, 1, 5, 2⟩, ⟨16, 1, 4, 4⟩, ⟨16, 1, 3, 6⟩, ⟨16, 1, 2, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 1, 0, 12⟩]
  exact AllWinning.cons node_9772 (AllWinning.cons node_8800 (AllWinning.cons node_7764 (AllWinning.cons node_6814 (AllWinning.cons node_5916 (AllWinning.cons node_5150 (AllWinning.cons node_4449 (AllWinning.cons node_3766 (AllWinning.cons node_3177 (AllWinning.cons node_2671 (AllWinning.cons node_9799 (AllWinning.cons node_9804 (AllWinning.cons node_8852 (AllWinning.cons node_7861 (AllWinning.cons node_6917 (AllWinning.cons node_6019 (AllWinning.cons node_5306 (AllWinning.nil)))))))))))))))))

theorem node_10879 : Outcome ⟨16, 1, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 6, 2⟩, ⟨14, 1, 6, 4⟩, ⟨13, 1, 6, 6⟩, ⟨12, 1, 6, 8⟩, ⟨11, 1, 6, 10⟩, ⟨10, 1, 6, 12⟩, ⟨9, 1, 6, 14⟩, ⟨8, 1, 6, 16⟩, ⟨7, 1, 6, 18⟩, ⟨6, 1, 6, 20⟩, ⟨5, 1, 6, 22⟩, ⟨4, 1, 6, 24⟩, ⟨16, 0, 6, 2⟩, ⟨16, 1, 5, 2⟩, ⟨16, 1, 4, 4⟩, ⟨16, 1, 3, 6⟩, ⟨16, 1, 2, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 1, 0, 12⟩]
  exact AllWinning.cons node_9772 (AllWinning.cons node_8800 (AllWinning.cons node_7764 (AllWinning.cons node_6814 (AllWinning.cons node_5916 (AllWinning.cons node_5150 (AllWinning.cons node_4449 (AllWinning.cons node_3766 (AllWinning.cons node_3177 (AllWinning.cons node_2671 (AllWinning.cons node_2167 (AllWinning.cons node_1723 (AllWinning.cons node_9799 (AllWinning.cons node_9804 (AllWinning.cons node_8852 (AllWinning.cons node_7861 (AllWinning.cons node_6917 (AllWinning.cons node_6019 (AllWinning.cons node_5306 (AllWinning.nil)))))))))))))))))))

theorem node_10880 : Outcome ⟨16, 1, 6, 18⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 26⟩) (by decide) node_1331

theorem node_10881 : Outcome ⟨16, 1, 6, 22⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 26⟩) (by decide) node_1331

theorem node_10882 : Outcome ⟨16, 2, 5, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 5, 2⟩) (by decide) node_9776

theorem node_10883 : Outcome ⟨16, 2, 5, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 5, 2⟩) (by decide) node_9776

theorem node_10884 : Outcome ⟨16, 2, 5, 10⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10885 : Outcome ⟨16, 2, 5, 26⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 12⟩) (by decide) node_5157

theorem node_10886 : Outcome ⟨16, 3, 4, 2⟩ true :=
  Outcome.win (q := ⟨16, 3, 3, 2⟩) (by decide) node_9812

theorem node_10887 : Outcome ⟨16, 3, 4, 8⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 8⟩) (by decide) node_6927

theorem node_10888 : Outcome ⟨16, 3, 4, 12⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 8⟩) (by decide) node_6927

theorem node_10889 : Outcome ⟨16, 4, 3, 2⟩ true :=
  Outcome.win (q := ⟨16, 3, 3, 2⟩) (by decide) node_9812

theorem node_10890 : Outcome ⟨16, 4, 3, 8⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 8⟩) (by decide) node_6911

theorem node_10891 : Outcome ⟨16, 4, 3, 12⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 8⟩) (by decide) node_6911

theorem node_10892 : Outcome ⟨16, 5, 2, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 2, 2⟩) (by decide) node_9786

theorem node_10893 : Outcome ⟨16, 5, 2, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 2, 2⟩) (by decide) node_9786

theorem node_10894 : Outcome ⟨16, 5, 2, 10⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10895 : Outcome ⟨16, 5, 2, 26⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 12⟩) (by decide) node_5176

theorem node_10896 : Outcome ⟨16, 6, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 1, 2⟩, ⟨14, 6, 1, 4⟩, ⟨16, 5, 1, 2⟩, ⟨16, 4, 1, 4⟩, ⟨16, 6, 0, 2⟩]
  exact AllWinning.cons node_9790 (AllWinning.cons node_8815 (AllWinning.cons node_9819 (AllWinning.cons node_8865 (AllWinning.cons node_9822 (AllWinning.nil)))))

theorem node_10897 : Outcome ⟨16, 6, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 1, 2⟩, ⟨14, 6, 1, 4⟩, ⟨13, 6, 1, 6⟩, ⟨12, 6, 1, 8⟩, ⟨16, 5, 1, 2⟩, ⟨16, 4, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨16, 2, 1, 8⟩, ⟨16, 6, 0, 2⟩]
  exact AllWinning.cons node_9790 (AllWinning.cons node_8815 (AllWinning.cons node_7781 (AllWinning.cons node_6834 (AllWinning.cons node_9819 (AllWinning.cons node_8865 (AllWinning.cons node_7870 (AllWinning.cons node_6921 (AllWinning.cons node_9822 (AllWinning.nil)))))))))

theorem node_10898 : Outcome ⟨16, 6, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 1, 2⟩, ⟨14, 6, 1, 4⟩, ⟨13, 6, 1, 6⟩, ⟨12, 6, 1, 8⟩, ⟨11, 6, 1, 10⟩, ⟨10, 6, 1, 12⟩, ⟨16, 5, 1, 2⟩, ⟨16, 4, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨16, 2, 1, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 0, 1, 12⟩, ⟨16, 6, 0, 2⟩]
  exact AllWinning.cons node_9790 (AllWinning.cons node_8815 (AllWinning.cons node_7781 (AllWinning.cons node_6834 (AllWinning.cons node_5925 (AllWinning.cons node_5185 (AllWinning.cons node_9819 (AllWinning.cons node_8865 (AllWinning.cons node_7870 (AllWinning.cons node_6921 (AllWinning.cons node_6019 (AllWinning.cons node_5301 (AllWinning.cons node_9822 (AllWinning.nil)))))))))))))

theorem node_10899 : Outcome ⟨16, 6, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 1, 2⟩, ⟨14, 6, 1, 4⟩, ⟨13, 6, 1, 6⟩, ⟨12, 6, 1, 8⟩, ⟨11, 6, 1, 10⟩, ⟨10, 6, 1, 12⟩, ⟨9, 6, 1, 14⟩, ⟨8, 6, 1, 16⟩, ⟨16, 5, 1, 2⟩, ⟨16, 4, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨16, 2, 1, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 0, 1, 12⟩, ⟨16, 6, 0, 2⟩]
  exact AllWinning.cons node_9790 (AllWinning.cons node_8815 (AllWinning.cons node_7781 (AllWinning.cons node_6834 (AllWinning.cons node_5925 (AllWinning.cons node_5185 (AllWinning.cons node_4465 (AllWinning.cons node_3786 (AllWinning.cons node_9819 (AllWinning.cons node_8865 (AllWinning.cons node_7870 (AllWinning.cons node_6921 (AllWinning.cons node_6019 (AllWinning.cons node_5301 (AllWinning.cons node_9822 (AllWinning.nil)))))))))))))))

theorem node_10900 : Outcome ⟨16, 6, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 1, 2⟩, ⟨14, 6, 1, 4⟩, ⟨13, 6, 1, 6⟩, ⟨12, 6, 1, 8⟩, ⟨11, 6, 1, 10⟩, ⟨10, 6, 1, 12⟩, ⟨9, 6, 1, 14⟩, ⟨8, 6, 1, 16⟩, ⟨7, 6, 1, 18⟩, ⟨6, 6, 1, 20⟩, ⟨16, 5, 1, 2⟩, ⟨16, 4, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨16, 2, 1, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 0, 1, 12⟩, ⟨16, 6, 0, 2⟩]
  exact AllWinning.cons node_9790 (AllWinning.cons node_8815 (AllWinning.cons node_7781 (AllWinning.cons node_6834 (AllWinning.cons node_5925 (AllWinning.cons node_5185 (AllWinning.cons node_4465 (AllWinning.cons node_3786 (AllWinning.cons node_3197 (AllWinning.cons node_2689 (AllWinning.cons node_9819 (AllWinning.cons node_8865 (AllWinning.cons node_7870 (AllWinning.cons node_6921 (AllWinning.cons node_6019 (AllWinning.cons node_5301 (AllWinning.cons node_9822 (AllWinning.nil)))))))))))))))))

theorem node_10901 : Outcome ⟨16, 6, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 6, 1, 2⟩, ⟨14, 6, 1, 4⟩, ⟨13, 6, 1, 6⟩, ⟨12, 6, 1, 8⟩, ⟨11, 6, 1, 10⟩, ⟨10, 6, 1, 12⟩, ⟨9, 6, 1, 14⟩, ⟨8, 6, 1, 16⟩, ⟨7, 6, 1, 18⟩, ⟨6, 6, 1, 20⟩, ⟨5, 6, 1, 22⟩, ⟨4, 6, 1, 24⟩, ⟨16, 5, 1, 2⟩, ⟨16, 4, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨16, 2, 1, 8⟩, ⟨16, 1, 1, 10⟩, ⟨16, 0, 1, 12⟩, ⟨16, 6, 0, 2⟩]
  exact AllWinning.cons node_9790 (AllWinning.cons node_8815 (AllWinning.cons node_7781 (AllWinning.cons node_6834 (AllWinning.cons node_5925 (AllWinning.cons node_5185 (AllWinning.cons node_4465 (AllWinning.cons node_3786 (AllWinning.cons node_3197 (AllWinning.cons node_2689 (AllWinning.cons node_2186 (AllWinning.cons node_1747 (AllWinning.cons node_9819 (AllWinning.cons node_8865 (AllWinning.cons node_7870 (AllWinning.cons node_6921 (AllWinning.cons node_6019 (AllWinning.cons node_5301 (AllWinning.cons node_9822 (AllWinning.nil)))))))))))))))))))

theorem node_10902 : Outcome ⟨16, 6, 1, 18⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 26⟩) (by decide) node_1362

theorem node_10903 : Outcome ⟨16, 6, 1, 22⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 26⟩) (by decide) node_1362

theorem node_10904 : Outcome ⟨16, 7, 0, 2⟩ true :=
  Outcome.win (q := ⟨15, 7, 0, 2⟩) (by decide) node_9794

theorem node_10905 : Outcome ⟨16, 7, 0, 4⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 8⟩) (by decide) node_6927

theorem node_10906 : Outcome ⟨16, 7, 0, 8⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 8⟩) (by decide) node_6927

theorem node_10907 : Outcome ⟨16, 7, 0, 18⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 18⟩) (by decide) node_3206

theorem node_10908 : Outcome ⟨16, 7, 0, 22⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 18⟩) (by decide) node_3206

theorem node_10909 : Outcome ⟨17, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 4⟩) (by decide) node_8872

theorem node_10910 : Outcome ⟨17, 0, 6, 6⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 4⟩) (by decide) node_8872

theorem node_10911 : Outcome ⟨17, 0, 6, 18⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 22⟩) (by decide) node_2201

theorem node_10912 : Outcome ⟨17, 1, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 5, 2⟩, ⟨15, 1, 5, 4⟩, ⟨17, 0, 5, 2⟩, ⟨17, 1, 4, 2⟩, ⟨17, 1, 3, 4⟩]
  exact AllWinning.cons node_9804 (AllWinning.cons node_8827 (AllWinning.cons node_9827 (AllWinning.cons node_9830 (AllWinning.cons node_8877 (AllWinning.nil)))))

theorem node_10913 : Outcome ⟨17, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨17, 1, 2, 6⟩) (by decide) node_7881

theorem node_10914 : Outcome ⟨17, 1, 5, 6⟩ true :=
  Outcome.win (q := ⟨17, 1, 2, 6⟩) (by decide) node_7881

theorem node_10915 : Outcome ⟨17, 1, 5, 12⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 16⟩) (by decide) node_3802

theorem node_10916 : Outcome ⟨17, 1, 5, 16⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 16⟩) (by decide) node_3802

theorem node_10917 : Outcome ⟨17, 2, 4, 2⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 4⟩) (by decide) node_8872

theorem node_10918 : Outcome ⟨17, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10919 : Outcome ⟨17, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10920 : Outcome ⟨17, 2, 4, 12⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10921 : Outcome ⟨17, 2, 4, 14⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 6⟩) (by decide) node_7799

theorem node_10922 : Outcome ⟨17, 3, 3, 2⟩ true :=
  Outcome.win (q := ⟨16, 3, 3, 2⟩) (by decide) node_9812

theorem node_10923 : Outcome ⟨17, 4, 2, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 4⟩) (by decide) node_8887

theorem node_10924 : Outcome ⟨17, 4, 2, 4⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10925 : Outcome ⟨17, 4, 2, 6⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10926 : Outcome ⟨17, 4, 2, 12⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10927 : Outcome ⟨17, 4, 2, 14⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 6⟩) (by decide) node_7810

theorem node_10928 : Outcome ⟨17, 5, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 5, 1, 2⟩, ⟨15, 5, 1, 4⟩, ⟨17, 4, 1, 2⟩, ⟨17, 3, 1, 4⟩, ⟨17, 5, 0, 2⟩]
  exact AllWinning.cons node_9819 (AllWinning.cons node_8841 (AllWinning.cons node_9842 (AllWinning.cons node_8883 (AllWinning.cons node_9848 (AllWinning.nil)))))

theorem node_10929 : Outcome ⟨17, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨17, 2, 1, 6⟩) (by decide) node_7888

theorem node_10930 : Outcome ⟨17, 5, 1, 6⟩ true :=
  Outcome.win (q := ⟨17, 2, 1, 6⟩) (by decide) node_7888

theorem node_10931 : Outcome ⟨17, 5, 1, 12⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 16⟩) (by decide) node_3830

theorem node_10932 : Outcome ⟨17, 5, 1, 16⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 16⟩) (by decide) node_3830

theorem node_10933 : Outcome ⟨17, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 4⟩) (by decide) node_8887

theorem node_10934 : Outcome ⟨17, 6, 0, 6⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 4⟩) (by decide) node_8887

theorem node_10935 : Outcome ⟨17, 6, 0, 18⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 22⟩) (by decide) node_2235

theorem node_10936 : Outcome ⟨18, 0, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 5, 2⟩, ⟨16, 0, 5, 4⟩, ⟨18, 0, 4, 2⟩, ⟨18, 0, 3, 4⟩]
  exact AllWinning.cons node_9827 (AllWinning.cons node_8849 (AllWinning.cons node_9851 (AllWinning.cons node_8892 (AllWinning.nil))))

theorem node_10937 : Outcome ⟨18, 0, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 5, 2⟩, ⟨16, 0, 5, 4⟩, ⟨15, 0, 5, 6⟩, ⟨14, 0, 5, 8⟩, ⟨18, 0, 4, 2⟩, ⟨18, 0, 3, 4⟩, ⟨18, 0, 2, 6⟩, ⟨18, 0, 1, 8⟩]
  exact AllWinning.cons node_9827 (AllWinning.cons node_8849 (AllWinning.cons node_7827 (AllWinning.cons node_6870 (AllWinning.cons node_9851 (AllWinning.cons node_8892 (AllWinning.cons node_7895 (AllWinning.cons node_6939 (AllWinning.nil))))))))

theorem node_10938 : Outcome ⟨18, 0, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 5, 2⟩, ⟨16, 0, 5, 4⟩, ⟨15, 0, 5, 6⟩, ⟨14, 0, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨12, 0, 5, 12⟩, ⟨18, 0, 4, 2⟩, ⟨18, 0, 3, 4⟩, ⟨18, 0, 2, 6⟩, ⟨18, 0, 1, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9827 (AllWinning.cons node_8849 (AllWinning.cons node_7827 (AllWinning.cons node_6870 (AllWinning.cons node_5955 (AllWinning.cons node_5213 (AllWinning.cons node_9851 (AllWinning.cons node_8892 (AllWinning.cons node_7895 (AllWinning.cons node_6939 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))

theorem node_10939 : Outcome ⟨18, 0, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 5, 2⟩, ⟨16, 0, 5, 4⟩, ⟨15, 0, 5, 6⟩, ⟨14, 0, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨12, 0, 5, 12⟩, ⟨11, 0, 5, 14⟩, ⟨10, 0, 5, 16⟩, ⟨18, 0, 4, 2⟩, ⟨18, 0, 3, 4⟩, ⟨18, 0, 2, 6⟩, ⟨18, 0, 1, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9827 (AllWinning.cons node_8849 (AllWinning.cons node_7827 (AllWinning.cons node_6870 (AllWinning.cons node_5955 (AllWinning.cons node_5213 (AllWinning.cons node_4496 (AllWinning.cons node_3843 (AllWinning.cons node_9851 (AllWinning.cons node_8892 (AllWinning.cons node_7895 (AllWinning.cons node_6939 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))))

theorem node_10940 : Outcome ⟨18, 0, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 5, 2⟩, ⟨16, 0, 5, 4⟩, ⟨15, 0, 5, 6⟩, ⟨14, 0, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨12, 0, 5, 12⟩, ⟨11, 0, 5, 14⟩, ⟨10, 0, 5, 16⟩, ⟨9, 0, 5, 18⟩, ⟨8, 0, 5, 20⟩, ⟨18, 0, 4, 2⟩, ⟨18, 0, 3, 4⟩, ⟨18, 0, 2, 6⟩, ⟨18, 0, 1, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9827 (AllWinning.cons node_8849 (AllWinning.cons node_7827 (AllWinning.cons node_6870 (AllWinning.cons node_5955 (AllWinning.cons node_5213 (AllWinning.cons node_4496 (AllWinning.cons node_3843 (AllWinning.cons node_3242 (AllWinning.cons node_2724 (AllWinning.cons node_9851 (AllWinning.cons node_8892 (AllWinning.cons node_7895 (AllWinning.cons node_6939 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))))))

theorem node_10941 : Outcome ⟨18, 0, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 5, 2⟩, ⟨16, 0, 5, 4⟩, ⟨15, 0, 5, 6⟩, ⟨14, 0, 5, 8⟩, ⟨13, 0, 5, 10⟩, ⟨12, 0, 5, 12⟩, ⟨11, 0, 5, 14⟩, ⟨10, 0, 5, 16⟩, ⟨9, 0, 5, 18⟩, ⟨8, 0, 5, 20⟩, ⟨7, 0, 5, 22⟩, ⟨6, 0, 5, 24⟩, ⟨18, 0, 4, 2⟩, ⟨18, 0, 3, 4⟩, ⟨18, 0, 2, 6⟩, ⟨18, 0, 1, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9827 (AllWinning.cons node_8849 (AllWinning.cons node_7827 (AllWinning.cons node_6870 (AllWinning.cons node_5955 (AllWinning.cons node_5213 (AllWinning.cons node_4496 (AllWinning.cons node_3843 (AllWinning.cons node_3242 (AllWinning.cons node_2724 (AllWinning.cons node_2242 (AllWinning.cons node_1780 (AllWinning.cons node_9851 (AllWinning.cons node_8892 (AllWinning.cons node_7895 (AllWinning.cons node_6939 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))))))))

theorem node_10942 : Outcome ⟨18, 0, 5, 24⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 26⟩) (by decide) node_1416

theorem node_10943 : Outcome ⟨18, 1, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 4, 2⟩, ⟨16, 1, 4, 4⟩, ⟨18, 0, 4, 2⟩, ⟨18, 1, 3, 2⟩, ⟨18, 1, 2, 4⟩]
  exact AllWinning.cons node_9830 (AllWinning.cons node_8852 (AllWinning.cons node_9851 (AllWinning.cons node_9853 (AllWinning.cons node_8894 (AllWinning.nil)))))

theorem node_10944 : Outcome ⟨18, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 6⟩) (by decide) node_7832

theorem node_10945 : Outcome ⟨18, 2, 3, 8⟩ true :=
  Outcome.win (q := ⟨18, 2, 2, 2⟩) (by decide) node_9854

theorem node_10946 : Outcome ⟨18, 3, 2, 8⟩ true :=
  Outcome.win (q := ⟨18, 2, 2, 2⟩) (by decide) node_9854

theorem node_10947 : Outcome ⟨18, 4, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 4, 1, 2⟩, ⟨16, 4, 1, 4⟩, ⟨18, 3, 1, 2⟩, ⟨18, 2, 1, 4⟩, ⟨18, 4, 0, 2⟩]
  exact AllWinning.cons node_9842 (AllWinning.cons node_8865 (AllWinning.cons node_9857 (AllWinning.cons node_8897 (AllWinning.cons node_9858 (AllWinning.nil)))))

theorem node_10948 : Outcome ⟨18, 4, 1, 6⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 6⟩) (by decide) node_7847

theorem node_10949 : Outcome ⟨18, 5, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 5, 0, 2⟩, ⟨16, 5, 0, 4⟩, ⟨18, 4, 0, 2⟩, ⟨18, 3, 0, 4⟩]
  exact AllWinning.cons node_9848 (AllWinning.cons node_8868 (AllWinning.cons node_9858 (AllWinning.cons node_8899 (AllWinning.nil))))

theorem node_10950 : Outcome ⟨18, 5, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 5, 0, 2⟩, ⟨16, 5, 0, 4⟩, ⟨15, 5, 0, 6⟩, ⟨14, 5, 0, 8⟩, ⟨18, 4, 0, 2⟩, ⟨18, 3, 0, 4⟩, ⟨18, 2, 0, 6⟩, ⟨18, 1, 0, 8⟩]
  exact AllWinning.cons node_9848 (AllWinning.cons node_8868 (AllWinning.cons node_7853 (AllWinning.cons node_6887 (AllWinning.cons node_9858 (AllWinning.cons node_8899 (AllWinning.cons node_7900 (AllWinning.cons node_6941 (AllWinning.nil))))))))

theorem node_10951 : Outcome ⟨18, 5, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 5, 0, 2⟩, ⟨16, 5, 0, 4⟩, ⟨15, 5, 0, 6⟩, ⟨14, 5, 0, 8⟩, ⟨13, 5, 0, 10⟩, ⟨12, 5, 0, 12⟩, ⟨18, 4, 0, 2⟩, ⟨18, 3, 0, 4⟩, ⟨18, 2, 0, 6⟩, ⟨18, 1, 0, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9848 (AllWinning.cons node_8868 (AllWinning.cons node_7853 (AllWinning.cons node_6887 (AllWinning.cons node_5976 (AllWinning.cons node_5235 (AllWinning.cons node_9858 (AllWinning.cons node_8899 (AllWinning.cons node_7900 (AllWinning.cons node_6941 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))

theorem node_10952 : Outcome ⟨18, 5, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 5, 0, 2⟩, ⟨16, 5, 0, 4⟩, ⟨15, 5, 0, 6⟩, ⟨14, 5, 0, 8⟩, ⟨13, 5, 0, 10⟩, ⟨12, 5, 0, 12⟩, ⟨11, 5, 0, 14⟩, ⟨10, 5, 0, 16⟩, ⟨18, 4, 0, 2⟩, ⟨18, 3, 0, 4⟩, ⟨18, 2, 0, 6⟩, ⟨18, 1, 0, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9848 (AllWinning.cons node_8868 (AllWinning.cons node_7853 (AllWinning.cons node_6887 (AllWinning.cons node_5976 (AllWinning.cons node_5235 (AllWinning.cons node_4511 (AllWinning.cons node_3862 (AllWinning.cons node_9858 (AllWinning.cons node_8899 (AllWinning.cons node_7900 (AllWinning.cons node_6941 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))))

theorem node_10953 : Outcome ⟨18, 5, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 5, 0, 2⟩, ⟨16, 5, 0, 4⟩, ⟨15, 5, 0, 6⟩, ⟨14, 5, 0, 8⟩, ⟨13, 5, 0, 10⟩, ⟨12, 5, 0, 12⟩, ⟨11, 5, 0, 14⟩, ⟨10, 5, 0, 16⟩, ⟨9, 5, 0, 18⟩, ⟨8, 5, 0, 20⟩, ⟨18, 4, 0, 2⟩, ⟨18, 3, 0, 4⟩, ⟨18, 2, 0, 6⟩, ⟨18, 1, 0, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9848 (AllWinning.cons node_8868 (AllWinning.cons node_7853 (AllWinning.cons node_6887 (AllWinning.cons node_5976 (AllWinning.cons node_5235 (AllWinning.cons node_4511 (AllWinning.cons node_3862 (AllWinning.cons node_3259 (AllWinning.cons node_2750 (AllWinning.cons node_9858 (AllWinning.cons node_8899 (AllWinning.cons node_7900 (AllWinning.cons node_6941 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))))))

theorem node_10954 : Outcome ⟨18, 5, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 5, 0, 2⟩, ⟨16, 5, 0, 4⟩, ⟨15, 5, 0, 6⟩, ⟨14, 5, 0, 8⟩, ⟨13, 5, 0, 10⟩, ⟨12, 5, 0, 12⟩, ⟨11, 5, 0, 14⟩, ⟨10, 5, 0, 16⟩, ⟨9, 5, 0, 18⟩, ⟨8, 5, 0, 20⟩, ⟨7, 5, 0, 22⟩, ⟨6, 5, 0, 24⟩, ⟨18, 4, 0, 2⟩, ⟨18, 3, 0, 4⟩, ⟨18, 2, 0, 6⟩, ⟨18, 1, 0, 8⟩, ⟨18, 0, 0, 10⟩]
  exact AllWinning.cons node_9848 (AllWinning.cons node_8868 (AllWinning.cons node_7853 (AllWinning.cons node_6887 (AllWinning.cons node_5976 (AllWinning.cons node_5235 (AllWinning.cons node_4511 (AllWinning.cons node_3862 (AllWinning.cons node_3259 (AllWinning.cons node_2750 (AllWinning.cons node_2290 (AllWinning.cons node_1797 (AllWinning.cons node_9858 (AllWinning.cons node_8899 (AllWinning.cons node_7900 (AllWinning.cons node_6941 (AllWinning.cons node_6034 (AllWinning.nil)))))))))))))))))

theorem node_10955 : Outcome ⟨18, 5, 0, 24⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 26⟩) (by decide) node_1450

theorem node_10956 : Outcome ⟨19, 0, 4, 4⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 4⟩) (by decide) node_8872

theorem node_10957 : Outcome ⟨19, 0, 4, 28⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 30⟩) (by decide) node_834

theorem node_10958 : Outcome ⟨19, 0, 4, 30⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 30⟩) (by decide) node_834

theorem node_10959 : Outcome ⟨19, 1, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 3, 2⟩, ⟨17, 1, 3, 4⟩, ⟨19, 0, 3, 2⟩, ⟨19, 1, 2, 2⟩, ⟨19, 1, 1, 4⟩]
  exact AllWinning.cons node_9853 (AllWinning.cons node_8877 (AllWinning.cons node_9860 (AllWinning.cons node_9863 (AllWinning.cons node_8902 (AllWinning.nil)))))

theorem node_10960 : Outcome ⟨19, 1, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 3, 2⟩, ⟨17, 1, 3, 4⟩, ⟨16, 1, 3, 6⟩, ⟨15, 1, 3, 8⟩, ⟨19, 0, 3, 2⟩, ⟨19, 1, 2, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 1, 0, 6⟩]
  exact AllWinning.cons node_9853 (AllWinning.cons node_8877 (AllWinning.cons node_7861 (AllWinning.cons node_6894 (AllWinning.cons node_9860 (AllWinning.cons node_9863 (AllWinning.cons node_8902 (AllWinning.cons node_7906 (AllWinning.nil))))))))

theorem node_10961 : Outcome ⟨19, 1, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 3, 2⟩, ⟨17, 1, 3, 4⟩, ⟨16, 1, 3, 6⟩, ⟨15, 1, 3, 8⟩, ⟨14, 1, 3, 10⟩, ⟨13, 1, 3, 12⟩, ⟨19, 0, 3, 2⟩, ⟨19, 1, 2, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 1, 0, 6⟩]
  exact AllWinning.cons node_9853 (AllWinning.cons node_8877 (AllWinning.cons node_7861 (AllWinning.cons node_6894 (AllWinning.cons node_5983 (AllWinning.cons node_5244 (AllWinning.cons node_9860 (AllWinning.cons node_9863 (AllWinning.cons node_8902 (AllWinning.cons node_7906 (AllWinning.nil))))))))))

theorem node_10962 : Outcome ⟨19, 1, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 3, 2⟩, ⟨17, 1, 3, 4⟩, ⟨16, 1, 3, 6⟩, ⟨15, 1, 3, 8⟩, ⟨14, 1, 3, 10⟩, ⟨13, 1, 3, 12⟩, ⟨12, 1, 3, 14⟩, ⟨11, 1, 3, 16⟩, ⟨19, 0, 3, 2⟩, ⟨19, 1, 2, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 1, 0, 6⟩]
  exact AllWinning.cons node_9853 (AllWinning.cons node_8877 (AllWinning.cons node_7861 (AllWinning.cons node_6894 (AllWinning.cons node_5983 (AllWinning.cons node_5244 (AllWinning.cons node_4520 (AllWinning.cons node_3869 (AllWinning.cons node_9860 (AllWinning.cons node_9863 (AllWinning.cons node_8902 (AllWinning.cons node_7906 (AllWinning.nil))))))))))))

theorem node_10963 : Outcome ⟨19, 1, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 3, 2⟩, ⟨17, 1, 3, 4⟩, ⟨16, 1, 3, 6⟩, ⟨15, 1, 3, 8⟩, ⟨14, 1, 3, 10⟩, ⟨13, 1, 3, 12⟩, ⟨12, 1, 3, 14⟩, ⟨11, 1, 3, 16⟩, ⟨10, 1, 3, 18⟩, ⟨9, 1, 3, 20⟩, ⟨8, 1, 3, 22⟩, ⟨7, 1, 3, 24⟩, ⟨19, 0, 3, 2⟩, ⟨19, 1, 2, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 1, 0, 6⟩]
  exact AllWinning.cons node_9853 (AllWinning.cons node_8877 (AllWinning.cons node_7861 (AllWinning.cons node_6894 (AllWinning.cons node_5983 (AllWinning.cons node_5244 (AllWinning.cons node_4520 (AllWinning.cons node_3869 (AllWinning.cons node_3265 (AllWinning.cons node_2760 (AllWinning.cons node_2299 (AllWinning.cons node_1805 (AllWinning.cons node_9860 (AllWinning.cons node_9863 (AllWinning.cons node_8902 (AllWinning.cons node_7906 (AllWinning.nil))))))))))))))))

theorem node_10964 : Outcome ⟨19, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨18, 2, 2, 2⟩) (by decide) node_9854

theorem node_10965 : Outcome ⟨19, 2, 2, 12⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 12⟩) (by decide) node_5252

theorem node_10966 : Outcome ⟨19, 3, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 3, 1, 2⟩, ⟨17, 3, 1, 4⟩, ⟨19, 2, 1, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 3, 0, 2⟩]
  exact AllWinning.cons node_9857 (AllWinning.cons node_8883 (AllWinning.cons node_9865 (AllWinning.cons node_8902 (AllWinning.cons node_9868 (AllWinning.nil)))))

theorem node_10967 : Outcome ⟨19, 3, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 3, 1, 2⟩, ⟨17, 3, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨15, 3, 1, 8⟩, ⟨19, 2, 1, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 0, 1, 6⟩, ⟨19, 3, 0, 2⟩]
  exact AllWinning.cons node_9857 (AllWinning.cons node_8883 (AllWinning.cons node_7870 (AllWinning.cons node_6901 (AllWinning.cons node_9865 (AllWinning.cons node_8902 (AllWinning.cons node_7903 (AllWinning.cons node_9868 (AllWinning.nil))))))))

theorem node_10968 : Outcome ⟨19, 3, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 3, 1, 2⟩, ⟨17, 3, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨15, 3, 1, 8⟩, ⟨14, 3, 1, 10⟩, ⟨13, 3, 1, 12⟩, ⟨19, 2, 1, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 0, 1, 6⟩, ⟨19, 3, 0, 2⟩]
  exact AllWinning.cons node_9857 (AllWinning.cons node_8883 (AllWinning.cons node_7870 (AllWinning.cons node_6901 (AllWinning.cons node_5991 (AllWinning.cons node_5256 (AllWinning.cons node_9865 (AllWinning.cons node_8902 (AllWinning.cons node_7903 (AllWinning.cons node_9868 (AllWinning.nil))))))))))

theorem node_10969 : Outcome ⟨19, 3, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 3, 1, 2⟩, ⟨17, 3, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨15, 3, 1, 8⟩, ⟨14, 3, 1, 10⟩, ⟨13, 3, 1, 12⟩, ⟨12, 3, 1, 14⟩, ⟨11, 3, 1, 16⟩, ⟨19, 2, 1, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 0, 1, 6⟩, ⟨19, 3, 0, 2⟩]
  exact AllWinning.cons node_9857 (AllWinning.cons node_8883 (AllWinning.cons node_7870 (AllWinning.cons node_6901 (AllWinning.cons node_5991 (AllWinning.cons node_5256 (AllWinning.cons node_4527 (AllWinning.cons node_3875 (AllWinning.cons node_9865 (AllWinning.cons node_8902 (AllWinning.cons node_7903 (AllWinning.cons node_9868 (AllWinning.nil))))))))))))

theorem node_10970 : Outcome ⟨19, 3, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 3, 1, 2⟩, ⟨17, 3, 1, 4⟩, ⟨16, 3, 1, 6⟩, ⟨15, 3, 1, 8⟩, ⟨14, 3, 1, 10⟩, ⟨13, 3, 1, 12⟩, ⟨12, 3, 1, 14⟩, ⟨11, 3, 1, 16⟩, ⟨10, 3, 1, 18⟩, ⟨9, 3, 1, 20⟩, ⟨8, 3, 1, 22⟩, ⟨7, 3, 1, 24⟩, ⟨19, 2, 1, 2⟩, ⟨19, 1, 1, 4⟩, ⟨19, 0, 1, 6⟩, ⟨19, 3, 0, 2⟩]
  exact AllWinning.cons node_9857 (AllWinning.cons node_8883 (AllWinning.cons node_7870 (AllWinning.cons node_6901 (AllWinning.cons node_5991 (AllWinning.cons node_5256 (AllWinning.cons node_4527 (AllWinning.cons node_3875 (AllWinning.cons node_3272 (AllWinning.cons node_2768 (AllWinning.cons node_2310 (AllWinning.cons node_1811 (AllWinning.cons node_9865 (AllWinning.cons node_8902 (AllWinning.cons node_7903 (AllWinning.cons node_9868 (AllWinning.nil))))))))))))))))

theorem node_10971 : Outcome ⟨19, 4, 0, 4⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 4⟩) (by decide) node_8887

theorem node_10972 : Outcome ⟨19, 4, 0, 28⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 30⟩) (by decide) node_860

theorem node_10973 : Outcome ⟨19, 4, 0, 30⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 30⟩) (by decide) node_860

theorem node_10974 : Outcome ⟨0, 4, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 20, 4⟩) (by decide) node_8905

theorem node_10975 : Outcome ⟨0, 4, 20, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 6⟩) (by decide) node_7918

theorem node_10976 : Outcome ⟨0, 4, 20, 10⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 6⟩) (by decide) node_7918

theorem node_10977 : Outcome ⟨0, 5, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 2⟩) (by decide) node_9875

theorem node_10978 : Outcome ⟨0, 5, 19, 20⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 28⟩) (by decide) node_1184

theorem node_10979 : Outcome ⟨0, 6, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 2⟩) (by decide) node_9875

theorem node_10980 : Outcome ⟨0, 6, 18, 8⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 2⟩) (by decide) node_9875

theorem node_10981 : Outcome ⟨0, 6, 18, 20⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 24⟩) (by decide) node_1900

theorem node_10982 : Outcome ⟨0, 6, 18, 24⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 24⟩) (by decide) node_1900

theorem node_10983 : Outcome ⟨0, 7, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 15, 4⟩) (by decide) node_8924

theorem node_10984 : Outcome ⟨0, 7, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 6⟩) (by decide) node_7918

theorem node_10985 : Outcome ⟨0, 7, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 6⟩) (by decide) node_7918

theorem node_10986 : Outcome ⟨0, 7, 17, 10⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 20⟩) (by decide) node_2858

theorem node_10987 : Outcome ⟨0, 7, 17, 20⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 20⟩) (by decide) node_2858

theorem node_10988 : Outcome ⟨0, 8, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 16, 2⟩, ⟨0, 6, 16, 4⟩, ⟨0, 8, 15, 2⟩, ⟨0, 8, 14, 4⟩]
  exact AllWinning.cons node_9886 (AllWinning.cons node_8919 (AllWinning.cons node_9890 (AllWinning.cons node_8930 (AllWinning.nil))))

theorem node_10989 : Outcome ⟨0, 8, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 16, 2⟩, ⟨0, 6, 16, 4⟩, ⟨0, 5, 16, 6⟩, ⟨0, 4, 16, 8⟩, ⟨0, 8, 15, 2⟩, ⟨0, 8, 14, 4⟩, ⟨0, 8, 13, 6⟩, ⟨0, 8, 12, 8⟩]
  exact AllWinning.cons node_9886 (AllWinning.cons node_8919 (AllWinning.cons node_7923 (AllWinning.cons node_6958 (AllWinning.cons node_9890 (AllWinning.cons node_8930 (AllWinning.cons node_7936 (AllWinning.cons node_6977 (AllWinning.nil))))))))

theorem node_10990 : Outcome ⟨0, 8, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 10⟩) (by decide) node_6046

theorem node_10991 : Outcome ⟨0, 8, 16, 16⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 16⟩) (by decide) node_3965

theorem node_10992 : Outcome ⟨0, 9, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 15, 4⟩) (by decide) node_8924

theorem node_10993 : Outcome ⟨0, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 7, 15, 4⟩) (by decide) node_8924

theorem node_10994 : Outcome ⟨0, 9, 15, 12⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 12⟩) (by decide) node_5349

theorem node_10995 : Outcome ⟨0, 10, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 14, 2⟩) (by decide) node_9894

theorem node_10996 : Outcome ⟨0, 10, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 8⟩) (by decide) node_6983

theorem node_10997 : Outcome ⟨0, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 4⟩) (by decide) node_8939

theorem node_10998 : Outcome ⟨0, 11, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 4⟩) (by decide) node_8939

theorem node_10999 : Outcome ⟨0, 12, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.nil))))

theorem node_11000 : Outcome ⟨0, 12, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.nil))))))))

theorem node_11001 : Outcome ⟨0, 12, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 7, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 12, 7, 10⟩, ⟨0, 12, 6, 12⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_6065 (AllWinning.cons node_5335 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.cons node_6085 (AllWinning.cons node_5364 (AllWinning.nil))))))))))))

theorem node_11002 : Outcome ⟨0, 12, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 7, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨0, 5, 12, 14⟩, ⟨0, 4, 12, 16⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 12, 7, 10⟩, ⟨0, 12, 6, 12⟩, ⟨0, 12, 5, 14⟩, ⟨0, 12, 4, 16⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_6065 (AllWinning.cons node_5335 (AllWinning.cons node_4595 (AllWinning.cons node_3945 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.cons node_6085 (AllWinning.cons node_5364 (AllWinning.cons node_4624 (AllWinning.cons node_3986 (AllWinning.nil))))))))))))))))

theorem node_11003 : Outcome ⟨0, 12, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 7, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨0, 5, 12, 14⟩, ⟨0, 4, 12, 16⟩, ⟨0, 3, 12, 18⟩, ⟨0, 2, 12, 20⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 12, 7, 10⟩, ⟨0, 12, 6, 12⟩, ⟨0, 12, 5, 14⟩, ⟨0, 12, 4, 16⟩, ⟨0, 12, 3, 18⟩, ⟨0, 12, 2, 20⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_6065 (AllWinning.cons node_5335 (AllWinning.cons node_4595 (AllWinning.cons node_3945 (AllWinning.cons node_3334 (AllWinning.cons node_2832 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.cons node_6085 (AllWinning.cons node_5364 (AllWinning.cons node_4624 (AllWinning.cons node_3986 (AllWinning.cons node_3369 (AllWinning.cons node_2881 (AllWinning.nil))))))))))))))))))))

theorem node_11004 : Outcome ⟨0, 12, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 7, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨0, 5, 12, 14⟩, ⟨0, 4, 12, 16⟩, ⟨0, 3, 12, 18⟩, ⟨0, 2, 12, 20⟩, ⟨0, 1, 12, 22⟩, ⟨0, 0, 12, 24⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 12, 7, 10⟩, ⟨0, 12, 6, 12⟩, ⟨0, 12, 5, 14⟩, ⟨0, 12, 4, 16⟩, ⟨0, 12, 3, 18⟩, ⟨0, 12, 2, 20⟩, ⟨0, 12, 1, 22⟩, ⟨0, 12, 0, 24⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_6065 (AllWinning.cons node_5335 (AllWinning.cons node_4595 (AllWinning.cons node_3945 (AllWinning.cons node_3334 (AllWinning.cons node_2832 (AllWinning.cons node_2371 (AllWinning.cons node_1866 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.cons node_6085 (AllWinning.cons node_5364 (AllWinning.cons node_4624 (AllWinning.cons node_3986 (AllWinning.cons node_3369 (AllWinning.cons node_2881 (AllWinning.cons node_2423 (AllWinning.cons node_1927 (AllWinning.nil))))))))))))))))))))))))

theorem node_11005 : Outcome ⟨0, 12, 12, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 7, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨0, 5, 12, 14⟩, ⟨0, 4, 12, 16⟩, ⟨0, 3, 12, 18⟩, ⟨0, 2, 12, 20⟩, ⟨0, 1, 12, 22⟩, ⟨0, 0, 12, 24⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 12, 7, 10⟩, ⟨0, 12, 6, 12⟩, ⟨0, 12, 5, 14⟩, ⟨0, 12, 4, 16⟩, ⟨0, 12, 3, 18⟩, ⟨0, 12, 2, 20⟩, ⟨0, 12, 1, 22⟩, ⟨0, 12, 0, 24⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_6065 (AllWinning.cons node_5335 (AllWinning.cons node_4595 (AllWinning.cons node_3945 (AllWinning.cons node_3334 (AllWinning.cons node_2832 (AllWinning.cons node_2371 (AllWinning.cons node_1866 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.cons node_6085 (AllWinning.cons node_5364 (AllWinning.cons node_4624 (AllWinning.cons node_3986 (AllWinning.cons node_3369 (AllWinning.cons node_2881 (AllWinning.cons node_2423 (AllWinning.cons node_1927 (AllWinning.nil))))))))))))))))))))))))

theorem node_11006 : Outcome ⟨0, 12, 12, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 7, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨0, 5, 12, 14⟩, ⟨0, 4, 12, 16⟩, ⟨0, 3, 12, 18⟩, ⟨0, 2, 12, 20⟩, ⟨0, 1, 12, 22⟩, ⟨0, 0, 12, 24⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 12, 7, 10⟩, ⟨0, 12, 6, 12⟩, ⟨0, 12, 5, 14⟩, ⟨0, 12, 4, 16⟩, ⟨0, 12, 3, 18⟩, ⟨0, 12, 2, 20⟩, ⟨0, 12, 1, 22⟩, ⟨0, 12, 0, 24⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_6065 (AllWinning.cons node_5335 (AllWinning.cons node_4595 (AllWinning.cons node_3945 (AllWinning.cons node_3334 (AllWinning.cons node_2832 (AllWinning.cons node_2371 (AllWinning.cons node_1866 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.cons node_6085 (AllWinning.cons node_5364 (AllWinning.cons node_4624 (AllWinning.cons node_3986 (AllWinning.cons node_3369 (AllWinning.cons node_2881 (AllWinning.cons node_2423 (AllWinning.cons node_1927 (AllWinning.nil))))))))))))))))))))))))

theorem node_11007 : Outcome ⟨0, 12, 12, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨0, 8, 12, 8⟩, ⟨0, 7, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨0, 5, 12, 14⟩, ⟨0, 4, 12, 16⟩, ⟨0, 3, 12, 18⟩, ⟨0, 2, 12, 20⟩, ⟨0, 1, 12, 22⟩, ⟨0, 0, 12, 24⟩, ⟨0, 12, 11, 2⟩, ⟨0, 12, 10, 4⟩, ⟨0, 12, 9, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 12, 7, 10⟩, ⟨0, 12, 6, 12⟩, ⟨0, 12, 5, 14⟩, ⟨0, 12, 4, 16⟩, ⟨0, 12, 3, 18⟩, ⟨0, 12, 2, 20⟩, ⟨0, 12, 1, 22⟩, ⟨0, 12, 0, 24⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_8935 (AllWinning.cons node_7939 (AllWinning.cons node_6977 (AllWinning.cons node_6065 (AllWinning.cons node_5335 (AllWinning.cons node_4595 (AllWinning.cons node_3945 (AllWinning.cons node_3334 (AllWinning.cons node_2832 (AllWinning.cons node_2371 (AllWinning.cons node_1866 (AllWinning.cons node_9902 (AllWinning.cons node_8947 (AllWinning.cons node_7948 (AllWinning.cons node_6995 (AllWinning.cons node_6085 (AllWinning.cons node_5364 (AllWinning.cons node_4624 (AllWinning.cons node_3986 (AllWinning.cons node_3369 (AllWinning.cons node_2881 (AllWinning.cons node_2423 (AllWinning.cons node_1927 (AllWinning.nil))))))))))))))))))))))))

theorem node_11008 : Outcome ⟨0, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 4⟩) (by decide) node_8939

theorem node_11009 : Outcome ⟨0, 13, 11, 6⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 4⟩) (by decide) node_8939

theorem node_11010 : Outcome ⟨0, 14, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 9, 2⟩) (by decide) node_9906

theorem node_11011 : Outcome ⟨0, 14, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 8⟩) (by decide) node_6983

theorem node_11012 : Outcome ⟨0, 15, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 7, 4⟩) (by decide) node_8957

theorem node_11013 : Outcome ⟨0, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 7, 4⟩) (by decide) node_8957

theorem node_11014 : Outcome ⟨0, 15, 9, 12⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 12⟩) (by decide) node_5349

theorem node_11015 : Outcome ⟨0, 16, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 8, 2⟩, ⟨0, 14, 8, 4⟩, ⟨0, 16, 7, 2⟩, ⟨0, 16, 6, 4⟩]
  exact AllWinning.cons node_9910 (AllWinning.cons node_8954 (AllWinning.cons node_9914 (AllWinning.cons node_8963 (AllWinning.nil))))

theorem node_11016 : Outcome ⟨0, 16, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 8, 2⟩, ⟨0, 14, 8, 4⟩, ⟨0, 13, 8, 6⟩, ⟨0, 12, 8, 8⟩, ⟨0, 16, 7, 2⟩, ⟨0, 16, 6, 4⟩, ⟨0, 16, 5, 6⟩, ⟨0, 16, 4, 8⟩]
  exact AllWinning.cons node_9910 (AllWinning.cons node_8954 (AllWinning.cons node_7950 (AllWinning.cons node_6995 (AllWinning.cons node_9914 (AllWinning.cons node_8963 (AllWinning.cons node_7962 (AllWinning.cons node_7012 (AllWinning.nil))))))))

theorem node_11017 : Outcome ⟨0, 16, 8, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 10⟩) (by decide) node_6104

theorem node_11018 : Outcome ⟨0, 16, 8, 16⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 16⟩) (by decide) node_3965

end RQ9F1
