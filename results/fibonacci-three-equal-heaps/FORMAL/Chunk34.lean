import Chunk33
set_option autoImplicit false
namespace RQ9F1

theorem node_7847 : Outcome ⟨15, 4, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 1, 2⟩, ⟨13, 4, 1, 4⟩, ⟨12, 4, 1, 6⟩, ⟨11, 4, 1, 8⟩, ⟨10, 4, 1, 10⟩, ⟨9, 4, 1, 12⟩, ⟨15, 3, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨15, 1, 1, 6⟩, ⟨15, 0, 1, 8⟩, ⟨15, 4, 0, 2⟩]
  exact AllWinning.cons node_6883 (AllWinning.cons node_5968 (AllWinning.cons node_5230 (AllWinning.cons node_4506 (AllWinning.cons node_3857 (AllWinning.cons node_3255 (AllWinning.cons node_6900 (AllWinning.cons node_6005 (AllWinning.cons node_5289 (AllWinning.cons node_4558 (AllWinning.cons node_6904 (AllWinning.nil)))))))))))

theorem node_7848 : Outcome ⟨15, 4, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 1, 2⟩, ⟨13, 4, 1, 4⟩, ⟨12, 4, 1, 6⟩, ⟨11, 4, 1, 8⟩, ⟨10, 4, 1, 10⟩, ⟨9, 4, 1, 12⟩, ⟨8, 4, 1, 14⟩, ⟨7, 4, 1, 16⟩, ⟨15, 3, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨15, 1, 1, 6⟩, ⟨15, 0, 1, 8⟩, ⟨15, 4, 0, 2⟩]
  exact AllWinning.cons node_6883 (AllWinning.cons node_5968 (AllWinning.cons node_5230 (AllWinning.cons node_4506 (AllWinning.cons node_3857 (AllWinning.cons node_3255 (AllWinning.cons node_2743 (AllWinning.cons node_2286 (AllWinning.cons node_6900 (AllWinning.cons node_6005 (AllWinning.cons node_5289 (AllWinning.cons node_4558 (AllWinning.cons node_6904 (AllWinning.nil)))))))))))))

theorem node_7849 : Outcome ⟨15, 4, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 1, 2⟩, ⟨13, 4, 1, 4⟩, ⟨12, 4, 1, 6⟩, ⟨11, 4, 1, 8⟩, ⟨10, 4, 1, 10⟩, ⟨9, 4, 1, 12⟩, ⟨8, 4, 1, 14⟩, ⟨7, 4, 1, 16⟩, ⟨6, 4, 1, 18⟩, ⟨5, 4, 1, 20⟩, ⟨15, 3, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨15, 1, 1, 6⟩, ⟨15, 0, 1, 8⟩, ⟨15, 4, 0, 2⟩]
  exact AllWinning.cons node_6883 (AllWinning.cons node_5968 (AllWinning.cons node_5230 (AllWinning.cons node_4506 (AllWinning.cons node_3857 (AllWinning.cons node_3255 (AllWinning.cons node_2743 (AllWinning.cons node_2286 (AllWinning.cons node_1793 (AllWinning.cons node_1437 (AllWinning.cons node_6900 (AllWinning.cons node_6005 (AllWinning.cons node_5289 (AllWinning.cons node_4558 (AllWinning.cons node_6904 (AllWinning.nil)))))))))))))))

theorem node_7850 : Outcome ⟨15, 4, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 1, 2⟩, ⟨13, 4, 1, 4⟩, ⟨12, 4, 1, 6⟩, ⟨11, 4, 1, 8⟩, ⟨10, 4, 1, 10⟩, ⟨9, 4, 1, 12⟩, ⟨8, 4, 1, 14⟩, ⟨7, 4, 1, 16⟩, ⟨6, 4, 1, 18⟩, ⟨5, 4, 1, 20⟩, ⟨4, 4, 1, 22⟩, ⟨3, 4, 1, 24⟩, ⟨15, 3, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨15, 1, 1, 6⟩, ⟨15, 0, 1, 8⟩, ⟨15, 4, 0, 2⟩]
  exact AllWinning.cons node_6883 (AllWinning.cons node_5968 (AllWinning.cons node_5230 (AllWinning.cons node_4506 (AllWinning.cons node_3857 (AllWinning.cons node_3255 (AllWinning.cons node_2743 (AllWinning.cons node_2286 (AllWinning.cons node_1793 (AllWinning.cons node_1437 (AllWinning.cons node_1081 (AllWinning.cons node_815 (AllWinning.cons node_6900 (AllWinning.cons node_6005 (AllWinning.cons node_5289 (AllWinning.cons node_4558 (AllWinning.cons node_6904 (AllWinning.nil)))))))))))))))))

theorem node_7851 : Outcome ⟨15, 4, 1, 24⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 26⟩) (by decide) node_589

theorem node_7852 : Outcome ⟨15, 5, 0, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 6⟩) (by decide) node_5293

theorem node_7853 : Outcome ⟨15, 5, 0, 6⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 6⟩) (by decide) node_5293

theorem node_7854 : Outcome ⟨15, 5, 0, 16⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 20⟩) (by decide) node_1447

theorem node_7855 : Outcome ⟨15, 5, 0, 20⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 20⟩) (by decide) node_1447

theorem node_7856 : Outcome ⟨16, 0, 4, 2⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 2⟩) (by decide) node_6908

theorem node_7857 : Outcome ⟨16, 0, 4, 8⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 2⟩) (by decide) node_6908

theorem node_7858 : Outcome ⟨16, 0, 4, 18⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 24⟩) (by decide) node_831

theorem node_7859 : Outcome ⟨16, 0, 4, 24⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 24⟩) (by decide) node_831

theorem node_7860 : Outcome ⟨16, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 2⟩) (by decide) node_6908

theorem node_7861 : Outcome ⟨16, 1, 3, 6⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 2⟩) (by decide) node_6908

theorem node_7862 : Outcome ⟨16, 1, 3, 8⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 2⟩) (by decide) node_6908

theorem node_7863 : Outcome ⟨16, 1, 3, 14⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 20⟩) (by decide) node_1464

theorem node_7864 : Outcome ⟨16, 1, 3, 24⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 20⟩) (by decide) node_1464

theorem node_7865 : Outcome ⟨16, 2, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 2, 2, 2⟩, ⟨14, 2, 2, 4⟩, ⟨16, 1, 2, 2⟩, ⟨16, 0, 2, 4⟩, ⟨16, 2, 1, 2⟩, ⟨16, 2, 0, 4⟩]
  exact AllWinning.cons node_6897 (AllWinning.cons node_5986 (AllWinning.cons node_6916 (AllWinning.cons node_6014 (AllWinning.cons node_6920 (AllWinning.cons node_6022 (AllWinning.nil))))))

theorem node_7866 : Outcome ⟨16, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 6⟩) (by decide) node_5249

theorem node_7867 : Outcome ⟨16, 2, 2, 16⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 32⟩) (by decide) node_155

theorem node_7868 : Outcome ⟨16, 2, 2, 32⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 32⟩) (by decide) node_155

theorem node_7869 : Outcome ⟨16, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 2⟩) (by decide) node_6924

theorem node_7870 : Outcome ⟨16, 3, 1, 6⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 2⟩) (by decide) node_6924

theorem node_7871 : Outcome ⟨16, 3, 1, 8⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 2⟩) (by decide) node_6924

theorem node_7872 : Outcome ⟨16, 3, 1, 14⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 20⟩) (by decide) node_1484

theorem node_7873 : Outcome ⟨16, 3, 1, 24⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 20⟩) (by decide) node_1484

theorem node_7874 : Outcome ⟨16, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 2⟩) (by decide) node_6924

theorem node_7875 : Outcome ⟨16, 4, 0, 8⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 2⟩) (by decide) node_6924

theorem node_7876 : Outcome ⟨16, 4, 0, 18⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 24⟩) (by decide) node_857

theorem node_7877 : Outcome ⟨16, 4, 0, 24⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 24⟩) (by decide) node_857

theorem node_7878 : Outcome ⟨17, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 2⟩) (by decide) node_6908

theorem node_7879 : Outcome ⟨17, 1, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 2, 2⟩, ⟨15, 1, 2, 4⟩, ⟨17, 0, 2, 2⟩, ⟨17, 1, 1, 2⟩, ⟨17, 1, 0, 4⟩]
  exact AllWinning.cons node_6916 (AllWinning.cons node_6001 (AllWinning.cons node_6932 (AllWinning.cons node_6934 (AllWinning.cons node_6030 (AllWinning.nil)))))

theorem node_7880 : Outcome ⟨17, 1, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 2, 2⟩, ⟨15, 1, 2, 4⟩, ⟨14, 1, 2, 6⟩, ⟨13, 1, 2, 8⟩, ⟨17, 0, 2, 2⟩, ⟨17, 1, 1, 2⟩, ⟨17, 1, 0, 4⟩]
  exact AllWinning.cons node_6916 (AllWinning.cons node_6001 (AllWinning.cons node_5269 (AllWinning.cons node_4540 (AllWinning.cons node_6932 (AllWinning.cons node_6934 (AllWinning.cons node_6030 (AllWinning.nil)))))))

theorem node_7881 : Outcome ⟨17, 1, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 2, 2⟩, ⟨15, 1, 2, 4⟩, ⟨14, 1, 2, 6⟩, ⟨13, 1, 2, 8⟩, ⟨12, 1, 2, 10⟩, ⟨11, 1, 2, 12⟩, ⟨17, 0, 2, 2⟩, ⟨17, 1, 1, 2⟩, ⟨17, 1, 0, 4⟩]
  exact AllWinning.cons node_6916 (AllWinning.cons node_6001 (AllWinning.cons node_5269 (AllWinning.cons node_4540 (AllWinning.cons node_3886 (AllWinning.cons node_3286 (AllWinning.cons node_6932 (AllWinning.cons node_6934 (AllWinning.cons node_6030 (AllWinning.nil)))))))))

theorem node_7882 : Outcome ⟨17, 1, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 2, 2⟩, ⟨15, 1, 2, 4⟩, ⟨14, 1, 2, 6⟩, ⟨13, 1, 2, 8⟩, ⟨12, 1, 2, 10⟩, ⟨11, 1, 2, 12⟩, ⟨10, 1, 2, 14⟩, ⟨9, 1, 2, 16⟩, ⟨17, 0, 2, 2⟩, ⟨17, 1, 1, 2⟩, ⟨17, 1, 0, 4⟩]
  exact AllWinning.cons node_6916 (AllWinning.cons node_6001 (AllWinning.cons node_5269 (AllWinning.cons node_4540 (AllWinning.cons node_3886 (AllWinning.cons node_3286 (AllWinning.cons node_2781 (AllWinning.cons node_2323 (AllWinning.cons node_6932 (AllWinning.cons node_6934 (AllWinning.cons node_6030 (AllWinning.nil)))))))))))

theorem node_7883 : Outcome ⟨17, 1, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 2, 2⟩, ⟨15, 1, 2, 4⟩, ⟨14, 1, 2, 6⟩, ⟨13, 1, 2, 8⟩, ⟨12, 1, 2, 10⟩, ⟨11, 1, 2, 12⟩, ⟨10, 1, 2, 14⟩, ⟨9, 1, 2, 16⟩, ⟨8, 1, 2, 18⟩, ⟨7, 1, 2, 20⟩, ⟨6, 1, 2, 22⟩, ⟨5, 1, 2, 24⟩, ⟨17, 0, 2, 2⟩, ⟨17, 1, 1, 2⟩, ⟨17, 1, 0, 4⟩]
  exact AllWinning.cons node_6916 (AllWinning.cons node_6001 (AllWinning.cons node_5269 (AllWinning.cons node_4540 (AllWinning.cons node_3886 (AllWinning.cons node_3286 (AllWinning.cons node_2781 (AllWinning.cons node_2323 (AllWinning.cons node_1824 (AllWinning.cons node_1502 (AllWinning.cons node_1112 (AllWinning.cons node_870 (AllWinning.cons node_6932 (AllWinning.cons node_6934 (AllWinning.cons node_6030 (AllWinning.nil)))))))))))))))

theorem node_7884 : Outcome ⟨17, 1, 2, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 26⟩) (by decide) node_628

theorem node_7885 : Outcome ⟨17, 1, 2, 22⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 26⟩) (by decide) node_628

theorem node_7886 : Outcome ⟨17, 2, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨17, 1, 1, 2⟩, ⟨17, 0, 1, 4⟩, ⟨17, 2, 0, 2⟩]
  exact AllWinning.cons node_6920 (AllWinning.cons node_6005 (AllWinning.cons node_6934 (AllWinning.cons node_6026 (AllWinning.cons node_6936 (AllWinning.nil)))))

theorem node_7887 : Outcome ⟨17, 2, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨14, 2, 1, 6⟩, ⟨13, 2, 1, 8⟩, ⟨17, 1, 1, 2⟩, ⟨17, 0, 1, 4⟩, ⟨17, 2, 0, 2⟩]
  exact AllWinning.cons node_6920 (AllWinning.cons node_6005 (AllWinning.cons node_5273 (AllWinning.cons node_4543 (AllWinning.cons node_6934 (AllWinning.cons node_6026 (AllWinning.cons node_6936 (AllWinning.nil)))))))

theorem node_7888 : Outcome ⟨17, 2, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨14, 2, 1, 6⟩, ⟨13, 2, 1, 8⟩, ⟨12, 2, 1, 10⟩, ⟨11, 2, 1, 12⟩, ⟨17, 1, 1, 2⟩, ⟨17, 0, 1, 4⟩, ⟨17, 2, 0, 2⟩]
  exact AllWinning.cons node_6920 (AllWinning.cons node_6005 (AllWinning.cons node_5273 (AllWinning.cons node_4543 (AllWinning.cons node_3892 (AllWinning.cons node_3289 (AllWinning.cons node_6934 (AllWinning.cons node_6026 (AllWinning.cons node_6936 (AllWinning.nil)))))))))

theorem node_7889 : Outcome ⟨17, 2, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨14, 2, 1, 6⟩, ⟨13, 2, 1, 8⟩, ⟨12, 2, 1, 10⟩, ⟨11, 2, 1, 12⟩, ⟨10, 2, 1, 14⟩, ⟨9, 2, 1, 16⟩, ⟨17, 1, 1, 2⟩, ⟨17, 0, 1, 4⟩, ⟨17, 2, 0, 2⟩]
  exact AllWinning.cons node_6920 (AllWinning.cons node_6005 (AllWinning.cons node_5273 (AllWinning.cons node_4543 (AllWinning.cons node_3892 (AllWinning.cons node_3289 (AllWinning.cons node_2785 (AllWinning.cons node_2327 (AllWinning.cons node_6934 (AllWinning.cons node_6026 (AllWinning.cons node_6936 (AllWinning.nil)))))))))))

theorem node_7890 : Outcome ⟨17, 2, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 1, 2⟩, ⟨15, 2, 1, 4⟩, ⟨14, 2, 1, 6⟩, ⟨13, 2, 1, 8⟩, ⟨12, 2, 1, 10⟩, ⟨11, 2, 1, 12⟩, ⟨10, 2, 1, 14⟩, ⟨9, 2, 1, 16⟩, ⟨8, 2, 1, 18⟩, ⟨7, 2, 1, 20⟩, ⟨6, 2, 1, 22⟩, ⟨5, 2, 1, 24⟩, ⟨17, 1, 1, 2⟩, ⟨17, 0, 1, 4⟩, ⟨17, 2, 0, 2⟩]
  exact AllWinning.cons node_6920 (AllWinning.cons node_6005 (AllWinning.cons node_5273 (AllWinning.cons node_4543 (AllWinning.cons node_3892 (AllWinning.cons node_3289 (AllWinning.cons node_2785 (AllWinning.cons node_2327 (AllWinning.cons node_1829 (AllWinning.cons node_1506 (AllWinning.cons node_1117 (AllWinning.cons node_875 (AllWinning.cons node_6934 (AllWinning.cons node_6026 (AllWinning.cons node_6936 (AllWinning.nil)))))))))))))))

theorem node_7891 : Outcome ⟨17, 2, 1, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 26⟩) (by decide) node_646

theorem node_7892 : Outcome ⟨17, 2, 1, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 26⟩) (by decide) node_646

theorem node_7893 : Outcome ⟨17, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 2⟩) (by decide) node_6924

theorem node_7894 : Outcome ⟨18, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 6⟩) (by decide) node_5283

theorem node_7895 : Outcome ⟨18, 0, 2, 6⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 6⟩) (by decide) node_5283

theorem node_7896 : Outcome ⟨18, 0, 2, 14⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 6⟩) (by decide) node_5283

theorem node_7897 : Outcome ⟨18, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 1, 2⟩, ⟨16, 1, 1, 4⟩, ⟨18, 0, 1, 2⟩, ⟨18, 1, 0, 2⟩]
  exact AllWinning.cons node_6934 (AllWinning.cons node_6018 (AllWinning.cons node_6938 (AllWinning.cons node_6940 (AllWinning.nil))))

theorem node_7898 : Outcome ⟨18, 1, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 1, 2⟩, ⟨16, 1, 1, 4⟩, ⟨15, 1, 1, 6⟩, ⟨14, 1, 1, 8⟩, ⟨18, 0, 1, 2⟩, ⟨18, 1, 0, 2⟩]
  exact AllWinning.cons node_6934 (AllWinning.cons node_6018 (AllWinning.cons node_5289 (AllWinning.cons node_4551 (AllWinning.cons node_6938 (AllWinning.cons node_6940 (AllWinning.nil))))))

theorem node_7899 : Outcome ⟨18, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 6⟩) (by decide) node_5293

theorem node_7900 : Outcome ⟨18, 2, 0, 6⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 6⟩) (by decide) node_5293

theorem node_7901 : Outcome ⟨18, 2, 0, 14⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 6⟩) (by decide) node_5293

theorem node_7902 : Outcome ⟨19, 0, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 0, 1, 2⟩, ⟨17, 0, 1, 4⟩, ⟨16, 0, 1, 6⟩, ⟨15, 0, 1, 8⟩, ⟨19, 0, 0, 2⟩]
  exact AllWinning.cons node_6938 (AllWinning.cons node_6026 (AllWinning.cons node_5300 (AllWinning.cons node_4558 (AllWinning.cons node_6942 (AllWinning.nil)))))

theorem node_7903 : Outcome ⟨19, 0, 1, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 10⟩) (by decide) node_3913

theorem node_7904 : Outcome ⟨19, 0, 1, 10⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 10⟩) (by decide) node_3913

theorem node_7905 : Outcome ⟨19, 1, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 1, 0, 2⟩, ⟨17, 1, 0, 4⟩, ⟨16, 1, 0, 6⟩, ⟨15, 1, 0, 8⟩, ⟨19, 0, 0, 2⟩]
  exact AllWinning.cons node_6940 (AllWinning.cons node_6030 (AllWinning.cons node_5305 (AllWinning.cons node_4562 (AllWinning.cons node_6942 (AllWinning.nil)))))

theorem node_7906 : Outcome ⟨19, 1, 0, 6⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 10⟩) (by decide) node_3921

theorem node_7907 : Outcome ⟨19, 1, 0, 10⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 10⟩) (by decide) node_3921

theorem node_7908 : Outcome ⟨0, 1, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 19, 2⟩) (by decide) node_6947

theorem node_7909 : Outcome ⟨0, 1, 20, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 12⟩) (by decide) node_3326

theorem node_7910 : Outcome ⟨0, 2, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 19, 2⟩) (by decide) node_6947

theorem node_7911 : Outcome ⟨0, 2, 19, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 8⟩) (by decide) node_4578

theorem node_7912 : Outcome ⟨0, 2, 19, 16⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 8⟩) (by decide) node_4578

theorem node_7913 : Outcome ⟨0, 3, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 4⟩) (by decide) node_6043

theorem node_7914 : Outcome ⟨0, 3, 18, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 4⟩) (by decide) node_6043

theorem node_7915 : Outcome ⟨0, 3, 18, 30⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 30⟩) (by decide) node_351

theorem node_7916 : Outcome ⟨0, 4, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 17, 2⟩, ⟨0, 2, 17, 4⟩, ⟨0, 4, 16, 2⟩, ⟨0, 4, 15, 4⟩]
  exact AllWinning.cons node_6955 (AllWinning.cons node_6040 (AllWinning.cons node_6957 (AllWinning.cons node_6051 (AllWinning.nil))))

theorem node_7917 : Outcome ⟨0, 4, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 17, 2⟩, ⟨0, 2, 17, 4⟩, ⟨0, 1, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨0, 4, 16, 2⟩, ⟨0, 4, 15, 4⟩, ⟨0, 4, 14, 6⟩, ⟨0, 4, 13, 8⟩]
  exact AllWinning.cons node_6955 (AllWinning.cons node_6040 (AllWinning.cons node_5315 (AllWinning.cons node_4569 (AllWinning.cons node_6957 (AllWinning.cons node_6051 (AllWinning.cons node_5326 (AllWinning.cons node_4588 (AllWinning.nil))))))))

theorem node_7918 : Outcome ⟨0, 4, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 17, 2⟩, ⟨0, 2, 17, 4⟩, ⟨0, 1, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨0, 4, 16, 2⟩, ⟨0, 4, 15, 4⟩, ⟨0, 4, 14, 6⟩, ⟨0, 4, 13, 8⟩, ⟨0, 4, 12, 10⟩, ⟨0, 4, 11, 12⟩]
  exact AllWinning.cons node_6955 (AllWinning.cons node_6040 (AllWinning.cons node_5315 (AllWinning.cons node_4569 (AllWinning.cons node_6957 (AllWinning.cons node_6051 (AllWinning.cons node_5326 (AllWinning.cons node_4588 (AllWinning.cons node_3944 (AllWinning.cons node_3337 (AllWinning.nil))))))))))

theorem node_7919 : Outcome ⟨0, 4, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 17, 2⟩, ⟨0, 2, 17, 4⟩, ⟨0, 1, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨0, 4, 16, 2⟩, ⟨0, 4, 15, 4⟩, ⟨0, 4, 14, 6⟩, ⟨0, 4, 13, 8⟩, ⟨0, 4, 12, 10⟩, ⟨0, 4, 11, 12⟩, ⟨0, 4, 10, 14⟩, ⟨0, 4, 9, 16⟩]
  exact AllWinning.cons node_6955 (AllWinning.cons node_6040 (AllWinning.cons node_5315 (AllWinning.cons node_4569 (AllWinning.cons node_6957 (AllWinning.cons node_6051 (AllWinning.cons node_5326 (AllWinning.cons node_4588 (AllWinning.cons node_3944 (AllWinning.cons node_3337 (AllWinning.cons node_2842 (AllWinning.cons node_2385 (AllWinning.nil))))))))))))

theorem node_7920 : Outcome ⟨0, 4, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 17, 2⟩, ⟨0, 2, 17, 4⟩, ⟨0, 1, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨0, 4, 16, 2⟩, ⟨0, 4, 15, 4⟩, ⟨0, 4, 14, 6⟩, ⟨0, 4, 13, 8⟩, ⟨0, 4, 12, 10⟩, ⟨0, 4, 11, 12⟩, ⟨0, 4, 10, 14⟩, ⟨0, 4, 9, 16⟩, ⟨0, 4, 8, 18⟩, ⟨0, 4, 7, 20⟩]
  exact AllWinning.cons node_6955 (AllWinning.cons node_6040 (AllWinning.cons node_5315 (AllWinning.cons node_4569 (AllWinning.cons node_6957 (AllWinning.cons node_6051 (AllWinning.cons node_5326 (AllWinning.cons node_4588 (AllWinning.cons node_3944 (AllWinning.cons node_3337 (AllWinning.cons node_2842 (AllWinning.cons node_2385 (AllWinning.cons node_1884 (AllWinning.cons node_1565 (AllWinning.nil))))))))))))))

theorem node_7921 : Outcome ⟨0, 4, 17, 16⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 26⟩) (by decide) node_711

theorem node_7922 : Outcome ⟨0, 5, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 4⟩) (by decide) node_6043

theorem node_7923 : Outcome ⟨0, 5, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 4⟩) (by decide) node_6043

theorem node_7924 : Outcome ⟨0, 5, 16, 22⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 22⟩) (by decide) node_1181

theorem node_7925 : Outcome ⟨0, 6, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 14, 2⟩) (by decide) node_6965

theorem node_7926 : Outcome ⟨0, 6, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 8⟩) (by decide) node_4578

theorem node_7927 : Outcome ⟨0, 6, 15, 18⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 18⟩) (by decide) node_1897

theorem node_7928 : Outcome ⟨0, 6, 15, 22⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 18⟩) (by decide) node_1897

theorem node_7929 : Outcome ⟨0, 7, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 14, 2⟩) (by decide) node_6965

theorem node_7930 : Outcome ⟨0, 7, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 14, 2⟩) (by decide) node_6965

theorem node_7931 : Outcome ⟨0, 7, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 14⟩) (by decide) node_2855

theorem node_7932 : Outcome ⟨0, 7, 14, 12⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 14⟩) (by decide) node_2855

theorem node_7933 : Outcome ⟨0, 7, 14, 14⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 14⟩) (by decide) node_2855

theorem node_7934 : Outcome ⟨0, 8, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 13, 2⟩, ⟨0, 6, 13, 4⟩, ⟨0, 8, 12, 2⟩, ⟨0, 8, 11, 4⟩]
  exact AllWinning.cons node_6971 (AllWinning.cons node_6058 (AllWinning.cons node_6976 (AllWinning.cons node_6070 (AllWinning.nil))))

theorem node_7935 : Outcome ⟨0, 8, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 13, 2⟩, ⟨0, 6, 13, 4⟩, ⟨0, 5, 13, 6⟩, ⟨0, 4, 13, 8⟩, ⟨0, 8, 12, 2⟩, ⟨0, 8, 11, 4⟩, ⟨0, 8, 10, 6⟩, ⟨0, 8, 9, 8⟩]
  exact AllWinning.cons node_6971 (AllWinning.cons node_6058 (AllWinning.cons node_5330 (AllWinning.cons node_4588 (AllWinning.cons node_6976 (AllWinning.cons node_6070 (AllWinning.cons node_5342 (AllWinning.cons node_4607 (AllWinning.nil))))))))

theorem node_7936 : Outcome ⟨0, 8, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 10⟩) (by decide) node_3962

theorem node_7937 : Outcome ⟨0, 8, 13, 10⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 10⟩) (by decide) node_3962

theorem node_7938 : Outcome ⟨0, 9, 12, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 6⟩) (by decide) node_5346

theorem node_7939 : Outcome ⟨0, 9, 12, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 6⟩) (by decide) node_5346

theorem node_7940 : Outcome ⟨0, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_7941 : Outcome ⟨0, 10, 11, 8⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_7942 : Outcome ⟨0, 10, 11, 16⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_7943 : Outcome ⟨0, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_7944 : Outcome ⟨0, 11, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_7945 : Outcome ⟨0, 11, 10, 16⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_7946 : Outcome ⟨0, 12, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 9, 2⟩, ⟨0, 10, 9, 4⟩, ⟨0, 12, 8, 2⟩, ⟨0, 12, 7, 4⟩]
  exact AllWinning.cons node_6991 (AllWinning.cons node_6076 (AllWinning.cons node_6994 (AllWinning.cons node_6083 (AllWinning.nil))))

theorem node_7947 : Outcome ⟨0, 12, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 6⟩) (by decide) node_5346

theorem node_7948 : Outcome ⟨0, 12, 9, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 6⟩) (by decide) node_5346

theorem node_7949 : Outcome ⟨0, 13, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨0, 11, 8, 4⟩, ⟨0, 10, 8, 6⟩, ⟨0, 9, 8, 8⟩, ⟨0, 13, 7, 2⟩, ⟨0, 13, 6, 4⟩, ⟨0, 13, 5, 6⟩, ⟨0, 13, 4, 8⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_6079 (AllWinning.cons node_5357 (AllWinning.cons node_4610 (AllWinning.cons node_6996 (AllWinning.cons node_6090 (AllWinning.cons node_5368 (AllWinning.cons node_4626 (AllWinning.nil))))))))

theorem node_7950 : Outcome ⟨0, 13, 8, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 10⟩) (by decide) node_3962

theorem node_7951 : Outcome ⟨0, 13, 8, 10⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 10⟩) (by decide) node_3962

theorem node_7952 : Outcome ⟨0, 14, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 6, 2⟩) (by decide) node_7001

theorem node_7953 : Outcome ⟨0, 14, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 6, 2⟩) (by decide) node_7001

theorem node_7954 : Outcome ⟨0, 14, 7, 8⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 14⟩) (by decide) node_2855

theorem node_7955 : Outcome ⟨0, 14, 7, 12⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 14⟩) (by decide) node_2855

theorem node_7956 : Outcome ⟨0, 14, 7, 14⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 14⟩) (by decide) node_2855

theorem node_7957 : Outcome ⟨0, 15, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 6, 2⟩) (by decide) node_7001

theorem node_7958 : Outcome ⟨0, 15, 6, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 8⟩) (by decide) node_4637

theorem node_7959 : Outcome ⟨0, 15, 6, 18⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 18⟩) (by decide) node_1897

theorem node_7960 : Outcome ⟨0, 15, 6, 22⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 18⟩) (by decide) node_1897

theorem node_7961 : Outcome ⟨0, 16, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 4⟩) (by decide) node_6101

theorem node_7962 : Outcome ⟨0, 16, 5, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 4⟩) (by decide) node_6101

theorem node_7963 : Outcome ⟨0, 16, 5, 22⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 22⟩) (by decide) node_1181

theorem node_7964 : Outcome ⟨0, 17, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 4, 2⟩, ⟨0, 15, 4, 4⟩, ⟨0, 17, 3, 2⟩, ⟨0, 17, 2, 4⟩]
  exact AllWinning.cons node_7011 (AllWinning.cons node_6097 (AllWinning.cons node_7015 (AllWinning.cons node_6109 (AllWinning.nil))))

theorem node_7965 : Outcome ⟨0, 17, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 4, 2⟩, ⟨0, 15, 4, 4⟩, ⟨0, 14, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨0, 17, 3, 2⟩, ⟨0, 17, 2, 4⟩, ⟨0, 17, 1, 6⟩, ⟨0, 17, 0, 8⟩]
  exact AllWinning.cons node_7011 (AllWinning.cons node_6097 (AllWinning.cons node_5372 (AllWinning.cons node_4626 (AllWinning.cons node_7015 (AllWinning.cons node_6109 (AllWinning.cons node_5384 (AllWinning.cons node_4647 (AllWinning.nil))))))))

theorem node_7966 : Outcome ⟨0, 17, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 4, 2⟩, ⟨0, 15, 4, 4⟩, ⟨0, 14, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨0, 12, 4, 10⟩, ⟨0, 11, 4, 12⟩, ⟨0, 17, 3, 2⟩, ⟨0, 17, 2, 4⟩, ⟨0, 17, 1, 6⟩, ⟨0, 17, 0, 8⟩]
  exact AllWinning.cons node_7011 (AllWinning.cons node_6097 (AllWinning.cons node_5372 (AllWinning.cons node_4626 (AllWinning.cons node_3985 (AllWinning.cons node_3365 (AllWinning.cons node_7015 (AllWinning.cons node_6109 (AllWinning.cons node_5384 (AllWinning.cons node_4647 (AllWinning.nil))))))))))

theorem node_7967 : Outcome ⟨0, 17, 4, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 4, 2⟩, ⟨0, 15, 4, 4⟩, ⟨0, 14, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨0, 12, 4, 10⟩, ⟨0, 11, 4, 12⟩, ⟨0, 10, 4, 14⟩, ⟨0, 9, 4, 16⟩, ⟨0, 17, 3, 2⟩, ⟨0, 17, 2, 4⟩, ⟨0, 17, 1, 6⟩, ⟨0, 17, 0, 8⟩]
  exact AllWinning.cons node_7011 (AllWinning.cons node_6097 (AllWinning.cons node_5372 (AllWinning.cons node_4626 (AllWinning.cons node_3985 (AllWinning.cons node_3365 (AllWinning.cons node_2871 (AllWinning.cons node_2408 (AllWinning.cons node_7015 (AllWinning.cons node_6109 (AllWinning.cons node_5384 (AllWinning.cons node_4647 (AllWinning.nil))))))))))))

theorem node_7968 : Outcome ⟨0, 17, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 4, 2⟩, ⟨0, 15, 4, 4⟩, ⟨0, 14, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨0, 12, 4, 10⟩, ⟨0, 11, 4, 12⟩, ⟨0, 10, 4, 14⟩, ⟨0, 9, 4, 16⟩, ⟨0, 8, 4, 18⟩, ⟨0, 7, 4, 20⟩, ⟨0, 17, 3, 2⟩, ⟨0, 17, 2, 4⟩, ⟨0, 17, 1, 6⟩, ⟨0, 17, 0, 8⟩]
  exact AllWinning.cons node_7011 (AllWinning.cons node_6097 (AllWinning.cons node_5372 (AllWinning.cons node_4626 (AllWinning.cons node_3985 (AllWinning.cons node_3365 (AllWinning.cons node_2871 (AllWinning.cons node_2408 (AllWinning.cons node_1909 (AllWinning.cons node_1575 (AllWinning.cons node_7015 (AllWinning.cons node_6109 (AllWinning.cons node_5384 (AllWinning.cons node_4647 (AllWinning.nil))))))))))))))

theorem node_7969 : Outcome ⟨0, 17, 4, 16⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 26⟩) (by decide) node_711

theorem node_7970 : Outcome ⟨0, 18, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 4⟩) (by decide) node_6101

theorem node_7971 : Outcome ⟨0, 18, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 4⟩) (by decide) node_6101

theorem node_7972 : Outcome ⟨0, 18, 3, 30⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 30⟩) (by decide) node_351

theorem node_7973 : Outcome ⟨0, 19, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 1, 2⟩) (by decide) node_7021

theorem node_7974 : Outcome ⟨0, 19, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 8⟩) (by decide) node_4637

theorem node_7975 : Outcome ⟨0, 19, 2, 16⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 8⟩) (by decide) node_4637

theorem node_7976 : Outcome ⟨0, 20, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 1, 2⟩) (by decide) node_7021

theorem node_7977 : Outcome ⟨0, 20, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 12⟩) (by decide) node_3378

theorem node_7978 : Outcome ⟨1, 0, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 19, 2⟩) (by decide) node_7027

theorem node_7979 : Outcome ⟨1, 0, 20, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 12⟩) (by decide) node_3389

theorem node_7980 : Outcome ⟨1, 0, 20, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 12⟩) (by decide) node_3389

theorem node_7981 : Outcome ⟨1, 1, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 19, 2⟩) (by decide) node_6947

theorem node_7982 : Outcome ⟨1, 2, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 18, 2⟩) (by decide) node_7031

theorem node_7983 : Outcome ⟨1, 2, 18, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 18, 2⟩) (by decide) node_7031

theorem node_7984 : Outcome ⟨1, 2, 18, 30⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 28⟩) (by decide) node_517

theorem node_7985 : Outcome ⟨1, 3, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 2⟩) (by decide) node_7033

theorem node_7986 : Outcome ⟨1, 3, 17, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 2⟩) (by decide) node_7033

theorem node_7987 : Outcome ⟨1, 3, 17, 20⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 22⟩) (by decide) node_1229

theorem node_7988 : Outcome ⟨1, 3, 17, 26⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 22⟩) (by decide) node_1229

theorem node_7989 : Outcome ⟨1, 4, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 2⟩) (by decide) node_7045

theorem node_7990 : Outcome ⟨1, 4, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 2⟩) (by decide) node_7045

theorem node_7991 : Outcome ⟨1, 4, 16, 16⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 28⟩) (by decide) node_538

theorem node_7992 : Outcome ⟨1, 4, 16, 22⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 28⟩) (by decide) node_538

theorem node_7993 : Outcome ⟨1, 5, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 2⟩) (by decide) node_7045

theorem node_7994 : Outcome ⟨1, 5, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 2⟩) (by decide) node_7045

theorem node_7995 : Outcome ⟨1, 5, 15, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 12⟩) (by decide) node_3417

theorem node_7996 : Outcome ⟨1, 5, 15, 14⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 12⟩) (by decide) node_3417

theorem node_7997 : Outcome ⟨1, 5, 15, 22⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 12⟩) (by decide) node_3417

theorem node_7998 : Outcome ⟨1, 6, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 14, 2⟩) (by decide) node_6965

theorem node_7999 : Outcome ⟨1, 6, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 12⟩) (by decide) node_3389

theorem node_8000 : Outcome ⟨1, 6, 14, 24⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 22⟩) (by decide) node_1257

theorem node_8001 : Outcome ⟨1, 7, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 4⟩) (by decide) node_6138

theorem node_8002 : Outcome ⟨1, 7, 13, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 12⟩) (by decide) node_3397

theorem node_8003 : Outcome ⟨1, 7, 13, 16⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 12⟩) (by decide) node_3397

theorem node_8004 : Outcome ⟨1, 7, 13, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 12⟩) (by decide) node_3397

theorem node_8005 : Outcome ⟨1, 8, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.nil)))))

theorem node_8006 : Outcome ⟨1, 8, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.nil)))))))))

theorem node_8007 : Outcome ⟨1, 8, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.nil)))))))))))))

theorem node_8008 : Outcome ⟨1, 8, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.nil)))))))))))))))))

theorem node_8009 : Outcome ⟨1, 8, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.nil)))))))))))))))))))

theorem node_8010 : Outcome ⟨1, 8, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩, ⟨1, 8, 1, 22⟩, ⟨1, 8, 0, 24⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.cons node_1272 (AllWinning.cons node_992 (AllWinning.nil)))))))))))))))))))))

theorem node_8011 : Outcome ⟨1, 8, 12, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩, ⟨1, 8, 1, 22⟩, ⟨1, 8, 0, 24⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.cons node_1272 (AllWinning.cons node_992 (AllWinning.nil)))))))))))))))))))))

theorem node_8012 : Outcome ⟨1, 8, 12, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩, ⟨1, 8, 1, 22⟩, ⟨1, 8, 0, 24⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.cons node_1272 (AllWinning.cons node_992 (AllWinning.nil)))))))))))))))))))))

theorem node_8013 : Outcome ⟨1, 8, 12, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩, ⟨1, 8, 1, 22⟩, ⟨1, 8, 0, 24⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.cons node_1272 (AllWinning.cons node_992 (AllWinning.nil)))))))))))))))))))))

theorem node_8014 : Outcome ⟨1, 8, 12, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩, ⟨1, 8, 1, 22⟩, ⟨1, 8, 0, 24⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.cons node_1272 (AllWinning.cons node_992 (AllWinning.nil)))))))))))))))))))))

theorem node_8015 : Outcome ⟨1, 8, 12, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩, ⟨1, 8, 1, 22⟩, ⟨1, 8, 0, 24⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.cons node_1272 (AllWinning.cons node_992 (AllWinning.nil)))))))))))))))))))))

theorem node_8016 : Outcome ⟨1, 8, 12, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 12, 2⟩, ⟨1, 7, 12, 2⟩, ⟨1, 6, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨1, 3, 12, 10⟩, ⟨1, 2, 12, 12⟩, ⟨1, 1, 12, 14⟩, ⟨1, 0, 12, 16⟩, ⟨1, 8, 11, 2⟩, ⟨1, 8, 10, 4⟩, ⟨1, 8, 9, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 8, 7, 10⟩, ⟨1, 8, 6, 12⟩, ⟨1, 8, 5, 14⟩, ⟨1, 8, 4, 16⟩, ⟨1, 8, 3, 18⟩, ⟨1, 8, 2, 20⟩, ⟨1, 8, 1, 22⟩, ⟨1, 8, 0, 24⟩]
  exact AllWinning.cons node_6976 (AllWinning.cons node_7060 (AllWinning.cons node_6134 (AllWinning.cons node_5411 (AllWinning.cons node_4669 (AllWinning.cons node_4010 (AllWinning.cons node_3402 (AllWinning.cons node_2894 (AllWinning.cons node_2433 (AllWinning.cons node_7063 (AllWinning.cons node_6150 (AllWinning.cons node_5420 (AllWinning.cons node_4684 (AllWinning.cons node_4029 (AllWinning.cons node_3434 (AllWinning.cons node_2920 (AllWinning.cons node_2462 (AllWinning.cons node_1967 (AllWinning.cons node_1627 (AllWinning.cons node_1272 (AllWinning.cons node_992 (AllWinning.nil)))))))))))))))))))))

theorem node_8017 : Outcome ⟨1, 9, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 4⟩) (by decide) node_6138

theorem node_8018 : Outcome ⟨1, 9, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 4⟩) (by decide) node_6138

theorem node_8019 : Outcome ⟨1, 9, 11, 12⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 12⟩) (by decide) node_3441

theorem node_8020 : Outcome ⟨1, 10, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_8021 : Outcome ⟨1, 10, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_8022 : Outcome ⟨1, 10, 10, 12⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 2⟩) (by decide) node_6980

theorem node_8023 : Outcome ⟨1, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 4⟩) (by decide) node_6163

theorem node_8024 : Outcome ⟨1, 11, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 4⟩) (by decide) node_6163

theorem node_8025 : Outcome ⟨1, 11, 9, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 12⟩) (by decide) node_3417

theorem node_8026 : Outcome ⟨1, 12, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.nil)))))

theorem node_8027 : Outcome ⟨1, 12, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.nil)))))))))

theorem node_8028 : Outcome ⟨1, 12, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.nil)))))))))))))

theorem node_8029 : Outcome ⟨1, 12, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))

theorem node_8030 : Outcome ⟨1, 12, 8, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))

theorem node_8031 : Outcome ⟨1, 12, 8, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 1, 8, 22⟩, ⟨1, 0, 8, 24⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_1214 (AllWinning.cons node_955 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))))

theorem node_8032 : Outcome ⟨1, 12, 8, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 1, 8, 22⟩, ⟨1, 0, 8, 24⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_1214 (AllWinning.cons node_955 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))))

theorem node_8033 : Outcome ⟨1, 12, 8, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 1, 8, 22⟩, ⟨1, 0, 8, 24⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_1214 (AllWinning.cons node_955 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))))

theorem node_8034 : Outcome ⟨1, 12, 8, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 1, 8, 22⟩, ⟨1, 0, 8, 24⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_1214 (AllWinning.cons node_955 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))))

theorem node_8035 : Outcome ⟨1, 12, 8, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 1, 8, 22⟩, ⟨1, 0, 8, 24⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_1214 (AllWinning.cons node_955 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))))

end RQ9F1
