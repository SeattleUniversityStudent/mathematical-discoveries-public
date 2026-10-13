import Chunk28
set_option autoImplicit false
namespace RQ9F1

theorem node_6892 : Outcome ⟨15, 0, 4, 22⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 22⟩) (by decide) node_830

theorem node_6893 : Outcome ⟨15, 1, 3, 2⟩ true :=
  Outcome.win (q := ⟨14, 1, 3, 2⟩) (by decide) node_5981

theorem node_6894 : Outcome ⟨15, 1, 3, 8⟩ true :=
  Outcome.win (q := ⟨14, 1, 3, 2⟩) (by decide) node_5981

theorem node_6895 : Outcome ⟨15, 1, 3, 12⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 18⟩) (by decide) node_1463

theorem node_6896 : Outcome ⟨15, 1, 3, 26⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 18⟩) (by decide) node_1463

theorem node_6897 : Outcome ⟨15, 2, 2, 2⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 4⟩) (by decide) node_5248

theorem node_6898 : Outcome ⟨15, 2, 2, 6⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 4⟩) (by decide) node_5248

theorem node_6899 : Outcome ⟨15, 2, 2, 14⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 4⟩) (by decide) node_5248

theorem node_6900 : Outcome ⟨15, 3, 1, 2⟩ true :=
  Outcome.win (q := ⟨14, 3, 1, 2⟩) (by decide) node_5989

theorem node_6901 : Outcome ⟨15, 3, 1, 8⟩ true :=
  Outcome.win (q := ⟨14, 3, 1, 2⟩) (by decide) node_5989

theorem node_6902 : Outcome ⟨15, 3, 1, 12⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 18⟩) (by decide) node_1483

theorem node_6903 : Outcome ⟨15, 3, 1, 26⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 18⟩) (by decide) node_1483

theorem node_6904 : Outcome ⟨15, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 4⟩) (by decide) node_5292

theorem node_6905 : Outcome ⟨15, 4, 0, 4⟩ true :=
  Outcome.win (q := ⟨12, 4, 0, 6⟩) (by decide) node_4531

theorem node_6906 : Outcome ⟨15, 4, 0, 6⟩ true :=
  Outcome.win (q := ⟨12, 4, 0, 6⟩) (by decide) node_4531

theorem node_6907 : Outcome ⟨15, 4, 0, 22⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 22⟩) (by decide) node_856

theorem node_6908 : Outcome ⟨16, 0, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 3, 2⟩, ⟨14, 0, 3, 4⟩, ⟨16, 0, 2, 2⟩, ⟨16, 0, 1, 4⟩]
  exact AllWinning.cons node_5997 (AllWinning.cons node_5264 (AllWinning.cons node_6013 (AllWinning.cons node_5299 (AllWinning.nil))))

theorem node_6909 : Outcome ⟨16, 0, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 3, 2⟩, ⟨14, 0, 3, 4⟩, ⟨13, 0, 3, 6⟩, ⟨12, 0, 3, 8⟩, ⟨16, 0, 2, 2⟩, ⟨16, 0, 1, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_5997 (AllWinning.cons node_5264 (AllWinning.cons node_4536 (AllWinning.cons node_3881 (AllWinning.cons node_6013 (AllWinning.cons node_5299 (AllWinning.cons node_4566 (AllWinning.nil)))))))

theorem node_6910 : Outcome ⟨16, 0, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 3, 2⟩, ⟨14, 0, 3, 4⟩, ⟨13, 0, 3, 6⟩, ⟨12, 0, 3, 8⟩, ⟨11, 0, 3, 10⟩, ⟨10, 0, 3, 12⟩, ⟨16, 0, 2, 2⟩, ⟨16, 0, 1, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_5997 (AllWinning.cons node_5264 (AllWinning.cons node_4536 (AllWinning.cons node_3881 (AllWinning.cons node_3282 (AllWinning.cons node_2776 (AllWinning.cons node_6013 (AllWinning.cons node_5299 (AllWinning.cons node_4566 (AllWinning.nil)))))))))

theorem node_6911 : Outcome ⟨16, 0, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 3, 2⟩, ⟨14, 0, 3, 4⟩, ⟨13, 0, 3, 6⟩, ⟨12, 0, 3, 8⟩, ⟨11, 0, 3, 10⟩, ⟨10, 0, 3, 12⟩, ⟨9, 0, 3, 14⟩, ⟨8, 0, 3, 16⟩, ⟨16, 0, 2, 2⟩, ⟨16, 0, 1, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_5997 (AllWinning.cons node_5264 (AllWinning.cons node_4536 (AllWinning.cons node_3881 (AllWinning.cons node_3282 (AllWinning.cons node_2776 (AllWinning.cons node_2319 (AllWinning.cons node_1820 (AllWinning.cons node_6013 (AllWinning.cons node_5299 (AllWinning.cons node_4566 (AllWinning.nil)))))))))))

theorem node_6912 : Outcome ⟨16, 0, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 3, 2⟩, ⟨14, 0, 3, 4⟩, ⟨13, 0, 3, 6⟩, ⟨12, 0, 3, 8⟩, ⟨11, 0, 3, 10⟩, ⟨10, 0, 3, 12⟩, ⟨9, 0, 3, 14⟩, ⟨8, 0, 3, 16⟩, ⟨7, 0, 3, 18⟩, ⟨6, 0, 3, 20⟩, ⟨16, 0, 2, 2⟩, ⟨16, 0, 1, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_5997 (AllWinning.cons node_5264 (AllWinning.cons node_4536 (AllWinning.cons node_3881 (AllWinning.cons node_3282 (AllWinning.cons node_2776 (AllWinning.cons node_2319 (AllWinning.cons node_1820 (AllWinning.cons node_1498 (AllWinning.cons node_1107 (AllWinning.cons node_6013 (AllWinning.cons node_5299 (AllWinning.cons node_4566 (AllWinning.nil)))))))))))))

theorem node_6913 : Outcome ⟨16, 0, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 3, 2⟩, ⟨14, 0, 3, 4⟩, ⟨13, 0, 3, 6⟩, ⟨12, 0, 3, 8⟩, ⟨11, 0, 3, 10⟩, ⟨10, 0, 3, 12⟩, ⟨9, 0, 3, 14⟩, ⟨8, 0, 3, 16⟩, ⟨7, 0, 3, 18⟩, ⟨6, 0, 3, 20⟩, ⟨5, 0, 3, 22⟩, ⟨4, 0, 3, 24⟩, ⟨16, 0, 2, 2⟩, ⟨16, 0, 1, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_5997 (AllWinning.cons node_5264 (AllWinning.cons node_4536 (AllWinning.cons node_3881 (AllWinning.cons node_3282 (AllWinning.cons node_2776 (AllWinning.cons node_2319 (AllWinning.cons node_1820 (AllWinning.cons node_1498 (AllWinning.cons node_1107 (AllWinning.cons node_865 (AllWinning.cons node_615 (AllWinning.cons node_6013 (AllWinning.cons node_5299 (AllWinning.cons node_4566 (AllWinning.nil)))))))))))))))

theorem node_6914 : Outcome ⟨16, 0, 3, 16⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 26⟩) (by decide) node_415

theorem node_6915 : Outcome ⟨16, 0, 3, 26⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 26⟩) (by decide) node_415

theorem node_6916 : Outcome ⟨16, 1, 2, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 1, 2⟩) (by decide) node_6017

theorem node_6917 : Outcome ⟨16, 1, 2, 8⟩ true :=
  Outcome.win (q := ⟨16, 1, 1, 2⟩) (by decide) node_6017

theorem node_6918 : Outcome ⟨16, 1, 2, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 24⟩) (by decide) node_627

theorem node_6919 : Outcome ⟨16, 1, 2, 26⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 24⟩) (by decide) node_627

theorem node_6920 : Outcome ⟨16, 2, 1, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 1, 2⟩) (by decide) node_6017

theorem node_6921 : Outcome ⟨16, 2, 1, 8⟩ true :=
  Outcome.win (q := ⟨16, 1, 1, 2⟩) (by decide) node_6017

theorem node_6922 : Outcome ⟨16, 2, 1, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 24⟩) (by decide) node_645

theorem node_6923 : Outcome ⟨16, 2, 1, 26⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 24⟩) (by decide) node_645

theorem node_6924 : Outcome ⟨16, 3, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 0, 2⟩, ⟨14, 3, 0, 4⟩, ⟨16, 2, 0, 2⟩, ⟨16, 1, 0, 4⟩]
  exact AllWinning.cons node_6009 (AllWinning.cons node_5277 (AllWinning.cons node_6021 (AllWinning.cons node_5304 (AllWinning.nil))))

theorem node_6925 : Outcome ⟨16, 3, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 0, 2⟩, ⟨14, 3, 0, 4⟩, ⟨13, 3, 0, 6⟩, ⟨12, 3, 0, 8⟩, ⟨16, 2, 0, 2⟩, ⟨16, 1, 0, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_6009 (AllWinning.cons node_5277 (AllWinning.cons node_4545 (AllWinning.cons node_3896 (AllWinning.cons node_6021 (AllWinning.cons node_5304 (AllWinning.cons node_4566 (AllWinning.nil)))))))

theorem node_6926 : Outcome ⟨16, 3, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 0, 2⟩, ⟨14, 3, 0, 4⟩, ⟨13, 3, 0, 6⟩, ⟨12, 3, 0, 8⟩, ⟨11, 3, 0, 10⟩, ⟨10, 3, 0, 12⟩, ⟨16, 2, 0, 2⟩, ⟨16, 1, 0, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_6009 (AllWinning.cons node_5277 (AllWinning.cons node_4545 (AllWinning.cons node_3896 (AllWinning.cons node_3293 (AllWinning.cons node_2788 (AllWinning.cons node_6021 (AllWinning.cons node_5304 (AllWinning.cons node_4566 (AllWinning.nil)))))))))

theorem node_6927 : Outcome ⟨16, 3, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 0, 2⟩, ⟨14, 3, 0, 4⟩, ⟨13, 3, 0, 6⟩, ⟨12, 3, 0, 8⟩, ⟨11, 3, 0, 10⟩, ⟨10, 3, 0, 12⟩, ⟨9, 3, 0, 14⟩, ⟨8, 3, 0, 16⟩, ⟨16, 2, 0, 2⟩, ⟨16, 1, 0, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_6009 (AllWinning.cons node_5277 (AllWinning.cons node_4545 (AllWinning.cons node_3896 (AllWinning.cons node_3293 (AllWinning.cons node_2788 (AllWinning.cons node_2332 (AllWinning.cons node_1836 (AllWinning.cons node_6021 (AllWinning.cons node_5304 (AllWinning.cons node_4566 (AllWinning.nil)))))))))))

theorem node_6928 : Outcome ⟨16, 3, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 0, 2⟩, ⟨14, 3, 0, 4⟩, ⟨13, 3, 0, 6⟩, ⟨12, 3, 0, 8⟩, ⟨11, 3, 0, 10⟩, ⟨10, 3, 0, 12⟩, ⟨9, 3, 0, 14⟩, ⟨8, 3, 0, 16⟩, ⟨7, 3, 0, 18⟩, ⟨6, 3, 0, 20⟩, ⟨16, 2, 0, 2⟩, ⟨16, 1, 0, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_6009 (AllWinning.cons node_5277 (AllWinning.cons node_4545 (AllWinning.cons node_3896 (AllWinning.cons node_3293 (AllWinning.cons node_2788 (AllWinning.cons node_2332 (AllWinning.cons node_1836 (AllWinning.cons node_1510 (AllWinning.cons node_1122 (AllWinning.cons node_6021 (AllWinning.cons node_5304 (AllWinning.cons node_4566 (AllWinning.nil)))))))))))))

theorem node_6929 : Outcome ⟨16, 3, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 0, 2⟩, ⟨14, 3, 0, 4⟩, ⟨13, 3, 0, 6⟩, ⟨12, 3, 0, 8⟩, ⟨11, 3, 0, 10⟩, ⟨10, 3, 0, 12⟩, ⟨9, 3, 0, 14⟩, ⟨8, 3, 0, 16⟩, ⟨7, 3, 0, 18⟩, ⟨6, 3, 0, 20⟩, ⟨5, 3, 0, 22⟩, ⟨4, 3, 0, 24⟩, ⟨16, 2, 0, 2⟩, ⟨16, 1, 0, 4⟩, ⟨16, 0, 0, 6⟩]
  exact AllWinning.cons node_6009 (AllWinning.cons node_5277 (AllWinning.cons node_4545 (AllWinning.cons node_3896 (AllWinning.cons node_3293 (AllWinning.cons node_2788 (AllWinning.cons node_2332 (AllWinning.cons node_1836 (AllWinning.cons node_1510 (AllWinning.cons node_1122 (AllWinning.cons node_879 (AllWinning.cons node_653 (AllWinning.cons node_6021 (AllWinning.cons node_5304 (AllWinning.cons node_4566 (AllWinning.nil)))))))))))))))

theorem node_6930 : Outcome ⟨16, 3, 0, 16⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 26⟩) (by decide) node_438

theorem node_6931 : Outcome ⟨16, 3, 0, 26⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 26⟩) (by decide) node_438

theorem node_6932 : Outcome ⟨17, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 4⟩) (by decide) node_5282

theorem node_6933 : Outcome ⟨17, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 4⟩) (by decide) node_5282

theorem node_6934 : Outcome ⟨17, 1, 1, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 1, 2⟩) (by decide) node_6017

theorem node_6935 : Outcome ⟨17, 1, 1, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 34⟩) (by decide) node_48

theorem node_6936 : Outcome ⟨17, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 4⟩) (by decide) node_5292

theorem node_6937 : Outcome ⟨17, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 4⟩) (by decide) node_5292

theorem node_6938 : Outcome ⟨18, 0, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 0, 1, 2⟩) (by decide) node_6025

theorem node_6939 : Outcome ⟨18, 0, 1, 8⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 8⟩) (by decide) node_3912

theorem node_6940 : Outcome ⟨18, 1, 0, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 0, 2⟩) (by decide) node_6029

theorem node_6941 : Outcome ⟨18, 1, 0, 8⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 8⟩) (by decide) node_3920

theorem node_6942 : Outcome ⟨19, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨18, 0, 0, 2⟩) (by decide) node_6033

theorem node_6943 : Outcome ⟨19, 0, 0, 12⟩ true :=
  Outcome.win (q := ⟨13, 0, 0, 12⟩) (by decide) node_2819

theorem node_6944 : Outcome ⟨0, 0, 20, 1⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 19, 2⟩]
  exact AllWinning.cons node_6035 (AllWinning.nil)

theorem node_6945 : Outcome ⟨0, 0, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 18, 4⟩) (by decide) node_5311

theorem node_6946 : Outcome ⟨0, 0, 20, 14⟩ true :=
  Outcome.win (q := ⟨0, 0, 18, 4⟩) (by decide) node_5311

theorem node_6947 : Outcome ⟨0, 1, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 19, 2⟩, ⟨0, 1, 18, 2⟩, ⟨0, 1, 17, 4⟩]
  exact AllWinning.cons node_6035 (AllWinning.cons node_6037 (AllWinning.cons node_5314 (AllWinning.nil)))

theorem node_6948 : Outcome ⟨0, 1, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 19, 2⟩, ⟨0, 1, 18, 2⟩, ⟨0, 1, 17, 4⟩, ⟨0, 1, 16, 6⟩, ⟨0, 1, 15, 8⟩]
  exact AllWinning.cons node_6035 (AllWinning.cons node_6037 (AllWinning.cons node_5314 (AllWinning.cons node_4572 (AllWinning.cons node_3933 (AllWinning.nil)))))

theorem node_6949 : Outcome ⟨0, 1, 19, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 10⟩) (by decide) node_3325

theorem node_6950 : Outcome ⟨0, 1, 19, 10⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 10⟩) (by decide) node_3325

theorem node_6951 : Outcome ⟨0, 2, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 6⟩) (by decide) node_4577

theorem node_6952 : Outcome ⟨0, 2, 18, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 6⟩) (by decide) node_4577

theorem node_6953 : Outcome ⟨0, 2, 18, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 6⟩) (by decide) node_4577

theorem node_6954 : Outcome ⟨0, 2, 18, 32⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 32⟩) (by decide) node_155

theorem node_6955 : Outcome ⟨0, 3, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 2⟩) (by decide) node_6042

theorem node_6956 : Outcome ⟨0, 3, 17, 28⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 28⟩) (by decide) node_350

theorem node_6957 : Outcome ⟨0, 4, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 2⟩) (by decide) node_6042

theorem node_6958 : Outcome ⟨0, 4, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 2⟩) (by decide) node_6042

theorem node_6959 : Outcome ⟨0, 4, 16, 18⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 24⟩) (by decide) node_710

theorem node_6960 : Outcome ⟨0, 4, 16, 24⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 24⟩) (by decide) node_710

theorem node_6961 : Outcome ⟨0, 5, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 6⟩) (by decide) node_4577

theorem node_6962 : Outcome ⟨0, 5, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 6⟩) (by decide) node_4577

theorem node_6963 : Outcome ⟨0, 5, 15, 16⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 20⟩) (by decide) node_1180

theorem node_6964 : Outcome ⟨0, 5, 15, 20⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 20⟩) (by decide) node_1180

theorem node_6965 : Outcome ⟨0, 6, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨0, 6, 13, 2⟩, ⟨0, 6, 12, 4⟩]
  exact AllWinning.cons node_6054 (AllWinning.cons node_5325 (AllWinning.cons node_6057 (AllWinning.cons node_5334 (AllWinning.nil))))

theorem node_6966 : Outcome ⟨0, 6, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 14, 2⟩, ⟨0, 4, 14, 4⟩, ⟨0, 3, 14, 6⟩, ⟨0, 2, 14, 8⟩, ⟨0, 6, 13, 2⟩, ⟨0, 6, 12, 4⟩, ⟨0, 6, 11, 6⟩, ⟨0, 6, 10, 8⟩]
  exact AllWinning.cons node_6054 (AllWinning.cons node_5325 (AllWinning.cons node_4584 (AllWinning.cons node_3936 (AllWinning.cons node_6057 (AllWinning.cons node_5334 (AllWinning.cons node_4598 (AllWinning.cons node_3953 (AllWinning.nil))))))))

theorem node_6967 : Outcome ⟨0, 6, 14, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 10⟩) (by decide) node_3325

theorem node_6968 : Outcome ⟨0, 6, 14, 10⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 16⟩) (by decide) node_1896

theorem node_6969 : Outcome ⟨0, 6, 14, 16⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 16⟩) (by decide) node_1896

theorem node_6970 : Outcome ⟨0, 6, 14, 26⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 16⟩) (by decide) node_1896

theorem node_6971 : Outcome ⟨0, 7, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 13, 4⟩) (by decide) node_5329

theorem node_6972 : Outcome ⟨0, 7, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 13, 4⟩) (by decide) node_5329

theorem node_6973 : Outcome ⟨0, 7, 13, 12⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 12⟩) (by decide) node_2854

theorem node_6974 : Outcome ⟨0, 7, 13, 14⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 12⟩) (by decide) node_2854

theorem node_6975 : Outcome ⟨0, 7, 13, 18⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 12⟩) (by decide) node_2854

theorem node_6976 : Outcome ⟨0, 8, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 12, 2⟩) (by decide) node_6062

theorem node_6977 : Outcome ⟨0, 8, 12, 8⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 8⟩) (by decide) node_3961

theorem node_6978 : Outcome ⟨0, 9, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_6979 : Outcome ⟨0, 9, 11, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_6980 : Outcome ⟨0, 10, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.nil))))

theorem node_6981 : Outcome ⟨0, 10, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.nil))))))))

theorem node_6982 : Outcome ⟨0, 10, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.nil))))))))))))

theorem node_6983 : Outcome ⟨0, 10, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.nil))))))))))))))))

theorem node_6984 : Outcome ⟨0, 10, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 1, 10, 18⟩, ⟨0, 0, 10, 20⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩, ⟨0, 10, 1, 18⟩, ⟨0, 10, 0, 20⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_1547 (AllWinning.cons node_1154 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.cons node_1590 (AllWinning.cons node_1204 (AllWinning.nil))))))))))))))))))))

theorem node_6985 : Outcome ⟨0, 10, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 1, 10, 18⟩, ⟨0, 0, 10, 20⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩, ⟨0, 10, 1, 18⟩, ⟨0, 10, 0, 20⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_1547 (AllWinning.cons node_1154 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.cons node_1590 (AllWinning.cons node_1204 (AllWinning.nil))))))))))))))))))))

theorem node_6986 : Outcome ⟨0, 10, 10, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 1, 10, 18⟩, ⟨0, 0, 10, 20⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩, ⟨0, 10, 1, 18⟩, ⟨0, 10, 0, 20⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_1547 (AllWinning.cons node_1154 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.cons node_1590 (AllWinning.cons node_1204 (AllWinning.nil))))))))))))))))))))

theorem node_6987 : Outcome ⟨0, 10, 10, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 1, 10, 18⟩, ⟨0, 0, 10, 20⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩, ⟨0, 10, 1, 18⟩, ⟨0, 10, 0, 20⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_1547 (AllWinning.cons node_1154 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.cons node_1590 (AllWinning.cons node_1204 (AllWinning.nil))))))))))))))))))))

theorem node_6988 : Outcome ⟨0, 10, 10, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 1, 10, 18⟩, ⟨0, 0, 10, 20⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩, ⟨0, 10, 1, 18⟩, ⟨0, 10, 0, 20⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_1547 (AllWinning.cons node_1154 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.cons node_1590 (AllWinning.cons node_1204 (AllWinning.nil))))))))))))))))))))

theorem node_6989 : Outcome ⟨0, 10, 10, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 1, 10, 18⟩, ⟨0, 0, 10, 20⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩, ⟨0, 10, 1, 18⟩, ⟨0, 10, 0, 20⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_1547 (AllWinning.cons node_1154 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.cons node_1590 (AllWinning.cons node_1204 (AllWinning.nil))))))))))))))))))))

theorem node_6990 : Outcome ⟨0, 10, 10, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨0, 8, 10, 4⟩, ⟨0, 7, 10, 6⟩, ⟨0, 6, 10, 8⟩, ⟨0, 5, 10, 10⟩, ⟨0, 4, 10, 12⟩, ⟨0, 3, 10, 14⟩, ⟨0, 2, 10, 16⟩, ⟨0, 1, 10, 18⟩, ⟨0, 0, 10, 20⟩, ⟨0, 10, 9, 2⟩, ⟨0, 10, 8, 4⟩, ⟨0, 10, 7, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 10, 5, 10⟩, ⟨0, 10, 4, 12⟩, ⟨0, 10, 3, 14⟩, ⟨0, 10, 2, 16⟩, ⟨0, 10, 1, 18⟩, ⟨0, 10, 0, 20⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_5341 (AllWinning.cons node_4603 (AllWinning.cons node_3953 (AllWinning.cons node_3342 (AllWinning.cons node_2841 (AllWinning.cons node_2379 (AllWinning.cons node_1876 (AllWinning.cons node_1547 (AllWinning.cons node_1154 (AllWinning.cons node_6075 (AllWinning.cons node_5356 (AllWinning.cons node_4613 (AllWinning.cons node_3975 (AllWinning.cons node_3361 (AllWinning.cons node_2870 (AllWinning.cons node_2413 (AllWinning.cons node_1919 (AllWinning.cons node_1590 (AllWinning.cons node_1204 (AllWinning.nil))))))))))))))))))))

theorem node_6991 : Outcome ⟨0, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_6992 : Outcome ⟨0, 11, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_6993 : Outcome ⟨0, 11, 9, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 4⟩) (by decide) node_5345

theorem node_6994 : Outcome ⟨0, 12, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 8, 2⟩) (by decide) node_6078

theorem node_6995 : Outcome ⟨0, 12, 8, 8⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 8⟩) (by decide) node_3961

theorem node_6996 : Outcome ⟨0, 13, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 5, 4⟩) (by decide) node_5367

theorem node_6997 : Outcome ⟨0, 13, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 5, 4⟩) (by decide) node_5367

theorem node_6998 : Outcome ⟨0, 13, 7, 12⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 12⟩) (by decide) node_2854

theorem node_6999 : Outcome ⟨0, 13, 7, 14⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 12⟩) (by decide) node_2854

theorem node_7000 : Outcome ⟨0, 13, 7, 18⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 12⟩) (by decide) node_2854

theorem node_7001 : Outcome ⟨0, 14, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 6, 2⟩, ⟨0, 12, 6, 4⟩, ⟨0, 14, 5, 2⟩, ⟨0, 14, 4, 4⟩]
  exact AllWinning.cons node_6089 (AllWinning.cons node_5363 (AllWinning.cons node_6093 (AllWinning.cons node_5371 (AllWinning.nil))))

theorem node_7002 : Outcome ⟨0, 14, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 6, 2⟩, ⟨0, 12, 6, 4⟩, ⟨0, 11, 6, 6⟩, ⟨0, 10, 6, 8⟩, ⟨0, 14, 5, 2⟩, ⟨0, 14, 4, 4⟩, ⟨0, 14, 3, 6⟩, ⟨0, 14, 2, 8⟩]
  exact AllWinning.cons node_6089 (AllWinning.cons node_5363 (AllWinning.cons node_4617 (AllWinning.cons node_3975 (AllWinning.cons node_6093 (AllWinning.cons node_5371 (AllWinning.cons node_4631 (AllWinning.cons node_3992 (AllWinning.nil))))))))

theorem node_7003 : Outcome ⟨0, 14, 6, 6⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 10⟩) (by decide) node_3377

theorem node_7004 : Outcome ⟨0, 14, 6, 10⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 16⟩) (by decide) node_1896

theorem node_7005 : Outcome ⟨0, 14, 6, 16⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 16⟩) (by decide) node_1896

theorem node_7006 : Outcome ⟨0, 14, 6, 26⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 16⟩) (by decide) node_1896

theorem node_7007 : Outcome ⟨0, 15, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 6⟩) (by decide) node_4636

theorem node_7008 : Outcome ⟨0, 15, 5, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 6⟩) (by decide) node_4636

theorem node_7009 : Outcome ⟨0, 15, 5, 16⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 20⟩) (by decide) node_1180

theorem node_7010 : Outcome ⟨0, 15, 5, 20⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 20⟩) (by decide) node_1180

theorem node_7011 : Outcome ⟨0, 16, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 2⟩) (by decide) node_6100

theorem node_7012 : Outcome ⟨0, 16, 4, 8⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 2⟩) (by decide) node_6100

theorem node_7013 : Outcome ⟨0, 16, 4, 18⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 24⟩) (by decide) node_710

theorem node_7014 : Outcome ⟨0, 16, 4, 24⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 24⟩) (by decide) node_710

theorem node_7015 : Outcome ⟨0, 17, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 2⟩) (by decide) node_6100

theorem node_7016 : Outcome ⟨0, 17, 3, 28⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 28⟩) (by decide) node_350

theorem node_7017 : Outcome ⟨0, 18, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 6⟩) (by decide) node_4636

theorem node_7018 : Outcome ⟨0, 18, 2, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 6⟩) (by decide) node_4636

theorem node_7019 : Outcome ⟨0, 18, 2, 14⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 6⟩) (by decide) node_4636

theorem node_7020 : Outcome ⟨0, 18, 2, 32⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 32⟩) (by decide) node_155

theorem node_7021 : Outcome ⟨0, 19, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 1, 2⟩, ⟨0, 17, 1, 4⟩, ⟨0, 19, 0, 2⟩]
  exact AllWinning.cons node_6111 (AllWinning.cons node_5383 (AllWinning.cons node_6113 (AllWinning.nil)))

theorem node_7022 : Outcome ⟨0, 19, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 1, 2⟩, ⟨0, 17, 1, 4⟩, ⟨0, 16, 1, 6⟩, ⟨0, 15, 1, 8⟩, ⟨0, 19, 0, 2⟩]
  exact AllWinning.cons node_6111 (AllWinning.cons node_5383 (AllWinning.cons node_4643 (AllWinning.cons node_3996 (AllWinning.cons node_6113 (AllWinning.nil)))))

theorem node_7023 : Outcome ⟨0, 19, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 10⟩) (by decide) node_3377

theorem node_7024 : Outcome ⟨0, 19, 1, 10⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 10⟩) (by decide) node_3377

theorem node_7025 : Outcome ⟨0, 20, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 0, 4⟩) (by decide) node_5387

theorem node_7026 : Outcome ⟨0, 20, 0, 14⟩ true :=
  Outcome.win (q := ⟨0, 18, 0, 4⟩) (by decide) node_5387

theorem node_7027 : Outcome ⟨1, 0, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 19, 2⟩, ⟨1, 0, 18, 2⟩, ⟨1, 0, 17, 4⟩]
  exact AllWinning.cons node_6035 (AllWinning.cons node_6115 (AllWinning.cons node_5389 (AllWinning.nil)))

theorem node_7028 : Outcome ⟨1, 0, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 19, 2⟩, ⟨1, 0, 18, 2⟩, ⟨1, 0, 17, 4⟩, ⟨1, 0, 16, 6⟩, ⟨1, 0, 15, 8⟩]
  exact AllWinning.cons node_6035 (AllWinning.cons node_6115 (AllWinning.cons node_5389 (AllWinning.cons node_4650 (AllWinning.cons node_4003 (AllWinning.nil)))))

theorem node_7029 : Outcome ⟨1, 0, 19, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 10⟩) (by decide) node_3388

theorem node_7030 : Outcome ⟨1, 0, 19, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 10⟩) (by decide) node_3388

theorem node_7031 : Outcome ⟨1, 1, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 18, 2⟩, ⟨1, 0, 18, 2⟩, ⟨1, 1, 17, 2⟩, ⟨1, 1, 16, 4⟩]
  exact AllWinning.cons node_6037 (AllWinning.cons node_6115 (AllWinning.cons node_6117 (AllWinning.cons node_5393 (AllWinning.nil))))

theorem node_7032 : Outcome ⟨1, 1, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 18, 2⟩, ⟨1, 0, 18, 2⟩, ⟨1, 1, 17, 2⟩, ⟨1, 1, 16, 4⟩, ⟨1, 1, 15, 6⟩, ⟨1, 1, 14, 8⟩]
  exact AllWinning.cons node_6037 (AllWinning.cons node_6115 (AllWinning.cons node_6117 (AllWinning.cons node_5393 (AllWinning.cons node_4654 (AllWinning.cons node_4005 (AllWinning.nil))))))

theorem node_7033 : Outcome ⟨1, 2, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 17, 2⟩, ⟨1, 1, 17, 2⟩, ⟨1, 0, 17, 4⟩, ⟨1, 2, 16, 2⟩, ⟨1, 2, 15, 4⟩]
  exact AllWinning.cons node_6039 (AllWinning.cons node_6117 (AllWinning.cons node_5389 (AllWinning.cons node_6119 (AllWinning.cons node_5396 (AllWinning.nil)))))

theorem node_7034 : Outcome ⟨1, 2, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 17, 2⟩, ⟨1, 1, 17, 2⟩, ⟨1, 0, 17, 4⟩, ⟨1, 2, 16, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 2, 14, 6⟩, ⟨1, 2, 13, 8⟩]
  exact AllWinning.cons node_6039 (AllWinning.cons node_6117 (AllWinning.cons node_5389 (AllWinning.cons node_6119 (AllWinning.cons node_5396 (AllWinning.cons node_4657 (AllWinning.cons node_4008 (AllWinning.nil)))))))

theorem node_7035 : Outcome ⟨1, 2, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 17, 2⟩, ⟨1, 1, 17, 2⟩, ⟨1, 0, 17, 4⟩, ⟨1, 2, 16, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 2, 14, 6⟩, ⟨1, 2, 13, 8⟩, ⟨1, 2, 12, 10⟩, ⟨1, 2, 11, 12⟩]
  exact AllWinning.cons node_6039 (AllWinning.cons node_6117 (AllWinning.cons node_5389 (AllWinning.cons node_6119 (AllWinning.cons node_5396 (AllWinning.cons node_4657 (AllWinning.cons node_4008 (AllWinning.cons node_3401 (AllWinning.cons node_2897 (AllWinning.nil)))))))))

theorem node_7036 : Outcome ⟨1, 2, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 17, 2⟩, ⟨1, 1, 17, 2⟩, ⟨1, 0, 17, 4⟩, ⟨1, 2, 16, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 2, 14, 6⟩, ⟨1, 2, 13, 8⟩, ⟨1, 2, 12, 10⟩, ⟨1, 2, 11, 12⟩, ⟨1, 2, 10, 14⟩, ⟨1, 2, 9, 16⟩]
  exact AllWinning.cons node_6039 (AllWinning.cons node_6117 (AllWinning.cons node_5389 (AllWinning.cons node_6119 (AllWinning.cons node_5396 (AllWinning.cons node_4657 (AllWinning.cons node_4008 (AllWinning.cons node_3401 (AllWinning.cons node_2897 (AllWinning.cons node_2440 (AllWinning.cons node_1938 (AllWinning.nil)))))))))))

theorem node_7037 : Outcome ⟨1, 2, 17, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 17, 2⟩, ⟨1, 1, 17, 2⟩, ⟨1, 0, 17, 4⟩, ⟨1, 2, 16, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 2, 14, 6⟩, ⟨1, 2, 13, 8⟩, ⟨1, 2, 12, 10⟩, ⟨1, 2, 11, 12⟩, ⟨1, 2, 10, 14⟩, ⟨1, 2, 9, 16⟩, ⟨1, 2, 8, 18⟩, ⟨1, 2, 7, 20⟩, ⟨1, 2, 6, 22⟩, ⟨1, 2, 5, 24⟩]
  exact AllWinning.cons node_6039 (AllWinning.cons node_6117 (AllWinning.cons node_5389 (AllWinning.cons node_6119 (AllWinning.cons node_5396 (AllWinning.cons node_4657 (AllWinning.cons node_4008 (AllWinning.cons node_3401 (AllWinning.cons node_2897 (AllWinning.cons node_2440 (AllWinning.cons node_1938 (AllWinning.cons node_1604 (AllWinning.cons node_1218 (AllWinning.cons node_964 (AllWinning.cons node_745 (AllWinning.nil)))))))))))))))

theorem node_7038 : Outcome ⟨1, 2, 17, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 26⟩) (by decide) node_516

theorem node_7039 : Outcome ⟨1, 2, 17, 22⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 26⟩) (by decide) node_516

theorem node_7040 : Outcome ⟨1, 3, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 2⟩) (by decide) node_6042

theorem node_7041 : Outcome ⟨1, 3, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 2⟩) (by decide) node_6042

theorem node_7042 : Outcome ⟨1, 3, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 2⟩) (by decide) node_6042

theorem node_7043 : Outcome ⟨1, 3, 16, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 20⟩) (by decide) node_1228

theorem node_7044 : Outcome ⟨1, 3, 16, 24⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 20⟩) (by decide) node_1228

theorem node_7045 : Outcome ⟨1, 4, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 15, 2⟩, ⟨1, 3, 15, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 4, 14, 2⟩, ⟨1, 4, 13, 4⟩]
  exact AllWinning.cons node_6050 (AllWinning.cons node_6123 (AllWinning.cons node_5396 (AllWinning.cons node_6127 (AllWinning.cons node_5404 (AllWinning.nil)))))

theorem node_7046 : Outcome ⟨1, 4, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 15, 2⟩, ⟨1, 3, 15, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨1, 0, 15, 8⟩, ⟨1, 4, 14, 2⟩, ⟨1, 4, 13, 4⟩, ⟨1, 4, 12, 6⟩, ⟨1, 4, 11, 8⟩]
  exact AllWinning.cons node_6050 (AllWinning.cons node_6123 (AllWinning.cons node_5396 (AllWinning.cons node_4654 (AllWinning.cons node_4003 (AllWinning.cons node_6127 (AllWinning.cons node_5404 (AllWinning.cons node_4668 (AllWinning.cons node_4014 (AllWinning.nil)))))))))

theorem node_7047 : Outcome ⟨1, 4, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 15, 2⟩, ⟨1, 3, 15, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨1, 0, 15, 8⟩, ⟨1, 4, 14, 2⟩, ⟨1, 4, 13, 4⟩, ⟨1, 4, 12, 6⟩, ⟨1, 4, 11, 8⟩, ⟨1, 4, 10, 10⟩, ⟨1, 4, 9, 12⟩]
  exact AllWinning.cons node_6050 (AllWinning.cons node_6123 (AllWinning.cons node_5396 (AllWinning.cons node_4654 (AllWinning.cons node_4003 (AllWinning.cons node_6127 (AllWinning.cons node_5404 (AllWinning.cons node_4668 (AllWinning.cons node_4014 (AllWinning.cons node_3410 (AllWinning.cons node_2904 (AllWinning.nil)))))))))))

theorem node_7048 : Outcome ⟨1, 4, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 15, 2⟩, ⟨1, 3, 15, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨1, 0, 15, 8⟩, ⟨1, 4, 14, 2⟩, ⟨1, 4, 13, 4⟩, ⟨1, 4, 12, 6⟩, ⟨1, 4, 11, 8⟩, ⟨1, 4, 10, 10⟩, ⟨1, 4, 9, 12⟩, ⟨1, 4, 8, 14⟩, ⟨1, 4, 7, 16⟩]
  exact AllWinning.cons node_6050 (AllWinning.cons node_6123 (AllWinning.cons node_5396 (AllWinning.cons node_4654 (AllWinning.cons node_4003 (AllWinning.cons node_6127 (AllWinning.cons node_5404 (AllWinning.cons node_4668 (AllWinning.cons node_4014 (AllWinning.cons node_3410 (AllWinning.cons node_2904 (AllWinning.cons node_2449 (AllWinning.cons node_1951 (AllWinning.nil)))))))))))))

theorem node_7049 : Outcome ⟨1, 4, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 15, 2⟩, ⟨1, 3, 15, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨1, 0, 15, 8⟩, ⟨1, 4, 14, 2⟩, ⟨1, 4, 13, 4⟩, ⟨1, 4, 12, 6⟩, ⟨1, 4, 11, 8⟩, ⟨1, 4, 10, 10⟩, ⟨1, 4, 9, 12⟩, ⟨1, 4, 8, 14⟩, ⟨1, 4, 7, 16⟩, ⟨1, 4, 6, 18⟩, ⟨1, 4, 5, 20⟩]
  exact AllWinning.cons node_6050 (AllWinning.cons node_6123 (AllWinning.cons node_5396 (AllWinning.cons node_4654 (AllWinning.cons node_4003 (AllWinning.cons node_6127 (AllWinning.cons node_5404 (AllWinning.cons node_4668 (AllWinning.cons node_4014 (AllWinning.cons node_3410 (AllWinning.cons node_2904 (AllWinning.cons node_2449 (AllWinning.cons node_1951 (AllWinning.cons node_1612 (AllWinning.cons node_1240 (AllWinning.nil)))))))))))))))

theorem node_7050 : Outcome ⟨1, 4, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 15, 2⟩, ⟨1, 3, 15, 2⟩, ⟨1, 2, 15, 4⟩, ⟨1, 1, 15, 6⟩, ⟨1, 0, 15, 8⟩, ⟨1, 4, 14, 2⟩, ⟨1, 4, 13, 4⟩, ⟨1, 4, 12, 6⟩, ⟨1, 4, 11, 8⟩, ⟨1, 4, 10, 10⟩, ⟨1, 4, 9, 12⟩, ⟨1, 4, 8, 14⟩, ⟨1, 4, 7, 16⟩, ⟨1, 4, 6, 18⟩, ⟨1, 4, 5, 20⟩, ⟨1, 4, 4, 22⟩, ⟨1, 4, 3, 24⟩]
  exact AllWinning.cons node_6050 (AllWinning.cons node_6123 (AllWinning.cons node_5396 (AllWinning.cons node_4654 (AllWinning.cons node_4003 (AllWinning.cons node_6127 (AllWinning.cons node_5404 (AllWinning.cons node_4668 (AllWinning.cons node_4014 (AllWinning.cons node_3410 (AllWinning.cons node_2904 (AllWinning.cons node_2449 (AllWinning.cons node_1951 (AllWinning.cons node_1612 (AllWinning.cons node_1240 (AllWinning.cons node_974 (AllWinning.cons node_751 (AllWinning.nil)))))))))))))))))

theorem node_7051 : Outcome ⟨1, 4, 15, 24⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 26⟩) (by decide) node_537

theorem node_7052 : Outcome ⟨1, 5, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 14, 2⟩, ⟨1, 4, 14, 2⟩, ⟨1, 3, 14, 4⟩, ⟨1, 5, 13, 2⟩, ⟨1, 5, 12, 4⟩]
  exact AllWinning.cons node_6054 (AllWinning.cons node_6127 (AllWinning.cons node_5401 (AllWinning.cons node_6130 (AllWinning.cons node_5410 (AllWinning.nil)))))

theorem node_7053 : Outcome ⟨1, 5, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 14, 2⟩, ⟨1, 4, 14, 2⟩, ⟨1, 3, 14, 4⟩, ⟨1, 2, 14, 6⟩, ⟨1, 1, 14, 8⟩, ⟨1, 5, 13, 2⟩, ⟨1, 5, 12, 4⟩, ⟨1, 5, 11, 6⟩, ⟨1, 5, 10, 8⟩]
  exact AllWinning.cons node_6054 (AllWinning.cons node_6127 (AllWinning.cons node_5401 (AllWinning.cons node_4657 (AllWinning.cons node_4005 (AllWinning.cons node_6130 (AllWinning.cons node_5410 (AllWinning.cons node_4673 (AllWinning.cons node_4017 (AllWinning.nil)))))))))

theorem node_7054 : Outcome ⟨1, 5, 14, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 10⟩) (by decide) node_3388

theorem node_7055 : Outcome ⟨1, 5, 14, 16⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 10⟩) (by decide) node_3388

theorem node_7056 : Outcome ⟨1, 6, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 13, 2⟩, ⟨1, 5, 13, 2⟩, ⟨1, 4, 13, 4⟩, ⟨1, 3, 13, 6⟩, ⟨1, 2, 13, 8⟩, ⟨1, 6, 12, 2⟩, ⟨1, 6, 11, 4⟩, ⟨1, 6, 10, 6⟩, ⟨1, 6, 9, 8⟩]
  exact AllWinning.cons node_6057 (AllWinning.cons node_6130 (AllWinning.cons node_5404 (AllWinning.cons node_4662 (AllWinning.cons node_4008 (AllWinning.cons node_6133 (AllWinning.cons node_5413 (AllWinning.cons node_4674 (AllWinning.cons node_4020 (AllWinning.nil)))))))))

theorem node_7057 : Outcome ⟨1, 6, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 10⟩) (by decide) node_3396

theorem node_7058 : Outcome ⟨1, 6, 13, 22⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 20⟩) (by decide) node_1256

theorem node_7059 : Outcome ⟨1, 6, 13, 26⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 20⟩) (by decide) node_1256

theorem node_7060 : Outcome ⟨1, 7, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 12, 2⟩) (by decide) node_6062

theorem node_7061 : Outcome ⟨1, 7, 12, 12⟩ true :=
  Outcome.win (q := ⟨0, 7, 12, 2⟩) (by decide) node_6062

theorem node_7062 : Outcome ⟨1, 7, 12, 28⟩ true :=
  Outcome.win (q := ⟨0, 7, 12, 2⟩) (by decide) node_6062

theorem node_7063 : Outcome ⟨1, 8, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 11, 2⟩) (by decide) node_6069

theorem node_7064 : Outcome ⟨1, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 11, 2⟩) (by decide) node_6069

theorem node_7065 : Outcome ⟨1, 8, 11, 18⟩ true :=
  Outcome.win (q := ⟨0, 8, 11, 2⟩) (by decide) node_6069

theorem node_7066 : Outcome ⟨1, 9, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨1, 8, 10, 2⟩, ⟨1, 7, 10, 4⟩, ⟨1, 9, 9, 2⟩, ⟨1, 9, 8, 4⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_6149 (AllWinning.cons node_5416 (AllWinning.cons node_6154 (AllWinning.cons node_5423 (AllWinning.nil)))))

theorem node_7067 : Outcome ⟨1, 9, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 10, 2⟩, ⟨1, 8, 10, 2⟩, ⟨1, 7, 10, 4⟩, ⟨1, 6, 10, 6⟩, ⟨1, 5, 10, 8⟩, ⟨1, 9, 9, 2⟩, ⟨1, 9, 8, 4⟩, ⟨1, 9, 7, 6⟩, ⟨1, 9, 6, 8⟩]
  exact AllWinning.cons node_6073 (AllWinning.cons node_6149 (AllWinning.cons node_5416 (AllWinning.cons node_4674 (AllWinning.cons node_4017 (AllWinning.cons node_6154 (AllWinning.cons node_5423 (AllWinning.cons node_4687 (AllWinning.cons node_4031 (AllWinning.nil)))))))))

theorem node_7068 : Outcome ⟨1, 9, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 10⟩) (by decide) node_3440

theorem node_7069 : Outcome ⟨1, 9, 10, 10⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 10⟩) (by decide) node_3440

theorem node_7070 : Outcome ⟨1, 10, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 9, 2⟩, ⟨1, 9, 9, 2⟩, ⟨1, 8, 9, 4⟩, ⟨1, 10, 8, 2⟩, ⟨1, 10, 7, 4⟩]
  exact AllWinning.cons node_6075 (AllWinning.cons node_6154 (AllWinning.cons node_5419 (AllWinning.cons node_6157 (AllWinning.cons node_5427 (AllWinning.nil)))))

theorem node_7071 : Outcome ⟨1, 10, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 9, 2⟩, ⟨1, 9, 9, 2⟩, ⟨1, 8, 9, 4⟩, ⟨1, 7, 9, 6⟩, ⟨1, 6, 9, 8⟩, ⟨1, 10, 8, 2⟩, ⟨1, 10, 7, 4⟩, ⟨1, 10, 6, 6⟩, ⟨1, 10, 5, 8⟩]
  exact AllWinning.cons node_6075 (AllWinning.cons node_6154 (AllWinning.cons node_5419 (AllWinning.cons node_4679 (AllWinning.cons node_4020 (AllWinning.cons node_6157 (AllWinning.cons node_5427 (AllWinning.cons node_4690 (AllWinning.cons node_4035 (AllWinning.nil)))))))))

theorem node_7072 : Outcome ⟨1, 10, 9, 6⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 10⟩) (by decide) node_3416

theorem node_7073 : Outcome ⟨1, 10, 9, 10⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 10⟩) (by decide) node_3416

theorem node_7074 : Outcome ⟨1, 11, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 8, 2⟩) (by decide) node_6078

theorem node_7075 : Outcome ⟨1, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 8, 2⟩) (by decide) node_6078

theorem node_7076 : Outcome ⟨1, 11, 8, 18⟩ true :=
  Outcome.win (q := ⟨0, 11, 8, 2⟩) (by decide) node_6078

theorem node_7077 : Outcome ⟨1, 12, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 7, 2⟩) (by decide) node_6082

theorem node_7078 : Outcome ⟨1, 12, 7, 12⟩ true :=
  Outcome.win (q := ⟨0, 12, 7, 2⟩) (by decide) node_6082

theorem node_7079 : Outcome ⟨1, 12, 7, 28⟩ true :=
  Outcome.win (q := ⟨0, 12, 7, 2⟩) (by decide) node_6082

theorem node_7080 : Outcome ⟨1, 13, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 6, 2⟩, ⟨1, 12, 6, 2⟩, ⟨1, 11, 6, 4⟩, ⟨1, 10, 6, 6⟩, ⟨1, 9, 6, 8⟩, ⟨1, 13, 5, 2⟩, ⟨1, 13, 4, 4⟩, ⟨1, 13, 3, 6⟩, ⟨1, 13, 2, 8⟩]
  exact AllWinning.cons node_6089 (AllWinning.cons node_6174 (AllWinning.cons node_5430 (AllWinning.cons node_4690 (AllWinning.cons node_4031 (AllWinning.cons node_6178 (AllWinning.cons node_5436 (AllWinning.cons node_4703 (AllWinning.cons node_4046 (AllWinning.nil)))))))))

theorem node_7081 : Outcome ⟨1, 13, 6, 6⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 10⟩) (by decide) node_3468

theorem node_7082 : Outcome ⟨1, 13, 6, 22⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 20⟩) (by decide) node_1228

theorem node_7083 : Outcome ⟨1, 14, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 5, 2⟩, ⟨1, 13, 5, 2⟩, ⟨1, 12, 5, 4⟩, ⟨1, 14, 4, 2⟩, ⟨1, 14, 3, 4⟩]
  exact AllWinning.cons node_6093 (AllWinning.cons node_6178 (AllWinning.cons node_5433 (AllWinning.cons node_6181 (AllWinning.cons node_5442 (AllWinning.nil)))))

theorem node_7084 : Outcome ⟨1, 14, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 5, 2⟩, ⟨1, 13, 5, 2⟩, ⟨1, 12, 5, 4⟩, ⟨1, 11, 5, 6⟩, ⟨1, 10, 5, 8⟩, ⟨1, 14, 4, 2⟩, ⟨1, 14, 3, 4⟩, ⟨1, 14, 2, 6⟩, ⟨1, 14, 1, 8⟩]
  exact AllWinning.cons node_6093 (AllWinning.cons node_6178 (AllWinning.cons node_5433 (AllWinning.cons node_4695 (AllWinning.cons node_4035 (AllWinning.cons node_6181 (AllWinning.cons node_5442 (AllWinning.cons node_4708 (AllWinning.cons node_4048 (AllWinning.nil)))))))))

theorem node_7085 : Outcome ⟨1, 14, 5, 10⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 10⟩) (by decide) node_3440

theorem node_7086 : Outcome ⟨1, 14, 5, 16⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 10⟩) (by decide) node_3440

theorem node_7087 : Outcome ⟨1, 15, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 4, 2⟩, ⟨1, 14, 4, 2⟩, ⟨1, 13, 4, 4⟩, ⟨1, 15, 3, 2⟩, ⟨1, 15, 2, 4⟩]
  exact AllWinning.cons node_6096 (AllWinning.cons node_6181 (AllWinning.cons node_5436 (AllWinning.cons node_6184 (AllWinning.cons node_5445 (AllWinning.nil)))))

theorem node_7088 : Outcome ⟨1, 15, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 4, 2⟩, ⟨1, 14, 4, 2⟩, ⟨1, 13, 4, 4⟩, ⟨1, 12, 4, 6⟩, ⟨1, 11, 4, 8⟩, ⟨1, 15, 3, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 15, 1, 6⟩, ⟨1, 15, 0, 8⟩]
  exact AllWinning.cons node_6096 (AllWinning.cons node_6181 (AllWinning.cons node_5436 (AllWinning.cons node_4698 (AllWinning.cons node_4039 (AllWinning.cons node_6184 (AllWinning.cons node_5445 (AllWinning.cons node_4712 (AllWinning.cons node_4051 (AllWinning.nil)))))))))

theorem node_7089 : Outcome ⟨1, 15, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 4, 2⟩, ⟨1, 14, 4, 2⟩, ⟨1, 13, 4, 4⟩, ⟨1, 12, 4, 6⟩, ⟨1, 11, 4, 8⟩, ⟨1, 10, 4, 10⟩, ⟨1, 9, 4, 12⟩, ⟨1, 15, 3, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 15, 1, 6⟩, ⟨1, 15, 0, 8⟩]
  exact AllWinning.cons node_6096 (AllWinning.cons node_6181 (AllWinning.cons node_5436 (AllWinning.cons node_4698 (AllWinning.cons node_4039 (AllWinning.cons node_3453 (AllWinning.cons node_2923 (AllWinning.cons node_6184 (AllWinning.cons node_5445 (AllWinning.cons node_4712 (AllWinning.cons node_4051 (AllWinning.nil)))))))))))

theorem node_7090 : Outcome ⟨1, 15, 4, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 4, 2⟩, ⟨1, 14, 4, 2⟩, ⟨1, 13, 4, 4⟩, ⟨1, 12, 4, 6⟩, ⟨1, 11, 4, 8⟩, ⟨1, 10, 4, 10⟩, ⟨1, 9, 4, 12⟩, ⟨1, 8, 4, 14⟩, ⟨1, 7, 4, 16⟩, ⟨1, 15, 3, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 15, 1, 6⟩, ⟨1, 15, 0, 8⟩]
  exact AllWinning.cons node_6096 (AllWinning.cons node_6181 (AllWinning.cons node_5436 (AllWinning.cons node_4698 (AllWinning.cons node_4039 (AllWinning.cons node_3453 (AllWinning.cons node_2923 (AllWinning.cons node_2461 (AllWinning.cons node_1963 (AllWinning.cons node_6184 (AllWinning.cons node_5445 (AllWinning.cons node_4712 (AllWinning.cons node_4051 (AllWinning.nil)))))))))))))

theorem node_7091 : Outcome ⟨1, 15, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 4, 2⟩, ⟨1, 14, 4, 2⟩, ⟨1, 13, 4, 4⟩, ⟨1, 12, 4, 6⟩, ⟨1, 11, 4, 8⟩, ⟨1, 10, 4, 10⟩, ⟨1, 9, 4, 12⟩, ⟨1, 8, 4, 14⟩, ⟨1, 7, 4, 16⟩, ⟨1, 6, 4, 18⟩, ⟨1, 5, 4, 20⟩, ⟨1, 15, 3, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 15, 1, 6⟩, ⟨1, 15, 0, 8⟩]
  exact AllWinning.cons node_6096 (AllWinning.cons node_6181 (AllWinning.cons node_5436 (AllWinning.cons node_4698 (AllWinning.cons node_4039 (AllWinning.cons node_3453 (AllWinning.cons node_2923 (AllWinning.cons node_2461 (AllWinning.cons node_1963 (AllWinning.cons node_1618 (AllWinning.cons node_1246 (AllWinning.cons node_6184 (AllWinning.cons node_5445 (AllWinning.cons node_4712 (AllWinning.cons node_4051 (AllWinning.nil)))))))))))))))

theorem node_7092 : Outcome ⟨1, 15, 4, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 4, 2⟩, ⟨1, 14, 4, 2⟩, ⟨1, 13, 4, 4⟩, ⟨1, 12, 4, 6⟩, ⟨1, 11, 4, 8⟩, ⟨1, 10, 4, 10⟩, ⟨1, 9, 4, 12⟩, ⟨1, 8, 4, 14⟩, ⟨1, 7, 4, 16⟩, ⟨1, 6, 4, 18⟩, ⟨1, 5, 4, 20⟩, ⟨1, 4, 4, 22⟩, ⟨1, 3, 4, 24⟩, ⟨1, 15, 3, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 15, 1, 6⟩, ⟨1, 15, 0, 8⟩]
  exact AllWinning.cons node_6096 (AllWinning.cons node_6181 (AllWinning.cons node_5436 (AllWinning.cons node_4698 (AllWinning.cons node_4039 (AllWinning.cons node_3453 (AllWinning.cons node_2923 (AllWinning.cons node_2461 (AllWinning.cons node_1963 (AllWinning.cons node_1618 (AllWinning.cons node_1246 (AllWinning.cons node_974 (AllWinning.cons node_748 (AllWinning.cons node_6184 (AllWinning.cons node_5445 (AllWinning.cons node_4712 (AllWinning.cons node_4051 (AllWinning.nil)))))))))))))))))

theorem node_7093 : Outcome ⟨1, 15, 4, 24⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 26⟩) (by decide) node_516

theorem node_7094 : Outcome ⟨1, 16, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 2⟩) (by decide) node_6100

theorem node_7095 : Outcome ⟨1, 16, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 2⟩) (by decide) node_6100

theorem node_7096 : Outcome ⟨1, 16, 3, 8⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 2⟩) (by decide) node_6100

theorem node_7097 : Outcome ⟨1, 16, 3, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 20⟩) (by decide) node_1256

theorem node_7098 : Outcome ⟨1, 16, 3, 24⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 20⟩) (by decide) node_1256

theorem node_7099 : Outcome ⟨1, 17, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 2, 2⟩, ⟨1, 16, 2, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 17, 1, 2⟩, ⟨1, 17, 0, 4⟩]
  exact AllWinning.cons node_6108 (AllWinning.cons node_6188 (AllWinning.cons node_5445 (AllWinning.cons node_6192 (AllWinning.cons node_5453 (AllWinning.nil)))))

theorem node_7100 : Outcome ⟨1, 17, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 2, 2⟩, ⟨1, 16, 2, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 14, 2, 6⟩, ⟨1, 13, 2, 8⟩, ⟨1, 17, 1, 2⟩, ⟨1, 17, 0, 4⟩]
  exact AllWinning.cons node_6108 (AllWinning.cons node_6188 (AllWinning.cons node_5445 (AllWinning.cons node_4708 (AllWinning.cons node_4046 (AllWinning.cons node_6192 (AllWinning.cons node_5453 (AllWinning.nil)))))))

theorem node_7101 : Outcome ⟨1, 17, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 2, 2⟩, ⟨1, 16, 2, 2⟩, ⟨1, 15, 2, 4⟩, ⟨1, 14, 2, 6⟩, ⟨1, 13, 2, 8⟩, ⟨1, 12, 2, 10⟩, ⟨1, 11, 2, 12⟩, ⟨1, 17, 1, 2⟩, ⟨1, 17, 0, 4⟩]
  exact AllWinning.cons node_6108 (AllWinning.cons node_6188 (AllWinning.cons node_5445 (AllWinning.cons node_4708 (AllWinning.cons node_4046 (AllWinning.cons node_3461 (AllWinning.cons node_2932 (AllWinning.cons node_6192 (AllWinning.cons node_5453 (AllWinning.nil)))))))))

end RQ9F1
