import Chunk23
set_option autoImplicit false
namespace RQ9F1

theorem node_5998 : Outcome ⟨15, 0, 3, 8⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 2⟩) (by decide) node_5281

theorem node_5999 : Outcome ⟨15, 0, 3, 14⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 24⟩) (by decide) node_414

theorem node_6000 : Outcome ⟨15, 0, 3, 24⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 24⟩) (by decide) node_414

theorem node_6001 : Outcome ⟨15, 1, 2, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 2, 6⟩) (by decide) node_3885

theorem node_6002 : Outcome ⟨15, 1, 2, 8⟩ true :=
  Outcome.win (q := ⟨12, 1, 2, 6⟩) (by decide) node_3885

theorem node_6003 : Outcome ⟨15, 1, 2, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 22⟩) (by decide) node_626

theorem node_6004 : Outcome ⟨15, 1, 2, 28⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 22⟩) (by decide) node_626

theorem node_6005 : Outcome ⟨15, 2, 1, 4⟩ true :=
  Outcome.win (q := ⟨12, 2, 1, 6⟩) (by decide) node_3891

theorem node_6006 : Outcome ⟨15, 2, 1, 8⟩ true :=
  Outcome.win (q := ⟨12, 2, 1, 6⟩) (by decide) node_3891

theorem node_6007 : Outcome ⟨15, 2, 1, 16⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 22⟩) (by decide) node_644

theorem node_6008 : Outcome ⟨15, 2, 1, 28⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 22⟩) (by decide) node_644

theorem node_6009 : Outcome ⟨15, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 2⟩) (by decide) node_5291

theorem node_6010 : Outcome ⟨15, 3, 0, 8⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 2⟩) (by decide) node_5291

theorem node_6011 : Outcome ⟨15, 3, 0, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 24⟩) (by decide) node_437

theorem node_6012 : Outcome ⟨15, 3, 0, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 24⟩) (by decide) node_437

theorem node_6013 : Outcome ⟨16, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 2⟩) (by decide) node_5281

theorem node_6014 : Outcome ⟨16, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 2⟩) (by decide) node_5281

theorem node_6015 : Outcome ⟨16, 0, 2, 20⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 28⟩) (by decide) node_196

theorem node_6016 : Outcome ⟨16, 0, 2, 28⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 28⟩) (by decide) node_196

theorem node_6017 : Outcome ⟨16, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 1, 2⟩, ⟨14, 1, 1, 4⟩, ⟨16, 0, 1, 2⟩, ⟨16, 1, 0, 2⟩]
  exact AllWinning.cons node_5288 (AllWinning.cons node_4550 (AllWinning.cons node_5298 (AllWinning.cons node_5303 (AllWinning.nil))))

theorem node_6018 : Outcome ⟨16, 1, 1, 4⟩ true :=
  Outcome.win (q := ⟨13, 1, 1, 6⟩) (by decide) node_3903

theorem node_6019 : Outcome ⟨16, 1, 1, 10⟩ true :=
  Outcome.win (q := ⟨13, 1, 1, 6⟩) (by decide) node_3903

theorem node_6020 : Outcome ⟨16, 1, 1, 28⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 32⟩) (by decide) node_47

theorem node_6021 : Outcome ⟨16, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 2⟩) (by decide) node_5291

theorem node_6022 : Outcome ⟨16, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 2⟩) (by decide) node_5291

theorem node_6023 : Outcome ⟨16, 2, 0, 20⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 28⟩) (by decide) node_217

theorem node_6024 : Outcome ⟨16, 2, 0, 28⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 28⟩) (by decide) node_217

theorem node_6025 : Outcome ⟨17, 0, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 0, 1, 2⟩, ⟨15, 0, 1, 4⟩, ⟨17, 0, 0, 2⟩]
  exact AllWinning.cons node_5298 (AllWinning.cons node_4557 (AllWinning.cons node_5308 (AllWinning.nil)))

theorem node_6026 : Outcome ⟨17, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 6⟩) (by decide) node_3911

theorem node_6027 : Outcome ⟨17, 0, 1, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 6⟩) (by decide) node_3911

theorem node_6028 : Outcome ⟨17, 0, 1, 26⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 32⟩) (by decide) node_69

theorem node_6029 : Outcome ⟨17, 1, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 1, 0, 2⟩, ⟨15, 1, 0, 4⟩, ⟨17, 0, 0, 2⟩]
  exact AllWinning.cons node_5303 (AllWinning.cons node_4561 (AllWinning.cons node_5308 (AllWinning.nil)))

theorem node_6030 : Outcome ⟨17, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 6⟩) (by decide) node_3919

theorem node_6031 : Outcome ⟨17, 1, 0, 6⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 6⟩) (by decide) node_3919

theorem node_6032 : Outcome ⟨17, 1, 0, 26⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 32⟩) (by decide) node_86

theorem node_6033 : Outcome ⟨18, 0, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 0, 0, 2⟩, ⟨16, 0, 0, 4⟩]
  exact AllWinning.cons node_5308 (AllWinning.cons node_4565 (AllWinning.nil))

theorem node_6034 : Outcome ⟨18, 0, 0, 10⟩ true :=
  Outcome.win (q := ⟨13, 0, 0, 10⟩) (by decide) node_2818

theorem node_6035 : Outcome ⟨0, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 18, 2⟩) (by decide) node_5310

theorem node_6036 : Outcome ⟨0, 0, 19, 12⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 12⟩) (by decide) node_2365

theorem node_6037 : Outcome ⟨0, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 18, 2⟩) (by decide) node_5310

theorem node_6038 : Outcome ⟨0, 1, 18, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 8⟩) (by decide) node_3324

theorem node_6039 : Outcome ⟨0, 2, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 4⟩) (by decide) node_4576

theorem node_6040 : Outcome ⟨0, 2, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 4⟩) (by decide) node_4576

theorem node_6041 : Outcome ⟨0, 2, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 4⟩) (by decide) node_4576

theorem node_6042 : Outcome ⟨0, 3, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 16, 2⟩, ⟨0, 1, 16, 4⟩, ⟨0, 3, 15, 2⟩, ⟨0, 3, 14, 4⟩]
  exact AllWinning.cons node_5317 (AllWinning.cons node_4571 (AllWinning.cons node_5321 (AllWinning.cons node_4583 (AllWinning.nil))))

theorem node_6043 : Outcome ⟨0, 3, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 16, 2⟩, ⟨0, 1, 16, 4⟩, ⟨0, 0, 16, 6⟩, ⟨0, 3, 15, 2⟩, ⟨0, 3, 14, 4⟩, ⟨0, 3, 13, 6⟩, ⟨0, 3, 12, 8⟩]
  exact AllWinning.cons node_5317 (AllWinning.cons node_4571 (AllWinning.cons node_3929 (AllWinning.cons node_5321 (AllWinning.cons node_4583 (AllWinning.cons node_3939 (AllWinning.cons node_3333 (AllWinning.nil)))))))

theorem node_6044 : Outcome ⟨0, 3, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 16, 2⟩, ⟨0, 1, 16, 4⟩, ⟨0, 0, 16, 6⟩, ⟨0, 3, 15, 2⟩, ⟨0, 3, 14, 4⟩, ⟨0, 3, 13, 6⟩, ⟨0, 3, 12, 8⟩, ⟨0, 3, 11, 10⟩, ⟨0, 3, 10, 12⟩]
  exact AllWinning.cons node_5317 (AllWinning.cons node_4571 (AllWinning.cons node_3929 (AllWinning.cons node_5321 (AllWinning.cons node_4583 (AllWinning.cons node_3939 (AllWinning.cons node_3333 (AllWinning.cons node_2837 (AllWinning.cons node_2378 (AllWinning.nil)))))))))

theorem node_6045 : Outcome ⟨0, 3, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 16, 2⟩, ⟨0, 1, 16, 4⟩, ⟨0, 0, 16, 6⟩, ⟨0, 3, 15, 2⟩, ⟨0, 3, 14, 4⟩, ⟨0, 3, 13, 6⟩, ⟨0, 3, 12, 8⟩, ⟨0, 3, 11, 10⟩, ⟨0, 3, 10, 12⟩, ⟨0, 3, 9, 14⟩, ⟨0, 3, 8, 16⟩]
  exact AllWinning.cons node_5317 (AllWinning.cons node_4571 (AllWinning.cons node_3929 (AllWinning.cons node_5321 (AllWinning.cons node_4583 (AllWinning.cons node_3939 (AllWinning.cons node_3333 (AllWinning.cons node_2837 (AllWinning.cons node_2378 (AllWinning.cons node_1880 (AllWinning.cons node_1559 (AllWinning.nil)))))))))))

theorem node_6046 : Outcome ⟨0, 3, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 16, 2⟩, ⟨0, 1, 16, 4⟩, ⟨0, 0, 16, 6⟩, ⟨0, 3, 15, 2⟩, ⟨0, 3, 14, 4⟩, ⟨0, 3, 13, 6⟩, ⟨0, 3, 12, 8⟩, ⟨0, 3, 11, 10⟩, ⟨0, 3, 10, 12⟩, ⟨0, 3, 9, 14⟩, ⟨0, 3, 8, 16⟩, ⟨0, 3, 7, 18⟩, ⟨0, 3, 6, 20⟩]
  exact AllWinning.cons node_5317 (AllWinning.cons node_4571 (AllWinning.cons node_3929 (AllWinning.cons node_5321 (AllWinning.cons node_4583 (AllWinning.cons node_3939 (AllWinning.cons node_3333 (AllWinning.cons node_2837 (AllWinning.cons node_2378 (AllWinning.cons node_1880 (AllWinning.cons node_1559 (AllWinning.cons node_1167 (AllWinning.cons node_925 (AllWinning.nil)))))))))))))

theorem node_6047 : Outcome ⟨0, 3, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 16, 2⟩, ⟨0, 1, 16, 4⟩, ⟨0, 0, 16, 6⟩, ⟨0, 3, 15, 2⟩, ⟨0, 3, 14, 4⟩, ⟨0, 3, 13, 6⟩, ⟨0, 3, 12, 8⟩, ⟨0, 3, 11, 10⟩, ⟨0, 3, 10, 12⟩, ⟨0, 3, 9, 14⟩, ⟨0, 3, 8, 16⟩, ⟨0, 3, 7, 18⟩, ⟨0, 3, 6, 20⟩, ⟨0, 3, 5, 22⟩, ⟨0, 3, 4, 24⟩]
  exact AllWinning.cons node_5317 (AllWinning.cons node_4571 (AllWinning.cons node_3929 (AllWinning.cons node_5321 (AllWinning.cons node_4583 (AllWinning.cons node_3939 (AllWinning.cons node_3333 (AllWinning.cons node_2837 (AllWinning.cons node_2378 (AllWinning.cons node_1880 (AllWinning.cons node_1559 (AllWinning.cons node_1167 (AllWinning.cons node_925 (AllWinning.cons node_698 (AllWinning.cons node_480 (AllWinning.nil)))))))))))))))

theorem node_6048 : Outcome ⟨0, 3, 16, 16⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 26⟩) (by decide) node_349

theorem node_6049 : Outcome ⟨0, 3, 16, 26⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 26⟩) (by decide) node_349

theorem node_6050 : Outcome ⟨0, 4, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 4⟩) (by decide) node_4576

theorem node_6051 : Outcome ⟨0, 4, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 12, 6⟩) (by decide) node_3943

theorem node_6052 : Outcome ⟨0, 4, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 12, 6⟩) (by decide) node_3943

theorem node_6053 : Outcome ⟨0, 4, 15, 22⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 22⟩) (by decide) node_709

theorem node_6054 : Outcome ⟨0, 5, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 13, 2⟩) (by decide) node_5328

theorem node_6055 : Outcome ⟨0, 5, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 8⟩) (by decide) node_3324

theorem node_6056 : Outcome ⟨0, 5, 14, 18⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 18⟩) (by decide) node_1179

theorem node_6057 : Outcome ⟨0, 6, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 13, 2⟩) (by decide) node_5328

theorem node_6058 : Outcome ⟨0, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 13, 2⟩) (by decide) node_5328

theorem node_6059 : Outcome ⟨0, 6, 13, 12⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 14⟩) (by decide) node_1895

theorem node_6060 : Outcome ⟨0, 6, 13, 14⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 14⟩) (by decide) node_1895

theorem node_6061 : Outcome ⟨0, 6, 13, 28⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 14⟩) (by decide) node_1895

theorem node_6062 : Outcome ⟨0, 7, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 12, 2⟩, ⟨0, 5, 12, 4⟩, ⟨0, 7, 11, 2⟩, ⟨0, 7, 10, 4⟩]
  exact AllWinning.cons node_5333 (AllWinning.cons node_4592 (AllWinning.cons node_5337 (AllWinning.cons node_4602 (AllWinning.nil))))

theorem node_6063 : Outcome ⟨0, 7, 12, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 12, 6⟩) (by decide) node_3943

theorem node_6064 : Outcome ⟨0, 7, 12, 6⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6065 : Outcome ⟨0, 7, 12, 10⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6066 : Outcome ⟨0, 7, 12, 14⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6067 : Outcome ⟨0, 7, 12, 16⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6068 : Outcome ⟨0, 7, 12, 30⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6069 : Outcome ⟨0, 8, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨0, 6, 11, 4⟩, ⟨0, 8, 10, 2⟩, ⟨0, 8, 9, 4⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_4597 (AllWinning.cons node_5340 (AllWinning.cons node_4606 (AllWinning.nil))))

theorem node_6070 : Outcome ⟨0, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 6⟩) (by decide) node_3960

theorem node_6071 : Outcome ⟨0, 8, 11, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 6⟩) (by decide) node_3960

theorem node_6072 : Outcome ⟨0, 8, 11, 20⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 6⟩) (by decide) node_3960

theorem node_6073 : Outcome ⟨0, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 2⟩) (by decide) node_5344

theorem node_6074 : Outcome ⟨0, 9, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 2⟩) (by decide) node_5344

theorem node_6075 : Outcome ⟨0, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 2⟩) (by decide) node_5344

theorem node_6076 : Outcome ⟨0, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 2⟩) (by decide) node_5344

theorem node_6077 : Outcome ⟨0, 10, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 2⟩) (by decide) node_5344

theorem node_6078 : Outcome ⟨0, 11, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 8, 2⟩, ⟨0, 9, 8, 4⟩, ⟨0, 11, 7, 2⟩, ⟨0, 11, 6, 4⟩]
  exact AllWinning.cons node_5355 (AllWinning.cons node_4609 (AllWinning.cons node_5359 (AllWinning.cons node_4616 (AllWinning.nil))))

theorem node_6079 : Outcome ⟨0, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 6⟩) (by decide) node_3960

theorem node_6080 : Outcome ⟨0, 11, 8, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 6⟩) (by decide) node_3960

theorem node_6081 : Outcome ⟨0, 11, 8, 20⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 6⟩) (by decide) node_3960

theorem node_6082 : Outcome ⟨0, 12, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨0, 10, 7, 4⟩, ⟨0, 12, 6, 2⟩, ⟨0, 12, 5, 4⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_4612 (AllWinning.cons node_5362 (AllWinning.cons node_4621 (AllWinning.nil))))

theorem node_6083 : Outcome ⟨0, 12, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 12, 4, 6⟩) (by decide) node_3984

theorem node_6084 : Outcome ⟨0, 12, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6085 : Outcome ⟨0, 12, 7, 10⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6086 : Outcome ⟨0, 12, 7, 14⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6087 : Outcome ⟨0, 12, 7, 16⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6088 : Outcome ⟨0, 12, 7, 30⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6089 : Outcome ⟨0, 13, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 5, 2⟩) (by decide) node_5366

theorem node_6090 : Outcome ⟨0, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 5, 2⟩) (by decide) node_5366

theorem node_6091 : Outcome ⟨0, 13, 6, 12⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 14⟩) (by decide) node_1895

theorem node_6092 : Outcome ⟨0, 13, 6, 14⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 14⟩) (by decide) node_1895

theorem node_6093 : Outcome ⟨0, 14, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 5, 2⟩) (by decide) node_5366

theorem node_6094 : Outcome ⟨0, 14, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 8⟩) (by decide) node_3376

theorem node_6095 : Outcome ⟨0, 14, 5, 18⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 18⟩) (by decide) node_1179

theorem node_6096 : Outcome ⟨0, 15, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 4⟩) (by decide) node_4635

theorem node_6097 : Outcome ⟨0, 15, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 12, 4, 6⟩) (by decide) node_3984

theorem node_6098 : Outcome ⟨0, 15, 4, 6⟩ true :=
  Outcome.win (q := ⟨0, 12, 4, 6⟩) (by decide) node_3984

theorem node_6099 : Outcome ⟨0, 15, 4, 22⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 22⟩) (by decide) node_709

theorem node_6100 : Outcome ⟨0, 16, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 3, 2⟩, ⟨0, 14, 3, 4⟩, ⟨0, 16, 2, 2⟩, ⟨0, 16, 1, 4⟩]
  exact AllWinning.cons node_5374 (AllWinning.cons node_4630 (AllWinning.cons node_5378 (AllWinning.cons node_4642 (AllWinning.nil))))

theorem node_6101 : Outcome ⟨0, 16, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 3, 2⟩, ⟨0, 14, 3, 4⟩, ⟨0, 13, 3, 6⟩, ⟨0, 12, 3, 8⟩, ⟨0, 16, 2, 2⟩, ⟨0, 16, 1, 4⟩, ⟨0, 16, 0, 6⟩]
  exact AllWinning.cons node_5374 (AllWinning.cons node_4630 (AllWinning.cons node_3989 (AllWinning.cons node_3368 (AllWinning.cons node_5378 (AllWinning.cons node_4642 (AllWinning.cons node_4000 (AllWinning.nil)))))))

theorem node_6102 : Outcome ⟨0, 16, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 3, 2⟩, ⟨0, 14, 3, 4⟩, ⟨0, 13, 3, 6⟩, ⟨0, 12, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨0, 10, 3, 12⟩, ⟨0, 16, 2, 2⟩, ⟨0, 16, 1, 4⟩, ⟨0, 16, 0, 6⟩]
  exact AllWinning.cons node_5374 (AllWinning.cons node_4630 (AllWinning.cons node_3989 (AllWinning.cons node_3368 (AllWinning.cons node_2875 (AllWinning.cons node_2412 (AllWinning.cons node_5378 (AllWinning.cons node_4642 (AllWinning.cons node_4000 (AllWinning.nil)))))))))

theorem node_6103 : Outcome ⟨0, 16, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 3, 2⟩, ⟨0, 14, 3, 4⟩, ⟨0, 13, 3, 6⟩, ⟨0, 12, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨0, 10, 3, 12⟩, ⟨0, 9, 3, 14⟩, ⟨0, 8, 3, 16⟩, ⟨0, 16, 2, 2⟩, ⟨0, 16, 1, 4⟩, ⟨0, 16, 0, 6⟩]
  exact AllWinning.cons node_5374 (AllWinning.cons node_4630 (AllWinning.cons node_3989 (AllWinning.cons node_3368 (AllWinning.cons node_2875 (AllWinning.cons node_2412 (AllWinning.cons node_1913 (AllWinning.cons node_1580 (AllWinning.cons node_5378 (AllWinning.cons node_4642 (AllWinning.cons node_4000 (AllWinning.nil)))))))))))

theorem node_6104 : Outcome ⟨0, 16, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 3, 2⟩, ⟨0, 14, 3, 4⟩, ⟨0, 13, 3, 6⟩, ⟨0, 12, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨0, 10, 3, 12⟩, ⟨0, 9, 3, 14⟩, ⟨0, 8, 3, 16⟩, ⟨0, 7, 3, 18⟩, ⟨0, 6, 3, 20⟩, ⟨0, 16, 2, 2⟩, ⟨0, 16, 1, 4⟩, ⟨0, 16, 0, 6⟩]
  exact AllWinning.cons node_5374 (AllWinning.cons node_4630 (AllWinning.cons node_3989 (AllWinning.cons node_3368 (AllWinning.cons node_2875 (AllWinning.cons node_2412 (AllWinning.cons node_1913 (AllWinning.cons node_1580 (AllWinning.cons node_1191 (AllWinning.cons node_936 (AllWinning.cons node_5378 (AllWinning.cons node_4642 (AllWinning.cons node_4000 (AllWinning.nil)))))))))))))

theorem node_6105 : Outcome ⟨0, 16, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 3, 2⟩, ⟨0, 14, 3, 4⟩, ⟨0, 13, 3, 6⟩, ⟨0, 12, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨0, 10, 3, 12⟩, ⟨0, 9, 3, 14⟩, ⟨0, 8, 3, 16⟩, ⟨0, 7, 3, 18⟩, ⟨0, 6, 3, 20⟩, ⟨0, 5, 3, 22⟩, ⟨0, 4, 3, 24⟩, ⟨0, 16, 2, 2⟩, ⟨0, 16, 1, 4⟩, ⟨0, 16, 0, 6⟩]
  exact AllWinning.cons node_5374 (AllWinning.cons node_4630 (AllWinning.cons node_3989 (AllWinning.cons node_3368 (AllWinning.cons node_2875 (AllWinning.cons node_2412 (AllWinning.cons node_1913 (AllWinning.cons node_1580 (AllWinning.cons node_1191 (AllWinning.cons node_936 (AllWinning.cons node_718 (AllWinning.cons node_482 (AllWinning.cons node_5378 (AllWinning.cons node_4642 (AllWinning.cons node_4000 (AllWinning.nil)))))))))))))))

theorem node_6106 : Outcome ⟨0, 16, 3, 16⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 26⟩) (by decide) node_349

theorem node_6107 : Outcome ⟨0, 16, 3, 26⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 26⟩) (by decide) node_349

theorem node_6108 : Outcome ⟨0, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 4⟩) (by decide) node_4635

theorem node_6109 : Outcome ⟨0, 17, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 4⟩) (by decide) node_4635

theorem node_6110 : Outcome ⟨0, 17, 2, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 4⟩) (by decide) node_4635

theorem node_6111 : Outcome ⟨0, 18, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 1, 2⟩) (by decide) node_5382

theorem node_6112 : Outcome ⟨0, 18, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 8⟩) (by decide) node_3376

theorem node_6113 : Outcome ⟨0, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 0, 2⟩) (by decide) node_5386

theorem node_6114 : Outcome ⟨0, 19, 0, 12⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 12⟩) (by decide) node_2429

theorem node_6115 : Outcome ⟨1, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 18, 2⟩) (by decide) node_5310

theorem node_6116 : Outcome ⟨1, 0, 18, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 8⟩) (by decide) node_3387

theorem node_6117 : Outcome ⟨1, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 17, 2⟩) (by decide) node_5313

theorem node_6118 : Outcome ⟨1, 1, 17, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 34⟩) (by decide) node_87

theorem node_6119 : Outcome ⟨1, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 16, 2⟩) (by decide) node_5392

theorem node_6120 : Outcome ⟨1, 2, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 16, 2⟩) (by decide) node_5392

theorem node_6121 : Outcome ⟨1, 2, 16, 18⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 24⟩) (by decide) node_515

theorem node_6122 : Outcome ⟨1, 2, 16, 26⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 24⟩) (by decide) node_515

theorem node_6123 : Outcome ⟨1, 3, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 14, 2⟩) (by decide) node_5400

theorem node_6124 : Outcome ⟨1, 3, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 3, 14, 2⟩) (by decide) node_5400

theorem node_6125 : Outcome ⟨1, 3, 15, 12⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 18⟩) (by decide) node_1227

theorem node_6126 : Outcome ⟨1, 3, 15, 26⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 18⟩) (by decide) node_1227

theorem node_6127 : Outcome ⟨1, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 14, 2⟩) (by decide) node_5400

theorem node_6128 : Outcome ⟨1, 4, 14, 12⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 24⟩) (by decide) node_536

theorem node_6129 : Outcome ⟨1, 4, 14, 36⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 24⟩) (by decide) node_536

theorem node_6130 : Outcome ⟨1, 5, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 13, 2⟩) (by decide) node_5328

theorem node_6131 : Outcome ⟨1, 5, 13, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 8⟩) (by decide) node_3395

theorem node_6132 : Outcome ⟨1, 5, 13, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 8⟩) (by decide) node_3395

theorem node_6133 : Outcome ⟨1, 6, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 12, 2⟩) (by decide) node_5409

theorem node_6134 : Outcome ⟨1, 6, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 12, 2⟩) (by decide) node_5409

theorem node_6135 : Outcome ⟨1, 6, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 5, 12, 2⟩) (by decide) node_5409

theorem node_6136 : Outcome ⟨1, 6, 12, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 18⟩) (by decide) node_1255

theorem node_6137 : Outcome ⟨1, 7, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.nil)))))

theorem node_6138 : Outcome ⟨1, 7, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.nil)))))))))

theorem node_6139 : Outcome ⟨1, 7, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.nil)))))))))))))

theorem node_6140 : Outcome ⟨1, 7, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.nil))))))))))))))))

theorem node_6141 : Outcome ⟨1, 7, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.nil))))))))))))))))))

theorem node_6142 : Outcome ⟨1, 7, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩, ⟨1, 7, 0, 22⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.cons node_764 (AllWinning.nil)))))))))))))))))))

theorem node_6143 : Outcome ⟨1, 7, 11, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩, ⟨1, 7, 0, 22⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.cons node_764 (AllWinning.nil)))))))))))))))))))

theorem node_6144 : Outcome ⟨1, 7, 11, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩, ⟨1, 7, 0, 22⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.cons node_764 (AllWinning.nil)))))))))))))))))))

theorem node_6145 : Outcome ⟨1, 7, 11, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩, ⟨1, 7, 0, 22⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.cons node_764 (AllWinning.nil)))))))))))))))))))

theorem node_6146 : Outcome ⟨1, 7, 11, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩, ⟨1, 7, 0, 22⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.cons node_764 (AllWinning.nil)))))))))))))))))))

theorem node_6147 : Outcome ⟨1, 7, 11, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩, ⟨1, 7, 0, 22⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.cons node_764 (AllWinning.nil)))))))))))))))))))

theorem node_6148 : Outcome ⟨1, 7, 11, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 11, 2⟩, ⟨1, 6, 11, 2⟩, ⟨1, 5, 11, 4⟩, ⟨1, 4, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨1, 1, 11, 12⟩, ⟨1, 0, 11, 14⟩, ⟨1, 7, 10, 2⟩, ⟨1, 7, 9, 4⟩, ⟨1, 7, 8, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 7, 6, 10⟩, ⟨1, 7, 5, 12⟩, ⟨1, 7, 4, 14⟩, ⟨1, 7, 3, 16⟩, ⟨1, 7, 2, 18⟩, ⟨1, 7, 1, 20⟩, ⟨1, 7, 0, 22⟩]
  exact AllWinning.cons node_5337 (AllWinning.cons node_5412 (AllWinning.cons node_4672 (AllWinning.cons node_4013 (AllWinning.cons node_3405 (AllWinning.cons node_2896 (AllWinning.cons node_2437 (AllWinning.cons node_1931 (AllWinning.cons node_5415 (AllWinning.cons node_4678 (AllWinning.cons node_4024 (AllWinning.cons node_3430 (AllWinning.cons node_2915 (AllWinning.cons node_2458 (AllWinning.cons node_1962 (AllWinning.cons node_1622 (AllWinning.cons node_1266 (AllWinning.cons node_987 (AllWinning.cons node_764 (AllWinning.nil)))))))))))))))))))

theorem node_6149 : Outcome ⟨1, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 9, 2⟩) (by decide) node_5418

theorem node_6150 : Outcome ⟨1, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 9, 2⟩) (by decide) node_5418

theorem node_6151 : Outcome ⟨1, 8, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 9, 2⟩) (by decide) node_5418

theorem node_6152 : Outcome ⟨1, 8, 10, 12⟩ true :=
  Outcome.win (q := ⟨1, 8, 9, 2⟩) (by decide) node_5418

theorem node_6153 : Outcome ⟨1, 8, 10, 20⟩ true :=
  Outcome.win (q := ⟨1, 8, 9, 2⟩) (by decide) node_5418

theorem node_6154 : Outcome ⟨1, 9, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 2⟩) (by decide) node_5344

theorem node_6155 : Outcome ⟨1, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 8⟩) (by decide) node_3415

theorem node_6156 : Outcome ⟨1, 9, 9, 8⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 8⟩) (by decide) node_3415

theorem node_6157 : Outcome ⟨1, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 8, 2⟩) (by decide) node_5422

theorem node_6158 : Outcome ⟨1, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 8, 2⟩) (by decide) node_5422

theorem node_6159 : Outcome ⟨1, 10, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 9, 8, 2⟩) (by decide) node_5422

theorem node_6160 : Outcome ⟨1, 10, 8, 12⟩ true :=
  Outcome.win (q := ⟨1, 9, 8, 2⟩) (by decide) node_5422

theorem node_6161 : Outcome ⟨1, 10, 8, 20⟩ true :=
  Outcome.win (q := ⟨1, 9, 8, 2⟩) (by decide) node_5422

theorem node_6162 : Outcome ⟨1, 11, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.nil)))))

theorem node_6163 : Outcome ⟨1, 11, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.nil)))))))))

theorem node_6164 : Outcome ⟨1, 11, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.nil)))))))))))))

theorem node_6165 : Outcome ⟨1, 11, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil))))))))))))))))

theorem node_6166 : Outcome ⟨1, 11, 7, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil))))))))))))))))))

theorem node_6167 : Outcome ⟨1, 11, 7, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 0, 7, 22⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_739 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil)))))))))))))))))))

theorem node_6168 : Outcome ⟨1, 11, 7, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 0, 7, 22⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_739 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil)))))))))))))))))))

theorem node_6169 : Outcome ⟨1, 11, 7, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 0, 7, 22⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_739 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil)))))))))))))))))))

theorem node_6170 : Outcome ⟨1, 11, 7, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 0, 7, 22⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_739 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil)))))))))))))))))))

theorem node_6171 : Outcome ⟨1, 11, 7, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 0, 7, 22⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_739 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil)))))))))))))))))))

theorem node_6172 : Outcome ⟨1, 11, 7, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 0, 7, 22⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_739 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil)))))))))))))))))))

theorem node_6173 : Outcome ⟨1, 11, 7, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 7, 2⟩, ⟨1, 10, 7, 2⟩, ⟨1, 9, 7, 4⟩, ⟨1, 8, 7, 6⟩, ⟨1, 7, 7, 8⟩, ⟨1, 6, 7, 10⟩, ⟨1, 5, 7, 12⟩, ⟨1, 4, 7, 14⟩, ⟨1, 3, 7, 16⟩, ⟨1, 2, 7, 18⟩, ⟨1, 1, 7, 20⟩, ⟨1, 0, 7, 22⟩, ⟨1, 11, 6, 2⟩, ⟨1, 11, 5, 4⟩, ⟨1, 11, 4, 6⟩, ⟨1, 11, 3, 8⟩, ⟨1, 11, 2, 10⟩, ⟨1, 11, 1, 12⟩, ⟨1, 11, 0, 14⟩]
  exact AllWinning.cons node_5359 (AllWinning.cons node_5426 (AllWinning.cons node_4686 (AllWinning.cons node_4028 (AllWinning.cons node_3430 (AllWinning.cons node_2911 (AllWinning.cons node_2453 (AllWinning.cons node_1950 (AllWinning.cons node_1608 (AllWinning.cons node_1217 (AllWinning.cons node_959 (AllWinning.cons node_739 (AllWinning.cons node_5429 (AllWinning.cons node_4694 (AllWinning.cons node_4038 (AllWinning.cons node_3456 (AllWinning.cons node_2931 (AllWinning.cons node_2475 (AllWinning.cons node_1980 (AllWinning.nil)))))))))))))))))))

theorem node_6174 : Outcome ⟨1, 12, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 5, 2⟩) (by decide) node_5432

theorem node_6175 : Outcome ⟨1, 12, 6, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 5, 2⟩) (by decide) node_5432

theorem node_6176 : Outcome ⟨1, 12, 6, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 5, 2⟩) (by decide) node_5432

theorem node_6177 : Outcome ⟨1, 12, 6, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 18⟩) (by decide) node_1227

theorem node_6178 : Outcome ⟨1, 13, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 5, 2⟩) (by decide) node_5366

theorem node_6179 : Outcome ⟨1, 13, 5, 8⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 8⟩) (by decide) node_3439

theorem node_6180 : Outcome ⟨1, 13, 5, 24⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 8⟩) (by decide) node_3439

theorem node_6181 : Outcome ⟨1, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 4, 2⟩) (by decide) node_5435

theorem node_6182 : Outcome ⟨1, 14, 4, 12⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 24⟩) (by decide) node_515

theorem node_6183 : Outcome ⟨1, 14, 4, 36⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 24⟩) (by decide) node_515

theorem node_6184 : Outcome ⟨1, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 3, 2⟩) (by decide) node_5441

theorem node_6185 : Outcome ⟨1, 15, 3, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 3, 2⟩) (by decide) node_5441

theorem node_6186 : Outcome ⟨1, 15, 3, 12⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 18⟩) (by decide) node_1255

theorem node_6187 : Outcome ⟨1, 15, 3, 26⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 18⟩) (by decide) node_1255

theorem node_6188 : Outcome ⟨1, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 1, 2⟩) (by decide) node_5449

theorem node_6189 : Outcome ⟨1, 16, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 1, 2⟩) (by decide) node_5449

theorem node_6190 : Outcome ⟨1, 16, 2, 18⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 24⟩) (by decide) node_536

theorem node_6191 : Outcome ⟨1, 16, 2, 26⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 24⟩) (by decide) node_536

theorem node_6192 : Outcome ⟨1, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 1, 2⟩) (by decide) node_5382

theorem node_6193 : Outcome ⟨1, 17, 1, 24⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 34⟩) (by decide) node_70

theorem node_6194 : Outcome ⟨1, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 0, 2⟩) (by decide) node_5386

theorem node_6195 : Outcome ⟨1, 18, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 8⟩) (by decide) node_3473

theorem node_6196 : Outcome ⟨2, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 4⟩) (by decide) node_4720

theorem node_6197 : Outcome ⟨2, 0, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 4⟩) (by decide) node_4720

theorem node_6198 : Outcome ⟨2, 0, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 4⟩) (by decide) node_4720

theorem node_6199 : Outcome ⟨2, 1, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 16, 2⟩) (by decide) node_5392

theorem node_6200 : Outcome ⟨2, 1, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 16, 2⟩) (by decide) node_5392

theorem node_6201 : Outcome ⟨2, 1, 16, 18⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 24⟩) (by decide) node_566

theorem node_6202 : Outcome ⟨2, 1, 16, 26⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 24⟩) (by decide) node_566

theorem node_6203 : Outcome ⟨2, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 4⟩) (by decide) node_4576

theorem node_6204 : Outcome ⟨2, 2, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 4⟩) (by decide) node_4576

theorem node_6205 : Outcome ⟨2, 2, 15, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 4⟩) (by decide) node_4576

theorem node_6206 : Outcome ⟨2, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 14, 2⟩) (by decide) node_5400

theorem node_6207 : Outcome ⟨2, 3, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 14⟩) (by decide) node_2000

theorem node_6208 : Outcome ⟨2, 3, 14, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 14⟩) (by decide) node_2000

theorem node_6209 : Outcome ⟨2, 3, 14, 18⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 14⟩) (by decide) node_2000

theorem node_6210 : Outcome ⟨2, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 4⟩) (by decide) node_4731

theorem node_6211 : Outcome ⟨2, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 4⟩) (by decide) node_4731

theorem node_6212 : Outcome ⟨2, 4, 13, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 24⟩) (by decide) node_588

theorem node_6213 : Outcome ⟨2, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 4⟩) (by decide) node_4744

theorem node_6214 : Outcome ⟨2, 5, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 4⟩) (by decide) node_4744

theorem node_6215 : Outcome ⟨2, 5, 12, 16⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 4⟩) (by decide) node_4744

theorem node_6216 : Outcome ⟨2, 5, 12, 18⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 4⟩) (by decide) node_4744

theorem node_6217 : Outcome ⟨2, 6, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 6, 11, 2⟩, ⟨0, 6, 11, 4⟩, ⟨2, 5, 11, 2⟩, ⟨2, 4, 11, 4⟩, ⟨2, 6, 10, 2⟩, ⟨2, 6, 9, 4⟩]
  exact AllWinning.cons node_5412 (AllWinning.cons node_4597 (AllWinning.cons node_5475 (AllWinning.cons node_4741 (AllWinning.cons node_5477 (AllWinning.cons node_4757 (AllWinning.nil))))))

theorem node_6218 : Outcome ⟨2, 6, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 6, 11, 2⟩, ⟨0, 6, 11, 4⟩, ⟨2, 5, 11, 2⟩, ⟨2, 4, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨2, 6, 10, 2⟩, ⟨2, 6, 9, 4⟩, ⟨2, 6, 8, 6⟩, ⟨2, 6, 7, 8⟩]
  exact AllWinning.cons node_5412 (AllWinning.cons node_4597 (AllWinning.cons node_5475 (AllWinning.cons node_4741 (AllWinning.cons node_4062 (AllWinning.cons node_3488 (AllWinning.cons node_5477 (AllWinning.cons node_4757 (AllWinning.cons node_4070 (AllWinning.cons node_3504 (AllWinning.nil))))))))))

theorem node_6219 : Outcome ⟨2, 6, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 6, 11, 2⟩, ⟨0, 6, 11, 4⟩, ⟨2, 5, 11, 2⟩, ⟨2, 4, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨2, 0, 11, 12⟩, ⟨2, 6, 10, 2⟩, ⟨2, 6, 9, 4⟩, ⟨2, 6, 8, 6⟩, ⟨2, 6, 7, 8⟩, ⟨2, 6, 6, 10⟩, ⟨2, 6, 5, 12⟩]
  exact AllWinning.cons node_5412 (AllWinning.cons node_4597 (AllWinning.cons node_5475 (AllWinning.cons node_4741 (AllWinning.cons node_4062 (AllWinning.cons node_3488 (AllWinning.cons node_2945 (AllWinning.cons node_2482 (AllWinning.cons node_5477 (AllWinning.cons node_4757 (AllWinning.cons node_4070 (AllWinning.cons node_3504 (AllWinning.cons node_2964 (AllWinning.cons node_2506 (AllWinning.nil))))))))))))))

theorem node_6220 : Outcome ⟨2, 6, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 6, 11, 2⟩, ⟨0, 6, 11, 4⟩, ⟨2, 5, 11, 2⟩, ⟨2, 4, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨2, 0, 11, 12⟩, ⟨2, 6, 10, 2⟩, ⟨2, 6, 9, 4⟩, ⟨2, 6, 8, 6⟩, ⟨2, 6, 7, 8⟩, ⟨2, 6, 6, 10⟩, ⟨2, 6, 5, 12⟩, ⟨2, 6, 4, 14⟩, ⟨2, 6, 3, 16⟩]
  exact AllWinning.cons node_5412 (AllWinning.cons node_4597 (AllWinning.cons node_5475 (AllWinning.cons node_4741 (AllWinning.cons node_4062 (AllWinning.cons node_3488 (AllWinning.cons node_2945 (AllWinning.cons node_2482 (AllWinning.cons node_5477 (AllWinning.cons node_4757 (AllWinning.cons node_4070 (AllWinning.cons node_3504 (AllWinning.cons node_2964 (AllWinning.cons node_2506 (AllWinning.cons node_2022 (AllWinning.cons node_1662 (AllWinning.nil))))))))))))))))

theorem node_6221 : Outcome ⟨2, 6, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 6, 11, 2⟩, ⟨0, 6, 11, 4⟩, ⟨2, 5, 11, 2⟩, ⟨2, 4, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨2, 1, 11, 10⟩, ⟨2, 0, 11, 12⟩, ⟨2, 6, 10, 2⟩, ⟨2, 6, 9, 4⟩, ⟨2, 6, 8, 6⟩, ⟨2, 6, 7, 8⟩, ⟨2, 6, 6, 10⟩, ⟨2, 6, 5, 12⟩, ⟨2, 6, 4, 14⟩, ⟨2, 6, 3, 16⟩, ⟨2, 6, 2, 18⟩, ⟨2, 6, 1, 20⟩]
  exact AllWinning.cons node_5412 (AllWinning.cons node_4597 (AllWinning.cons node_5475 (AllWinning.cons node_4741 (AllWinning.cons node_4062 (AllWinning.cons node_3488 (AllWinning.cons node_2945 (AllWinning.cons node_2482 (AllWinning.cons node_5477 (AllWinning.cons node_4757 (AllWinning.cons node_4070 (AllWinning.cons node_3504 (AllWinning.cons node_2964 (AllWinning.cons node_2506 (AllWinning.cons node_2022 (AllWinning.cons node_1662 (AllWinning.cons node_1305 (AllWinning.cons node_1022 (AllWinning.nil))))))))))))))))))

end RQ9F1
