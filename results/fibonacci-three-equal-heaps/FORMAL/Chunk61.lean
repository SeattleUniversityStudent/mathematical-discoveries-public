import Chunk60
set_option autoImplicit false
namespace RQ9F1

theorem node_14043 : Outcome ⟨1, 18, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 8, 2⟩, ⟨1, 17, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨1, 15, 8, 6⟩, ⟨1, 14, 8, 8⟩, ⟨1, 18, 7, 2⟩, ⟨1, 18, 6, 4⟩, ⟨1, 18, 5, 6⟩, ⟨1, 18, 4, 8⟩]
  exact AllWinning.cons node_13022 (AllWinning.cons node_13067 (AllWinning.cons node_12067 (AllWinning.cons node_11072 (AllWinning.cons node_9991 (AllWinning.cons node_13071 (AllWinning.cons node_12074 (AllWinning.cons node_11082 (AllWinning.cons node_10012 (AllWinning.nil)))))))))

theorem node_14044 : Outcome ⟨1, 18, 8, 12⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 12⟩) (by decide) node_8031

theorem node_14045 : Outcome ⟨1, 18, 8, 14⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 12⟩) (by decide) node_8031

theorem node_14046 : Outcome ⟨1, 18, 8, 22⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 12⟩) (by decide) node_8031

theorem node_14047 : Outcome ⟨1, 19, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 8⟩) (by decide) node_10017

theorem node_14048 : Outcome ⟨1, 19, 7, 10⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 16⟩) (by decide) node_6169

theorem node_14049 : Outcome ⟨1, 19, 7, 22⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 16⟩) (by decide) node_6169

theorem node_14050 : Outcome ⟨1, 20, 6, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 8⟩) (by decide) node_10000

theorem node_14051 : Outcome ⟨1, 20, 6, 10⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 8⟩) (by decide) node_10000

theorem node_14052 : Outcome ⟨2, 5, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 4⟩) (by decide) node_12083

theorem node_14053 : Outcome ⟨2, 5, 20, 8⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 4⟩) (by decide) node_12083

theorem node_14054 : Outcome ⟨2, 6, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 19, 4⟩) (by decide) node_11962

theorem node_14055 : Outcome ⟨2, 6, 19, 10⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 16⟩) (by decide) node_6224

theorem node_14056 : Outcome ⟨2, 7, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 18, 2⟩, ⟨0, 7, 18, 4⟩, ⟨2, 6, 18, 2⟩, ⟨2, 5, 18, 4⟩, ⟨2, 7, 17, 2⟩, ⟨2, 7, 16, 4⟩]
  exact AllWinning.cons node_13035 (AllWinning.cons node_11967 (AllWinning.cons node_13081 (AllWinning.cons node_12092 (AllWinning.cons node_13084 (AllWinning.cons node_12101 (AllWinning.nil))))))

theorem node_14057 : Outcome ⟨2, 7, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 18, 2⟩, ⟨0, 7, 18, 4⟩, ⟨2, 6, 18, 2⟩, ⟨2, 5, 18, 4⟩, ⟨2, 4, 18, 6⟩, ⟨2, 3, 18, 8⟩, ⟨2, 7, 17, 2⟩, ⟨2, 7, 16, 4⟩, ⟨2, 7, 15, 6⟩, ⟨2, 7, 14, 8⟩]
  exact AllWinning.cons node_13035 (AllWinning.cons node_11967 (AllWinning.cons node_13081 (AllWinning.cons node_12092 (AllWinning.cons node_11095 (AllWinning.cons node_10028 (AllWinning.cons node_13084 (AllWinning.cons node_12101 (AllWinning.cons node_11108 (AllWinning.cons node_10042 (AllWinning.nil))))))))))

theorem node_14058 : Outcome ⟨2, 7, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 18, 2⟩, ⟨0, 7, 18, 4⟩, ⟨2, 6, 18, 2⟩, ⟨2, 5, 18, 4⟩, ⟨2, 4, 18, 6⟩, ⟨2, 3, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨2, 1, 18, 12⟩, ⟨2, 7, 17, 2⟩, ⟨2, 7, 16, 4⟩, ⟨2, 7, 15, 6⟩, ⟨2, 7, 14, 8⟩, ⟨2, 7, 13, 10⟩, ⟨2, 7, 12, 12⟩]
  exact AllWinning.cons node_13035 (AllWinning.cons node_11967 (AllWinning.cons node_13081 (AllWinning.cons node_12092 (AllWinning.cons node_11095 (AllWinning.cons node_10028 (AllWinning.cons node_9054 (AllWinning.cons node_8070 (AllWinning.cons node_13084 (AllWinning.cons node_12101 (AllWinning.cons node_11108 (AllWinning.cons node_10042 (AllWinning.cons node_9075 (AllWinning.cons node_8094 (AllWinning.nil))))))))))))))

theorem node_14059 : Outcome ⟨2, 7, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 18, 2⟩, ⟨0, 7, 18, 4⟩, ⟨2, 6, 18, 2⟩, ⟨2, 5, 18, 4⟩, ⟨2, 4, 18, 6⟩, ⟨2, 3, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨2, 1, 18, 12⟩, ⟨2, 0, 18, 14⟩, ⟨2, 7, 17, 2⟩, ⟨2, 7, 16, 4⟩, ⟨2, 7, 15, 6⟩, ⟨2, 7, 14, 8⟩, ⟨2, 7, 13, 10⟩, ⟨2, 7, 12, 12⟩, ⟨2, 7, 11, 14⟩, ⟨2, 7, 10, 16⟩]
  exact AllWinning.cons node_13035 (AllWinning.cons node_11967 (AllWinning.cons node_13081 (AllWinning.cons node_12092 (AllWinning.cons node_11095 (AllWinning.cons node_10028 (AllWinning.cons node_9054 (AllWinning.cons node_8070 (AllWinning.cons node_7114 (AllWinning.cons node_13084 (AllWinning.cons node_12101 (AllWinning.cons node_11108 (AllWinning.cons node_10042 (AllWinning.cons node_9075 (AllWinning.cons node_8094 (AllWinning.cons node_7147 (AllWinning.cons node_6229 (AllWinning.nil)))))))))))))))))

theorem node_14060 : Outcome ⟨2, 7, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 18, 2⟩, ⟨0, 7, 18, 4⟩, ⟨2, 6, 18, 2⟩, ⟨2, 5, 18, 4⟩, ⟨2, 4, 18, 6⟩, ⟨2, 3, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨2, 1, 18, 12⟩, ⟨2, 0, 18, 14⟩, ⟨2, 7, 17, 2⟩, ⟨2, 7, 16, 4⟩, ⟨2, 7, 15, 6⟩, ⟨2, 7, 14, 8⟩, ⟨2, 7, 13, 10⟩, ⟨2, 7, 12, 12⟩, ⟨2, 7, 11, 14⟩, ⟨2, 7, 10, 16⟩, ⟨2, 7, 9, 18⟩, ⟨2, 7, 8, 20⟩]
  exact AllWinning.cons node_13035 (AllWinning.cons node_11967 (AllWinning.cons node_13081 (AllWinning.cons node_12092 (AllWinning.cons node_11095 (AllWinning.cons node_10028 (AllWinning.cons node_9054 (AllWinning.cons node_8070 (AllWinning.cons node_7114 (AllWinning.cons node_13084 (AllWinning.cons node_12101 (AllWinning.cons node_11108 (AllWinning.cons node_10042 (AllWinning.cons node_9075 (AllWinning.cons node_8094 (AllWinning.cons node_7147 (AllWinning.cons node_6229 (AllWinning.cons node_5483 (AllWinning.cons node_4762 (AllWinning.nil)))))))))))))))))))

theorem node_14061 : Outcome ⟨2, 7, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 18, 2⟩, ⟨0, 7, 18, 4⟩, ⟨2, 6, 18, 2⟩, ⟨2, 5, 18, 4⟩, ⟨2, 4, 18, 6⟩, ⟨2, 3, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨2, 1, 18, 12⟩, ⟨2, 0, 18, 14⟩, ⟨2, 7, 17, 2⟩, ⟨2, 7, 16, 4⟩, ⟨2, 7, 15, 6⟩, ⟨2, 7, 14, 8⟩, ⟨2, 7, 13, 10⟩, ⟨2, 7, 12, 12⟩, ⟨2, 7, 11, 14⟩, ⟨2, 7, 10, 16⟩, ⟨2, 7, 9, 18⟩, ⟨2, 7, 8, 20⟩, ⟨2, 7, 7, 22⟩, ⟨2, 7, 6, 24⟩]
  exact AllWinning.cons node_13035 (AllWinning.cons node_11967 (AllWinning.cons node_13081 (AllWinning.cons node_12092 (AllWinning.cons node_11095 (AllWinning.cons node_10028 (AllWinning.cons node_9054 (AllWinning.cons node_8070 (AllWinning.cons node_7114 (AllWinning.cons node_13084 (AllWinning.cons node_12101 (AllWinning.cons node_11108 (AllWinning.cons node_10042 (AllWinning.cons node_9075 (AllWinning.cons node_8094 (AllWinning.cons node_7147 (AllWinning.cons node_6229 (AllWinning.cons node_5483 (AllWinning.cons node_4762 (AllWinning.cons node_4076 (AllWinning.cons node_3510 (AllWinning.nil)))))))))))))))))))))

theorem node_14062 : Outcome ⟨2, 7, 18, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 18, 2⟩, ⟨0, 7, 18, 4⟩, ⟨2, 6, 18, 2⟩, ⟨2, 5, 18, 4⟩, ⟨2, 4, 18, 6⟩, ⟨2, 3, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨2, 1, 18, 12⟩, ⟨2, 0, 18, 14⟩, ⟨2, 7, 17, 2⟩, ⟨2, 7, 16, 4⟩, ⟨2, 7, 15, 6⟩, ⟨2, 7, 14, 8⟩, ⟨2, 7, 13, 10⟩, ⟨2, 7, 12, 12⟩, ⟨2, 7, 11, 14⟩, ⟨2, 7, 10, 16⟩, ⟨2, 7, 9, 18⟩, ⟨2, 7, 8, 20⟩, ⟨2, 7, 7, 22⟩, ⟨2, 7, 6, 24⟩, ⟨2, 7, 5, 26⟩, ⟨2, 7, 4, 28⟩]
  exact AllWinning.cons node_13035 (AllWinning.cons node_11967 (AllWinning.cons node_13081 (AllWinning.cons node_12092 (AllWinning.cons node_11095 (AllWinning.cons node_10028 (AllWinning.cons node_9054 (AllWinning.cons node_8070 (AllWinning.cons node_7114 (AllWinning.cons node_13084 (AllWinning.cons node_12101 (AllWinning.cons node_11108 (AllWinning.cons node_10042 (AllWinning.cons node_9075 (AllWinning.cons node_8094 (AllWinning.cons node_7147 (AllWinning.cons node_6229 (AllWinning.cons node_5483 (AllWinning.cons node_4762 (AllWinning.cons node_4076 (AllWinning.cons node_3510 (AllWinning.cons node_2969 (AllWinning.cons node_2512 (AllWinning.nil)))))))))))))))))))))))

theorem node_14063 : Outcome ⟨2, 7, 18, 18⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 30⟩) (by decide) node_2038

theorem node_14064 : Outcome ⟨2, 8, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 6, 17, 4⟩) (by decide) node_12097

theorem node_14065 : Outcome ⟨2, 8, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 6, 17, 4⟩) (by decide) node_12097

theorem node_14066 : Outcome ⟨2, 9, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 16, 2⟩) (by decide) node_13041

theorem node_14067 : Outcome ⟨2, 9, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 16, 2⟩) (by decide) node_13041

theorem node_14068 : Outcome ⟨2, 9, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 9, 16, 2⟩) (by decide) node_13041

theorem node_14069 : Outcome ⟨2, 9, 16, 18⟩ true :=
  Outcome.win (q := ⟨1, 9, 16, 2⟩) (by decide) node_13041

theorem node_14070 : Outcome ⟨2, 10, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 10, 15, 4⟩) (by decide) node_11978

theorem node_14071 : Outcome ⟨2, 11, 14, 2⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 2⟩) (by decide) node_13099

theorem node_14072 : Outcome ⟨2, 11, 14, 6⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 2⟩) (by decide) node_13099

theorem node_14073 : Outcome ⟨2, 12, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 13, 2⟩) (by decide) node_13049

theorem node_14074 : Outcome ⟨2, 12, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 13, 2⟩) (by decide) node_13049

theorem node_14075 : Outcome ⟨2, 13, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 12, 2⟩) (by decide) node_13054

theorem node_14076 : Outcome ⟨2, 13, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 12, 2⟩) (by decide) node_13054

theorem node_14077 : Outcome ⟨2, 14, 11, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 2⟩) (by decide) node_13105

theorem node_14078 : Outcome ⟨2, 14, 11, 6⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 2⟩) (by decide) node_13105

theorem node_14079 : Outcome ⟨2, 15, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 10, 4⟩) (by decide) node_11990

theorem node_14080 : Outcome ⟨2, 16, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 9, 2⟩) (by decide) node_13064

theorem node_14081 : Outcome ⟨2, 16, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 9, 2⟩) (by decide) node_13064

theorem node_14082 : Outcome ⟨2, 16, 9, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 9, 2⟩) (by decide) node_13064

theorem node_14083 : Outcome ⟨2, 16, 9, 18⟩ true :=
  Outcome.win (q := ⟨1, 16, 9, 2⟩) (by decide) node_13064

theorem node_14084 : Outcome ⟨2, 17, 8, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 6, 4⟩) (by decide) node_12134

theorem node_14085 : Outcome ⟨2, 17, 8, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 6, 4⟩) (by decide) node_12134

theorem node_14086 : Outcome ⟨2, 18, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 7, 2⟩, ⟨0, 18, 7, 4⟩, ⟨2, 17, 7, 2⟩, ⟨2, 16, 7, 4⟩, ⟨2, 18, 6, 2⟩, ⟨2, 18, 5, 4⟩]
  exact AllWinning.cons node_13071 (AllWinning.cons node_12000 (AllWinning.cons node_13121 (AllWinning.cons node_12128 (AllWinning.cons node_13124 (AllWinning.cons node_12138 (AllWinning.nil))))))

theorem node_14087 : Outcome ⟨2, 18, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 7, 2⟩, ⟨0, 18, 7, 4⟩, ⟨2, 17, 7, 2⟩, ⟨2, 16, 7, 4⟩, ⟨2, 15, 7, 6⟩, ⟨2, 14, 7, 8⟩, ⟨2, 18, 6, 2⟩, ⟨2, 18, 5, 4⟩, ⟨2, 18, 4, 6⟩, ⟨2, 18, 3, 8⟩]
  exact AllWinning.cons node_13071 (AllWinning.cons node_12000 (AllWinning.cons node_13121 (AllWinning.cons node_12128 (AllWinning.cons node_11131 (AllWinning.cons node_10067 (AllWinning.cons node_13124 (AllWinning.cons node_12138 (AllWinning.cons node_11143 (AllWinning.cons node_10082 (AllWinning.nil))))))))))

theorem node_14088 : Outcome ⟨2, 18, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 7, 2⟩, ⟨0, 18, 7, 4⟩, ⟨2, 17, 7, 2⟩, ⟨2, 16, 7, 4⟩, ⟨2, 15, 7, 6⟩, ⟨2, 14, 7, 8⟩, ⟨2, 13, 7, 10⟩, ⟨2, 12, 7, 12⟩, ⟨2, 18, 6, 2⟩, ⟨2, 18, 5, 4⟩, ⟨2, 18, 4, 6⟩, ⟨2, 18, 3, 8⟩, ⟨2, 18, 2, 10⟩, ⟨2, 18, 1, 12⟩]
  exact AllWinning.cons node_13071 (AllWinning.cons node_12000 (AllWinning.cons node_13121 (AllWinning.cons node_12128 (AllWinning.cons node_11131 (AllWinning.cons node_10067 (AllWinning.cons node_9095 (AllWinning.cons node_8120 (AllWinning.cons node_13124 (AllWinning.cons node_12138 (AllWinning.cons node_11143 (AllWinning.cons node_10082 (AllWinning.cons node_9116 (AllWinning.cons node_8142 (AllWinning.nil))))))))))))))

theorem node_14089 : Outcome ⟨2, 18, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 7, 2⟩, ⟨0, 18, 7, 4⟩, ⟨2, 17, 7, 2⟩, ⟨2, 16, 7, 4⟩, ⟨2, 15, 7, 6⟩, ⟨2, 14, 7, 8⟩, ⟨2, 13, 7, 10⟩, ⟨2, 12, 7, 12⟩, ⟨2, 11, 7, 14⟩, ⟨2, 10, 7, 16⟩, ⟨2, 18, 6, 2⟩, ⟨2, 18, 5, 4⟩, ⟨2, 18, 4, 6⟩, ⟨2, 18, 3, 8⟩, ⟨2, 18, 2, 10⟩, ⟨2, 18, 1, 12⟩, ⟨2, 18, 0, 14⟩]
  exact AllWinning.cons node_13071 (AllWinning.cons node_12000 (AllWinning.cons node_13121 (AllWinning.cons node_12128 (AllWinning.cons node_11131 (AllWinning.cons node_10067 (AllWinning.cons node_9095 (AllWinning.cons node_8120 (AllWinning.cons node_7165 (AllWinning.cons node_6239 (AllWinning.cons node_13124 (AllWinning.cons node_12138 (AllWinning.cons node_11143 (AllWinning.cons node_10082 (AllWinning.cons node_9116 (AllWinning.cons node_8142 (AllWinning.cons node_7198 (AllWinning.nil)))))))))))))))))

theorem node_14090 : Outcome ⟨2, 18, 7, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 7, 2⟩, ⟨0, 18, 7, 4⟩, ⟨2, 17, 7, 2⟩, ⟨2, 16, 7, 4⟩, ⟨2, 15, 7, 6⟩, ⟨2, 14, 7, 8⟩, ⟨2, 13, 7, 10⟩, ⟨2, 12, 7, 12⟩, ⟨2, 11, 7, 14⟩, ⟨2, 10, 7, 16⟩, ⟨2, 9, 7, 18⟩, ⟨2, 8, 7, 20⟩, ⟨2, 18, 6, 2⟩, ⟨2, 18, 5, 4⟩, ⟨2, 18, 4, 6⟩, ⟨2, 18, 3, 8⟩, ⟨2, 18, 2, 10⟩, ⟨2, 18, 1, 12⟩, ⟨2, 18, 0, 14⟩]
  exact AllWinning.cons node_13071 (AllWinning.cons node_12000 (AllWinning.cons node_13121 (AllWinning.cons node_12128 (AllWinning.cons node_11131 (AllWinning.cons node_10067 (AllWinning.cons node_9095 (AllWinning.cons node_8120 (AllWinning.cons node_7165 (AllWinning.cons node_6239 (AllWinning.cons node_5492 (AllWinning.cons node_4767 (AllWinning.cons node_13124 (AllWinning.cons node_12138 (AllWinning.cons node_11143 (AllWinning.cons node_10082 (AllWinning.cons node_9116 (AllWinning.cons node_8142 (AllWinning.cons node_7198 (AllWinning.nil)))))))))))))))))))

theorem node_14091 : Outcome ⟨2, 18, 7, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 7, 2⟩, ⟨0, 18, 7, 4⟩, ⟨2, 17, 7, 2⟩, ⟨2, 16, 7, 4⟩, ⟨2, 15, 7, 6⟩, ⟨2, 14, 7, 8⟩, ⟨2, 13, 7, 10⟩, ⟨2, 12, 7, 12⟩, ⟨2, 11, 7, 14⟩, ⟨2, 10, 7, 16⟩, ⟨2, 9, 7, 18⟩, ⟨2, 8, 7, 20⟩, ⟨2, 7, 7, 22⟩, ⟨2, 6, 7, 24⟩, ⟨2, 18, 6, 2⟩, ⟨2, 18, 5, 4⟩, ⟨2, 18, 4, 6⟩, ⟨2, 18, 3, 8⟩, ⟨2, 18, 2, 10⟩, ⟨2, 18, 1, 12⟩, ⟨2, 18, 0, 14⟩]
  exact AllWinning.cons node_13071 (AllWinning.cons node_12000 (AllWinning.cons node_13121 (AllWinning.cons node_12128 (AllWinning.cons node_11131 (AllWinning.cons node_10067 (AllWinning.cons node_9095 (AllWinning.cons node_8120 (AllWinning.cons node_7165 (AllWinning.cons node_6239 (AllWinning.cons node_5492 (AllWinning.cons node_4767 (AllWinning.cons node_4076 (AllWinning.cons node_3506 (AllWinning.cons node_13124 (AllWinning.cons node_12138 (AllWinning.cons node_11143 (AllWinning.cons node_10082 (AllWinning.cons node_9116 (AllWinning.cons node_8142 (AllWinning.cons node_7198 (AllWinning.nil)))))))))))))))))))))

theorem node_14092 : Outcome ⟨2, 18, 7, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 7, 2⟩, ⟨0, 18, 7, 4⟩, ⟨2, 17, 7, 2⟩, ⟨2, 16, 7, 4⟩, ⟨2, 15, 7, 6⟩, ⟨2, 14, 7, 8⟩, ⟨2, 13, 7, 10⟩, ⟨2, 12, 7, 12⟩, ⟨2, 11, 7, 14⟩, ⟨2, 10, 7, 16⟩, ⟨2, 9, 7, 18⟩, ⟨2, 8, 7, 20⟩, ⟨2, 7, 7, 22⟩, ⟨2, 6, 7, 24⟩, ⟨2, 5, 7, 26⟩, ⟨2, 4, 7, 28⟩, ⟨2, 18, 6, 2⟩, ⟨2, 18, 5, 4⟩, ⟨2, 18, 4, 6⟩, ⟨2, 18, 3, 8⟩, ⟨2, 18, 2, 10⟩, ⟨2, 18, 1, 12⟩, ⟨2, 18, 0, 14⟩]
  exact AllWinning.cons node_13071 (AllWinning.cons node_12000 (AllWinning.cons node_13121 (AllWinning.cons node_12128 (AllWinning.cons node_11131 (AllWinning.cons node_10067 (AllWinning.cons node_9095 (AllWinning.cons node_8120 (AllWinning.cons node_7165 (AllWinning.cons node_6239 (AllWinning.cons node_5492 (AllWinning.cons node_4767 (AllWinning.cons node_4076 (AllWinning.cons node_3506 (AllWinning.cons node_2961 (AllWinning.cons node_2500 (AllWinning.cons node_13124 (AllWinning.cons node_12138 (AllWinning.cons node_11143 (AllWinning.cons node_10082 (AllWinning.cons node_9116 (AllWinning.cons node_8142 (AllWinning.cons node_7198 (AllWinning.nil)))))))))))))))))))))))

theorem node_14093 : Outcome ⟨2, 18, 7, 18⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 30⟩) (by decide) node_2008

theorem node_14094 : Outcome ⟨2, 19, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 19, 6, 4⟩) (by decide) node_12004

theorem node_14095 : Outcome ⟨2, 19, 6, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 16⟩) (by decide) node_6248

theorem node_14096 : Outcome ⟨2, 20, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 4⟩) (by decide) node_12146

theorem node_14097 : Outcome ⟨2, 20, 5, 8⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 4⟩) (by decide) node_12146

theorem node_14098 : Outcome ⟨3, 4, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 20, 4⟩) (by decide) node_12012

theorem node_14099 : Outcome ⟨3, 4, 20, 16⟩ true :=
  Outcome.win (q := ⟨1, 4, 20, 4⟩) (by decide) node_12012

theorem node_14100 : Outcome ⟨3, 5, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 5, 19, 2⟩, ⟨1, 5, 19, 4⟩, ⟨3, 4, 19, 2⟩, ⟨3, 3, 19, 4⟩, ⟨3, 5, 18, 2⟩, ⟨3, 5, 17, 4⟩]
  exact AllWinning.cons node_13078 (AllWinning.cons node_12014 (AllWinning.cons node_13131 (AllWinning.cons node_12156 (AllWinning.cons node_13134 (AllWinning.cons node_12162 (AllWinning.nil))))))

theorem node_14101 : Outcome ⟨3, 5, 19, 4⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 8⟩) (by decide) node_10092

theorem node_14102 : Outcome ⟨3, 5, 19, 12⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 16⟩) (by decide) node_6306

theorem node_14103 : Outcome ⟨3, 5, 19, 14⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 16⟩) (by decide) node_6306

theorem node_14104 : Outcome ⟨3, 6, 18, 8⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 8⟩) (by decide) node_10112

theorem node_14105 : Outcome ⟨3, 6, 18, 14⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 8⟩) (by decide) node_10112

theorem node_14106 : Outcome ⟨3, 6, 18, 18⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 34⟩) (by decide) node_1366

theorem node_14107 : Outcome ⟨3, 7, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 17, 4⟩) (by decide) node_12021

theorem node_14108 : Outcome ⟨3, 7, 17, 14⟩ true :=
  Outcome.win (q := ⟨1, 7, 17, 4⟩) (by decide) node_12021

theorem node_14109 : Outcome ⟨3, 8, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.nil))))))

theorem node_14110 : Outcome ⟨3, 8, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.nil)))))))))))

theorem node_14111 : Outcome ⟨3, 8, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨3, 2, 16, 12⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩, ⟨3, 8, 11, 10⟩, ⟨3, 8, 10, 12⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_9136 (AllWinning.cons node_8156 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.cons node_9153 (AllWinning.cons node_8179 (AllWinning.nil)))))))))))))))

theorem node_14112 : Outcome ⟨3, 8, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨3, 2, 16, 12⟩, ⟨3, 1, 16, 14⟩, ⟨3, 0, 16, 16⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩, ⟨3, 8, 11, 10⟩, ⟨3, 8, 10, 12⟩, ⟨3, 8, 9, 14⟩, ⟨3, 8, 8, 16⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_9136 (AllWinning.cons node_8156 (AllWinning.cons node_7204 (AllWinning.cons node_6278 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.cons node_9153 (AllWinning.cons node_8179 (AllWinning.cons node_7232 (AllWinning.cons node_6321 (AllWinning.nil)))))))))))))))))))

theorem node_14113 : Outcome ⟨3, 8, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨3, 2, 16, 12⟩, ⟨3, 1, 16, 14⟩, ⟨3, 0, 16, 16⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩, ⟨3, 8, 11, 10⟩, ⟨3, 8, 10, 12⟩, ⟨3, 8, 9, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 8, 7, 18⟩, ⟨3, 8, 6, 20⟩, ⟨3, 8, 5, 22⟩, ⟨3, 8, 4, 24⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_9136 (AllWinning.cons node_8156 (AllWinning.cons node_7204 (AllWinning.cons node_6278 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.cons node_9153 (AllWinning.cons node_8179 (AllWinning.cons node_7232 (AllWinning.cons node_6321 (AllWinning.cons node_5551 (AllWinning.cons node_4848 (AllWinning.cons node_4131 (AllWinning.cons node_3566 (AllWinning.nil)))))))))))))))))))))))

theorem node_14114 : Outcome ⟨3, 8, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨3, 2, 16, 12⟩, ⟨3, 1, 16, 14⟩, ⟨3, 0, 16, 16⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩, ⟨3, 8, 11, 10⟩, ⟨3, 8, 10, 12⟩, ⟨3, 8, 9, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 8, 7, 18⟩, ⟨3, 8, 6, 20⟩, ⟨3, 8, 5, 22⟩, ⟨3, 8, 4, 24⟩, ⟨3, 8, 3, 26⟩, ⟨3, 8, 2, 28⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_9136 (AllWinning.cons node_8156 (AllWinning.cons node_7204 (AllWinning.cons node_6278 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.cons node_9153 (AllWinning.cons node_8179 (AllWinning.cons node_7232 (AllWinning.cons node_6321 (AllWinning.cons node_5551 (AllWinning.cons node_4848 (AllWinning.cons node_4131 (AllWinning.cons node_3566 (AllWinning.cons node_3029 (AllWinning.cons node_2567 (AllWinning.nil)))))))))))))))))))))))))

theorem node_14115 : Outcome ⟨3, 8, 16, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨3, 2, 16, 12⟩, ⟨3, 1, 16, 14⟩, ⟨3, 0, 16, 16⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩, ⟨3, 8, 11, 10⟩, ⟨3, 8, 10, 12⟩, ⟨3, 8, 9, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 8, 7, 18⟩, ⟨3, 8, 6, 20⟩, ⟨3, 8, 5, 22⟩, ⟨3, 8, 4, 24⟩, ⟨3, 8, 3, 26⟩, ⟨3, 8, 2, 28⟩, ⟨3, 8, 1, 30⟩, ⟨3, 8, 0, 32⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_9136 (AllWinning.cons node_8156 (AllWinning.cons node_7204 (AllWinning.cons node_6278 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.cons node_9153 (AllWinning.cons node_8179 (AllWinning.cons node_7232 (AllWinning.cons node_6321 (AllWinning.cons node_5551 (AllWinning.cons node_4848 (AllWinning.cons node_4131 (AllWinning.cons node_3566 (AllWinning.cons node_3029 (AllWinning.cons node_2567 (AllWinning.cons node_2116 (AllWinning.cons node_1714 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14116 : Outcome ⟨3, 8, 16, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨3, 2, 16, 12⟩, ⟨3, 1, 16, 14⟩, ⟨3, 0, 16, 16⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩, ⟨3, 8, 11, 10⟩, ⟨3, 8, 10, 12⟩, ⟨3, 8, 9, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 8, 7, 18⟩, ⟨3, 8, 6, 20⟩, ⟨3, 8, 5, 22⟩, ⟨3, 8, 4, 24⟩, ⟨3, 8, 3, 26⟩, ⟨3, 8, 2, 28⟩, ⟨3, 8, 1, 30⟩, ⟨3, 8, 0, 32⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_9136 (AllWinning.cons node_8156 (AllWinning.cons node_7204 (AllWinning.cons node_6278 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.cons node_9153 (AllWinning.cons node_8179 (AllWinning.cons node_7232 (AllWinning.cons node_6321 (AllWinning.cons node_5551 (AllWinning.cons node_4848 (AllWinning.cons node_4131 (AllWinning.cons node_3566 (AllWinning.cons node_3029 (AllWinning.cons node_2567 (AllWinning.cons node_2116 (AllWinning.cons node_1714 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14117 : Outcome ⟨3, 8, 16, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 16, 2⟩, ⟨1, 8, 16, 4⟩, ⟨0, 8, 16, 6⟩, ⟨3, 7, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨3, 5, 16, 6⟩, ⟨3, 4, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨3, 2, 16, 12⟩, ⟨3, 1, 16, 14⟩, ⟨3, 0, 16, 16⟩, ⟨3, 8, 15, 2⟩, ⟨3, 8, 14, 4⟩, ⟨3, 8, 13, 6⟩, ⟨3, 8, 12, 8⟩, ⟨3, 8, 11, 10⟩, ⟨3, 8, 10, 12⟩, ⟨3, 8, 9, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 8, 7, 18⟩, ⟨3, 8, 6, 20⟩, ⟨3, 8, 5, 22⟩, ⟨3, 8, 4, 24⟩, ⟨3, 8, 3, 26⟩, ⟨3, 8, 2, 28⟩, ⟨3, 8, 1, 30⟩, ⟨3, 8, 0, 32⟩]
  exact AllWinning.cons node_13087 (AllWinning.cons node_12025 (AllWinning.cons node_10990 (AllWinning.cons node_13141 (AllWinning.cons node_12165 (AllWinning.cons node_11163 (AllWinning.cons node_10103 (AllWinning.cons node_9136 (AllWinning.cons node_8156 (AllWinning.cons node_7204 (AllWinning.cons node_6278 (AllWinning.cons node_13144 (AllWinning.cons node_12176 (AllWinning.cons node_11171 (AllWinning.cons node_10120 (AllWinning.cons node_9153 (AllWinning.cons node_8179 (AllWinning.cons node_7232 (AllWinning.cons node_6321 (AllWinning.cons node_5551 (AllWinning.cons node_4848 (AllWinning.cons node_4131 (AllWinning.cons node_3566 (AllWinning.cons node_3029 (AllWinning.cons node_2567 (AllWinning.cons node_2116 (AllWinning.cons node_1714 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14118 : Outcome ⟨3, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 6⟩) (by decide) node_11174

theorem node_14119 : Outcome ⟨3, 9, 15, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 6⟩) (by decide) node_11174

theorem node_14120 : Outcome ⟨3, 9, 15, 12⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 6⟩) (by decide) node_11174

theorem node_14121 : Outcome ⟨3, 9, 15, 18⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 6⟩) (by decide) node_11174

theorem node_14122 : Outcome ⟨3, 10, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 4⟩) (by decide) node_12033

theorem node_14123 : Outcome ⟨3, 10, 14, 8⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 8⟩) (by decide) node_10112

theorem node_14124 : Outcome ⟨3, 10, 14, 14⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 8⟩) (by decide) node_10112

theorem node_14125 : Outcome ⟨3, 11, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 2⟩) (by decide) node_13099

theorem node_14126 : Outcome ⟨3, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 2⟩) (by decide) node_13099

theorem node_14127 : Outcome ⟨3, 11, 13, 12⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 16⟩) (by decide) node_6337

theorem node_14128 : Outcome ⟨3, 12, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 12, 2⟩, ⟨1, 12, 12, 4⟩, ⟨3, 11, 12, 2⟩, ⟨3, 10, 12, 4⟩, ⟨3, 12, 11, 2⟩, ⟨3, 12, 10, 4⟩]
  exact AllWinning.cons node_13103 (AllWinning.cons node_12046 (AllWinning.cons node_13159 (AllWinning.cons node_12182 (AllWinning.cons node_13164 (AllWinning.cons node_12189 (AllWinning.nil))))))

theorem node_14129 : Outcome ⟨3, 12, 12, 6⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 6⟩) (by decide) node_11001

theorem node_14130 : Outcome ⟨3, 12, 12, 8⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 6⟩) (by decide) node_11001

theorem node_14131 : Outcome ⟨3, 12, 12, 16⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 6⟩) (by decide) node_11001

theorem node_14132 : Outcome ⟨3, 13, 11, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 2⟩) (by decide) node_13105

theorem node_14133 : Outcome ⟨3, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 2⟩) (by decide) node_13105

theorem node_14134 : Outcome ⟨3, 13, 11, 12⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 16⟩) (by decide) node_6306

theorem node_14135 : Outcome ⟨3, 14, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 4⟩) (by decide) node_12053

theorem node_14136 : Outcome ⟨3, 14, 10, 8⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 8⟩) (by decide) node_10143

theorem node_14137 : Outcome ⟨3, 14, 10, 14⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 8⟩) (by decide) node_10143

theorem node_14138 : Outcome ⟨3, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 6⟩) (by decide) node_11195

theorem node_14139 : Outcome ⟨3, 15, 9, 6⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 6⟩) (by decide) node_11195

theorem node_14140 : Outcome ⟨3, 15, 9, 12⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 6⟩) (by decide) node_11195

theorem node_14141 : Outcome ⟨3, 15, 9, 18⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 6⟩) (by decide) node_11195

theorem node_14142 : Outcome ⟨3, 16, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.nil))))))

theorem node_14143 : Outcome ⟨3, 16, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.nil)))))))))))

theorem node_14144 : Outcome ⟨3, 16, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 11, 8, 10⟩, ⟨3, 10, 8, 12⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩, ⟨3, 16, 3, 10⟩, ⟨3, 16, 2, 12⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_9166 (AllWinning.cons node_8188 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.cons node_9185 (AllWinning.cons node_8211 (AllWinning.nil)))))))))))))))

theorem node_14145 : Outcome ⟨3, 16, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 11, 8, 10⟩, ⟨3, 10, 8, 12⟩, ⟨3, 9, 8, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩, ⟨3, 16, 3, 10⟩, ⟨3, 16, 2, 12⟩, ⟨3, 16, 1, 14⟩, ⟨3, 16, 0, 16⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_9166 (AllWinning.cons node_8188 (AllWinning.cons node_7237 (AllWinning.cons node_6321 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.cons node_9185 (AllWinning.cons node_8211 (AllWinning.cons node_7263 (AllWinning.cons node_6366 (AllWinning.nil)))))))))))))))))))

theorem node_14146 : Outcome ⟨3, 16, 8, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 11, 8, 10⟩, ⟨3, 10, 8, 12⟩, ⟨3, 9, 8, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 7, 8, 18⟩, ⟨3, 6, 8, 20⟩, ⟨3, 5, 8, 22⟩, ⟨3, 4, 8, 24⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩, ⟨3, 16, 3, 10⟩, ⟨3, 16, 2, 12⟩, ⟨3, 16, 1, 14⟩, ⟨3, 16, 0, 16⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_9166 (AllWinning.cons node_8188 (AllWinning.cons node_7237 (AllWinning.cons node_6321 (AllWinning.cons node_5546 (AllWinning.cons node_4838 (AllWinning.cons node_4117 (AllWinning.cons node_3552 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.cons node_9185 (AllWinning.cons node_8211 (AllWinning.cons node_7263 (AllWinning.cons node_6366 (AllWinning.nil)))))))))))))))))))))))

theorem node_14147 : Outcome ⟨3, 16, 8, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 11, 8, 10⟩, ⟨3, 10, 8, 12⟩, ⟨3, 9, 8, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 7, 8, 18⟩, ⟨3, 6, 8, 20⟩, ⟨3, 5, 8, 22⟩, ⟨3, 4, 8, 24⟩, ⟨3, 3, 8, 26⟩, ⟨3, 2, 8, 28⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩, ⟨3, 16, 3, 10⟩, ⟨3, 16, 2, 12⟩, ⟨3, 16, 1, 14⟩, ⟨3, 16, 0, 16⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_9166 (AllWinning.cons node_8188 (AllWinning.cons node_7237 (AllWinning.cons node_6321 (AllWinning.cons node_5546 (AllWinning.cons node_4838 (AllWinning.cons node_4117 (AllWinning.cons node_3552 (AllWinning.cons node_3010 (AllWinning.cons node_2543 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.cons node_9185 (AllWinning.cons node_8211 (AllWinning.cons node_7263 (AllWinning.cons node_6366 (AllWinning.nil)))))))))))))))))))))))))

theorem node_14148 : Outcome ⟨3, 16, 8, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 11, 8, 10⟩, ⟨3, 10, 8, 12⟩, ⟨3, 9, 8, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 7, 8, 18⟩, ⟨3, 6, 8, 20⟩, ⟨3, 5, 8, 22⟩, ⟨3, 4, 8, 24⟩, ⟨3, 3, 8, 26⟩, ⟨3, 2, 8, 28⟩, ⟨3, 1, 8, 30⟩, ⟨3, 0, 8, 32⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩, ⟨3, 16, 3, 10⟩, ⟨3, 16, 2, 12⟩, ⟨3, 16, 1, 14⟩, ⟨3, 16, 0, 16⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_9166 (AllWinning.cons node_8188 (AllWinning.cons node_7237 (AllWinning.cons node_6321 (AllWinning.cons node_5546 (AllWinning.cons node_4838 (AllWinning.cons node_4117 (AllWinning.cons node_3552 (AllWinning.cons node_3010 (AllWinning.cons node_2543 (AllWinning.cons node_2064 (AllWinning.cons node_1682 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.cons node_9185 (AllWinning.cons node_8211 (AllWinning.cons node_7263 (AllWinning.cons node_6366 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14149 : Outcome ⟨3, 16, 8, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 11, 8, 10⟩, ⟨3, 10, 8, 12⟩, ⟨3, 9, 8, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 7, 8, 18⟩, ⟨3, 6, 8, 20⟩, ⟨3, 5, 8, 22⟩, ⟨3, 4, 8, 24⟩, ⟨3, 3, 8, 26⟩, ⟨3, 2, 8, 28⟩, ⟨3, 1, 8, 30⟩, ⟨3, 0, 8, 32⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩, ⟨3, 16, 3, 10⟩, ⟨3, 16, 2, 12⟩, ⟨3, 16, 1, 14⟩, ⟨3, 16, 0, 16⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_9166 (AllWinning.cons node_8188 (AllWinning.cons node_7237 (AllWinning.cons node_6321 (AllWinning.cons node_5546 (AllWinning.cons node_4838 (AllWinning.cons node_4117 (AllWinning.cons node_3552 (AllWinning.cons node_3010 (AllWinning.cons node_2543 (AllWinning.cons node_2064 (AllWinning.cons node_1682 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.cons node_9185 (AllWinning.cons node_8211 (AllWinning.cons node_7263 (AllWinning.cons node_6366 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14150 : Outcome ⟨3, 16, 8, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 8, 2⟩, ⟨1, 16, 8, 4⟩, ⟨0, 16, 8, 6⟩, ⟨3, 15, 8, 2⟩, ⟨3, 14, 8, 4⟩, ⟨3, 13, 8, 6⟩, ⟨3, 12, 8, 8⟩, ⟨3, 11, 8, 10⟩, ⟨3, 10, 8, 12⟩, ⟨3, 9, 8, 14⟩, ⟨3, 8, 8, 16⟩, ⟨3, 7, 8, 18⟩, ⟨3, 6, 8, 20⟩, ⟨3, 5, 8, 22⟩, ⟨3, 4, 8, 24⟩, ⟨3, 3, 8, 26⟩, ⟨3, 2, 8, 28⟩, ⟨3, 1, 8, 30⟩, ⟨3, 0, 8, 32⟩, ⟨3, 16, 7, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 16, 5, 6⟩, ⟨3, 16, 4, 8⟩, ⟨3, 16, 3, 10⟩, ⟨3, 16, 2, 12⟩, ⟨3, 16, 1, 14⟩, ⟨3, 16, 0, 16⟩]
  exact AllWinning.cons node_13117 (AllWinning.cons node_12067 (AllWinning.cons node_11017 (AllWinning.cons node_13180 (AllWinning.cons node_12192 (AllWinning.cons node_11205 (AllWinning.cons node_10134 (AllWinning.cons node_9166 (AllWinning.cons node_8188 (AllWinning.cons node_7237 (AllWinning.cons node_6321 (AllWinning.cons node_5546 (AllWinning.cons node_4838 (AllWinning.cons node_4117 (AllWinning.cons node_3552 (AllWinning.cons node_3010 (AllWinning.cons node_2543 (AllWinning.cons node_2064 (AllWinning.cons node_1682 (AllWinning.cons node_13184 (AllWinning.cons node_12203 (AllWinning.cons node_11214 (AllWinning.cons node_10152 (AllWinning.cons node_9185 (AllWinning.cons node_8211 (AllWinning.cons node_7263 (AllWinning.cons node_6366 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14151 : Outcome ⟨3, 17, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 7, 4⟩) (by decide) node_12071

theorem node_14152 : Outcome ⟨3, 17, 7, 14⟩ true :=
  Outcome.win (q := ⟨1, 17, 7, 4⟩) (by decide) node_12071

theorem node_14153 : Outcome ⟨3, 18, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 18, 6, 2⟩, ⟨1, 18, 6, 4⟩, ⟨3, 17, 6, 2⟩, ⟨3, 16, 6, 4⟩, ⟨3, 18, 5, 2⟩, ⟨3, 18, 4, 4⟩]
  exact AllWinning.cons node_13124 (AllWinning.cons node_12074 (AllWinning.cons node_13187 (AllWinning.cons node_12203 (AllWinning.cons node_13191 (AllWinning.cons node_12211 (AllWinning.nil))))))

theorem node_14154 : Outcome ⟨3, 18, 6, 8⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 8⟩) (by decide) node_10143

theorem node_14155 : Outcome ⟨3, 18, 6, 14⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 8⟩) (by decide) node_10143

theorem node_14156 : Outcome ⟨3, 18, 6, 18⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 34⟩) (by decide) node_1335

theorem node_14157 : Outcome ⟨3, 19, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 19, 5, 2⟩, ⟨1, 19, 5, 4⟩, ⟨3, 18, 5, 2⟩, ⟨3, 17, 5, 4⟩, ⟨3, 19, 4, 2⟩, ⟨3, 19, 3, 4⟩]
  exact AllWinning.cons node_13127 (AllWinning.cons node_12076 (AllWinning.cons node_13191 (AllWinning.cons node_12207 (AllWinning.cons node_13195 (AllWinning.cons node_12214 (AllWinning.nil))))))

theorem node_14158 : Outcome ⟨3, 19, 5, 4⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 8⟩) (by decide) node_10163

theorem node_14159 : Outcome ⟨3, 19, 5, 12⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 16⟩) (by decide) node_6337

theorem node_14160 : Outcome ⟨3, 19, 5, 14⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 16⟩) (by decide) node_6337

theorem node_14161 : Outcome ⟨3, 20, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 20, 4, 4⟩) (by decide) node_12081

theorem node_14162 : Outcome ⟨3, 20, 4, 16⟩ true :=
  Outcome.win (q := ⟨1, 20, 4, 4⟩) (by decide) node_12081

theorem node_14163 : Outcome ⟨4, 3, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 4⟩) (by decide) node_12083

theorem node_14164 : Outcome ⟨4, 4, 19, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 19, 4⟩) (by decide) node_12089

theorem node_14165 : Outcome ⟨4, 4, 19, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 38⟩) (by decide) node_861

theorem node_14166 : Outcome ⟨4, 5, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 18, 2⟩) (by decide) node_13202

theorem node_14167 : Outcome ⟨4, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 8⟩) (by decide) node_9878

theorem node_14168 : Outcome ⟨4, 5, 18, 12⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 22⟩) (by decide) node_4180

theorem node_14169 : Outcome ⟨4, 5, 18, 16⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 22⟩) (by decide) node_4180

theorem node_14170 : Outcome ⟨4, 6, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 6, 17, 4⟩) (by decide) node_12097

theorem node_14171 : Outcome ⟨4, 6, 17, 10⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 14⟩) (by decide) node_7299

theorem node_14172 : Outcome ⟨4, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 4⟩) (by decide) node_12240

theorem node_14173 : Outcome ⟨4, 7, 16, 14⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 22⟩) (by decide) node_4197

theorem node_14174 : Outcome ⟨4, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 6, 15, 4⟩) (by decide) node_12237

theorem node_14175 : Outcome ⟨4, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 15, 4⟩) (by decide) node_12237

theorem node_14176 : Outcome ⟨4, 9, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 4⟩) (by decide) node_12240

theorem node_14177 : Outcome ⟨4, 9, 14, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 4⟩) (by decide) node_12240

theorem node_14178 : Outcome ⟨4, 9, 14, 20⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 4⟩) (by decide) node_12240

theorem node_14179 : Outcome ⟨4, 10, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 4⟩) (by decide) node_12247

theorem node_14180 : Outcome ⟨4, 10, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 4⟩) (by decide) node_12247

theorem node_14181 : Outcome ⟨4, 10, 13, 12⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 14⟩) (by decide) node_7319

theorem node_14182 : Outcome ⟨4, 11, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 4⟩) (by decide) node_12251

theorem node_14183 : Outcome ⟨4, 11, 12, 12⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 4⟩) (by decide) node_12251

theorem node_14184 : Outcome ⟨4, 12, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 4⟩) (by decide) node_12247

theorem node_14185 : Outcome ⟨4, 12, 11, 12⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 4⟩) (by decide) node_12247

theorem node_14186 : Outcome ⟨4, 13, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 4⟩) (by decide) node_12251

theorem node_14187 : Outcome ⟨4, 13, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 4⟩) (by decide) node_12251

theorem node_14188 : Outcome ⟨4, 13, 10, 12⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 14⟩) (by decide) node_7299

theorem node_14189 : Outcome ⟨4, 14, 9, 2⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 4⟩) (by decide) node_12259

theorem node_14190 : Outcome ⟨4, 14, 9, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 4⟩) (by decide) node_12259

theorem node_14191 : Outcome ⟨4, 14, 9, 20⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 4⟩) (by decide) node_12259

theorem node_14192 : Outcome ⟨4, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 6, 4⟩) (by decide) node_12262

theorem node_14193 : Outcome ⟨4, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 15, 6, 4⟩) (by decide) node_12262

theorem node_14194 : Outcome ⟨4, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 4⟩) (by decide) node_12259

theorem node_14195 : Outcome ⟨4, 16, 7, 14⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 22⟩) (by decide) node_4180

theorem node_14196 : Outcome ⟨4, 17, 6, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 6, 4⟩) (by decide) node_12134

theorem node_14197 : Outcome ⟨4, 17, 6, 10⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 14⟩) (by decide) node_7319

theorem node_14198 : Outcome ⟨4, 18, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 5, 2⟩) (by decide) node_13235

theorem node_14199 : Outcome ⟨4, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 8⟩) (by decide) node_9924

theorem node_14200 : Outcome ⟨4, 18, 5, 12⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 22⟩) (by decide) node_4197

theorem node_14201 : Outcome ⟨4, 18, 5, 16⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 22⟩) (by decide) node_4197

theorem node_14202 : Outcome ⟨4, 19, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 19, 4, 4⟩) (by decide) node_12143

theorem node_14203 : Outcome ⟨4, 19, 4, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 38⟩) (by decide) node_835

theorem node_14204 : Outcome ⟨4, 20, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 4⟩) (by decide) node_12146

theorem node_14205 : Outcome ⟨5, 2, 20, 4⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 4⟩) (by decide) node_12151

theorem node_14206 : Outcome ⟨5, 2, 20, 8⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 4⟩) (by decide) node_12151

theorem node_14207 : Outcome ⟨5, 3, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 19, 2⟩, ⟨3, 3, 19, 4⟩, ⟨5, 2, 19, 2⟩, ⟨5, 1, 19, 4⟩, ⟨5, 3, 18, 2⟩, ⟨5, 3, 17, 4⟩]
  exact AllWinning.cons node_13199 (AllWinning.cons node_12156 (AllWinning.cons node_13246 (AllWinning.cons node_12281 (AllWinning.cons node_13249 (AllWinning.cons node_12290 (AllWinning.nil))))))

theorem node_14208 : Outcome ⟨5, 3, 19, 4⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 8⟩) (by decide) node_9937

theorem node_14209 : Outcome ⟨5, 3, 19, 12⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 16⟩) (by decide) node_6439

theorem node_14210 : Outcome ⟨5, 3, 19, 14⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 16⟩) (by decide) node_6439

theorem node_14211 : Outcome ⟨5, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 18, 2⟩) (by decide) node_13202

theorem node_14212 : Outcome ⟨5, 4, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 8⟩) (by decide) node_10249

theorem node_14213 : Outcome ⟨5, 4, 18, 12⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 22⟩) (by decide) node_4246

theorem node_14214 : Outcome ⟨5, 4, 18, 16⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 22⟩) (by decide) node_4246

theorem node_14215 : Outcome ⟨5, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 17, 2⟩) (by decide) node_13205

theorem node_14216 : Outcome ⟨5, 5, 17, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 8⟩) (by decide) node_10271

theorem node_14217 : Outcome ⟨5, 6, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 6, 16, 2⟩, ⟨3, 6, 16, 4⟩, ⟨5, 5, 16, 2⟩, ⟨5, 4, 16, 4⟩, ⟨5, 6, 15, 2⟩, ⟨5, 6, 14, 4⟩]
  exact AllWinning.cons node_13208 (AllWinning.cons node_12165 (AllWinning.cons node_13255 (AllWinning.cons node_12294 (AllWinning.cons node_13257 (AllWinning.cons node_12297 (AllWinning.nil))))))

theorem node_14218 : Outcome ⟨5, 6, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 8⟩) (by decide) node_9954

theorem node_14219 : Outcome ⟨5, 6, 16, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 8⟩) (by decide) node_9954

theorem node_14220 : Outcome ⟨5, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 4⟩) (by decide) node_12169

theorem node_14221 : Outcome ⟨5, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 4⟩) (by decide) node_12169

theorem node_14222 : Outcome ⟨5, 7, 15, 14⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 22⟩) (by decide) node_4263

theorem node_14223 : Outcome ⟨5, 8, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 13, 2⟩) (by decide) node_13262

theorem node_14224 : Outcome ⟨5, 9, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 9, 13, 2⟩) (by decide) node_13215

theorem node_14225 : Outcome ⟨5, 9, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 8⟩) (by decide) node_10271

theorem node_14226 : Outcome ⟨5, 9, 13, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 8⟩) (by decide) node_10271

theorem node_14227 : Outcome ⟨5, 10, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 12, 2⟩, ⟨3, 10, 12, 4⟩, ⟨5, 9, 12, 2⟩, ⟨5, 8, 12, 4⟩, ⟨5, 10, 11, 2⟩, ⟨5, 10, 10, 4⟩]
  exact AllWinning.cons node_13217 (AllWinning.cons node_12182 (AllWinning.cons node_13264 (AllWinning.cons node_12303 (AllWinning.cons node_13267 (AllWinning.cons node_12309 (AllWinning.nil))))))

theorem node_14228 : Outcome ⟨5, 10, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 12, 2⟩, ⟨3, 10, 12, 4⟩, ⟨2, 10, 12, 6⟩, ⟨1, 10, 12, 8⟩, ⟨5, 9, 12, 2⟩, ⟨5, 8, 12, 4⟩, ⟨5, 7, 12, 6⟩, ⟨5, 6, 12, 8⟩, ⟨5, 10, 11, 2⟩, ⟨5, 10, 10, 4⟩, ⟨5, 10, 9, 6⟩, ⟨5, 10, 8, 8⟩]
  exact AllWinning.cons node_13217 (AllWinning.cons node_12182 (AllWinning.cons node_11115 (AllWinning.cons node_9974 (AllWinning.cons node_13264 (AllWinning.cons node_12303 (AllWinning.cons node_11319 (AllWinning.cons node_10275 (AllWinning.cons node_13267 (AllWinning.cons node_12309 (AllWinning.cons node_11332 (AllWinning.cons node_10295 (AllWinning.nil))))))))))))

theorem node_14229 : Outcome ⟨5, 10, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 12, 2⟩, ⟨3, 10, 12, 4⟩, ⟨2, 10, 12, 6⟩, ⟨1, 10, 12, 8⟩, ⟨0, 10, 12, 10⟩, ⟨5, 9, 12, 2⟩, ⟨5, 8, 12, 4⟩, ⟨5, 7, 12, 6⟩, ⟨5, 6, 12, 8⟩, ⟨5, 5, 12, 10⟩, ⟨5, 4, 12, 12⟩, ⟨5, 10, 11, 2⟩, ⟨5, 10, 10, 4⟩, ⟨5, 10, 9, 6⟩, ⟨5, 10, 8, 8⟩, ⟨5, 10, 7, 10⟩, ⟨5, 10, 6, 12⟩]
  exact AllWinning.cons node_13217 (AllWinning.cons node_12182 (AllWinning.cons node_11115 (AllWinning.cons node_9974 (AllWinning.cons node_8937 (AllWinning.cons node_13264 (AllWinning.cons node_12303 (AllWinning.cons node_11319 (AllWinning.cons node_10275 (AllWinning.cons node_9289 (AllWinning.cons node_8301 (AllWinning.cons node_13267 (AllWinning.cons node_12309 (AllWinning.cons node_11332 (AllWinning.cons node_10295 (AllWinning.cons node_9309 (AllWinning.cons node_8323 (AllWinning.nil)))))))))))))))))

end RQ9F1
