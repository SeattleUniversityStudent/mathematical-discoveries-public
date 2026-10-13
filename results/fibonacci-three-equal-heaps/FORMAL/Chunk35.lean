import Chunk34
set_option autoImplicit false
namespace RQ9F1

theorem node_8036 : Outcome ⟨1, 12, 8, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 1, 8, 22⟩, ⟨1, 0, 8, 24⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_1214 (AllWinning.cons node_955 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))))

theorem node_8037 : Outcome ⟨1, 12, 8, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 8, 2⟩, ⟨1, 11, 8, 2⟩, ⟨1, 10, 8, 4⟩, ⟨1, 9, 8, 6⟩, ⟨1, 8, 8, 8⟩, ⟨1, 7, 8, 10⟩, ⟨1, 6, 8, 12⟩, ⟨1, 5, 8, 14⟩, ⟨1, 4, 8, 16⟩, ⟨1, 3, 8, 18⟩, ⟨1, 2, 8, 20⟩, ⟨1, 1, 8, 22⟩, ⟨1, 0, 8, 24⟩, ⟨1, 12, 7, 2⟩, ⟨1, 12, 6, 4⟩, ⟨1, 12, 5, 6⟩, ⟨1, 12, 4, 8⟩, ⟨1, 12, 3, 10⟩, ⟨1, 12, 2, 12⟩, ⟨1, 12, 1, 14⟩, ⟨1, 12, 0, 16⟩]
  exact AllWinning.cons node_6994 (AllWinning.cons node_7074 (AllWinning.cons node_6158 (AllWinning.cons node_5424 (AllWinning.cons node_4684 (AllWinning.cons node_4025 (AllWinning.cons node_3428 (AllWinning.cons node_2908 (AllWinning.cons node_2450 (AllWinning.cons node_1943 (AllWinning.cons node_1605 (AllWinning.cons node_1214 (AllWinning.cons node_955 (AllWinning.cons node_7077 (AllWinning.cons node_6175 (AllWinning.cons node_5434 (AllWinning.cons node_4699 (AllWinning.cons node_4041 (AllWinning.cons node_3462 (AllWinning.cons node_2934 (AllWinning.cons node_2478 (AllWinning.nil)))))))))))))))))))))

theorem node_8038 : Outcome ⟨1, 13, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 4⟩) (by decide) node_6163

theorem node_8039 : Outcome ⟨1, 13, 7, 8⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 12⟩) (by decide) node_3469

theorem node_8040 : Outcome ⟨1, 13, 7, 16⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 12⟩) (by decide) node_3469

theorem node_8041 : Outcome ⟨1, 13, 7, 20⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 12⟩) (by decide) node_3469

theorem node_8042 : Outcome ⟨1, 14, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 6, 2⟩) (by decide) node_7001

theorem node_8043 : Outcome ⟨1, 14, 6, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 12⟩) (by decide) node_3475

theorem node_8044 : Outcome ⟨1, 14, 6, 24⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 22⟩) (by decide) node_1229

theorem node_8045 : Outcome ⟨1, 15, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 5, 2⟩) (by decide) node_7083

theorem node_8046 : Outcome ⟨1, 15, 5, 12⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 12⟩) (by decide) node_3441

theorem node_8047 : Outcome ⟨1, 15, 5, 14⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 12⟩) (by decide) node_3441

theorem node_8048 : Outcome ⟨1, 15, 5, 22⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 12⟩) (by decide) node_3441

theorem node_8049 : Outcome ⟨1, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 2⟩) (by decide) node_7087

theorem node_8050 : Outcome ⟨1, 16, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 2⟩) (by decide) node_7087

theorem node_8051 : Outcome ⟨1, 16, 4, 16⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 28⟩) (by decide) node_517

theorem node_8052 : Outcome ⟨1, 16, 4, 22⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 28⟩) (by decide) node_517

theorem node_8053 : Outcome ⟨1, 17, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 2⟩) (by decide) node_7099

theorem node_8054 : Outcome ⟨1, 17, 3, 8⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 2⟩) (by decide) node_7099

theorem node_8055 : Outcome ⟨1, 17, 3, 20⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 22⟩) (by decide) node_1257

theorem node_8056 : Outcome ⟨1, 17, 3, 26⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 22⟩) (by decide) node_1257

theorem node_8057 : Outcome ⟨1, 18, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 2⟩) (by decide) node_7099

theorem node_8058 : Outcome ⟨1, 18, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 2⟩) (by decide) node_7099

theorem node_8059 : Outcome ⟨1, 18, 2, 12⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 2⟩) (by decide) node_7099

theorem node_8060 : Outcome ⟨1, 18, 2, 30⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 28⟩) (by decide) node_538

theorem node_8061 : Outcome ⟨1, 19, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 19, 1, 2⟩) (by decide) node_7021

theorem node_8062 : Outcome ⟨1, 20, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 0, 2⟩) (by decide) node_7108

theorem node_8063 : Outcome ⟨1, 20, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 12⟩) (by decide) node_3475

theorem node_8064 : Outcome ⟨1, 20, 0, 12⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 12⟩) (by decide) node_3475

theorem node_8065 : Outcome ⟨2, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 19, 2⟩) (by decide) node_7027

theorem node_8066 : Outcome ⟨2, 0, 19, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 8⟩) (by decide) node_4722

theorem node_8067 : Outcome ⟨2, 0, 19, 16⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 8⟩) (by decide) node_4722

theorem node_8068 : Outcome ⟨2, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 18, 2⟩) (by decide) node_7031

theorem node_8069 : Outcome ⟨2, 1, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 18, 2⟩) (by decide) node_7031

theorem node_8070 : Outcome ⟨2, 1, 18, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 18, 2⟩) (by decide) node_7031

theorem node_8071 : Outcome ⟨2, 1, 18, 30⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 28⟩) (by decide) node_568

theorem node_8072 : Outcome ⟨2, 2, 17, 2⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 2⟩) (by decide) node_7033

theorem node_8073 : Outcome ⟨2, 2, 17, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 8⟩) (by decide) node_4733

theorem node_8074 : Outcome ⟨2, 2, 17, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 34⟩) (by decide) node_219

theorem node_8075 : Outcome ⟨2, 3, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 4⟩) (by decide) node_6043

theorem node_8076 : Outcome ⟨2, 3, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 4⟩) (by decide) node_6043

theorem node_8077 : Outcome ⟨2, 3, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 4⟩) (by decide) node_6043

theorem node_8078 : Outcome ⟨2, 3, 16, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 18⟩) (by decide) node_2002

theorem node_8079 : Outcome ⟨2, 3, 16, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 18⟩) (by decide) node_2002

theorem node_8080 : Outcome ⟨2, 3, 16, 30⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 18⟩) (by decide) node_2002

theorem node_8081 : Outcome ⟨2, 4, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 2⟩) (by decide) node_7045

theorem node_8082 : Outcome ⟨2, 4, 15, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 8⟩) (by decide) node_4722

theorem node_8083 : Outcome ⟨2, 4, 15, 10⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 8⟩) (by decide) node_4722

theorem node_8084 : Outcome ⟨2, 5, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 14, 2⟩) (by decide) node_7052

theorem node_8085 : Outcome ⟨2, 5, 14, 14⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 8⟩) (by decide) node_4746

theorem node_8086 : Outcome ⟨2, 6, 13, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 8⟩) (by decide) node_4733

theorem node_8087 : Outcome ⟨2, 6, 13, 10⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 8⟩) (by decide) node_4733

theorem node_8088 : Outcome ⟨2, 6, 13, 24⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 8⟩) (by decide) node_4733

theorem node_8089 : Outcome ⟨2, 7, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 12, 2⟩, ⟨0, 7, 12, 4⟩, ⟨2, 6, 12, 2⟩, ⟨2, 5, 12, 4⟩, ⟨2, 7, 11, 2⟩, ⟨2, 7, 10, 4⟩]
  exact AllWinning.cons node_7060 (AllWinning.cons node_6063 (AllWinning.cons node_7140 (AllWinning.cons node_6213 (AllWinning.cons node_7144 (AllWinning.cons node_6228 (AllWinning.nil))))))

theorem node_8090 : Outcome ⟨2, 7, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 12, 2⟩, ⟨0, 7, 12, 4⟩, ⟨2, 6, 12, 2⟩, ⟨2, 5, 12, 4⟩, ⟨2, 4, 12, 6⟩, ⟨2, 3, 12, 8⟩, ⟨2, 7, 11, 2⟩, ⟨2, 7, 10, 4⟩, ⟨2, 7, 9, 6⟩, ⟨2, 7, 8, 8⟩]
  exact AllWinning.cons node_7060 (AllWinning.cons node_6063 (AllWinning.cons node_7140 (AllWinning.cons node_6213 (AllWinning.cons node_5472 (AllWinning.cons node_4737 (AllWinning.cons node_7144 (AllWinning.cons node_6228 (AllWinning.cons node_5481 (AllWinning.cons node_4761 (AllWinning.nil))))))))))

theorem node_8091 : Outcome ⟨2, 7, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 12, 2⟩, ⟨0, 7, 12, 4⟩, ⟨2, 6, 12, 2⟩, ⟨2, 5, 12, 4⟩, ⟨2, 4, 12, 6⟩, ⟨2, 3, 12, 8⟩, ⟨2, 2, 12, 10⟩, ⟨2, 1, 12, 12⟩, ⟨2, 7, 11, 2⟩, ⟨2, 7, 10, 4⟩, ⟨2, 7, 9, 6⟩, ⟨2, 7, 8, 8⟩, ⟨2, 7, 7, 10⟩, ⟨2, 7, 6, 12⟩]
  exact AllWinning.cons node_7060 (AllWinning.cons node_6063 (AllWinning.cons node_7140 (AllWinning.cons node_6213 (AllWinning.cons node_5472 (AllWinning.cons node_4737 (AllWinning.cons node_4059 (AllWinning.cons node_3485 (AllWinning.cons node_7144 (AllWinning.cons node_6228 (AllWinning.cons node_5481 (AllWinning.cons node_4761 (AllWinning.cons node_4074 (AllWinning.cons node_3509 (AllWinning.nil))))))))))))))

theorem node_8092 : Outcome ⟨2, 7, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 12, 2⟩, ⟨0, 7, 12, 4⟩, ⟨2, 6, 12, 2⟩, ⟨2, 5, 12, 4⟩, ⟨2, 4, 12, 6⟩, ⟨2, 3, 12, 8⟩, ⟨2, 2, 12, 10⟩, ⟨2, 1, 12, 12⟩, ⟨2, 0, 12, 14⟩, ⟨2, 7, 11, 2⟩, ⟨2, 7, 10, 4⟩, ⟨2, 7, 9, 6⟩, ⟨2, 7, 8, 8⟩, ⟨2, 7, 7, 10⟩, ⟨2, 7, 6, 12⟩, ⟨2, 7, 5, 14⟩, ⟨2, 7, 4, 16⟩]
  exact AllWinning.cons node_7060 (AllWinning.cons node_6063 (AllWinning.cons node_7140 (AllWinning.cons node_6213 (AllWinning.cons node_5472 (AllWinning.cons node_4737 (AllWinning.cons node_4059 (AllWinning.cons node_3485 (AllWinning.cons node_2941 (AllWinning.cons node_7144 (AllWinning.cons node_6228 (AllWinning.cons node_5481 (AllWinning.cons node_4761 (AllWinning.cons node_4074 (AllWinning.cons node_3509 (AllWinning.cons node_2968 (AllWinning.cons node_2511 (AllWinning.nil)))))))))))))))))

theorem node_8093 : Outcome ⟨2, 7, 12, 10⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 18⟩) (by decide) node_2032

theorem node_8094 : Outcome ⟨2, 7, 12, 12⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 18⟩) (by decide) node_2032

theorem node_8095 : Outcome ⟨2, 7, 12, 14⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 18⟩) (by decide) node_2032

theorem node_8096 : Outcome ⟨2, 7, 12, 26⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 18⟩) (by decide) node_2032

theorem node_8097 : Outcome ⟨2, 8, 11, 2⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8098 : Outcome ⟨2, 8, 11, 10⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8099 : Outcome ⟨2, 8, 11, 16⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8100 : Outcome ⟨2, 8, 11, 18⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8101 : Outcome ⟨2, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 10, 2⟩) (by decide) node_7066

theorem node_8102 : Outcome ⟨2, 9, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 8⟩) (by decide) node_4746

theorem node_8103 : Outcome ⟨2, 9, 10, 8⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 8⟩) (by decide) node_4746

theorem node_8104 : Outcome ⟨2, 9, 10, 10⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 8⟩) (by decide) node_4746

theorem node_8105 : Outcome ⟨2, 9, 10, 14⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 8⟩) (by decide) node_4746

theorem node_8106 : Outcome ⟨2, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 10, 9, 2⟩) (by decide) node_7070

theorem node_8107 : Outcome ⟨2, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 8⟩) (by decide) node_4775

theorem node_8108 : Outcome ⟨2, 10, 9, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 8⟩) (by decide) node_4775

theorem node_8109 : Outcome ⟨2, 10, 9, 10⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 8⟩) (by decide) node_4775

theorem node_8110 : Outcome ⟨2, 10, 9, 14⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 8⟩) (by decide) node_4775

theorem node_8111 : Outcome ⟨2, 11, 8, 2⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8112 : Outcome ⟨2, 11, 8, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8113 : Outcome ⟨2, 11, 8, 16⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8114 : Outcome ⟨2, 11, 8, 18⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8115 : Outcome ⟨2, 12, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 7, 2⟩, ⟨0, 12, 7, 4⟩, ⟨2, 11, 7, 2⟩, ⟨2, 10, 7, 4⟩, ⟨2, 12, 6, 2⟩, ⟨2, 12, 5, 4⟩]
  exact AllWinning.cons node_7077 (AllWinning.cons node_6083 (AllWinning.cons node_7162 (AllWinning.cons node_6238 (AllWinning.cons node_7168 (AllWinning.cons node_6251 (AllWinning.nil))))))

theorem node_8116 : Outcome ⟨2, 12, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 7, 2⟩, ⟨0, 12, 7, 4⟩, ⟨2, 11, 7, 2⟩, ⟨2, 10, 7, 4⟩, ⟨2, 9, 7, 6⟩, ⟨2, 8, 7, 8⟩, ⟨2, 12, 6, 2⟩, ⟨2, 12, 5, 4⟩, ⟨2, 12, 4, 6⟩, ⟨2, 12, 3, 8⟩]
  exact AllWinning.cons node_7077 (AllWinning.cons node_6083 (AllWinning.cons node_7162 (AllWinning.cons node_6238 (AllWinning.cons node_5490 (AllWinning.cons node_4766 (AllWinning.cons node_7168 (AllWinning.cons node_6251 (AllWinning.cons node_5501 (AllWinning.cons node_4788 (AllWinning.nil))))))))))

theorem node_8117 : Outcome ⟨2, 12, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 7, 2⟩, ⟨0, 12, 7, 4⟩, ⟨2, 11, 7, 2⟩, ⟨2, 10, 7, 4⟩, ⟨2, 9, 7, 6⟩, ⟨2, 8, 7, 8⟩, ⟨2, 7, 7, 10⟩, ⟨2, 6, 7, 12⟩, ⟨2, 12, 6, 2⟩, ⟨2, 12, 5, 4⟩, ⟨2, 12, 4, 6⟩, ⟨2, 12, 3, 8⟩, ⟨2, 12, 2, 10⟩, ⟨2, 12, 1, 12⟩]
  exact AllWinning.cons node_7077 (AllWinning.cons node_6083 (AllWinning.cons node_7162 (AllWinning.cons node_6238 (AllWinning.cons node_5490 (AllWinning.cons node_4766 (AllWinning.cons node_4074 (AllWinning.cons node_3505 (AllWinning.cons node_7168 (AllWinning.cons node_6251 (AllWinning.cons node_5501 (AllWinning.cons node_4788 (AllWinning.cons node_4090 (AllWinning.cons node_3531 (AllWinning.nil))))))))))))))

theorem node_8118 : Outcome ⟨2, 12, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 7, 2⟩, ⟨0, 12, 7, 4⟩, ⟨2, 11, 7, 2⟩, ⟨2, 10, 7, 4⟩, ⟨2, 9, 7, 6⟩, ⟨2, 8, 7, 8⟩, ⟨2, 7, 7, 10⟩, ⟨2, 6, 7, 12⟩, ⟨2, 5, 7, 14⟩, ⟨2, 4, 7, 16⟩, ⟨2, 12, 6, 2⟩, ⟨2, 12, 5, 4⟩, ⟨2, 12, 4, 6⟩, ⟨2, 12, 3, 8⟩, ⟨2, 12, 2, 10⟩, ⟨2, 12, 1, 12⟩, ⟨2, 12, 0, 14⟩]
  exact AllWinning.cons node_7077 (AllWinning.cons node_6083 (AllWinning.cons node_7162 (AllWinning.cons node_6238 (AllWinning.cons node_5490 (AllWinning.cons node_4766 (AllWinning.cons node_4074 (AllWinning.cons node_3505 (AllWinning.cons node_2960 (AllWinning.cons node_2499 (AllWinning.cons node_7168 (AllWinning.cons node_6251 (AllWinning.cons node_5501 (AllWinning.cons node_4788 (AllWinning.cons node_4090 (AllWinning.cons node_3531 (AllWinning.cons node_2988 (AllWinning.nil)))))))))))))))))

theorem node_8119 : Outcome ⟨2, 12, 7, 10⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 18⟩) (by decide) node_2002

theorem node_8120 : Outcome ⟨2, 12, 7, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 18⟩) (by decide) node_2002

theorem node_8121 : Outcome ⟨2, 12, 7, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 18⟩) (by decide) node_2002

theorem node_8122 : Outcome ⟨2, 12, 7, 26⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 18⟩) (by decide) node_2002

theorem node_8123 : Outcome ⟨2, 13, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 8⟩) (by decide) node_4795

theorem node_8124 : Outcome ⟨2, 13, 6, 10⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 8⟩) (by decide) node_4795

theorem node_8125 : Outcome ⟨2, 13, 6, 24⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 8⟩) (by decide) node_4795

theorem node_8126 : Outcome ⟨2, 14, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 5, 2⟩) (by decide) node_7083

theorem node_8127 : Outcome ⟨2, 14, 5, 14⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 8⟩) (by decide) node_4775

theorem node_8128 : Outcome ⟨2, 15, 4, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 2⟩) (by decide) node_7087

theorem node_8129 : Outcome ⟨2, 15, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 8⟩) (by decide) node_4805

theorem node_8130 : Outcome ⟨2, 15, 4, 10⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 8⟩) (by decide) node_4805

theorem node_8131 : Outcome ⟨2, 16, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 4⟩) (by decide) node_6101

theorem node_8132 : Outcome ⟨2, 16, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 4⟩) (by decide) node_6101

theorem node_8133 : Outcome ⟨2, 16, 3, 8⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 4⟩) (by decide) node_6101

theorem node_8134 : Outcome ⟨2, 16, 3, 12⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 18⟩) (by decide) node_2032

theorem node_8135 : Outcome ⟨2, 16, 3, 14⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 18⟩) (by decide) node_2032

theorem node_8136 : Outcome ⟨2, 16, 3, 30⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 18⟩) (by decide) node_2032

theorem node_8137 : Outcome ⟨2, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 2⟩) (by decide) node_7099

theorem node_8138 : Outcome ⟨2, 17, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 8⟩) (by decide) node_4795

theorem node_8139 : Outcome ⟨2, 17, 2, 18⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 34⟩) (by decide) node_198

theorem node_8140 : Outcome ⟨2, 18, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 1, 2⟩) (by decide) node_7106

theorem node_8141 : Outcome ⟨2, 18, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 18, 1, 2⟩) (by decide) node_7106

theorem node_8142 : Outcome ⟨2, 18, 1, 12⟩ true :=
  Outcome.win (q := ⟨1, 18, 1, 2⟩) (by decide) node_7106

theorem node_8143 : Outcome ⟨2, 18, 1, 30⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 28⟩) (by decide) node_590

theorem node_8144 : Outcome ⟨2, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 0, 2⟩) (by decide) node_7108

theorem node_8145 : Outcome ⟨2, 19, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 8⟩) (by decide) node_4805

theorem node_8146 : Outcome ⟨2, 19, 0, 16⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 8⟩) (by decide) node_4805

theorem node_8147 : Outcome ⟨3, 0, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 4⟩) (by decide) node_6273

theorem node_8148 : Outcome ⟨3, 0, 18, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 4⟩) (by decide) node_6273

theorem node_8149 : Outcome ⟨3, 0, 18, 30⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 30⟩) (by decide) node_416

theorem node_8150 : Outcome ⟨3, 1, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 2⟩) (by decide) node_7116

theorem node_8151 : Outcome ⟨3, 1, 17, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 2⟩) (by decide) node_7116

theorem node_8152 : Outcome ⟨3, 1, 17, 20⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 22⟩) (by decide) node_1329

theorem node_8153 : Outcome ⟨3, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 4⟩) (by decide) node_6273

theorem node_8154 : Outcome ⟨3, 2, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 4⟩) (by decide) node_6273

theorem node_8155 : Outcome ⟨3, 2, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 4⟩) (by decide) node_6273

theorem node_8156 : Outcome ⟨3, 2, 16, 12⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 18⟩) (by decide) node_2073

theorem node_8157 : Outcome ⟨3, 2, 16, 14⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 18⟩) (by decide) node_2073

theorem node_8158 : Outcome ⟨3, 3, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8159 : Outcome ⟨3, 3, 15, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8160 : Outcome ⟨3, 3, 15, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8161 : Outcome ⟨3, 3, 15, 30⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 30⟩) (by decide) node_439

theorem node_8162 : Outcome ⟨3, 4, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 2⟩) (by decide) node_7129

theorem node_8163 : Outcome ⟨3, 4, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 2⟩) (by decide) node_7129

theorem node_8164 : Outcome ⟨3, 4, 14, 32⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 2⟩) (by decide) node_7129

theorem node_8165 : Outcome ⟨3, 5, 13, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8166 : Outcome ⟨3, 5, 13, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8167 : Outcome ⟨3, 5, 13, 10⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8168 : Outcome ⟨3, 6, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 6⟩) (by decide) node_5539

theorem node_8169 : Outcome ⟨3, 6, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 6⟩) (by decide) node_5539

theorem node_8170 : Outcome ⟨3, 6, 12, 26⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 22⟩) (by decide) node_1360

theorem node_8171 : Outcome ⟨3, 7, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 4⟩) (by decide) node_6138

theorem node_8172 : Outcome ⟨3, 7, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 4⟩) (by decide) node_6138

theorem node_8173 : Outcome ⟨3, 7, 11, 8⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 4⟩) (by decide) node_6138

theorem node_8174 : Outcome ⟨3, 7, 11, 24⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 18⟩) (by decide) node_2104

theorem node_8175 : Outcome ⟨3, 7, 11, 26⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 18⟩) (by decide) node_2104

theorem node_8176 : Outcome ⟨3, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨2, 8, 10, 2⟩) (by decide) node_7150

theorem node_8177 : Outcome ⟨3, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 8, 10, 2⟩) (by decide) node_7150

theorem node_8178 : Outcome ⟨3, 8, 10, 10⟩ true :=
  Outcome.win (q := ⟨2, 8, 10, 2⟩) (by decide) node_7150

theorem node_8179 : Outcome ⟨3, 8, 10, 12⟩ true :=
  Outcome.win (q := ⟨2, 8, 10, 2⟩) (by decide) node_7150

theorem node_8180 : Outcome ⟨3, 8, 10, 16⟩ true :=
  Outcome.win (q := ⟨2, 8, 10, 2⟩) (by decide) node_7150

theorem node_8181 : Outcome ⟨3, 9, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 9, 2⟩, ⟨1, 9, 9, 4⟩, ⟨3, 8, 9, 2⟩, ⟨3, 7, 9, 4⟩, ⟨3, 9, 8, 2⟩, ⟨3, 9, 7, 4⟩]
  exact AllWinning.cons node_7154 (AllWinning.cons node_6155 (AllWinning.cons node_7228 (AllWinning.cons node_6314 (AllWinning.cons node_7233 (AllWinning.cons node_6323 (AllWinning.nil))))))

theorem node_8182 : Outcome ⟨3, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 6⟩) (by decide) node_5346

theorem node_8183 : Outcome ⟨3, 9, 9, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 6⟩) (by decide) node_5346

theorem node_8184 : Outcome ⟨3, 9, 9, 10⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 6⟩) (by decide) node_5346

theorem node_8185 : Outcome ⟨3, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 8, 2⟩) (by decide) node_7158

theorem node_8186 : Outcome ⟨3, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 8, 2⟩) (by decide) node_7158

theorem node_8187 : Outcome ⟨3, 10, 8, 10⟩ true :=
  Outcome.win (q := ⟨2, 10, 8, 2⟩) (by decide) node_7158

theorem node_8188 : Outcome ⟨3, 10, 8, 12⟩ true :=
  Outcome.win (q := ⟨2, 10, 8, 2⟩) (by decide) node_7158

theorem node_8189 : Outcome ⟨3, 10, 8, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 8, 2⟩) (by decide) node_7158

theorem node_8190 : Outcome ⟨3, 11, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 4⟩) (by decide) node_6163

theorem node_8191 : Outcome ⟨3, 11, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 4⟩) (by decide) node_6163

theorem node_8192 : Outcome ⟨3, 11, 7, 8⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 4⟩) (by decide) node_6163

theorem node_8193 : Outcome ⟨3, 11, 7, 24⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 18⟩) (by decide) node_2073

theorem node_8194 : Outcome ⟨3, 11, 7, 26⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 18⟩) (by decide) node_2073

theorem node_8195 : Outcome ⟨3, 12, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 6⟩) (by decide) node_5554

theorem node_8196 : Outcome ⟨3, 12, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 6⟩) (by decide) node_5554

theorem node_8197 : Outcome ⟨3, 12, 6, 26⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 22⟩) (by decide) node_1329

theorem node_8198 : Outcome ⟨3, 13, 5, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 4⟩) (by decide) node_6331

theorem node_8199 : Outcome ⟨3, 13, 5, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 4⟩) (by decide) node_6331

theorem node_8200 : Outcome ⟨3, 13, 5, 10⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 4⟩) (by decide) node_6331

theorem node_8201 : Outcome ⟨3, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 2⟩) (by decide) node_7175

theorem node_8202 : Outcome ⟨3, 14, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 2⟩) (by decide) node_7175

theorem node_8203 : Outcome ⟨3, 14, 4, 32⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 2⟩) (by decide) node_7175

theorem node_8204 : Outcome ⟨3, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 4⟩) (by decide) node_6346

theorem node_8205 : Outcome ⟨3, 15, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 4⟩) (by decide) node_6346

theorem node_8206 : Outcome ⟨3, 15, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 4⟩) (by decide) node_6346

theorem node_8207 : Outcome ⟨3, 15, 3, 30⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 30⟩) (by decide) node_416

theorem node_8208 : Outcome ⟨3, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 4⟩) (by decide) node_6361

theorem node_8209 : Outcome ⟨3, 16, 2, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 4⟩) (by decide) node_6361

theorem node_8210 : Outcome ⟨3, 16, 2, 8⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 4⟩) (by decide) node_6361

theorem node_8211 : Outcome ⟨3, 16, 2, 12⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 18⟩) (by decide) node_2104

theorem node_8212 : Outcome ⟨3, 16, 2, 14⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 18⟩) (by decide) node_2104

theorem node_8213 : Outcome ⟨3, 17, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 2⟩) (by decide) node_7189

theorem node_8214 : Outcome ⟨3, 17, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 2⟩) (by decide) node_7189

theorem node_8215 : Outcome ⟨3, 17, 1, 20⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 22⟩) (by decide) node_1360

theorem node_8216 : Outcome ⟨3, 18, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 4⟩) (by decide) node_6361

theorem node_8217 : Outcome ⟨3, 18, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 4⟩) (by decide) node_6361

theorem node_8218 : Outcome ⟨3, 18, 0, 30⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 30⟩) (by decide) node_439

theorem node_8219 : Outcome ⟨4, 0, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 17, 2⟩, ⟨2, 0, 17, 4⟩, ⟨4, 0, 16, 2⟩, ⟨4, 0, 15, 4⟩]
  exact AllWinning.cons node_7200 (AllWinning.cons node_6197 (AllWinning.cons node_7266 (AllWinning.cons node_6369 (AllWinning.nil))))

theorem node_8220 : Outcome ⟨4, 0, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 17, 2⟩, ⟨2, 0, 17, 4⟩, ⟨1, 0, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨4, 0, 16, 2⟩, ⟨4, 0, 15, 4⟩, ⟨4, 0, 14, 6⟩, ⟨4, 0, 13, 8⟩]
  exact AllWinning.cons node_7200 (AllWinning.cons node_6197 (AllWinning.cons node_5390 (AllWinning.cons node_4569 (AllWinning.cons node_7266 (AllWinning.cons node_6369 (AllWinning.cons node_5577 (AllWinning.cons node_4875 (AllWinning.nil))))))))

theorem node_8221 : Outcome ⟨4, 0, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 17, 2⟩, ⟨2, 0, 17, 4⟩, ⟨1, 0, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨4, 0, 16, 2⟩, ⟨4, 0, 15, 4⟩, ⟨4, 0, 14, 6⟩, ⟨4, 0, 13, 8⟩, ⟨4, 0, 12, 10⟩, ⟨4, 0, 11, 12⟩]
  exact AllWinning.cons node_7200 (AllWinning.cons node_6197 (AllWinning.cons node_5390 (AllWinning.cons node_4569 (AllWinning.cons node_7266 (AllWinning.cons node_6369 (AllWinning.cons node_5577 (AllWinning.cons node_4875 (AllWinning.cons node_4153 (AllWinning.cons node_3585 (AllWinning.nil))))))))))

theorem node_8222 : Outcome ⟨4, 0, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 17, 2⟩, ⟨2, 0, 17, 4⟩, ⟨1, 0, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨4, 0, 16, 2⟩, ⟨4, 0, 15, 4⟩, ⟨4, 0, 14, 6⟩, ⟨4, 0, 13, 8⟩, ⟨4, 0, 12, 10⟩, ⟨4, 0, 11, 12⟩, ⟨4, 0, 10, 14⟩, ⟨4, 0, 9, 16⟩]
  exact AllWinning.cons node_7200 (AllWinning.cons node_6197 (AllWinning.cons node_5390 (AllWinning.cons node_4569 (AllWinning.cons node_7266 (AllWinning.cons node_6369 (AllWinning.cons node_5577 (AllWinning.cons node_4875 (AllWinning.cons node_4153 (AllWinning.cons node_3585 (AllWinning.cons node_3048 (AllWinning.cons node_2582 (AllWinning.nil))))))))))))

theorem node_8223 : Outcome ⟨4, 0, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 17, 2⟩, ⟨2, 0, 17, 4⟩, ⟨1, 0, 17, 6⟩, ⟨0, 0, 17, 8⟩, ⟨4, 0, 16, 2⟩, ⟨4, 0, 15, 4⟩, ⟨4, 0, 14, 6⟩, ⟨4, 0, 13, 8⟩, ⟨4, 0, 12, 10⟩, ⟨4, 0, 11, 12⟩, ⟨4, 0, 10, 14⟩, ⟨4, 0, 9, 16⟩, ⟨4, 0, 8, 18⟩, ⟨4, 0, 7, 20⟩]
  exact AllWinning.cons node_7200 (AllWinning.cons node_6197 (AllWinning.cons node_5390 (AllWinning.cons node_4569 (AllWinning.cons node_7266 (AllWinning.cons node_6369 (AllWinning.cons node_5577 (AllWinning.cons node_4875 (AllWinning.cons node_4153 (AllWinning.cons node_3585 (AllWinning.cons node_3048 (AllWinning.cons node_2582 (AllWinning.cons node_2124 (AllWinning.cons node_1719 (AllWinning.nil))))))))))))))

theorem node_8224 : Outcome ⟨4, 0, 17, 16⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 26⟩) (by decide) node_832

theorem node_8225 : Outcome ⟨4, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 2⟩) (by decide) node_7270

theorem node_8226 : Outcome ⟨4, 1, 16, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 28⟩) (by decide) node_629

theorem node_8227 : Outcome ⟨4, 1, 16, 22⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 28⟩) (by decide) node_629

theorem node_8228 : Outcome ⟨4, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 2, 15, 2⟩) (by decide) node_7206

theorem node_8229 : Outcome ⟨4, 2, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 8⟩) (by decide) node_4578

theorem node_8230 : Outcome ⟨4, 2, 15, 10⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 8⟩) (by decide) node_4578

theorem node_8231 : Outcome ⟨4, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 2⟩) (by decide) node_7277

theorem node_8232 : Outcome ⟨4, 3, 14, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 2⟩) (by decide) node_7277

theorem node_8233 : Outcome ⟨4, 4, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 13, 2⟩, ⟨2, 4, 13, 4⟩, ⟨4, 3, 13, 2⟩, ⟨4, 2, 13, 4⟩, ⟨4, 4, 12, 2⟩, ⟨4, 4, 11, 4⟩]
  exact AllWinning.cons node_7214 (AllWinning.cons node_6211 (AllWinning.cons node_7284 (AllWinning.cons node_6375 (AllWinning.cons node_7287 (AllWinning.cons node_6382 (AllWinning.nil))))))

theorem node_8234 : Outcome ⟨4, 4, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 13, 2⟩, ⟨2, 4, 13, 4⟩, ⟨1, 4, 13, 6⟩, ⟨0, 4, 13, 8⟩, ⟨4, 3, 13, 2⟩, ⟨4, 2, 13, 4⟩, ⟨4, 1, 13, 6⟩, ⟨4, 0, 13, 8⟩, ⟨4, 4, 12, 2⟩, ⟨4, 4, 11, 4⟩, ⟨4, 4, 10, 6⟩, ⟨4, 4, 9, 8⟩]
  exact AllWinning.cons node_7214 (AllWinning.cons node_6211 (AllWinning.cons node_5405 (AllWinning.cons node_4588 (AllWinning.cons node_7284 (AllWinning.cons node_6375 (AllWinning.cons node_5581 (AllWinning.cons node_4875 (AllWinning.cons node_7287 (AllWinning.cons node_6382 (AllWinning.cons node_5594 (AllWinning.cons node_4890 (AllWinning.nil))))))))))))

theorem node_8235 : Outcome ⟨4, 4, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 13, 2⟩, ⟨2, 4, 13, 4⟩, ⟨1, 4, 13, 6⟩, ⟨0, 4, 13, 8⟩, ⟨4, 3, 13, 2⟩, ⟨4, 2, 13, 4⟩, ⟨4, 1, 13, 6⟩, ⟨4, 0, 13, 8⟩, ⟨4, 4, 12, 2⟩, ⟨4, 4, 11, 4⟩, ⟨4, 4, 10, 6⟩, ⟨4, 4, 9, 8⟩, ⟨4, 4, 8, 10⟩, ⟨4, 4, 7, 12⟩]
  exact AllWinning.cons node_7214 (AllWinning.cons node_6211 (AllWinning.cons node_5405 (AllWinning.cons node_4588 (AllWinning.cons node_7284 (AllWinning.cons node_6375 (AllWinning.cons node_5581 (AllWinning.cons node_4875 (AllWinning.cons node_7287 (AllWinning.cons node_6382 (AllWinning.cons node_5594 (AllWinning.cons node_4890 (AllWinning.cons node_4168 (AllWinning.cons node_3603 (AllWinning.nil))))))))))))))

theorem node_8236 : Outcome ⟨4, 4, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 13, 2⟩, ⟨2, 4, 13, 4⟩, ⟨1, 4, 13, 6⟩, ⟨0, 4, 13, 8⟩, ⟨4, 3, 13, 2⟩, ⟨4, 2, 13, 4⟩, ⟨4, 1, 13, 6⟩, ⟨4, 0, 13, 8⟩, ⟨4, 4, 12, 2⟩, ⟨4, 4, 11, 4⟩, ⟨4, 4, 10, 6⟩, ⟨4, 4, 9, 8⟩, ⟨4, 4, 8, 10⟩, ⟨4, 4, 7, 12⟩, ⟨4, 4, 6, 14⟩, ⟨4, 4, 5, 16⟩]
  exact AllWinning.cons node_7214 (AllWinning.cons node_6211 (AllWinning.cons node_5405 (AllWinning.cons node_4588 (AllWinning.cons node_7284 (AllWinning.cons node_6375 (AllWinning.cons node_5581 (AllWinning.cons node_4875 (AllWinning.cons node_7287 (AllWinning.cons node_6382 (AllWinning.cons node_5594 (AllWinning.cons node_4890 (AllWinning.cons node_4168 (AllWinning.cons node_3603 (AllWinning.cons node_3062 (AllWinning.cons node_2602 (AllWinning.nil))))))))))))))))

theorem node_8237 : Outcome ⟨4, 4, 13, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 13, 2⟩, ⟨2, 4, 13, 4⟩, ⟨1, 4, 13, 6⟩, ⟨0, 4, 13, 8⟩, ⟨4, 3, 13, 2⟩, ⟨4, 2, 13, 4⟩, ⟨4, 1, 13, 6⟩, ⟨4, 0, 13, 8⟩, ⟨4, 4, 12, 2⟩, ⟨4, 4, 11, 4⟩, ⟨4, 4, 10, 6⟩, ⟨4, 4, 9, 8⟩, ⟨4, 4, 8, 10⟩, ⟨4, 4, 7, 12⟩, ⟨4, 4, 6, 14⟩, ⟨4, 4, 5, 16⟩, ⟨4, 4, 4, 18⟩, ⟨4, 4, 3, 20⟩]
  exact AllWinning.cons node_7214 (AllWinning.cons node_6211 (AllWinning.cons node_5405 (AllWinning.cons node_4588 (AllWinning.cons node_7284 (AllWinning.cons node_6375 (AllWinning.cons node_5581 (AllWinning.cons node_4875 (AllWinning.cons node_7287 (AllWinning.cons node_6382 (AllWinning.cons node_5594 (AllWinning.cons node_4890 (AllWinning.cons node_4168 (AllWinning.cons node_3603 (AllWinning.cons node_3062 (AllWinning.cons node_2602 (AllWinning.cons node_2142 (AllWinning.cons node_1737 (AllWinning.nil))))))))))))))))))

theorem node_8238 : Outcome ⟨4, 4, 13, 16⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 26⟩) (by decide) node_858

theorem node_8239 : Outcome ⟨4, 5, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 12, 2⟩, ⟨2, 5, 12, 4⟩, ⟨4, 4, 12, 2⟩, ⟨4, 3, 12, 4⟩, ⟨4, 5, 11, 2⟩, ⟨4, 5, 10, 4⟩]
  exact AllWinning.cons node_7217 (AllWinning.cons node_6213 (AllWinning.cons node_7287 (AllWinning.cons node_6378 (AllWinning.cons node_7289 (AllWinning.cons node_6385 (AllWinning.nil))))))

theorem node_8240 : Outcome ⟨4, 5, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 12, 2⟩, ⟨2, 5, 12, 4⟩, ⟨1, 5, 12, 6⟩, ⟨0, 5, 12, 8⟩, ⟨4, 4, 12, 2⟩, ⟨4, 3, 12, 4⟩, ⟨4, 2, 12, 6⟩, ⟨4, 1, 12, 8⟩, ⟨4, 5, 11, 2⟩, ⟨4, 5, 10, 4⟩, ⟨4, 5, 9, 6⟩, ⟨4, 5, 8, 8⟩]
  exact AllWinning.cons node_7217 (AllWinning.cons node_6213 (AllWinning.cons node_5411 (AllWinning.cons node_4593 (AllWinning.cons node_7287 (AllWinning.cons node_6378 (AllWinning.cons node_5587 (AllWinning.cons node_4881 (AllWinning.cons node_7289 (AllWinning.cons node_6385 (AllWinning.cons node_5596 (AllWinning.cons node_4893 (AllWinning.nil))))))))))))

theorem node_8241 : Outcome ⟨4, 5, 12, 12⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 10⟩) (by decide) node_4174

theorem node_8242 : Outcome ⟨4, 5, 12, 16⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 10⟩) (by decide) node_4174

theorem node_8243 : Outcome ⟨4, 6, 11, 2⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8244 : Outcome ⟨4, 6, 11, 8⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8245 : Outcome ⟨4, 6, 11, 22⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8246 : Outcome ⟨4, 6, 11, 24⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 4⟩) (by decide) node_6218

theorem node_8247 : Outcome ⟨4, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 2⟩) (by decide) node_7223

theorem node_8248 : Outcome ⟨4, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 2⟩) (by decide) node_7223

theorem node_8249 : Outcome ⟨4, 7, 10, 8⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 10⟩) (by decide) node_4191

theorem node_8250 : Outcome ⟨4, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 9, 2⟩) (by decide) node_7304

theorem node_8251 : Outcome ⟨4, 8, 9, 10⟩ true :=
  Outcome.win (q := ⟨4, 7, 9, 2⟩) (by decide) node_7304

theorem node_8252 : Outcome ⟨4, 8, 9, 16⟩ true :=
  Outcome.win (q := ⟨4, 7, 9, 2⟩) (by decide) node_7304

theorem node_8253 : Outcome ⟨4, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 7, 2⟩) (by decide) node_7310

theorem node_8254 : Outcome ⟨4, 9, 8, 10⟩ true :=
  Outcome.win (q := ⟨4, 9, 7, 2⟩) (by decide) node_7310

theorem node_8255 : Outcome ⟨4, 9, 8, 16⟩ true :=
  Outcome.win (q := ⟨4, 9, 7, 2⟩) (by decide) node_7310

theorem node_8256 : Outcome ⟨4, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 2⟩) (by decide) node_7238

theorem node_8257 : Outcome ⟨4, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 2⟩) (by decide) node_7238

theorem node_8258 : Outcome ⟨4, 10, 7, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 10⟩) (by decide) node_4174

theorem node_8259 : Outcome ⟨4, 11, 6, 2⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8260 : Outcome ⟨4, 11, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8261 : Outcome ⟨4, 11, 6, 22⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8262 : Outcome ⟨4, 11, 6, 24⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 4⟩) (by decide) node_6242

theorem node_8263 : Outcome ⟨4, 12, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 5, 2⟩, ⟨2, 12, 5, 4⟩, ⟨4, 11, 5, 2⟩, ⟨4, 10, 5, 4⟩, ⟨4, 12, 4, 2⟩, ⟨4, 12, 3, 4⟩]
  exact AllWinning.cons node_7246 (AllWinning.cons node_6251 (AllWinning.cons node_7324 (AllWinning.cons node_6402 (AllWinning.cons node_7328 (AllWinning.cons node_6410 (AllWinning.nil))))))

theorem node_8264 : Outcome ⟨4, 12, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 5, 2⟩, ⟨2, 12, 5, 4⟩, ⟨1, 12, 5, 6⟩, ⟨0, 12, 5, 8⟩, ⟨4, 11, 5, 2⟩, ⟨4, 10, 5, 4⟩, ⟨4, 9, 5, 6⟩, ⟨4, 8, 5, 8⟩, ⟨4, 12, 4, 2⟩, ⟨4, 12, 3, 4⟩, ⟨4, 12, 2, 6⟩, ⟨4, 12, 1, 8⟩]
  exact AllWinning.cons node_7246 (AllWinning.cons node_6251 (AllWinning.cons node_5434 (AllWinning.cons node_4622 (AllWinning.cons node_7324 (AllWinning.cons node_6402 (AllWinning.cons node_5610 (AllWinning.cons node_4901 (AllWinning.cons node_7328 (AllWinning.cons node_6410 (AllWinning.cons node_5620 (AllWinning.cons node_4916 (AllWinning.nil))))))))))))

theorem node_8265 : Outcome ⟨4, 12, 5, 12⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 10⟩) (by decide) node_4191

theorem node_8266 : Outcome ⟨4, 12, 5, 16⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 10⟩) (by decide) node_4191

theorem node_8267 : Outcome ⟨4, 13, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 4, 2⟩, ⟨2, 13, 4, 4⟩, ⟨4, 12, 4, 2⟩, ⟨4, 11, 4, 4⟩, ⟨4, 13, 3, 2⟩, ⟨4, 13, 2, 4⟩]
  exact AllWinning.cons node_7249 (AllWinning.cons node_6256 (AllWinning.cons node_7328 (AllWinning.cons node_6407 (AllWinning.cons node_7330 (AllWinning.cons node_6414 (AllWinning.nil))))))

theorem node_8268 : Outcome ⟨4, 13, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 4, 2⟩, ⟨2, 13, 4, 4⟩, ⟨1, 13, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨4, 12, 4, 2⟩, ⟨4, 11, 4, 4⟩, ⟨4, 10, 4, 6⟩, ⟨4, 9, 4, 8⟩, ⟨4, 13, 3, 2⟩, ⟨4, 13, 2, 4⟩, ⟨4, 13, 1, 6⟩, ⟨4, 13, 0, 8⟩]
  exact AllWinning.cons node_7249 (AllWinning.cons node_6256 (AllWinning.cons node_5437 (AllWinning.cons node_4626 (AllWinning.cons node_7328 (AllWinning.cons node_6407 (AllWinning.cons node_5615 (AllWinning.cons node_4905 (AllWinning.cons node_7330 (AllWinning.cons node_6414 (AllWinning.cons node_5625 (AllWinning.cons node_4919 (AllWinning.nil))))))))))))

theorem node_8269 : Outcome ⟨4, 13, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 4, 2⟩, ⟨2, 13, 4, 4⟩, ⟨1, 13, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨4, 12, 4, 2⟩, ⟨4, 11, 4, 4⟩, ⟨4, 10, 4, 6⟩, ⟨4, 9, 4, 8⟩, ⟨4, 8, 4, 10⟩, ⟨4, 7, 4, 12⟩, ⟨4, 13, 3, 2⟩, ⟨4, 13, 2, 4⟩, ⟨4, 13, 1, 6⟩, ⟨4, 13, 0, 8⟩]
  exact AllWinning.cons node_7249 (AllWinning.cons node_6256 (AllWinning.cons node_5437 (AllWinning.cons node_4626 (AllWinning.cons node_7328 (AllWinning.cons node_6407 (AllWinning.cons node_5615 (AllWinning.cons node_4905 (AllWinning.cons node_4203 (AllWinning.cons node_3609 (AllWinning.cons node_7330 (AllWinning.cons node_6414 (AllWinning.cons node_5625 (AllWinning.cons node_4919 (AllWinning.nil))))))))))))))

theorem node_8270 : Outcome ⟨4, 13, 4, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 4, 2⟩, ⟨2, 13, 4, 4⟩, ⟨1, 13, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨4, 12, 4, 2⟩, ⟨4, 11, 4, 4⟩, ⟨4, 10, 4, 6⟩, ⟨4, 9, 4, 8⟩, ⟨4, 8, 4, 10⟩, ⟨4, 7, 4, 12⟩, ⟨4, 6, 4, 14⟩, ⟨4, 5, 4, 16⟩, ⟨4, 13, 3, 2⟩, ⟨4, 13, 2, 4⟩, ⟨4, 13, 1, 6⟩, ⟨4, 13, 0, 8⟩]
  exact AllWinning.cons node_7249 (AllWinning.cons node_6256 (AllWinning.cons node_5437 (AllWinning.cons node_4626 (AllWinning.cons node_7328 (AllWinning.cons node_6407 (AllWinning.cons node_5615 (AllWinning.cons node_4905 (AllWinning.cons node_4203 (AllWinning.cons node_3609 (AllWinning.cons node_3069 (AllWinning.cons node_2606 (AllWinning.cons node_7330 (AllWinning.cons node_6414 (AllWinning.cons node_5625 (AllWinning.cons node_4919 (AllWinning.nil))))))))))))))))

theorem node_8271 : Outcome ⟨4, 13, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 4, 2⟩, ⟨2, 13, 4, 4⟩, ⟨1, 13, 4, 6⟩, ⟨0, 13, 4, 8⟩, ⟨4, 12, 4, 2⟩, ⟨4, 11, 4, 4⟩, ⟨4, 10, 4, 6⟩, ⟨4, 9, 4, 8⟩, ⟨4, 8, 4, 10⟩, ⟨4, 7, 4, 12⟩, ⟨4, 6, 4, 14⟩, ⟨4, 5, 4, 16⟩, ⟨4, 4, 4, 18⟩, ⟨4, 3, 4, 20⟩, ⟨4, 13, 3, 2⟩, ⟨4, 13, 2, 4⟩, ⟨4, 13, 1, 6⟩, ⟨4, 13, 0, 8⟩]
  exact AllWinning.cons node_7249 (AllWinning.cons node_6256 (AllWinning.cons node_5437 (AllWinning.cons node_4626 (AllWinning.cons node_7328 (AllWinning.cons node_6407 (AllWinning.cons node_5615 (AllWinning.cons node_4905 (AllWinning.cons node_4203 (AllWinning.cons node_3609 (AllWinning.cons node_3069 (AllWinning.cons node_2606 (AllWinning.cons node_2142 (AllWinning.cons node_1733 (AllWinning.cons node_7330 (AllWinning.cons node_6414 (AllWinning.cons node_5625 (AllWinning.cons node_4919 (AllWinning.nil))))))))))))))))))

theorem node_8272 : Outcome ⟨4, 13, 4, 16⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 26⟩) (by decide) node_832

theorem node_8273 : Outcome ⟨4, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 2⟩) (by decide) node_7333

theorem node_8274 : Outcome ⟨4, 14, 3, 8⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 2⟩) (by decide) node_7333

theorem node_8275 : Outcome ⟨4, 15, 2, 2⟩ true :=
  Outcome.win (q := ⟨3, 15, 2, 2⟩) (by decide) node_7255

theorem node_8276 : Outcome ⟨4, 15, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 8⟩) (by decide) node_4637

theorem node_8277 : Outcome ⟨4, 15, 2, 10⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 8⟩) (by decide) node_4637

theorem node_8278 : Outcome ⟨4, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 2⟩) (by decide) node_7340

theorem node_8279 : Outcome ⟨4, 16, 1, 16⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 28⟩) (by decide) node_647

theorem node_8280 : Outcome ⟨4, 16, 1, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 28⟩) (by decide) node_647

theorem node_8281 : Outcome ⟨4, 17, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 0, 2⟩, ⟨2, 17, 0, 4⟩, ⟨4, 16, 0, 2⟩, ⟨4, 15, 0, 4⟩]
  exact AllWinning.cons node_7265 (AllWinning.cons node_6270 (AllWinning.cons node_7347 (AllWinning.cons node_6419 (AllWinning.nil))))

theorem node_8282 : Outcome ⟨4, 17, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 0, 2⟩, ⟨2, 17, 0, 4⟩, ⟨1, 17, 0, 6⟩, ⟨0, 17, 0, 8⟩, ⟨4, 16, 0, 2⟩, ⟨4, 15, 0, 4⟩, ⟨4, 14, 0, 6⟩, ⟨4, 13, 0, 8⟩]
  exact AllWinning.cons node_7265 (AllWinning.cons node_6270 (AllWinning.cons node_5454 (AllWinning.cons node_4647 (AllWinning.cons node_7347 (AllWinning.cons node_6419 (AllWinning.cons node_5629 (AllWinning.cons node_4919 (AllWinning.nil))))))))

theorem node_8283 : Outcome ⟨4, 17, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 0, 2⟩, ⟨2, 17, 0, 4⟩, ⟨1, 17, 0, 6⟩, ⟨0, 17, 0, 8⟩, ⟨4, 16, 0, 2⟩, ⟨4, 15, 0, 4⟩, ⟨4, 14, 0, 6⟩, ⟨4, 13, 0, 8⟩, ⟨4, 12, 0, 10⟩, ⟨4, 11, 0, 12⟩]
  exact AllWinning.cons node_7265 (AllWinning.cons node_6270 (AllWinning.cons node_5454 (AllWinning.cons node_4647 (AllWinning.cons node_7347 (AllWinning.cons node_6419 (AllWinning.cons node_5629 (AllWinning.cons node_4919 (AllWinning.cons node_4217 (AllWinning.cons node_3626 (AllWinning.nil))))))))))

theorem node_8284 : Outcome ⟨4, 17, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 0, 2⟩, ⟨2, 17, 0, 4⟩, ⟨1, 17, 0, 6⟩, ⟨0, 17, 0, 8⟩, ⟨4, 16, 0, 2⟩, ⟨4, 15, 0, 4⟩, ⟨4, 14, 0, 6⟩, ⟨4, 13, 0, 8⟩, ⟨4, 12, 0, 10⟩, ⟨4, 11, 0, 12⟩, ⟨4, 10, 0, 14⟩, ⟨4, 9, 0, 16⟩]
  exact AllWinning.cons node_7265 (AllWinning.cons node_6270 (AllWinning.cons node_5454 (AllWinning.cons node_4647 (AllWinning.cons node_7347 (AllWinning.cons node_6419 (AllWinning.cons node_5629 (AllWinning.cons node_4919 (AllWinning.cons node_4217 (AllWinning.cons node_3626 (AllWinning.cons node_3083 (AllWinning.cons node_2626 (AllWinning.nil))))))))))))

theorem node_8285 : Outcome ⟨4, 17, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 0, 2⟩, ⟨2, 17, 0, 4⟩, ⟨1, 17, 0, 6⟩, ⟨0, 17, 0, 8⟩, ⟨4, 16, 0, 2⟩, ⟨4, 15, 0, 4⟩, ⟨4, 14, 0, 6⟩, ⟨4, 13, 0, 8⟩, ⟨4, 12, 0, 10⟩, ⟨4, 11, 0, 12⟩, ⟨4, 10, 0, 14⟩, ⟨4, 9, 0, 16⟩, ⟨4, 8, 0, 18⟩, ⟨4, 7, 0, 20⟩]
  exact AllWinning.cons node_7265 (AllWinning.cons node_6270 (AllWinning.cons node_5454 (AllWinning.cons node_4647 (AllWinning.cons node_7347 (AllWinning.cons node_6419 (AllWinning.cons node_5629 (AllWinning.cons node_4919 (AllWinning.cons node_4217 (AllWinning.cons node_3626 (AllWinning.cons node_3083 (AllWinning.cons node_2626 (AllWinning.cons node_2160 (AllWinning.cons node_1752 (AllWinning.nil))))))))))))))

theorem node_8286 : Outcome ⟨4, 17, 0, 16⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 26⟩) (by decide) node_858

theorem node_8287 : Outcome ⟨5, 0, 16, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 4⟩) (by decide) node_6273

theorem node_8288 : Outcome ⟨5, 0, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 4⟩) (by decide) node_6273

theorem node_8289 : Outcome ⟨5, 0, 16, 22⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 22⟩) (by decide) node_1414

theorem node_8290 : Outcome ⟨5, 1, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 2⟩) (by decide) node_7270

theorem node_8291 : Outcome ⟨5, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 2⟩) (by decide) node_7270

theorem node_8292 : Outcome ⟨5, 1, 15, 12⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 12⟩) (by decide) node_3639

theorem node_8293 : Outcome ⟨5, 1, 15, 14⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 12⟩) (by decide) node_3639

theorem node_8294 : Outcome ⟨5, 1, 15, 22⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 12⟩) (by decide) node_3639

theorem node_8295 : Outcome ⟨5, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 2⟩) (by decide) node_7277

theorem node_8296 : Outcome ⟨5, 2, 14, 14⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 8⟩) (by decide) node_4933

theorem node_8297 : Outcome ⟨5, 3, 13, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8298 : Outcome ⟨5, 3, 13, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8299 : Outcome ⟨5, 3, 13, 10⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 4⟩) (by decide) node_6289

theorem node_8300 : Outcome ⟨5, 4, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 4, 12, 2⟩, ⟨3, 4, 12, 4⟩, ⟨2, 4, 12, 6⟩, ⟨1, 4, 12, 8⟩, ⟨5, 3, 12, 2⟩, ⟨5, 2, 12, 4⟩, ⟨5, 1, 12, 6⟩, ⟨5, 0, 12, 8⟩, ⟨5, 4, 11, 2⟩, ⟨5, 4, 10, 4⟩, ⟨5, 4, 9, 6⟩, ⟨5, 4, 8, 8⟩]
  exact AllWinning.cons node_7287 (AllWinning.cons node_6296 (AllWinning.cons node_5472 (AllWinning.cons node_4669 (AllWinning.cons node_7362 (AllWinning.cons node_6428 (AllWinning.cons node_5638 (AllWinning.cons node_4924 (AllWinning.cons node_7366 (AllWinning.cons node_6443 (AllWinning.cons node_5645 (AllWinning.cons node_4947 (AllWinning.nil))))))))))))

theorem node_8301 : Outcome ⟨5, 4, 12, 12⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 10⟩) (by decide) node_4240

theorem node_8302 : Outcome ⟨5, 4, 12, 16⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 10⟩) (by decide) node_4240

theorem node_8303 : Outcome ⟨5, 4, 12, 28⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 10⟩) (by decide) node_4240

theorem node_8304 : Outcome ⟨5, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 4⟩) (by decide) node_6300

theorem node_8305 : Outcome ⟨5, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 6⟩) (by decide) node_5650

theorem node_8306 : Outcome ⟨5, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 2⟩) (by decide) node_7293

theorem node_8307 : Outcome ⟨5, 6, 10, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 8⟩) (by decide) node_4933

theorem node_8308 : Outcome ⟨5, 6, 10, 8⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 8⟩) (by decide) node_4933

theorem node_8309 : Outcome ⟨5, 6, 10, 12⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 8⟩) (by decide) node_4933

theorem node_8310 : Outcome ⟨5, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 9, 2⟩) (by decide) node_7304

theorem node_8311 : Outcome ⟨5, 7, 9, 14⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 12⟩) (by decide) node_3639

theorem node_8312 : Outcome ⟨5, 7, 9, 16⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 12⟩) (by decide) node_3639

theorem node_8313 : Outcome ⟨5, 8, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 8, 2⟩, ⟨3, 8, 8, 4⟩, ⟨5, 7, 8, 2⟩, ⟨5, 6, 8, 4⟩, ⟨5, 8, 7, 2⟩, ⟨5, 8, 6, 4⟩]
  exact AllWinning.cons node_7307 (AllWinning.cons node_6319 (AllWinning.cons node_7376 (AllWinning.cons node_6449 (AllWinning.cons node_7380 (AllWinning.cons node_6456 (AllWinning.nil))))))

theorem node_8314 : Outcome ⟨5, 8, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 6⟩) (by decide) node_5650

theorem node_8315 : Outcome ⟨5, 8, 8, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 10⟩) (by decide) node_3962

theorem node_8316 : Outcome ⟨5, 8, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 10⟩) (by decide) node_3962

theorem node_8317 : Outcome ⟨5, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 7, 2⟩) (by decide) node_7310

theorem node_8318 : Outcome ⟨5, 9, 7, 14⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 12⟩) (by decide) node_3677

theorem node_8319 : Outcome ⟨5, 9, 7, 16⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 12⟩) (by decide) node_3677

theorem node_8320 : Outcome ⟨5, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 2⟩) (by decide) node_7313

theorem node_8321 : Outcome ⟨5, 10, 6, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 8⟩) (by decide) node_4971

theorem node_8322 : Outcome ⟨5, 10, 6, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 8⟩) (by decide) node_4971

theorem node_8323 : Outcome ⟨5, 10, 6, 12⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 8⟩) (by decide) node_4971

theorem node_8324 : Outcome ⟨5, 11, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 4⟩) (by decide) node_6331

theorem node_8325 : Outcome ⟨5, 11, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 5, 6⟩) (by decide) node_5661

theorem node_8326 : Outcome ⟨5, 12, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 4, 2⟩, ⟨3, 12, 4, 4⟩, ⟨2, 12, 4, 6⟩, ⟨1, 12, 4, 8⟩, ⟨5, 11, 4, 2⟩, ⟨5, 10, 4, 4⟩, ⟨5, 9, 4, 6⟩, ⟨5, 8, 4, 8⟩, ⟨5, 12, 3, 2⟩, ⟨5, 12, 2, 4⟩, ⟨5, 12, 1, 6⟩, ⟨5, 12, 0, 8⟩]
  exact AllWinning.cons node_7328 (AllWinning.cons node_6342 (AllWinning.cons node_5501 (AllWinning.cons node_4699 (AllWinning.cons node_7391 (AllWinning.cons node_6462 (AllWinning.cons node_5665 (AllWinning.cons node_4961 (AllWinning.cons node_7394 (AllWinning.cons node_6475 (AllWinning.cons node_5675 (AllWinning.cons node_4985 (AllWinning.nil))))))))))))

theorem node_8327 : Outcome ⟨5, 12, 4, 12⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 10⟩) (by decide) node_4257

theorem node_8328 : Outcome ⟨5, 12, 4, 16⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 10⟩) (by decide) node_4257

theorem node_8329 : Outcome ⟨5, 12, 4, 28⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 10⟩) (by decide) node_4257

theorem node_8330 : Outcome ⟨5, 13, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 4⟩) (by decide) node_6346

theorem node_8331 : Outcome ⟨5, 13, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 4⟩) (by decide) node_6346

end RQ9F1
