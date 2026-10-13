import Chunk39
set_option autoImplicit false
namespace RQ9F1

theorem node_9089 : Outcome ⟨2, 11, 9, 16⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 6⟩) (by decide) node_6243

theorem node_9090 : Outcome ⟨2, 12, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 2⟩) (by decide) node_8026

theorem node_9091 : Outcome ⟨2, 12, 8, 12⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 2⟩) (by decide) node_8026

theorem node_9092 : Outcome ⟨2, 12, 8, 14⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 2⟩) (by decide) node_8026

theorem node_9093 : Outcome ⟨2, 13, 7, 2⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 2⟩) (by decide) node_8115

theorem node_9094 : Outcome ⟨2, 13, 7, 8⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 10⟩) (by decide) node_4796

theorem node_9095 : Outcome ⟨2, 13, 7, 10⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 20⟩) (by decide) node_2003

theorem node_9096 : Outcome ⟨2, 13, 7, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 20⟩) (by decide) node_2003

theorem node_9097 : Outcome ⟨2, 14, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 6, 4⟩) (by decide) node_7002

theorem node_9098 : Outcome ⟨2, 14, 6, 6⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 6⟩) (by decide) node_6243

theorem node_9099 : Outcome ⟨2, 14, 6, 12⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 6⟩) (by decide) node_6243

theorem node_9100 : Outcome ⟨2, 14, 6, 22⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 6⟩) (by decide) node_6243

theorem node_9101 : Outcome ⟨2, 15, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 5, 2⟩, ⟨0, 15, 5, 4⟩, ⟨2, 14, 5, 2⟩, ⟨2, 13, 5, 4⟩, ⟨2, 15, 4, 2⟩, ⟨2, 15, 3, 4⟩]
  exact AllWinning.cons node_8045 (AllWinning.cons node_7007 (AllWinning.cons node_8126 (AllWinning.cons node_7172 (AllWinning.cons node_8128 (AllWinning.cons node_7183 (AllWinning.nil))))))

theorem node_9102 : Outcome ⟨2, 15, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 5, 2⟩, ⟨0, 15, 5, 4⟩, ⟨2, 14, 5, 2⟩, ⟨2, 13, 5, 4⟩, ⟨2, 12, 5, 6⟩, ⟨2, 11, 5, 8⟩, ⟨2, 15, 4, 2⟩, ⟨2, 15, 3, 4⟩, ⟨2, 15, 2, 6⟩, ⟨2, 15, 1, 8⟩]
  exact AllWinning.cons node_8045 (AllWinning.cons node_7007 (AllWinning.cons node_8126 (AllWinning.cons node_7172 (AllWinning.cons node_6252 (AllWinning.cons node_5498 (AllWinning.cons node_8128 (AllWinning.cons node_7183 (AllWinning.cons node_6263 (AllWinning.cons node_5511 (AllWinning.nil))))))))))

theorem node_9103 : Outcome ⟨2, 15, 5, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 10⟩) (by decide) node_4776

theorem node_9104 : Outcome ⟨2, 15, 5, 12⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 10⟩) (by decide) node_4776

theorem node_9105 : Outcome ⟨2, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 4⟩) (by decide) node_7176

theorem node_9106 : Outcome ⟨2, 16, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 4⟩) (by decide) node_7176

theorem node_9107 : Outcome ⟨2, 16, 4, 12⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 4⟩) (by decide) node_7176

theorem node_9108 : Outcome ⟨2, 16, 4, 14⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 4⟩) (by decide) node_7176

theorem node_9109 : Outcome ⟨2, 16, 4, 28⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 30⟩) (by decide) node_569

theorem node_9110 : Outcome ⟨2, 17, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 4⟩) (by decide) node_7190

theorem node_9111 : Outcome ⟨2, 17, 3, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 4⟩) (by decide) node_7190

theorem node_9112 : Outcome ⟨2, 17, 3, 16⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 20⟩) (by decide) node_2033

theorem node_9113 : Outcome ⟨2, 17, 3, 24⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 20⟩) (by decide) node_2033

theorem node_9114 : Outcome ⟨2, 18, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 2, 2⟩, ⟨0, 18, 2, 4⟩, ⟨2, 17, 2, 2⟩, ⟨2, 16, 2, 4⟩, ⟨2, 18, 1, 2⟩, ⟨2, 18, 0, 4⟩]
  exact AllWinning.cons node_8057 (AllWinning.cons node_7017 (AllWinning.cons node_8137 (AllWinning.cons node_7186 (AllWinning.cons node_8140 (AllWinning.cons node_7196 (AllWinning.nil))))))

theorem node_9115 : Outcome ⟨2, 18, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 18, 2, 2⟩, ⟨0, 18, 2, 4⟩, ⟨2, 17, 2, 2⟩, ⟨2, 16, 2, 4⟩, ⟨2, 15, 2, 6⟩, ⟨2, 14, 2, 8⟩, ⟨2, 18, 1, 2⟩, ⟨2, 18, 0, 4⟩]
  exact AllWinning.cons node_8057 (AllWinning.cons node_7017 (AllWinning.cons node_8137 (AllWinning.cons node_7186 (AllWinning.cons node_6263 (AllWinning.cons node_5508 (AllWinning.cons node_8140 (AllWinning.cons node_7196 (AllWinning.nil))))))))

theorem node_9116 : Outcome ⟨2, 18, 2, 10⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 10⟩) (by decide) node_4796

theorem node_9117 : Outcome ⟨2, 18, 2, 28⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 36⟩) (by decide) node_199

theorem node_9118 : Outcome ⟨2, 19, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 1, 4⟩) (by decide) node_7022

theorem node_9119 : Outcome ⟨2, 19, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 19, 1, 4⟩) (by decide) node_7022

theorem node_9120 : Outcome ⟨2, 19, 1, 14⟩ true :=
  Outcome.win (q := ⟨0, 19, 1, 4⟩) (by decide) node_7022

theorem node_9121 : Outcome ⟨2, 20, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 0, 2⟩, ⟨0, 20, 0, 4⟩, ⟨2, 19, 0, 2⟩, ⟨2, 18, 0, 4⟩, ⟨2, 17, 0, 6⟩, ⟨2, 16, 0, 8⟩]
  exact AllWinning.cons node_8062 (AllWinning.cons node_7025 (AllWinning.cons node_8144 (AllWinning.cons node_7196 (AllWinning.cons node_6271 (AllWinning.cons node_5515 (AllWinning.nil))))))

theorem node_9122 : Outcome ⟨2, 20, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 10⟩) (by decide) node_4806

theorem node_9123 : Outcome ⟨2, 20, 0, 10⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 10⟩) (by decide) node_4806

theorem node_9124 : Outcome ⟨3, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 19, 4⟩) (by decide) node_7028

theorem node_9125 : Outcome ⟨3, 0, 19, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 6⟩) (by decide) node_6274

theorem node_9126 : Outcome ⟨3, 0, 19, 22⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 32⟩) (by decide) node_417

theorem node_9127 : Outcome ⟨3, 0, 19, 32⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 32⟩) (by decide) node_417

theorem node_9128 : Outcome ⟨3, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 18, 4⟩) (by decide) node_7032

theorem node_9129 : Outcome ⟨3, 1, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 18, 4⟩) (by decide) node_7032

theorem node_9130 : Outcome ⟨3, 1, 18, 28⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 24⟩) (by decide) node_1330

theorem node_9131 : Outcome ⟨3, 2, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 4⟩) (by decide) node_7034

theorem node_9132 : Outcome ⟨3, 2, 17, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 4⟩) (by decide) node_7034

theorem node_9133 : Outcome ⟨3, 2, 17, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 20⟩) (by decide) node_2074

theorem node_9134 : Outcome ⟨3, 3, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 3, 16, 2⟩, ⟨1, 3, 16, 4⟩, ⟨3, 2, 16, 2⟩, ⟨3, 1, 16, 4⟩, ⟨3, 3, 15, 2⟩, ⟨3, 3, 14, 4⟩]
  exact AllWinning.cons node_8075 (AllWinning.cons node_7040 (AllWinning.cons node_8153 (AllWinning.cons node_7201 (AllWinning.cons node_8158 (AllWinning.cons node_7211 (AllWinning.nil))))))

theorem node_9135 : Outcome ⟨3, 3, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 6⟩) (by decide) node_6044

theorem node_9136 : Outcome ⟨3, 3, 16, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 6⟩) (by decide) node_6044

theorem node_9137 : Outcome ⟨3, 4, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 4⟩) (by decide) node_7046

theorem node_9138 : Outcome ⟨3, 4, 15, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 4⟩) (by decide) node_7046

theorem node_9139 : Outcome ⟨3, 4, 15, 28⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 4⟩) (by decide) node_7046

theorem node_9140 : Outcome ⟨3, 5, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 14, 4⟩) (by decide) node_7053

theorem node_9141 : Outcome ⟨3, 5, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9142 : Outcome ⟨3, 5, 14, 12⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9143 : Outcome ⟨3, 6, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 13, 4⟩) (by decide) node_7056

theorem node_9144 : Outcome ⟨3, 6, 13, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 6⟩) (by decide) node_6290

theorem node_9145 : Outcome ⟨3, 6, 13, 22⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 24⟩) (by decide) node_1361

theorem node_9146 : Outcome ⟨3, 7, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 4⟩) (by decide) node_7224

theorem node_9147 : Outcome ⟨3, 7, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 4⟩) (by decide) node_7224

theorem node_9148 : Outcome ⟨3, 7, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 4⟩) (by decide) node_7224

theorem node_9149 : Outcome ⟨3, 7, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 4⟩) (by decide) node_7224

theorem node_9150 : Outcome ⟨3, 7, 12, 24⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 20⟩) (by decide) node_2105

theorem node_9151 : Outcome ⟨3, 8, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 11, 2⟩, ⟨1, 8, 11, 4⟩, ⟨3, 7, 11, 2⟩, ⟨3, 6, 11, 4⟩, ⟨3, 8, 10, 2⟩, ⟨3, 8, 9, 4⟩]
  exact AllWinning.cons node_8097 (AllWinning.cons node_7064 (AllWinning.cons node_8171 (AllWinning.cons node_7220 (AllWinning.cons node_8176 (AllWinning.cons node_7229 (AllWinning.nil))))))

theorem node_9152 : Outcome ⟨3, 8, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9153 : Outcome ⟨3, 8, 11, 10⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9154 : Outcome ⟨3, 8, 11, 14⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9155 : Outcome ⟨3, 8, 11, 22⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9156 : Outcome ⟨3, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 10, 4⟩) (by decide) node_7067

theorem node_9157 : Outcome ⟨3, 9, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 10, 4⟩) (by decide) node_7067

theorem node_9158 : Outcome ⟨3, 9, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 9, 10, 4⟩) (by decide) node_7067

theorem node_9159 : Outcome ⟨3, 9, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 9, 10, 4⟩) (by decide) node_7067

theorem node_9160 : Outcome ⟨3, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 10, 9, 4⟩) (by decide) node_7071

theorem node_9161 : Outcome ⟨3, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 9, 4⟩) (by decide) node_7071

theorem node_9162 : Outcome ⟨3, 10, 9, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 9, 4⟩) (by decide) node_7071

theorem node_9163 : Outcome ⟨3, 10, 9, 8⟩ true :=
  Outcome.win (q := ⟨1, 10, 9, 4⟩) (by decide) node_7071

theorem node_9164 : Outcome ⟨3, 11, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 8, 2⟩, ⟨1, 11, 8, 4⟩, ⟨3, 10, 8, 2⟩, ⟨3, 9, 8, 4⟩, ⟨3, 11, 7, 2⟩, ⟨3, 11, 6, 4⟩]
  exact AllWinning.cons node_8111 (AllWinning.cons node_7075 (AllWinning.cons node_8185 (AllWinning.cons node_7234 (AllWinning.cons node_8190 (AllWinning.cons node_7243 (AllWinning.nil))))))

theorem node_9165 : Outcome ⟨3, 11, 8, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9166 : Outcome ⟨3, 11, 8, 10⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9167 : Outcome ⟨3, 11, 8, 14⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9168 : Outcome ⟨3, 11, 8, 22⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9169 : Outcome ⟨3, 12, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 4⟩) (by decide) node_7239

theorem node_9170 : Outcome ⟨3, 12, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 4⟩) (by decide) node_7239

theorem node_9171 : Outcome ⟨3, 12, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 4⟩) (by decide) node_7239

theorem node_9172 : Outcome ⟨3, 12, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 4⟩) (by decide) node_7239

theorem node_9173 : Outcome ⟨3, 12, 7, 24⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 20⟩) (by decide) node_2074

theorem node_9174 : Outcome ⟨3, 13, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 6, 4⟩) (by decide) node_7080

theorem node_9175 : Outcome ⟨3, 13, 6, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 6⟩) (by decide) node_6347

theorem node_9176 : Outcome ⟨3, 13, 6, 22⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 24⟩) (by decide) node_1330

theorem node_9177 : Outcome ⟨3, 14, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 5, 4⟩) (by decide) node_7084

theorem node_9178 : Outcome ⟨3, 14, 5, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9179 : Outcome ⟨3, 14, 5, 12⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9180 : Outcome ⟨3, 15, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 4⟩) (by decide) node_7088

theorem node_9181 : Outcome ⟨3, 15, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 4⟩) (by decide) node_7088

theorem node_9182 : Outcome ⟨3, 15, 4, 28⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 4⟩) (by decide) node_7088

theorem node_9183 : Outcome ⟨3, 16, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 3, 2⟩, ⟨1, 16, 3, 4⟩, ⟨3, 15, 3, 2⟩, ⟨3, 14, 3, 4⟩, ⟨3, 16, 2, 2⟩, ⟨3, 16, 1, 4⟩]
  exact AllWinning.cons node_8131 (AllWinning.cons node_7094 (AllWinning.cons node_8204 (AllWinning.cons node_7252 (AllWinning.cons node_8208 (AllWinning.cons node_7260 (AllWinning.nil))))))

theorem node_9184 : Outcome ⟨3, 16, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 6⟩) (by decide) node_6102

theorem node_9185 : Outcome ⟨3, 16, 3, 10⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 6⟩) (by decide) node_6102

theorem node_9186 : Outcome ⟨3, 17, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 4⟩) (by decide) node_7100

theorem node_9187 : Outcome ⟨3, 17, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 4⟩) (by decide) node_7100

theorem node_9188 : Outcome ⟨3, 17, 2, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 20⟩) (by decide) node_2105

theorem node_9189 : Outcome ⟨3, 18, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 1, 4⟩) (by decide) node_7107

theorem node_9190 : Outcome ⟨3, 18, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 18, 1, 4⟩) (by decide) node_7107

theorem node_9191 : Outcome ⟨3, 18, 1, 28⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 24⟩) (by decide) node_1361

theorem node_9192 : Outcome ⟨3, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 0, 4⟩) (by decide) node_7109

theorem node_9193 : Outcome ⟨3, 19, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 6⟩) (by decide) node_6362

theorem node_9194 : Outcome ⟨3, 19, 0, 22⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 32⟩) (by decide) node_440

theorem node_9195 : Outcome ⟨3, 19, 0, 32⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 32⟩) (by decide) node_440

theorem node_9196 : Outcome ⟨4, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 2⟩) (by decide) node_8219

theorem node_9197 : Outcome ⟨4, 0, 18, 8⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 2⟩) (by decide) node_8219

theorem node_9198 : Outcome ⟨4, 0, 18, 22⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 28⟩) (by decide) node_833

theorem node_9199 : Outcome ⟨4, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 4⟩) (by decide) node_7117

theorem node_9200 : Outcome ⟨4, 1, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 4⟩) (by decide) node_7117

theorem node_9201 : Outcome ⟨4, 1, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 4⟩) (by decide) node_7117

theorem node_9202 : Outcome ⟨4, 1, 17, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 4⟩) (by decide) node_7117

theorem node_9203 : Outcome ⟨4, 1, 17, 14⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 4⟩) (by decide) node_7117

theorem node_9204 : Outcome ⟨4, 1, 17, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 30⟩) (by decide) node_630

theorem node_9205 : Outcome ⟨4, 2, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 4⟩) (by decide) node_7278

theorem node_9206 : Outcome ⟨4, 2, 16, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 4⟩) (by decide) node_7278

theorem node_9207 : Outcome ⟨4, 2, 16, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 4⟩) (by decide) node_7278

theorem node_9208 : Outcome ⟨4, 2, 16, 14⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 4⟩) (by decide) node_7278

theorem node_9209 : Outcome ⟨4, 3, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 4⟩) (by decide) node_7271

theorem node_9210 : Outcome ⟨4, 3, 15, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 4⟩) (by decide) node_7271

theorem node_9211 : Outcome ⟨4, 4, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 4⟩) (by decide) node_7130

theorem node_9212 : Outcome ⟨4, 4, 14, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 4⟩) (by decide) node_7130

theorem node_9213 : Outcome ⟨4, 4, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 4⟩) (by decide) node_7130

theorem node_9214 : Outcome ⟨4, 4, 14, 30⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 28⟩) (by decide) node_859

theorem node_9215 : Outcome ⟨4, 5, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 2⟩) (by decide) node_8233

theorem node_9216 : Outcome ⟨4, 5, 13, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9217 : Outcome ⟨4, 5, 13, 14⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9218 : Outcome ⟨4, 6, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9219 : Outcome ⟨4, 6, 12, 6⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9220 : Outcome ⟨4, 6, 12, 14⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9221 : Outcome ⟨4, 6, 12, 24⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9222 : Outcome ⟨4, 7, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 7, 11, 2⟩, ⟨2, 7, 11, 4⟩, ⟨4, 6, 11, 2⟩, ⟨4, 5, 11, 4⟩, ⟨4, 7, 10, 2⟩, ⟨4, 7, 9, 4⟩]
  exact AllWinning.cons node_8171 (AllWinning.cons node_7145 (AllWinning.cons node_8243 (AllWinning.cons node_7290 (AllWinning.cons node_8247 (AllWinning.cons node_7305 (AllWinning.nil))))))

theorem node_9223 : Outcome ⟨4, 7, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 6⟩) (by decide) node_6139

theorem node_9224 : Outcome ⟨4, 7, 11, 6⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9225 : Outcome ⟨4, 7, 11, 8⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9226 : Outcome ⟨4, 7, 11, 22⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9227 : Outcome ⟨4, 7, 11, 24⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9228 : Outcome ⟨4, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9229 : Outcome ⟨4, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9230 : Outcome ⟨4, 8, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9231 : Outcome ⟨4, 8, 10, 14⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9232 : Outcome ⟨4, 9, 9, 2⟩ true :=
  Outcome.win (q := ⟨3, 9, 9, 2⟩) (by decide) node_8181

theorem node_9233 : Outcome ⟨4, 9, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 8⟩) (by decide) node_5347

theorem node_9234 : Outcome ⟨4, 9, 9, 14⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 8⟩) (by decide) node_5347

theorem node_9235 : Outcome ⟨4, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9236 : Outcome ⟨4, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9237 : Outcome ⟨4, 10, 8, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9238 : Outcome ⟨4, 10, 8, 14⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9239 : Outcome ⟨4, 11, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 7, 2⟩, ⟨2, 11, 7, 4⟩, ⟨4, 10, 7, 2⟩, ⟨4, 9, 7, 4⟩, ⟨4, 11, 6, 2⟩, ⟨4, 11, 5, 4⟩]
  exact AllWinning.cons node_8190 (AllWinning.cons node_7163 (AllWinning.cons node_8256 (AllWinning.cons node_7311 (AllWinning.cons node_8259 (AllWinning.cons node_7325 (AllWinning.nil))))))

theorem node_9240 : Outcome ⟨4, 11, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 6⟩) (by decide) node_6164

theorem node_9241 : Outcome ⟨4, 11, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9242 : Outcome ⟨4, 11, 7, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9243 : Outcome ⟨4, 11, 7, 22⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9244 : Outcome ⟨4, 11, 7, 24⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 12⟩) (by decide) node_4175

theorem node_9245 : Outcome ⟨4, 12, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9246 : Outcome ⟨4, 12, 6, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9247 : Outcome ⟨4, 12, 6, 14⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9248 : Outcome ⟨4, 12, 6, 24⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9249 : Outcome ⟨4, 13, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 2⟩) (by decide) node_8263

theorem node_9250 : Outcome ⟨4, 13, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9251 : Outcome ⟨4, 13, 5, 14⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 12⟩) (by decide) node_4192

theorem node_9252 : Outcome ⟨4, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 4⟩) (by decide) node_7176

theorem node_9253 : Outcome ⟨4, 14, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 4⟩) (by decide) node_7176

theorem node_9254 : Outcome ⟨4, 14, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 4⟩) (by decide) node_7176

theorem node_9255 : Outcome ⟨4, 14, 4, 30⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 28⟩) (by decide) node_833

theorem node_9256 : Outcome ⟨4, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 4⟩) (by decide) node_7341

theorem node_9257 : Outcome ⟨4, 15, 3, 6⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 4⟩) (by decide) node_7341

theorem node_9258 : Outcome ⟨4, 16, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 4⟩) (by decide) node_7334

theorem node_9259 : Outcome ⟨4, 16, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 4⟩) (by decide) node_7334

theorem node_9260 : Outcome ⟨4, 16, 2, 12⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 4⟩) (by decide) node_7334

theorem node_9261 : Outcome ⟨4, 16, 2, 14⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 4⟩) (by decide) node_7334

theorem node_9262 : Outcome ⟨4, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 4⟩) (by decide) node_7190

theorem node_9263 : Outcome ⟨4, 17, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 4⟩) (by decide) node_7190

theorem node_9264 : Outcome ⟨4, 17, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 4⟩) (by decide) node_7190

theorem node_9265 : Outcome ⟨4, 17, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 4⟩) (by decide) node_7190

theorem node_9266 : Outcome ⟨4, 17, 1, 14⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 4⟩) (by decide) node_7190

theorem node_9267 : Outcome ⟨4, 17, 1, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 30⟩) (by decide) node_648

theorem node_9268 : Outcome ⟨4, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 2⟩) (by decide) node_8281

theorem node_9269 : Outcome ⟨4, 18, 0, 8⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 2⟩) (by decide) node_8281

theorem node_9270 : Outcome ⟨4, 18, 0, 22⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 28⟩) (by decide) node_859

theorem node_9271 : Outcome ⟨5, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 2⟩) (by decide) node_8219

theorem node_9272 : Outcome ⟨5, 0, 17, 8⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 2⟩) (by decide) node_8219

theorem node_9273 : Outcome ⟨5, 0, 17, 14⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 24⟩) (by decide) node_1415

theorem node_9274 : Outcome ⟨5, 1, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 14, 4⟩) (by decide) node_7356

theorem node_9275 : Outcome ⟨5, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 14, 4⟩) (by decide) node_7356

theorem node_9276 : Outcome ⟨5, 1, 16, 20⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 14⟩) (by decide) node_3640

theorem node_9277 : Outcome ⟨5, 2, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 15, 2⟩, ⟨3, 2, 15, 4⟩, ⟨5, 1, 15, 2⟩, ⟨5, 0, 15, 4⟩, ⟨5, 2, 14, 2⟩, ⟨5, 2, 13, 4⟩]
  exact AllWinning.cons node_8228 (AllWinning.cons node_7207 (AllWinning.cons node_8290 (AllWinning.cons node_7351 (AllWinning.cons node_8295 (AllWinning.cons node_7359 (AllWinning.nil))))))

theorem node_9278 : Outcome ⟨5, 2, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 15, 2⟩, ⟨3, 2, 15, 4⟩, ⟨2, 2, 15, 6⟩, ⟨1, 2, 15, 8⟩, ⟨5, 1, 15, 2⟩, ⟨5, 0, 15, 4⟩, ⟨5, 2, 14, 2⟩, ⟨5, 2, 13, 4⟩, ⟨5, 2, 12, 6⟩, ⟨5, 2, 11, 8⟩]
  exact AllWinning.cons node_8228 (AllWinning.cons node_7207 (AllWinning.cons node_6204 (AllWinning.cons node_5397 (AllWinning.cons node_8290 (AllWinning.cons node_7351 (AllWinning.cons node_8295 (AllWinning.cons node_7359 (AllWinning.cons node_6429 (AllWinning.cons node_5640 (AllWinning.nil))))))))))

theorem node_9279 : Outcome ⟨5, 2, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 10⟩) (by decide) node_4579

theorem node_9280 : Outcome ⟨5, 2, 15, 12⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 10⟩) (by decide) node_4579

theorem node_9281 : Outcome ⟨5, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 14, 4⟩) (by decide) node_7356

theorem node_9282 : Outcome ⟨5, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 6⟩) (by decide) node_6434

theorem node_9283 : Outcome ⟨5, 3, 14, 12⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 6⟩) (by decide) node_6434

theorem node_9284 : Outcome ⟨5, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 2⟩) (by decide) node_8233

theorem node_9285 : Outcome ⟨5, 4, 13, 8⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9286 : Outcome ⟨5, 4, 13, 14⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9287 : Outcome ⟨5, 5, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 12, 2⟩) (by decide) node_8239

theorem node_9288 : Outcome ⟨5, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 5, 12, 2⟩) (by decide) node_8239

theorem node_9289 : Outcome ⟨5, 5, 12, 10⟩ true :=
  Outcome.win (q := ⟨4, 5, 12, 2⟩) (by decide) node_8239

theorem node_9290 : Outcome ⟨5, 5, 12, 26⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 24⟩) (by decide) node_1449

theorem node_9291 : Outcome ⟨5, 6, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 6, 11, 2⟩, ⟨3, 6, 11, 4⟩, ⟨5, 5, 11, 2⟩, ⟨5, 4, 11, 4⟩, ⟨5, 6, 10, 2⟩, ⟨5, 6, 9, 4⟩]
  exact AllWinning.cons node_8243 (AllWinning.cons node_7220 (AllWinning.cons node_8304 (AllWinning.cons node_7367 (AllWinning.cons node_8306 (AllWinning.cons node_7372 (AllWinning.nil))))))

theorem node_9292 : Outcome ⟨5, 6, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 6⟩) (by decide) node_6219

theorem node_9293 : Outcome ⟨5, 6, 11, 20⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 6⟩) (by decide) node_6219

theorem node_9294 : Outcome ⟨5, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 4⟩) (by decide) node_7224

theorem node_9295 : Outcome ⟨5, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 4⟩) (by decide) node_7224

theorem node_9296 : Outcome ⟨5, 7, 10, 10⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9297 : Outcome ⟨5, 7, 10, 14⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9298 : Outcome ⟨5, 7, 10, 24⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9299 : Outcome ⟨5, 8, 9, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 8, 2⟩) (by decide) node_8313

theorem node_9300 : Outcome ⟨5, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 8, 2⟩) (by decide) node_8313

theorem node_9301 : Outcome ⟨5, 8, 9, 8⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 14⟩) (by decide) node_3640

theorem node_9302 : Outcome ⟨5, 8, 9, 12⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 14⟩) (by decide) node_3640

theorem node_9303 : Outcome ⟨5, 9, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 8, 2⟩) (by decide) node_8313

theorem node_9304 : Outcome ⟨5, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 8, 2⟩) (by decide) node_8313

theorem node_9305 : Outcome ⟨5, 9, 8, 8⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 14⟩) (by decide) node_3678

theorem node_9306 : Outcome ⟨5, 9, 8, 12⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 14⟩) (by decide) node_3678

theorem node_9307 : Outcome ⟨5, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 4⟩) (by decide) node_7239

theorem node_9308 : Outcome ⟨5, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 4⟩) (by decide) node_7239

theorem node_9309 : Outcome ⟨5, 10, 7, 10⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9310 : Outcome ⟨5, 10, 7, 14⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9311 : Outcome ⟨5, 10, 7, 24⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 12⟩) (by decide) node_4241

theorem node_9312 : Outcome ⟨5, 11, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 6, 2⟩, ⟨3, 11, 6, 4⟩, ⟨5, 10, 6, 2⟩, ⟨5, 9, 6, 4⟩, ⟨5, 11, 5, 2⟩, ⟨5, 11, 4, 4⟩]
  exact AllWinning.cons node_8259 (AllWinning.cons node_7243 (AllWinning.cons node_8320 (AllWinning.cons node_7385 (AllWinning.cons node_8324 (AllWinning.cons node_7392 (AllWinning.nil))))))

theorem node_9313 : Outcome ⟨5, 11, 6, 4⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 6⟩) (by decide) node_6243

theorem node_9314 : Outcome ⟨5, 11, 6, 20⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 6⟩) (by decide) node_6243

theorem node_9315 : Outcome ⟨5, 12, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 2⟩) (by decide) node_8263

theorem node_9316 : Outcome ⟨5, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 2⟩) (by decide) node_8263

theorem node_9317 : Outcome ⟨5, 12, 5, 10⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 2⟩) (by decide) node_8263

theorem node_9318 : Outcome ⟨5, 12, 5, 26⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 24⟩) (by decide) node_1415

theorem node_9319 : Outcome ⟨5, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 2⟩) (by decide) node_8267

theorem node_9320 : Outcome ⟨5, 13, 4, 8⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9321 : Outcome ⟨5, 13, 4, 14⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 12⟩) (by decide) node_4258

theorem node_9322 : Outcome ⟨5, 14, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 1, 4⟩) (by decide) node_7402

theorem node_9323 : Outcome ⟨5, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 6⟩) (by decide) node_6467

theorem node_9324 : Outcome ⟨5, 14, 3, 12⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 6⟩) (by decide) node_6467

theorem node_9325 : Outcome ⟨5, 15, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 2, 2⟩, ⟨3, 15, 2, 4⟩, ⟨5, 14, 2, 2⟩, ⟨5, 13, 2, 4⟩, ⟨5, 15, 1, 2⟩, ⟨5, 15, 0, 4⟩]
  exact AllWinning.cons node_8275 (AllWinning.cons node_7256 (AllWinning.cons node_8333 (AllWinning.cons node_7398 (AllWinning.cons node_8335 (AllWinning.cons node_7405 (AllWinning.nil))))))

theorem node_9326 : Outcome ⟨5, 15, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 2, 2⟩, ⟨3, 15, 2, 4⟩, ⟨2, 15, 2, 6⟩, ⟨1, 15, 2, 8⟩, ⟨5, 14, 2, 2⟩, ⟨5, 13, 2, 4⟩, ⟨5, 12, 2, 6⟩, ⟨5, 11, 2, 8⟩, ⟨5, 15, 1, 2⟩, ⟨5, 15, 0, 4⟩]
  exact AllWinning.cons node_8275 (AllWinning.cons node_7256 (AllWinning.cons node_6263 (AllWinning.cons node_5446 (AllWinning.cons node_8333 (AllWinning.cons node_7398 (AllWinning.cons node_6476 (AllWinning.cons node_5672 (AllWinning.cons node_8335 (AllWinning.cons node_7405 (AllWinning.nil))))))))))

theorem node_9327 : Outcome ⟨5, 15, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 10⟩) (by decide) node_4638

theorem node_9328 : Outcome ⟨5, 15, 2, 12⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 10⟩) (by decide) node_4638

theorem node_9329 : Outcome ⟨5, 16, 1, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 1, 4⟩) (by decide) node_7402

theorem node_9330 : Outcome ⟨5, 16, 1, 4⟩ true :=
  Outcome.win (q := ⟨5, 14, 1, 4⟩) (by decide) node_7402

theorem node_9331 : Outcome ⟨5, 16, 1, 20⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 14⟩) (by decide) node_3678

theorem node_9332 : Outcome ⟨5, 17, 0, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 2⟩) (by decide) node_8281

theorem node_9333 : Outcome ⟨5, 17, 0, 8⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 2⟩) (by decide) node_8281

theorem node_9334 : Outcome ⟨5, 17, 0, 14⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 24⟩) (by decide) node_1449

theorem node_9335 : Outcome ⟨6, 0, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 14, 4⟩) (by decide) node_7410

theorem node_9336 : Outcome ⟨6, 0, 16, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 6⟩) (by decide) node_6274

theorem node_9337 : Outcome ⟨6, 0, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 6⟩) (by decide) node_6274

theorem node_9338 : Outcome ⟨6, 0, 16, 20⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 20⟩) (by decide) node_2200

theorem node_9339 : Outcome ⟨6, 0, 16, 24⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 20⟩) (by decide) node_2200

theorem node_9340 : Outcome ⟨6, 1, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 4⟩) (by decide) node_7271

theorem node_9341 : Outcome ⟨6, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 4⟩) (by decide) node_7271

theorem node_9342 : Outcome ⟨6, 1, 15, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 4⟩) (by decide) node_7271

theorem node_9343 : Outcome ⟨6, 1, 15, 10⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 4⟩) (by decide) node_7271

theorem node_9344 : Outcome ⟨6, 1, 15, 20⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 24⟩) (by decide) node_1466

theorem node_9345 : Outcome ⟨6, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 4⟩) (by decide) node_7278

theorem node_9346 : Outcome ⟨6, 2, 14, 6⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 6⟩) (by decide) node_6498

theorem node_9347 : Outcome ⟨6, 2, 14, 12⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 6⟩) (by decide) node_6498

theorem node_9348 : Outcome ⟨6, 2, 14, 22⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 6⟩) (by decide) node_6498

theorem node_9349 : Outcome ⟨6, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 13, 4⟩) (by decide) node_7415

theorem node_9350 : Outcome ⟨6, 3, 13, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 6⟩) (by decide) node_6290

theorem node_9351 : Outcome ⟨6, 3, 13, 22⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 24⟩) (by decide) node_1486

theorem node_9352 : Outcome ⟨6, 4, 12, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9353 : Outcome ⟨6, 4, 12, 6⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9354 : Outcome ⟨6, 4, 12, 14⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9355 : Outcome ⟨6, 4, 12, 24⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9356 : Outcome ⟨6, 5, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 5, 11, 2⟩, ⟨4, 5, 11, 4⟩, ⟨6, 4, 11, 2⟩, ⟨6, 3, 11, 4⟩, ⟨6, 5, 10, 2⟩, ⟨6, 5, 9, 4⟩]
  exact AllWinning.cons node_8304 (AllWinning.cons node_7290 (AllWinning.cons node_8356 (AllWinning.cons node_7423 (AllWinning.cons node_8359 (AllWinning.cons node_7438 (AllWinning.nil))))))

theorem node_9357 : Outcome ⟨6, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9358 : Outcome ⟨6, 5, 11, 20⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 6⟩) (by decide) node_6301

theorem node_9359 : Outcome ⟨6, 6, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9360 : Outcome ⟨6, 6, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 4⟩) (by decide) node_7294

theorem node_9361 : Outcome ⟨6, 6, 10, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 20⟩) (by decide) node_2234

theorem node_9362 : Outcome ⟨6, 6, 10, 24⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 20⟩) (by decide) node_2234

theorem node_9363 : Outcome ⟨6, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9364 : Outcome ⟨6, 7, 9, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9365 : Outcome ⟨6, 7, 9, 8⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9366 : Outcome ⟨6, 7, 9, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9367 : Outcome ⟨6, 7, 9, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9368 : Outcome ⟨6, 8, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 8, 2⟩) (by decide) node_8313

theorem node_9369 : Outcome ⟨6, 8, 8, 12⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 12⟩) (by decide) node_3963

theorem node_9370 : Outcome ⟨6, 8, 8, 24⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 12⟩) (by decide) node_3963

theorem node_9371 : Outcome ⟨6, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 2⟩) (by decide) node_8379

theorem node_9372 : Outcome ⟨6, 9, 7, 6⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 2⟩) (by decide) node_8379

theorem node_9373 : Outcome ⟨6, 9, 7, 8⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 2⟩) (by decide) node_8379

theorem node_9374 : Outcome ⟨6, 9, 7, 14⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 2⟩) (by decide) node_8379

theorem node_9375 : Outcome ⟨6, 9, 7, 20⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 2⟩) (by decide) node_8379

theorem node_9376 : Outcome ⟨6, 10, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9377 : Outcome ⟨6, 10, 6, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 4⟩) (by decide) node_7314

theorem node_9378 : Outcome ⟨6, 10, 6, 20⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 20⟩) (by decide) node_2200

theorem node_9379 : Outcome ⟨6, 10, 6, 24⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 20⟩) (by decide) node_2200

theorem node_9380 : Outcome ⟨6, 11, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 5, 2⟩, ⟨4, 11, 5, 4⟩, ⟨6, 10, 5, 2⟩, ⟨6, 9, 5, 4⟩, ⟨6, 11, 4, 2⟩, ⟨6, 11, 3, 4⟩]
  exact AllWinning.cons node_8324 (AllWinning.cons node_7325 (AllWinning.cons node_8395 (AllWinning.cons node_7451 (AllWinning.cons node_8399 (AllWinning.cons node_7466 (AllWinning.nil))))))

theorem node_9381 : Outcome ⟨6, 11, 5, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9382 : Outcome ⟨6, 11, 5, 20⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 6⟩) (by decide) node_6332

theorem node_9383 : Outcome ⟨6, 12, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9384 : Outcome ⟨6, 12, 4, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9385 : Outcome ⟨6, 12, 4, 14⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9386 : Outcome ⟨6, 12, 4, 24⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 4⟩) (by decide) node_7456

theorem node_9387 : Outcome ⟨6, 13, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 13, 1, 4⟩) (by decide) node_7473

theorem node_9388 : Outcome ⟨6, 13, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 6⟩) (by decide) node_6347

theorem node_9389 : Outcome ⟨6, 13, 3, 22⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 24⟩) (by decide) node_1466

theorem node_9390 : Outcome ⟨6, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 4⟩) (by decide) node_7334

theorem node_9391 : Outcome ⟨6, 14, 2, 4⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 6⟩) (by decide) node_6532

theorem node_9392 : Outcome ⟨6, 14, 2, 6⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 6⟩) (by decide) node_6532

theorem node_9393 : Outcome ⟨6, 14, 2, 12⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 6⟩) (by decide) node_6532

theorem node_9394 : Outcome ⟨6, 14, 2, 22⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 6⟩) (by decide) node_6532

theorem node_9395 : Outcome ⟨6, 15, 1, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 4⟩) (by decide) node_7341

theorem node_9396 : Outcome ⟨6, 15, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 4⟩) (by decide) node_7341

theorem node_9397 : Outcome ⟨6, 15, 1, 10⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 4⟩) (by decide) node_7341

theorem node_9398 : Outcome ⟨6, 15, 1, 20⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 24⟩) (by decide) node_1486

theorem node_9399 : Outcome ⟨6, 16, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 0, 4⟩) (by decide) node_7478

theorem node_9400 : Outcome ⟨6, 16, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 6⟩) (by decide) node_6362

theorem node_9401 : Outcome ⟨6, 16, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 6⟩) (by decide) node_6362

theorem node_9402 : Outcome ⟨6, 16, 0, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 20⟩) (by decide) node_2234

theorem node_9403 : Outcome ⟨6, 16, 0, 24⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 20⟩) (by decide) node_2234

theorem node_9404 : Outcome ⟨7, 0, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 15, 2⟩, ⟨5, 0, 15, 4⟩, ⟨7, 0, 14, 2⟩, ⟨7, 0, 13, 4⟩]
  exact AllWinning.cons node_8343 (AllWinning.cons node_7351 (AllWinning.cons node_8415 (AllWinning.cons node_7484 (AllWinning.nil))))

theorem node_9405 : Outcome ⟨7, 0, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 15, 2⟩, ⟨5, 0, 15, 4⟩, ⟨4, 0, 15, 6⟩, ⟨3, 0, 15, 8⟩, ⟨7, 0, 14, 2⟩, ⟨7, 0, 13, 4⟩, ⟨7, 0, 12, 6⟩, ⟨7, 0, 11, 8⟩]
  exact AllWinning.cons node_8343 (AllWinning.cons node_7351 (AllWinning.cons node_6370 (AllWinning.cons node_5520 (AllWinning.cons node_8415 (AllWinning.cons node_7484 (AllWinning.cons node_6551 (AllWinning.cons node_5730 (AllWinning.nil))))))))

theorem node_9406 : Outcome ⟨7, 0, 15, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 10⟩) (by decide) node_4723

theorem node_9407 : Outcome ⟨7, 0, 15, 10⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 16⟩) (by decide) node_3168

theorem node_9408 : Outcome ⟨7, 0, 15, 16⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 16⟩) (by decide) node_3168

theorem node_9409 : Outcome ⟨7, 0, 15, 24⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 16⟩) (by decide) node_3168

theorem node_9410 : Outcome ⟨7, 1, 14, 6⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 6⟩) (by decide) node_6558

theorem node_9411 : Outcome ⟨7, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 2⟩) (by decide) node_8424

theorem node_9412 : Outcome ⟨7, 2, 13, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 10⟩) (by decide) node_4734

theorem node_9413 : Outcome ⟨7, 2, 13, 10⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 20⟩) (by decide) node_2258

theorem node_9414 : Outcome ⟨7, 2, 13, 14⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 20⟩) (by decide) node_2258

theorem node_9415 : Outcome ⟨7, 3, 12, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9416 : Outcome ⟨7, 3, 12, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9417 : Outcome ⟨7, 3, 12, 6⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9418 : Outcome ⟨7, 3, 12, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9419 : Outcome ⟨7, 3, 12, 24⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 20⟩) (by decide) node_2274

theorem node_9420 : Outcome ⟨7, 4, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 4, 11, 2⟩, ⟨5, 4, 11, 4⟩, ⟨7, 3, 11, 2⟩, ⟨7, 2, 11, 4⟩, ⟨7, 4, 10, 2⟩, ⟨7, 4, 9, 4⟩]
  exact AllWinning.cons node_8356 (AllWinning.cons node_7367 (AllWinning.cons node_8432 (AllWinning.cons node_7492 (AllWinning.cons node_8436 (AllWinning.cons node_7503 (AllWinning.nil))))))

theorem node_9421 : Outcome ⟨7, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 6⟩) (by decide) node_6558

theorem node_9422 : Outcome ⟨7, 4, 11, 6⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9423 : Outcome ⟨7, 4, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9424 : Outcome ⟨7, 4, 11, 24⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9425 : Outcome ⟨7, 5, 10, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 10, 4⟩) (by decide) node_7498

theorem node_9426 : Outcome ⟨7, 5, 10, 10⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9427 : Outcome ⟨7, 5, 10, 14⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9428 : Outcome ⟨7, 5, 10, 24⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9429 : Outcome ⟨7, 6, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9430 : Outcome ⟨7, 6, 9, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9431 : Outcome ⟨7, 6, 9, 8⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9432 : Outcome ⟨7, 6, 9, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9433 : Outcome ⟨7, 6, 9, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 9, 2⟩) (by decide) node_8363

theorem node_9434 : Outcome ⟨7, 7, 8, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 2⟩) (by decide) node_8367

theorem node_9435 : Outcome ⟨7, 7, 8, 8⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 16⟩) (by decide) node_3205

theorem node_9436 : Outcome ⟨7, 8, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 2⟩) (by decide) node_8379

theorem node_9437 : Outcome ⟨7, 8, 7, 8⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 16⟩) (by decide) node_3168

theorem node_9438 : Outcome ⟨7, 9, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 9, 6, 2⟩) (by decide) node_8391

theorem node_9439 : Outcome ⟨7, 9, 6, 6⟩ true :=
  Outcome.win (q := ⟨6, 9, 6, 2⟩) (by decide) node_8391

theorem node_9440 : Outcome ⟨7, 9, 6, 8⟩ true :=
  Outcome.win (q := ⟨6, 9, 6, 2⟩) (by decide) node_8391

theorem node_9441 : Outcome ⟨7, 9, 6, 14⟩ true :=
  Outcome.win (q := ⟨6, 9, 6, 2⟩) (by decide) node_8391

theorem node_9442 : Outcome ⟨7, 9, 6, 20⟩ true :=
  Outcome.win (q := ⟨6, 9, 6, 2⟩) (by decide) node_8391

theorem node_9443 : Outcome ⟨7, 10, 5, 2⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9444 : Outcome ⟨7, 10, 5, 10⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9445 : Outcome ⟨7, 10, 5, 14⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9446 : Outcome ⟨7, 10, 5, 24⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 12⟩) (by decide) node_4348

theorem node_9447 : Outcome ⟨7, 11, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 4, 2⟩, ⟨5, 11, 4, 4⟩, ⟨7, 10, 4, 2⟩, ⟨7, 9, 4, 4⟩, ⟨7, 11, 3, 2⟩, ⟨7, 11, 2, 4⟩]
  exact AllWinning.cons node_8399 (AllWinning.cons node_7392 (AllWinning.cons node_8474 (AllWinning.cons node_7518 (AllWinning.cons node_8478 (AllWinning.cons node_7526 (AllWinning.nil))))))

theorem node_9448 : Outcome ⟨7, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 6⟩) (by decide) node_6605

theorem node_9449 : Outcome ⟨7, 11, 4, 6⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9450 : Outcome ⟨7, 11, 4, 8⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9451 : Outcome ⟨7, 11, 4, 24⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 12⟩) (by decide) node_4363

theorem node_9452 : Outcome ⟨7, 12, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9453 : Outcome ⟨7, 12, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9454 : Outcome ⟨7, 12, 3, 6⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9455 : Outcome ⟨7, 12, 3, 8⟩ true :=
  Outcome.win (q := ⟨7, 10, 3, 4⟩) (by decide) node_7521

theorem node_9456 : Outcome ⟨7, 12, 3, 24⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 20⟩) (by decide) node_2258

theorem node_9457 : Outcome ⟨7, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 2⟩) (by decide) node_8482

theorem node_9458 : Outcome ⟨7, 13, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 10⟩) (by decide) node_4796

theorem node_9459 : Outcome ⟨7, 13, 2, 10⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 20⟩) (by decide) node_2274

theorem node_9460 : Outcome ⟨7, 13, 2, 14⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 20⟩) (by decide) node_2274

theorem node_9461 : Outcome ⟨7, 14, 1, 6⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 6⟩) (by decide) node_6605

theorem node_9462 : Outcome ⟨7, 15, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 0, 2⟩, ⟨5, 15, 0, 4⟩, ⟨7, 14, 0, 2⟩, ⟨7, 13, 0, 4⟩]
  exact AllWinning.cons node_8411 (AllWinning.cons node_7405 (AllWinning.cons node_8494 (AllWinning.cons node_7535 (AllWinning.nil))))

theorem node_9463 : Outcome ⟨7, 15, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 15, 0, 2⟩, ⟨5, 15, 0, 4⟩, ⟨4, 15, 0, 6⟩, ⟨3, 15, 0, 8⟩, ⟨7, 14, 0, 2⟩, ⟨7, 13, 0, 4⟩, ⟨7, 12, 0, 6⟩, ⟨7, 11, 0, 8⟩]
  exact AllWinning.cons node_8411 (AllWinning.cons node_7405 (AllWinning.cons node_6420 (AllWinning.cons node_5573 (AllWinning.cons node_8494 (AllWinning.cons node_7535 (AllWinning.cons node_6616 (AllWinning.cons node_5773 (AllWinning.nil))))))))

theorem node_9464 : Outcome ⟨7, 15, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 10⟩) (by decide) node_4806

theorem node_9465 : Outcome ⟨7, 15, 0, 10⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 16⟩) (by decide) node_3205

theorem node_9466 : Outcome ⟨7, 15, 0, 16⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 16⟩) (by decide) node_3205

theorem node_9467 : Outcome ⟨7, 15, 0, 24⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 16⟩) (by decide) node_3205

theorem node_9468 : Outcome ⟨8, 0, 14, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 14, 4⟩) (by decide) node_7410

theorem node_9469 : Outcome ⟨8, 0, 14, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 14, 4⟩) (by decide) node_7410

theorem node_9470 : Outcome ⟨8, 0, 14, 12⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 12⟩) (by decide) node_4395

theorem node_9471 : Outcome ⟨8, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 13, 4⟩) (by decide) node_7415

theorem node_9472 : Outcome ⟨8, 1, 13, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 13, 4⟩) (by decide) node_7415

theorem node_9473 : Outcome ⟨8, 1, 13, 18⟩ true :=
  Outcome.win (q := ⟨6, 1, 13, 4⟩) (by decide) node_7415

theorem node_9474 : Outcome ⟨8, 2, 12, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 2⟩) (by decide) node_8424

theorem node_9475 : Outcome ⟨8, 2, 12, 12⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 2⟩) (by decide) node_8424

theorem node_9476 : Outcome ⟨8, 2, 12, 14⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 2⟩) (by decide) node_8424

theorem node_9477 : Outcome ⟨8, 3, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 11, 2⟩, ⟨6, 3, 11, 4⟩, ⟨8, 2, 11, 2⟩, ⟨8, 1, 11, 4⟩, ⟨8, 3, 10, 2⟩, ⟨8, 3, 9, 4⟩]
  exact AllWinning.cons node_8432 (AllWinning.cons node_7423 (AllWinning.cons node_8512 (AllWinning.cons node_7542 (AllWinning.cons node_8516 (AllWinning.cons node_7549 (AllWinning.nil))))))

theorem node_9478 : Outcome ⟨8, 3, 11, 8⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 6⟩) (by decide) node_6434

theorem node_9479 : Outcome ⟨8, 3, 11, 10⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 6⟩) (by decide) node_6434

theorem node_9480 : Outcome ⟨8, 3, 11, 14⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 6⟩) (by decide) node_6434

theorem node_9481 : Outcome ⟨8, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9482 : Outcome ⟨8, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9483 : Outcome ⟨8, 4, 10, 6⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9484 : Outcome ⟨8, 4, 10, 14⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 4⟩) (by decide) node_7427

theorem node_9485 : Outcome ⟨8, 5, 9, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 8, 2⟩) (by decide) node_8524

theorem node_9486 : Outcome ⟨8, 5, 9, 8⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 14⟩) (by decide) node_3418

theorem node_9487 : Outcome ⟨8, 5, 9, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 14⟩) (by decide) node_3418

theorem node_9488 : Outcome ⟨8, 6, 8, 4⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 2⟩) (by decide) node_8443

theorem node_9489 : Outcome ⟨8, 6, 8, 12⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 12⟩) (by decide) node_4395

theorem node_9490 : Outcome ⟨8, 6, 8, 24⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 12⟩) (by decide) node_4395

theorem node_9491 : Outcome ⟨8, 7, 7, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 2⟩) (by decide) node_8455

theorem node_9492 : Outcome ⟨8, 7, 7, 8⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 16⟩) (by decide) node_2856

theorem node_9493 : Outcome ⟨8, 8, 6, 4⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 2⟩) (by decide) node_8459

theorem node_9494 : Outcome ⟨8, 8, 6, 12⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 12⟩) (by decide) node_4436

end RQ9F1
