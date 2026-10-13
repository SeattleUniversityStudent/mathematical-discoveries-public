import Chunk65
set_option autoImplicit false
namespace RQ9F1

theorem node_15060 : Outcome ⟨2, 18, 8, 16⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 2⟩) (by decide) node_14042

theorem node_15061 : Outcome ⟨2, 19, 7, 2⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 2⟩) (by decide) node_14086

theorem node_15062 : Outcome ⟨2, 19, 7, 8⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 2⟩) (by decide) node_14086

theorem node_15063 : Outcome ⟨2, 20, 6, 6⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 6⟩) (by decide) node_12147

theorem node_15064 : Outcome ⟨2, 20, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 6⟩) (by decide) node_12147

theorem node_15065 : Outcome ⟨3, 5, 20, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 19, 2⟩) (by decide) node_14100

theorem node_15066 : Outcome ⟨3, 5, 20, 14⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 18⟩) (by decide) node_6307

theorem node_15067 : Outcome ⟨3, 6, 19, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 19, 2⟩) (by decide) node_14100

theorem node_15068 : Outcome ⟨3, 6, 19, 8⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 10⟩) (by decide) node_10093

theorem node_15069 : Outcome ⟨3, 6, 19, 10⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 10⟩) (by decide) node_10093

theorem node_15070 : Outcome ⟨3, 7, 18, 2⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 2⟩) (by decide) node_14056

theorem node_15071 : Outcome ⟨3, 7, 18, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 6⟩) (by decide) node_12170

theorem node_15072 : Outcome ⟨3, 7, 18, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 6⟩) (by decide) node_12170

theorem node_15073 : Outcome ⟨3, 7, 18, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 32⟩) (by decide) node_2110

theorem node_15074 : Outcome ⟨3, 8, 17, 2⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 2⟩) (by decide) node_14109

theorem node_15075 : Outcome ⟨3, 8, 17, 12⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 2⟩) (by decide) node_14109

theorem node_15076 : Outcome ⟨3, 9, 16, 2⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 2⟩) (by decide) node_14109

theorem node_15077 : Outcome ⟨3, 9, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 8⟩) (by decide) node_11175

theorem node_15078 : Outcome ⟨3, 10, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 6⟩) (by decide) node_12170

theorem node_15079 : Outcome ⟨3, 10, 15, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 6⟩) (by decide) node_12170

theorem node_15080 : Outcome ⟨3, 10, 15, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 6⟩) (by decide) node_12170

theorem node_15081 : Outcome ⟨3, 11, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 14, 2⟩, ⟨1, 11, 14, 4⟩, ⟨3, 10, 14, 2⟩, ⟨3, 9, 14, 4⟩, ⟨3, 11, 13, 2⟩, ⟨3, 11, 12, 4⟩]
  exact AllWinning.cons node_14071 (AllWinning.cons node_13048 (AllWinning.cons node_14122 (AllWinning.cons node_13148 (AllWinning.cons node_14125 (AllWinning.cons node_13160 (AllWinning.nil))))))

theorem node_15082 : Outcome ⟨3, 11, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 14, 2⟩, ⟨1, 11, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨3, 10, 14, 2⟩, ⟨3, 9, 14, 4⟩, ⟨3, 8, 14, 6⟩, ⟨3, 7, 14, 8⟩, ⟨3, 11, 13, 2⟩, ⟨3, 11, 12, 4⟩, ⟨3, 11, 11, 6⟩, ⟨3, 11, 10, 8⟩]
  exact AllWinning.cons node_14071 (AllWinning.cons node_13048 (AllWinning.cons node_11982 (AllWinning.cons node_14122 (AllWinning.cons node_13148 (AllWinning.cons node_12177 (AllWinning.cons node_11168 (AllWinning.cons node_14125 (AllWinning.cons node_13160 (AllWinning.cons node_12185 (AllWinning.cons node_11190 (AllWinning.nil)))))))))))

theorem node_15083 : Outcome ⟨3, 11, 14, 10⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 18⟩) (by decide) node_6338

theorem node_15084 : Outcome ⟨3, 11, 14, 12⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 18⟩) (by decide) node_6338

theorem node_15085 : Outcome ⟨3, 12, 13, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 4⟩) (by decide) node_13151

theorem node_15086 : Outcome ⟨3, 12, 13, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 8⟩) (by decide) node_11196

theorem node_15087 : Outcome ⟨3, 12, 13, 8⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 8⟩) (by decide) node_11196

theorem node_15088 : Outcome ⟨3, 12, 13, 14⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 8⟩) (by decide) node_11196

theorem node_15089 : Outcome ⟨3, 13, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 4⟩) (by decide) node_13169

theorem node_15090 : Outcome ⟨3, 13, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 8⟩) (by decide) node_11175

theorem node_15091 : Outcome ⟨3, 13, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 8⟩) (by decide) node_11175

theorem node_15092 : Outcome ⟨3, 13, 12, 14⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 8⟩) (by decide) node_11175

theorem node_15093 : Outcome ⟨3, 14, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 11, 2⟩, ⟨1, 14, 11, 4⟩, ⟨3, 13, 11, 2⟩, ⟨3, 12, 11, 4⟩, ⟨3, 14, 10, 2⟩, ⟨3, 14, 9, 4⟩]
  exact AllWinning.cons node_14077 (AllWinning.cons node_13060 (AllWinning.cons node_14132 (AllWinning.cons node_13165 (AllWinning.cons node_14135 (AllWinning.cons node_13177 (AllWinning.nil))))))

theorem node_15094 : Outcome ⟨3, 14, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 11, 2⟩, ⟨1, 14, 11, 4⟩, ⟨0, 14, 11, 6⟩, ⟨3, 13, 11, 2⟩, ⟨3, 12, 11, 4⟩, ⟨3, 11, 11, 6⟩, ⟨3, 10, 11, 8⟩, ⟨3, 14, 10, 2⟩, ⟨3, 14, 9, 4⟩, ⟨3, 14, 8, 6⟩, ⟨3, 14, 7, 8⟩]
  exact AllWinning.cons node_14077 (AllWinning.cons node_13060 (AllWinning.cons node_11988 (AllWinning.cons node_14132 (AllWinning.cons node_13165 (AllWinning.cons node_12185 (AllWinning.cons node_11185 (AllWinning.cons node_14135 (AllWinning.cons node_13177 (AllWinning.cons node_12193 (AllWinning.cons node_11207 (AllWinning.nil)))))))))))

theorem node_15095 : Outcome ⟨3, 14, 11, 10⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 18⟩) (by decide) node_6307

theorem node_15096 : Outcome ⟨3, 14, 11, 12⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 18⟩) (by decide) node_6307

theorem node_15097 : Outcome ⟨3, 15, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 6⟩) (by decide) node_12197

theorem node_15098 : Outcome ⟨3, 15, 10, 6⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 6⟩) (by decide) node_12197

theorem node_15099 : Outcome ⟨3, 15, 10, 16⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 6⟩) (by decide) node_12197

theorem node_15100 : Outcome ⟨3, 16, 9, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 2⟩) (by decide) node_14142

theorem node_15101 : Outcome ⟨3, 16, 9, 8⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 8⟩) (by decide) node_11196

theorem node_15102 : Outcome ⟨3, 17, 8, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 2⟩) (by decide) node_14142

theorem node_15103 : Outcome ⟨3, 17, 8, 12⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 2⟩) (by decide) node_14142

theorem node_15104 : Outcome ⟨3, 18, 7, 2⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 2⟩) (by decide) node_14086

theorem node_15105 : Outcome ⟨3, 18, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 6⟩) (by decide) node_12197

theorem node_15106 : Outcome ⟨3, 18, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 6⟩) (by decide) node_12197

theorem node_15107 : Outcome ⟨3, 18, 7, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 32⟩) (by decide) node_2079

theorem node_15108 : Outcome ⟨3, 19, 6, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 6, 2⟩) (by decide) node_14153

theorem node_15109 : Outcome ⟨3, 19, 6, 8⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 10⟩) (by decide) node_10144

theorem node_15110 : Outcome ⟨3, 19, 6, 10⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 10⟩) (by decide) node_10144

theorem node_15111 : Outcome ⟨3, 20, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 19, 5, 2⟩) (by decide) node_14157

theorem node_15112 : Outcome ⟨3, 20, 5, 14⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 18⟩) (by decide) node_6338

theorem node_15113 : Outcome ⟨4, 4, 20, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 18, 4⟩) (by decide) node_13203

theorem node_15114 : Outcome ⟨4, 5, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 17, 4⟩) (by decide) node_13206

theorem node_15115 : Outcome ⟨4, 5, 19, 12⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 24⟩) (by decide) node_4181

theorem node_15116 : Outcome ⟨4, 5, 19, 18⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 24⟩) (by decide) node_4181

theorem node_15117 : Outcome ⟨4, 6, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 18, 4⟩) (by decide) node_13203

theorem node_15118 : Outcome ⟨4, 6, 18, 10⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 16⟩) (by decide) node_7300

theorem node_15119 : Outcome ⟨4, 6, 18, 12⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 16⟩) (by decide) node_7300

theorem node_15120 : Outcome ⟨4, 7, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 17, 4⟩) (by decide) node_13206

theorem node_15121 : Outcome ⟨4, 8, 16, 2⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 2⟩) (by decide) node_14109

theorem node_15122 : Outcome ⟨4, 9, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 4⟩) (by decide) node_13091

theorem node_15123 : Outcome ⟨4, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 4⟩) (by decide) node_13091

theorem node_15124 : Outcome ⟨4, 9, 15, 10⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 4⟩) (by decide) node_13091

theorem node_15125 : Outcome ⟨4, 10, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 10, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨4, 9, 14, 2⟩, ⟨4, 8, 14, 4⟩, ⟨4, 10, 13, 2⟩, ⟨4, 10, 12, 4⟩]
  exact AllWinning.cons node_14122 (AllWinning.cons node_13098 (AllWinning.cons node_14176 (AllWinning.cons node_13212 (AllWinning.cons node_14179 (AllWinning.cons node_13218 (AllWinning.nil))))))

theorem node_15126 : Outcome ⟨4, 10, 14, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 6⟩) (by decide) node_12034

theorem node_15127 : Outcome ⟨4, 10, 14, 18⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 16⟩) (by decide) node_7320

theorem node_15128 : Outcome ⟨4, 11, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 4⟩) (by decide) node_13100

theorem node_15129 : Outcome ⟨4, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 4⟩) (by decide) node_13100

theorem node_15130 : Outcome ⟨4, 11, 13, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 4⟩) (by decide) node_13100

theorem node_15131 : Outcome ⟨4, 12, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 12, 12, 2⟩) (by decide) node_14128

theorem node_15132 : Outcome ⟨4, 12, 12, 6⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 8⟩) (by decide) node_11002

theorem node_15133 : Outcome ⟨4, 13, 11, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 4⟩) (by decide) node_13106

theorem node_15134 : Outcome ⟨4, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 4⟩) (by decide) node_13106

theorem node_15135 : Outcome ⟨4, 13, 11, 10⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 4⟩) (by decide) node_13106

theorem node_15136 : Outcome ⟨4, 14, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 14, 10, 2⟩, ⟨2, 14, 10, 4⟩, ⟨4, 13, 10, 2⟩, ⟨4, 12, 10, 4⟩, ⟨4, 14, 9, 2⟩, ⟨4, 14, 8, 4⟩]
  exact AllWinning.cons node_14135 (AllWinning.cons node_13109 (AllWinning.cons node_14186 (AllWinning.cons node_13224 (AllWinning.cons node_14189 (AllWinning.cons node_13228 (AllWinning.nil))))))

theorem node_15137 : Outcome ⟨4, 14, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 6⟩) (by decide) node_12054

theorem node_15138 : Outcome ⟨4, 14, 10, 18⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 16⟩) (by decide) node_7300

theorem node_15139 : Outcome ⟨4, 15, 9, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 4⟩) (by decide) node_13110

theorem node_15140 : Outcome ⟨4, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 4⟩) (by decide) node_13110

theorem node_15141 : Outcome ⟨4, 15, 9, 10⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 4⟩) (by decide) node_13110

theorem node_15142 : Outcome ⟨4, 16, 8, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 2⟩) (by decide) node_14142

theorem node_15143 : Outcome ⟨4, 17, 7, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 5, 4⟩) (by decide) node_13236

theorem node_15144 : Outcome ⟨4, 18, 6, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 4, 4⟩) (by decide) node_13239

theorem node_15145 : Outcome ⟨4, 18, 6, 10⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 16⟩) (by decide) node_7320

theorem node_15146 : Outcome ⟨4, 18, 6, 12⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 16⟩) (by decide) node_7320

theorem node_15147 : Outcome ⟨4, 19, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 5, 4⟩) (by decide) node_13236

theorem node_15148 : Outcome ⟨4, 19, 5, 12⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 24⟩) (by decide) node_4198

theorem node_15149 : Outcome ⟨4, 19, 5, 18⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 24⟩) (by decide) node_4198

theorem node_15150 : Outcome ⟨4, 20, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 4, 4⟩) (by decide) node_13239

theorem node_15151 : Outcome ⟨5, 3, 20, 2⟩ true :=
  Outcome.win (q := ⟨5, 3, 19, 2⟩) (by decide) node_14207

theorem node_15152 : Outcome ⟨5, 4, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 17, 4⟩) (by decide) node_13253

theorem node_15153 : Outcome ⟨5, 4, 19, 12⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 24⟩) (by decide) node_4247

theorem node_15154 : Outcome ⟨5, 4, 19, 18⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 24⟩) (by decide) node_4247

theorem node_15155 : Outcome ⟨5, 5, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 18, 2⟩, ⟨3, 5, 18, 4⟩, ⟨5, 4, 18, 2⟩, ⟨5, 3, 18, 4⟩, ⟨5, 5, 17, 2⟩, ⟨5, 5, 16, 4⟩]
  exact AllWinning.cons node_14166 (AllWinning.cons node_13135 (AllWinning.cons node_14211 (AllWinning.cons node_13250 (AllWinning.cons node_14215 (AllWinning.cons node_13256 (AllWinning.nil))))))

theorem node_15156 : Outcome ⟨5, 5, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 18, 2⟩, ⟨3, 5, 18, 4⟩, ⟨2, 5, 18, 6⟩, ⟨1, 5, 18, 8⟩, ⟨5, 4, 18, 2⟩, ⟨5, 3, 18, 4⟩, ⟨5, 2, 18, 6⟩, ⟨5, 1, 18, 8⟩, ⟨5, 5, 17, 2⟩, ⟨5, 5, 16, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 5, 14, 8⟩]
  exact AllWinning.cons node_14166 (AllWinning.cons node_13135 (AllWinning.cons node_12093 (AllWinning.cons node_11038 (AllWinning.cons node_14211 (AllWinning.cons node_13250 (AllWinning.cons node_12286 (AllWinning.cons node_11302 (AllWinning.cons node_14215 (AllWinning.cons node_13256 (AllWinning.cons node_12296 (AllWinning.cons node_11314 (AllWinning.nil))))))))))))

theorem node_15157 : Outcome ⟨5, 5, 18, 14⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 10⟩) (by decide) node_9879

theorem node_15158 : Outcome ⟨5, 6, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 17, 4⟩) (by decide) node_13253

theorem node_15159 : Outcome ⟨5, 6, 17, 8⟩ true :=
  Outcome.win (q := ⟨5, 4, 17, 4⟩) (by decide) node_13253

theorem node_15160 : Outcome ⟨5, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 6, 16, 2⟩) (by decide) node_14217

theorem node_15161 : Outcome ⟨5, 7, 16, 12⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 24⟩) (by decide) node_4264

theorem node_15162 : Outcome ⟨5, 8, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.nil))))))

theorem node_15163 : Outcome ⟨5, 8, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.nil))))))))))))

theorem node_15164 : Outcome ⟨5, 8, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.nil)))))))))))))))))

theorem node_15165 : Outcome ⟨5, 8, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 1, 15, 14⟩, ⟨5, 0, 15, 16⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 8, 7, 16⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_8293 (AllWinning.cons node_7353 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.cons node_8316 (AllWinning.cons node_7382 (AllWinning.nil)))))))))))))))))))))

theorem node_15166 : Outcome ⟨5, 8, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 1, 15, 14⟩, ⟨5, 0, 15, 16⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 8, 7, 16⟩, ⟨5, 8, 6, 18⟩, ⟨5, 8, 5, 20⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_8293 (AllWinning.cons node_7353 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.cons node_8316 (AllWinning.cons node_7382 (AllWinning.cons node_6458 (AllWinning.cons node_5663 (AllWinning.nil)))))))))))))))))))))))

theorem node_15167 : Outcome ⟨5, 8, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 1, 15, 14⟩, ⟨5, 0, 15, 16⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 8, 7, 16⟩, ⟨5, 8, 6, 18⟩, ⟨5, 8, 5, 20⟩, ⟨5, 8, 4, 22⟩, ⟨5, 8, 3, 24⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_8293 (AllWinning.cons node_7353 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.cons node_8316 (AllWinning.cons node_7382 (AllWinning.cons node_6458 (AllWinning.cons node_5663 (AllWinning.cons node_4962 (AllWinning.cons node_4269 (AllWinning.nil)))))))))))))))))))))))))

theorem node_15168 : Outcome ⟨5, 8, 15, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 1, 15, 14⟩, ⟨5, 0, 15, 16⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 8, 7, 16⟩, ⟨5, 8, 6, 18⟩, ⟨5, 8, 5, 20⟩, ⟨5, 8, 4, 22⟩, ⟨5, 8, 3, 24⟩, ⟨5, 8, 2, 26⟩, ⟨5, 8, 1, 28⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_8293 (AllWinning.cons node_7353 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.cons node_8316 (AllWinning.cons node_7382 (AllWinning.cons node_6458 (AllWinning.cons node_5663 (AllWinning.cons node_4962 (AllWinning.cons node_4269 (AllWinning.cons node_3670 (AllWinning.cons node_3120 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_15169 : Outcome ⟨5, 8, 15, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 1, 15, 14⟩, ⟨5, 0, 15, 16⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 8, 7, 16⟩, ⟨5, 8, 6, 18⟩, ⟨5, 8, 5, 20⟩, ⟨5, 8, 4, 22⟩, ⟨5, 8, 3, 24⟩, ⟨5, 8, 2, 26⟩, ⟨5, 8, 1, 28⟩, ⟨5, 8, 0, 30⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_8293 (AllWinning.cons node_7353 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.cons node_8316 (AllWinning.cons node_7382 (AllWinning.cons node_6458 (AllWinning.cons node_5663 (AllWinning.cons node_4962 (AllWinning.cons node_4269 (AllWinning.cons node_3670 (AllWinning.cons node_3120 (AllWinning.cons node_2666 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15170 : Outcome ⟨5, 8, 15, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 1, 15, 14⟩, ⟨5, 0, 15, 16⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 8, 7, 16⟩, ⟨5, 8, 6, 18⟩, ⟨5, 8, 5, 20⟩, ⟨5, 8, 4, 22⟩, ⟨5, 8, 3, 24⟩, ⟨5, 8, 2, 26⟩, ⟨5, 8, 1, 28⟩, ⟨5, 8, 0, 30⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_8293 (AllWinning.cons node_7353 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.cons node_8316 (AllWinning.cons node_7382 (AllWinning.cons node_6458 (AllWinning.cons node_5663 (AllWinning.cons node_4962 (AllWinning.cons node_4269 (AllWinning.cons node_3670 (AllWinning.cons node_3120 (AllWinning.cons node_2666 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15171 : Outcome ⟨5, 8, 15, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 15, 2⟩, ⟨3, 8, 15, 4⟩, ⟨2, 8, 15, 6⟩, ⟨1, 8, 15, 8⟩, ⟨0, 8, 15, 10⟩, ⟨5, 7, 15, 2⟩, ⟨5, 6, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨5, 4, 15, 8⟩, ⟨5, 3, 15, 10⟩, ⟨5, 2, 15, 12⟩, ⟨5, 1, 15, 14⟩, ⟨5, 0, 15, 16⟩, ⟨5, 8, 14, 2⟩, ⟨5, 8, 13, 4⟩, ⟨5, 8, 12, 6⟩, ⟨5, 8, 11, 8⟩, ⟨5, 8, 10, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 8, 7, 16⟩, ⟨5, 8, 6, 18⟩, ⟨5, 8, 5, 20⟩, ⟨5, 8, 4, 22⟩, ⟨5, 8, 3, 24⟩, ⟨5, 8, 2, 26⟩, ⟨5, 8, 1, 28⟩, ⟨5, 8, 0, 30⟩]
  exact AllWinning.cons node_14174 (AllWinning.cons node_13145 (AllWinning.cons node_12107 (AllWinning.cons node_11049 (AllWinning.cons node_9892 (AllWinning.cons node_14220 (AllWinning.cons node_13258 (AllWinning.cons node_12296 (AllWinning.cons node_11312 (AllWinning.cons node_10262 (AllWinning.cons node_9280 (AllWinning.cons node_8293 (AllWinning.cons node_7353 (AllWinning.cons node_14223 (AllWinning.cons node_13263 (AllWinning.cons node_12304 (AllWinning.cons node_11325 (AllWinning.cons node_10286 (AllWinning.cons node_9302 (AllWinning.cons node_8316 (AllWinning.cons node_7382 (AllWinning.cons node_6458 (AllWinning.cons node_5663 (AllWinning.cons node_4962 (AllWinning.cons node_4269 (AllWinning.cons node_3670 (AllWinning.cons node_3120 (AllWinning.cons node_2666 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15172 : Outcome ⟨5, 9, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 9, 14, 2⟩, ⟨3, 9, 14, 4⟩, ⟨5, 8, 14, 2⟩, ⟨5, 7, 14, 4⟩, ⟨5, 9, 13, 2⟩, ⟨5, 9, 12, 4⟩]
  exact AllWinning.cons node_14176 (AllWinning.cons node_13148 (AllWinning.cons node_14223 (AllWinning.cons node_13260 (AllWinning.cons node_14224 (AllWinning.cons node_13265 (AllWinning.nil))))))

theorem node_15173 : Outcome ⟨5, 9, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 9, 14, 2⟩, ⟨3, 9, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨1, 9, 14, 8⟩, ⟨5, 8, 14, 2⟩, ⟨5, 7, 14, 4⟩, ⟨5, 6, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨5, 9, 13, 2⟩, ⟨5, 9, 12, 4⟩, ⟨5, 9, 11, 6⟩, ⟨5, 9, 10, 8⟩]
  exact AllWinning.cons node_14176 (AllWinning.cons node_13148 (AllWinning.cons node_12110 (AllWinning.cons node_11053 (AllWinning.cons node_14223 (AllWinning.cons node_13260 (AllWinning.cons node_12298 (AllWinning.cons node_11314 (AllWinning.cons node_14224 (AllWinning.cons node_13265 (AllWinning.cons node_12307 (AllWinning.cons node_11329 (AllWinning.nil))))))))))))

theorem node_15174 : Outcome ⟨5, 9, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 9, 14, 2⟩, ⟨3, 9, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨1, 9, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨5, 8, 14, 2⟩, ⟨5, 7, 14, 4⟩, ⟨5, 6, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨5, 4, 14, 10⟩, ⟨5, 3, 14, 12⟩, ⟨5, 9, 13, 2⟩, ⟨5, 9, 12, 4⟩, ⟨5, 9, 11, 6⟩, ⟨5, 9, 10, 8⟩, ⟨5, 9, 9, 10⟩, ⟨5, 9, 8, 12⟩]
  exact AllWinning.cons node_14176 (AllWinning.cons node_13148 (AllWinning.cons node_12110 (AllWinning.cons node_11053 (AllWinning.cons node_9897 (AllWinning.cons node_14223 (AllWinning.cons node_13260 (AllWinning.cons node_12298 (AllWinning.cons node_11314 (AllWinning.cons node_10265 (AllWinning.cons node_9283 (AllWinning.cons node_14224 (AllWinning.cons node_13265 (AllWinning.cons node_12307 (AllWinning.cons node_11329 (AllWinning.cons node_10292 (AllWinning.cons node_9306 (AllWinning.nil)))))))))))))))))

theorem node_15175 : Outcome ⟨5, 9, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 9, 14, 2⟩, ⟨3, 9, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨1, 9, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨5, 8, 14, 2⟩, ⟨5, 7, 14, 4⟩, ⟨5, 6, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨5, 4, 14, 10⟩, ⟨5, 3, 14, 12⟩, ⟨5, 2, 14, 14⟩, ⟨5, 1, 14, 16⟩, ⟨5, 9, 13, 2⟩, ⟨5, 9, 12, 4⟩, ⟨5, 9, 11, 6⟩, ⟨5, 9, 10, 8⟩, ⟨5, 9, 9, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 9, 7, 14⟩, ⟨5, 9, 6, 16⟩]
  exact AllWinning.cons node_14176 (AllWinning.cons node_13148 (AllWinning.cons node_12110 (AllWinning.cons node_11053 (AllWinning.cons node_9897 (AllWinning.cons node_14223 (AllWinning.cons node_13260 (AllWinning.cons node_12298 (AllWinning.cons node_11314 (AllWinning.cons node_10265 (AllWinning.cons node_9283 (AllWinning.cons node_8296 (AllWinning.cons node_7358 (AllWinning.cons node_14224 (AllWinning.cons node_13265 (AllWinning.cons node_12307 (AllWinning.cons node_11329 (AllWinning.cons node_10292 (AllWinning.cons node_9306 (AllWinning.cons node_8318 (AllWinning.cons node_7387 (AllWinning.nil)))))))))))))))))))))

theorem node_15176 : Outcome ⟨5, 9, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 9, 14, 2⟩, ⟨3, 9, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨1, 9, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨5, 8, 14, 2⟩, ⟨5, 7, 14, 4⟩, ⟨5, 6, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨5, 4, 14, 10⟩, ⟨5, 3, 14, 12⟩, ⟨5, 2, 14, 14⟩, ⟨5, 1, 14, 16⟩, ⟨5, 0, 14, 18⟩, ⟨5, 9, 13, 2⟩, ⟨5, 9, 12, 4⟩, ⟨5, 9, 11, 6⟩, ⟨5, 9, 10, 8⟩, ⟨5, 9, 9, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 9, 7, 14⟩, ⟨5, 9, 6, 16⟩, ⟨5, 9, 5, 18⟩, ⟨5, 9, 4, 20⟩, ⟨5, 9, 3, 22⟩, ⟨5, 9, 2, 24⟩]
  exact AllWinning.cons node_14176 (AllWinning.cons node_13148 (AllWinning.cons node_12110 (AllWinning.cons node_11053 (AllWinning.cons node_9897 (AllWinning.cons node_14223 (AllWinning.cons node_13260 (AllWinning.cons node_12298 (AllWinning.cons node_11314 (AllWinning.cons node_10265 (AllWinning.cons node_9283 (AllWinning.cons node_8296 (AllWinning.cons node_7358 (AllWinning.cons node_6424 (AllWinning.cons node_14224 (AllWinning.cons node_13265 (AllWinning.cons node_12307 (AllWinning.cons node_11329 (AllWinning.cons node_10292 (AllWinning.cons node_9306 (AllWinning.cons node_8318 (AllWinning.cons node_7387 (AllWinning.cons node_6460 (AllWinning.cons node_5666 (AllWinning.cons node_4967 (AllWinning.cons node_4272 (AllWinning.nil))))))))))))))))))))))))))

theorem node_15177 : Outcome ⟨5, 10, 13, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 4⟩) (by decide) node_13151

theorem node_15178 : Outcome ⟨5, 10, 13, 6⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 10⟩) (by decide) node_10272

theorem node_15179 : Outcome ⟨5, 10, 13, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 10⟩) (by decide) node_10272

theorem node_15180 : Outcome ⟨5, 10, 13, 12⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 22⟩) (by decide) node_4978

theorem node_15181 : Outcome ⟨5, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 2⟩) (by decide) node_14227

theorem node_15182 : Outcome ⟨5, 11, 12, 14⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 18⟩) (by decide) node_6473

theorem node_15183 : Outcome ⟨5, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨5, 11, 11, 2⟩) (by decide) node_14233

theorem node_15184 : Outcome ⟨5, 12, 11, 14⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 18⟩) (by decide) node_6440

theorem node_15185 : Outcome ⟨5, 13, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 4⟩) (by decide) node_13169

theorem node_15186 : Outcome ⟨5, 13, 10, 6⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 10⟩) (by decide) node_10312

theorem node_15187 : Outcome ⟨5, 13, 10, 10⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 10⟩) (by decide) node_10312

theorem node_15188 : Outcome ⟨5, 13, 10, 12⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 22⟩) (by decide) node_4940

theorem node_15189 : Outcome ⟨5, 14, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 9, 2⟩, ⟨3, 14, 9, 4⟩, ⟨5, 13, 9, 2⟩, ⟨5, 12, 9, 4⟩, ⟨5, 14, 8, 2⟩, ⟨5, 14, 7, 4⟩]
  exact AllWinning.cons node_14189 (AllWinning.cons node_13177 (AllWinning.cons node_14241 (AllWinning.cons node_13274 (AllWinning.cons node_14244 (AllWinning.cons node_13278 (AllWinning.nil))))))

theorem node_15190 : Outcome ⟨5, 14, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 9, 2⟩, ⟨3, 14, 9, 4⟩, ⟨2, 14, 9, 6⟩, ⟨1, 14, 9, 8⟩, ⟨5, 13, 9, 2⟩, ⟨5, 12, 9, 4⟩, ⟨5, 11, 9, 6⟩, ⟨5, 10, 9, 8⟩, ⟨5, 14, 8, 2⟩, ⟨5, 14, 7, 4⟩, ⟨5, 14, 6, 6⟩, ⟨5, 14, 5, 8⟩]
  exact AllWinning.cons node_14189 (AllWinning.cons node_13177 (AllWinning.cons node_12124 (AllWinning.cons node_11070 (AllWinning.cons node_14241 (AllWinning.cons node_13274 (AllWinning.cons node_12313 (AllWinning.cons node_11333 (AllWinning.cons node_14244 (AllWinning.cons node_13278 (AllWinning.cons node_12322 (AllWinning.cons node_11347 (AllWinning.nil))))))))))))

theorem node_15191 : Outcome ⟨5, 14, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 9, 2⟩, ⟨3, 14, 9, 4⟩, ⟨2, 14, 9, 6⟩, ⟨1, 14, 9, 8⟩, ⟨0, 14, 9, 10⟩, ⟨5, 13, 9, 2⟩, ⟨5, 12, 9, 4⟩, ⟨5, 11, 9, 6⟩, ⟨5, 10, 9, 8⟩, ⟨5, 9, 9, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 14, 8, 2⟩, ⟨5, 14, 7, 4⟩, ⟨5, 14, 6, 6⟩, ⟨5, 14, 5, 8⟩, ⟨5, 14, 4, 10⟩, ⟨5, 14, 3, 12⟩]
  exact AllWinning.cons node_14189 (AllWinning.cons node_13177 (AllWinning.cons node_12124 (AllWinning.cons node_11070 (AllWinning.cons node_9909 (AllWinning.cons node_14241 (AllWinning.cons node_13274 (AllWinning.cons node_12313 (AllWinning.cons node_11333 (AllWinning.cons node_10292 (AllWinning.cons node_9302 (AllWinning.cons node_14244 (AllWinning.cons node_13278 (AllWinning.cons node_12322 (AllWinning.cons node_11347 (AllWinning.cons node_10316 (AllWinning.cons node_9324 (AllWinning.nil)))))))))))))))))

theorem node_15192 : Outcome ⟨5, 14, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 9, 2⟩, ⟨3, 14, 9, 4⟩, ⟨2, 14, 9, 6⟩, ⟨1, 14, 9, 8⟩, ⟨0, 14, 9, 10⟩, ⟨5, 13, 9, 2⟩, ⟨5, 12, 9, 4⟩, ⟨5, 11, 9, 6⟩, ⟨5, 10, 9, 8⟩, ⟨5, 9, 9, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 7, 9, 14⟩, ⟨5, 6, 9, 16⟩, ⟨5, 14, 8, 2⟩, ⟨5, 14, 7, 4⟩, ⟨5, 14, 6, 6⟩, ⟨5, 14, 5, 8⟩, ⟨5, 14, 4, 10⟩, ⟨5, 14, 3, 12⟩, ⟨5, 14, 2, 14⟩, ⟨5, 14, 1, 16⟩]
  exact AllWinning.cons node_14189 (AllWinning.cons node_13177 (AllWinning.cons node_12124 (AllWinning.cons node_11070 (AllWinning.cons node_9909 (AllWinning.cons node_14241 (AllWinning.cons node_13274 (AllWinning.cons node_12313 (AllWinning.cons node_11333 (AllWinning.cons node_10292 (AllWinning.cons node_9302 (AllWinning.cons node_8311 (AllWinning.cons node_7374 (AllWinning.cons node_14244 (AllWinning.cons node_13278 (AllWinning.cons node_12322 (AllWinning.cons node_11347 (AllWinning.cons node_10316 (AllWinning.cons node_9324 (AllWinning.cons node_8334 (AllWinning.cons node_7404 (AllWinning.nil)))))))))))))))))))))

theorem node_15193 : Outcome ⟨5, 14, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 9, 2⟩, ⟨3, 14, 9, 4⟩, ⟨2, 14, 9, 6⟩, ⟨1, 14, 9, 8⟩, ⟨0, 14, 9, 10⟩, ⟨5, 13, 9, 2⟩, ⟨5, 12, 9, 4⟩, ⟨5, 11, 9, 6⟩, ⟨5, 10, 9, 8⟩, ⟨5, 9, 9, 10⟩, ⟨5, 8, 9, 12⟩, ⟨5, 7, 9, 14⟩, ⟨5, 6, 9, 16⟩, ⟨5, 5, 9, 18⟩, ⟨5, 4, 9, 20⟩, ⟨5, 3, 9, 22⟩, ⟨5, 2, 9, 24⟩, ⟨5, 14, 8, 2⟩, ⟨5, 14, 7, 4⟩, ⟨5, 14, 6, 6⟩, ⟨5, 14, 5, 8⟩, ⟨5, 14, 4, 10⟩, ⟨5, 14, 3, 12⟩, ⟨5, 14, 2, 14⟩, ⟨5, 14, 1, 16⟩, ⟨5, 14, 0, 18⟩]
  exact AllWinning.cons node_14189 (AllWinning.cons node_13177 (AllWinning.cons node_12124 (AllWinning.cons node_11070 (AllWinning.cons node_9909 (AllWinning.cons node_14241 (AllWinning.cons node_13274 (AllWinning.cons node_12313 (AllWinning.cons node_11333 (AllWinning.cons node_10292 (AllWinning.cons node_9302 (AllWinning.cons node_8311 (AllWinning.cons node_7374 (AllWinning.cons node_6448 (AllWinning.cons node_5646 (AllWinning.cons node_4945 (AllWinning.cons node_4231 (AllWinning.cons node_14244 (AllWinning.cons node_13278 (AllWinning.cons node_12322 (AllWinning.cons node_11347 (AllWinning.cons node_10316 (AllWinning.cons node_9324 (AllWinning.cons node_8334 (AllWinning.cons node_7404 (AllWinning.cons node_6485 (AllWinning.nil))))))))))))))))))))))))))

theorem node_15194 : Outcome ⟨5, 15, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.nil))))))

theorem node_15195 : Outcome ⟨5, 15, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.nil))))))))))))

theorem node_15196 : Outcome ⟨5, 15, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨0, 15, 8, 10⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 10, 8, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩, ⟨5, 15, 3, 10⟩, ⟨5, 15, 2, 12⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_9912 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_10296 (AllWinning.cons node_9306 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.cons node_10321 (AllWinning.cons node_9328 (AllWinning.nil)))))))))))))))))

theorem node_15197 : Outcome ⟨5, 15, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨0, 15, 8, 10⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 10, 8, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 7, 8, 16⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩, ⟨5, 15, 3, 10⟩, ⟨5, 15, 2, 12⟩, ⟨5, 15, 1, 14⟩, ⟨5, 15, 0, 16⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_9912 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_10296 (AllWinning.cons node_9306 (AllWinning.cons node_8316 (AllWinning.cons node_7378 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.cons node_10321 (AllWinning.cons node_9328 (AllWinning.cons node_8338 (AllWinning.cons node_7407 (AllWinning.nil)))))))))))))))))))))

theorem node_15198 : Outcome ⟨5, 15, 8, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨0, 15, 8, 10⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 10, 8, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 7, 8, 16⟩, ⟨5, 6, 8, 18⟩, ⟨5, 5, 8, 20⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩, ⟨5, 15, 3, 10⟩, ⟨5, 15, 2, 12⟩, ⟨5, 15, 1, 14⟩, ⟨5, 15, 0, 16⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_9912 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_10296 (AllWinning.cons node_9306 (AllWinning.cons node_8316 (AllWinning.cons node_7378 (AllWinning.cons node_6451 (AllWinning.cons node_5652 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.cons node_10321 (AllWinning.cons node_9328 (AllWinning.cons node_8338 (AllWinning.cons node_7407 (AllWinning.nil)))))))))))))))))))))))

theorem node_15199 : Outcome ⟨5, 15, 8, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨0, 15, 8, 10⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 10, 8, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 7, 8, 16⟩, ⟨5, 6, 8, 18⟩, ⟨5, 5, 8, 20⟩, ⟨5, 4, 8, 22⟩, ⟨5, 3, 8, 24⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩, ⟨5, 15, 3, 10⟩, ⟨5, 15, 2, 12⟩, ⟨5, 15, 1, 14⟩, ⟨5, 15, 0, 16⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_9912 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_10296 (AllWinning.cons node_9306 (AllWinning.cons node_8316 (AllWinning.cons node_7378 (AllWinning.cons node_6451 (AllWinning.cons node_5652 (AllWinning.cons node_4948 (AllWinning.cons node_4235 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.cons node_10321 (AllWinning.cons node_9328 (AllWinning.cons node_8338 (AllWinning.cons node_7407 (AllWinning.nil)))))))))))))))))))))))))

theorem node_15200 : Outcome ⟨5, 15, 8, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨0, 15, 8, 10⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 10, 8, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 7, 8, 16⟩, ⟨5, 6, 8, 18⟩, ⟨5, 5, 8, 20⟩, ⟨5, 4, 8, 22⟩, ⟨5, 3, 8, 24⟩, ⟨5, 2, 8, 26⟩, ⟨5, 1, 8, 28⟩, ⟨5, 0, 8, 30⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩, ⟨5, 15, 3, 10⟩, ⟨5, 15, 2, 12⟩, ⟨5, 15, 1, 14⟩, ⟨5, 15, 0, 16⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_9912 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_10296 (AllWinning.cons node_9306 (AllWinning.cons node_8316 (AllWinning.cons node_7378 (AllWinning.cons node_6451 (AllWinning.cons node_5652 (AllWinning.cons node_4948 (AllWinning.cons node_4235 (AllWinning.cons node_3648 (AllWinning.cons node_3090 (AllWinning.cons node_2633 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.cons node_10321 (AllWinning.cons node_9328 (AllWinning.cons node_8338 (AllWinning.cons node_7407 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15201 : Outcome ⟨5, 15, 8, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨0, 15, 8, 10⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 10, 8, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 7, 8, 16⟩, ⟨5, 6, 8, 18⟩, ⟨5, 5, 8, 20⟩, ⟨5, 4, 8, 22⟩, ⟨5, 3, 8, 24⟩, ⟨5, 2, 8, 26⟩, ⟨5, 1, 8, 28⟩, ⟨5, 0, 8, 30⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩, ⟨5, 15, 3, 10⟩, ⟨5, 15, 2, 12⟩, ⟨5, 15, 1, 14⟩, ⟨5, 15, 0, 16⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_9912 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_10296 (AllWinning.cons node_9306 (AllWinning.cons node_8316 (AllWinning.cons node_7378 (AllWinning.cons node_6451 (AllWinning.cons node_5652 (AllWinning.cons node_4948 (AllWinning.cons node_4235 (AllWinning.cons node_3648 (AllWinning.cons node_3090 (AllWinning.cons node_2633 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.cons node_10321 (AllWinning.cons node_9328 (AllWinning.cons node_8338 (AllWinning.cons node_7407 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15202 : Outcome ⟨5, 15, 8, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 8, 2⟩, ⟨3, 15, 8, 4⟩, ⟨2, 15, 8, 6⟩, ⟨1, 15, 8, 8⟩, ⟨0, 15, 8, 10⟩, ⟨5, 14, 8, 2⟩, ⟨5, 13, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨5, 11, 8, 8⟩, ⟨5, 10, 8, 10⟩, ⟨5, 9, 8, 12⟩, ⟨5, 8, 8, 14⟩, ⟨5, 7, 8, 16⟩, ⟨5, 6, 8, 18⟩, ⟨5, 5, 8, 20⟩, ⟨5, 4, 8, 22⟩, ⟨5, 3, 8, 24⟩, ⟨5, 2, 8, 26⟩, ⟨5, 1, 8, 28⟩, ⟨5, 0, 8, 30⟩, ⟨5, 15, 7, 2⟩, ⟨5, 15, 6, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 15, 4, 8⟩, ⟨5, 15, 3, 10⟩, ⟨5, 15, 2, 12⟩, ⟨5, 15, 1, 14⟩, ⟨5, 15, 0, 16⟩]
  exact AllWinning.cons node_14192 (AllWinning.cons node_13181 (AllWinning.cons node_12126 (AllWinning.cons node_11073 (AllWinning.cons node_9912 (AllWinning.cons node_14244 (AllWinning.cons node_13277 (AllWinning.cons node_12317 (AllWinning.cons node_11337 (AllWinning.cons node_10296 (AllWinning.cons node_9306 (AllWinning.cons node_8316 (AllWinning.cons node_7378 (AllWinning.cons node_6451 (AllWinning.cons node_5652 (AllWinning.cons node_4948 (AllWinning.cons node_4235 (AllWinning.cons node_3648 (AllWinning.cons node_3090 (AllWinning.cons node_2633 (AllWinning.cons node_14245 (AllWinning.cons node_13281 (AllWinning.cons node_12324 (AllWinning.cons node_11350 (AllWinning.cons node_10321 (AllWinning.cons node_9328 (AllWinning.cons node_8338 (AllWinning.cons node_7407 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15203 : Outcome ⟨5, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 6, 2⟩) (by decide) node_14248

theorem node_15204 : Outcome ⟨5, 16, 7, 12⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 24⟩) (by decide) node_4247

theorem node_15205 : Outcome ⟨5, 17, 6, 2⟩ true :=
  Outcome.win (q := ⟨5, 17, 4, 4⟩) (by decide) node_13285

theorem node_15206 : Outcome ⟨5, 17, 6, 8⟩ true :=
  Outcome.win (q := ⟨5, 17, 4, 4⟩) (by decide) node_13285

theorem node_15207 : Outcome ⟨5, 18, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 5, 2⟩, ⟨3, 18, 5, 4⟩, ⟨5, 17, 5, 2⟩, ⟨5, 16, 5, 4⟩, ⟨5, 18, 4, 2⟩, ⟨5, 18, 3, 4⟩]
  exact AllWinning.cons node_14198 (AllWinning.cons node_13192 (AllWinning.cons node_14251 (AllWinning.cons node_13284 (AllWinning.cons node_14253 (AllWinning.cons node_13288 (AllWinning.nil))))))

theorem node_15208 : Outcome ⟨5, 18, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 5, 2⟩, ⟨3, 18, 5, 4⟩, ⟨2, 18, 5, 6⟩, ⟨1, 18, 5, 8⟩, ⟨5, 17, 5, 2⟩, ⟨5, 16, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨5, 14, 5, 8⟩, ⟨5, 18, 4, 2⟩, ⟨5, 18, 3, 4⟩, ⟨5, 18, 2, 6⟩, ⟨5, 18, 1, 8⟩]
  exact AllWinning.cons node_14198 (AllWinning.cons node_13192 (AllWinning.cons node_12139 (AllWinning.cons node_11083 (AllWinning.cons node_14251 (AllWinning.cons node_13284 (AllWinning.cons node_12324 (AllWinning.cons node_11347 (AllWinning.cons node_14253 (AllWinning.cons node_13288 (AllWinning.cons node_12333 (AllWinning.cons node_11359 (AllWinning.nil))))))))))))

theorem node_15209 : Outcome ⟨5, 18, 5, 14⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 10⟩) (by decide) node_9925

theorem node_15210 : Outcome ⟨5, 19, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 17, 4, 4⟩) (by decide) node_13285

theorem node_15211 : Outcome ⟨5, 19, 4, 12⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 24⟩) (by decide) node_4264

theorem node_15212 : Outcome ⟨5, 19, 4, 18⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 24⟩) (by decide) node_4264

theorem node_15213 : Outcome ⟨5, 20, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 19, 3, 2⟩) (by decide) node_14257

theorem node_15214 : Outcome ⟨6, 2, 20, 6⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 6⟩) (by decide) node_12152

theorem node_15215 : Outcome ⟨6, 2, 20, 8⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 6⟩) (by decide) node_12152

theorem node_15216 : Outcome ⟨6, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 3, 19, 2⟩) (by decide) node_14207

theorem node_15217 : Outcome ⟨6, 3, 19, 8⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 10⟩) (by decide) node_9938

theorem node_15218 : Outcome ⟨6, 3, 19, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 10⟩) (by decide) node_9938

theorem node_15219 : Outcome ⟨6, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 18, 4⟩) (by decide) node_13203

theorem node_15220 : Outcome ⟨6, 4, 18, 10⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 16⟩) (by decide) node_7433

theorem node_15221 : Outcome ⟨6, 4, 18, 12⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 16⟩) (by decide) node_7433

theorem node_15222 : Outcome ⟨6, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 17, 4⟩) (by decide) node_13206

theorem node_15223 : Outcome ⟨6, 5, 17, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 17, 4⟩) (by decide) node_13206

theorem node_15224 : Outcome ⟨6, 6, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 6, 16, 2⟩) (by decide) node_14217

theorem node_15225 : Outcome ⟨6, 6, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 10⟩) (by decide) node_9955

theorem node_15226 : Outcome ⟨6, 6, 16, 12⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 10⟩) (by decide) node_9955

theorem node_15227 : Outcome ⟨6, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 13, 4⟩) (by decide) node_13317

theorem node_15228 : Outcome ⟨6, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 6⟩) (by decide) node_12170

theorem node_15229 : Outcome ⟨6, 7, 15, 8⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 14⟩) (by decide) node_8373

theorem node_15230 : Outcome ⟨6, 7, 15, 12⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 14⟩) (by decide) node_8373

theorem node_15231 : Outcome ⟨6, 8, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 8, 14, 2⟩, ⟨4, 8, 14, 4⟩, ⟨6, 7, 14, 2⟩, ⟨6, 6, 14, 4⟩, ⟨6, 8, 13, 2⟩, ⟨6, 8, 12, 4⟩]
  exact AllWinning.cons node_14223 (AllWinning.cons node_13212 (AllWinning.cons node_14278 (AllWinning.cons node_13312 (AllWinning.cons node_14283 (AllWinning.cons node_13321 (AllWinning.nil))))))

theorem node_15232 : Outcome ⟨6, 8, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 8, 14, 2⟩, ⟨4, 8, 14, 4⟩, ⟨3, 8, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨6, 7, 14, 2⟩, ⟨6, 6, 14, 4⟩, ⟨6, 5, 14, 6⟩, ⟨6, 4, 14, 8⟩, ⟨6, 8, 13, 2⟩, ⟨6, 8, 12, 4⟩, ⟨6, 8, 11, 6⟩, ⟨6, 8, 10, 8⟩]
  exact AllWinning.cons node_14223 (AllWinning.cons node_13212 (AllWinning.cons node_12177 (AllWinning.cons node_11110 (AllWinning.cons node_14278 (AllWinning.cons node_13312 (AllWinning.cons node_12363 (AllWinning.cons node_11376 (AllWinning.cons node_14283 (AllWinning.cons node_13321 (AllWinning.cons node_12374 (AllWinning.cons node_11392 (AllWinning.nil))))))))))))

theorem node_15233 : Outcome ⟨6, 8, 14, 10⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 14⟩) (by decide) node_8385

theorem node_15234 : Outcome ⟨6, 9, 13, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 13, 4⟩) (by decide) node_13317

theorem node_15235 : Outcome ⟨6, 9, 13, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 13, 4⟩) (by decide) node_13317

theorem node_15236 : Outcome ⟨6, 9, 13, 8⟩ true :=
  Outcome.win (q := ⟨6, 7, 13, 4⟩) (by decide) node_13317

theorem node_15237 : Outcome ⟨6, 9, 13, 10⟩ true :=
  Outcome.win (q := ⟨6, 7, 13, 4⟩) (by decide) node_13317

theorem node_15238 : Outcome ⟨6, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 2⟩) (by decide) node_14227

theorem node_15239 : Outcome ⟨6, 10, 12, 12⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 16⟩) (by decide) node_7462

theorem node_15240 : Outcome ⟨6, 11, 11, 2⟩ true :=
  Outcome.win (q := ⟨5, 11, 11, 2⟩) (by decide) node_14233

theorem node_15241 : Outcome ⟨6, 11, 11, 6⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 12⟩) (by decide) node_8943

theorem node_15242 : Outcome ⟨6, 11, 11, 8⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 12⟩) (by decide) node_8943

theorem node_15243 : Outcome ⟨6, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 2⟩) (by decide) node_14236

theorem node_15244 : Outcome ⟨6, 12, 10, 12⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 16⟩) (by decide) node_7433

theorem node_15245 : Outcome ⟨6, 13, 9, 2⟩ true :=
  Outcome.win (q := ⟨6, 13, 7, 4⟩) (by decide) node_13337

theorem node_15246 : Outcome ⟨6, 13, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 13, 7, 4⟩) (by decide) node_13337

theorem node_15247 : Outcome ⟨6, 13, 9, 8⟩ true :=
  Outcome.win (q := ⟨6, 13, 7, 4⟩) (by decide) node_13337

theorem node_15248 : Outcome ⟨6, 13, 9, 10⟩ true :=
  Outcome.win (q := ⟨6, 13, 7, 4⟩) (by decide) node_13337

theorem node_15249 : Outcome ⟨6, 14, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 8, 2⟩, ⟨4, 14, 8, 4⟩, ⟨6, 13, 8, 2⟩, ⟨6, 12, 8, 4⟩, ⟨6, 14, 7, 2⟩, ⟨6, 14, 6, 4⟩]
  exact AllWinning.cons node_14244 (AllWinning.cons node_13228 (AllWinning.cons node_14298 (AllWinning.cons node_13333 (AllWinning.cons node_14301 (AllWinning.cons node_13341 (AllWinning.nil))))))

end RQ9F1
