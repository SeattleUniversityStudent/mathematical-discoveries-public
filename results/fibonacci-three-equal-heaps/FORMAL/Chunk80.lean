import Chunk79
set_option autoImplicit false
namespace RQ9F1

theorem node_17127 : Outcome ⟨4, 6, 20, 4⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 2⟩) (by decide) node_16071

theorem node_17128 : Outcome ⟨4, 6, 20, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 2⟩) (by decide) node_16071

theorem node_17129 : Outcome ⟨4, 7, 19, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 19, 2⟩) (by decide) node_16024

theorem node_17130 : Outcome ⟨4, 7, 19, 14⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 28⟩) (by decide) node_4199

theorem node_17131 : Outcome ⟨4, 8, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 2⟩) (by decide) node_16082

theorem node_17132 : Outcome ⟨4, 8, 18, 6⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 2⟩) (by decide) node_16082

theorem node_17133 : Outcome ⟨4, 8, 18, 8⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 2⟩) (by decide) node_16082

theorem node_17134 : Outcome ⟨4, 9, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 17, 2⟩) (by decide) node_16030

theorem node_17135 : Outcome ⟨4, 9, 17, 12⟩ true :=
  Outcome.win (q := ⟨3, 9, 17, 2⟩) (by decide) node_16030

theorem node_17136 : Outcome ⟨4, 10, 16, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 4⟩) (by decide) node_15019

theorem node_17137 : Outcome ⟨4, 10, 16, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 4⟩) (by decide) node_15019

theorem node_17138 : Outcome ⟨4, 10, 16, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 4⟩) (by decide) node_15019

theorem node_17139 : Outcome ⟨4, 11, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 15, 2⟩, ⟨2, 11, 15, 4⟩, ⟨4, 10, 15, 2⟩, ⟨4, 9, 15, 4⟩, ⟨4, 11, 14, 2⟩, ⟨4, 11, 13, 4⟩]
  exact AllWinning.cons node_16036 (AllWinning.cons node_15024 (AllWinning.cons node_16097 (AllWinning.cons node_15123 (AllWinning.cons node_16098 (AllWinning.cons node_15129 (AllWinning.nil))))))

theorem node_17140 : Outcome ⟨4, 11, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 6⟩) (by decide) node_14016

theorem node_17141 : Outcome ⟨4, 11, 15, 6⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 6⟩) (by decide) node_14016

theorem node_17142 : Outcome ⟨4, 11, 15, 12⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 6⟩) (by decide) node_14016

theorem node_17143 : Outcome ⟨4, 12, 14, 2⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 4⟩) (by decide) node_15027

theorem node_17144 : Outcome ⟨4, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 4⟩) (by decide) node_15027

theorem node_17145 : Outcome ⟨4, 12, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 4⟩) (by decide) node_15027

theorem node_17146 : Outcome ⟨4, 12, 14, 14⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 4⟩) (by decide) node_15027

theorem node_17147 : Outcome ⟨4, 13, 13, 2⟩ true :=
  Outcome.win (q := ⟨3, 13, 13, 2⟩) (by decide) node_16044

theorem node_17148 : Outcome ⟨4, 13, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 8⟩) (by decide) node_13004

theorem node_17149 : Outcome ⟨4, 13, 13, 8⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 8⟩) (by decide) node_13004

theorem node_17150 : Outcome ⟨4, 13, 13, 18⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 8⟩) (by decide) node_13004

theorem node_17151 : Outcome ⟨4, 14, 12, 2⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 4⟩) (by decide) node_15040

theorem node_17152 : Outcome ⟨4, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 4⟩) (by decide) node_15040

theorem node_17153 : Outcome ⟨4, 14, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 4⟩) (by decide) node_15040

theorem node_17154 : Outcome ⟨4, 14, 12, 14⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 4⟩) (by decide) node_15040

theorem node_17155 : Outcome ⟨4, 15, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 15, 11, 2⟩, ⟨2, 15, 11, 4⟩, ⟨4, 14, 11, 2⟩, ⟨4, 13, 11, 4⟩, ⟨4, 15, 10, 2⟩, ⟨4, 15, 9, 4⟩]
  exact AllWinning.cons node_16053 (AllWinning.cons node_15047 (AllWinning.cons node_16121 (AllWinning.cons node_15134 (AllWinning.cons node_16124 (AllWinning.cons node_15140 (AllWinning.nil))))))

theorem node_17156 : Outcome ⟨4, 15, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 6⟩) (by decide) node_14032

theorem node_17157 : Outcome ⟨4, 15, 11, 6⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 6⟩) (by decide) node_14032

theorem node_17158 : Outcome ⟨4, 15, 11, 12⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 6⟩) (by decide) node_14032

theorem node_17159 : Outcome ⟨4, 16, 10, 2⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 4⟩) (by decide) node_15049

theorem node_17160 : Outcome ⟨4, 16, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 4⟩) (by decide) node_15049

theorem node_17161 : Outcome ⟨4, 16, 10, 8⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 4⟩) (by decide) node_15049

theorem node_17162 : Outcome ⟨4, 17, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 17, 9, 2⟩) (by decide) node_16059

theorem node_17163 : Outcome ⟨4, 17, 9, 12⟩ true :=
  Outcome.win (q := ⟨3, 17, 9, 2⟩) (by decide) node_16059

theorem node_17164 : Outcome ⟨4, 18, 8, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 2⟩) (by decide) node_16133

theorem node_17165 : Outcome ⟨4, 18, 8, 6⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 2⟩) (by decide) node_16133

theorem node_17166 : Outcome ⟨4, 18, 8, 8⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 2⟩) (by decide) node_16133

theorem node_17167 : Outcome ⟨4, 19, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 19, 7, 2⟩) (by decide) node_16066

theorem node_17168 : Outcome ⟨4, 19, 7, 14⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 28⟩) (by decide) node_4182

theorem node_17169 : Outcome ⟨4, 20, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 19, 6, 2⟩) (by decide) node_16142

theorem node_17170 : Outcome ⟨4, 20, 6, 8⟩ true :=
  Outcome.win (q := ⟨4, 19, 6, 2⟩) (by decide) node_16142

theorem node_17171 : Outcome ⟨5, 5, 20, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 18, 4⟩) (by decide) node_15156

theorem node_17172 : Outcome ⟨5, 5, 20, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 18, 4⟩) (by decide) node_15156

theorem node_17173 : Outcome ⟨5, 6, 19, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 19, 2⟩) (by decide) node_16077

theorem node_17174 : Outcome ⟨5, 6, 19, 8⟩ true :=
  Outcome.win (q := ⟨0, 6, 19, 10⟩) (by decide) node_11965

theorem node_17175 : Outcome ⟨5, 7, 18, 2⟩ true :=
  Outcome.win (q := ⟨5, 5, 18, 4⟩) (by decide) node_15156

theorem node_17176 : Outcome ⟨5, 7, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 6⟩) (by decide) node_14058

theorem node_17177 : Outcome ⟨5, 7, 18, 10⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 6⟩) (by decide) node_14058

theorem node_17178 : Outcome ⟨5, 7, 18, 16⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 28⟩) (by decide) node_4265

theorem node_17179 : Outcome ⟨5, 8, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 4⟩) (by decide) node_15163

theorem node_17180 : Outcome ⟨5, 8, 17, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 4⟩) (by decide) node_15163

theorem node_17181 : Outcome ⟨5, 9, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 4⟩) (by decide) node_15173

theorem node_17182 : Outcome ⟨5, 9, 16, 8⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 4⟩) (by decide) node_15173

theorem node_17183 : Outcome ⟨5, 10, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 4⟩) (by decide) node_15163

theorem node_17184 : Outcome ⟨5, 10, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 6⟩) (by decide) node_14229

theorem node_17185 : Outcome ⟨5, 11, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 14, 4⟩) (by decide) node_15082

theorem node_17186 : Outcome ⟨5, 11, 14, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 14, 4⟩) (by decide) node_15082

theorem node_17187 : Outcome ⟨5, 12, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 2⟩) (by decide) node_16101

theorem node_17188 : Outcome ⟨5, 12, 13, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 6⟩) (by decide) node_14237

theorem node_17189 : Outcome ⟨5, 12, 13, 10⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 6⟩) (by decide) node_14237

theorem node_17190 : Outcome ⟨5, 13, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 2⟩) (by decide) node_16111

theorem node_17191 : Outcome ⟨5, 13, 12, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 6⟩) (by decide) node_14229

theorem node_17192 : Outcome ⟨5, 13, 12, 10⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 6⟩) (by decide) node_14229

theorem node_17193 : Outcome ⟨5, 14, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 14, 11, 4⟩) (by decide) node_15094

theorem node_17194 : Outcome ⟨5, 14, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 14, 11, 4⟩) (by decide) node_15094

theorem node_17195 : Outcome ⟨5, 15, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 4⟩) (by decide) node_15195

theorem node_17196 : Outcome ⟨5, 15, 10, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 6⟩) (by decide) node_14237

theorem node_17197 : Outcome ⟨5, 16, 9, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 4⟩) (by decide) node_15190

theorem node_17198 : Outcome ⟨5, 16, 9, 8⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 4⟩) (by decide) node_15190

theorem node_17199 : Outcome ⟨5, 17, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 4⟩) (by decide) node_15195

theorem node_17200 : Outcome ⟨5, 17, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 4⟩) (by decide) node_15195

theorem node_17201 : Outcome ⟨5, 18, 7, 2⟩ true :=
  Outcome.win (q := ⟨5, 18, 5, 4⟩) (by decide) node_15208

theorem node_17202 : Outcome ⟨5, 18, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 6⟩) (by decide) node_14088

theorem node_17203 : Outcome ⟨5, 18, 7, 10⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 6⟩) (by decide) node_14088

theorem node_17204 : Outcome ⟨5, 18, 7, 16⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 28⟩) (by decide) node_4248

theorem node_17205 : Outcome ⟨5, 19, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 19, 6, 2⟩) (by decide) node_16142

theorem node_17206 : Outcome ⟨5, 19, 6, 8⟩ true :=
  Outcome.win (q := ⟨0, 19, 6, 10⟩) (by decide) node_12007

theorem node_17207 : Outcome ⟨5, 20, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 5, 4⟩) (by decide) node_15208

theorem node_17208 : Outcome ⟨5, 20, 5, 8⟩ true :=
  Outcome.win (q := ⟨5, 18, 5, 4⟩) (by decide) node_15208

theorem node_17209 : Outcome ⟨6, 4, 20, 4⟩ true :=
  Outcome.win (q := ⟨5, 4, 20, 2⟩) (by decide) node_16150

theorem node_17210 : Outcome ⟨6, 4, 20, 8⟩ true :=
  Outcome.win (q := ⟨5, 4, 20, 2⟩) (by decide) node_16150

theorem node_17211 : Outcome ⟨6, 5, 19, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 19, 2⟩) (by decide) node_16201

theorem node_17212 : Outcome ⟨6, 5, 19, 8⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 10⟩) (by decide) node_12346

theorem node_17213 : Outcome ⟨6, 6, 18, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 17, 2⟩) (by decide) node_16207

theorem node_17214 : Outcome ⟨6, 6, 18, 8⟩ true :=
  Outcome.win (q := ⟨6, 6, 17, 2⟩) (by decide) node_16207

theorem node_17215 : Outcome ⟨6, 7, 17, 4⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 2⟩) (by decide) node_16160

theorem node_17216 : Outcome ⟨6, 7, 17, 8⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 2⟩) (by decide) node_16160

theorem node_17217 : Outcome ⟨6, 8, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 6⟩) (by decide) node_14111

theorem node_17218 : Outcome ⟨6, 9, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 15, 2⟩, ⟨4, 9, 15, 4⟩, ⟨6, 8, 15, 2⟩, ⟨6, 7, 15, 4⟩, ⟨6, 9, 14, 2⟩, ⟨6, 9, 13, 4⟩]
  exact AllWinning.cons node_16167 (AllWinning.cons node_15123 (AllWinning.cons node_16213 (AllWinning.cons node_15228 (AllWinning.cons node_16217 (AllWinning.cons node_15235 (AllWinning.nil))))))

theorem node_17219 : Outcome ⟨6, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 8⟩) (by decide) node_13093

theorem node_17220 : Outcome ⟨6, 9, 15, 6⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 8⟩) (by decide) node_13093

theorem node_17221 : Outcome ⟨6, 10, 14, 2⟩ true :=
  Outcome.win (q := ⟨6, 8, 14, 4⟩) (by decide) node_15232

theorem node_17222 : Outcome ⟨6, 10, 14, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 10⟩) (by decide) node_12036

theorem node_17223 : Outcome ⟨6, 10, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 10⟩) (by decide) node_12036

theorem node_17224 : Outcome ⟨6, 10, 14, 20⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 20⟩) (by decide) node_7464

theorem node_17225 : Outcome ⟨6, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 13, 2⟩) (by decide) node_16222

theorem node_17226 : Outcome ⟨6, 11, 13, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 13, 2⟩) (by decide) node_16222

theorem node_17227 : Outcome ⟨6, 12, 12, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 12, 2⟩) (by decide) node_16225

theorem node_17228 : Outcome ⟨6, 12, 12, 8⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 12⟩) (by decide) node_11004

theorem node_17229 : Outcome ⟨6, 12, 12, 10⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 12⟩) (by decide) node_11004

theorem node_17230 : Outcome ⟨6, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 11, 2⟩) (by decide) node_16230

theorem node_17231 : Outcome ⟨6, 13, 11, 6⟩ true :=
  Outcome.win (q := ⟨6, 12, 11, 2⟩) (by decide) node_16230

theorem node_17232 : Outcome ⟨6, 14, 10, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 8, 4⟩) (by decide) node_15250

theorem node_17233 : Outcome ⟨6, 14, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 10⟩) (by decide) node_12056

theorem node_17234 : Outcome ⟨6, 14, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 10⟩) (by decide) node_12056

theorem node_17235 : Outcome ⟨6, 14, 10, 20⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 20⟩) (by decide) node_7435

theorem node_17236 : Outcome ⟨6, 15, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 9, 2⟩, ⟨4, 15, 9, 4⟩, ⟨6, 14, 9, 2⟩, ⟨6, 13, 9, 4⟩, ⟨6, 15, 8, 2⟩, ⟨6, 15, 7, 4⟩]
  exact AllWinning.cons node_16179 (AllWinning.cons node_15140 (AllWinning.cons node_16238 (AllWinning.cons node_15246 (AllWinning.cons node_16243 (AllWinning.cons node_15253 (AllWinning.nil))))))

theorem node_17237 : Outcome ⟨6, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 8⟩) (by decide) node_13112

theorem node_17238 : Outcome ⟨6, 15, 9, 6⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 8⟩) (by decide) node_13112

theorem node_17239 : Outcome ⟨6, 16, 8, 8⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 6⟩) (by decide) node_14144

theorem node_17240 : Outcome ⟨6, 17, 7, 4⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 2⟩) (by decide) node_16182

theorem node_17241 : Outcome ⟨6, 17, 7, 8⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 2⟩) (by decide) node_16182

theorem node_17242 : Outcome ⟨6, 18, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 6, 2⟩) (by decide) node_16250

theorem node_17243 : Outcome ⟨6, 18, 6, 8⟩ true :=
  Outcome.win (q := ⟨6, 17, 6, 2⟩) (by decide) node_16250

theorem node_17244 : Outcome ⟨6, 19, 5, 4⟩ true :=
  Outcome.win (q := ⟨6, 19, 4, 2⟩) (by decide) node_16256

theorem node_17245 : Outcome ⟨6, 19, 5, 8⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 10⟩) (by decide) node_12417

theorem node_17246 : Outcome ⟨6, 20, 4, 4⟩ true :=
  Outcome.win (q := ⟨5, 20, 4, 2⟩) (by decide) node_16192

theorem node_17247 : Outcome ⟨6, 20, 4, 8⟩ true :=
  Outcome.win (q := ⟨5, 20, 4, 2⟩) (by decide) node_16192

theorem node_17248 : Outcome ⟨7, 3, 20, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 19, 2⟩) (by decide) node_16264

theorem node_17249 : Outcome ⟨7, 3, 20, 4⟩ true :=
  Outcome.win (q := ⟨7, 0, 20, 6⟩) (by decide) node_14323

theorem node_17250 : Outcome ⟨7, 3, 20, 10⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 10⟩) (by decide) node_12086

theorem node_17251 : Outcome ⟨7, 4, 19, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 19, 2⟩) (by decide) node_16201

theorem node_17252 : Outcome ⟨7, 4, 19, 14⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 28⟩) (by decide) node_4355

theorem node_17253 : Outcome ⟨7, 5, 18, 2⟩ true :=
  Outcome.win (q := ⟨5, 5, 18, 4⟩) (by decide) node_15156

theorem node_17254 : Outcome ⟨7, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 6⟩) (by decide) node_14331

theorem node_17255 : Outcome ⟨7, 5, 18, 10⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 6⟩) (by decide) node_14331

theorem node_17256 : Outcome ⟨7, 5, 18, 16⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 28⟩) (by decide) node_4370

theorem node_17257 : Outcome ⟨7, 6, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 17, 2⟩) (by decide) node_16207

theorem node_17258 : Outcome ⟨7, 6, 17, 8⟩ true :=
  Outcome.win (q := ⟨6, 6, 17, 2⟩) (by decide) node_16207

theorem node_17259 : Outcome ⟨7, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 8⟩) (by decide) node_13384

theorem node_17260 : Outcome ⟨7, 7, 16, 8⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 8⟩) (by decide) node_13384

theorem node_17261 : Outcome ⟨7, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 4⟩) (by decide) node_15163

theorem node_17262 : Outcome ⟨7, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 4⟩) (by decide) node_15163

theorem node_17263 : Outcome ⟨7, 8, 15, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 10⟩) (by decide) node_12434

theorem node_17264 : Outcome ⟨7, 8, 15, 10⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 18⟩) (by decide) node_8467

theorem node_17265 : Outcome ⟨7, 8, 15, 14⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 18⟩) (by decide) node_8467

theorem node_17266 : Outcome ⟨7, 9, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 4⟩) (by decide) node_15173

theorem node_17267 : Outcome ⟨7, 9, 14, 14⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 4⟩) (by decide) node_15173

theorem node_17268 : Outcome ⟨7, 10, 13, 2⟩ true :=
  Outcome.win (q := ⟨6, 10, 13, 2⟩) (by decide) node_16222

theorem node_17269 : Outcome ⟨7, 10, 13, 6⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 8⟩) (by decide) node_13153

theorem node_17270 : Outcome ⟨7, 10, 13, 8⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 8⟩) (by decide) node_13153

theorem node_17271 : Outcome ⟨7, 10, 13, 16⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 8⟩) (by decide) node_13153

theorem node_17272 : Outcome ⟨7, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 12, 2⟩) (by decide) node_16225

theorem node_17273 : Outcome ⟨7, 11, 12, 8⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 8⟩) (by decide) node_13384

theorem node_17274 : Outcome ⟨7, 11, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 8⟩) (by decide) node_13384

theorem node_17275 : Outcome ⟨7, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨6, 12, 11, 2⟩) (by decide) node_16230

theorem node_17276 : Outcome ⟨7, 12, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 8⟩) (by decide) node_13404

theorem node_17277 : Outcome ⟨7, 12, 11, 10⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 8⟩) (by decide) node_13404

theorem node_17278 : Outcome ⟨7, 13, 10, 2⟩ true :=
  Outcome.win (q := ⟨6, 13, 10, 2⟩) (by decide) node_16235

theorem node_17279 : Outcome ⟨7, 13, 10, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 8⟩) (by decide) node_13171

theorem node_17280 : Outcome ⟨7, 13, 10, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 8⟩) (by decide) node_13171

theorem node_17281 : Outcome ⟨7, 13, 10, 16⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 8⟩) (by decide) node_13171

theorem node_17282 : Outcome ⟨7, 14, 9, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 4⟩) (by decide) node_15190

theorem node_17283 : Outcome ⟨7, 14, 9, 14⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 4⟩) (by decide) node_15190

theorem node_17284 : Outcome ⟨7, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 4⟩) (by decide) node_15195

theorem node_17285 : Outcome ⟨7, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 4⟩) (by decide) node_15195

theorem node_17286 : Outcome ⟨7, 15, 8, 8⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 10⟩) (by decide) node_12473

theorem node_17287 : Outcome ⟨7, 15, 8, 10⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 18⟩) (by decide) node_8451

theorem node_17288 : Outcome ⟨7, 15, 8, 14⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 18⟩) (by decide) node_8451

theorem node_17289 : Outcome ⟨7, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 8⟩) (by decide) node_13404

theorem node_17290 : Outcome ⟨7, 16, 7, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 8⟩) (by decide) node_13404

theorem node_17291 : Outcome ⟨7, 17, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 6, 2⟩) (by decide) node_16250

theorem node_17292 : Outcome ⟨7, 17, 6, 8⟩ true :=
  Outcome.win (q := ⟨6, 17, 6, 2⟩) (by decide) node_16250

theorem node_17293 : Outcome ⟨7, 18, 5, 2⟩ true :=
  Outcome.win (q := ⟨5, 18, 5, 4⟩) (by decide) node_15208

theorem node_17294 : Outcome ⟨7, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 6⟩) (by decide) node_14385

theorem node_17295 : Outcome ⟨7, 18, 5, 10⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 6⟩) (by decide) node_14385

theorem node_17296 : Outcome ⟨7, 18, 5, 16⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 28⟩) (by decide) node_4355

theorem node_17297 : Outcome ⟨7, 19, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 19, 4, 2⟩) (by decide) node_16256

theorem node_17298 : Outcome ⟨7, 19, 4, 14⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 28⟩) (by decide) node_4370

theorem node_17299 : Outcome ⟨7, 20, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 19, 3, 2⟩) (by decide) node_16323

theorem node_17300 : Outcome ⟨7, 20, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 20, 0, 6⟩) (by decide) node_14395

theorem node_17301 : Outcome ⟨7, 20, 3, 10⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 10⟩) (by decide) node_12149

theorem node_17302 : Outcome ⟨8, 2, 20, 2⟩ true :=
  Outcome.win (q := ⟨8, 2, 19, 2⟩) (by decide) node_16330

theorem node_17303 : Outcome ⟨8, 2, 20, 10⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 10⟩) (by decide) node_12154

theorem node_17304 : Outcome ⟨8, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 19, 2⟩) (by decide) node_16264

theorem node_17305 : Outcome ⟨8, 3, 19, 6⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 6⟩) (by decide) node_14409

theorem node_17306 : Outcome ⟨8, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 2⟩) (by decide) node_16340

theorem node_17307 : Outcome ⟨8, 4, 18, 6⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 2⟩) (by decide) node_16340

theorem node_17308 : Outcome ⟨8, 4, 18, 8⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 2⟩) (by decide) node_16340

theorem node_17309 : Outcome ⟨8, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 4⟩) (by decide) node_15332

theorem node_17310 : Outcome ⟨8, 5, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 4⟩) (by decide) node_15332

theorem node_17311 : Outcome ⟨8, 5, 17, 12⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 4⟩) (by decide) node_15332

theorem node_17312 : Outcome ⟨8, 6, 16, 8⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 6⟩) (by decide) node_14409

theorem node_17313 : Outcome ⟨8, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 4⟩) (by decide) node_15332

theorem node_17314 : Outcome ⟨8, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 4⟩) (by decide) node_15332

theorem node_17315 : Outcome ⟨8, 7, 15, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 10⟩) (by decide) node_12172

theorem node_17316 : Outcome ⟨8, 7, 15, 10⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 18⟩) (by decide) node_8549

theorem node_17317 : Outcome ⟨8, 7, 15, 14⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 18⟩) (by decide) node_8549

theorem node_17318 : Outcome ⟨8, 8, 14, 2⟩ true :=
  Outcome.win (q := ⟨6, 8, 14, 4⟩) (by decide) node_15232

theorem node_17319 : Outcome ⟨8, 8, 14, 8⟩ true :=
  Outcome.win (q := ⟨6, 8, 14, 4⟩) (by decide) node_15232

theorem node_17320 : Outcome ⟨8, 8, 14, 14⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 28⟩) (by decide) node_4443

theorem node_17321 : Outcome ⟨8, 9, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 2⟩) (by decide) node_16282

theorem node_17322 : Outcome ⟨8, 9, 13, 4⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 2⟩) (by decide) node_16282

theorem node_17323 : Outcome ⟨8, 9, 13, 8⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 2⟩) (by decide) node_16282

theorem node_17324 : Outcome ⟨8, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 8, 12, 4⟩) (by decide) node_15348

theorem node_17325 : Outcome ⟨8, 10, 12, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 6⟩) (by decide) node_14229

theorem node_17326 : Outcome ⟨8, 11, 11, 2⟩ true :=
  Outcome.win (q := ⟨8, 10, 11, 2⟩) (by decide) node_16359

theorem node_17327 : Outcome ⟨8, 11, 11, 4⟩ true :=
  Outcome.win (q := ⟨8, 10, 11, 2⟩) (by decide) node_16359

theorem node_17328 : Outcome ⟨8, 11, 11, 12⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 16⟩) (by decide) node_8945

theorem node_17329 : Outcome ⟨8, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 8, 4⟩) (by decide) node_15359

theorem node_17330 : Outcome ⟨8, 12, 10, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 6⟩) (by decide) node_14237

theorem node_17331 : Outcome ⟨8, 13, 9, 2⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 2⟩) (by decide) node_16298

theorem node_17332 : Outcome ⟨8, 13, 9, 4⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 2⟩) (by decide) node_16298

theorem node_17333 : Outcome ⟨8, 13, 9, 8⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 2⟩) (by decide) node_16298

theorem node_17334 : Outcome ⟨8, 14, 8, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 8, 4⟩) (by decide) node_15250

theorem node_17335 : Outcome ⟨8, 14, 8, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 8, 4⟩) (by decide) node_15250

theorem node_17336 : Outcome ⟨8, 14, 8, 14⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 28⟩) (by decide) node_4402

theorem node_17337 : Outcome ⟨8, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 4⟩) (by decide) node_15369

theorem node_17338 : Outcome ⟨8, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 4⟩) (by decide) node_15369

theorem node_17339 : Outcome ⟨8, 15, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 10⟩) (by decide) node_12199

theorem node_17340 : Outcome ⟨8, 15, 7, 10⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 18⟩) (by decide) node_8537

theorem node_17341 : Outcome ⟨8, 15, 7, 14⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 18⟩) (by decide) node_8537

theorem node_17342 : Outcome ⟨8, 16, 6, 8⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 6⟩) (by decide) node_14445

theorem node_17343 : Outcome ⟨8, 17, 5, 2⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 4⟩) (by decide) node_15369

theorem node_17344 : Outcome ⟨8, 17, 5, 4⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 4⟩) (by decide) node_15369

theorem node_17345 : Outcome ⟨8, 17, 5, 12⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 4⟩) (by decide) node_15369

theorem node_17346 : Outcome ⟨8, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 2⟩) (by decide) node_16382

theorem node_17347 : Outcome ⟨8, 18, 4, 6⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 2⟩) (by decide) node_16382

theorem node_17348 : Outcome ⟨8, 18, 4, 8⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 2⟩) (by decide) node_16382

theorem node_17349 : Outcome ⟨8, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 19, 3, 2⟩) (by decide) node_16323

theorem node_17350 : Outcome ⟨8, 19, 3, 6⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 6⟩) (by decide) node_14445

theorem node_17351 : Outcome ⟨8, 20, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 19, 2, 2⟩) (by decide) node_16392

theorem node_17352 : Outcome ⟨8, 20, 2, 10⟩ true :=
  Outcome.win (q := ⟨3, 20, 2, 10⟩) (by decide) node_12219

theorem node_17353 : Outcome ⟨9, 1, 20, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 19, 2⟩) (by decide) node_16403

theorem node_17354 : Outcome ⟨9, 1, 20, 8⟩ true :=
  Outcome.win (q := ⟨9, 1, 19, 2⟩) (by decide) node_16403

theorem node_17355 : Outcome ⟨9, 1, 20, 16⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 30⟩) (by decide) node_3806

theorem node_17356 : Outcome ⟨9, 2, 19, 2⟩ true :=
  Outcome.win (q := ⟨8, 2, 19, 2⟩) (by decide) node_16330

theorem node_17357 : Outcome ⟨9, 2, 19, 4⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 8⟩) (by decide) node_13498

theorem node_17358 : Outcome ⟨9, 2, 19, 8⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 8⟩) (by decide) node_13498

theorem node_17359 : Outcome ⟨9, 3, 18, 2⟩ true :=
  Outcome.win (q := ⟨9, 3, 17, 2⟩) (by decide) node_16408

theorem node_17360 : Outcome ⟨9, 3, 18, 12⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 12⟩) (by decide) node_11566

theorem node_17361 : Outcome ⟨9, 4, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 2⟩) (by decide) node_16340

theorem node_17362 : Outcome ⟨9, 4, 17, 12⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 2⟩) (by decide) node_16340

theorem node_17363 : Outcome ⟨9, 5, 16, 2⟩ true :=
  Outcome.win (q := ⟨9, 5, 14, 4⟩) (by decide) node_15401

theorem node_17364 : Outcome ⟨9, 5, 16, 8⟩ true :=
  Outcome.win (q := ⟨9, 5, 14, 4⟩) (by decide) node_15401

theorem node_17365 : Outcome ⟨9, 6, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 6, 15, 2⟩, ⟨7, 6, 15, 4⟩, ⟨9, 5, 15, 2⟩, ⟨9, 4, 15, 4⟩, ⟨9, 6, 14, 2⟩, ⟨9, 6, 13, 4⟩]
  exact AllWinning.cons node_16349 (AllWinning.cons node_15281 (AllWinning.cons node_16420 (AllWinning.cons node_15399 (AllWinning.cons node_16422 (AllWinning.cons node_15407 (AllWinning.nil))))))

theorem node_17366 : Outcome ⟨9, 6, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 8⟩) (by decide) node_13498

theorem node_17367 : Outcome ⟨9, 6, 15, 6⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 8⟩) (by decide) node_13498

theorem node_17368 : Outcome ⟨9, 7, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 5, 14, 4⟩) (by decide) node_15401

theorem node_17369 : Outcome ⟨9, 7, 14, 14⟩ true :=
  Outcome.win (q := ⟨9, 5, 14, 4⟩) (by decide) node_15401

theorem node_17370 : Outcome ⟨9, 8, 13, 2⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 2⟩) (by decide) node_16427

theorem node_17371 : Outcome ⟨9, 8, 13, 4⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 2⟩) (by decide) node_16427

theorem node_17372 : Outcome ⟨9, 8, 13, 8⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 2⟩) (by decide) node_16427

theorem node_17373 : Outcome ⟨9, 9, 12, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 11, 2⟩) (by decide) node_16438

theorem node_17374 : Outcome ⟨9, 9, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 12⟩) (by decide) node_11177

theorem node_17375 : Outcome ⟨9, 9, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 12⟩) (by decide) node_11177

theorem node_17376 : Outcome ⟨9, 9, 12, 16⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 24⟩) (by decide) node_5880

theorem node_17377 : Outcome ⟨9, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨8, 10, 11, 2⟩) (by decide) node_16359

theorem node_17378 : Outcome ⟨9, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨8, 11, 10, 2⟩) (by decide) node_16365

theorem node_17379 : Outcome ⟨9, 12, 9, 2⟩ true :=
  Outcome.win (q := ⟨9, 11, 9, 2⟩) (by decide) node_16445

theorem node_17380 : Outcome ⟨9, 12, 9, 6⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 12⟩) (by decide) node_11198

theorem node_17381 : Outcome ⟨9, 12, 9, 8⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 12⟩) (by decide) node_11198

theorem node_17382 : Outcome ⟨9, 12, 9, 16⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 24⟩) (by decide) node_5830

theorem node_17383 : Outcome ⟨9, 13, 8, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 2⟩) (by decide) node_16450

theorem node_17384 : Outcome ⟨9, 13, 8, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 2⟩) (by decide) node_16450

theorem node_17385 : Outcome ⟨9, 13, 8, 8⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 2⟩) (by decide) node_16450

theorem node_17386 : Outcome ⟨9, 14, 7, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 4⟩) (by decide) node_15430

theorem node_17387 : Outcome ⟨9, 14, 7, 14⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 4⟩) (by decide) node_15430

theorem node_17388 : Outcome ⟨9, 15, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 15, 6, 2⟩, ⟨7, 15, 6, 4⟩, ⟨9, 14, 6, 2⟩, ⟨9, 13, 6, 4⟩, ⟨9, 15, 5, 2⟩, ⟨9, 15, 4, 4⟩]
  exact AllWinning.cons node_16377 (AllWinning.cons node_15307 (AllWinning.cons node_16459 (AllWinning.cons node_15427 (AllWinning.cons node_16464 (AllWinning.cons node_15436 (AllWinning.nil))))))

theorem node_17389 : Outcome ⟨9, 15, 6, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 8⟩) (by decide) node_13535

theorem node_17390 : Outcome ⟨9, 15, 6, 6⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 8⟩) (by decide) node_13535

theorem node_17391 : Outcome ⟨9, 16, 5, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 4⟩) (by decide) node_15430

theorem node_17392 : Outcome ⟨9, 16, 5, 8⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 4⟩) (by decide) node_15430

theorem node_17393 : Outcome ⟨9, 17, 4, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 2⟩) (by decide) node_16382

theorem node_17394 : Outcome ⟨9, 17, 4, 12⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 2⟩) (by decide) node_16382

theorem node_17395 : Outcome ⟨9, 18, 3, 2⟩ true :=
  Outcome.win (q := ⟨9, 17, 3, 2⟩) (by decide) node_16473

theorem node_17396 : Outcome ⟨9, 18, 3, 12⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 12⟩) (by decide) node_11599

theorem node_17397 : Outcome ⟨9, 19, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 19, 2, 2⟩) (by decide) node_16392

theorem node_17398 : Outcome ⟨9, 19, 2, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 8⟩) (by decide) node_13535

theorem node_17399 : Outcome ⟨9, 19, 2, 8⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 8⟩) (by decide) node_13535

theorem node_17400 : Outcome ⟨9, 20, 1, 2⟩ true :=
  Outcome.win (q := ⟨9, 19, 1, 2⟩) (by decide) node_16479

theorem node_17401 : Outcome ⟨9, 20, 1, 8⟩ true :=
  Outcome.win (q := ⟨9, 19, 1, 2⟩) (by decide) node_16479

theorem node_17402 : Outcome ⟨9, 20, 1, 16⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 30⟩) (by decide) node_3834

theorem node_17403 : Outcome ⟨10, 0, 20, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 18, 4⟩) (by decide) node_15449

theorem node_17404 : Outcome ⟨10, 0, 20, 4⟩ true :=
  Outcome.win (q := ⟨7, 0, 20, 6⟩) (by decide) node_14323

theorem node_17405 : Outcome ⟨10, 0, 20, 8⟩ true :=
  Outcome.win (q := ⟨7, 0, 20, 6⟩) (by decide) node_14323

theorem node_17406 : Outcome ⟨10, 1, 19, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 19, 2⟩) (by decide) node_16403

theorem node_17407 : Outcome ⟨10, 1, 19, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 19, 2⟩) (by decide) node_16403

theorem node_17408 : Outcome ⟨10, 1, 19, 8⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 10⟩) (by decide) node_12600

theorem node_17409 : Outcome ⟨10, 1, 19, 16⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 10⟩) (by decide) node_12600

theorem node_17410 : Outcome ⟨10, 2, 18, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 18, 4⟩) (by decide) node_15449

theorem node_17411 : Outcome ⟨10, 2, 18, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 6⟩) (by decide) node_14331

theorem node_17412 : Outcome ⟨10, 2, 18, 12⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 6⟩) (by decide) node_14331

theorem node_17413 : Outcome ⟨10, 3, 17, 2⟩ true :=
  Outcome.win (q := ⟨9, 3, 17, 2⟩) (by decide) node_16408

theorem node_17414 : Outcome ⟨10, 3, 17, 8⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17415 : Outcome ⟨10, 3, 17, 14⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17416 : Outcome ⟨10, 4, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 4⟩) (by decide) node_15455

theorem node_17417 : Outcome ⟨10, 4, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 4⟩) (by decide) node_15455

theorem node_17418 : Outcome ⟨10, 4, 16, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 4⟩) (by decide) node_15455

theorem node_17419 : Outcome ⟨10, 4, 16, 20⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 20⟩) (by decide) node_7660

theorem node_17420 : Outcome ⟨10, 5, 15, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 4⟩) (by decide) node_15332

theorem node_17421 : Outcome ⟨10, 5, 15, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 6⟩) (by decide) node_14530

theorem node_17422 : Outcome ⟨10, 6, 14, 2⟩ true :=
  Outcome.win (q := ⟨8, 6, 14, 4⟩) (by decide) node_15342

theorem node_17423 : Outcome ⟨10, 6, 14, 6⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 10⟩) (by decide) node_12600

theorem node_17424 : Outcome ⟨10, 6, 14, 8⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 10⟩) (by decide) node_12600

theorem node_17425 : Outcome ⟨10, 6, 14, 20⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 20⟩) (by decide) node_7674

theorem node_17426 : Outcome ⟨10, 7, 13, 2⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 2⟩) (by decide) node_16427

theorem node_17427 : Outcome ⟨10, 7, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17428 : Outcome ⟨10, 7, 13, 8⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17429 : Outcome ⟨10, 7, 13, 16⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 8⟩) (by decide) node_13556

theorem node_17430 : Outcome ⟨10, 8, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 8, 12, 4⟩) (by decide) node_15348

theorem node_17431 : Outcome ⟨10, 8, 12, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 12, 6⟩) (by decide) node_14530

theorem node_17432 : Outcome ⟨10, 9, 11, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 11, 2⟩) (by decide) node_16438

theorem node_17433 : Outcome ⟨10, 10, 10, 6⟩ true :=
  Outcome.win (q := ⟨7, 10, 10, 6⟩) (by decide) node_14359

theorem node_17434 : Outcome ⟨10, 10, 10, 14⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 20⟩) (by decide) node_6989

theorem node_17435 : Outcome ⟨10, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨9, 11, 9, 2⟩) (by decide) node_16445

theorem node_17436 : Outcome ⟨10, 12, 8, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 8, 4⟩) (by decide) node_15359

theorem node_17437 : Outcome ⟨10, 12, 8, 8⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 6⟩) (by decide) node_14554

theorem node_17438 : Outcome ⟨10, 13, 7, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 2⟩) (by decide) node_16450

theorem node_17439 : Outcome ⟨10, 13, 7, 6⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17440 : Outcome ⟨10, 13, 7, 8⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17441 : Outcome ⟨10, 13, 7, 16⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17442 : Outcome ⟨10, 14, 6, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 6, 4⟩) (by decide) node_15366

theorem node_17443 : Outcome ⟨10, 14, 6, 6⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 10⟩) (by decide) node_12643

theorem node_17444 : Outcome ⟨10, 14, 6, 8⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 10⟩) (by decide) node_12643

theorem node_17445 : Outcome ⟨10, 14, 6, 20⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 20⟩) (by decide) node_7660

theorem node_17446 : Outcome ⟨10, 15, 5, 2⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 4⟩) (by decide) node_15369

theorem node_17447 : Outcome ⟨10, 15, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 12, 5, 6⟩) (by decide) node_14554

theorem node_17448 : Outcome ⟨10, 16, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 4⟩) (by decide) node_15498

theorem node_17449 : Outcome ⟨10, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 4⟩) (by decide) node_15498

theorem node_17450 : Outcome ⟨10, 16, 4, 8⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 4⟩) (by decide) node_15498

theorem node_17451 : Outcome ⟨10, 16, 4, 20⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 20⟩) (by decide) node_7674

theorem node_17452 : Outcome ⟨10, 17, 3, 2⟩ true :=
  Outcome.win (q := ⟨9, 17, 3, 2⟩) (by decide) node_16473

theorem node_17453 : Outcome ⟨10, 17, 3, 8⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17454 : Outcome ⟨10, 17, 3, 14⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 8⟩) (by decide) node_13589

theorem node_17455 : Outcome ⟨10, 18, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 4⟩) (by decide) node_15498

theorem node_17456 : Outcome ⟨10, 18, 2, 4⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 6⟩) (by decide) node_14385

theorem node_17457 : Outcome ⟨10, 18, 2, 8⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 6⟩) (by decide) node_14385

theorem node_17458 : Outcome ⟨10, 18, 2, 12⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 6⟩) (by decide) node_14385

theorem node_17459 : Outcome ⟨10, 19, 1, 2⟩ true :=
  Outcome.win (q := ⟨9, 19, 1, 2⟩) (by decide) node_16479

theorem node_17460 : Outcome ⟨10, 19, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 19, 1, 2⟩) (by decide) node_16479

theorem node_17461 : Outcome ⟨10, 19, 1, 8⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 10⟩) (by decide) node_12643

theorem node_17462 : Outcome ⟨10, 20, 0, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 0, 4⟩) (by decide) node_15505

theorem node_17463 : Outcome ⟨10, 20, 0, 4⟩ true :=
  Outcome.win (q := ⟨7, 20, 0, 6⟩) (by decide) node_14395

theorem node_17464 : Outcome ⟨10, 20, 0, 8⟩ true :=
  Outcome.win (q := ⟨7, 20, 0, 6⟩) (by decide) node_14395

theorem node_17465 : Outcome ⟨11, 0, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 19, 2⟩, ⟨9, 0, 19, 4⟩, ⟨11, 0, 18, 2⟩, ⟨11, 0, 17, 4⟩]
  exact AllWinning.cons node_16485 (AllWinning.cons node_15389 (AllWinning.cons node_16543 (AllWinning.cons node_15509 (AllWinning.nil))))

theorem node_17466 : Outcome ⟨11, 0, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 19, 2⟩, ⟨9, 0, 19, 4⟩, ⟨8, 0, 19, 6⟩, ⟨7, 0, 19, 8⟩, ⟨11, 0, 18, 2⟩, ⟨11, 0, 17, 4⟩, ⟨11, 0, 16, 6⟩, ⟨11, 0, 15, 8⟩]
  exact AllWinning.cons node_16485 (AllWinning.cons node_15389 (AllWinning.cons node_14400 (AllWinning.cons node_13363 (AllWinning.cons node_16543 (AllWinning.cons node_15509 (AllWinning.cons node_14575 (AllWinning.cons node_13601 (AllWinning.nil))))))))

theorem node_17467 : Outcome ⟨11, 0, 19, 6⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 10⟩) (by decide) node_12346

theorem node_17468 : Outcome ⟨11, 0, 19, 16⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 16⟩) (by decide) node_9616

theorem node_17469 : Outcome ⟨11, 1, 18, 6⟩ true :=
  Outcome.win (q := ⟨11, 1, 15, 6⟩) (by decide) node_14580

theorem node_17470 : Outcome ⟨11, 2, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 17, 2⟩, ⟨9, 2, 17, 4⟩, ⟨8, 2, 17, 6⟩, ⟨7, 2, 17, 8⟩, ⟨11, 1, 17, 2⟩, ⟨11, 0, 17, 4⟩, ⟨11, 2, 16, 2⟩, ⟨11, 2, 15, 4⟩, ⟨11, 2, 14, 6⟩, ⟨11, 2, 13, 8⟩]
  exact AllWinning.cons node_16492 (AllWinning.cons node_15393 (AllWinning.cons node_14406 (AllWinning.cons node_13369 (AllWinning.cons node_16546 (AllWinning.cons node_15509 (AllWinning.cons node_16548 (AllWinning.cons node_15514 (AllWinning.cons node_14583 (AllWinning.cons node_13608 (AllWinning.nil))))))))))

theorem node_17471 : Outcome ⟨11, 2, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 17, 2⟩, ⟨9, 2, 17, 4⟩, ⟨8, 2, 17, 6⟩, ⟨7, 2, 17, 8⟩, ⟨6, 2, 17, 10⟩, ⟨5, 2, 17, 12⟩, ⟨11, 1, 17, 2⟩, ⟨11, 0, 17, 4⟩, ⟨11, 2, 16, 2⟩, ⟨11, 2, 15, 4⟩, ⟨11, 2, 14, 6⟩, ⟨11, 2, 13, 8⟩, ⟨11, 2, 12, 10⟩, ⟨11, 2, 11, 12⟩]
  exact AllWinning.cons node_16492 (AllWinning.cons node_15393 (AllWinning.cons node_14406 (AllWinning.cons node_13369 (AllWinning.cons node_12354 (AllWinning.cons node_11307 (AllWinning.cons node_16546 (AllWinning.cons node_15509 (AllWinning.cons node_16548 (AllWinning.cons node_15514 (AllWinning.cons node_14583 (AllWinning.cons node_13608 (AllWinning.cons node_12660 (AllWinning.cons node_11664 (AllWinning.nil))))))))))))))

theorem node_17472 : Outcome ⟨11, 2, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 17, 2⟩, ⟨9, 2, 17, 4⟩, ⟨8, 2, 17, 6⟩, ⟨7, 2, 17, 8⟩, ⟨6, 2, 17, 10⟩, ⟨5, 2, 17, 12⟩, ⟨4, 2, 17, 14⟩, ⟨3, 2, 17, 16⟩, ⟨11, 1, 17, 2⟩, ⟨11, 0, 17, 4⟩, ⟨11, 2, 16, 2⟩, ⟨11, 2, 15, 4⟩, ⟨11, 2, 14, 6⟩, ⟨11, 2, 13, 8⟩, ⟨11, 2, 12, 10⟩, ⟨11, 2, 11, 12⟩, ⟨11, 2, 10, 14⟩, ⟨11, 2, 9, 16⟩]
  exact AllWinning.cons node_16492 (AllWinning.cons node_15393 (AllWinning.cons node_14406 (AllWinning.cons node_13369 (AllWinning.cons node_12354 (AllWinning.cons node_11307 (AllWinning.cons node_10179 (AllWinning.cons node_9133 (AllWinning.cons node_16546 (AllWinning.cons node_15509 (AllWinning.cons node_16548 (AllWinning.cons node_15514 (AllWinning.cons node_14583 (AllWinning.cons node_13608 (AllWinning.cons node_12660 (AllWinning.cons node_11664 (AllWinning.cons node_10670 (AllWinning.cons node_9625 (AllWinning.nil))))))))))))))))))

theorem node_17473 : Outcome ⟨11, 2, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 17, 2⟩, ⟨9, 2, 17, 4⟩, ⟨8, 2, 17, 6⟩, ⟨7, 2, 17, 8⟩, ⟨6, 2, 17, 10⟩, ⟨5, 2, 17, 12⟩, ⟨4, 2, 17, 14⟩, ⟨3, 2, 17, 16⟩, ⟨2, 2, 17, 18⟩, ⟨1, 2, 17, 20⟩, ⟨11, 1, 17, 2⟩, ⟨11, 0, 17, 4⟩, ⟨11, 2, 16, 2⟩, ⟨11, 2, 15, 4⟩, ⟨11, 2, 14, 6⟩, ⟨11, 2, 13, 8⟩, ⟨11, 2, 12, 10⟩, ⟨11, 2, 11, 12⟩, ⟨11, 2, 10, 14⟩, ⟨11, 2, 9, 16⟩, ⟨11, 2, 8, 18⟩, ⟨11, 2, 7, 20⟩]
  exact AllWinning.cons node_16492 (AllWinning.cons node_15393 (AllWinning.cons node_14406 (AllWinning.cons node_13369 (AllWinning.cons node_12354 (AllWinning.cons node_11307 (AllWinning.cons node_10179 (AllWinning.cons node_9133 (AllWinning.cons node_8074 (AllWinning.cons node_7038 (AllWinning.cons node_16546 (AllWinning.cons node_15509 (AllWinning.cons node_16548 (AllWinning.cons node_15514 (AllWinning.cons node_14583 (AllWinning.cons node_13608 (AllWinning.cons node_12660 (AllWinning.cons node_11664 (AllWinning.cons node_10670 (AllWinning.cons node_9625 (AllWinning.cons node_8679 (AllWinning.cons node_7708 (AllWinning.nil))))))))))))))))))))))

theorem node_17474 : Outcome ⟨11, 3, 16, 4⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 6⟩) (by decide) node_14409

theorem node_17475 : Outcome ⟨11, 3, 16, 6⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 6⟩) (by decide) node_14409

theorem node_17476 : Outcome ⟨11, 3, 16, 8⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 6⟩) (by decide) node_14409

theorem node_17477 : Outcome ⟨11, 4, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 4, 15, 2⟩, ⟨9, 4, 15, 4⟩, ⟨11, 3, 15, 2⟩, ⟨11, 2, 15, 4⟩, ⟨11, 4, 14, 2⟩, ⟨11, 4, 13, 4⟩]
  exact AllWinning.cons node_16496 (AllWinning.cons node_15399 (AllWinning.cons node_16550 (AllWinning.cons node_15514 (AllWinning.cons node_16554 (AllWinning.cons node_15521 (AllWinning.nil))))))

theorem node_17478 : Outcome ⟨11, 4, 15, 4⟩ true :=
  Outcome.win (q := ⟨11, 1, 15, 6⟩) (by decide) node_14580

theorem node_17479 : Outcome ⟨11, 4, 15, 6⟩ true :=
  Outcome.win (q := ⟨11, 1, 15, 6⟩) (by decide) node_14580

theorem node_17480 : Outcome ⟨11, 5, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 5, 14, 4⟩) (by decide) node_15401

theorem node_17481 : Outcome ⟨11, 5, 14, 6⟩ true :=
  Outcome.win (q := ⟨9, 5, 14, 4⟩) (by decide) node_15401

theorem node_17482 : Outcome ⟨11, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 13, 2⟩) (by decide) node_16500

theorem node_17483 : Outcome ⟨11, 6, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 6, 13, 2⟩) (by decide) node_16500

theorem node_17484 : Outcome ⟨11, 7, 12, 2⟩ true :=
  Outcome.win (q := ⟨11, 6, 12, 2⟩) (by decide) node_16558

theorem node_17485 : Outcome ⟨11, 7, 12, 8⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 8⟩) (by decide) node_13384

theorem node_17486 : Outcome ⟨11, 7, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 8⟩) (by decide) node_13384

theorem node_17487 : Outcome ⟨11, 8, 11, 2⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 2⟩) (by decide) node_16505

theorem node_17488 : Outcome ⟨11, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 2⟩) (by decide) node_16505

theorem node_17489 : Outcome ⟨11, 8, 11, 12⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 16⟩) (by decide) node_9616

theorem node_17490 : Outcome ⟨11, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 2⟩) (by decide) node_16565

theorem node_17491 : Outcome ⟨11, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 9, 2⟩) (by decide) node_16571

theorem node_17492 : Outcome ⟨11, 11, 8, 2⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 2⟩) (by decide) node_16517

theorem node_17493 : Outcome ⟨11, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 2⟩) (by decide) node_16517

theorem node_17494 : Outcome ⟨11, 12, 7, 2⟩ true :=
  Outcome.win (q := ⟨11, 12, 6, 2⟩) (by decide) node_16581

theorem node_17495 : Outcome ⟨11, 12, 7, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 8⟩) (by decide) node_13404

theorem node_17496 : Outcome ⟨11, 12, 7, 10⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 8⟩) (by decide) node_13404

theorem node_17497 : Outcome ⟨11, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 13, 6, 2⟩) (by decide) node_16525

theorem node_17498 : Outcome ⟨11, 13, 6, 6⟩ true :=
  Outcome.win (q := ⟨10, 13, 6, 2⟩) (by decide) node_16525

theorem node_17499 : Outcome ⟨11, 14, 5, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 4⟩) (by decide) node_15430

theorem node_17500 : Outcome ⟨11, 14, 5, 6⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 4⟩) (by decide) node_15430

theorem node_17501 : Outcome ⟨11, 15, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 4, 2⟩, ⟨9, 15, 4, 4⟩, ⟨11, 14, 4, 2⟩, ⟨11, 13, 4, 4⟩, ⟨11, 15, 3, 2⟩, ⟨11, 15, 2, 4⟩]
  exact AllWinning.cons node_16531 (AllWinning.cons node_15436 (AllWinning.cons node_16587 (AllWinning.cons node_15544 (AllWinning.cons node_16590 (AllWinning.cons node_15550 (AllWinning.nil))))))

theorem node_17502 : Outcome ⟨11, 15, 4, 4⟩ true :=
  Outcome.win (q := ⟨11, 15, 1, 6⟩) (by decide) node_14617

theorem node_17503 : Outcome ⟨11, 15, 4, 6⟩ true :=
  Outcome.win (q := ⟨11, 15, 1, 6⟩) (by decide) node_14617

theorem node_17504 : Outcome ⟨11, 16, 3, 4⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 6⟩) (by decide) node_14445

theorem node_17505 : Outcome ⟨11, 16, 3, 6⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 6⟩) (by decide) node_14445

theorem node_17506 : Outcome ⟨11, 16, 3, 8⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 6⟩) (by decide) node_14445

theorem node_17507 : Outcome ⟨11, 17, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 2, 2⟩, ⟨9, 17, 2, 4⟩, ⟨11, 16, 2, 2⟩, ⟨11, 15, 2, 4⟩, ⟨11, 17, 1, 2⟩, ⟨11, 17, 0, 4⟩]
  exact AllWinning.cons node_16534 (AllWinning.cons node_15441 (AllWinning.cons node_16594 (AllWinning.cons node_15550 (AllWinning.cons node_16596 (AllWinning.cons node_15556 (AllWinning.nil))))))

theorem node_17508 : Outcome ⟨11, 17, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 2, 2⟩, ⟨9, 17, 2, 4⟩, ⟨8, 17, 2, 6⟩, ⟨7, 17, 2, 8⟩, ⟨11, 16, 2, 2⟩, ⟨11, 15, 2, 4⟩, ⟨11, 14, 2, 6⟩, ⟨11, 13, 2, 8⟩, ⟨11, 17, 1, 2⟩, ⟨11, 17, 0, 4⟩]
  exact AllWinning.cons node_16534 (AllWinning.cons node_15441 (AllWinning.cons node_14452 (AllWinning.cons node_13420 (AllWinning.cons node_16594 (AllWinning.cons node_15550 (AllWinning.cons node_14614 (AllWinning.cons node_13648 (AllWinning.cons node_16596 (AllWinning.cons node_15556 (AllWinning.nil))))))))))

theorem node_17509 : Outcome ⟨11, 17, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 2, 2⟩, ⟨9, 17, 2, 4⟩, ⟨8, 17, 2, 6⟩, ⟨7, 17, 2, 8⟩, ⟨6, 17, 2, 10⟩, ⟨5, 17, 2, 12⟩, ⟨11, 16, 2, 2⟩, ⟨11, 15, 2, 4⟩, ⟨11, 14, 2, 6⟩, ⟨11, 13, 2, 8⟩, ⟨11, 12, 2, 10⟩, ⟨11, 11, 2, 12⟩, ⟨11, 17, 1, 2⟩, ⟨11, 17, 0, 4⟩]
  exact AllWinning.cons node_16534 (AllWinning.cons node_15441 (AllWinning.cons node_14452 (AllWinning.cons node_13420 (AllWinning.cons node_12409 (AllWinning.cons node_11357 (AllWinning.cons node_16594 (AllWinning.cons node_15550 (AllWinning.cons node_14614 (AllWinning.cons node_13648 (AllWinning.cons node_12696 (AllWinning.cons node_11703 (AllWinning.cons node_16596 (AllWinning.cons node_15556 (AllWinning.nil))))))))))))))

theorem node_17510 : Outcome ⟨11, 17, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 2, 2⟩, ⟨9, 17, 2, 4⟩, ⟨8, 17, 2, 6⟩, ⟨7, 17, 2, 8⟩, ⟨6, 17, 2, 10⟩, ⟨5, 17, 2, 12⟩, ⟨4, 17, 2, 14⟩, ⟨3, 17, 2, 16⟩, ⟨11, 16, 2, 2⟩, ⟨11, 15, 2, 4⟩, ⟨11, 14, 2, 6⟩, ⟨11, 13, 2, 8⟩, ⟨11, 12, 2, 10⟩, ⟨11, 11, 2, 12⟩, ⟨11, 10, 2, 14⟩, ⟨11, 9, 2, 16⟩, ⟨11, 17, 1, 2⟩, ⟨11, 17, 0, 4⟩]
  exact AllWinning.cons node_16534 (AllWinning.cons node_15441 (AllWinning.cons node_14452 (AllWinning.cons node_13420 (AllWinning.cons node_12409 (AllWinning.cons node_11357 (AllWinning.cons node_10238 (AllWinning.cons node_9188 (AllWinning.cons node_16594 (AllWinning.cons node_15550 (AllWinning.cons node_14614 (AllWinning.cons node_13648 (AllWinning.cons node_12696 (AllWinning.cons node_11703 (AllWinning.cons node_10704 (AllWinning.cons node_9656 (AllWinning.cons node_16596 (AllWinning.cons node_15556 (AllWinning.nil))))))))))))))))))

end RQ9F1
