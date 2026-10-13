import Chunk56
set_option autoImplicit false
namespace RQ9F1

theorem node_13219 : Outcome ⟨4, 10, 12, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 12⟩) (by decide) node_7318

theorem node_13220 : Outcome ⟨4, 11, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 11, 2⟩) (by decide) node_12183

theorem node_13221 : Outcome ⟨4, 11, 11, 10⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 8⟩) (by decide) node_8941

theorem node_13222 : Outcome ⟨4, 11, 11, 14⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 8⟩) (by decide) node_8941

theorem node_13223 : Outcome ⟨4, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 2⟩) (by decide) node_12250

theorem node_13224 : Outcome ⟨4, 12, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 2⟩) (by decide) node_12250

theorem node_13225 : Outcome ⟨4, 12, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 12⟩) (by decide) node_7298

theorem node_13226 : Outcome ⟨4, 13, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨4, 12, 9, 2⟩, ⟨4, 11, 9, 4⟩, ⟨4, 13, 8, 2⟩, ⟨4, 13, 7, 4⟩]
  exact AllWinning.cons node_12190 (AllWinning.cons node_11125 (AllWinning.cons node_12254 (AllWinning.cons node_11264 (AllWinning.cons node_12256 (AllWinning.cons node_11272 (AllWinning.nil))))))

theorem node_13227 : Outcome ⟨4, 13, 9, 6⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 10⟩) (by decide) node_8271

theorem node_13228 : Outcome ⟨4, 14, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 2⟩) (by decide) node_12258

theorem node_13229 : Outcome ⟨4, 14, 8, 6⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 12⟩) (by decide) node_7338

theorem node_13230 : Outcome ⟨4, 14, 8, 22⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 12⟩) (by decide) node_7338

theorem node_13231 : Outcome ⟨4, 15, 7, 16⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 20⟩) (by decide) node_4179

theorem node_13232 : Outcome ⟨4, 16, 6, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 6, 2⟩) (by decide) node_12261

theorem node_13233 : Outcome ⟨4, 16, 6, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 12⟩) (by decide) node_7318

theorem node_13234 : Outcome ⟨4, 16, 6, 16⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 12⟩) (by decide) node_7318

theorem node_13235 : Outcome ⟨4, 17, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 5, 2⟩, ⟨2, 17, 5, 4⟩, ⟨4, 16, 5, 2⟩, ⟨4, 15, 5, 4⟩, ⟨4, 17, 4, 2⟩, ⟨4, 17, 3, 4⟩]
  exact AllWinning.cons node_12206 (AllWinning.cons node_11138 (AllWinning.cons node_12264 (AllWinning.cons node_11278 (AllWinning.cons node_12267 (AllWinning.cons node_11285 (AllWinning.nil))))))

theorem node_13236 : Outcome ⟨4, 17, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 5, 2⟩, ⟨2, 17, 5, 4⟩, ⟨1, 17, 5, 6⟩, ⟨0, 17, 5, 8⟩, ⟨4, 16, 5, 2⟩, ⟨4, 15, 5, 4⟩, ⟨4, 14, 5, 6⟩, ⟨4, 13, 5, 8⟩, ⟨4, 17, 4, 2⟩, ⟨4, 17, 3, 4⟩, ⟨4, 17, 2, 6⟩, ⟨4, 17, 1, 8⟩]
  exact AllWinning.cons node_12206 (AllWinning.cons node_11138 (AllWinning.cons node_10006 (AllWinning.cons node_8968 (AllWinning.cons node_12264 (AllWinning.cons node_11278 (AllWinning.cons node_10225 (AllWinning.cons node_9250 (AllWinning.cons node_12267 (AllWinning.cons node_11285 (AllWinning.cons node_10236 (AllWinning.cons node_9265 (AllWinning.nil))))))))))))

theorem node_13237 : Outcome ⟨4, 17, 5, 6⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 10⟩) (by decide) node_8285

theorem node_13238 : Outcome ⟨4, 18, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 4, 2⟩, ⟨2, 18, 4, 4⟩, ⟨4, 17, 4, 2⟩, ⟨4, 16, 4, 4⟩, ⟨4, 18, 3, 2⟩, ⟨4, 18, 2, 4⟩]
  exact AllWinning.cons node_12210 (AllWinning.cons node_11142 (AllWinning.cons node_12267 (AllWinning.cons node_11282 (AllWinning.cons node_12269 (AllWinning.cons node_11289 (AllWinning.nil))))))

theorem node_13239 : Outcome ⟨4, 18, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 4, 2⟩, ⟨2, 18, 4, 4⟩, ⟨1, 18, 4, 6⟩, ⟨0, 18, 4, 8⟩, ⟨4, 17, 4, 2⟩, ⟨4, 16, 4, 4⟩, ⟨4, 15, 4, 6⟩, ⟨4, 14, 4, 8⟩, ⟨4, 18, 3, 2⟩, ⟨4, 18, 2, 4⟩, ⟨4, 18, 1, 6⟩, ⟨4, 18, 0, 8⟩]
  exact AllWinning.cons node_12210 (AllWinning.cons node_11142 (AllWinning.cons node_10011 (AllWinning.cons node_8971 (AllWinning.cons node_12267 (AllWinning.cons node_11282 (AllWinning.cons node_10230 (AllWinning.cons node_9254 (AllWinning.cons node_12269 (AllWinning.cons node_11289 (AllWinning.cons node_10241 (AllWinning.cons node_9269 (AllWinning.nil))))))))))))

theorem node_13240 : Outcome ⟨4, 18, 4, 14⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 10⟩) (by decide) node_8271

theorem node_13241 : Outcome ⟨4, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨4, 19, 2, 2⟩) (by decide) node_12273

theorem node_13242 : Outcome ⟨4, 19, 3, 14⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 6⟩) (by decide) node_10016

theorem node_13243 : Outcome ⟨4, 19, 3, 22⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 6⟩) (by decide) node_10016

theorem node_13244 : Outcome ⟨4, 20, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 12⟩) (by decide) node_7338

theorem node_13245 : Outcome ⟨5, 1, 20, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 20, 2⟩) (by decide) node_12221

theorem node_13246 : Outcome ⟨5, 2, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 19, 2⟩) (by decide) node_12223

theorem node_13247 : Outcome ⟨5, 2, 19, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 19, 2⟩) (by decide) node_12223

theorem node_13248 : Outcome ⟨5, 2, 19, 16⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 18⟩) (by decide) node_4938

theorem node_13249 : Outcome ⟨5, 3, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 18, 4⟩) (by decide) node_11155

theorem node_13250 : Outcome ⟨5, 3, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 6⟩) (by decide) node_10248

theorem node_13251 : Outcome ⟨5, 3, 18, 18⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 14⟩) (by decide) node_6438

theorem node_13252 : Outcome ⟨5, 3, 18, 20⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 14⟩) (by decide) node_6438

theorem node_13253 : Outcome ⟨5, 4, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 4, 17, 2⟩, ⟨3, 4, 17, 4⟩, ⟨2, 4, 17, 6⟩, ⟨1, 4, 17, 8⟩, ⟨5, 3, 17, 2⟩, ⟨5, 2, 17, 4⟩, ⟨5, 1, 17, 6⟩, ⟨5, 0, 17, 8⟩, ⟨5, 4, 16, 2⟩, ⟨5, 4, 15, 4⟩, ⟨5, 4, 14, 6⟩, ⟨5, 4, 13, 8⟩]
  exact AllWinning.cons node_12231 (AllWinning.cons node_11158 (AllWinning.cons node_10032 (AllWinning.cons node_8991 (AllWinning.cons node_12289 (AllWinning.cons node_11305 (AllWinning.cons node_10255 (AllWinning.cons node_9272 (AllWinning.cons node_12293 (AllWinning.cons node_11311 (AllWinning.cons node_10264 (AllWinning.cons node_9285 (AllWinning.nil))))))))))))

theorem node_13254 : Outcome ⟨5, 4, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 10⟩) (by decide) node_7920

theorem node_13255 : Outcome ⟨5, 5, 16, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 16, 4⟩) (by decide) node_11162

theorem node_13256 : Outcome ⟨5, 5, 16, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 6⟩) (by decide) node_10270

theorem node_13257 : Outcome ⟨5, 6, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 6, 15, 2⟩) (by decide) node_12236

theorem node_13258 : Outcome ⟨5, 6, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 15, 2⟩) (by decide) node_12236

theorem node_13259 : Outcome ⟨5, 6, 15, 12⟩ true :=
  Outcome.win (q := ⟨4, 6, 15, 2⟩) (by decide) node_12236

theorem node_13260 : Outcome ⟨5, 7, 14, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 2⟩) (by decide) node_12239

theorem node_13261 : Outcome ⟨5, 7, 14, 6⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 2⟩) (by decide) node_12239

theorem node_13262 : Outcome ⟨5, 8, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨5, 7, 13, 2⟩, ⟨5, 6, 13, 4⟩, ⟨5, 8, 12, 2⟩, ⟨5, 8, 11, 4⟩]
  exact AllWinning.cons node_12242 (AllWinning.cons node_11170 (AllWinning.cons node_12300 (AllWinning.cons node_11315 (AllWinning.cons node_12302 (AllWinning.cons node_11323 (AllWinning.nil))))))

theorem node_13263 : Outcome ⟨5, 8, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 6⟩) (by decide) node_10270

theorem node_13264 : Outcome ⟨5, 9, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 4⟩) (by decide) node_11173

theorem node_13265 : Outcome ⟨5, 9, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 4⟩) (by decide) node_11173

theorem node_13266 : Outcome ⟨5, 9, 12, 18⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 22⟩) (by decide) node_3682

theorem node_13267 : Outcome ⟨5, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 2⟩) (by decide) node_12246

theorem node_13268 : Outcome ⟨5, 10, 11, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 2⟩) (by decide) node_12246

theorem node_13269 : Outcome ⟨5, 10, 11, 16⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 18⟩) (by decide) node_4976

theorem node_13270 : Outcome ⟨5, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 2⟩) (by decide) node_12250

theorem node_13271 : Outcome ⟨5, 11, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 2⟩) (by decide) node_12250

theorem node_13272 : Outcome ⟨5, 11, 10, 16⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 18⟩) (by decide) node_4938

theorem node_13273 : Outcome ⟨5, 12, 9, 2⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 4⟩) (by decide) node_11194

theorem node_13274 : Outcome ⟨5, 12, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 4⟩) (by decide) node_11194

theorem node_13275 : Outcome ⟨5, 12, 9, 18⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 22⟩) (by decide) node_3644

theorem node_13276 : Outcome ⟨5, 13, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 8, 2⟩, ⟨3, 13, 8, 4⟩, ⟨5, 12, 8, 2⟩, ⟨5, 11, 8, 4⟩, ⟨5, 13, 7, 2⟩, ⟨5, 13, 6, 4⟩]
  exact AllWinning.cons node_12256 (AllWinning.cons node_11204 (AllWinning.cons node_12315 (AllWinning.cons node_11335 (AllWinning.cons node_12319 (AllWinning.cons node_11345 (AllWinning.nil))))))

theorem node_13277 : Outcome ⟨5, 13, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 6⟩) (by decide) node_10310

theorem node_13278 : Outcome ⟨5, 14, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 2⟩) (by decide) node_12258

theorem node_13279 : Outcome ⟨5, 14, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 2⟩) (by decide) node_12258

theorem node_13280 : Outcome ⟨5, 15, 6, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 6, 2⟩) (by decide) node_12261

theorem node_13281 : Outcome ⟨5, 15, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 15, 6, 2⟩) (by decide) node_12261

theorem node_13282 : Outcome ⟨5, 15, 6, 12⟩ true :=
  Outcome.win (q := ⟨4, 15, 6, 2⟩) (by decide) node_12261

theorem node_13283 : Outcome ⟨5, 16, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 5, 4⟩) (by decide) node_11213

theorem node_13284 : Outcome ⟨5, 16, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 6⟩) (by decide) node_10310

theorem node_13285 : Outcome ⟨5, 17, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 4, 2⟩, ⟨3, 17, 4, 4⟩, ⟨2, 17, 4, 6⟩, ⟨1, 17, 4, 8⟩, ⟨5, 16, 4, 2⟩, ⟨5, 15, 4, 4⟩, ⟨5, 14, 4, 6⟩, ⟨5, 13, 4, 8⟩, ⟨5, 17, 3, 2⟩, ⟨5, 17, 2, 4⟩, ⟨5, 17, 1, 6⟩, ⟨5, 17, 0, 8⟩]
  exact AllWinning.cons node_12267 (AllWinning.cons node_11216 (AllWinning.cons node_10077 (AllWinning.cons node_9035 (AllWinning.cons node_12325 (AllWinning.cons node_11349 (AllWinning.cons node_10315 (AllWinning.cons node_9320 (AllWinning.cons node_12328 (AllWinning.cons node_11355 (AllWinning.cons node_10326 (AllWinning.cons node_9333 (AllWinning.nil))))))))))))

theorem node_13286 : Outcome ⟨5, 17, 4, 6⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 10⟩) (by decide) node_7968

theorem node_13287 : Outcome ⟨5, 18, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 3, 4⟩) (by decide) node_11220

theorem node_13288 : Outcome ⟨5, 18, 3, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 6⟩) (by decide) node_10331

theorem node_13289 : Outcome ⟨5, 18, 3, 18⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 14⟩) (by decide) node_6471

theorem node_13290 : Outcome ⟨5, 18, 3, 20⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 14⟩) (by decide) node_6471

theorem node_13291 : Outcome ⟨5, 19, 2, 2⟩ true :=
  Outcome.win (q := ⟨4, 19, 2, 2⟩) (by decide) node_12273

theorem node_13292 : Outcome ⟨5, 19, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 19, 2, 2⟩) (by decide) node_12273

theorem node_13293 : Outcome ⟨5, 19, 2, 16⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 18⟩) (by decide) node_4976

theorem node_13294 : Outcome ⟨5, 20, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 20, 1, 2⟩) (by decide) node_12277

theorem node_13295 : Outcome ⟨6, 0, 20, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 2⟩) (by decide) node_12342

theorem node_13296 : Outcome ⟨6, 0, 20, 12⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 2⟩) (by decide) node_12342

theorem node_13297 : Outcome ⟨6, 1, 19, 6⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 6⟩) (by decide) node_10091

theorem node_13298 : Outcome ⟨6, 1, 19, 12⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 6⟩) (by decide) node_10091

theorem node_13299 : Outcome ⟨6, 2, 18, 2⟩ true :=
  Outcome.win (q := ⟨6, 2, 17, 2⟩) (by decide) node_12351

theorem node_13300 : Outcome ⟨6, 2, 18, 16⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 14⟩) (by decide) node_6502

theorem node_13301 : Outcome ⟨6, 2, 18, 20⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 14⟩) (by decide) node_6502

theorem node_13302 : Outcome ⟨6, 3, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 2, 17, 2⟩) (by decide) node_12351

theorem node_13303 : Outcome ⟨6, 3, 17, 6⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 6⟩) (by decide) node_10352

theorem node_13304 : Outcome ⟨6, 3, 17, 12⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 6⟩) (by decide) node_10352

theorem node_13305 : Outcome ⟨6, 3, 17, 16⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 32⟩) (by decide) node_1490

theorem node_13306 : Outcome ⟨6, 4, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 4, 15, 2⟩) (by decide) node_12359

theorem node_13307 : Outcome ⟨6, 4, 16, 6⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 12⟩) (by decide) node_7431

theorem node_13308 : Outcome ⟨6, 4, 16, 16⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 12⟩) (by decide) node_7431

theorem node_13309 : Outcome ⟨6, 5, 15, 2⟩ true :=
  Outcome.win (q := ⟨6, 4, 15, 2⟩) (by decide) node_12359

theorem node_13310 : Outcome ⟨6, 5, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 15, 2⟩) (by decide) node_12359

theorem node_13311 : Outcome ⟨6, 5, 15, 12⟩ true :=
  Outcome.win (q := ⟨6, 4, 15, 2⟩) (by decide) node_12359

theorem node_13312 : Outcome ⟨6, 6, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13313 : Outcome ⟨6, 6, 14, 6⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13314 : Outcome ⟨6, 6, 14, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13315 : Outcome ⟨6, 6, 14, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 28⟩) (by decide) node_2238

theorem node_13316 : Outcome ⟨6, 7, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 7, 13, 2⟩, ⟨4, 7, 13, 4⟩, ⟨6, 6, 13, 2⟩, ⟨6, 5, 13, 4⟩, ⟨6, 7, 12, 2⟩, ⟨6, 7, 11, 4⟩]
  exact AllWinning.cons node_12300 (AllWinning.cons node_11251 (AllWinning.cons node_12365 (AllWinning.cons node_11379 (AllWinning.cons node_12369 (AllWinning.cons node_11388 (AllWinning.nil))))))

theorem node_13317 : Outcome ⟨6, 7, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 7, 13, 2⟩, ⟨4, 7, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨2, 7, 13, 8⟩, ⟨6, 6, 13, 2⟩, ⟨6, 5, 13, 4⟩, ⟨6, 4, 13, 6⟩, ⟨6, 3, 13, 8⟩, ⟨6, 7, 12, 2⟩, ⟨6, 7, 11, 4⟩, ⟨6, 7, 10, 6⟩, ⟨6, 7, 9, 8⟩]
  exact AllWinning.cons node_12300 (AllWinning.cons node_11251 (AllWinning.cons node_10117 (AllWinning.cons node_9074 (AllWinning.cons node_12365 (AllWinning.cons node_11379 (AllWinning.cons node_10357 (AllWinning.cons node_9350 (AllWinning.cons node_12369 (AllWinning.cons node_11388 (AllWinning.cons node_10368 (AllWinning.cons node_9365 (AllWinning.nil))))))))))))

theorem node_13318 : Outcome ⟨6, 7, 13, 6⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 10⟩) (by decide) node_8371

theorem node_13319 : Outcome ⟨6, 7, 13, 12⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 10⟩) (by decide) node_8371

theorem node_13320 : Outcome ⟨6, 7, 13, 14⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 10⟩) (by decide) node_8371

theorem node_13321 : Outcome ⟨6, 8, 12, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 4⟩) (by decide) node_11382

theorem node_13322 : Outcome ⟨6, 8, 12, 6⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 10⟩) (by decide) node_8009

theorem node_13323 : Outcome ⟨6, 8, 12, 16⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 10⟩) (by decide) node_8009

theorem node_13324 : Outcome ⟨6, 9, 11, 6⟩ true :=
  Outcome.win (q := ⟨6, 9, 10, 2⟩) (by decide) node_12377

theorem node_13325 : Outcome ⟨6, 9, 11, 10⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 14⟩) (by decide) node_6502

theorem node_13326 : Outcome ⟨6, 9, 11, 12⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 14⟩) (by decide) node_6502

theorem node_13327 : Outcome ⟨6, 10, 10, 2⟩ true :=
  Outcome.win (q := ⟨6, 9, 10, 2⟩) (by decide) node_12377

theorem node_13328 : Outcome ⟨6, 10, 10, 16⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 12⟩) (by decide) node_6985

theorem node_13329 : Outcome ⟨6, 10, 10, 22⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 12⟩) (by decide) node_6985

theorem node_13330 : Outcome ⟨6, 11, 9, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 9, 2⟩) (by decide) node_12381

theorem node_13331 : Outcome ⟨6, 11, 9, 10⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 14⟩) (by decide) node_6536

theorem node_13332 : Outcome ⟨6, 11, 9, 12⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 14⟩) (by decide) node_6536

theorem node_13333 : Outcome ⟨6, 12, 8, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 4⟩) (by decide) node_11407

theorem node_13334 : Outcome ⟨6, 12, 8, 6⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 10⟩) (by decide) node_8030

theorem node_13335 : Outcome ⟨6, 12, 8, 16⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 10⟩) (by decide) node_8030

theorem node_13336 : Outcome ⟨6, 13, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 7, 2⟩, ⟨4, 13, 7, 4⟩, ⟨6, 12, 7, 2⟩, ⟨6, 11, 7, 4⟩, ⟨6, 13, 6, 2⟩, ⟨6, 13, 5, 4⟩]
  exact AllWinning.cons node_12319 (AllWinning.cons node_11272 (AllWinning.cons node_12389 (AllWinning.cons node_11403 (AllWinning.cons node_12393 (AllWinning.cons node_11412 (AllWinning.nil))))))

theorem node_13337 : Outcome ⟨6, 13, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 7, 2⟩, ⟨4, 13, 7, 4⟩, ⟨3, 13, 7, 6⟩, ⟨2, 13, 7, 8⟩, ⟨6, 12, 7, 2⟩, ⟨6, 11, 7, 4⟩, ⟨6, 10, 7, 6⟩, ⟨6, 9, 7, 8⟩, ⟨6, 13, 6, 2⟩, ⟨6, 13, 5, 4⟩, ⟨6, 13, 4, 6⟩, ⟨6, 13, 3, 8⟩]
  exact AllWinning.cons node_12319 (AllWinning.cons node_11272 (AllWinning.cons node_10138 (AllWinning.cons node_9094 (AllWinning.cons node_12389 (AllWinning.cons node_11403 (AllWinning.cons node_10382 (AllWinning.cons node_9373 (AllWinning.cons node_12393 (AllWinning.cons node_11412 (AllWinning.cons node_10393 (AllWinning.cons node_9388 (AllWinning.nil))))))))))))

theorem node_13338 : Outcome ⟨6, 13, 7, 6⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 10⟩) (by decide) node_8383

theorem node_13339 : Outcome ⟨6, 13, 7, 12⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 10⟩) (by decide) node_8383

theorem node_13340 : Outcome ⟨6, 13, 7, 14⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 10⟩) (by decide) node_8383

theorem node_13341 : Outcome ⟨6, 14, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13342 : Outcome ⟨6, 14, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13343 : Outcome ⟨6, 14, 6, 12⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13344 : Outcome ⟨6, 14, 6, 14⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 28⟩) (by decide) node_2204

theorem node_13345 : Outcome ⟨6, 15, 5, 2⟩ true :=
  Outcome.win (q := ⟨6, 15, 4, 2⟩) (by decide) node_12400

theorem node_13346 : Outcome ⟨6, 15, 5, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 4, 2⟩) (by decide) node_12400

theorem node_13347 : Outcome ⟨6, 15, 5, 12⟩ true :=
  Outcome.win (q := ⟨6, 15, 4, 2⟩) (by decide) node_12400

theorem node_13348 : Outcome ⟨6, 16, 4, 2⟩ true :=
  Outcome.win (q := ⟨6, 15, 4, 2⟩) (by decide) node_12400

theorem node_13349 : Outcome ⟨6, 16, 4, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 12⟩) (by decide) node_7460

theorem node_13350 : Outcome ⟨6, 16, 4, 16⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 12⟩) (by decide) node_7460

theorem node_13351 : Outcome ⟨6, 17, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 2, 2⟩) (by decide) node_12406

theorem node_13352 : Outcome ⟨6, 17, 3, 6⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 6⟩) (by decide) node_10398

theorem node_13353 : Outcome ⟨6, 17, 3, 12⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 6⟩) (by decide) node_10398

theorem node_13354 : Outcome ⟨6, 17, 3, 16⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 32⟩) (by decide) node_1470

theorem node_13355 : Outcome ⟨6, 18, 2, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 2, 2⟩) (by decide) node_12406

theorem node_13356 : Outcome ⟨6, 18, 2, 16⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 14⟩) (by decide) node_6536

theorem node_13357 : Outcome ⟨6, 18, 2, 20⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 14⟩) (by decide) node_6536

theorem node_13358 : Outcome ⟨6, 19, 1, 6⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 6⟩) (by decide) node_10162

theorem node_13359 : Outcome ⟨6, 19, 1, 12⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 6⟩) (by decide) node_10162

theorem node_13360 : Outcome ⟨6, 20, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 2⟩) (by decide) node_12413

theorem node_13361 : Outcome ⟨6, 20, 0, 12⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 2⟩) (by decide) node_12413

theorem node_13362 : Outcome ⟨7, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 2⟩) (by decide) node_12342

theorem node_13363 : Outcome ⟨7, 0, 19, 8⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 2⟩) (by decide) node_12342

theorem node_13364 : Outcome ⟨7, 0, 19, 12⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 24⟩) (by decide) node_3172

theorem node_13365 : Outcome ⟨7, 0, 19, 24⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 24⟩) (by decide) node_3172

theorem node_13366 : Outcome ⟨7, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 2⟩) (by decide) node_12422

theorem node_13367 : Outcome ⟨7, 2, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 2, 17, 2⟩) (by decide) node_12351

theorem node_13368 : Outcome ⟨7, 2, 17, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 12⟩) (by decide) node_7037

theorem node_13369 : Outcome ⟨7, 2, 17, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 12⟩) (by decide) node_7037

theorem node_13370 : Outcome ⟨7, 3, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 3, 16, 4⟩) (by decide) node_11308

theorem node_13371 : Outcome ⟨7, 3, 16, 6⟩ true :=
  Outcome.win (q := ⟨5, 3, 16, 4⟩) (by decide) node_11308

theorem node_13372 : Outcome ⟨7, 3, 16, 16⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 28⟩) (by decide) node_2278

theorem node_13373 : Outcome ⟨7, 4, 15, 16⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 20⟩) (by decide) node_4352

theorem node_13374 : Outcome ⟨7, 5, 14, 4⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 2⟩) (by decide) node_12437

theorem node_13375 : Outcome ⟨7, 5, 14, 6⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 2⟩) (by decide) node_12437

theorem node_13376 : Outcome ⟨7, 6, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 6, 13, 2⟩, ⟨5, 6, 13, 4⟩, ⟨7, 5, 13, 2⟩, ⟨7, 4, 13, 4⟩, ⟨7, 6, 12, 2⟩, ⟨7, 6, 11, 4⟩]
  exact AllWinning.cons node_12365 (AllWinning.cons node_11315 (AllWinning.cons node_12440 (AllWinning.cons node_11446 (AllWinning.cons node_12442 (AllWinning.cons node_11454 (AllWinning.nil))))))

theorem node_13377 : Outcome ⟨7, 6, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 6, 13, 2⟩, ⟨5, 6, 13, 4⟩, ⟨4, 6, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨7, 5, 13, 2⟩, ⟨7, 4, 13, 4⟩, ⟨7, 3, 13, 6⟩, ⟨7, 2, 13, 8⟩, ⟨7, 6, 12, 2⟩, ⟨7, 6, 11, 4⟩, ⟨7, 6, 10, 6⟩, ⟨7, 6, 9, 8⟩]
  exact AllWinning.cons node_12365 (AllWinning.cons node_11315 (AllWinning.cons node_10191 (AllWinning.cons node_9144 (AllWinning.cons node_12440 (AllWinning.cons node_11446 (AllWinning.cons node_10430 (AllWinning.cons node_9412 (AllWinning.cons node_12442 (AllWinning.cons node_11454 (AllWinning.cons node_10444 (AllWinning.cons node_9431 (AllWinning.nil))))))))))))

theorem node_13378 : Outcome ⟨7, 6, 13, 6⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 10⟩) (by decide) node_8447

theorem node_13379 : Outcome ⟨7, 6, 13, 12⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 10⟩) (by decide) node_8447

theorem node_13380 : Outcome ⟨7, 6, 13, 14⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 10⟩) (by decide) node_8447

theorem node_13381 : Outcome ⟨7, 7, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 7, 12, 2⟩, ⟨5, 7, 12, 4⟩, ⟨7, 6, 12, 2⟩, ⟨7, 5, 12, 4⟩, ⟨7, 7, 11, 2⟩, ⟨7, 7, 10, 4⟩]
  exact AllWinning.cons node_12369 (AllWinning.cons node_11318 (AllWinning.cons node_12442 (AllWinning.cons node_11448 (AllWinning.cons node_12446 (AllWinning.cons node_11457 (AllWinning.nil))))))

theorem node_13382 : Outcome ⟨7, 7, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 7, 12, 2⟩, ⟨5, 7, 12, 4⟩, ⟨4, 7, 12, 6⟩, ⟨3, 7, 12, 8⟩, ⟨7, 6, 12, 2⟩, ⟨7, 5, 12, 4⟩, ⟨7, 4, 12, 6⟩, ⟨7, 3, 12, 8⟩, ⟨7, 7, 11, 2⟩, ⟨7, 7, 10, 4⟩, ⟨7, 7, 9, 6⟩, ⟨7, 7, 8, 8⟩]
  exact AllWinning.cons node_12369 (AllWinning.cons node_11318 (AllWinning.cons node_10196 (AllWinning.cons node_9149 (AllWinning.cons node_12442 (AllWinning.cons node_11448 (AllWinning.cons node_10434 (AllWinning.cons node_9418 (AllWinning.cons node_12446 (AllWinning.cons node_11457 (AllWinning.cons node_10449 (AllWinning.cons node_9435 (AllWinning.nil))))))))))))

theorem node_13383 : Outcome ⟨7, 7, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 7, 12, 2⟩, ⟨5, 7, 12, 4⟩, ⟨4, 7, 12, 6⟩, ⟨3, 7, 12, 8⟩, ⟨2, 7, 12, 10⟩, ⟨1, 7, 12, 12⟩, ⟨7, 6, 12, 2⟩, ⟨7, 5, 12, 4⟩, ⟨7, 4, 12, 6⟩, ⟨7, 3, 12, 8⟩, ⟨7, 2, 12, 10⟩, ⟨7, 1, 12, 12⟩, ⟨7, 7, 11, 2⟩, ⟨7, 7, 10, 4⟩, ⟨7, 7, 9, 6⟩, ⟨7, 7, 8, 8⟩, ⟨7, 7, 7, 10⟩, ⟨7, 7, 6, 12⟩]
  exact AllWinning.cons node_12369 (AllWinning.cons node_11318 (AllWinning.cons node_10196 (AllWinning.cons node_9149 (AllWinning.cons node_8093 (AllWinning.cons node_7061 (AllWinning.cons node_12442 (AllWinning.cons node_11448 (AllWinning.cons node_10434 (AllWinning.cons node_9418 (AllWinning.cons node_8428 (AllWinning.cons node_7489 (AllWinning.cons node_12446 (AllWinning.cons node_11457 (AllWinning.cons node_10449 (AllWinning.cons node_9435 (AllWinning.cons node_8458 (AllWinning.cons node_7512 (AllWinning.nil))))))))))))))))))

theorem node_13384 : Outcome ⟨7, 7, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 7, 12, 2⟩, ⟨5, 7, 12, 4⟩, ⟨4, 7, 12, 6⟩, ⟨3, 7, 12, 8⟩, ⟨2, 7, 12, 10⟩, ⟨1, 7, 12, 12⟩, ⟨0, 7, 12, 14⟩, ⟨7, 6, 12, 2⟩, ⟨7, 5, 12, 4⟩, ⟨7, 4, 12, 6⟩, ⟨7, 3, 12, 8⟩, ⟨7, 2, 12, 10⟩, ⟨7, 1, 12, 12⟩, ⟨7, 0, 12, 14⟩, ⟨7, 7, 11, 2⟩, ⟨7, 7, 10, 4⟩, ⟨7, 7, 9, 6⟩, ⟨7, 7, 8, 8⟩, ⟨7, 7, 7, 10⟩, ⟨7, 7, 6, 12⟩, ⟨7, 7, 5, 14⟩, ⟨7, 7, 4, 16⟩]
  exact AllWinning.cons node_12369 (AllWinning.cons node_11318 (AllWinning.cons node_10196 (AllWinning.cons node_9149 (AllWinning.cons node_8093 (AllWinning.cons node_7061 (AllWinning.cons node_6066 (AllWinning.cons node_12442 (AllWinning.cons node_11448 (AllWinning.cons node_10434 (AllWinning.cons node_9418 (AllWinning.cons node_8428 (AllWinning.cons node_7489 (AllWinning.cons node_6553 (AllWinning.cons node_12446 (AllWinning.cons node_11457 (AllWinning.cons node_10449 (AllWinning.cons node_9435 (AllWinning.cons node_8458 (AllWinning.cons node_7512 (AllWinning.cons node_6589 (AllWinning.cons node_5758 (AllWinning.nil))))))))))))))))))))))

theorem node_13385 : Outcome ⟨7, 7, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 7, 12, 2⟩, ⟨5, 7, 12, 4⟩, ⟨4, 7, 12, 6⟩, ⟨3, 7, 12, 8⟩, ⟨2, 7, 12, 10⟩, ⟨1, 7, 12, 12⟩, ⟨0, 7, 12, 14⟩, ⟨7, 6, 12, 2⟩, ⟨7, 5, 12, 4⟩, ⟨7, 4, 12, 6⟩, ⟨7, 3, 12, 8⟩, ⟨7, 2, 12, 10⟩, ⟨7, 1, 12, 12⟩, ⟨7, 0, 12, 14⟩, ⟨7, 7, 11, 2⟩, ⟨7, 7, 10, 4⟩, ⟨7, 7, 9, 6⟩, ⟨7, 7, 8, 8⟩, ⟨7, 7, 7, 10⟩, ⟨7, 7, 6, 12⟩, ⟨7, 7, 5, 14⟩, ⟨7, 7, 4, 16⟩, ⟨7, 7, 3, 18⟩, ⟨7, 7, 2, 20⟩]
  exact AllWinning.cons node_12369 (AllWinning.cons node_11318 (AllWinning.cons node_10196 (AllWinning.cons node_9149 (AllWinning.cons node_8093 (AllWinning.cons node_7061 (AllWinning.cons node_6066 (AllWinning.cons node_12442 (AllWinning.cons node_11448 (AllWinning.cons node_10434 (AllWinning.cons node_9418 (AllWinning.cons node_8428 (AllWinning.cons node_7489 (AllWinning.cons node_6553 (AllWinning.cons node_12446 (AllWinning.cons node_11457 (AllWinning.cons node_10449 (AllWinning.cons node_9435 (AllWinning.cons node_8458 (AllWinning.cons node_7512 (AllWinning.cons node_6589 (AllWinning.cons node_5758 (AllWinning.cons node_5063 (AllWinning.cons node_4381 (AllWinning.nil))))))))))))))))))))))))

theorem node_13386 : Outcome ⟨7, 7, 12, 16⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 24⟩) (by decide) node_3209

theorem node_13387 : Outcome ⟨7, 8, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 11, 2⟩, ⟨5, 8, 11, 4⟩, ⟨7, 7, 11, 2⟩, ⟨7, 6, 11, 4⟩, ⟨7, 8, 10, 2⟩, ⟨7, 8, 9, 4⟩]
  exact AllWinning.cons node_12373 (AllWinning.cons node_11323 (AllWinning.cons node_12446 (AllWinning.cons node_11454 (AllWinning.cons node_12448 (AllWinning.cons node_11460 (AllWinning.nil))))))

theorem node_13388 : Outcome ⟨7, 8, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 11, 2⟩, ⟨5, 8, 11, 4⟩, ⟨4, 8, 11, 6⟩, ⟨3, 8, 11, 8⟩, ⟨7, 7, 11, 2⟩, ⟨7, 6, 11, 4⟩, ⟨7, 5, 11, 6⟩, ⟨7, 4, 11, 8⟩, ⟨7, 8, 10, 2⟩, ⟨7, 8, 9, 4⟩, ⟨7, 8, 8, 6⟩, ⟨7, 8, 7, 8⟩]
  exact AllWinning.cons node_12373 (AllWinning.cons node_11323 (AllWinning.cons node_10201 (AllWinning.cons node_9152 (AllWinning.cons node_12446 (AllWinning.cons node_11454 (AllWinning.cons node_10438 (AllWinning.cons node_9423 (AllWinning.cons node_12448 (AllWinning.cons node_11460 (AllWinning.cons node_10452 (AllWinning.cons node_9437 (AllWinning.nil))))))))))))

theorem node_13389 : Outcome ⟨7, 8, 11, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 10⟩) (by decide) node_8463

theorem node_13390 : Outcome ⟨7, 8, 11, 16⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 14⟩) (by decide) node_6562

theorem node_13391 : Outcome ⟨7, 8, 11, 18⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 14⟩) (by decide) node_6562

theorem node_13392 : Outcome ⟨7, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨6, 9, 10, 2⟩) (by decide) node_12377

theorem node_13393 : Outcome ⟨7, 9, 10, 6⟩ true :=
  Outcome.win (q := ⟨6, 9, 10, 2⟩) (by decide) node_12377

theorem node_13394 : Outcome ⟨7, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨6, 10, 9, 2⟩) (by decide) node_12381

theorem node_13395 : Outcome ⟨7, 10, 9, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 9, 2⟩) (by decide) node_12381

theorem node_13396 : Outcome ⟨7, 11, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 8, 2⟩, ⟨5, 11, 8, 4⟩, ⟨7, 10, 8, 2⟩, ⟨7, 9, 8, 4⟩, ⟨7, 11, 7, 2⟩, ⟨7, 11, 6, 4⟩]
  exact AllWinning.cons node_12385 (AllWinning.cons node_11335 (AllWinning.cons node_12454 (AllWinning.cons node_11464 (AllWinning.cons node_12458 (AllWinning.cons node_11470 (AllWinning.nil))))))

theorem node_13397 : Outcome ⟨7, 11, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 8, 2⟩, ⟨5, 11, 8, 4⟩, ⟨4, 11, 8, 6⟩, ⟨3, 11, 8, 8⟩, ⟨7, 10, 8, 2⟩, ⟨7, 9, 8, 4⟩, ⟨7, 8, 8, 6⟩, ⟨7, 7, 8, 8⟩, ⟨7, 11, 7, 2⟩, ⟨7, 11, 6, 4⟩, ⟨7, 11, 5, 6⟩, ⟨7, 11, 4, 8⟩]
  exact AllWinning.cons node_12385 (AllWinning.cons node_11335 (AllWinning.cons node_10212 (AllWinning.cons node_9165 (AllWinning.cons node_12454 (AllWinning.cons node_11464 (AllWinning.cons node_10452 (AllWinning.cons node_9435 (AllWinning.cons node_12458 (AllWinning.cons node_11470 (AllWinning.cons node_10466 (AllWinning.cons node_9450 (AllWinning.nil))))))))))))

theorem node_13398 : Outcome ⟨7, 11, 8, 6⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 10⟩) (by decide) node_8447

theorem node_13399 : Outcome ⟨7, 11, 8, 16⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 14⟩) (by decide) node_6609

theorem node_13400 : Outcome ⟨7, 11, 8, 18⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 14⟩) (by decide) node_6609

theorem node_13401 : Outcome ⟨7, 12, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 7, 2⟩, ⟨5, 12, 7, 4⟩, ⟨7, 11, 7, 2⟩, ⟨7, 10, 7, 4⟩, ⟨7, 12, 6, 2⟩, ⟨7, 12, 5, 4⟩]
  exact AllWinning.cons node_12389 (AllWinning.cons node_11340 (AllWinning.cons node_12458 (AllWinning.cons node_11467 (AllWinning.cons node_12460 (AllWinning.cons node_11473 (AllWinning.nil))))))

theorem node_13402 : Outcome ⟨7, 12, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 7, 2⟩, ⟨5, 12, 7, 4⟩, ⟨4, 12, 7, 6⟩, ⟨3, 12, 7, 8⟩, ⟨7, 11, 7, 2⟩, ⟨7, 10, 7, 4⟩, ⟨7, 9, 7, 6⟩, ⟨7, 8, 7, 8⟩, ⟨7, 12, 6, 2⟩, ⟨7, 12, 5, 4⟩, ⟨7, 12, 4, 6⟩, ⟨7, 12, 3, 8⟩]
  exact AllWinning.cons node_12389 (AllWinning.cons node_11340 (AllWinning.cons node_10217 (AllWinning.cons node_9172 (AllWinning.cons node_12458 (AllWinning.cons node_11467 (AllWinning.cons node_10457 (AllWinning.cons node_9437 (AllWinning.cons node_12460 (AllWinning.cons node_11473 (AllWinning.cons node_10472 (AllWinning.cons node_9455 (AllWinning.nil))))))))))))

theorem node_13403 : Outcome ⟨7, 12, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 7, 2⟩, ⟨5, 12, 7, 4⟩, ⟨4, 12, 7, 6⟩, ⟨3, 12, 7, 8⟩, ⟨2, 12, 7, 10⟩, ⟨1, 12, 7, 12⟩, ⟨7, 11, 7, 2⟩, ⟨7, 10, 7, 4⟩, ⟨7, 9, 7, 6⟩, ⟨7, 8, 7, 8⟩, ⟨7, 7, 7, 10⟩, ⟨7, 6, 7, 12⟩, ⟨7, 12, 6, 2⟩, ⟨7, 12, 5, 4⟩, ⟨7, 12, 4, 6⟩, ⟨7, 12, 3, 8⟩, ⟨7, 12, 2, 10⟩, ⟨7, 12, 1, 12⟩]
  exact AllWinning.cons node_12389 (AllWinning.cons node_11340 (AllWinning.cons node_10217 (AllWinning.cons node_9172 (AllWinning.cons node_8119 (AllWinning.cons node_7078 (AllWinning.cons node_12458 (AllWinning.cons node_11467 (AllWinning.cons node_10457 (AllWinning.cons node_9437 (AllWinning.cons node_8458 (AllWinning.cons node_7510 (AllWinning.cons node_12460 (AllWinning.cons node_11473 (AllWinning.cons node_10472 (AllWinning.cons node_9455 (AllWinning.cons node_8486 (AllWinning.cons node_7532 (AllWinning.nil))))))))))))))))))

theorem node_13404 : Outcome ⟨7, 12, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 7, 2⟩, ⟨5, 12, 7, 4⟩, ⟨4, 12, 7, 6⟩, ⟨3, 12, 7, 8⟩, ⟨2, 12, 7, 10⟩, ⟨1, 12, 7, 12⟩, ⟨0, 12, 7, 14⟩, ⟨7, 11, 7, 2⟩, ⟨7, 10, 7, 4⟩, ⟨7, 9, 7, 6⟩, ⟨7, 8, 7, 8⟩, ⟨7, 7, 7, 10⟩, ⟨7, 6, 7, 12⟩, ⟨7, 5, 7, 14⟩, ⟨7, 4, 7, 16⟩, ⟨7, 12, 6, 2⟩, ⟨7, 12, 5, 4⟩, ⟨7, 12, 4, 6⟩, ⟨7, 12, 3, 8⟩, ⟨7, 12, 2, 10⟩, ⟨7, 12, 1, 12⟩, ⟨7, 12, 0, 14⟩]
  exact AllWinning.cons node_12389 (AllWinning.cons node_11340 (AllWinning.cons node_10217 (AllWinning.cons node_9172 (AllWinning.cons node_8119 (AllWinning.cons node_7078 (AllWinning.cons node_6086 (AllWinning.cons node_12458 (AllWinning.cons node_11467 (AllWinning.cons node_10457 (AllWinning.cons node_9437 (AllWinning.cons node_8458 (AllWinning.cons node_7510 (AllWinning.cons node_6583 (AllWinning.cons node_5748 (AllWinning.cons node_12460 (AllWinning.cons node_11473 (AllWinning.cons node_10472 (AllWinning.cons node_9455 (AllWinning.cons node_8486 (AllWinning.cons node_7532 (AllWinning.cons node_6618 (AllWinning.nil))))))))))))))))))))))

theorem node_13405 : Outcome ⟨7, 12, 7, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 7, 2⟩, ⟨5, 12, 7, 4⟩, ⟨4, 12, 7, 6⟩, ⟨3, 12, 7, 8⟩, ⟨2, 12, 7, 10⟩, ⟨1, 12, 7, 12⟩, ⟨0, 12, 7, 14⟩, ⟨7, 11, 7, 2⟩, ⟨7, 10, 7, 4⟩, ⟨7, 9, 7, 6⟩, ⟨7, 8, 7, 8⟩, ⟨7, 7, 7, 10⟩, ⟨7, 6, 7, 12⟩, ⟨7, 5, 7, 14⟩, ⟨7, 4, 7, 16⟩, ⟨7, 3, 7, 18⟩, ⟨7, 2, 7, 20⟩, ⟨7, 12, 6, 2⟩, ⟨7, 12, 5, 4⟩, ⟨7, 12, 4, 6⟩, ⟨7, 12, 3, 8⟩, ⟨7, 12, 2, 10⟩, ⟨7, 12, 1, 12⟩, ⟨7, 12, 0, 14⟩]
  exact AllWinning.cons node_12389 (AllWinning.cons node_11340 (AllWinning.cons node_10217 (AllWinning.cons node_9172 (AllWinning.cons node_8119 (AllWinning.cons node_7078 (AllWinning.cons node_6086 (AllWinning.cons node_12458 (AllWinning.cons node_11467 (AllWinning.cons node_10457 (AllWinning.cons node_9437 (AllWinning.cons node_8458 (AllWinning.cons node_7510 (AllWinning.cons node_6583 (AllWinning.cons node_5748 (AllWinning.cons node_5049 (AllWinning.cons node_4335 (AllWinning.cons node_12460 (AllWinning.cons node_11473 (AllWinning.cons node_10472 (AllWinning.cons node_9455 (AllWinning.cons node_8486 (AllWinning.cons node_7532 (AllWinning.cons node_6618 (AllWinning.nil))))))))))))))))))))))))

theorem node_13406 : Outcome ⟨7, 12, 7, 16⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 24⟩) (by decide) node_3172

theorem node_13407 : Outcome ⟨7, 13, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 6, 2⟩, ⟨5, 13, 6, 4⟩, ⟨7, 12, 6, 2⟩, ⟨7, 11, 6, 4⟩, ⟨7, 13, 5, 2⟩, ⟨7, 13, 4, 4⟩]
  exact AllWinning.cons node_12393 (AllWinning.cons node_11345 (AllWinning.cons node_12460 (AllWinning.cons node_11470 (AllWinning.cons node_12464 (AllWinning.cons node_11479 (AllWinning.nil))))))

theorem node_13408 : Outcome ⟨7, 13, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 6, 2⟩, ⟨5, 13, 6, 4⟩, ⟨4, 13, 6, 6⟩, ⟨3, 13, 6, 8⟩, ⟨7, 12, 6, 2⟩, ⟨7, 11, 6, 4⟩, ⟨7, 10, 6, 6⟩, ⟨7, 9, 6, 8⟩, ⟨7, 13, 5, 2⟩, ⟨7, 13, 4, 4⟩, ⟨7, 13, 3, 6⟩, ⟨7, 13, 2, 8⟩]
  exact AllWinning.cons node_12393 (AllWinning.cons node_11345 (AllWinning.cons node_10221 (AllWinning.cons node_9175 (AllWinning.cons node_12460 (AllWinning.cons node_11470 (AllWinning.cons node_10461 (AllWinning.cons node_9440 (AllWinning.cons node_12464 (AllWinning.cons node_11479 (AllWinning.cons node_10477 (AllWinning.cons node_9458 (AllWinning.nil))))))))))))

theorem node_13409 : Outcome ⟨7, 13, 6, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 10⟩) (by decide) node_8463

theorem node_13410 : Outcome ⟨7, 13, 6, 12⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 10⟩) (by decide) node_8463

theorem node_13411 : Outcome ⟨7, 13, 6, 14⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 10⟩) (by decide) node_8463

theorem node_13412 : Outcome ⟨7, 14, 5, 4⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 2⟩) (by decide) node_12466

theorem node_13413 : Outcome ⟨7, 14, 5, 6⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 2⟩) (by decide) node_12466

theorem node_13414 : Outcome ⟨7, 15, 4, 16⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 20⟩) (by decide) node_4367

theorem node_13415 : Outcome ⟨7, 16, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 3, 4⟩) (by decide) node_11352

theorem node_13416 : Outcome ⟨7, 16, 3, 6⟩ true :=
  Outcome.win (q := ⟨5, 16, 3, 4⟩) (by decide) node_11352

theorem node_13417 : Outcome ⟨7, 16, 3, 16⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 28⟩) (by decide) node_2262

theorem node_13418 : Outcome ⟨7, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨6, 17, 2, 2⟩) (by decide) node_12406

theorem node_13419 : Outcome ⟨7, 17, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 12⟩) (by decide) node_7103

theorem node_13420 : Outcome ⟨7, 17, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 12⟩) (by decide) node_7103

theorem node_13421 : Outcome ⟨7, 18, 1, 2⟩ true :=
  Outcome.win (q := ⟨7, 17, 1, 2⟩) (by decide) node_12480

theorem node_13422 : Outcome ⟨7, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 2⟩) (by decide) node_12413

theorem node_13423 : Outcome ⟨7, 19, 0, 8⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 2⟩) (by decide) node_12413

theorem node_13424 : Outcome ⟨7, 19, 0, 12⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 24⟩) (by decide) node_3209

theorem node_13425 : Outcome ⟨7, 19, 0, 24⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 24⟩) (by decide) node_3209

theorem node_13426 : Outcome ⟨8, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 16, 4⟩) (by decide) node_11497

theorem node_13427 : Outcome ⟨8, 0, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 6⟩) (by decide) node_10248

theorem node_13428 : Outcome ⟨8, 0, 18, 16⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 20⟩) (by decide) node_4399

theorem node_13429 : Outcome ⟨8, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 2⟩) (by decide) node_12422

theorem node_13430 : Outcome ⟨8, 1, 17, 4⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 2⟩) (by decide) node_12422

theorem node_13431 : Outcome ⟨8, 1, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 12⟩) (by decide) node_7120

theorem node_13432 : Outcome ⟨8, 1, 17, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 12⟩) (by decide) node_7120

theorem node_13433 : Outcome ⟨8, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 16, 4⟩) (by decide) node_11497

theorem node_13434 : Outcome ⟨8, 2, 16, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 16, 4⟩) (by decide) node_11497

theorem node_13435 : Outcome ⟨8, 2, 16, 6⟩ true :=
  Outcome.win (q := ⟨8, 0, 16, 4⟩) (by decide) node_11497

theorem node_13436 : Outcome ⟨8, 3, 15, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 2⟩) (by decide) node_12430

theorem node_13437 : Outcome ⟨8, 3, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 2⟩) (by decide) node_12430

theorem node_13438 : Outcome ⟨8, 3, 15, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 2⟩) (by decide) node_12430

theorem node_13439 : Outcome ⟨8, 3, 15, 20⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 2⟩) (by decide) node_12430

theorem node_13440 : Outcome ⟨8, 4, 14, 4⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 2⟩) (by decide) node_12437

theorem node_13441 : Outcome ⟨8, 4, 14, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 12⟩) (by decide) node_7134

theorem node_13442 : Outcome ⟨8, 4, 14, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 12⟩) (by decide) node_7134

theorem node_13443 : Outcome ⟨8, 5, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 13, 2⟩, ⟨6, 5, 13, 4⟩, ⟨8, 4, 13, 2⟩, ⟨8, 3, 13, 4⟩, ⟨8, 5, 12, 2⟩, ⟨8, 5, 11, 4⟩]
  exact AllWinning.cons node_12440 (AllWinning.cons node_11379 (AllWinning.cons node_12499 (AllWinning.cons node_11506 (AllWinning.cons node_12501 (AllWinning.cons node_11511 (AllWinning.nil))))))

theorem node_13444 : Outcome ⟨8, 5, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 6⟩) (by decide) node_10270

theorem node_13445 : Outcome ⟨8, 6, 12, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 4⟩) (by decide) node_11382

theorem node_13446 : Outcome ⟨8, 6, 12, 6⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 10⟩) (by decide) node_8506

theorem node_13447 : Outcome ⟨8, 6, 12, 16⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 10⟩) (by decide) node_8506

theorem node_13448 : Outcome ⟨8, 7, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 7, 11, 2⟩, ⟨6, 7, 11, 4⟩, ⟨8, 6, 11, 2⟩, ⟨8, 5, 11, 4⟩, ⟨8, 7, 10, 2⟩, ⟨8, 7, 9, 4⟩]
  exact AllWinning.cons node_12446 (AllWinning.cons node_11388 (AllWinning.cons node_12505 (AllWinning.cons node_11511 (AllWinning.cons node_12509 (AllWinning.cons node_11519 (AllWinning.nil))))))

theorem node_13449 : Outcome ⟨8, 7, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 7, 11, 2⟩, ⟨6, 7, 11, 4⟩, ⟨5, 7, 11, 6⟩, ⟨4, 7, 11, 8⟩, ⟨8, 6, 11, 2⟩, ⟨8, 5, 11, 4⟩, ⟨8, 4, 11, 6⟩, ⟨8, 3, 11, 8⟩, ⟨8, 7, 10, 2⟩, ⟨8, 7, 9, 4⟩, ⟨8, 7, 8, 6⟩, ⟨8, 7, 7, 8⟩]
  exact AllWinning.cons node_12446 (AllWinning.cons node_11388 (AllWinning.cons node_10279 (AllWinning.cons node_9225 (AllWinning.cons node_12505 (AllWinning.cons node_11511 (AllWinning.cons node_10505 (AllWinning.cons node_9478 (AllWinning.cons node_12509 (AllWinning.cons node_11519 (AllWinning.cons node_10517 (AllWinning.cons node_9492 (AllWinning.nil))))))))))))

theorem node_13450 : Outcome ⟨8, 7, 11, 6⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 10⟩) (by decide) node_8545

theorem node_13451 : Outcome ⟨8, 7, 11, 16⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 14⟩) (by decide) node_6143

theorem node_13452 : Outcome ⟨8, 7, 11, 18⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 14⟩) (by decide) node_6143

theorem node_13453 : Outcome ⟨8, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 4⟩) (by decide) node_11523

theorem node_13454 : Outcome ⟨8, 8, 10, 6⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 4⟩) (by decide) node_11523

theorem node_13455 : Outcome ⟨8, 8, 10, 16⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 20⟩) (by decide) node_4440

theorem node_13456 : Outcome ⟨8, 9, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 9, 9, 2⟩, ⟨6, 9, 9, 4⟩, ⟨8, 8, 9, 2⟩, ⟨8, 7, 9, 4⟩, ⟨8, 9, 8, 2⟩, ⟨8, 9, 7, 4⟩]
  exact AllWinning.cons node_12452 (AllWinning.cons node_11396 (AllWinning.cons node_12513 (AllWinning.cons node_11519 (AllWinning.cons node_12516 (AllWinning.cons node_11527 (AllWinning.nil))))))

theorem node_13457 : Outcome ⟨8, 9, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 9, 9, 2⟩, ⟨6, 9, 9, 4⟩, ⟨5, 9, 9, 6⟩, ⟨4, 9, 9, 8⟩, ⟨8, 8, 9, 2⟩, ⟨8, 7, 9, 4⟩, ⟨8, 6, 9, 6⟩, ⟨8, 5, 9, 8⟩, ⟨8, 9, 8, 2⟩, ⟨8, 9, 7, 4⟩, ⟨8, 9, 6, 6⟩, ⟨8, 9, 5, 8⟩]
  exact AllWinning.cons node_12452 (AllWinning.cons node_11396 (AllWinning.cons node_10291 (AllWinning.cons node_9233 (AllWinning.cons node_12513 (AllWinning.cons node_11519 (AllWinning.cons node_10514 (AllWinning.cons node_9486 (AllWinning.cons node_12516 (AllWinning.cons node_11527 (AllWinning.cons node_10527 (AllWinning.cons node_9497 (AllWinning.nil))))))))))))

theorem node_13458 : Outcome ⟨8, 9, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 9, 9, 2⟩, ⟨6, 9, 9, 4⟩, ⟨5, 9, 9, 6⟩, ⟨4, 9, 9, 8⟩, ⟨3, 9, 9, 10⟩, ⟨2, 9, 9, 12⟩, ⟨8, 8, 9, 2⟩, ⟨8, 7, 9, 4⟩, ⟨8, 6, 9, 6⟩, ⟨8, 5, 9, 8⟩, ⟨8, 4, 9, 10⟩, ⟨8, 3, 9, 12⟩, ⟨8, 9, 8, 2⟩, ⟨8, 9, 7, 4⟩, ⟨8, 9, 6, 6⟩, ⟨8, 9, 5, 8⟩, ⟨8, 9, 4, 10⟩, ⟨8, 9, 3, 12⟩]
  exact AllWinning.cons node_12452 (AllWinning.cons node_11396 (AllWinning.cons node_10291 (AllWinning.cons node_9233 (AllWinning.cons node_8184 (AllWinning.cons node_7157 (AllWinning.cons node_12513 (AllWinning.cons node_11519 (AllWinning.cons node_10514 (AllWinning.cons node_9486 (AllWinning.cons node_8522 (AllWinning.cons node_7551 (AllWinning.cons node_12516 (AllWinning.cons node_11527 (AllWinning.cons node_10527 (AllWinning.cons node_9497 (AllWinning.cons node_8559 (AllWinning.cons node_7574 (AllWinning.nil))))))))))))))))))

theorem node_13459 : Outcome ⟨8, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 4⟩) (by decide) node_11523

theorem node_13460 : Outcome ⟨8, 10, 8, 6⟩ true :=
  Outcome.win (q := ⟨8, 8, 8, 4⟩) (by decide) node_11523

theorem node_13461 : Outcome ⟨8, 10, 8, 16⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 20⟩) (by decide) node_4399

theorem node_13462 : Outcome ⟨8, 11, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 11, 7, 2⟩, ⟨6, 11, 7, 4⟩, ⟨8, 10, 7, 2⟩, ⟨8, 9, 7, 4⟩, ⟨8, 11, 6, 2⟩, ⟨8, 11, 5, 4⟩]
  exact AllWinning.cons node_12458 (AllWinning.cons node_11403 (AllWinning.cons node_12519 (AllWinning.cons node_11527 (AllWinning.cons node_12523 (AllWinning.cons node_11534 (AllWinning.nil))))))

theorem node_13463 : Outcome ⟨8, 11, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 11, 7, 2⟩, ⟨6, 11, 7, 4⟩, ⟨5, 11, 7, 6⟩, ⟨4, 11, 7, 8⟩, ⟨8, 10, 7, 2⟩, ⟨8, 9, 7, 4⟩, ⟨8, 8, 7, 6⟩, ⟨8, 7, 7, 8⟩, ⟨8, 11, 6, 2⟩, ⟨8, 11, 5, 4⟩, ⟨8, 11, 4, 6⟩, ⟨8, 11, 3, 8⟩]
  exact AllWinning.cons node_12458 (AllWinning.cons node_11403 (AllWinning.cons node_10300 (AllWinning.cons node_9242 (AllWinning.cons node_12519 (AllWinning.cons node_11527 (AllWinning.cons node_10522 (AllWinning.cons node_9492 (AllWinning.cons node_12523 (AllWinning.cons node_11534 (AllWinning.cons node_10537 (AllWinning.cons node_9504 (AllWinning.nil))))))))))))

theorem node_13464 : Outcome ⟨8, 11, 7, 6⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 10⟩) (by decide) node_8533

theorem node_13465 : Outcome ⟨8, 11, 7, 16⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 14⟩) (by decide) node_6168

theorem node_13466 : Outcome ⟨8, 11, 7, 18⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 14⟩) (by decide) node_6168

theorem node_13467 : Outcome ⟨8, 12, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 4⟩) (by decide) node_11407

theorem node_13468 : Outcome ⟨8, 12, 6, 6⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 10⟩) (by decide) node_8545

theorem node_13469 : Outcome ⟨8, 12, 6, 16⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 10⟩) (by decide) node_8545

theorem node_13470 : Outcome ⟨8, 13, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 13, 5, 2⟩, ⟨6, 13, 5, 4⟩, ⟨8, 12, 5, 2⟩, ⟨8, 11, 5, 4⟩, ⟨8, 13, 4, 2⟩, ⟨8, 13, 3, 4⟩]
  exact AllWinning.cons node_12464 (AllWinning.cons node_11412 (AllWinning.cons node_12527 (AllWinning.cons node_11534 (AllWinning.cons node_12531 (AllWinning.cons node_11541 (AllWinning.nil))))))

theorem node_13471 : Outcome ⟨8, 13, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 6⟩) (by decide) node_10310

theorem node_13472 : Outcome ⟨8, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 2⟩) (by decide) node_12466

theorem node_13473 : Outcome ⟨8, 14, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 12⟩) (by decide) node_7180

theorem node_13474 : Outcome ⟨8, 14, 4, 22⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 12⟩) (by decide) node_7180

theorem node_13475 : Outcome ⟨8, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 2⟩) (by decide) node_12469

theorem node_13476 : Outcome ⟨8, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 2⟩) (by decide) node_12469

theorem node_13477 : Outcome ⟨8, 15, 3, 8⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 2⟩) (by decide) node_12469

theorem node_13478 : Outcome ⟨8, 15, 3, 20⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 2⟩) (by decide) node_12469

theorem node_13479 : Outcome ⟨8, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 16, 0, 4⟩) (by decide) node_11550

theorem node_13480 : Outcome ⟨8, 16, 2, 4⟩ true :=
  Outcome.win (q := ⟨8, 16, 0, 4⟩) (by decide) node_11550

theorem node_13481 : Outcome ⟨8, 16, 2, 6⟩ true :=
  Outcome.win (q := ⟨8, 16, 0, 4⟩) (by decide) node_11550

theorem node_13482 : Outcome ⟨8, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨7, 17, 1, 2⟩) (by decide) node_12480

theorem node_13483 : Outcome ⟨8, 17, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 12⟩) (by decide) node_7193

theorem node_13484 : Outcome ⟨8, 17, 1, 10⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 12⟩) (by decide) node_7193

theorem node_13485 : Outcome ⟨8, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 16, 0, 4⟩) (by decide) node_11550

theorem node_13486 : Outcome ⟨8, 18, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 6⟩) (by decide) node_10331

theorem node_13487 : Outcome ⟨8, 18, 0, 16⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 20⟩) (by decide) node_4440

theorem node_13488 : Outcome ⟨9, 0, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 17, 2⟩, ⟨7, 0, 17, 4⟩, ⟨9, 0, 16, 2⟩, ⟨9, 0, 15, 4⟩]
  exact AllWinning.cons node_12486 (AllWinning.cons node_11430 (AllWinning.cons node_12545 (AllWinning.cons node_11554 (AllWinning.nil))))

theorem node_13489 : Outcome ⟨9, 0, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 17, 2⟩, ⟨7, 0, 17, 4⟩, ⟨6, 0, 17, 6⟩, ⟨5, 0, 17, 8⟩, ⟨9, 0, 16, 2⟩, ⟨9, 0, 15, 4⟩, ⟨9, 0, 14, 6⟩, ⟨9, 0, 13, 8⟩]
  exact AllWinning.cons node_12486 (AllWinning.cons node_11430 (AllWinning.cons node_10337 (AllWinning.cons node_9272 (AllWinning.cons node_12545 (AllWinning.cons node_11554 (AllWinning.cons node_10554 (AllWinning.cons node_9516 (AllWinning.nil))))))))

theorem node_13490 : Outcome ⟨9, 0, 17, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 10⟩) (by decide) node_8223

theorem node_13491 : Outcome ⟨9, 0, 17, 12⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 16⟩) (by decide) node_5827

theorem node_13492 : Outcome ⟨9, 0, 17, 16⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 16⟩) (by decide) node_5827

theorem node_13493 : Outcome ⟨9, 1, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 16, 2⟩, ⟨7, 1, 16, 4⟩, ⟨9, 0, 16, 2⟩, ⟨9, 1, 15, 2⟩, ⟨9, 1, 14, 4⟩]
  exact AllWinning.cons node_12489 (AllWinning.cons node_11435 (AllWinning.cons node_12545 (AllWinning.cons node_12549 (AllWinning.cons node_11557 (AllWinning.nil)))))

theorem node_13494 : Outcome ⟨9, 1, 16, 6⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 6⟩) (by decide) node_10341

theorem node_13495 : Outcome ⟨9, 1, 16, 12⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 22⟩) (by decide) node_3805

theorem node_13496 : Outcome ⟨9, 2, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 2, 15, 2⟩, ⟨7, 2, 15, 4⟩, ⟨6, 2, 15, 6⟩, ⟨5, 2, 15, 8⟩, ⟨9, 1, 15, 2⟩, ⟨9, 0, 15, 4⟩, ⟨9, 2, 14, 2⟩, ⟨9, 2, 13, 4⟩, ⟨9, 2, 12, 6⟩, ⟨9, 2, 11, 8⟩]
  exact AllWinning.cons node_12493 (AllWinning.cons node_11439 (AllWinning.cons node_10348 (AllWinning.cons node_9279 (AllWinning.cons node_12549 (AllWinning.cons node_11554 (AllWinning.cons node_12553 (AllWinning.cons node_11559 (AllWinning.cons node_10562 (AllWinning.cons node_9521 (AllWinning.nil))))))))))

end RQ9F1
