import Chunk61
set_option autoImplicit false
namespace RQ9F1

theorem node_14230 : Outcome ⟨5, 10, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 12, 2⟩, ⟨3, 10, 12, 4⟩, ⟨2, 10, 12, 6⟩, ⟨1, 10, 12, 8⟩, ⟨0, 10, 12, 10⟩, ⟨5, 9, 12, 2⟩, ⟨5, 8, 12, 4⟩, ⟨5, 7, 12, 6⟩, ⟨5, 6, 12, 8⟩, ⟨5, 5, 12, 10⟩, ⟨5, 4, 12, 12⟩, ⟨5, 3, 12, 14⟩, ⟨5, 2, 12, 16⟩, ⟨5, 10, 11, 2⟩, ⟨5, 10, 10, 4⟩, ⟨5, 10, 9, 6⟩, ⟨5, 10, 8, 8⟩, ⟨5, 10, 7, 10⟩, ⟨5, 10, 6, 12⟩, ⟨5, 10, 5, 14⟩, ⟨5, 10, 4, 16⟩]
  exact AllWinning.cons node_13217 (AllWinning.cons node_12182 (AllWinning.cons node_11115 (AllWinning.cons node_9974 (AllWinning.cons node_8937 (AllWinning.cons node_13264 (AllWinning.cons node_12303 (AllWinning.cons node_11319 (AllWinning.cons node_10275 (AllWinning.cons node_9289 (AllWinning.cons node_8301 (AllWinning.cons node_7364 (AllWinning.cons node_6430 (AllWinning.cons node_13267 (AllWinning.cons node_12309 (AllWinning.cons node_11332 (AllWinning.cons node_10295 (AllWinning.cons node_9309 (AllWinning.cons node_8323 (AllWinning.cons node_7390 (AllWinning.cons node_6464 (AllWinning.nil)))))))))))))))))))))

theorem node_14231 : Outcome ⟨5, 10, 12, 14⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 20⟩) (by decide) node_4977

theorem node_14232 : Outcome ⟨5, 10, 12, 16⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 20⟩) (by decide) node_4977

theorem node_14233 : Outcome ⟨5, 11, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 11, 2⟩, ⟨3, 11, 11, 4⟩, ⟨5, 10, 11, 2⟩, ⟨5, 9, 11, 4⟩, ⟨5, 11, 10, 2⟩, ⟨5, 11, 9, 4⟩]
  exact AllWinning.cons node_13220 (AllWinning.cons node_12184 (AllWinning.cons node_13267 (AllWinning.cons node_12306 (AllWinning.cons node_13270 (AllWinning.cons node_12312 (AllWinning.nil))))))

theorem node_14234 : Outcome ⟨5, 11, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 11, 2⟩, ⟨3, 11, 11, 4⟩, ⟨2, 11, 11, 6⟩, ⟨1, 11, 11, 8⟩, ⟨5, 10, 11, 2⟩, ⟨5, 9, 11, 4⟩, ⟨5, 8, 11, 6⟩, ⟨5, 7, 11, 8⟩, ⟨5, 11, 10, 2⟩, ⟨5, 11, 9, 4⟩, ⟨5, 11, 8, 6⟩, ⟨5, 11, 7, 8⟩]
  exact AllWinning.cons node_13220 (AllWinning.cons node_12184 (AllWinning.cons node_11119 (AllWinning.cons node_9978 (AllWinning.cons node_13267 (AllWinning.cons node_12306 (AllWinning.cons node_11324 (AllWinning.cons node_10280 (AllWinning.cons node_13270 (AllWinning.cons node_12312 (AllWinning.cons node_11336 (AllWinning.cons node_10301 (AllWinning.nil))))))))))))

theorem node_14235 : Outcome ⟨5, 11, 11, 8⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 16⟩) (by decide) node_6439

theorem node_14236 : Outcome ⟨5, 12, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 10, 2⟩, ⟨3, 12, 10, 4⟩, ⟨5, 11, 10, 2⟩, ⟨5, 10, 10, 4⟩, ⟨5, 12, 9, 2⟩, ⟨5, 12, 8, 4⟩]
  exact AllWinning.cons node_13223 (AllWinning.cons node_12189 (AllWinning.cons node_13270 (AllWinning.cons node_12309 (AllWinning.cons node_13273 (AllWinning.cons node_12316 (AllWinning.nil))))))

theorem node_14237 : Outcome ⟨5, 12, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 10, 2⟩, ⟨3, 12, 10, 4⟩, ⟨2, 12, 10, 6⟩, ⟨1, 12, 10, 8⟩, ⟨0, 12, 10, 10⟩, ⟨5, 11, 10, 2⟩, ⟨5, 10, 10, 4⟩, ⟨5, 9, 10, 6⟩, ⟨5, 8, 10, 8⟩, ⟨5, 7, 10, 10⟩, ⟨5, 6, 10, 12⟩, ⟨5, 12, 9, 2⟩, ⟨5, 12, 8, 4⟩, ⟨5, 12, 7, 6⟩, ⟨5, 12, 6, 8⟩, ⟨5, 12, 5, 10⟩, ⟨5, 12, 4, 12⟩]
  exact AllWinning.cons node_13223 (AllWinning.cons node_12189 (AllWinning.cons node_11123 (AllWinning.cons node_9982 (AllWinning.cons node_8949 (AllWinning.cons node_13270 (AllWinning.cons node_12309 (AllWinning.cons node_11328 (AllWinning.cons node_10285 (AllWinning.cons node_9296 (AllWinning.cons node_8309 (AllWinning.cons node_13273 (AllWinning.cons node_12316 (AllWinning.cons node_11341 (AllWinning.cons node_10305 (AllWinning.cons node_9317 (AllWinning.cons node_8327 (AllWinning.nil)))))))))))))))))

theorem node_14238 : Outcome ⟨5, 12, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 10, 2⟩, ⟨3, 12, 10, 4⟩, ⟨2, 12, 10, 6⟩, ⟨1, 12, 10, 8⟩, ⟨0, 12, 10, 10⟩, ⟨5, 11, 10, 2⟩, ⟨5, 10, 10, 4⟩, ⟨5, 9, 10, 6⟩, ⟨5, 8, 10, 8⟩, ⟨5, 7, 10, 10⟩, ⟨5, 6, 10, 12⟩, ⟨5, 5, 10, 14⟩, ⟨5, 4, 10, 16⟩, ⟨5, 12, 9, 2⟩, ⟨5, 12, 8, 4⟩, ⟨5, 12, 7, 6⟩, ⟨5, 12, 6, 8⟩, ⟨5, 12, 5, 10⟩, ⟨5, 12, 4, 12⟩, ⟨5, 12, 3, 14⟩, ⟨5, 12, 2, 16⟩]
  exact AllWinning.cons node_13223 (AllWinning.cons node_12189 (AllWinning.cons node_11123 (AllWinning.cons node_9982 (AllWinning.cons node_8949 (AllWinning.cons node_13270 (AllWinning.cons node_12309 (AllWinning.cons node_11328 (AllWinning.cons node_10285 (AllWinning.cons node_9296 (AllWinning.cons node_8309 (AllWinning.cons node_7370 (AllWinning.cons node_6445 (AllWinning.cons node_13273 (AllWinning.cons node_12316 (AllWinning.cons node_11341 (AllWinning.cons node_10305 (AllWinning.cons node_9317 (AllWinning.cons node_8327 (AllWinning.cons node_7396 (AllWinning.cons node_6477 (AllWinning.nil)))))))))))))))))))))

theorem node_14239 : Outcome ⟨5, 12, 10, 14⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 20⟩) (by decide) node_4939

theorem node_14240 : Outcome ⟨5, 12, 10, 16⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 20⟩) (by decide) node_4939

theorem node_14241 : Outcome ⟨5, 13, 9, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 9, 2⟩) (by decide) node_13226

theorem node_14242 : Outcome ⟨5, 13, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 8⟩) (by decide) node_10311

theorem node_14243 : Outcome ⟨5, 13, 9, 8⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 8⟩) (by decide) node_10311

theorem node_14244 : Outcome ⟨5, 14, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 13, 8, 2⟩) (by decide) node_13276

theorem node_14245 : Outcome ⟨5, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 4⟩) (by decide) node_12196

theorem node_14246 : Outcome ⟨5, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 4⟩) (by decide) node_12196

theorem node_14247 : Outcome ⟨5, 15, 7, 14⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 22⟩) (by decide) node_4246

theorem node_14248 : Outcome ⟨5, 16, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 16, 6, 2⟩, ⟨3, 16, 6, 4⟩, ⟨5, 15, 6, 2⟩, ⟨5, 14, 6, 4⟩, ⟨5, 16, 5, 2⟩, ⟨5, 16, 4, 4⟩]
  exact AllWinning.cons node_13232 (AllWinning.cons node_12203 (AllWinning.cons node_13280 (AllWinning.cons node_12321 (AllWinning.cons node_13283 (AllWinning.cons node_12326 (AllWinning.nil))))))

theorem node_14249 : Outcome ⟨5, 16, 6, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 8⟩) (by decide) node_10000

theorem node_14250 : Outcome ⟨5, 16, 6, 14⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 8⟩) (by decide) node_10000

theorem node_14251 : Outcome ⟨5, 17, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 5, 2⟩) (by decide) node_13235

theorem node_14252 : Outcome ⟨5, 17, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 8⟩) (by decide) node_10311

theorem node_14253 : Outcome ⟨5, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 4, 2⟩) (by decide) node_13238

theorem node_14254 : Outcome ⟨5, 18, 4, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 8⟩) (by decide) node_10332

theorem node_14255 : Outcome ⟨5, 18, 4, 12⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 22⟩) (by decide) node_4263

theorem node_14256 : Outcome ⟨5, 18, 4, 16⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 22⟩) (by decide) node_4263

theorem node_14257 : Outcome ⟨5, 19, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 19, 3, 2⟩, ⟨3, 19, 3, 4⟩, ⟨5, 18, 3, 2⟩, ⟨5, 17, 3, 4⟩, ⟨5, 19, 2, 2⟩, ⟨5, 19, 1, 4⟩]
  exact AllWinning.cons node_13241 (AllWinning.cons node_12214 (AllWinning.cons node_13287 (AllWinning.cons node_12329 (AllWinning.cons node_13291 (AllWinning.cons node_12336 (AllWinning.nil))))))

theorem node_14258 : Outcome ⟨5, 19, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 8⟩) (by decide) node_10017

theorem node_14259 : Outcome ⟨5, 19, 3, 12⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 16⟩) (by decide) node_6472

theorem node_14260 : Outcome ⟨5, 19, 3, 14⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 16⟩) (by decide) node_6472

theorem node_14261 : Outcome ⟨5, 20, 2, 4⟩ true :=
  Outcome.win (q := ⟨3, 20, 2, 4⟩) (by decide) node_12216

theorem node_14262 : Outcome ⟨5, 20, 2, 8⟩ true :=
  Outcome.win (q := ⟨3, 20, 2, 4⟩) (by decide) node_12216

theorem node_14263 : Outcome ⟨6, 1, 20, 8⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 8⟩) (by decide) node_10342

theorem node_14264 : Outcome ⟨6, 1, 20, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 8⟩) (by decide) node_10342

theorem node_14265 : Outcome ⟨6, 2, 19, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 19, 4⟩) (by decide) node_12224

theorem node_14266 : Outcome ⟨6, 2, 19, 10⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 16⟩) (by decide) node_6503

theorem node_14267 : Outcome ⟨6, 3, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 18, 2⟩, ⟨4, 3, 18, 4⟩, ⟨6, 2, 18, 2⟩, ⟨6, 1, 18, 4⟩, ⟨6, 3, 17, 2⟩, ⟨6, 3, 16, 4⟩]
  exact AllWinning.cons node_13249 (AllWinning.cons node_12228 (AllWinning.cons node_13299 (AllWinning.cons node_12349 (AllWinning.cons node_13302 (AllWinning.cons node_12356 (AllWinning.nil))))))

theorem node_14268 : Outcome ⟨6, 3, 18, 8⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 8⟩) (by decide) node_10353

theorem node_14269 : Outcome ⟨6, 3, 18, 14⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 8⟩) (by decide) node_10353

theorem node_14270 : Outcome ⟨6, 3, 18, 18⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 34⟩) (by decide) node_1491

theorem node_14271 : Outcome ⟨6, 4, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 2, 17, 4⟩) (by decide) node_12352

theorem node_14272 : Outcome ⟨6, 4, 17, 10⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 14⟩) (by decide) node_7432

theorem node_14273 : Outcome ⟨6, 5, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 5, 16, 2⟩, ⟨4, 5, 16, 4⟩, ⟨6, 4, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨6, 5, 15, 2⟩, ⟨6, 5, 14, 4⟩]
  exact AllWinning.cons node_13255 (AllWinning.cons node_12234 (AllWinning.cons node_13306 (AllWinning.cons node_12356 (AllWinning.cons node_13309 (AllWinning.cons node_12362 (AllWinning.nil))))))

theorem node_14274 : Outcome ⟨6, 5, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 8⟩) (by decide) node_10342

theorem node_14275 : Outcome ⟨6, 5, 16, 14⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 8⟩) (by decide) node_10342

theorem node_14276 : Outcome ⟨6, 6, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 6⟩) (by decide) node_11383

theorem node_14277 : Outcome ⟨6, 6, 15, 10⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 6⟩) (by decide) node_11383

theorem node_14278 : Outcome ⟨6, 7, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 4⟩) (by decide) node_12240

theorem node_14279 : Outcome ⟨6, 7, 14, 4⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 8⟩) (by decide) node_10353

theorem node_14280 : Outcome ⟨6, 7, 14, 8⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 12⟩) (by decide) node_8372

theorem node_14281 : Outcome ⟨6, 7, 14, 10⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 12⟩) (by decide) node_8372

theorem node_14282 : Outcome ⟨6, 7, 14, 12⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 12⟩) (by decide) node_8372

theorem node_14283 : Outcome ⟨6, 8, 13, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 13, 2⟩) (by decide) node_13262

theorem node_14284 : Outcome ⟨6, 8, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 13, 2⟩) (by decide) node_13262

theorem node_14285 : Outcome ⟨6, 8, 13, 12⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 12⟩) (by decide) node_8384

theorem node_14286 : Outcome ⟨6, 9, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 6⟩) (by decide) node_11174

theorem node_14287 : Outcome ⟨6, 9, 12, 10⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 6⟩) (by decide) node_11174

theorem node_14288 : Outcome ⟨6, 9, 12, 14⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 6⟩) (by decide) node_11174

theorem node_14289 : Outcome ⟨6, 10, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 4⟩) (by decide) node_12247

theorem node_14290 : Outcome ⟨6, 10, 11, 10⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 16⟩) (by decide) node_6503

theorem node_14291 : Outcome ⟨6, 10, 11, 14⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 16⟩) (by decide) node_6503

theorem node_14292 : Outcome ⟨6, 11, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 11, 10, 4⟩) (by decide) node_12251

theorem node_14293 : Outcome ⟨6, 11, 10, 10⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 16⟩) (by decide) node_6537

theorem node_14294 : Outcome ⟨6, 11, 10, 14⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 16⟩) (by decide) node_6537

theorem node_14295 : Outcome ⟨6, 12, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 6⟩) (by decide) node_11195

theorem node_14296 : Outcome ⟨6, 12, 9, 10⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 6⟩) (by decide) node_11195

theorem node_14297 : Outcome ⟨6, 12, 9, 14⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 6⟩) (by decide) node_11195

theorem node_14298 : Outcome ⟨6, 13, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 13, 8, 2⟩) (by decide) node_13276

theorem node_14299 : Outcome ⟨6, 13, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 8, 2⟩) (by decide) node_13276

theorem node_14300 : Outcome ⟨6, 13, 8, 12⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 12⟩) (by decide) node_8372

theorem node_14301 : Outcome ⟨6, 14, 7, 2⟩ true :=
  Outcome.win (q := ⟨4, 14, 7, 4⟩) (by decide) node_12259

theorem node_14302 : Outcome ⟨6, 14, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 8⟩) (by decide) node_10399

theorem node_14303 : Outcome ⟨6, 14, 7, 8⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 12⟩) (by decide) node_8384

theorem node_14304 : Outcome ⟨6, 14, 7, 10⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 12⟩) (by decide) node_8384

theorem node_14305 : Outcome ⟨6, 14, 7, 12⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 12⟩) (by decide) node_8384

theorem node_14306 : Outcome ⟨6, 15, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 6⟩) (by decide) node_11408

theorem node_14307 : Outcome ⟨6, 15, 6, 10⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 6⟩) (by decide) node_11408

theorem node_14308 : Outcome ⟨6, 16, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 5, 2⟩, ⟨4, 16, 5, 4⟩, ⟨6, 15, 5, 2⟩, ⟨6, 14, 5, 4⟩, ⟨6, 16, 4, 2⟩, ⟨6, 16, 3, 4⟩]
  exact AllWinning.cons node_13283 (AllWinning.cons node_12265 (AllWinning.cons node_13345 (AllWinning.cons node_12397 (AllWinning.cons node_13348 (AllWinning.cons node_12403 (AllWinning.nil))))))

theorem node_14309 : Outcome ⟨6, 16, 5, 4⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 8⟩) (by decide) node_10408

theorem node_14310 : Outcome ⟨6, 16, 5, 14⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 8⟩) (by decide) node_10408

theorem node_14311 : Outcome ⟨6, 17, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 4, 4⟩) (by decide) node_12401

theorem node_14312 : Outcome ⟨6, 17, 4, 10⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 14⟩) (by decide) node_7461

theorem node_14313 : Outcome ⟨6, 18, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 3, 2⟩, ⟨4, 18, 3, 4⟩, ⟨6, 17, 3, 2⟩, ⟨6, 16, 3, 4⟩, ⟨6, 18, 2, 2⟩, ⟨6, 18, 1, 4⟩]
  exact AllWinning.cons node_13287 (AllWinning.cons node_12270 (AllWinning.cons node_13351 (AllWinning.cons node_12403 (AllWinning.cons node_13355 (AllWinning.cons node_12411 (AllWinning.nil))))))

theorem node_14314 : Outcome ⟨6, 18, 3, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 8⟩) (by decide) node_10399

theorem node_14315 : Outcome ⟨6, 18, 3, 14⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 8⟩) (by decide) node_10399

theorem node_14316 : Outcome ⟨6, 18, 3, 18⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 34⟩) (by decide) node_1471

theorem node_14317 : Outcome ⟨6, 19, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 19, 2, 4⟩) (by decide) node_12274

theorem node_14318 : Outcome ⟨6, 19, 2, 10⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 16⟩) (by decide) node_6537

theorem node_14319 : Outcome ⟨6, 20, 1, 8⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 8⟩) (by decide) node_10408

theorem node_14320 : Outcome ⟨6, 20, 1, 10⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 8⟩) (by decide) node_10408

theorem node_14321 : Outcome ⟨7, 0, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 20, 2⟩, ⟨5, 0, 20, 4⟩, ⟨7, 0, 19, 2⟩, ⟨7, 0, 18, 4⟩]
  exact AllWinning.cons node_13295 (AllWinning.cons node_12279 (AllWinning.cons node_13362 (AllWinning.cons node_12420 (AllWinning.nil))))

theorem node_14322 : Outcome ⟨7, 0, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 20, 2⟩, ⟨5, 0, 20, 4⟩, ⟨4, 0, 20, 6⟩, ⟨3, 0, 20, 8⟩, ⟨7, 0, 19, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 0, 17, 6⟩, ⟨7, 0, 16, 8⟩]
  exact AllWinning.cons node_13295 (AllWinning.cons node_12279 (AllWinning.cons node_11227 (AllWinning.cons node_10088 (AllWinning.cons node_13362 (AllWinning.cons node_12420 (AllWinning.cons node_11431 (AllWinning.cons node_10417 (AllWinning.nil))))))))

theorem node_14323 : Outcome ⟨7, 0, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 20, 2⟩, ⟨5, 0, 20, 4⟩, ⟨4, 0, 20, 6⟩, ⟨3, 0, 20, 8⟩, ⟨2, 0, 20, 10⟩, ⟨1, 0, 20, 12⟩, ⟨7, 0, 19, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 0, 17, 6⟩, ⟨7, 0, 16, 8⟩, ⟨7, 0, 15, 10⟩, ⟨7, 0, 14, 12⟩]
  exact AllWinning.cons node_13295 (AllWinning.cons node_12279 (AllWinning.cons node_11227 (AllWinning.cons node_10088 (AllWinning.cons node_9048 (AllWinning.cons node_7980 (AllWinning.cons node_13362 (AllWinning.cons node_12420 (AllWinning.cons node_11431 (AllWinning.cons node_10417 (AllWinning.cons node_9407 (AllWinning.cons node_8418 (AllWinning.nil))))))))))))

theorem node_14324 : Outcome ⟨7, 0, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 20, 2⟩, ⟨5, 0, 20, 4⟩, ⟨4, 0, 20, 6⟩, ⟨3, 0, 20, 8⟩, ⟨2, 0, 20, 10⟩, ⟨1, 0, 20, 12⟩, ⟨0, 0, 20, 14⟩, ⟨7, 0, 19, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 0, 17, 6⟩, ⟨7, 0, 16, 8⟩, ⟨7, 0, 15, 10⟩, ⟨7, 0, 14, 12⟩, ⟨7, 0, 13, 14⟩, ⟨7, 0, 12, 16⟩]
  exact AllWinning.cons node_13295 (AllWinning.cons node_12279 (AllWinning.cons node_11227 (AllWinning.cons node_10088 (AllWinning.cons node_9048 (AllWinning.cons node_7980 (AllWinning.cons node_6946 (AllWinning.cons node_13362 (AllWinning.cons node_12420 (AllWinning.cons node_11431 (AllWinning.cons node_10417 (AllWinning.cons node_9407 (AllWinning.cons node_8418 (AllWinning.cons node_7486 (AllWinning.cons node_6554 (AllWinning.nil)))))))))))))))

theorem node_14325 : Outcome ⟨7, 0, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 20, 2⟩, ⟨5, 0, 20, 4⟩, ⟨4, 0, 20, 6⟩, ⟨3, 0, 20, 8⟩, ⟨2, 0, 20, 10⟩, ⟨1, 0, 20, 12⟩, ⟨0, 0, 20, 14⟩, ⟨7, 0, 19, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 0, 17, 6⟩, ⟨7, 0, 16, 8⟩, ⟨7, 0, 15, 10⟩, ⟨7, 0, 14, 12⟩, ⟨7, 0, 13, 14⟩, ⟨7, 0, 12, 16⟩, ⟨7, 0, 11, 18⟩, ⟨7, 0, 10, 20⟩]
  exact AllWinning.cons node_13295 (AllWinning.cons node_12279 (AllWinning.cons node_11227 (AllWinning.cons node_10088 (AllWinning.cons node_9048 (AllWinning.cons node_7980 (AllWinning.cons node_6946 (AllWinning.cons node_13362 (AllWinning.cons node_12420 (AllWinning.cons node_11431 (AllWinning.cons node_10417 (AllWinning.cons node_9407 (AllWinning.cons node_8418 (AllWinning.cons node_7486 (AllWinning.cons node_6554 (AllWinning.cons node_5731 (AllWinning.cons node_5033 (AllWinning.nil)))))))))))))))))

theorem node_14326 : Outcome ⟨7, 0, 20, 16⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 26⟩) (by decide) node_3173

theorem node_14327 : Outcome ⟨7, 1, 19, 4⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 8⟩) (by decide) node_10092

theorem node_14328 : Outcome ⟨7, 1, 19, 10⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 16⟩) (by decide) node_6563

theorem node_14329 : Outcome ⟨7, 2, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 18, 2⟩, ⟨5, 2, 18, 4⟩, ⟨7, 1, 18, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 2, 17, 2⟩, ⟨7, 2, 16, 4⟩]
  exact AllWinning.cons node_13299 (AllWinning.cons node_12285 (AllWinning.cons node_13366 (AllWinning.cons node_12420 (AllWinning.cons node_13367 (AllWinning.cons node_12426 (AllWinning.nil))))))

theorem node_14330 : Outcome ⟨7, 2, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 18, 2⟩, ⟨5, 2, 18, 4⟩, ⟨4, 2, 18, 6⟩, ⟨3, 2, 18, 8⟩, ⟨7, 1, 18, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 2, 17, 2⟩, ⟨7, 2, 16, 4⟩, ⟨7, 2, 15, 6⟩, ⟨7, 2, 14, 8⟩]
  exact AllWinning.cons node_13299 (AllWinning.cons node_12285 (AllWinning.cons node_11233 (AllWinning.cons node_10098 (AllWinning.cons node_13366 (AllWinning.cons node_12420 (AllWinning.cons node_13367 (AllWinning.cons node_12426 (AllWinning.cons node_11440 (AllWinning.cons node_10426 (AllWinning.nil))))))))))

theorem node_14331 : Outcome ⟨7, 2, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 18, 2⟩, ⟨5, 2, 18, 4⟩, ⟨4, 2, 18, 6⟩, ⟨3, 2, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨1, 2, 18, 12⟩, ⟨7, 1, 18, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 2, 17, 2⟩, ⟨7, 2, 16, 4⟩, ⟨7, 2, 15, 6⟩, ⟨7, 2, 14, 8⟩, ⟨7, 2, 13, 10⟩, ⟨7, 2, 12, 12⟩]
  exact AllWinning.cons node_13299 (AllWinning.cons node_12285 (AllWinning.cons node_11233 (AllWinning.cons node_10098 (AllWinning.cons node_9054 (AllWinning.cons node_7983 (AllWinning.cons node_13366 (AllWinning.cons node_12420 (AllWinning.cons node_13367 (AllWinning.cons node_12426 (AllWinning.cons node_11440 (AllWinning.cons node_10426 (AllWinning.cons node_9413 (AllWinning.cons node_8429 (AllWinning.nil))))))))))))))

theorem node_14332 : Outcome ⟨7, 2, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 18, 2⟩, ⟨5, 2, 18, 4⟩, ⟨4, 2, 18, 6⟩, ⟨3, 2, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨1, 2, 18, 12⟩, ⟨0, 2, 18, 14⟩, ⟨7, 1, 18, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 2, 17, 2⟩, ⟨7, 2, 16, 4⟩, ⟨7, 2, 15, 6⟩, ⟨7, 2, 14, 8⟩, ⟨7, 2, 13, 10⟩, ⟨7, 2, 12, 12⟩, ⟨7, 2, 11, 14⟩, ⟨7, 2, 10, 16⟩]
  exact AllWinning.cons node_13299 (AllWinning.cons node_12285 (AllWinning.cons node_11233 (AllWinning.cons node_10098 (AllWinning.cons node_9054 (AllWinning.cons node_7983 (AllWinning.cons node_6953 (AllWinning.cons node_13366 (AllWinning.cons node_12420 (AllWinning.cons node_13367 (AllWinning.cons node_12426 (AllWinning.cons node_11440 (AllWinning.cons node_10426 (AllWinning.cons node_9413 (AllWinning.cons node_8429 (AllWinning.cons node_7494 (AllWinning.cons node_6571 (AllWinning.nil)))))))))))))))))

theorem node_14333 : Outcome ⟨7, 2, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 18, 2⟩, ⟨5, 2, 18, 4⟩, ⟨4, 2, 18, 6⟩, ⟨3, 2, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨1, 2, 18, 12⟩, ⟨0, 2, 18, 14⟩, ⟨7, 1, 18, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 2, 17, 2⟩, ⟨7, 2, 16, 4⟩, ⟨7, 2, 15, 6⟩, ⟨7, 2, 14, 8⟩, ⟨7, 2, 13, 10⟩, ⟨7, 2, 12, 12⟩, ⟨7, 2, 11, 14⟩, ⟨7, 2, 10, 16⟩, ⟨7, 2, 9, 18⟩, ⟨7, 2, 8, 20⟩]
  exact AllWinning.cons node_13299 (AllWinning.cons node_12285 (AllWinning.cons node_11233 (AllWinning.cons node_10098 (AllWinning.cons node_9054 (AllWinning.cons node_7983 (AllWinning.cons node_6953 (AllWinning.cons node_13366 (AllWinning.cons node_12420 (AllWinning.cons node_13367 (AllWinning.cons node_12426 (AllWinning.cons node_11440 (AllWinning.cons node_10426 (AllWinning.cons node_9413 (AllWinning.cons node_8429 (AllWinning.cons node_7494 (AllWinning.cons node_6571 (AllWinning.cons node_5738 (AllWinning.cons node_5042 (AllWinning.nil)))))))))))))))))))

theorem node_14334 : Outcome ⟨7, 2, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 18, 2⟩, ⟨5, 2, 18, 4⟩, ⟨4, 2, 18, 6⟩, ⟨3, 2, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨1, 2, 18, 12⟩, ⟨0, 2, 18, 14⟩, ⟨7, 1, 18, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 2, 17, 2⟩, ⟨7, 2, 16, 4⟩, ⟨7, 2, 15, 6⟩, ⟨7, 2, 14, 8⟩, ⟨7, 2, 13, 10⟩, ⟨7, 2, 12, 12⟩, ⟨7, 2, 11, 14⟩, ⟨7, 2, 10, 16⟩, ⟨7, 2, 9, 18⟩, ⟨7, 2, 8, 20⟩, ⟨7, 2, 7, 22⟩, ⟨7, 2, 6, 24⟩]
  exact AllWinning.cons node_13299 (AllWinning.cons node_12285 (AllWinning.cons node_11233 (AllWinning.cons node_10098 (AllWinning.cons node_9054 (AllWinning.cons node_7983 (AllWinning.cons node_6953 (AllWinning.cons node_13366 (AllWinning.cons node_12420 (AllWinning.cons node_13367 (AllWinning.cons node_12426 (AllWinning.cons node_11440 (AllWinning.cons node_10426 (AllWinning.cons node_9413 (AllWinning.cons node_8429 (AllWinning.cons node_7494 (AllWinning.cons node_6571 (AllWinning.cons node_5738 (AllWinning.cons node_5042 (AllWinning.cons node_4336 (AllWinning.cons node_3736 (AllWinning.nil)))))))))))))))))))))

theorem node_14335 : Outcome ⟨7, 2, 18, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 18, 2⟩, ⟨5, 2, 18, 4⟩, ⟨4, 2, 18, 6⟩, ⟨3, 2, 18, 8⟩, ⟨2, 2, 18, 10⟩, ⟨1, 2, 18, 12⟩, ⟨0, 2, 18, 14⟩, ⟨7, 1, 18, 2⟩, ⟨7, 0, 18, 4⟩, ⟨7, 2, 17, 2⟩, ⟨7, 2, 16, 4⟩, ⟨7, 2, 15, 6⟩, ⟨7, 2, 14, 8⟩, ⟨7, 2, 13, 10⟩, ⟨7, 2, 12, 12⟩, ⟨7, 2, 11, 14⟩, ⟨7, 2, 10, 16⟩, ⟨7, 2, 9, 18⟩, ⟨7, 2, 8, 20⟩, ⟨7, 2, 7, 22⟩, ⟨7, 2, 6, 24⟩, ⟨7, 2, 5, 26⟩, ⟨7, 2, 4, 28⟩]
  exact AllWinning.cons node_13299 (AllWinning.cons node_12285 (AllWinning.cons node_11233 (AllWinning.cons node_10098 (AllWinning.cons node_9054 (AllWinning.cons node_7983 (AllWinning.cons node_6953 (AllWinning.cons node_13366 (AllWinning.cons node_12420 (AllWinning.cons node_13367 (AllWinning.cons node_12426 (AllWinning.cons node_11440 (AllWinning.cons node_10426 (AllWinning.cons node_9413 (AllWinning.cons node_8429 (AllWinning.cons node_7494 (AllWinning.cons node_6571 (AllWinning.cons node_5738 (AllWinning.cons node_5042 (AllWinning.cons node_4336 (AllWinning.cons node_3736 (AllWinning.cons node_3182 (AllWinning.cons node_2704 (AllWinning.nil)))))))))))))))))))))))

theorem node_14336 : Outcome ⟨7, 2, 18, 18⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 30⟩) (by decide) node_2263

theorem node_14337 : Outcome ⟨7, 3, 17, 4⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 4⟩) (by decide) node_12423

theorem node_14338 : Outcome ⟨7, 3, 17, 14⟩ true :=
  Outcome.win (q := ⟨7, 1, 17, 4⟩) (by decide) node_12423

theorem node_14339 : Outcome ⟨7, 4, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 4⟩) (by decide) node_12438

theorem node_14340 : Outcome ⟨7, 4, 16, 14⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 22⟩) (by decide) node_4353

theorem node_14341 : Outcome ⟨7, 5, 15, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 4⟩) (by decide) node_12431

theorem node_14342 : Outcome ⟨7, 5, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 4⟩) (by decide) node_12431

theorem node_14343 : Outcome ⟨7, 5, 15, 14⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 22⟩) (by decide) node_4368

theorem node_14344 : Outcome ⟨7, 6, 14, 2⟩ true :=
  Outcome.win (q := ⟨7, 4, 14, 4⟩) (by decide) node_12438

theorem node_14345 : Outcome ⟨7, 6, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 8⟩) (by decide) node_10112

theorem node_14346 : Outcome ⟨7, 6, 14, 8⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 12⟩) (by decide) node_8448

theorem node_14347 : Outcome ⟨7, 6, 14, 10⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 12⟩) (by decide) node_8448

theorem node_14348 : Outcome ⟨7, 6, 14, 12⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 12⟩) (by decide) node_8448

theorem node_14349 : Outcome ⟨7, 7, 13, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 13, 2⟩) (by decide) node_13316

theorem node_14350 : Outcome ⟨7, 8, 12, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 2⟩) (by decide) node_13381

theorem node_14351 : Outcome ⟨7, 8, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 12⟩) (by decide) node_8010

theorem node_14352 : Outcome ⟨7, 8, 12, 14⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 12⟩) (by decide) node_8010

theorem node_14353 : Outcome ⟨7, 8, 12, 16⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 12⟩) (by decide) node_8010

theorem node_14354 : Outcome ⟨7, 9, 11, 4⟩ true :=
  Outcome.win (q := ⟨7, 8, 11, 2⟩) (by decide) node_13387

theorem node_14355 : Outcome ⟨7, 9, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 16⟩) (by decide) node_6563

theorem node_14356 : Outcome ⟨7, 9, 11, 14⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 16⟩) (by decide) node_6563

theorem node_14357 : Outcome ⟨7, 10, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 10, 10, 2⟩, ⟨5, 10, 10, 4⟩, ⟨7, 9, 10, 2⟩, ⟨7, 8, 10, 4⟩, ⟨7, 10, 9, 2⟩, ⟨7, 10, 8, 4⟩]
  exact AllWinning.cons node_13327 (AllWinning.cons node_12309 (AllWinning.cons node_13392 (AllWinning.cons node_12449 (AllWinning.cons node_13394 (AllWinning.cons node_12455 (AllWinning.nil))))))

theorem node_14358 : Outcome ⟨7, 10, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 10, 10, 2⟩, ⟨5, 10, 10, 4⟩, ⟨4, 10, 10, 6⟩, ⟨3, 10, 10, 8⟩, ⟨7, 9, 10, 2⟩, ⟨7, 8, 10, 4⟩, ⟨7, 7, 10, 6⟩, ⟨7, 6, 10, 8⟩, ⟨7, 10, 9, 2⟩, ⟨7, 10, 8, 4⟩, ⟨7, 10, 7, 6⟩, ⟨7, 10, 6, 8⟩]
  exact AllWinning.cons node_13327 (AllWinning.cons node_12309 (AllWinning.cons node_11262 (AllWinning.cons node_10128 (AllWinning.cons node_13392 (AllWinning.cons node_12449 (AllWinning.cons node_11458 (AllWinning.cons node_10445 (AllWinning.cons node_13394 (AllWinning.cons node_12455 (AllWinning.cons node_11468 (AllWinning.cons node_10462 (AllWinning.nil))))))))))))

theorem node_14359 : Outcome ⟨7, 10, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 10, 10, 2⟩, ⟨5, 10, 10, 4⟩, ⟨4, 10, 10, 6⟩, ⟨3, 10, 10, 8⟩, ⟨2, 10, 10, 10⟩, ⟨1, 10, 10, 12⟩, ⟨7, 9, 10, 2⟩, ⟨7, 8, 10, 4⟩, ⟨7, 7, 10, 6⟩, ⟨7, 6, 10, 8⟩, ⟨7, 5, 10, 10⟩, ⟨7, 4, 10, 12⟩, ⟨7, 10, 9, 2⟩, ⟨7, 10, 8, 4⟩, ⟨7, 10, 7, 6⟩, ⟨7, 10, 6, 8⟩, ⟨7, 10, 5, 10⟩, ⟨7, 10, 4, 12⟩]
  exact AllWinning.cons node_13327 (AllWinning.cons node_12309 (AllWinning.cons node_11262 (AllWinning.cons node_10128 (AllWinning.cons node_9085 (AllWinning.cons node_8022 (AllWinning.cons node_13392 (AllWinning.cons node_12449 (AllWinning.cons node_11458 (AllWinning.cons node_10445 (AllWinning.cons node_9426 (AllWinning.cons node_8439 (AllWinning.cons node_13394 (AllWinning.cons node_12455 (AllWinning.cons node_11468 (AllWinning.cons node_10462 (AllWinning.cons node_9444 (AllWinning.cons node_8477 (AllWinning.nil))))))))))))))))))

theorem node_14360 : Outcome ⟨7, 10, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 14⟩) (by decide) node_6986

theorem node_14361 : Outcome ⟨7, 10, 10, 12⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 14⟩) (by decide) node_6986

theorem node_14362 : Outcome ⟨7, 10, 10, 20⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 14⟩) (by decide) node_6986

theorem node_14363 : Outcome ⟨7, 11, 9, 4⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 2⟩) (by decide) node_13396

theorem node_14364 : Outcome ⟨7, 11, 9, 8⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 16⟩) (by decide) node_6610

theorem node_14365 : Outcome ⟨7, 11, 9, 14⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 16⟩) (by decide) node_6610

theorem node_14366 : Outcome ⟨7, 12, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 2⟩) (by decide) node_13396

theorem node_14367 : Outcome ⟨7, 12, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 12⟩) (by decide) node_8031

theorem node_14368 : Outcome ⟨7, 12, 8, 14⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 12⟩) (by decide) node_8031

theorem node_14369 : Outcome ⟨7, 12, 8, 16⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 12⟩) (by decide) node_8031

theorem node_14370 : Outcome ⟨7, 13, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 13, 7, 2⟩) (by decide) node_13336

theorem node_14371 : Outcome ⟨7, 14, 6, 2⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 4⟩) (by decide) node_12467

theorem node_14372 : Outcome ⟨7, 14, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 8⟩) (by decide) node_10143

theorem node_14373 : Outcome ⟨7, 14, 6, 8⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 12⟩) (by decide) node_8464

theorem node_14374 : Outcome ⟨7, 14, 6, 10⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 12⟩) (by decide) node_8464

theorem node_14375 : Outcome ⟨7, 14, 6, 12⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 12⟩) (by decide) node_8464

theorem node_14376 : Outcome ⟨7, 15, 5, 2⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 4⟩) (by decide) node_12470

theorem node_14377 : Outcome ⟨7, 15, 5, 4⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 4⟩) (by decide) node_12470

theorem node_14378 : Outcome ⟨7, 15, 5, 14⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 22⟩) (by decide) node_4353

theorem node_14379 : Outcome ⟨7, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨7, 14, 4, 4⟩) (by decide) node_12467

theorem node_14380 : Outcome ⟨7, 16, 4, 14⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 22⟩) (by decide) node_4368

theorem node_14381 : Outcome ⟨7, 17, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 4⟩) (by decide) node_12470

theorem node_14382 : Outcome ⟨7, 17, 3, 14⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 4⟩) (by decide) node_12470

theorem node_14383 : Outcome ⟨7, 18, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 2, 2⟩, ⟨5, 18, 2, 4⟩, ⟨7, 17, 2, 2⟩, ⟨7, 16, 2, 4⟩, ⟨7, 18, 1, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13355 (AllWinning.cons node_12332 (AllWinning.cons node_13418 (AllWinning.cons node_12476 (AllWinning.cons node_13421 (AllWinning.cons node_12484 (AllWinning.nil))))))

theorem node_14384 : Outcome ⟨7, 18, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 2, 2⟩, ⟨5, 18, 2, 4⟩, ⟨4, 18, 2, 6⟩, ⟨3, 18, 2, 8⟩, ⟨7, 17, 2, 2⟩, ⟨7, 16, 2, 4⟩, ⟨7, 15, 2, 6⟩, ⟨7, 14, 2, 8⟩, ⟨7, 18, 1, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13355 (AllWinning.cons node_12332 (AllWinning.cons node_11290 (AllWinning.cons node_10158 (AllWinning.cons node_13418 (AllWinning.cons node_12476 (AllWinning.cons node_11486 (AllWinning.cons node_10481 (AllWinning.cons node_13421 (AllWinning.cons node_12484 (AllWinning.nil))))))))))

theorem node_14385 : Outcome ⟨7, 18, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 2, 2⟩, ⟨5, 18, 2, 4⟩, ⟨4, 18, 2, 6⟩, ⟨3, 18, 2, 8⟩, ⟨2, 18, 2, 10⟩, ⟨1, 18, 2, 12⟩, ⟨7, 17, 2, 2⟩, ⟨7, 16, 2, 4⟩, ⟨7, 15, 2, 6⟩, ⟨7, 14, 2, 8⟩, ⟨7, 13, 2, 10⟩, ⟨7, 12, 2, 12⟩, ⟨7, 18, 1, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13355 (AllWinning.cons node_12332 (AllWinning.cons node_11290 (AllWinning.cons node_10158 (AllWinning.cons node_9116 (AllWinning.cons node_8059 (AllWinning.cons node_13418 (AllWinning.cons node_12476 (AllWinning.cons node_11486 (AllWinning.cons node_10481 (AllWinning.cons node_9459 (AllWinning.cons node_8487 (AllWinning.cons node_13421 (AllWinning.cons node_12484 (AllWinning.nil))))))))))))))

theorem node_14386 : Outcome ⟨7, 18, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 2, 2⟩, ⟨5, 18, 2, 4⟩, ⟨4, 18, 2, 6⟩, ⟨3, 18, 2, 8⟩, ⟨2, 18, 2, 10⟩, ⟨1, 18, 2, 12⟩, ⟨0, 18, 2, 14⟩, ⟨7, 17, 2, 2⟩, ⟨7, 16, 2, 4⟩, ⟨7, 15, 2, 6⟩, ⟨7, 14, 2, 8⟩, ⟨7, 13, 2, 10⟩, ⟨7, 12, 2, 12⟩, ⟨7, 11, 2, 14⟩, ⟨7, 10, 2, 16⟩, ⟨7, 18, 1, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13355 (AllWinning.cons node_12332 (AllWinning.cons node_11290 (AllWinning.cons node_10158 (AllWinning.cons node_9116 (AllWinning.cons node_8059 (AllWinning.cons node_7019 (AllWinning.cons node_13418 (AllWinning.cons node_12476 (AllWinning.cons node_11486 (AllWinning.cons node_10481 (AllWinning.cons node_9459 (AllWinning.cons node_8487 (AllWinning.cons node_7528 (AllWinning.cons node_6601 (AllWinning.cons node_13421 (AllWinning.cons node_12484 (AllWinning.nil)))))))))))))))))

theorem node_14387 : Outcome ⟨7, 18, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 2, 2⟩, ⟨5, 18, 2, 4⟩, ⟨4, 18, 2, 6⟩, ⟨3, 18, 2, 8⟩, ⟨2, 18, 2, 10⟩, ⟨1, 18, 2, 12⟩, ⟨0, 18, 2, 14⟩, ⟨7, 17, 2, 2⟩, ⟨7, 16, 2, 4⟩, ⟨7, 15, 2, 6⟩, ⟨7, 14, 2, 8⟩, ⟨7, 13, 2, 10⟩, ⟨7, 12, 2, 12⟩, ⟨7, 11, 2, 14⟩, ⟨7, 10, 2, 16⟩, ⟨7, 9, 2, 18⟩, ⟨7, 8, 2, 20⟩, ⟨7, 18, 1, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13355 (AllWinning.cons node_12332 (AllWinning.cons node_11290 (AllWinning.cons node_10158 (AllWinning.cons node_9116 (AllWinning.cons node_8059 (AllWinning.cons node_7019 (AllWinning.cons node_13418 (AllWinning.cons node_12476 (AllWinning.cons node_11486 (AllWinning.cons node_10481 (AllWinning.cons node_9459 (AllWinning.cons node_8487 (AllWinning.cons node_7528 (AllWinning.cons node_6601 (AllWinning.cons node_5767 (AllWinning.cons node_5066 (AllWinning.cons node_13421 (AllWinning.cons node_12484 (AllWinning.nil)))))))))))))))))))

theorem node_14388 : Outcome ⟨7, 18, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 2, 2⟩, ⟨5, 18, 2, 4⟩, ⟨4, 18, 2, 6⟩, ⟨3, 18, 2, 8⟩, ⟨2, 18, 2, 10⟩, ⟨1, 18, 2, 12⟩, ⟨0, 18, 2, 14⟩, ⟨7, 17, 2, 2⟩, ⟨7, 16, 2, 4⟩, ⟨7, 15, 2, 6⟩, ⟨7, 14, 2, 8⟩, ⟨7, 13, 2, 10⟩, ⟨7, 12, 2, 12⟩, ⟨7, 11, 2, 14⟩, ⟨7, 10, 2, 16⟩, ⟨7, 9, 2, 18⟩, ⟨7, 8, 2, 20⟩, ⟨7, 7, 2, 22⟩, ⟨7, 6, 2, 24⟩, ⟨7, 18, 1, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13355 (AllWinning.cons node_12332 (AllWinning.cons node_11290 (AllWinning.cons node_10158 (AllWinning.cons node_9116 (AllWinning.cons node_8059 (AllWinning.cons node_7019 (AllWinning.cons node_13418 (AllWinning.cons node_12476 (AllWinning.cons node_11486 (AllWinning.cons node_10481 (AllWinning.cons node_9459 (AllWinning.cons node_8487 (AllWinning.cons node_7528 (AllWinning.cons node_6601 (AllWinning.cons node_5767 (AllWinning.cons node_5066 (AllWinning.cons node_4382 (AllWinning.cons node_3753 (AllWinning.cons node_13421 (AllWinning.cons node_12484 (AllWinning.nil)))))))))))))))))))))

theorem node_14389 : Outcome ⟨7, 18, 2, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 18, 2, 2⟩, ⟨5, 18, 2, 4⟩, ⟨4, 18, 2, 6⟩, ⟨3, 18, 2, 8⟩, ⟨2, 18, 2, 10⟩, ⟨1, 18, 2, 12⟩, ⟨0, 18, 2, 14⟩, ⟨7, 17, 2, 2⟩, ⟨7, 16, 2, 4⟩, ⟨7, 15, 2, 6⟩, ⟨7, 14, 2, 8⟩, ⟨7, 13, 2, 10⟩, ⟨7, 12, 2, 12⟩, ⟨7, 11, 2, 14⟩, ⟨7, 10, 2, 16⟩, ⟨7, 9, 2, 18⟩, ⟨7, 8, 2, 20⟩, ⟨7, 7, 2, 22⟩, ⟨7, 6, 2, 24⟩, ⟨7, 5, 2, 26⟩, ⟨7, 4, 2, 28⟩, ⟨7, 18, 1, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13355 (AllWinning.cons node_12332 (AllWinning.cons node_11290 (AllWinning.cons node_10158 (AllWinning.cons node_9116 (AllWinning.cons node_8059 (AllWinning.cons node_7019 (AllWinning.cons node_13418 (AllWinning.cons node_12476 (AllWinning.cons node_11486 (AllWinning.cons node_10481 (AllWinning.cons node_9459 (AllWinning.cons node_8487 (AllWinning.cons node_7528 (AllWinning.cons node_6601 (AllWinning.cons node_5767 (AllWinning.cons node_5066 (AllWinning.cons node_4382 (AllWinning.cons node_3753 (AllWinning.cons node_3193 (AllWinning.cons node_2713 (AllWinning.cons node_13421 (AllWinning.cons node_12484 (AllWinning.nil)))))))))))))))))))))))

theorem node_14390 : Outcome ⟨7, 18, 2, 18⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 30⟩) (by decide) node_2279

theorem node_14391 : Outcome ⟨7, 19, 1, 4⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 8⟩) (by decide) node_10163

theorem node_14392 : Outcome ⟨7, 19, 1, 10⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 16⟩) (by decide) node_6610

theorem node_14393 : Outcome ⟨7, 20, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 0, 2⟩, ⟨5, 20, 0, 4⟩, ⟨7, 19, 0, 2⟩, ⟨7, 18, 0, 4⟩]
  exact AllWinning.cons node_13360 (AllWinning.cons node_12340 (AllWinning.cons node_13422 (AllWinning.cons node_12484 (AllWinning.nil))))

theorem node_14394 : Outcome ⟨7, 20, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 0, 2⟩, ⟨5, 20, 0, 4⟩, ⟨4, 20, 0, 6⟩, ⟨3, 20, 0, 8⟩, ⟨7, 19, 0, 2⟩, ⟨7, 18, 0, 4⟩, ⟨7, 17, 0, 6⟩, ⟨7, 16, 0, 8⟩]
  exact AllWinning.cons node_13360 (AllWinning.cons node_12340 (AllWinning.cons node_11296 (AllWinning.cons node_10167 (AllWinning.cons node_13422 (AllWinning.cons node_12484 (AllWinning.cons node_11493 (AllWinning.cons node_10488 (AllWinning.nil))))))))

theorem node_14395 : Outcome ⟨7, 20, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 0, 2⟩, ⟨5, 20, 0, 4⟩, ⟨4, 20, 0, 6⟩, ⟨3, 20, 0, 8⟩, ⟨2, 20, 0, 10⟩, ⟨1, 20, 0, 12⟩, ⟨7, 19, 0, 2⟩, ⟨7, 18, 0, 4⟩, ⟨7, 17, 0, 6⟩, ⟨7, 16, 0, 8⟩, ⟨7, 15, 0, 10⟩, ⟨7, 14, 0, 12⟩]
  exact AllWinning.cons node_13360 (AllWinning.cons node_12340 (AllWinning.cons node_11296 (AllWinning.cons node_10167 (AllWinning.cons node_9123 (AllWinning.cons node_8064 (AllWinning.cons node_13422 (AllWinning.cons node_12484 (AllWinning.cons node_11493 (AllWinning.cons node_10488 (AllWinning.cons node_9465 (AllWinning.cons node_8497 (AllWinning.nil))))))))))))

theorem node_14396 : Outcome ⟨7, 20, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 0, 2⟩, ⟨5, 20, 0, 4⟩, ⟨4, 20, 0, 6⟩, ⟨3, 20, 0, 8⟩, ⟨2, 20, 0, 10⟩, ⟨1, 20, 0, 12⟩, ⟨0, 20, 0, 14⟩, ⟨7, 19, 0, 2⟩, ⟨7, 18, 0, 4⟩, ⟨7, 17, 0, 6⟩, ⟨7, 16, 0, 8⟩, ⟨7, 15, 0, 10⟩, ⟨7, 14, 0, 12⟩, ⟨7, 13, 0, 14⟩, ⟨7, 12, 0, 16⟩]
  exact AllWinning.cons node_13360 (AllWinning.cons node_12340 (AllWinning.cons node_11296 (AllWinning.cons node_10167 (AllWinning.cons node_9123 (AllWinning.cons node_8064 (AllWinning.cons node_7026 (AllWinning.cons node_13422 (AllWinning.cons node_12484 (AllWinning.cons node_11493 (AllWinning.cons node_10488 (AllWinning.cons node_9465 (AllWinning.cons node_8497 (AllWinning.cons node_7537 (AllWinning.cons node_6619 (AllWinning.nil)))))))))))))))

theorem node_14397 : Outcome ⟨7, 20, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 0, 2⟩, ⟨5, 20, 0, 4⟩, ⟨4, 20, 0, 6⟩, ⟨3, 20, 0, 8⟩, ⟨2, 20, 0, 10⟩, ⟨1, 20, 0, 12⟩, ⟨0, 20, 0, 14⟩, ⟨7, 19, 0, 2⟩, ⟨7, 18, 0, 4⟩, ⟨7, 17, 0, 6⟩, ⟨7, 16, 0, 8⟩, ⟨7, 15, 0, 10⟩, ⟨7, 14, 0, 12⟩, ⟨7, 13, 0, 14⟩, ⟨7, 12, 0, 16⟩, ⟨7, 11, 0, 18⟩, ⟨7, 10, 0, 20⟩]
  exact AllWinning.cons node_13360 (AllWinning.cons node_12340 (AllWinning.cons node_11296 (AllWinning.cons node_10167 (AllWinning.cons node_9123 (AllWinning.cons node_8064 (AllWinning.cons node_7026 (AllWinning.cons node_13422 (AllWinning.cons node_12484 (AllWinning.cons node_11493 (AllWinning.cons node_10488 (AllWinning.cons node_9465 (AllWinning.cons node_8497 (AllWinning.cons node_7537 (AllWinning.cons node_6619 (AllWinning.cons node_5774 (AllWinning.cons node_5076 (AllWinning.nil)))))))))))))))))

theorem node_14398 : Outcome ⟨7, 20, 0, 16⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 26⟩) (by decide) node_3210

theorem node_14399 : Outcome ⟨8, 0, 19, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 4⟩) (by decide) node_12343

theorem node_14400 : Outcome ⟨8, 0, 19, 6⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 4⟩) (by decide) node_12343

theorem node_14401 : Outcome ⟨8, 0, 19, 22⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 22⟩) (by decide) node_4400

theorem node_14402 : Outcome ⟨8, 1, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 1, 18, 2⟩, ⟨6, 1, 18, 4⟩, ⟨8, 0, 18, 2⟩, ⟨8, 1, 17, 2⟩, ⟨8, 1, 16, 4⟩]
  exact AllWinning.cons node_13366 (AllWinning.cons node_12349 (AllWinning.cons node_13426 (AllWinning.cons node_13429 (AllWinning.cons node_12490 (AllWinning.nil)))))

theorem node_14403 : Outcome ⟨8, 1, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 1, 18, 2⟩, ⟨6, 1, 18, 4⟩, ⟨5, 1, 18, 6⟩, ⟨4, 1, 18, 8⟩, ⟨8, 0, 18, 2⟩, ⟨8, 1, 17, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 1, 15, 6⟩, ⟨8, 1, 14, 8⟩]
  exact AllWinning.cons node_13366 (AllWinning.cons node_12349 (AllWinning.cons node_11301 (AllWinning.cons node_10173 (AllWinning.cons node_13426 (AllWinning.cons node_13429 (AllWinning.cons node_12490 (AllWinning.cons node_11501 (AllWinning.cons node_10497 (AllWinning.nil)))))))))

theorem node_14404 : Outcome ⟨8, 1, 18, 14⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 12⟩) (by decide) node_8507

theorem node_14405 : Outcome ⟨8, 2, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 2, 17, 4⟩) (by decide) node_12352

theorem node_14406 : Outcome ⟨8, 2, 17, 6⟩ true :=
  Outcome.win (q := ⟨6, 2, 17, 4⟩) (by decide) node_12352

theorem node_14407 : Outcome ⟨8, 3, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.nil))))))

theorem node_14408 : Outcome ⟨8, 3, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨5, 3, 16, 6⟩, ⟨4, 3, 16, 8⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩, ⟨8, 3, 13, 6⟩, ⟨8, 3, 12, 8⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_11309 (AllWinning.cons node_10181 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_11498 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.cons node_11507 (AllWinning.cons node_10501 (AllWinning.nil)))))))))))

theorem node_14409 : Outcome ⟨8, 3, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨5, 3, 16, 6⟩, ⟨4, 3, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨2, 3, 16, 12⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩, ⟨8, 3, 13, 6⟩, ⟨8, 3, 12, 8⟩, ⟨8, 3, 11, 10⟩, ⟨8, 3, 10, 12⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_11309 (AllWinning.cons node_10181 (AllWinning.cons node_9136 (AllWinning.cons node_8078 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_11498 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.cons node_11507 (AllWinning.cons node_10501 (AllWinning.cons node_9479 (AllWinning.cons node_8519 (AllWinning.nil)))))))))))))))

theorem node_14410 : Outcome ⟨8, 3, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨5, 3, 16, 6⟩, ⟨4, 3, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨2, 3, 16, 12⟩, ⟨1, 3, 16, 14⟩, ⟨0, 3, 16, 16⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩, ⟨8, 3, 13, 6⟩, ⟨8, 3, 12, 8⟩, ⟨8, 3, 11, 10⟩, ⟨8, 3, 10, 12⟩, ⟨8, 3, 9, 14⟩, ⟨8, 3, 8, 16⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_11309 (AllWinning.cons node_10181 (AllWinning.cons node_9136 (AllWinning.cons node_8078 (AllWinning.cons node_7043 (AllWinning.cons node_6048 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_11498 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.cons node_11507 (AllWinning.cons node_10501 (AllWinning.cons node_9479 (AllWinning.cons node_8519 (AllWinning.cons node_7552 (AllWinning.cons node_6635 (AllWinning.nil)))))))))))))))))))

theorem node_14411 : Outcome ⟨8, 3, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨5, 3, 16, 6⟩, ⟨4, 3, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨2, 3, 16, 12⟩, ⟨1, 3, 16, 14⟩, ⟨0, 3, 16, 16⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩, ⟨8, 3, 13, 6⟩, ⟨8, 3, 12, 8⟩, ⟨8, 3, 11, 10⟩, ⟨8, 3, 10, 12⟩, ⟨8, 3, 9, 14⟩, ⟨8, 3, 8, 16⟩, ⟨8, 3, 7, 18⟩, ⟨8, 3, 6, 20⟩, ⟨8, 3, 5, 22⟩, ⟨8, 3, 4, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 3, 2, 28⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_11309 (AllWinning.cons node_10181 (AllWinning.cons node_9136 (AllWinning.cons node_8078 (AllWinning.cons node_7043 (AllWinning.cons node_6048 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_11498 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.cons node_11507 (AllWinning.cons node_10501 (AllWinning.cons node_9479 (AllWinning.cons node_8519 (AllWinning.cons node_7552 (AllWinning.cons node_6635 (AllWinning.cons node_5791 (AllWinning.cons node_5090 (AllWinning.cons node_4413 (AllWinning.cons node_3773 (AllWinning.cons node_3227 (AllWinning.cons node_2739 (AllWinning.nil)))))))))))))))))))))))))

theorem node_14412 : Outcome ⟨8, 3, 16, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨5, 3, 16, 6⟩, ⟨4, 3, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨2, 3, 16, 12⟩, ⟨1, 3, 16, 14⟩, ⟨0, 3, 16, 16⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩, ⟨8, 3, 13, 6⟩, ⟨8, 3, 12, 8⟩, ⟨8, 3, 11, 10⟩, ⟨8, 3, 10, 12⟩, ⟨8, 3, 9, 14⟩, ⟨8, 3, 8, 16⟩, ⟨8, 3, 7, 18⟩, ⟨8, 3, 6, 20⟩, ⟨8, 3, 5, 22⟩, ⟨8, 3, 4, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 3, 2, 28⟩, ⟨8, 3, 1, 30⟩, ⟨8, 3, 0, 32⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_11309 (AllWinning.cons node_10181 (AllWinning.cons node_9136 (AllWinning.cons node_8078 (AllWinning.cons node_7043 (AllWinning.cons node_6048 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_11498 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.cons node_11507 (AllWinning.cons node_10501 (AllWinning.cons node_9479 (AllWinning.cons node_8519 (AllWinning.cons node_7552 (AllWinning.cons node_6635 (AllWinning.cons node_5791 (AllWinning.cons node_5090 (AllWinning.cons node_4413 (AllWinning.cons node_3773 (AllWinning.cons node_3227 (AllWinning.cons node_2739 (AllWinning.cons node_2311 (AllWinning.cons node_1837 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14413 : Outcome ⟨8, 3, 16, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨5, 3, 16, 6⟩, ⟨4, 3, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨2, 3, 16, 12⟩, ⟨1, 3, 16, 14⟩, ⟨0, 3, 16, 16⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩, ⟨8, 3, 13, 6⟩, ⟨8, 3, 12, 8⟩, ⟨8, 3, 11, 10⟩, ⟨8, 3, 10, 12⟩, ⟨8, 3, 9, 14⟩, ⟨8, 3, 8, 16⟩, ⟨8, 3, 7, 18⟩, ⟨8, 3, 6, 20⟩, ⟨8, 3, 5, 22⟩, ⟨8, 3, 4, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 3, 2, 28⟩, ⟨8, 3, 1, 30⟩, ⟨8, 3, 0, 32⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_11309 (AllWinning.cons node_10181 (AllWinning.cons node_9136 (AllWinning.cons node_8078 (AllWinning.cons node_7043 (AllWinning.cons node_6048 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_11498 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.cons node_11507 (AllWinning.cons node_10501 (AllWinning.cons node_9479 (AllWinning.cons node_8519 (AllWinning.cons node_7552 (AllWinning.cons node_6635 (AllWinning.cons node_5791 (AllWinning.cons node_5090 (AllWinning.cons node_4413 (AllWinning.cons node_3773 (AllWinning.cons node_3227 (AllWinning.cons node_2739 (AllWinning.cons node_2311 (AllWinning.cons node_1837 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14414 : Outcome ⟨8, 3, 16, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 16, 2⟩, ⟨6, 3, 16, 4⟩, ⟨5, 3, 16, 6⟩, ⟨4, 3, 16, 8⟩, ⟨3, 3, 16, 10⟩, ⟨2, 3, 16, 12⟩, ⟨1, 3, 16, 14⟩, ⟨0, 3, 16, 16⟩, ⟨8, 2, 16, 2⟩, ⟨8, 1, 16, 4⟩, ⟨8, 0, 16, 6⟩, ⟨8, 3, 15, 2⟩, ⟨8, 3, 14, 4⟩, ⟨8, 3, 13, 6⟩, ⟨8, 3, 12, 8⟩, ⟨8, 3, 11, 10⟩, ⟨8, 3, 10, 12⟩, ⟨8, 3, 9, 14⟩, ⟨8, 3, 8, 16⟩, ⟨8, 3, 7, 18⟩, ⟨8, 3, 6, 20⟩, ⟨8, 3, 5, 22⟩, ⟨8, 3, 4, 24⟩, ⟨8, 3, 3, 26⟩, ⟨8, 3, 2, 28⟩, ⟨8, 3, 1, 30⟩, ⟨8, 3, 0, 32⟩]
  exact AllWinning.cons node_13370 (AllWinning.cons node_12356 (AllWinning.cons node_11309 (AllWinning.cons node_10181 (AllWinning.cons node_9136 (AllWinning.cons node_8078 (AllWinning.cons node_7043 (AllWinning.cons node_6048 (AllWinning.cons node_13433 (AllWinning.cons node_12490 (AllWinning.cons node_11498 (AllWinning.cons node_13436 (AllWinning.cons node_12496 (AllWinning.cons node_11507 (AllWinning.cons node_10501 (AllWinning.cons node_9479 (AllWinning.cons node_8519 (AllWinning.cons node_7552 (AllWinning.cons node_6635 (AllWinning.cons node_5791 (AllWinning.cons node_5090 (AllWinning.cons node_4413 (AllWinning.cons node_3773 (AllWinning.cons node_3227 (AllWinning.cons node_2739 (AllWinning.cons node_2311 (AllWinning.cons node_1837 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_14415 : Outcome ⟨8, 4, 15, 2⟩ true :=
  Outcome.win (q := ⟨6, 4, 15, 4⟩) (by decide) node_12360

theorem node_14416 : Outcome ⟨8, 4, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 15, 4⟩) (by decide) node_12360

theorem node_14417 : Outcome ⟨8, 5, 14, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 13, 2⟩) (by decide) node_13443

theorem node_14418 : Outcome ⟨8, 6, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 2⟩) (by decide) node_13376

theorem node_14419 : Outcome ⟨8, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 2⟩) (by decide) node_13376

theorem node_14420 : Outcome ⟨8, 6, 13, 12⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 12⟩) (by decide) node_8534

theorem node_14421 : Outcome ⟨8, 7, 12, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 2⟩) (by decide) node_13381

theorem node_14422 : Outcome ⟨8, 7, 12, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 12⟩) (by decide) node_8507

theorem node_14423 : Outcome ⟨8, 7, 12, 14⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 12⟩) (by decide) node_8507

theorem node_14424 : Outcome ⟨8, 7, 12, 16⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 12⟩) (by decide) node_8507

theorem node_14425 : Outcome ⟨8, 8, 11, 2⟩ true :=
  Outcome.win (q := ⟨7, 8, 11, 2⟩) (by decide) node_13387

end RQ9F1
