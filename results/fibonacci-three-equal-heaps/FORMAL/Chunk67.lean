import Chunk66
set_option autoImplicit false
namespace RQ9F1

theorem node_15250 : Outcome ⟨6, 14, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 8, 2⟩, ⟨4, 14, 8, 4⟩, ⟨3, 14, 8, 6⟩, ⟨2, 14, 8, 8⟩, ⟨6, 13, 8, 2⟩, ⟨6, 12, 8, 4⟩, ⟨6, 11, 8, 6⟩, ⟨6, 10, 8, 8⟩, ⟨6, 14, 7, 2⟩, ⟨6, 14, 6, 4⟩, ⟨6, 14, 5, 6⟩, ⟨6, 14, 4, 8⟩]
  exact AllWinning.cons node_14244 (AllWinning.cons node_13228 (AllWinning.cons node_12193 (AllWinning.cons node_11127 (AllWinning.cons node_14298 (AllWinning.cons node_13333 (AllWinning.cons node_12386 (AllWinning.cons node_11399 (AllWinning.cons node_14301 (AllWinning.cons node_13341 (AllWinning.cons node_12398 (AllWinning.cons node_11415 (AllWinning.nil))))))))))))

theorem node_15251 : Outcome ⟨6, 14, 8, 10⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 14⟩) (by decide) node_8373

theorem node_15252 : Outcome ⟨6, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨6, 13, 7, 4⟩) (by decide) node_13337

theorem node_15253 : Outcome ⟨6, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 6⟩) (by decide) node_12197

theorem node_15254 : Outcome ⟨6, 15, 7, 8⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 14⟩) (by decide) node_8385

theorem node_15255 : Outcome ⟨6, 15, 7, 12⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 14⟩) (by decide) node_8385

theorem node_15256 : Outcome ⟨6, 16, 6, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 6, 2⟩) (by decide) node_14248

theorem node_15257 : Outcome ⟨6, 16, 6, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 10⟩) (by decide) node_10001

theorem node_15258 : Outcome ⟨6, 16, 6, 12⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 10⟩) (by decide) node_10001

theorem node_15259 : Outcome ⟨6, 17, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 5, 4⟩) (by decide) node_13236

theorem node_15260 : Outcome ⟨6, 17, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 17, 5, 4⟩) (by decide) node_13236

theorem node_15261 : Outcome ⟨6, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 4, 4⟩) (by decide) node_13239

theorem node_15262 : Outcome ⟨6, 18, 4, 10⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 16⟩) (by decide) node_7462

theorem node_15263 : Outcome ⟨6, 18, 4, 12⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 16⟩) (by decide) node_7462

theorem node_15264 : Outcome ⟨6, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 19, 3, 2⟩) (by decide) node_14257

theorem node_15265 : Outcome ⟨6, 19, 3, 8⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 10⟩) (by decide) node_10018

theorem node_15266 : Outcome ⟨6, 19, 3, 10⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 10⟩) (by decide) node_10018

theorem node_15267 : Outcome ⟨6, 20, 2, 6⟩ true :=
  Outcome.win (q := ⟨3, 20, 2, 6⟩) (by decide) node_12217

theorem node_15268 : Outcome ⟨6, 20, 2, 8⟩ true :=
  Outcome.win (q := ⟨3, 20, 2, 6⟩) (by decide) node_12217

theorem node_15269 : Outcome ⟨7, 1, 20, 6⟩ true :=
  Outcome.win (q := ⟨7, 0, 20, 2⟩) (by decide) node_14321

theorem node_15270 : Outcome ⟨7, 1, 20, 14⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 18⟩) (by decide) node_6564

theorem node_15271 : Outcome ⟨7, 2, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 2⟩) (by decide) node_14329

theorem node_15272 : Outcome ⟨7, 2, 19, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 2⟩) (by decide) node_14329

theorem node_15273 : Outcome ⟨7, 3, 18, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 18, 2⟩) (by decide) node_14267

theorem node_15274 : Outcome ⟨7, 3, 18, 6⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 6⟩) (by decide) node_12432

theorem node_15275 : Outcome ⟨7, 3, 18, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 6⟩) (by decide) node_12432

theorem node_15276 : Outcome ⟨7, 3, 18, 16⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 32⟩) (by decide) node_2280

theorem node_15277 : Outcome ⟨7, 4, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 17, 4⟩) (by decide) node_13253

theorem node_15278 : Outcome ⟨7, 5, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 5, 16, 2⟩) (by decide) node_14273

theorem node_15279 : Outcome ⟨7, 5, 16, 12⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 24⟩) (by decide) node_4369

theorem node_15280 : Outcome ⟨7, 6, 15, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 4⟩) (by decide) node_13377

theorem node_15281 : Outcome ⟨7, 6, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 15, 6⟩) (by decide) node_12432

theorem node_15282 : Outcome ⟨7, 6, 15, 8⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 14⟩) (by decide) node_8449

theorem node_15283 : Outcome ⟨7, 6, 15, 12⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 14⟩) (by decide) node_8449

theorem node_15284 : Outcome ⟨7, 7, 14, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 4⟩) (by decide) node_13382

theorem node_15285 : Outcome ⟨7, 7, 14, 8⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 4⟩) (by decide) node_13382

theorem node_15286 : Outcome ⟨7, 8, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 4⟩) (by decide) node_13377

theorem node_15287 : Outcome ⟨7, 8, 13, 12⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 14⟩) (by decide) node_8465

theorem node_15288 : Outcome ⟨7, 8, 13, 14⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 14⟩) (by decide) node_8465

theorem node_15289 : Outcome ⟨7, 9, 12, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 4⟩) (by decide) node_13382

theorem node_15290 : Outcome ⟨7, 9, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 8⟩) (by decide) node_11175

theorem node_15291 : Outcome ⟨7, 9, 12, 12⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 8⟩) (by decide) node_11175

theorem node_15292 : Outcome ⟨7, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨7, 8, 11, 4⟩) (by decide) node_13388

theorem node_15293 : Outcome ⟨7, 10, 11, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 11, 4⟩) (by decide) node_13388

theorem node_15294 : Outcome ⟨7, 10, 11, 12⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 18⟩) (by decide) node_6564

theorem node_15295 : Outcome ⟨7, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 4⟩) (by decide) node_13397

theorem node_15296 : Outcome ⟨7, 11, 10, 6⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 4⟩) (by decide) node_13397

theorem node_15297 : Outcome ⟨7, 11, 10, 12⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 18⟩) (by decide) node_6611

theorem node_15298 : Outcome ⟨7, 12, 9, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 4⟩) (by decide) node_13402

theorem node_15299 : Outcome ⟨7, 12, 9, 6⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 8⟩) (by decide) node_11196

theorem node_15300 : Outcome ⟨7, 12, 9, 12⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 8⟩) (by decide) node_11196

theorem node_15301 : Outcome ⟨7, 13, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 4⟩) (by decide) node_13397

theorem node_15302 : Outcome ⟨7, 13, 8, 12⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 14⟩) (by decide) node_8449

theorem node_15303 : Outcome ⟨7, 13, 8, 14⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 14⟩) (by decide) node_8449

theorem node_15304 : Outcome ⟨7, 14, 7, 6⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 4⟩) (by decide) node_13402

theorem node_15305 : Outcome ⟨7, 14, 7, 8⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 4⟩) (by decide) node_13402

theorem node_15306 : Outcome ⟨7, 15, 6, 2⟩ true :=
  Outcome.win (q := ⟨7, 13, 6, 4⟩) (by decide) node_13408

theorem node_15307 : Outcome ⟨7, 15, 6, 4⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 6⟩) (by decide) node_12471

theorem node_15308 : Outcome ⟨7, 15, 6, 8⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 14⟩) (by decide) node_8465

theorem node_15309 : Outcome ⟨7, 15, 6, 12⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 14⟩) (by decide) node_8465

theorem node_15310 : Outcome ⟨7, 16, 5, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 5, 2⟩) (by decide) node_14308

theorem node_15311 : Outcome ⟨7, 16, 5, 12⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 24⟩) (by decide) node_4354

theorem node_15312 : Outcome ⟨7, 17, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 17, 4, 4⟩) (by decide) node_13285

theorem node_15313 : Outcome ⟨7, 18, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 18, 3, 2⟩) (by decide) node_14313

theorem node_15314 : Outcome ⟨7, 18, 3, 6⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 6⟩) (by decide) node_12471

theorem node_15315 : Outcome ⟨7, 18, 3, 8⟩ true :=
  Outcome.win (q := ⟨7, 15, 3, 6⟩) (by decide) node_12471

theorem node_15316 : Outcome ⟨7, 18, 3, 16⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 32⟩) (by decide) node_2264

theorem node_15317 : Outcome ⟨7, 19, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 2⟩) (by decide) node_14383

theorem node_15318 : Outcome ⟨7, 19, 2, 8⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 2⟩) (by decide) node_14383

theorem node_15319 : Outcome ⟨7, 20, 1, 6⟩ true :=
  Outcome.win (q := ⟨7, 20, 0, 2⟩) (by decide) node_14393

theorem node_15320 : Outcome ⟨7, 20, 1, 14⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 18⟩) (by decide) node_6611

theorem node_15321 : Outcome ⟨8, 0, 20, 8⟩ true :=
  Outcome.win (q := ⟨7, 0, 20, 2⟩) (by decide) node_14321

theorem node_15322 : Outcome ⟨8, 0, 20, 14⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 24⟩) (by decide) node_4401

theorem node_15323 : Outcome ⟨8, 1, 19, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 18, 2⟩) (by decide) node_14402

theorem node_15324 : Outcome ⟨8, 1, 19, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 14⟩) (by decide) node_8508

theorem node_15325 : Outcome ⟨8, 2, 18, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 2⟩) (by decide) node_14329

theorem node_15326 : Outcome ⟨8, 2, 18, 12⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 2⟩) (by decide) node_14329

theorem node_15327 : Outcome ⟨8, 2, 18, 16⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 2⟩) (by decide) node_14329

theorem node_15328 : Outcome ⟨8, 3, 17, 2⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 2⟩) (by decide) node_14407

theorem node_15329 : Outcome ⟨8, 3, 17, 12⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 2⟩) (by decide) node_14407

theorem node_15330 : Outcome ⟨8, 4, 16, 2⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 2⟩) (by decide) node_14407

theorem node_15331 : Outcome ⟨8, 5, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.nil))))))

theorem node_15332 : Outcome ⟨8, 5, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.nil))))))))))))

theorem node_15333 : Outcome ⟨8, 5, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.nil)))))))))))))))))

theorem node_15334 : Outcome ⟨8, 5, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨1, 5, 15, 14⟩, ⟨0, 5, 15, 16⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩, ⟨8, 5, 8, 14⟩, ⟨8, 5, 7, 16⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_7996 (AllWinning.cons node_6963 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.cons node_8527 (AllWinning.cons node_7559 (AllWinning.nil)))))))))))))))))))))

theorem node_15335 : Outcome ⟨8, 5, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨1, 5, 15, 14⟩, ⟨0, 5, 15, 16⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩, ⟨8, 5, 8, 14⟩, ⟨8, 5, 7, 16⟩, ⟨8, 5, 6, 18⟩, ⟨8, 5, 5, 20⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_7996 (AllWinning.cons node_6963 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.cons node_8527 (AllWinning.cons node_7559 (AllWinning.cons node_6642 (AllWinning.cons node_5799 (AllWinning.nil)))))))))))))))))))))))

theorem node_15336 : Outcome ⟨8, 5, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨1, 5, 15, 14⟩, ⟨0, 5, 15, 16⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩, ⟨8, 5, 8, 14⟩, ⟨8, 5, 7, 16⟩, ⟨8, 5, 6, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 5, 4, 22⟩, ⟨8, 5, 3, 24⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_7996 (AllWinning.cons node_6963 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.cons node_8527 (AllWinning.cons node_7559 (AllWinning.cons node_6642 (AllWinning.cons node_5799 (AllWinning.cons node_5097 (AllWinning.cons node_4422 (AllWinning.nil)))))))))))))))))))))))))

theorem node_15337 : Outcome ⟨8, 5, 15, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨1, 5, 15, 14⟩, ⟨0, 5, 15, 16⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩, ⟨8, 5, 8, 14⟩, ⟨8, 5, 7, 16⟩, ⟨8, 5, 6, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 5, 4, 22⟩, ⟨8, 5, 3, 24⟩, ⟨8, 5, 2, 26⟩, ⟨8, 5, 1, 28⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_7996 (AllWinning.cons node_6963 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.cons node_8527 (AllWinning.cons node_7559 (AllWinning.cons node_6642 (AllWinning.cons node_5799 (AllWinning.cons node_5097 (AllWinning.cons node_4422 (AllWinning.cons node_3781 (AllWinning.cons node_3236 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_15338 : Outcome ⟨8, 5, 15, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨1, 5, 15, 14⟩, ⟨0, 5, 15, 16⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩, ⟨8, 5, 8, 14⟩, ⟨8, 5, 7, 16⟩, ⟨8, 5, 6, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 5, 4, 22⟩, ⟨8, 5, 3, 24⟩, ⟨8, 5, 2, 26⟩, ⟨8, 5, 1, 28⟩, ⟨8, 5, 0, 30⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_7996 (AllWinning.cons node_6963 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.cons node_8527 (AllWinning.cons node_7559 (AllWinning.cons node_6642 (AllWinning.cons node_5799 (AllWinning.cons node_5097 (AllWinning.cons node_4422 (AllWinning.cons node_3781 (AllWinning.cons node_3236 (AllWinning.cons node_2751 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15339 : Outcome ⟨8, 5, 15, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨1, 5, 15, 14⟩, ⟨0, 5, 15, 16⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩, ⟨8, 5, 8, 14⟩, ⟨8, 5, 7, 16⟩, ⟨8, 5, 6, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 5, 4, 22⟩, ⟨8, 5, 3, 24⟩, ⟨8, 5, 2, 26⟩, ⟨8, 5, 1, 28⟩, ⟨8, 5, 0, 30⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_7996 (AllWinning.cons node_6963 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.cons node_8527 (AllWinning.cons node_7559 (AllWinning.cons node_6642 (AllWinning.cons node_5799 (AllWinning.cons node_5097 (AllWinning.cons node_4422 (AllWinning.cons node_3781 (AllWinning.cons node_3236 (AllWinning.cons node_2751 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15340 : Outcome ⟨8, 5, 15, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 15, 2⟩, ⟨6, 5, 15, 4⟩, ⟨5, 5, 15, 6⟩, ⟨4, 5, 15, 8⟩, ⟨3, 5, 15, 10⟩, ⟨2, 5, 15, 12⟩, ⟨1, 5, 15, 14⟩, ⟨0, 5, 15, 16⟩, ⟨8, 4, 15, 2⟩, ⟨8, 3, 15, 4⟩, ⟨8, 2, 15, 6⟩, ⟨8, 1, 15, 8⟩, ⟨8, 0, 15, 10⟩, ⟨8, 5, 14, 2⟩, ⟨8, 5, 13, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 5, 11, 8⟩, ⟨8, 5, 10, 10⟩, ⟨8, 5, 9, 12⟩, ⟨8, 5, 8, 14⟩, ⟨8, 5, 7, 16⟩, ⟨8, 5, 6, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 5, 4, 22⟩, ⟨8, 5, 3, 24⟩, ⟨8, 5, 2, 26⟩, ⟨8, 5, 1, 28⟩, ⟨8, 5, 0, 30⟩]
  exact AllWinning.cons node_14341 (AllWinning.cons node_13310 (AllWinning.cons node_12296 (AllWinning.cons node_11245 (AllWinning.cons node_10107 (AllWinning.cons node_9068 (AllWinning.cons node_7996 (AllWinning.cons node_6963 (AllWinning.cons node_14415 (AllWinning.cons node_13437 (AllWinning.cons node_12494 (AllWinning.cons node_11502 (AllWinning.cons node_10493 (AllWinning.cons node_14417 (AllWinning.cons node_13444 (AllWinning.cons node_12503 (AllWinning.cons node_11513 (AllWinning.cons node_10510 (AllWinning.cons node_9487 (AllWinning.cons node_8527 (AllWinning.cons node_7559 (AllWinning.cons node_6642 (AllWinning.cons node_5799 (AllWinning.cons node_5097 (AllWinning.cons node_4422 (AllWinning.cons node_3781 (AllWinning.cons node_3236 (AllWinning.cons node_2751 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15341 : Outcome ⟨8, 6, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 6, 14, 2⟩, ⟨6, 6, 14, 4⟩, ⟨8, 5, 14, 2⟩, ⟨8, 4, 14, 4⟩, ⟨8, 6, 13, 2⟩, ⟨8, 6, 12, 4⟩]
  exact AllWinning.cons node_14344 (AllWinning.cons node_13312 (AllWinning.cons node_14417 (AllWinning.cons node_13440 (AllWinning.cons node_14418 (AllWinning.cons node_13445 (AllWinning.nil))))))

theorem node_15342 : Outcome ⟨8, 6, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 6, 14, 2⟩, ⟨6, 6, 14, 4⟩, ⟨5, 6, 14, 6⟩, ⟨4, 6, 14, 8⟩, ⟨8, 5, 14, 2⟩, ⟨8, 4, 14, 4⟩, ⟨8, 3, 14, 6⟩, ⟨8, 2, 14, 8⟩, ⟨8, 6, 13, 2⟩, ⟨8, 6, 12, 4⟩, ⟨8, 6, 11, 6⟩, ⟨8, 6, 10, 8⟩]
  exact AllWinning.cons node_14344 (AllWinning.cons node_13312 (AllWinning.cons node_12298 (AllWinning.cons node_11248 (AllWinning.cons node_14417 (AllWinning.cons node_13440 (AllWinning.cons node_12497 (AllWinning.cons node_11504 (AllWinning.cons node_14418 (AllWinning.cons node_13445 (AllWinning.cons node_12506 (AllWinning.cons node_11516 (AllWinning.nil))))))))))))

theorem node_15343 : Outcome ⟨8, 6, 14, 10⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 14⟩) (by decide) node_8535

theorem node_15344 : Outcome ⟨8, 7, 13, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 13, 4⟩) (by decide) node_13317

theorem node_15345 : Outcome ⟨8, 7, 13, 12⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 14⟩) (by decide) node_8547

theorem node_15346 : Outcome ⟨8, 7, 13, 14⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 14⟩) (by decide) node_8547

theorem node_15347 : Outcome ⟨8, 8, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 12, 2⟩, ⟨6, 8, 12, 4⟩, ⟨8, 7, 12, 2⟩, ⟨8, 6, 12, 4⟩, ⟨8, 8, 11, 2⟩, ⟨8, 8, 10, 4⟩]
  exact AllWinning.cons node_14350 (AllWinning.cons node_13321 (AllWinning.cons node_14421 (AllWinning.cons node_13445 (AllWinning.cons node_14425 (AllWinning.cons node_13453 (AllWinning.nil))))))

theorem node_15348 : Outcome ⟨8, 8, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 12, 2⟩, ⟨6, 8, 12, 4⟩, ⟨5, 8, 12, 6⟩, ⟨4, 8, 12, 8⟩, ⟨8, 7, 12, 2⟩, ⟨8, 6, 12, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 4, 12, 8⟩, ⟨8, 8, 11, 2⟩, ⟨8, 8, 10, 4⟩, ⟨8, 8, 9, 6⟩, ⟨8, 8, 8, 8⟩]
  exact AllWinning.cons node_14350 (AllWinning.cons node_13321 (AllWinning.cons node_12304 (AllWinning.cons node_11254 (AllWinning.cons node_14421 (AllWinning.cons node_13445 (AllWinning.cons node_12503 (AllWinning.cons node_11509 (AllWinning.cons node_14425 (AllWinning.cons node_13453 (AllWinning.cons node_12514 (AllWinning.cons node_11525 (AllWinning.nil))))))))))))

theorem node_15349 : Outcome ⟨8, 8, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 12, 2⟩, ⟨6, 8, 12, 4⟩, ⟨5, 8, 12, 6⟩, ⟨4, 8, 12, 8⟩, ⟨3, 8, 12, 10⟩, ⟨2, 8, 12, 12⟩, ⟨8, 7, 12, 2⟩, ⟨8, 6, 12, 4⟩, ⟨8, 5, 12, 6⟩, ⟨8, 4, 12, 8⟩, ⟨8, 3, 12, 10⟩, ⟨8, 2, 12, 12⟩, ⟨8, 8, 11, 2⟩, ⟨8, 8, 10, 4⟩, ⟨8, 8, 9, 6⟩, ⟨8, 8, 8, 8⟩, ⟨8, 8, 7, 10⟩, ⟨8, 8, 6, 12⟩]
  exact AllWinning.cons node_14350 (AllWinning.cons node_13321 (AllWinning.cons node_12304 (AllWinning.cons node_11254 (AllWinning.cons node_10121 (AllWinning.cons node_9078 (AllWinning.cons node_14421 (AllWinning.cons node_13445 (AllWinning.cons node_12503 (AllWinning.cons node_11509 (AllWinning.cons node_10502 (AllWinning.cons node_9475 (AllWinning.cons node_14425 (AllWinning.cons node_13453 (AllWinning.cons node_12514 (AllWinning.cons node_11525 (AllWinning.cons node_10523 (AllWinning.cons node_9494 (AllWinning.nil))))))))))))))))))

theorem node_15350 : Outcome ⟨8, 8, 12, 12⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 24⟩) (by decide) node_4442

theorem node_15351 : Outcome ⟨8, 9, 11, 2⟩ true :=
  Outcome.win (q := ⟨8, 7, 11, 4⟩) (by decide) node_13449

theorem node_15352 : Outcome ⟨8, 9, 11, 6⟩ true :=
  Outcome.win (q := ⟨8, 7, 11, 4⟩) (by decide) node_13449

theorem node_15353 : Outcome ⟨8, 10, 10, 2⟩ true :=
  Outcome.win (q := ⟨7, 10, 10, 2⟩) (by decide) node_14357

theorem node_15354 : Outcome ⟨8, 10, 10, 10⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 16⟩) (by decide) node_6987

theorem node_15355 : Outcome ⟨8, 10, 10, 18⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 16⟩) (by decide) node_6987

theorem node_15356 : Outcome ⟨8, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨8, 9, 9, 4⟩) (by decide) node_13457

theorem node_15357 : Outcome ⟨8, 11, 9, 6⟩ true :=
  Outcome.win (q := ⟨8, 9, 9, 4⟩) (by decide) node_13457

theorem node_15358 : Outcome ⟨8, 12, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 8, 2⟩, ⟨6, 12, 8, 4⟩, ⟨8, 11, 8, 2⟩, ⟨8, 10, 8, 4⟩, ⟨8, 12, 7, 2⟩, ⟨8, 12, 6, 4⟩]
  exact AllWinning.cons node_14366 (AllWinning.cons node_13333 (AllWinning.cons node_14430 (AllWinning.cons node_13459 (AllWinning.cons node_14433 (AllWinning.cons node_13467 (AllWinning.nil))))))

theorem node_15359 : Outcome ⟨8, 12, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 8, 2⟩, ⟨6, 12, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨4, 12, 8, 8⟩, ⟨8, 11, 8, 2⟩, ⟨8, 10, 8, 4⟩, ⟨8, 9, 8, 6⟩, ⟨8, 8, 8, 8⟩, ⟨8, 12, 7, 2⟩, ⟨8, 12, 6, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 12, 4, 8⟩]
  exact AllWinning.cons node_14366 (AllWinning.cons node_13333 (AllWinning.cons node_12317 (AllWinning.cons node_11269 (AllWinning.cons node_14430 (AllWinning.cons node_13459 (AllWinning.cons node_12517 (AllWinning.cons node_11525 (AllWinning.cons node_14433 (AllWinning.cons node_13467 (AllWinning.cons node_12529 (AllWinning.cons node_11539 (AllWinning.nil))))))))))))

theorem node_15360 : Outcome ⟨8, 12, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 8, 2⟩, ⟨6, 12, 8, 4⟩, ⟨5, 12, 8, 6⟩, ⟨4, 12, 8, 8⟩, ⟨3, 12, 8, 10⟩, ⟨2, 12, 8, 12⟩, ⟨8, 11, 8, 2⟩, ⟨8, 10, 8, 4⟩, ⟨8, 9, 8, 6⟩, ⟨8, 8, 8, 8⟩, ⟨8, 7, 8, 10⟩, ⟨8, 6, 8, 12⟩, ⟨8, 12, 7, 2⟩, ⟨8, 12, 6, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 12, 4, 8⟩, ⟨8, 12, 3, 10⟩, ⟨8, 12, 2, 12⟩]
  exact AllWinning.cons node_14366 (AllWinning.cons node_13333 (AllWinning.cons node_12317 (AllWinning.cons node_11269 (AllWinning.cons node_10135 (AllWinning.cons node_9091 (AllWinning.cons node_14430 (AllWinning.cons node_13459 (AllWinning.cons node_12517 (AllWinning.cons node_11525 (AllWinning.cons node_10518 (AllWinning.cons node_9489 (AllWinning.cons node_14433 (AllWinning.cons node_13467 (AllWinning.cons node_12529 (AllWinning.cons node_11539 (AllWinning.cons node_10541 (AllWinning.cons node_9508 (AllWinning.nil))))))))))))))))))

theorem node_15361 : Outcome ⟨8, 12, 8, 12⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 24⟩) (by decide) node_4401

theorem node_15362 : Outcome ⟨8, 13, 7, 2⟩ true :=
  Outcome.win (q := ⟨6, 13, 7, 4⟩) (by decide) node_13337

theorem node_15363 : Outcome ⟨8, 13, 7, 12⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 14⟩) (by decide) node_8535

theorem node_15364 : Outcome ⟨8, 13, 7, 14⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 14⟩) (by decide) node_8535

theorem node_15365 : Outcome ⟨8, 14, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 14, 6, 2⟩, ⟨6, 14, 6, 4⟩, ⟨8, 13, 6, 2⟩, ⟨8, 12, 6, 4⟩, ⟨8, 14, 5, 2⟩, ⟨8, 14, 4, 4⟩]
  exact AllWinning.cons node_14371 (AllWinning.cons node_13341 (AllWinning.cons node_14437 (AllWinning.cons node_13467 (AllWinning.cons node_14440 (AllWinning.cons node_13472 (AllWinning.nil))))))

theorem node_15366 : Outcome ⟨8, 14, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 14, 6, 2⟩, ⟨6, 14, 6, 4⟩, ⟨5, 14, 6, 6⟩, ⟨4, 14, 6, 8⟩, ⟨8, 13, 6, 2⟩, ⟨8, 12, 6, 4⟩, ⟨8, 11, 6, 6⟩, ⟨8, 10, 6, 8⟩, ⟨8, 14, 5, 2⟩, ⟨8, 14, 4, 4⟩, ⟨8, 14, 3, 6⟩, ⟨8, 14, 2, 8⟩]
  exact AllWinning.cons node_14371 (AllWinning.cons node_13341 (AllWinning.cons node_12322 (AllWinning.cons node_11275 (AllWinning.cons node_14437 (AllWinning.cons node_13467 (AllWinning.cons node_12524 (AllWinning.cons node_11531 (AllWinning.cons node_14440 (AllWinning.cons node_13472 (AllWinning.cons node_12534 (AllWinning.cons node_11544 (AllWinning.nil))))))))))))

theorem node_15367 : Outcome ⟨8, 14, 6, 10⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 14⟩) (by decide) node_8547

theorem node_15368 : Outcome ⟨8, 15, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.nil))))))

theorem node_15369 : Outcome ⟨8, 15, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.nil))))))))))))

theorem node_15370 : Outcome ⟨8, 15, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil)))))))))))))))))

theorem node_15371 : Outcome ⟨8, 15, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨1, 15, 5, 14⟩, ⟨0, 15, 5, 16⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 8, 5, 14⟩, ⟨8, 7, 5, 16⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_8047 (AllWinning.cons node_7009 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_8556 (AllWinning.cons node_7565 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil)))))))))))))))))))))

theorem node_15372 : Outcome ⟨8, 15, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨1, 15, 5, 14⟩, ⟨0, 15, 5, 16⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 8, 5, 14⟩, ⟨8, 7, 5, 16⟩, ⟨8, 6, 5, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_8047 (AllWinning.cons node_7009 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_8556 (AllWinning.cons node_7565 (AllWinning.cons node_6645 (AllWinning.cons node_5799 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil)))))))))))))))))))))))

theorem node_15373 : Outcome ⟨8, 15, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨1, 15, 5, 14⟩, ⟨0, 15, 5, 16⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 8, 5, 14⟩, ⟨8, 7, 5, 16⟩, ⟨8, 6, 5, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 4, 5, 22⟩, ⟨8, 3, 5, 24⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_8047 (AllWinning.cons node_7009 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_8556 (AllWinning.cons node_7565 (AllWinning.cons node_6645 (AllWinning.cons node_5799 (AllWinning.cons node_5093 (AllWinning.cons node_4414 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil)))))))))))))))))))))))))

theorem node_15374 : Outcome ⟨8, 15, 5, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨1, 15, 5, 14⟩, ⟨0, 15, 5, 16⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 8, 5, 14⟩, ⟨8, 7, 5, 16⟩, ⟨8, 6, 5, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 4, 5, 22⟩, ⟨8, 3, 5, 24⟩, ⟨8, 2, 5, 26⟩, ⟨8, 1, 5, 28⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_8047 (AllWinning.cons node_7009 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_8556 (AllWinning.cons node_7565 (AllWinning.cons node_6645 (AllWinning.cons node_5799 (AllWinning.cons node_5093 (AllWinning.cons node_4414 (AllWinning.cons node_3770 (AllWinning.cons node_3217 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_15375 : Outcome ⟨8, 15, 5, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨1, 15, 5, 14⟩, ⟨0, 15, 5, 16⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 8, 5, 14⟩, ⟨8, 7, 5, 16⟩, ⟨8, 6, 5, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 4, 5, 22⟩, ⟨8, 3, 5, 24⟩, ⟨8, 2, 5, 26⟩, ⟨8, 1, 5, 28⟩, ⟨8, 0, 5, 30⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_8047 (AllWinning.cons node_7009 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_8556 (AllWinning.cons node_7565 (AllWinning.cons node_6645 (AllWinning.cons node_5799 (AllWinning.cons node_5093 (AllWinning.cons node_4414 (AllWinning.cons node_3770 (AllWinning.cons node_3217 (AllWinning.cons node_2725 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15376 : Outcome ⟨8, 15, 5, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨1, 15, 5, 14⟩, ⟨0, 15, 5, 16⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 8, 5, 14⟩, ⟨8, 7, 5, 16⟩, ⟨8, 6, 5, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 4, 5, 22⟩, ⟨8, 3, 5, 24⟩, ⟨8, 2, 5, 26⟩, ⟨8, 1, 5, 28⟩, ⟨8, 0, 5, 30⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_8047 (AllWinning.cons node_7009 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_8556 (AllWinning.cons node_7565 (AllWinning.cons node_6645 (AllWinning.cons node_5799 (AllWinning.cons node_5093 (AllWinning.cons node_4414 (AllWinning.cons node_3770 (AllWinning.cons node_3217 (AllWinning.cons node_2725 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15377 : Outcome ⟨8, 15, 5, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 15, 5, 2⟩, ⟨6, 15, 5, 4⟩, ⟨5, 15, 5, 6⟩, ⟨4, 15, 5, 8⟩, ⟨3, 15, 5, 10⟩, ⟨2, 15, 5, 12⟩, ⟨1, 15, 5, 14⟩, ⟨0, 15, 5, 16⟩, ⟨8, 14, 5, 2⟩, ⟨8, 13, 5, 4⟩, ⟨8, 12, 5, 6⟩, ⟨8, 11, 5, 8⟩, ⟨8, 10, 5, 10⟩, ⟨8, 9, 5, 12⟩, ⟨8, 8, 5, 14⟩, ⟨8, 7, 5, 16⟩, ⟨8, 6, 5, 18⟩, ⟨8, 5, 5, 20⟩, ⟨8, 4, 5, 22⟩, ⟨8, 3, 5, 24⟩, ⟨8, 2, 5, 26⟩, ⟨8, 1, 5, 28⟩, ⟨8, 0, 5, 30⟩, ⟨8, 15, 4, 2⟩, ⟨8, 15, 3, 4⟩, ⟨8, 15, 2, 6⟩, ⟨8, 15, 1, 8⟩, ⟨8, 15, 0, 10⟩]
  exact AllWinning.cons node_14376 (AllWinning.cons node_13346 (AllWinning.cons node_12324 (AllWinning.cons node_11279 (AllWinning.cons node_10149 (AllWinning.cons node_9104 (AllWinning.cons node_8047 (AllWinning.cons node_7009 (AllWinning.cons node_14440 (AllWinning.cons node_13471 (AllWinning.cons node_12529 (AllWinning.cons node_11536 (AllWinning.cons node_10532 (AllWinning.cons node_9498 (AllWinning.cons node_8556 (AllWinning.cons node_7565 (AllWinning.cons node_6645 (AllWinning.cons node_5799 (AllWinning.cons node_5093 (AllWinning.cons node_4414 (AllWinning.cons node_3770 (AllWinning.cons node_3217 (AllWinning.cons node_2725 (AllWinning.cons node_14441 (AllWinning.cons node_13476 (AllWinning.cons node_12537 (AllWinning.cons node_11547 (AllWinning.cons node_10550 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15378 : Outcome ⟨8, 16, 4, 2⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 2⟩) (by decide) node_14443

theorem node_15379 : Outcome ⟨8, 17, 3, 2⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 2⟩) (by decide) node_14443

theorem node_15380 : Outcome ⟨8, 17, 3, 12⟩ true :=
  Outcome.win (q := ⟨8, 16, 3, 2⟩) (by decide) node_14443

theorem node_15381 : Outcome ⟨8, 18, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 2⟩) (by decide) node_14383

theorem node_15382 : Outcome ⟨8, 18, 2, 12⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 2⟩) (by decide) node_14383

theorem node_15383 : Outcome ⟨8, 18, 2, 16⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 2⟩) (by decide) node_14383

theorem node_15384 : Outcome ⟨8, 19, 1, 2⟩ true :=
  Outcome.win (q := ⟨8, 18, 1, 2⟩) (by decide) node_14453

theorem node_15385 : Outcome ⟨8, 19, 1, 8⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 14⟩) (by decide) node_8575

theorem node_15386 : Outcome ⟨8, 20, 0, 8⟩ true :=
  Outcome.win (q := ⟨7, 20, 0, 2⟩) (by decide) node_14393

theorem node_15387 : Outcome ⟨8, 20, 0, 14⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 24⟩) (by decide) node_4442

theorem node_15388 : Outcome ⟨9, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 17, 4⟩) (by decide) node_13489

theorem node_15389 : Outcome ⟨9, 0, 19, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 6⟩) (by decide) node_12344

theorem node_15390 : Outcome ⟨9, 0, 19, 20⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 20⟩) (by decide) node_5828

theorem node_15391 : Outcome ⟨9, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 18, 2⟩) (by decide) node_14402

theorem node_15392 : Outcome ⟨9, 2, 17, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 17, 4⟩) (by decide) node_13489

theorem node_15393 : Outcome ⟨9, 2, 17, 4⟩ true :=
  Outcome.win (q := ⟨9, 0, 17, 4⟩) (by decide) node_13489

theorem node_15394 : Outcome ⟨9, 2, 17, 6⟩ true :=
  Outcome.win (q := ⟨9, 0, 17, 4⟩) (by decide) node_13489

theorem node_15395 : Outcome ⟨9, 2, 17, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 17, 4⟩) (by decide) node_13489

theorem node_15396 : Outcome ⟨9, 3, 16, 2⟩ true :=
  Outcome.win (q := ⟨8, 3, 16, 2⟩) (by decide) node_14407

theorem node_15397 : Outcome ⟨9, 3, 16, 8⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 8⟩) (by decide) node_11564

theorem node_15398 : Outcome ⟨9, 4, 15, 2⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 4⟩) (by decide) node_13496

theorem node_15399 : Outcome ⟨9, 4, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 4⟩) (by decide) node_13496

theorem node_15400 : Outcome ⟨9, 4, 15, 10⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 4⟩) (by decide) node_13496

theorem node_15401 : Outcome ⟨9, 5, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 14, 2⟩, ⟨7, 5, 14, 4⟩, ⟨6, 5, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨9, 4, 14, 2⟩, ⟨9, 3, 14, 4⟩, ⟨9, 2, 14, 6⟩, ⟨9, 1, 14, 8⟩, ⟨9, 5, 13, 2⟩, ⟨9, 5, 12, 4⟩, ⟨9, 5, 11, 6⟩, ⟨9, 5, 10, 8⟩]
  exact AllWinning.cons node_14417 (AllWinning.cons node_13374 (AllWinning.cons node_12363 (AllWinning.cons node_11314 (AllWinning.cons node_14472 (AllWinning.cons node_13502 (AllWinning.cons node_12554 (AllWinning.cons node_11558 (AllWinning.cons node_14475 (AllWinning.cons node_13507 (AllWinning.cons node_12559 (AllWinning.cons node_11575 (AllWinning.nil))))))))))))

theorem node_15402 : Outcome ⟨9, 5, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 14, 2⟩, ⟨7, 5, 14, 4⟩, ⟨6, 5, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨4, 5, 14, 10⟩, ⟨3, 5, 14, 12⟩, ⟨9, 4, 14, 2⟩, ⟨9, 3, 14, 4⟩, ⟨9, 2, 14, 6⟩, ⟨9, 1, 14, 8⟩, ⟨9, 0, 14, 10⟩, ⟨9, 5, 13, 2⟩, ⟨9, 5, 12, 4⟩, ⟨9, 5, 11, 6⟩, ⟨9, 5, 10, 8⟩, ⟨9, 5, 9, 10⟩, ⟨9, 5, 8, 12⟩]
  exact AllWinning.cons node_14417 (AllWinning.cons node_13374 (AllWinning.cons node_12363 (AllWinning.cons node_11314 (AllWinning.cons node_10188 (AllWinning.cons node_9142 (AllWinning.cons node_14472 (AllWinning.cons node_13502 (AllWinning.cons node_12554 (AllWinning.cons node_11558 (AllWinning.cons node_10555 (AllWinning.cons node_14475 (AllWinning.cons node_13507 (AllWinning.cons node_12559 (AllWinning.cons node_11575 (AllWinning.cons node_10572 (AllWinning.cons node_9532 (AllWinning.nil)))))))))))))))))

theorem node_15403 : Outcome ⟨9, 5, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 14, 2⟩, ⟨7, 5, 14, 4⟩, ⟨6, 5, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨4, 5, 14, 10⟩, ⟨3, 5, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨1, 5, 14, 16⟩, ⟨9, 4, 14, 2⟩, ⟨9, 3, 14, 4⟩, ⟨9, 2, 14, 6⟩, ⟨9, 1, 14, 8⟩, ⟨9, 0, 14, 10⟩, ⟨9, 5, 13, 2⟩, ⟨9, 5, 12, 4⟩, ⟨9, 5, 11, 6⟩, ⟨9, 5, 10, 8⟩, ⟨9, 5, 9, 10⟩, ⟨9, 5, 8, 12⟩, ⟨9, 5, 7, 14⟩, ⟨9, 5, 6, 16⟩]
  exact AllWinning.cons node_14417 (AllWinning.cons node_13374 (AllWinning.cons node_12363 (AllWinning.cons node_11314 (AllWinning.cons node_10188 (AllWinning.cons node_9142 (AllWinning.cons node_8085 (AllWinning.cons node_7055 (AllWinning.cons node_14472 (AllWinning.cons node_13502 (AllWinning.cons node_12554 (AllWinning.cons node_11558 (AllWinning.cons node_10555 (AllWinning.cons node_14475 (AllWinning.cons node_13507 (AllWinning.cons node_12559 (AllWinning.cons node_11575 (AllWinning.cons node_10572 (AllWinning.cons node_9532 (AllWinning.cons node_8601 (AllWinning.cons node_7605 (AllWinning.nil)))))))))))))))))))))

theorem node_15404 : Outcome ⟨9, 5, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 14, 2⟩, ⟨7, 5, 14, 4⟩, ⟨6, 5, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨4, 5, 14, 10⟩, ⟨3, 5, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨1, 5, 14, 16⟩, ⟨0, 5, 14, 18⟩, ⟨9, 4, 14, 2⟩, ⟨9, 3, 14, 4⟩, ⟨9, 2, 14, 6⟩, ⟨9, 1, 14, 8⟩, ⟨9, 0, 14, 10⟩, ⟨9, 5, 13, 2⟩, ⟨9, 5, 12, 4⟩, ⟨9, 5, 11, 6⟩, ⟨9, 5, 10, 8⟩, ⟨9, 5, 9, 10⟩, ⟨9, 5, 8, 12⟩, ⟨9, 5, 7, 14⟩, ⟨9, 5, 6, 16⟩, ⟨9, 5, 5, 18⟩, ⟨9, 5, 4, 20⟩]
  exact AllWinning.cons node_14417 (AllWinning.cons node_13374 (AllWinning.cons node_12363 (AllWinning.cons node_11314 (AllWinning.cons node_10188 (AllWinning.cons node_9142 (AllWinning.cons node_8085 (AllWinning.cons node_7055 (AllWinning.cons node_6056 (AllWinning.cons node_14472 (AllWinning.cons node_13502 (AllWinning.cons node_12554 (AllWinning.cons node_11558 (AllWinning.cons node_10555 (AllWinning.cons node_14475 (AllWinning.cons node_13507 (AllWinning.cons node_12559 (AllWinning.cons node_11575 (AllWinning.cons node_10572 (AllWinning.cons node_9532 (AllWinning.cons node_8601 (AllWinning.cons node_7605 (AllWinning.cons node_6682 (AllWinning.cons node_5854 (AllWinning.nil))))))))))))))))))))))))

theorem node_15405 : Outcome ⟨9, 5, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 14, 2⟩, ⟨7, 5, 14, 4⟩, ⟨6, 5, 14, 6⟩, ⟨5, 5, 14, 8⟩, ⟨4, 5, 14, 10⟩, ⟨3, 5, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨1, 5, 14, 16⟩, ⟨0, 5, 14, 18⟩, ⟨9, 4, 14, 2⟩, ⟨9, 3, 14, 4⟩, ⟨9, 2, 14, 6⟩, ⟨9, 1, 14, 8⟩, ⟨9, 0, 14, 10⟩, ⟨9, 5, 13, 2⟩, ⟨9, 5, 12, 4⟩, ⟨9, 5, 11, 6⟩, ⟨9, 5, 10, 8⟩, ⟨9, 5, 9, 10⟩, ⟨9, 5, 8, 12⟩, ⟨9, 5, 7, 14⟩, ⟨9, 5, 6, 16⟩, ⟨9, 5, 5, 18⟩, ⟨9, 5, 4, 20⟩, ⟨9, 5, 3, 22⟩, ⟨9, 5, 2, 24⟩]
  exact AllWinning.cons node_14417 (AllWinning.cons node_13374 (AllWinning.cons node_12363 (AllWinning.cons node_11314 (AllWinning.cons node_10188 (AllWinning.cons node_9142 (AllWinning.cons node_8085 (AllWinning.cons node_7055 (AllWinning.cons node_6056 (AllWinning.cons node_14472 (AllWinning.cons node_13502 (AllWinning.cons node_12554 (AllWinning.cons node_11558 (AllWinning.cons node_10555 (AllWinning.cons node_14475 (AllWinning.cons node_13507 (AllWinning.cons node_12559 (AllWinning.cons node_11575 (AllWinning.cons node_10572 (AllWinning.cons node_9532 (AllWinning.cons node_8601 (AllWinning.cons node_7605 (AllWinning.cons node_6682 (AllWinning.cons node_5854 (AllWinning.cons node_5135 (AllWinning.cons node_4462 (AllWinning.nil))))))))))))))))))))))))))

theorem node_15406 : Outcome ⟨9, 6, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 4⟩) (by decide) node_13377

theorem node_15407 : Outcome ⟨9, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 4⟩) (by decide) node_13377

theorem node_15408 : Outcome ⟨9, 6, 13, 8⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 4⟩) (by decide) node_13377

theorem node_15409 : Outcome ⟨9, 6, 13, 10⟩ true :=
  Outcome.win (q := ⟨7, 6, 13, 4⟩) (by decide) node_13377

theorem node_15410 : Outcome ⟨9, 7, 12, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 4⟩) (by decide) node_13382

theorem node_15411 : Outcome ⟨9, 7, 12, 6⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 8⟩) (by decide) node_11564

theorem node_15412 : Outcome ⟨9, 7, 12, 12⟩ true :=
  Outcome.win (q := ⟨9, 3, 12, 8⟩) (by decide) node_11564

theorem node_15413 : Outcome ⟨9, 8, 11, 2⟩ true :=
  Outcome.win (q := ⟨7, 8, 11, 4⟩) (by decide) node_13388

theorem node_15414 : Outcome ⟨9, 8, 11, 6⟩ true :=
  Outcome.win (q := ⟨7, 8, 11, 4⟩) (by decide) node_13388

theorem node_15415 : Outcome ⟨9, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨9, 9, 8, 4⟩) (by decide) node_13517

theorem node_15416 : Outcome ⟨9, 9, 10, 10⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 20⟩) (by decide) node_5878

theorem node_15417 : Outcome ⟨9, 9, 10, 20⟩ true :=
  Outcome.win (q := ⟨9, 9, 0, 20⟩) (by decide) node_5878

theorem node_15418 : Outcome ⟨9, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨9, 8, 9, 4⟩) (by decide) node_13514

theorem node_15419 : Outcome ⟨9, 10, 9, 10⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 20⟩) (by decide) node_5828

theorem node_15420 : Outcome ⟨9, 10, 9, 20⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 20⟩) (by decide) node_5828

theorem node_15421 : Outcome ⟨9, 11, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 4⟩) (by decide) node_13397

theorem node_15422 : Outcome ⟨9, 11, 8, 6⟩ true :=
  Outcome.win (q := ⟨7, 11, 8, 4⟩) (by decide) node_13397

theorem node_15423 : Outcome ⟨9, 12, 7, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 4⟩) (by decide) node_13402

theorem node_15424 : Outcome ⟨9, 12, 7, 6⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 8⟩) (by decide) node_11597

theorem node_15425 : Outcome ⟨9, 12, 7, 12⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 8⟩) (by decide) node_11597

theorem node_15426 : Outcome ⟨9, 13, 6, 2⟩ true :=
  Outcome.win (q := ⟨7, 13, 6, 4⟩) (by decide) node_13408

theorem node_15427 : Outcome ⟨9, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨7, 13, 6, 4⟩) (by decide) node_13408

theorem node_15428 : Outcome ⟨9, 13, 6, 8⟩ true :=
  Outcome.win (q := ⟨7, 13, 6, 4⟩) (by decide) node_13408

theorem node_15429 : Outcome ⟨9, 13, 6, 10⟩ true :=
  Outcome.win (q := ⟨7, 13, 6, 4⟩) (by decide) node_13408

theorem node_15430 : Outcome ⟨9, 14, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 14, 5, 2⟩, ⟨7, 14, 5, 4⟩, ⟨6, 14, 5, 6⟩, ⟨5, 14, 5, 8⟩, ⟨9, 13, 5, 2⟩, ⟨9, 12, 5, 4⟩, ⟨9, 11, 5, 6⟩, ⟨9, 10, 5, 8⟩, ⟨9, 14, 4, 2⟩, ⟨9, 14, 3, 4⟩, ⟨9, 14, 2, 6⟩, ⟨9, 14, 1, 8⟩]
  exact AllWinning.cons node_14440 (AllWinning.cons node_13412 (AllWinning.cons node_12398 (AllWinning.cons node_11347 (AllWinning.cons node_14495 (AllWinning.cons node_13526 (AllWinning.cons node_12577 (AllWinning.cons node_11589 (AllWinning.cons node_14498 (AllWinning.cons node_13529 (AllWinning.cons node_12583 (AllWinning.cons node_11606 (AllWinning.nil))))))))))))

theorem node_15431 : Outcome ⟨9, 14, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 14, 5, 2⟩, ⟨7, 14, 5, 4⟩, ⟨6, 14, 5, 6⟩, ⟨5, 14, 5, 8⟩, ⟨4, 14, 5, 10⟩, ⟨3, 14, 5, 12⟩, ⟨9, 13, 5, 2⟩, ⟨9, 12, 5, 4⟩, ⟨9, 11, 5, 6⟩, ⟨9, 10, 5, 8⟩, ⟨9, 9, 5, 10⟩, ⟨9, 8, 5, 12⟩, ⟨9, 14, 4, 2⟩, ⟨9, 14, 3, 4⟩, ⟨9, 14, 2, 6⟩, ⟨9, 14, 1, 8⟩, ⟨9, 14, 0, 10⟩]
  exact AllWinning.cons node_14440 (AllWinning.cons node_13412 (AllWinning.cons node_12398 (AllWinning.cons node_11347 (AllWinning.cons node_10226 (AllWinning.cons node_9179 (AllWinning.cons node_14495 (AllWinning.cons node_13526 (AllWinning.cons node_12577 (AllWinning.cons node_11589 (AllWinning.cons node_10585 (AllWinning.cons node_9545 (AllWinning.cons node_14498 (AllWinning.cons node_13529 (AllWinning.cons node_12583 (AllWinning.cons node_11606 (AllWinning.cons node_10601 (AllWinning.nil)))))))))))))))))

end RQ9F1
