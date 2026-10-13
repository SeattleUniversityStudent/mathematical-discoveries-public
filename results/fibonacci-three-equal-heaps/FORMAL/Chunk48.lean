import Chunk47
set_option autoImplicit false
namespace RQ9F1

theorem node_11259 : Outcome ⟨4, 9, 11, 14⟩ true :=
  Outcome.win (q := ⟨4, 9, 10, 2⟩) (by decide) node_10204

theorem node_11260 : Outcome ⟨4, 9, 11, 18⟩ true :=
  Outcome.win (q := ⟨4, 9, 10, 2⟩) (by decide) node_10204

theorem node_11261 : Outcome ⟨4, 10, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 10, 2⟩) (by decide) node_10126

theorem node_11262 : Outcome ⟨4, 10, 10, 6⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 8⟩) (by decide) node_6983

theorem node_11263 : Outcome ⟨4, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 9, 2⟩) (by decide) node_10207

theorem node_11264 : Outcome ⟨4, 11, 9, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 9, 2⟩) (by decide) node_10207

theorem node_11265 : Outcome ⟨4, 11, 9, 10⟩ true :=
  Outcome.win (q := ⟨4, 10, 9, 2⟩) (by decide) node_10207

theorem node_11266 : Outcome ⟨4, 11, 9, 14⟩ true :=
  Outcome.win (q := ⟨4, 10, 9, 2⟩) (by decide) node_10207

theorem node_11267 : Outcome ⟨4, 11, 9, 18⟩ true :=
  Outcome.win (q := ⟨4, 10, 9, 2⟩) (by decide) node_10207

theorem node_11268 : Outcome ⟨4, 12, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 8, 2⟩, ⟨2, 12, 8, 4⟩, ⟨4, 11, 8, 2⟩, ⟨4, 10, 8, 4⟩, ⟨4, 12, 7, 2⟩, ⟨4, 12, 6, 4⟩]
  exact AllWinning.cons node_10133 (AllWinning.cons node_9090 (AllWinning.cons node_10210 (AllWinning.cons node_9236 (AllWinning.cons node_10215 (AllWinning.cons node_9245 (AllWinning.nil))))))

theorem node_11269 : Outcome ⟨4, 12, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 6⟩) (by decide) node_8028

theorem node_11270 : Outcome ⟨4, 12, 8, 10⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 6⟩) (by decide) node_8028

theorem node_11271 : Outcome ⟨4, 13, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 13, 7, 2⟩) (by decide) node_10136

theorem node_11272 : Outcome ⟨4, 13, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 6⟩) (by decide) node_8269

theorem node_11273 : Outcome ⟨4, 13, 7, 10⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 16⟩) (by decide) node_4177

theorem node_11274 : Outcome ⟨4, 14, 6, 2⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 2⟩) (by decide) node_10140

theorem node_11275 : Outcome ⟨4, 14, 6, 8⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 8⟩) (by decide) node_7316

theorem node_11276 : Outcome ⟨4, 14, 6, 18⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 8⟩) (by decide) node_7316

theorem node_11277 : Outcome ⟨4, 15, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 5, 4⟩) (by decide) node_9102

theorem node_11278 : Outcome ⟨4, 15, 5, 4⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 8⟩) (by decide) node_7343

theorem node_11279 : Outcome ⟨4, 15, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 16⟩) (by decide) node_4194

theorem node_11280 : Outcome ⟨4, 15, 5, 10⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 16⟩) (by decide) node_4194

theorem node_11281 : Outcome ⟨4, 16, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 16, 4, 2⟩, ⟨2, 16, 4, 4⟩, ⟨4, 15, 4, 2⟩, ⟨4, 14, 4, 4⟩, ⟨4, 16, 3, 2⟩, ⟨4, 16, 2, 4⟩]
  exact AllWinning.cons node_10151 (AllWinning.cons node_9105 (AllWinning.cons node_10228 (AllWinning.cons node_9252 (AllWinning.cons node_10231 (AllWinning.cons node_9258 (AllWinning.nil))))))

theorem node_11282 : Outcome ⟨4, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 6⟩) (by decide) node_8269

theorem node_11283 : Outcome ⟨4, 16, 4, 10⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 6⟩) (by decide) node_8269

theorem node_11284 : Outcome ⟨4, 17, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 3, 2⟩, ⟨2, 17, 3, 4⟩, ⟨4, 16, 3, 2⟩, ⟨4, 15, 3, 4⟩, ⟨4, 17, 2, 2⟩, ⟨4, 17, 1, 4⟩]
  exact AllWinning.cons node_10154 (AllWinning.cons node_9110 (AllWinning.cons node_10231 (AllWinning.cons node_9256 (AllWinning.cons node_10234 (AllWinning.cons node_9263 (AllWinning.nil))))))

theorem node_11285 : Outcome ⟨4, 17, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 6⟩) (by decide) node_8283

theorem node_11286 : Outcome ⟨4, 17, 3, 10⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 6⟩) (by decide) node_8283

theorem node_11287 : Outcome ⟨4, 17, 3, 20⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 6⟩) (by decide) node_8283

theorem node_11288 : Outcome ⟨4, 18, 2, 2⟩ true :=
  Outcome.win (q := ⟨2, 18, 2, 4⟩) (by decide) node_9115

theorem node_11289 : Outcome ⟨4, 18, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 8⟩) (by decide) node_7336

theorem node_11290 : Outcome ⟨4, 18, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 8⟩) (by decide) node_7336

theorem node_11291 : Outcome ⟨4, 18, 2, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 34⟩) (by decide) node_632

theorem node_11292 : Outcome ⟨4, 18, 2, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 34⟩) (by decide) node_632

theorem node_11293 : Outcome ⟨4, 19, 1, 2⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 2⟩) (by decide) node_10160

theorem node_11294 : Outcome ⟨4, 19, 1, 16⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 8⟩) (by decide) node_7343

theorem node_11295 : Outcome ⟨4, 20, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 20, 0, 4⟩) (by decide) node_9121

theorem node_11296 : Outcome ⟨4, 20, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 6⟩) (by decide) node_8283

theorem node_11297 : Outcome ⟨4, 20, 0, 10⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 6⟩) (by decide) node_8283

theorem node_11298 : Outcome ⟨5, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 2⟩) (by decide) node_10246

theorem node_11299 : Outcome ⟨5, 0, 19, 20⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 28⟩) (by decide) node_1417

theorem node_11300 : Outcome ⟨5, 0, 19, 28⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 28⟩) (by decide) node_1417

theorem node_11301 : Outcome ⟨5, 1, 18, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 18, 2⟩) (by decide) node_10170

theorem node_11302 : Outcome ⟨5, 1, 18, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 18, 2⟩) (by decide) node_10170

theorem node_11303 : Outcome ⟨5, 1, 18, 22⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 18⟩) (by decide) node_3642

theorem node_11304 : Outcome ⟨5, 2, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 15, 4⟩) (by decide) node_9278

theorem node_11305 : Outcome ⟨5, 2, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 8⟩) (by decide) node_7036

theorem node_11306 : Outcome ⟨5, 2, 17, 10⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 14⟩) (by decide) node_4936

theorem node_11307 : Outcome ⟨5, 2, 17, 12⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 14⟩) (by decide) node_4936

theorem node_11308 : Outcome ⟨5, 3, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 16, 2⟩, ⟨3, 3, 16, 4⟩, ⟨2, 3, 16, 6⟩, ⟨1, 3, 16, 8⟩, ⟨5, 2, 16, 2⟩, ⟨5, 1, 16, 4⟩, ⟨5, 0, 16, 6⟩, ⟨5, 3, 15, 2⟩, ⟨5, 3, 14, 4⟩, ⟨5, 3, 13, 6⟩, ⟨5, 3, 12, 8⟩]
  exact AllWinning.cons node_10180 (AllWinning.cons node_9135 (AllWinning.cons node_8076 (AllWinning.cons node_7042 (AllWinning.cons node_10258 (AllWinning.cons node_9275 (AllWinning.cons node_8288 (AllWinning.cons node_10260 (AllWinning.cons node_9282 (AllWinning.cons node_8298 (AllWinning.cons node_7363 (AllWinning.nil)))))))))))

theorem node_11309 : Outcome ⟨5, 3, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 10⟩) (by decide) node_6046

theorem node_11310 : Outcome ⟨5, 4, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 15, 4⟩) (by decide) node_9278

theorem node_11311 : Outcome ⟨5, 4, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 8⟩) (by decide) node_7048

theorem node_11312 : Outcome ⟨5, 4, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 16⟩) (by decide) node_4243

theorem node_11313 : Outcome ⟨5, 4, 15, 10⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 16⟩) (by decide) node_4243

theorem node_11314 : Outcome ⟨5, 5, 14, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 2⟩) (by decide) node_10268

theorem node_11315 : Outcome ⟨5, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 2⟩) (by decide) node_10268

theorem node_11316 : Outcome ⟨5, 6, 13, 18⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 2⟩) (by decide) node_10268

theorem node_11317 : Outcome ⟨5, 7, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 7, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨5, 6, 12, 2⟩, ⟨5, 5, 12, 4⟩, ⟨5, 7, 11, 2⟩, ⟨5, 7, 10, 4⟩]
  exact AllWinning.cons node_10194 (AllWinning.cons node_9147 (AllWinning.cons node_10274 (AllWinning.cons node_9288 (AllWinning.cons node_10278 (AllWinning.cons node_9295 (AllWinning.nil))))))

theorem node_11318 : Outcome ⟨5, 7, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 6⟩) (by decide) node_8091

theorem node_11319 : Outcome ⟨5, 7, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 6⟩) (by decide) node_8091

theorem node_11320 : Outcome ⟨5, 7, 12, 10⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 16⟩) (by decide) node_4260

theorem node_11321 : Outcome ⟨5, 7, 12, 20⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 16⟩) (by decide) node_4260

theorem node_11322 : Outcome ⟨5, 7, 12, 22⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 16⟩) (by decide) node_4260

theorem node_11323 : Outcome ⟨5, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 10, 2⟩) (by decide) node_10283

theorem node_11324 : Outcome ⟨5, 8, 11, 6⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 10⟩) (by decide) node_6436

theorem node_11325 : Outcome ⟨5, 8, 11, 8⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 10⟩) (by decide) node_6436

theorem node_11326 : Outcome ⟨5, 8, 11, 10⟩ true :=
  Outcome.win (q := ⟨5, 3, 11, 10⟩) (by decide) node_6436

theorem node_11327 : Outcome ⟨5, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 9, 10, 2⟩) (by decide) node_10204

theorem node_11328 : Outcome ⟨5, 9, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 9, 10, 2⟩) (by decide) node_10204

theorem node_11329 : Outcome ⟨5, 9, 10, 8⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 14⟩) (by decide) node_4936

theorem node_11330 : Outcome ⟨5, 9, 10, 20⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 18⟩) (by decide) node_3680

theorem node_11331 : Outcome ⟨5, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 9, 2⟩) (by decide) node_10207

theorem node_11332 : Outcome ⟨5, 10, 9, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 9, 2⟩) (by decide) node_10207

theorem node_11333 : Outcome ⟨5, 10, 9, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 14⟩) (by decide) node_4974

theorem node_11334 : Outcome ⟨5, 10, 9, 20⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 18⟩) (by decide) node_3642

theorem node_11335 : Outcome ⟨5, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 8, 2⟩) (by decide) node_10293

theorem node_11336 : Outcome ⟨5, 11, 8, 6⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 10⟩) (by decide) node_6469

theorem node_11337 : Outcome ⟨5, 11, 8, 8⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 10⟩) (by decide) node_6469

theorem node_11338 : Outcome ⟨5, 11, 8, 10⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 10⟩) (by decide) node_6469

theorem node_11339 : Outcome ⟨5, 12, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 7, 2⟩, ⟨3, 12, 7, 4⟩, ⟨5, 11, 7, 2⟩, ⟨5, 10, 7, 4⟩, ⟨5, 12, 6, 2⟩, ⟨5, 12, 5, 4⟩]
  exact AllWinning.cons node_10215 (AllWinning.cons node_9170 (AllWinning.cons node_10299 (AllWinning.cons node_9308 (AllWinning.cons node_10304 (AllWinning.cons node_9316 (AllWinning.nil))))))

theorem node_11340 : Outcome ⟨5, 12, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 6⟩) (by decide) node_8117

theorem node_11341 : Outcome ⟨5, 12, 7, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 6⟩) (by decide) node_8117

theorem node_11342 : Outcome ⟨5, 12, 7, 10⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 16⟩) (by decide) node_4243

theorem node_11343 : Outcome ⟨5, 12, 7, 20⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 16⟩) (by decide) node_4243

theorem node_11344 : Outcome ⟨5, 12, 7, 22⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 16⟩) (by decide) node_4243

theorem node_11345 : Outcome ⟨5, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 2⟩) (by decide) node_10308

theorem node_11346 : Outcome ⟨5, 13, 6, 18⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 2⟩) (by decide) node_10308

theorem node_11347 : Outcome ⟨5, 14, 5, 8⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 2⟩) (by decide) node_10308

theorem node_11348 : Outcome ⟨5, 15, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 2, 4⟩) (by decide) node_9326

theorem node_11349 : Outcome ⟨5, 15, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 8⟩) (by decide) node_7090

theorem node_11350 : Outcome ⟨5, 15, 4, 8⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 16⟩) (by decide) node_4260

theorem node_11351 : Outcome ⟨5, 15, 4, 10⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 16⟩) (by decide) node_4260

theorem node_11352 : Outcome ⟨5, 16, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 16, 3, 2⟩, ⟨3, 16, 3, 4⟩, ⟨2, 16, 3, 6⟩, ⟨1, 16, 3, 8⟩, ⟨5, 15, 3, 2⟩, ⟨5, 14, 3, 4⟩, ⟨5, 13, 3, 6⟩, ⟨5, 12, 3, 8⟩, ⟨5, 16, 2, 2⟩, ⟨5, 16, 1, 4⟩, ⟨5, 16, 0, 6⟩]
  exact AllWinning.cons node_10231 (AllWinning.cons node_9184 (AllWinning.cons node_8132 (AllWinning.cons node_7096 (AllWinning.cons node_10319 (AllWinning.cons node_9323 (AllWinning.cons node_8331 (AllWinning.cons node_7395 (AllWinning.cons node_10322 (AllWinning.cons node_9330 (AllWinning.cons node_8341 (AllWinning.nil)))))))))))

theorem node_11353 : Outcome ⟨5, 16, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 10⟩) (by decide) node_6104

theorem node_11354 : Outcome ⟨5, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 2, 4⟩) (by decide) node_9326

theorem node_11355 : Outcome ⟨5, 17, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 8⟩) (by decide) node_7102

theorem node_11356 : Outcome ⟨5, 17, 2, 10⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 14⟩) (by decide) node_4974

theorem node_11357 : Outcome ⟨5, 17, 2, 12⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 14⟩) (by decide) node_4974

theorem node_11358 : Outcome ⟨5, 18, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 18, 1, 2⟩) (by decide) node_10239

theorem node_11359 : Outcome ⟨5, 18, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 18, 1, 2⟩) (by decide) node_10239

theorem node_11360 : Outcome ⟨5, 18, 1, 22⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 18⟩) (by decide) node_3680

theorem node_11361 : Outcome ⟨5, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 2⟩) (by decide) node_10329

theorem node_11362 : Outcome ⟨5, 19, 0, 20⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 28⟩) (by decide) node_1451

theorem node_11363 : Outcome ⟨5, 19, 0, 28⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 28⟩) (by decide) node_1451

theorem node_11364 : Outcome ⟨6, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 2⟩) (by decide) node_10246

theorem node_11365 : Outcome ⟨6, 0, 18, 8⟩ true :=
  Outcome.win (q := ⟨5, 0, 18, 2⟩) (by decide) node_10246

theorem node_11366 : Outcome ⟨6, 0, 18, 20⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 24⟩) (by decide) node_2202

theorem node_11367 : Outcome ⟨6, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 17, 2⟩) (by decide) node_10253

theorem node_11368 : Outcome ⟨6, 1, 17, 14⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 28⟩) (by decide) node_1468

theorem node_11369 : Outcome ⟨6, 1, 17, 16⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 28⟩) (by decide) node_1468

theorem node_11370 : Outcome ⟨6, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 2⟩) (by decide) node_10339

theorem node_11371 : Outcome ⟨6, 2, 16, 8⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 10⟩) (by decide) node_6500

theorem node_11372 : Outcome ⟨6, 2, 16, 20⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 10⟩) (by decide) node_6500

theorem node_11373 : Outcome ⟨6, 3, 15, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 2⟩) (by decide) node_10350

theorem node_11374 : Outcome ⟨6, 3, 15, 16⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 28⟩) (by decide) node_1488

theorem node_11375 : Outcome ⟨6, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 2⟩) (by decide) node_10350

theorem node_11376 : Outcome ⟨6, 4, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 8⟩) (by decide) node_7132

theorem node_11377 : Outcome ⟨6, 4, 14, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 8⟩) (by decide) node_7132

theorem node_11378 : Outcome ⟨6, 4, 14, 26⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 8⟩) (by decide) node_7132

theorem node_11379 : Outcome ⟨6, 5, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 2⟩) (by decide) node_10268

theorem node_11380 : Outcome ⟨6, 5, 13, 18⟩ true :=
  Outcome.win (q := ⟨5, 5, 13, 2⟩) (by decide) node_10268

theorem node_11381 : Outcome ⟨6, 6, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 12, 2⟩, ⟨4, 6, 12, 4⟩, ⟨6, 5, 12, 2⟩, ⟨6, 4, 12, 4⟩, ⟨6, 6, 11, 2⟩, ⟨6, 6, 10, 4⟩]
  exact AllWinning.cons node_10274 (AllWinning.cons node_9218 (AllWinning.cons node_10360 (AllWinning.cons node_9352 (AllWinning.cons node_10364 (AllWinning.cons node_9359 (AllWinning.nil))))))

theorem node_11382 : Outcome ⟨6, 6, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 12, 2⟩, ⟨4, 6, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨2, 6, 12, 8⟩, ⟨6, 5, 12, 2⟩, ⟨6, 4, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨6, 2, 12, 8⟩, ⟨6, 6, 11, 2⟩, ⟨6, 6, 10, 4⟩, ⟨6, 6, 9, 6⟩, ⟨6, 6, 8, 8⟩]
  exact AllWinning.cons node_10274 (AllWinning.cons node_9218 (AllWinning.cons node_8169 (AllWinning.cons node_7141 (AllWinning.cons node_10360 (AllWinning.cons node_9352 (AllWinning.cons node_8354 (AllWinning.cons node_7420 (AllWinning.cons node_10364 (AllWinning.cons node_9359 (AllWinning.cons node_8364 (AllWinning.cons node_7443 (AllWinning.nil))))))))))))

theorem node_11383 : Outcome ⟨6, 6, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 12, 2⟩, ⟨4, 6, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨2, 6, 12, 8⟩, ⟨1, 6, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨6, 5, 12, 2⟩, ⟨6, 4, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨6, 2, 12, 8⟩, ⟨6, 1, 12, 10⟩, ⟨6, 0, 12, 12⟩, ⟨6, 6, 11, 2⟩, ⟨6, 6, 10, 4⟩, ⟨6, 6, 9, 6⟩, ⟨6, 6, 8, 8⟩, ⟨6, 6, 7, 10⟩, ⟨6, 6, 6, 12⟩]
  exact AllWinning.cons node_10274 (AllWinning.cons node_9218 (AllWinning.cons node_8169 (AllWinning.cons node_7141 (AllWinning.cons node_6136 (AllWinning.cons node_5335 (AllWinning.cons node_10360 (AllWinning.cons node_9352 (AllWinning.cons node_8354 (AllWinning.cons node_7420 (AllWinning.cons node_6494 (AllWinning.cons node_5683 (AllWinning.cons node_10364 (AllWinning.cons node_9359 (AllWinning.cons node_8364 (AllWinning.cons node_7443 (AllWinning.cons node_6516 (AllWinning.cons node_5705 (AllWinning.nil))))))))))))))))))

theorem node_11384 : Outcome ⟨6, 6, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 12, 2⟩, ⟨4, 6, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨2, 6, 12, 8⟩, ⟨1, 6, 12, 10⟩, ⟨0, 6, 12, 12⟩, ⟨6, 5, 12, 2⟩, ⟨6, 4, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨6, 2, 12, 8⟩, ⟨6, 1, 12, 10⟩, ⟨6, 0, 12, 12⟩, ⟨6, 6, 11, 2⟩, ⟨6, 6, 10, 4⟩, ⟨6, 6, 9, 6⟩, ⟨6, 6, 8, 8⟩, ⟨6, 6, 7, 10⟩, ⟨6, 6, 6, 12⟩, ⟨6, 6, 5, 14⟩, ⟨6, 6, 4, 16⟩, ⟨6, 6, 3, 18⟩, ⟨6, 6, 2, 20⟩]
  exact AllWinning.cons node_10274 (AllWinning.cons node_9218 (AllWinning.cons node_8169 (AllWinning.cons node_7141 (AllWinning.cons node_6136 (AllWinning.cons node_5335 (AllWinning.cons node_10360 (AllWinning.cons node_9352 (AllWinning.cons node_8354 (AllWinning.cons node_7420 (AllWinning.cons node_6494 (AllWinning.cons node_5683 (AllWinning.cons node_10364 (AllWinning.cons node_9359 (AllWinning.cons node_8364 (AllWinning.cons node_7443 (AllWinning.cons node_6516 (AllWinning.cons node_5705 (AllWinning.cons node_5010 (AllWinning.cons node_4308 (AllWinning.cons node_3712 (AllWinning.cons node_3152 (AllWinning.nil))))))))))))))))))))))

theorem node_11385 : Outcome ⟨6, 6, 12, 16⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 24⟩) (by decide) node_2236

theorem node_11386 : Outcome ⟨6, 6, 12, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 24⟩) (by decide) node_2236

theorem node_11387 : Outcome ⟨6, 7, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 7, 11, 2⟩, ⟨4, 7, 11, 4⟩, ⟨6, 6, 11, 2⟩, ⟨6, 5, 11, 4⟩, ⟨6, 7, 10, 2⟩, ⟨6, 7, 9, 4⟩]
  exact AllWinning.cons node_10278 (AllWinning.cons node_9223 (AllWinning.cons node_10364 (AllWinning.cons node_9357 (AllWinning.cons node_10366 (AllWinning.cons node_9363 (AllWinning.nil))))))

theorem node_11388 : Outcome ⟨6, 7, 11, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 6⟩) (by decide) node_8369

theorem node_11389 : Outcome ⟨6, 7, 11, 16⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 10⟩) (by decide) node_6141

theorem node_11390 : Outcome ⟨6, 7, 11, 20⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 10⟩) (by decide) node_6141

theorem node_11391 : Outcome ⟨6, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 10, 2⟩) (by decide) node_10283

theorem node_11392 : Outcome ⟨6, 8, 10, 8⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 8⟩) (by decide) node_7429

theorem node_11393 : Outcome ⟨6, 8, 10, 10⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 8⟩) (by decide) node_7429

theorem node_11394 : Outcome ⟨6, 8, 10, 20⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 8⟩) (by decide) node_7429

theorem node_11395 : Outcome ⟨6, 9, 9, 2⟩ true :=
  Outcome.win (q := ⟨5, 9, 9, 2⟩) (by decide) node_10289

theorem node_11396 : Outcome ⟨6, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 9, 9, 2⟩) (by decide) node_10289

theorem node_11397 : Outcome ⟨6, 9, 9, 16⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 12⟩) (by decide) node_5349

theorem node_11398 : Outcome ⟨6, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 8, 2⟩) (by decide) node_10293

theorem node_11399 : Outcome ⟨6, 10, 8, 8⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 8⟩) (by decide) node_7458

theorem node_11400 : Outcome ⟨6, 10, 8, 10⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 8⟩) (by decide) node_7458

theorem node_11401 : Outcome ⟨6, 10, 8, 20⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 8⟩) (by decide) node_7458

theorem node_11402 : Outcome ⟨6, 11, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 7, 2⟩, ⟨4, 11, 7, 4⟩, ⟨6, 10, 7, 2⟩, ⟨6, 9, 7, 4⟩, ⟨6, 11, 6, 2⟩, ⟨6, 11, 5, 4⟩]
  exact AllWinning.cons node_10299 (AllWinning.cons node_9240 (AllWinning.cons node_10380 (AllWinning.cons node_9371 (AllWinning.cons node_10386 (AllWinning.cons node_9381 (AllWinning.nil))))))

theorem node_11403 : Outcome ⟨6, 11, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 6⟩) (by decide) node_8381

theorem node_11404 : Outcome ⟨6, 11, 7, 16⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 10⟩) (by decide) node_6166

theorem node_11405 : Outcome ⟨6, 11, 7, 20⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 10⟩) (by decide) node_6166

theorem node_11406 : Outcome ⟨6, 12, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 6, 2⟩, ⟨4, 12, 6, 4⟩, ⟨6, 11, 6, 2⟩, ⟨6, 10, 6, 4⟩, ⟨6, 12, 5, 2⟩, ⟨6, 12, 4, 4⟩]
  exact AllWinning.cons node_10304 (AllWinning.cons node_9245 (AllWinning.cons node_10386 (AllWinning.cons node_9376 (AllWinning.cons node_10388 (AllWinning.cons node_9383 (AllWinning.nil))))))

theorem node_11407 : Outcome ⟨6, 12, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 6, 2⟩, ⟨4, 12, 6, 4⟩, ⟨3, 12, 6, 6⟩, ⟨2, 12, 6, 8⟩, ⟨6, 11, 6, 2⟩, ⟨6, 10, 6, 4⟩, ⟨6, 9, 6, 6⟩, ⟨6, 8, 6, 8⟩, ⟨6, 12, 5, 2⟩, ⟨6, 12, 4, 4⟩, ⟨6, 12, 3, 6⟩, ⟨6, 12, 2, 8⟩]
  exact AllWinning.cons node_10304 (AllWinning.cons node_9245 (AllWinning.cons node_8196 (AllWinning.cons node_7169 (AllWinning.cons node_10386 (AllWinning.cons node_9376 (AllWinning.cons node_8392 (AllWinning.cons node_7448 (AllWinning.cons node_10388 (AllWinning.cons node_9383 (AllWinning.cons node_8403 (AllWinning.cons node_7470 (AllWinning.nil))))))))))))

theorem node_11408 : Outcome ⟨6, 12, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 6, 2⟩, ⟨4, 12, 6, 4⟩, ⟨3, 12, 6, 6⟩, ⟨2, 12, 6, 8⟩, ⟨1, 12, 6, 10⟩, ⟨0, 12, 6, 12⟩, ⟨6, 11, 6, 2⟩, ⟨6, 10, 6, 4⟩, ⟨6, 9, 6, 6⟩, ⟨6, 8, 6, 8⟩, ⟨6, 7, 6, 10⟩, ⟨6, 6, 6, 12⟩, ⟨6, 12, 5, 2⟩, ⟨6, 12, 4, 4⟩, ⟨6, 12, 3, 6⟩, ⟨6, 12, 2, 8⟩, ⟨6, 12, 1, 10⟩, ⟨6, 12, 0, 12⟩]
  exact AllWinning.cons node_10304 (AllWinning.cons node_9245 (AllWinning.cons node_8196 (AllWinning.cons node_7169 (AllWinning.cons node_6177 (AllWinning.cons node_5364 (AllWinning.cons node_10386 (AllWinning.cons node_9376 (AllWinning.cons node_8392 (AllWinning.cons node_7448 (AllWinning.cons node_6519 (AllWinning.cons node_5705 (AllWinning.cons node_10388 (AllWinning.cons node_9383 (AllWinning.cons node_8403 (AllWinning.cons node_7470 (AllWinning.cons node_6542 (AllWinning.cons node_5726 (AllWinning.nil))))))))))))))))))

theorem node_11409 : Outcome ⟨6, 12, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 6, 2⟩, ⟨4, 12, 6, 4⟩, ⟨3, 12, 6, 6⟩, ⟨2, 12, 6, 8⟩, ⟨1, 12, 6, 10⟩, ⟨0, 12, 6, 12⟩, ⟨6, 11, 6, 2⟩, ⟨6, 10, 6, 4⟩, ⟨6, 9, 6, 6⟩, ⟨6, 8, 6, 8⟩, ⟨6, 7, 6, 10⟩, ⟨6, 6, 6, 12⟩, ⟨6, 5, 6, 14⟩, ⟨6, 4, 6, 16⟩, ⟨6, 3, 6, 18⟩, ⟨6, 2, 6, 20⟩, ⟨6, 12, 5, 2⟩, ⟨6, 12, 4, 4⟩, ⟨6, 12, 3, 6⟩, ⟨6, 12, 2, 8⟩, ⟨6, 12, 1, 10⟩, ⟨6, 12, 0, 12⟩]
  exact AllWinning.cons node_10304 (AllWinning.cons node_9245 (AllWinning.cons node_8196 (AllWinning.cons node_7169 (AllWinning.cons node_6177 (AllWinning.cons node_5364 (AllWinning.cons node_10386 (AllWinning.cons node_9376 (AllWinning.cons node_8392 (AllWinning.cons node_7448 (AllWinning.cons node_6519 (AllWinning.cons node_5705 (AllWinning.cons node_5007 (AllWinning.cons node_4301 (AllWinning.cons node_3703 (AllWinning.cons node_3135 (AllWinning.cons node_10388 (AllWinning.cons node_9383 (AllWinning.cons node_8403 (AllWinning.cons node_7470 (AllWinning.cons node_6542 (AllWinning.cons node_5726 (AllWinning.nil))))))))))))))))))))))

theorem node_11410 : Outcome ⟨6, 12, 6, 16⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 24⟩) (by decide) node_2202

theorem node_11411 : Outcome ⟨6, 12, 6, 20⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 24⟩) (by decide) node_2202

theorem node_11412 : Outcome ⟨6, 13, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 2⟩) (by decide) node_10308

theorem node_11413 : Outcome ⟨6, 13, 5, 18⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 2⟩) (by decide) node_10308

theorem node_11414 : Outcome ⟨6, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 2⟩) (by decide) node_10396

theorem node_11415 : Outcome ⟨6, 14, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 8⟩) (by decide) node_7178

theorem node_11416 : Outcome ⟨6, 14, 4, 18⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 8⟩) (by decide) node_7178

theorem node_11417 : Outcome ⟨6, 14, 4, 26⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 8⟩) (by decide) node_7178

theorem node_11418 : Outcome ⟨6, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 2⟩) (by decide) node_10396

theorem node_11419 : Outcome ⟨6, 15, 3, 16⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 28⟩) (by decide) node_1468

theorem node_11420 : Outcome ⟨6, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 2⟩) (by decide) node_10405

theorem node_11421 : Outcome ⟨6, 16, 2, 8⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 10⟩) (by decide) node_6534

theorem node_11422 : Outcome ⟨6, 16, 2, 20⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 10⟩) (by decide) node_6534

theorem node_11423 : Outcome ⟨6, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨5, 17, 1, 2⟩) (by decide) node_10324

theorem node_11424 : Outcome ⟨6, 17, 1, 14⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 28⟩) (by decide) node_1488

theorem node_11425 : Outcome ⟨6, 17, 1, 16⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 28⟩) (by decide) node_1488

theorem node_11426 : Outcome ⟨6, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 2⟩) (by decide) node_10329

theorem node_11427 : Outcome ⟨6, 18, 0, 8⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 2⟩) (by decide) node_10329

theorem node_11428 : Outcome ⟨6, 18, 0, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 24⟩) (by decide) node_2236

theorem node_11429 : Outcome ⟨7, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 15, 4⟩) (by decide) node_9405

theorem node_11430 : Outcome ⟨7, 0, 17, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 6⟩) (by decide) node_8221

theorem node_11431 : Outcome ⟨7, 0, 17, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 6⟩) (by decide) node_8221

theorem node_11432 : Outcome ⟨7, 0, 17, 10⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 20⟩) (by decide) node_3170

theorem node_11433 : Outcome ⟨7, 0, 17, 20⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 20⟩) (by decide) node_3170

theorem node_11434 : Outcome ⟨7, 1, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 2⟩) (by decide) node_10339

theorem node_11435 : Outcome ⟨7, 1, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 2⟩) (by decide) node_10339

theorem node_11436 : Outcome ⟨7, 1, 16, 16⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 10⟩) (by decide) node_6560

theorem node_11437 : Outcome ⟨7, 1, 16, 20⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 10⟩) (by decide) node_6560

theorem node_11438 : Outcome ⟨7, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 15, 4⟩) (by decide) node_9278

theorem node_11439 : Outcome ⟨7, 2, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 6⟩) (by decide) node_8426

theorem node_11440 : Outcome ⟨7, 2, 15, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 6⟩) (by decide) node_8426

theorem node_11441 : Outcome ⟨7, 2, 15, 20⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 24⟩) (by decide) node_2260

theorem node_11442 : Outcome ⟨7, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 2⟩) (by decide) node_10350

theorem node_11443 : Outcome ⟨7, 3, 14, 8⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 2⟩) (by decide) node_10350

theorem node_11444 : Outcome ⟨7, 3, 14, 20⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 24⟩) (by decide) node_2276

theorem node_11445 : Outcome ⟨7, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 13, 2⟩) (by decide) node_10428

theorem node_11446 : Outcome ⟨7, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 6⟩) (by decide) node_8235

theorem node_11447 : Outcome ⟨7, 4, 13, 10⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 16⟩) (by decide) node_4350

theorem node_11448 : Outcome ⟨7, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 6⟩) (by decide) node_8426

theorem node_11449 : Outcome ⟨7, 5, 12, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 12, 6⟩) (by decide) node_8426

theorem node_11450 : Outcome ⟨7, 5, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 16⟩) (by decide) node_4365

theorem node_11451 : Outcome ⟨7, 5, 12, 20⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 16⟩) (by decide) node_4365

theorem node_11452 : Outcome ⟨7, 5, 12, 22⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 16⟩) (by decide) node_4365

theorem node_11453 : Outcome ⟨7, 6, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 6, 11, 2⟩, ⟨5, 6, 11, 4⟩, ⟨7, 5, 11, 2⟩, ⟨7, 4, 11, 4⟩, ⟨7, 6, 10, 2⟩, ⟨7, 6, 9, 4⟩]
  exact AllWinning.cons node_10364 (AllWinning.cons node_9292 (AllWinning.cons node_10437 (AllWinning.cons node_9421 (AllWinning.cons node_10442 (AllWinning.cons node_9429 (AllWinning.nil))))))

theorem node_11454 : Outcome ⟨7, 6, 11, 4⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 6⟩) (by decide) node_8445

theorem node_11455 : Outcome ⟨7, 6, 11, 16⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11456 : Outcome ⟨7, 6, 11, 20⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11457 : Outcome ⟨7, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 6⟩) (by decide) node_8457

theorem node_11458 : Outcome ⟨7, 7, 10, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 6⟩) (by decide) node_8457

theorem node_11459 : Outcome ⟨7, 8, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 9, 2⟩, ⟨5, 8, 9, 4⟩, ⟨7, 7, 9, 2⟩, ⟨7, 6, 9, 4⟩, ⟨7, 8, 8, 2⟩, ⟨7, 8, 7, 4⟩]
  exact AllWinning.cons node_10372 (AllWinning.cons node_9300 (AllWinning.cons node_10448 (AllWinning.cons node_9429 (AllWinning.cons node_10451 (AllWinning.cons node_9436 (AllWinning.nil))))))

theorem node_11460 : Outcome ⟨7, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 6⟩) (by decide) node_8461

theorem node_11461 : Outcome ⟨7, 8, 9, 10⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 6⟩) (by decide) node_8461

theorem node_11462 : Outcome ⟨7, 8, 9, 22⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 6⟩) (by decide) node_8461

theorem node_11463 : Outcome ⟨7, 9, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 8, 2⟩, ⟨5, 9, 8, 4⟩, ⟨7, 8, 8, 2⟩, ⟨7, 7, 8, 4⟩, ⟨7, 9, 7, 2⟩, ⟨7, 9, 6, 4⟩]
  exact AllWinning.cons node_10376 (AllWinning.cons node_9304 (AllWinning.cons node_10451 (AllWinning.cons node_9434 (AllWinning.cons node_10456 (AllWinning.cons node_9438 (AllWinning.nil))))))

theorem node_11464 : Outcome ⟨7, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 6⟩) (by decide) node_8445

theorem node_11465 : Outcome ⟨7, 9, 8, 10⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 6⟩) (by decide) node_8445

theorem node_11466 : Outcome ⟨7, 9, 8, 22⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 6⟩) (by decide) node_8445

theorem node_11467 : Outcome ⟨7, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 6⟩) (by decide) node_8457

theorem node_11468 : Outcome ⟨7, 10, 7, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 6⟩) (by decide) node_8457

theorem node_11469 : Outcome ⟨7, 11, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 6, 2⟩, ⟨5, 11, 6, 4⟩, ⟨7, 10, 6, 2⟩, ⟨7, 9, 6, 4⟩, ⟨7, 11, 5, 2⟩, ⟨7, 11, 4, 4⟩]
  exact AllWinning.cons node_10386 (AllWinning.cons node_9313 (AllWinning.cons node_10459 (AllWinning.cons node_9438 (AllWinning.cons node_10465 (AllWinning.cons node_9448 (AllWinning.nil))))))

theorem node_11470 : Outcome ⟨7, 11, 6, 4⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 6⟩) (by decide) node_8461

theorem node_11471 : Outcome ⟨7, 11, 6, 16⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 10⟩) (by decide) node_6245

theorem node_11472 : Outcome ⟨7, 11, 6, 20⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 10⟩) (by decide) node_6245

theorem node_11473 : Outcome ⟨7, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 6⟩) (by decide) node_8484

theorem node_11474 : Outcome ⟨7, 12, 5, 6⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 6⟩) (by decide) node_8484

theorem node_11475 : Outcome ⟨7, 12, 5, 10⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 16⟩) (by decide) node_4350

theorem node_11476 : Outcome ⟨7, 12, 5, 20⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 16⟩) (by decide) node_4350

theorem node_11477 : Outcome ⟨7, 12, 5, 22⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 16⟩) (by decide) node_4350

theorem node_11478 : Outcome ⟨7, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨7, 13, 3, 2⟩) (by decide) node_10475

theorem node_11479 : Outcome ⟨7, 13, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 4, 6⟩) (by decide) node_8269

theorem node_11480 : Outcome ⟨7, 13, 4, 10⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 16⟩) (by decide) node_4365

theorem node_11481 : Outcome ⟨7, 14, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 2⟩) (by decide) node_10396

theorem node_11482 : Outcome ⟨7, 14, 3, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 2⟩) (by decide) node_10396

theorem node_11483 : Outcome ⟨7, 14, 3, 20⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 24⟩) (by decide) node_2260

theorem node_11484 : Outcome ⟨7, 15, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 2, 4⟩) (by decide) node_9326

theorem node_11485 : Outcome ⟨7, 15, 2, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 6⟩) (by decide) node_8484

theorem node_11486 : Outcome ⟨7, 15, 2, 6⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 6⟩) (by decide) node_8484

theorem node_11487 : Outcome ⟨7, 15, 2, 20⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 24⟩) (by decide) node_2276

theorem node_11488 : Outcome ⟨7, 16, 1, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 2⟩) (by decide) node_10405

theorem node_11489 : Outcome ⟨7, 16, 1, 16⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 10⟩) (by decide) node_6607

theorem node_11490 : Outcome ⟨7, 16, 1, 20⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 10⟩) (by decide) node_6607

theorem node_11491 : Outcome ⟨7, 17, 0, 2⟩ true :=
  Outcome.win (q := ⟨7, 15, 0, 4⟩) (by decide) node_9463

theorem node_11492 : Outcome ⟨7, 17, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 6⟩) (by decide) node_8283

theorem node_11493 : Outcome ⟨7, 17, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 6⟩) (by decide) node_8283

theorem node_11494 : Outcome ⟨7, 17, 0, 10⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 20⟩) (by decide) node_3207

theorem node_11495 : Outcome ⟨7, 17, 0, 20⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 20⟩) (by decide) node_3207

theorem node_11496 : Outcome ⟨8, 0, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 0, 16, 2⟩, ⟨6, 0, 16, 4⟩, ⟨8, 0, 15, 2⟩, ⟨8, 0, 14, 4⟩]
  exact AllWinning.cons node_10416 (AllWinning.cons node_9336 (AllWinning.cons node_10491 (AllWinning.cons node_9469 (AllWinning.nil))))

theorem node_11497 : Outcome ⟨8, 0, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 0, 16, 2⟩, ⟨6, 0, 16, 4⟩, ⟨5, 0, 16, 6⟩, ⟨4, 0, 16, 8⟩, ⟨8, 0, 15, 2⟩, ⟨8, 0, 14, 4⟩, ⟨8, 0, 13, 6⟩, ⟨8, 0, 12, 8⟩]
  exact AllWinning.cons node_10416 (AllWinning.cons node_9336 (AllWinning.cons node_8288 (AllWinning.cons node_7267 (AllWinning.cons node_10491 (AllWinning.cons node_9469 (AllWinning.cons node_8501 (AllWinning.cons node_7540 (AllWinning.nil))))))))

theorem node_11498 : Outcome ⟨8, 0, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 10⟩) (by decide) node_6276

theorem node_11499 : Outcome ⟨8, 0, 16, 16⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 16⟩) (by decide) node_4397

theorem node_11500 : Outcome ⟨8, 1, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 1, 15, 2⟩, ⟨6, 1, 15, 4⟩, ⟨8, 0, 15, 2⟩, ⟨8, 1, 14, 2⟩, ⟨8, 1, 13, 4⟩]
  exact AllWinning.cons node_10420 (AllWinning.cons node_9341 (AllWinning.cons node_10491 (AllWinning.cons node_10495 (AllWinning.cons node_9472 (AllWinning.nil)))))

theorem node_11501 : Outcome ⟨8, 1, 15, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 8⟩) (by decide) node_7273

theorem node_11502 : Outcome ⟨8, 1, 15, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 8⟩) (by decide) node_7273

theorem node_11503 : Outcome ⟨8, 1, 15, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 8⟩) (by decide) node_7273

theorem node_11504 : Outcome ⟨8, 2, 14, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 8⟩) (by decide) node_7280

theorem node_11505 : Outcome ⟨8, 2, 14, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 8⟩) (by decide) node_7280

theorem node_11506 : Outcome ⟨8, 3, 13, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 13, 2⟩) (by decide) node_10428

theorem node_11507 : Outcome ⟨8, 3, 13, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 10⟩) (by decide) node_6292

theorem node_11508 : Outcome ⟨8, 4, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 4, 12, 2⟩, ⟨6, 4, 12, 4⟩, ⟨8, 3, 12, 2⟩, ⟨8, 2, 12, 4⟩, ⟨8, 4, 11, 2⟩, ⟨8, 4, 10, 4⟩]
  exact AllWinning.cons node_10432 (AllWinning.cons node_9352 (AllWinning.cons node_10500 (AllWinning.cons node_9474 (AllWinning.cons node_10503 (AllWinning.cons node_9482 (AllWinning.nil))))))

theorem node_11509 : Outcome ⟨8, 4, 12, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 6⟩) (by decide) node_8504

theorem node_11510 : Outcome ⟨8, 4, 12, 10⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 6⟩) (by decide) node_8504

theorem node_11511 : Outcome ⟨8, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨8, 5, 10, 2⟩) (by decide) node_10507

theorem node_11512 : Outcome ⟨8, 5, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 10⟩) (by decide) node_6303

theorem node_11513 : Outcome ⟨8, 5, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 10⟩) (by decide) node_6303

theorem node_11514 : Outcome ⟨8, 5, 11, 10⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 10⟩) (by decide) node_6303

theorem node_11515 : Outcome ⟨8, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨8, 5, 10, 2⟩) (by decide) node_10507

theorem node_11516 : Outcome ⟨8, 6, 10, 8⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 8⟩) (by decide) node_7296

theorem node_11517 : Outcome ⟨8, 6, 10, 10⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 8⟩) (by decide) node_7296

theorem node_11518 : Outcome ⟨8, 6, 10, 20⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 8⟩) (by decide) node_7296

theorem node_11519 : Outcome ⟨8, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 6⟩) (by decide) node_8543

theorem node_11520 : Outcome ⟨8, 7, 9, 10⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 6⟩) (by decide) node_8543

theorem node_11521 : Outcome ⟨8, 7, 9, 22⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 6⟩) (by decide) node_8543

theorem node_11522 : Outcome ⟨8, 8, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 8, 2⟩, ⟨6, 8, 8, 4⟩, ⟨8, 7, 8, 2⟩, ⟨8, 6, 8, 4⟩, ⟨8, 8, 7, 2⟩, ⟨8, 8, 6, 4⟩]
  exact AllWinning.cons node_10451 (AllWinning.cons node_9368 (AllWinning.cons node_10516 (AllWinning.cons node_9488 (AllWinning.cons node_10521 (AllWinning.cons node_9493 (AllWinning.nil))))))

theorem node_11523 : Outcome ⟨8, 8, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 8, 2⟩, ⟨6, 8, 8, 4⟩, ⟨5, 8, 8, 6⟩, ⟨4, 8, 8, 8⟩, ⟨8, 7, 8, 2⟩, ⟨8, 6, 8, 4⟩, ⟨8, 5, 8, 6⟩, ⟨8, 4, 8, 8⟩, ⟨8, 8, 7, 2⟩, ⟨8, 8, 6, 4⟩, ⟨8, 8, 5, 6⟩, ⟨8, 8, 4, 8⟩]
  exact AllWinning.cons node_10451 (AllWinning.cons node_9368 (AllWinning.cons node_8315 (AllWinning.cons node_7308 (AllWinning.cons node_10516 (AllWinning.cons node_9488 (AllWinning.cons node_8526 (AllWinning.cons node_7554 (AllWinning.cons node_10521 (AllWinning.cons node_9493 (AllWinning.cons node_8555 (AllWinning.cons node_7568 (AllWinning.nil))))))))))))

theorem node_11524 : Outcome ⟨8, 8, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 8, 8, 2⟩, ⟨6, 8, 8, 4⟩, ⟨5, 8, 8, 6⟩, ⟨4, 8, 8, 8⟩, ⟨3, 8, 8, 10⟩, ⟨2, 8, 8, 12⟩, ⟨8, 7, 8, 2⟩, ⟨8, 6, 8, 4⟩, ⟨8, 5, 8, 6⟩, ⟨8, 4, 8, 8⟩, ⟨8, 3, 8, 10⟩, ⟨8, 2, 8, 12⟩, ⟨8, 8, 7, 2⟩, ⟨8, 8, 6, 4⟩, ⟨8, 8, 5, 6⟩, ⟨8, 8, 4, 8⟩, ⟨8, 8, 3, 10⟩, ⟨8, 8, 2, 12⟩]
  exact AllWinning.cons node_10451 (AllWinning.cons node_9368 (AllWinning.cons node_8315 (AllWinning.cons node_7308 (AllWinning.cons node_6320 (AllWinning.cons node_5487 (AllWinning.cons node_10516 (AllWinning.cons node_9488 (AllWinning.cons node_8526 (AllWinning.cons node_7554 (AllWinning.cons node_6634 (AllWinning.cons node_5784 (AllWinning.cons node_10521 (AllWinning.cons node_9493 (AllWinning.cons node_8555 (AllWinning.cons node_7568 (AllWinning.cons node_6651 (AllWinning.cons node_5810 (AllWinning.nil))))))))))))))))))

theorem node_11525 : Outcome ⟨8, 8, 8, 8⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 16⟩) (by decide) node_3965

theorem node_11526 : Outcome ⟨8, 8, 8, 20⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 16⟩) (by decide) node_3965

theorem node_11527 : Outcome ⟨8, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 6⟩) (by decide) node_8531

theorem node_11528 : Outcome ⟨8, 9, 7, 10⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 6⟩) (by decide) node_8531

theorem node_11529 : Outcome ⟨8, 9, 7, 22⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 6⟩) (by decide) node_8531

theorem node_11530 : Outcome ⟨8, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨8, 10, 5, 2⟩) (by decide) node_10529

theorem node_11531 : Outcome ⟨8, 10, 6, 8⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 8⟩) (by decide) node_7316

theorem node_11532 : Outcome ⟨8, 10, 6, 10⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 8⟩) (by decide) node_7316

theorem node_11533 : Outcome ⟨8, 10, 6, 20⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 8⟩) (by decide) node_7316

theorem node_11534 : Outcome ⟨8, 11, 5, 4⟩ true :=
  Outcome.win (q := ⟨8, 10, 5, 2⟩) (by decide) node_10529

theorem node_11535 : Outcome ⟨8, 11, 5, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 10⟩) (by decide) node_6334

theorem node_11536 : Outcome ⟨8, 11, 5, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 10⟩) (by decide) node_6334

theorem node_11537 : Outcome ⟨8, 11, 5, 10⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 10⟩) (by decide) node_6334

theorem node_11538 : Outcome ⟨8, 12, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 12, 4, 2⟩, ⟨6, 12, 4, 4⟩, ⟨8, 11, 4, 2⟩, ⟨8, 10, 4, 4⟩, ⟨8, 12, 3, 2⟩, ⟨8, 12, 2, 4⟩]
  exact AllWinning.cons node_10470 (AllWinning.cons node_9383 (AllWinning.cons node_10535 (AllWinning.cons node_9500 (AllWinning.cons node_10539 (AllWinning.cons node_9507 (AllWinning.nil))))))

theorem node_11539 : Outcome ⟨8, 12, 4, 8⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 6⟩) (by decide) node_8571

theorem node_11540 : Outcome ⟨8, 12, 4, 10⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 6⟩) (by decide) node_8571

theorem node_11541 : Outcome ⟨8, 13, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 13, 3, 2⟩) (by decide) node_10475

theorem node_11542 : Outcome ⟨8, 13, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 10⟩) (by decide) node_6349

theorem node_11543 : Outcome ⟨8, 14, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 14, 2, 2⟩, ⟨6, 14, 2, 4⟩, ⟨8, 13, 2, 2⟩, ⟨8, 12, 2, 4⟩, ⟨8, 14, 1, 2⟩, ⟨8, 14, 0, 4⟩]
  exact AllWinning.cons node_10479 (AllWinning.cons node_9391 (AllWinning.cons node_10542 (AllWinning.cons node_9507 (AllWinning.cons node_10545 (AllWinning.cons node_9513 (AllWinning.nil))))))

theorem node_11544 : Outcome ⟨8, 14, 2, 8⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 8⟩) (by decide) node_7336

theorem node_11545 : Outcome ⟨8, 14, 2, 10⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 8⟩) (by decide) node_7336

theorem node_11546 : Outcome ⟨8, 15, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 8⟩) (by decide) node_7343

theorem node_11547 : Outcome ⟨8, 15, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 8⟩) (by decide) node_7343

theorem node_11548 : Outcome ⟨8, 15, 1, 16⟩ true :=
  Outcome.win (q := ⟨4, 15, 1, 8⟩) (by decide) node_7343

theorem node_11549 : Outcome ⟨8, 16, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 0, 2⟩, ⟨6, 16, 0, 4⟩, ⟨8, 15, 0, 2⟩, ⟨8, 14, 0, 4⟩]
  exact AllWinning.cons node_10487 (AllWinning.cons node_9400 (AllWinning.cons node_10548 (AllWinning.cons node_9513 (AllWinning.nil))))

theorem node_11550 : Outcome ⟨8, 16, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 16, 0, 2⟩, ⟨6, 16, 0, 4⟩, ⟨5, 16, 0, 6⟩, ⟨4, 16, 0, 8⟩, ⟨8, 15, 0, 2⟩, ⟨8, 14, 0, 4⟩, ⟨8, 13, 0, 6⟩, ⟨8, 12, 0, 8⟩]
  exact AllWinning.cons node_10487 (AllWinning.cons node_9400 (AllWinning.cons node_8341 (AllWinning.cons node_7348 (AllWinning.cons node_10548 (AllWinning.cons node_9513 (AllWinning.cons node_8581 (AllWinning.cons node_7584 (AllWinning.nil))))))))

theorem node_11551 : Outcome ⟨8, 16, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 10⟩) (by decide) node_6364

theorem node_11552 : Outcome ⟨8, 16, 0, 16⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 16⟩) (by decide) node_4438

theorem node_11553 : Outcome ⟨9, 0, 15, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 15, 4⟩) (by decide) node_9405

theorem node_11554 : Outcome ⟨9, 0, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 0, 15, 4⟩) (by decide) node_9405

theorem node_11555 : Outcome ⟨9, 0, 15, 12⟩ true :=
  Outcome.win (q := ⟨9, 0, 9, 12⟩) (by decide) node_5825

theorem node_11556 : Outcome ⟨9, 1, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 14, 2⟩) (by decide) node_10552

theorem node_11557 : Outcome ⟨9, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨9, 0, 14, 2⟩) (by decide) node_10552

theorem node_11558 : Outcome ⟨9, 1, 14, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 14, 2⟩) (by decide) node_10552

theorem node_11559 : Outcome ⟨9, 2, 13, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 13, 2⟩) (by decide) node_10556

theorem node_11560 : Outcome ⟨9, 2, 13, 10⟩ true :=
  Outcome.win (q := ⟨9, 1, 13, 2⟩) (by decide) node_10556

theorem node_11561 : Outcome ⟨9, 3, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 12, 2⟩, ⟨7, 3, 12, 4⟩, ⟨9, 2, 12, 2⟩, ⟨9, 1, 12, 4⟩, ⟨9, 3, 11, 2⟩, ⟨9, 3, 10, 4⟩]
  exact AllWinning.cons node_10500 (AllWinning.cons node_9416 (AllWinning.cons node_10561 (AllWinning.cons node_9519 (AllWinning.cons node_10564 (AllWinning.cons node_9524 (AllWinning.nil))))))

theorem node_11562 : Outcome ⟨9, 3, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 12, 2⟩, ⟨7, 3, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨5, 3, 12, 8⟩, ⟨9, 2, 12, 2⟩, ⟨9, 1, 12, 4⟩, ⟨9, 0, 12, 6⟩, ⟨9, 3, 11, 2⟩, ⟨9, 3, 10, 4⟩, ⟨9, 3, 9, 6⟩, ⟨9, 3, 8, 8⟩]
  exact AllWinning.cons node_10500 (AllWinning.cons node_9416 (AllWinning.cons node_8354 (AllWinning.cons node_7363 (AllWinning.cons node_10561 (AllWinning.cons node_9519 (AllWinning.cons node_8584 (AllWinning.cons node_10564 (AllWinning.cons node_9524 (AllWinning.cons node_8595 (AllWinning.cons node_7597 (AllWinning.nil)))))))))))

theorem node_11563 : Outcome ⟨9, 3, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 12, 2⟩, ⟨7, 3, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨5, 3, 12, 8⟩, ⟨4, 3, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨9, 2, 12, 2⟩, ⟨9, 1, 12, 4⟩, ⟨9, 0, 12, 6⟩, ⟨9, 3, 11, 2⟩, ⟨9, 3, 10, 4⟩, ⟨9, 3, 9, 6⟩, ⟨9, 3, 8, 8⟩, ⟨9, 3, 7, 10⟩, ⟨9, 3, 6, 12⟩]
  exact AllWinning.cons node_10500 (AllWinning.cons node_9416 (AllWinning.cons node_8354 (AllWinning.cons node_7363 (AllWinning.cons node_6379 (AllWinning.cons node_5532 (AllWinning.cons node_10561 (AllWinning.cons node_9519 (AllWinning.cons node_8584 (AllWinning.cons node_10564 (AllWinning.cons node_9524 (AllWinning.cons node_8595 (AllWinning.cons node_7597 (AllWinning.cons node_6675 (AllWinning.cons node_5846 (AllWinning.nil)))))))))))))))

theorem node_11564 : Outcome ⟨9, 3, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 12, 2⟩, ⟨7, 3, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨5, 3, 12, 8⟩, ⟨4, 3, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨2, 3, 12, 14⟩, ⟨1, 3, 12, 16⟩, ⟨9, 2, 12, 2⟩, ⟨9, 1, 12, 4⟩, ⟨9, 0, 12, 6⟩, ⟨9, 3, 11, 2⟩, ⟨9, 3, 10, 4⟩, ⟨9, 3, 9, 6⟩, ⟨9, 3, 8, 8⟩, ⟨9, 3, 7, 10⟩, ⟨9, 3, 6, 12⟩, ⟨9, 3, 5, 14⟩, ⟨9, 3, 4, 16⟩]
  exact AllWinning.cons node_10500 (AllWinning.cons node_9416 (AllWinning.cons node_8354 (AllWinning.cons node_7363 (AllWinning.cons node_6379 (AllWinning.cons node_5532 (AllWinning.cons node_4738 (AllWinning.cons node_4012 (AllWinning.cons node_10561 (AllWinning.cons node_9519 (AllWinning.cons node_8584 (AllWinning.cons node_10564 (AllWinning.cons node_9524 (AllWinning.cons node_8595 (AllWinning.cons node_7597 (AllWinning.cons node_6675 (AllWinning.cons node_5846 (AllWinning.cons node_5127 (AllWinning.cons node_4455 (AllWinning.nil)))))))))))))))))))

theorem node_11565 : Outcome ⟨9, 3, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 12, 2⟩, ⟨7, 3, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨5, 3, 12, 8⟩, ⟨4, 3, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨2, 3, 12, 14⟩, ⟨1, 3, 12, 16⟩, ⟨0, 3, 12, 18⟩, ⟨9, 2, 12, 2⟩, ⟨9, 1, 12, 4⟩, ⟨9, 0, 12, 6⟩, ⟨9, 3, 11, 2⟩, ⟨9, 3, 10, 4⟩, ⟨9, 3, 9, 6⟩, ⟨9, 3, 8, 8⟩, ⟨9, 3, 7, 10⟩, ⟨9, 3, 6, 12⟩, ⟨9, 3, 5, 14⟩, ⟨9, 3, 4, 16⟩, ⟨9, 3, 3, 18⟩, ⟨9, 3, 2, 20⟩]
  exact AllWinning.cons node_10500 (AllWinning.cons node_9416 (AllWinning.cons node_8354 (AllWinning.cons node_7363 (AllWinning.cons node_6379 (AllWinning.cons node_5532 (AllWinning.cons node_4738 (AllWinning.cons node_4012 (AllWinning.cons node_3334 (AllWinning.cons node_10561 (AllWinning.cons node_9519 (AllWinning.cons node_8584 (AllWinning.cons node_10564 (AllWinning.cons node_9524 (AllWinning.cons node_8595 (AllWinning.cons node_7597 (AllWinning.cons node_6675 (AllWinning.cons node_5846 (AllWinning.cons node_5127 (AllWinning.cons node_4455 (AllWinning.cons node_3816 (AllWinning.cons node_3252 (AllWinning.nil))))))))))))))))))))))

theorem node_11566 : Outcome ⟨9, 3, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 12, 2⟩, ⟨7, 3, 12, 4⟩, ⟨6, 3, 12, 6⟩, ⟨5, 3, 12, 8⟩, ⟨4, 3, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨2, 3, 12, 14⟩, ⟨1, 3, 12, 16⟩, ⟨0, 3, 12, 18⟩, ⟨9, 2, 12, 2⟩, ⟨9, 1, 12, 4⟩, ⟨9, 0, 12, 6⟩, ⟨9, 3, 11, 2⟩, ⟨9, 3, 10, 4⟩, ⟨9, 3, 9, 6⟩, ⟨9, 3, 8, 8⟩, ⟨9, 3, 7, 10⟩, ⟨9, 3, 6, 12⟩, ⟨9, 3, 5, 14⟩, ⟨9, 3, 4, 16⟩, ⟨9, 3, 3, 18⟩, ⟨9, 3, 2, 20⟩, ⟨9, 3, 1, 22⟩, ⟨9, 3, 0, 24⟩]
  exact AllWinning.cons node_10500 (AllWinning.cons node_9416 (AllWinning.cons node_8354 (AllWinning.cons node_7363 (AllWinning.cons node_6379 (AllWinning.cons node_5532 (AllWinning.cons node_4738 (AllWinning.cons node_4012 (AllWinning.cons node_3334 (AllWinning.cons node_10561 (AllWinning.cons node_9519 (AllWinning.cons node_8584 (AllWinning.cons node_10564 (AllWinning.cons node_9524 (AllWinning.cons node_8595 (AllWinning.cons node_7597 (AllWinning.cons node_6675 (AllWinning.cons node_5846 (AllWinning.cons node_5127 (AllWinning.cons node_4455 (AllWinning.cons node_3816 (AllWinning.cons node_3252 (AllWinning.cons node_2769 (AllWinning.cons node_2333 (AllWinning.nil))))))))))))))))))))))))

end RQ9F1
