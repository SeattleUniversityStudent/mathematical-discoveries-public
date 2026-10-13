import Chunk04
set_option autoImplicit false
namespace RQ9F1

theorem node_1341 : Outcome ⟨3, 3, 4, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

theorem node_1342 : Outcome ⟨3, 3, 4, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

theorem node_1343 : Outcome ⟨3, 4, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 3, 2⟩) (by decide) node_1042

theorem node_1344 : Outcome ⟨3, 4, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1345 : Outcome ⟨3, 4, 3, 18⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1346 : Outcome ⟨3, 5, 2, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1347 : Outcome ⟨3, 5, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1348 : Outcome ⟨3, 5, 2, 14⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1349 : Outcome ⟨3, 5, 2, 18⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1350 : Outcome ⟨3, 6, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_1054 (AllWinning.nil)))))

theorem node_1351 : Outcome ⟨3, 6, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_1054 (AllWinning.nil))))))))

theorem node_1352 : Outcome ⟨3, 6, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1353 : Outcome ⟨3, 6, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1354 : Outcome ⟨3, 6, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1355 : Outcome ⟨3, 6, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1356 : Outcome ⟨3, 6, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1357 : Outcome ⟨3, 6, 1, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1358 : Outcome ⟨3, 6, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1359 : Outcome ⟨3, 6, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1360 : Outcome ⟨3, 6, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1361 : Outcome ⟨3, 6, 1, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1362 : Outcome ⟨3, 6, 1, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1363 : Outcome ⟨3, 6, 1, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1364 : Outcome ⟨3, 6, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1365 : Outcome ⟨3, 6, 1, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1366 : Outcome ⟨3, 6, 1, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 6, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨3, 5, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨3, 2, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨3, 6, 0, 2⟩]
  exact AllWinning.cons node_1019 (AllWinning.cons node_757 (AllWinning.cons node_489 (AllWinning.cons node_1050 (AllWinning.cons node_813 (AllWinning.cons node_609 (AllWinning.cons node_424 (AllWinning.cons node_302 (AllWinning.cons node_224 (AllWinning.cons node_1054 (AllWinning.nil))))))))))

theorem node_1367 : Outcome ⟨3, 7, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 7, 0, 2⟩) (by decide) node_1024

theorem node_1368 : Outcome ⟨3, 7, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

theorem node_1369 : Outcome ⟨3, 7, 0, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

theorem node_1370 : Outcome ⟨3, 7, 0, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

theorem node_1371 : Outcome ⟨4, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 4⟩) (by decide) node_821

theorem node_1372 : Outcome ⟨4, 0, 6, 12⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 4⟩) (by decide) node_821

theorem node_1373 : Outcome ⟨4, 0, 6, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 4⟩) (by decide) node_821

theorem node_1374 : Outcome ⟨4, 1, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 5, 2⟩, ⟨2, 1, 5, 4⟩, ⟨4, 0, 5, 2⟩, ⟨4, 1, 4, 2⟩, ⟨4, 1, 3, 4⟩]
  exact AllWinning.cons node_1034 (AllWinning.cons node_770 (AllWinning.cons node_1059 (AllWinning.cons node_1062 (AllWinning.cons node_836 (AllWinning.nil)))))

theorem node_1375 : Outcome ⟨4, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1376 : Outcome ⟨4, 1, 5, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1377 : Outcome ⟨4, 1, 5, 10⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1378 : Outcome ⟨4, 1, 5, 12⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1379 : Outcome ⟨4, 1, 5, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1380 : Outcome ⟨4, 2, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 4⟩) (by decide) node_821

theorem node_1381 : Outcome ⟨4, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1382 : Outcome ⟨4, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1383 : Outcome ⟨4, 2, 4, 10⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1384 : Outcome ⟨4, 2, 4, 12⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1385 : Outcome ⟨4, 2, 4, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1386 : Outcome ⟨4, 3, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 3, 2⟩) (by decide) node_1042

theorem node_1387 : Outcome ⟨4, 3, 3, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1388 : Outcome ⟨4, 3, 3, 18⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1389 : Outcome ⟨4, 4, 2, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 4⟩) (by decide) node_847

theorem node_1390 : Outcome ⟨4, 4, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1391 : Outcome ⟨4, 4, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1392 : Outcome ⟨4, 4, 2, 10⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1393 : Outcome ⟨4, 4, 2, 12⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1394 : Outcome ⟨4, 4, 2, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1395 : Outcome ⟨4, 5, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 1, 2⟩, ⟨2, 5, 1, 4⟩, ⟨4, 4, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨4, 5, 0, 2⟩]
  exact AllWinning.cons node_1050 (AllWinning.cons node_788 (AllWinning.cons node_1076 (AllWinning.cons node_843 (AllWinning.cons node_1082 (AllWinning.nil)))))

theorem node_1396 : Outcome ⟨4, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1397 : Outcome ⟨4, 5, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1398 : Outcome ⟨4, 5, 1, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1399 : Outcome ⟨4, 5, 1, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1400 : Outcome ⟨4, 5, 1, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1401 : Outcome ⟨4, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 4⟩) (by decide) node_847

theorem node_1402 : Outcome ⟨4, 6, 0, 12⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 4⟩) (by decide) node_847

theorem node_1403 : Outcome ⟨4, 6, 0, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 4⟩) (by decide) node_847

theorem node_1404 : Outcome ⟨5, 0, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.nil))))

theorem node_1405 : Outcome ⟨5, 0, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.nil))))))))

theorem node_1406 : Outcome ⟨5, 0, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1407 : Outcome ⟨5, 0, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1408 : Outcome ⟨5, 0, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1409 : Outcome ⟨5, 0, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1410 : Outcome ⟨5, 0, 5, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1411 : Outcome ⟨5, 0, 5, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1412 : Outcome ⟨5, 0, 5, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1413 : Outcome ⟨5, 0, 5, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1414 : Outcome ⟨5, 0, 5, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1415 : Outcome ⟨5, 0, 5, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1416 : Outcome ⟨5, 0, 5, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1417 : Outcome ⟨5, 0, 5, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 5, 2⟩, ⟨3, 0, 5, 4⟩, ⟨2, 0, 5, 6⟩, ⟨1, 0, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨5, 0, 4, 2⟩, ⟨5, 0, 3, 4⟩, ⟨5, 0, 2, 6⟩, ⟨5, 0, 1, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1059 (AllWinning.cons node_796 (AllWinning.cons node_553 (AllWinning.cons node_366 (AllWinning.cons node_237 (AllWinning.cons node_1085 (AllWinning.cons node_862 (AllWinning.cons node_655 (AllWinning.cons node_457 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1418 : Outcome ⟨5, 1, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 4, 2⟩, ⟨3, 1, 4, 4⟩, ⟨5, 0, 4, 2⟩, ⟨5, 1, 3, 2⟩, ⟨5, 1, 2, 4⟩]
  exact AllWinning.cons node_1062 (AllWinning.cons node_800 (AllWinning.cons node_1085 (AllWinning.cons node_1088 (AllWinning.cons node_867 (AllWinning.nil)))))

theorem node_1419 : Outcome ⟨5, 1, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1420 : Outcome ⟨5, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1421 : Outcome ⟨5, 1, 4, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1422 : Outcome ⟨5, 1, 4, 12⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1423 : Outcome ⟨5, 1, 4, 20⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1424 : Outcome ⟨5, 2, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1425 : Outcome ⟨5, 2, 3, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1426 : Outcome ⟨5, 2, 3, 14⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1427 : Outcome ⟨5, 2, 3, 18⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1428 : Outcome ⟨5, 3, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1429 : Outcome ⟨5, 3, 2, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1430 : Outcome ⟨5, 3, 2, 14⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1431 : Outcome ⟨5, 3, 2, 18⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1432 : Outcome ⟨5, 4, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 4, 1, 2⟩, ⟨3, 4, 1, 4⟩, ⟨5, 3, 1, 2⟩, ⟨5, 2, 1, 4⟩, ⟨5, 4, 0, 2⟩]
  exact AllWinning.cons node_1076 (AllWinning.cons node_813 (AllWinning.cons node_1096 (AllWinning.cons node_872 (AllWinning.cons node_1100 (AllWinning.nil)))))

theorem node_1433 : Outcome ⟨5, 4, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1434 : Outcome ⟨5, 4, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1435 : Outcome ⟨5, 4, 1, 10⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1436 : Outcome ⟨5, 4, 1, 12⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1437 : Outcome ⟨5, 4, 1, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1438 : Outcome ⟨5, 5, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.nil))))

theorem node_1439 : Outcome ⟨5, 5, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.nil))))))))

theorem node_1440 : Outcome ⟨5, 5, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1441 : Outcome ⟨5, 5, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1442 : Outcome ⟨5, 5, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1443 : Outcome ⟨5, 5, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1444 : Outcome ⟨5, 5, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1445 : Outcome ⟨5, 5, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1446 : Outcome ⟨5, 5, 0, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1447 : Outcome ⟨5, 5, 0, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1448 : Outcome ⟨5, 5, 0, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1449 : Outcome ⟨5, 5, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1450 : Outcome ⟨5, 5, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1451 : Outcome ⟨5, 5, 0, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 5, 0, 2⟩, ⟨3, 5, 0, 4⟩, ⟨2, 5, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨0, 5, 0, 10⟩, ⟨5, 4, 0, 2⟩, ⟨5, 3, 0, 4⟩, ⟨5, 2, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨5, 0, 0, 10⟩]
  exact AllWinning.cons node_1082 (AllWinning.cons node_816 (AllWinning.cons node_595 (AllWinning.cons node_381 (AllWinning.cons node_260 (AllWinning.cons node_1100 (AllWinning.cons node_876 (AllWinning.cons node_663 (AllWinning.cons node_460 (AllWinning.cons node_322 (AllWinning.nil))))))))))

theorem node_1452 : Outcome ⟨6, 0, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 4⟩) (by decide) node_821

theorem node_1453 : Outcome ⟨6, 0, 4, 12⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 4⟩) (by decide) node_821

theorem node_1454 : Outcome ⟨6, 0, 4, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 4⟩) (by decide) node_821

theorem node_1455 : Outcome ⟨6, 1, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.nil)))))

theorem node_1456 : Outcome ⟨6, 1, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))

theorem node_1457 : Outcome ⟨6, 1, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1458 : Outcome ⟨6, 1, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1459 : Outcome ⟨6, 1, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1460 : Outcome ⟨6, 1, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1461 : Outcome ⟨6, 1, 3, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1462 : Outcome ⟨6, 1, 3, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1463 : Outcome ⟨6, 1, 3, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1464 : Outcome ⟨6, 1, 3, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1465 : Outcome ⟨6, 1, 3, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1466 : Outcome ⟨6, 1, 3, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1467 : Outcome ⟨6, 1, 3, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1468 : Outcome ⟨6, 1, 3, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1469 : Outcome ⟨6, 1, 3, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1470 : Outcome ⟨6, 1, 3, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1471 : Outcome ⟨6, 1, 3, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 3, 2⟩, ⟨4, 1, 3, 4⟩, ⟨3, 1, 3, 6⟩, ⟨2, 1, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨0, 1, 3, 12⟩, ⟨6, 0, 3, 2⟩, ⟨6, 1, 2, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 1, 0, 6⟩]
  exact AllWinning.cons node_1088 (AllWinning.cons node_836 (AllWinning.cons node_601 (AllWinning.cons node_389 (AllWinning.cons node_268 (AllWinning.cons node_139 (AllWinning.cons node_1103 (AllWinning.cons node_1108 (AllWinning.cons node_884 (AllWinning.cons node_673 (AllWinning.nil))))))))))

theorem node_1472 : Outcome ⟨6, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 2⟩) (by decide) node_1092

theorem node_1473 : Outcome ⟨6, 2, 2, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 12⟩) (by decide) node_146

theorem node_1474 : Outcome ⟨6, 2, 2, 18⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 12⟩) (by decide) node_146

theorem node_1475 : Outcome ⟨6, 3, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_1118 (AllWinning.nil)))))

theorem node_1476 : Outcome ⟨6, 3, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))

theorem node_1477 : Outcome ⟨6, 3, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1478 : Outcome ⟨6, 3, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1479 : Outcome ⟨6, 3, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1480 : Outcome ⟨6, 3, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1481 : Outcome ⟨6, 3, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1482 : Outcome ⟨6, 3, 1, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1483 : Outcome ⟨6, 3, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1484 : Outcome ⟨6, 3, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1485 : Outcome ⟨6, 3, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1486 : Outcome ⟨6, 3, 1, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1487 : Outcome ⟨6, 3, 1, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1488 : Outcome ⟨6, 3, 1, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1489 : Outcome ⟨6, 3, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1490 : Outcome ⟨6, 3, 1, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1491 : Outcome ⟨6, 3, 1, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 1, 2⟩, ⟨4, 3, 1, 4⟩, ⟨3, 3, 1, 6⟩, ⟨2, 3, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨6, 2, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨6, 3, 0, 2⟩]
  exact AllWinning.cons node_1096 (AllWinning.cons node_843 (AllWinning.cons node_609 (AllWinning.cons node_396 (AllWinning.cons node_275 (AllWinning.cons node_160 (AllWinning.cons node_1113 (AllWinning.cons node_884 (AllWinning.cons node_668 (AllWinning.cons node_1118 (AllWinning.nil))))))))))

theorem node_1492 : Outcome ⟨6, 4, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 4⟩) (by decide) node_847

theorem node_1493 : Outcome ⟨6, 4, 0, 12⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 4⟩) (by decide) node_847

theorem node_1494 : Outcome ⟨6, 4, 0, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 4⟩) (by decide) node_847

theorem node_1495 : Outcome ⟨7, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 2, 2⟩) (by decide) node_1123

theorem node_1496 : Outcome ⟨7, 0, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1497 : Outcome ⟨7, 0, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1498 : Outcome ⟨7, 0, 3, 18⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1499 : Outcome ⟨7, 1, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1500 : Outcome ⟨7, 1, 2, 10⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1501 : Outcome ⟨7, 1, 2, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1502 : Outcome ⟨7, 1, 2, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 6⟩) (by decide) node_618

theorem node_1503 : Outcome ⟨7, 2, 1, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1504 : Outcome ⟨7, 2, 1, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1505 : Outcome ⟨7, 2, 1, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1506 : Outcome ⟨7, 2, 1, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 6⟩) (by decide) node_636

theorem node_1507 : Outcome ⟨7, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 0, 2⟩) (by decide) node_1132

theorem node_1508 : Outcome ⟨7, 3, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

end RQ9F1
