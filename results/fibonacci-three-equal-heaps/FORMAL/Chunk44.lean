import Chunk43
set_option autoImplicit false
namespace RQ9F1

theorem node_10292 : Outcome ⟨5, 9, 9, 10⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 16⟩) (by decide) node_3641

theorem node_10293 : Outcome ⟨5, 10, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 8, 2⟩, ⟨3, 10, 8, 4⟩, ⟨5, 9, 8, 2⟩, ⟨5, 8, 8, 4⟩, ⟨5, 10, 7, 2⟩, ⟨5, 10, 6, 4⟩]
  exact AllWinning.cons node_9235 (AllWinning.cons node_8186 (AllWinning.cons node_9303 (AllWinning.cons node_8314 (AllWinning.cons node_9307 (AllWinning.cons node_8321 (AllWinning.nil))))))

theorem node_10294 : Outcome ⟨5, 10, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 8, 2⟩, ⟨3, 10, 8, 4⟩, ⟨2, 10, 8, 6⟩, ⟨1, 10, 8, 8⟩, ⟨5, 9, 8, 2⟩, ⟨5, 8, 8, 4⟩, ⟨5, 7, 8, 6⟩, ⟨5, 6, 8, 8⟩, ⟨5, 10, 7, 2⟩, ⟨5, 10, 6, 4⟩, ⟨5, 10, 5, 6⟩, ⟨5, 10, 4, 8⟩]
  exact AllWinning.cons node_9235 (AllWinning.cons node_8186 (AllWinning.cons node_7159 (AllWinning.cons node_6159 (AllWinning.cons node_9303 (AllWinning.cons node_8314 (AllWinning.cons node_7377 (AllWinning.cons node_6450 (AllWinning.cons node_9307 (AllWinning.cons node_8321 (AllWinning.cons node_7389 (AllWinning.cons node_6463 (AllWinning.nil))))))))))))

theorem node_10295 : Outcome ⟨5, 10, 8, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10296 : Outcome ⟨5, 10, 8, 10⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10297 : Outcome ⟨5, 10, 8, 12⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10298 : Outcome ⟨5, 10, 8, 22⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10299 : Outcome ⟨5, 11, 7, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 7, 2⟩) (by decide) node_9239

theorem node_10300 : Outcome ⟨5, 11, 7, 6⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 8⟩) (by decide) node_6165

theorem node_10301 : Outcome ⟨5, 11, 7, 8⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 14⟩) (by decide) node_4242

theorem node_10302 : Outcome ⟨5, 11, 7, 12⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 14⟩) (by decide) node_4242

theorem node_10303 : Outcome ⟨5, 11, 7, 22⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 14⟩) (by decide) node_4242

theorem node_10304 : Outcome ⟨5, 12, 6, 2⟩ true :=
  Outcome.win (q := ⟨5, 12, 4, 4⟩) (by decide) node_8326

theorem node_10305 : Outcome ⟨5, 12, 6, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 4, 4⟩) (by decide) node_8326

theorem node_10306 : Outcome ⟨5, 12, 6, 22⟩ true :=
  Outcome.win (q := ⟨5, 12, 4, 4⟩) (by decide) node_8326

theorem node_10307 : Outcome ⟨5, 12, 6, 24⟩ true :=
  Outcome.win (q := ⟨5, 12, 4, 4⟩) (by decide) node_8326

theorem node_10308 : Outcome ⟨5, 13, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 5, 2⟩, ⟨3, 13, 5, 4⟩, ⟨5, 12, 5, 2⟩, ⟨5, 11, 5, 4⟩, ⟨5, 13, 4, 2⟩, ⟨5, 13, 3, 4⟩]
  exact AllWinning.cons node_9249 (AllWinning.cons node_8198 (AllWinning.cons node_9315 (AllWinning.cons node_8325 (AllWinning.cons node_9319 (AllWinning.cons node_8330 (AllWinning.nil))))))

theorem node_10309 : Outcome ⟨5, 13, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 5, 2⟩, ⟨3, 13, 5, 4⟩, ⟨2, 13, 5, 6⟩, ⟨1, 13, 5, 8⟩, ⟨5, 12, 5, 2⟩, ⟨5, 11, 5, 4⟩, ⟨5, 10, 5, 6⟩, ⟨5, 9, 5, 8⟩, ⟨5, 13, 4, 2⟩, ⟨5, 13, 3, 4⟩, ⟨5, 13, 2, 6⟩, ⟨5, 13, 1, 8⟩]
  exact AllWinning.cons node_9249 (AllWinning.cons node_8198 (AllWinning.cons node_7173 (AllWinning.cons node_6179 (AllWinning.cons node_9315 (AllWinning.cons node_8325 (AllWinning.cons node_7389 (AllWinning.cons node_6459 (AllWinning.cons node_9319 (AllWinning.cons node_8330 (AllWinning.cons node_7399 (AllWinning.cons node_6481 (AllWinning.nil))))))))))))

theorem node_10310 : Outcome ⟨5, 13, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 5, 2⟩, ⟨3, 13, 5, 4⟩, ⟨2, 13, 5, 6⟩, ⟨1, 13, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨5, 12, 5, 2⟩, ⟨5, 11, 5, 4⟩, ⟨5, 10, 5, 6⟩, ⟨5, 9, 5, 8⟩, ⟨5, 8, 5, 10⟩, ⟨5, 7, 5, 12⟩, ⟨5, 13, 4, 2⟩, ⟨5, 13, 3, 4⟩, ⟨5, 13, 2, 6⟩, ⟨5, 13, 1, 8⟩, ⟨5, 13, 0, 10⟩]
  exact AllWinning.cons node_9249 (AllWinning.cons node_8198 (AllWinning.cons node_7173 (AllWinning.cons node_6179 (AllWinning.cons node_5369 (AllWinning.cons node_9315 (AllWinning.cons node_8325 (AllWinning.cons node_7389 (AllWinning.cons node_6459 (AllWinning.cons node_5662 (AllWinning.cons node_4958 (AllWinning.cons node_9319 (AllWinning.cons node_8330 (AllWinning.cons node_7399 (AllWinning.cons node_6481 (AllWinning.cons node_5679 (AllWinning.nil))))))))))))))))

theorem node_10311 : Outcome ⟨5, 13, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 5, 2⟩, ⟨3, 13, 5, 4⟩, ⟨2, 13, 5, 6⟩, ⟨1, 13, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨5, 12, 5, 2⟩, ⟨5, 11, 5, 4⟩, ⟨5, 10, 5, 6⟩, ⟨5, 9, 5, 8⟩, ⟨5, 8, 5, 10⟩, ⟨5, 7, 5, 12⟩, ⟨5, 6, 5, 14⟩, ⟨5, 5, 5, 16⟩, ⟨5, 13, 4, 2⟩, ⟨5, 13, 3, 4⟩, ⟨5, 13, 2, 6⟩, ⟨5, 13, 1, 8⟩, ⟨5, 13, 0, 10⟩]
  exact AllWinning.cons node_9249 (AllWinning.cons node_8198 (AllWinning.cons node_7173 (AllWinning.cons node_6179 (AllWinning.cons node_5369 (AllWinning.cons node_9315 (AllWinning.cons node_8325 (AllWinning.cons node_7389 (AllWinning.cons node_6459 (AllWinning.cons node_5662 (AllWinning.cons node_4958 (AllWinning.cons node_4252 (AllWinning.cons node_3660 (AllWinning.cons node_9319 (AllWinning.cons node_8330 (AllWinning.cons node_7399 (AllWinning.cons node_6481 (AllWinning.cons node_5679 (AllWinning.nil))))))))))))))))))

theorem node_10312 : Outcome ⟨5, 13, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 5, 2⟩, ⟨3, 13, 5, 4⟩, ⟨2, 13, 5, 6⟩, ⟨1, 13, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨5, 12, 5, 2⟩, ⟨5, 11, 5, 4⟩, ⟨5, 10, 5, 6⟩, ⟨5, 9, 5, 8⟩, ⟨5, 8, 5, 10⟩, ⟨5, 7, 5, 12⟩, ⟨5, 6, 5, 14⟩, ⟨5, 5, 5, 16⟩, ⟨5, 4, 5, 18⟩, ⟨5, 3, 5, 20⟩, ⟨5, 13, 4, 2⟩, ⟨5, 13, 3, 4⟩, ⟨5, 13, 2, 6⟩, ⟨5, 13, 1, 8⟩, ⟨5, 13, 0, 10⟩]
  exact AllWinning.cons node_9249 (AllWinning.cons node_8198 (AllWinning.cons node_7173 (AllWinning.cons node_6179 (AllWinning.cons node_5369 (AllWinning.cons node_9315 (AllWinning.cons node_8325 (AllWinning.cons node_7389 (AllWinning.cons node_6459 (AllWinning.cons node_5662 (AllWinning.cons node_4958 (AllWinning.cons node_4252 (AllWinning.cons node_3660 (AllWinning.cons node_3103 (AllWinning.cons node_2645 (AllWinning.cons node_9319 (AllWinning.cons node_8330 (AllWinning.cons node_7399 (AllWinning.cons node_6481 (AllWinning.cons node_5679 (AllWinning.nil))))))))))))))))))))

theorem node_10313 : Outcome ⟨5, 13, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 5, 2⟩, ⟨3, 13, 5, 4⟩, ⟨2, 13, 5, 6⟩, ⟨1, 13, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨5, 12, 5, 2⟩, ⟨5, 11, 5, 4⟩, ⟨5, 10, 5, 6⟩, ⟨5, 9, 5, 8⟩, ⟨5, 8, 5, 10⟩, ⟨5, 7, 5, 12⟩, ⟨5, 6, 5, 14⟩, ⟨5, 5, 5, 16⟩, ⟨5, 4, 5, 18⟩, ⟨5, 3, 5, 20⟩, ⟨5, 2, 5, 22⟩, ⟨5, 1, 5, 24⟩, ⟨5, 13, 4, 2⟩, ⟨5, 13, 3, 4⟩, ⟨5, 13, 2, 6⟩, ⟨5, 13, 1, 8⟩, ⟨5, 13, 0, 10⟩]
  exact AllWinning.cons node_9249 (AllWinning.cons node_8198 (AllWinning.cons node_7173 (AllWinning.cons node_6179 (AllWinning.cons node_5369 (AllWinning.cons node_9315 (AllWinning.cons node_8325 (AllWinning.cons node_7389 (AllWinning.cons node_6459 (AllWinning.cons node_5662 (AllWinning.cons node_4958 (AllWinning.cons node_4252 (AllWinning.cons node_3660 (AllWinning.cons node_3103 (AllWinning.cons node_2645 (AllWinning.cons node_2171 (AllWinning.cons node_1757 (AllWinning.cons node_9319 (AllWinning.cons node_8330 (AllWinning.cons node_7399 (AllWinning.cons node_6481 (AllWinning.cons node_5679 (AllWinning.nil))))))))))))))))))))))

theorem node_10314 : Outcome ⟨5, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 6⟩) (by decide) node_7177

theorem node_10315 : Outcome ⟨5, 14, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 6⟩) (by decide) node_7177

theorem node_10316 : Outcome ⟨5, 14, 4, 10⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 14⟩) (by decide) node_4259

theorem node_10317 : Outcome ⟨5, 14, 4, 12⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 14⟩) (by decide) node_4259

theorem node_10318 : Outcome ⟨5, 14, 4, 28⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 14⟩) (by decide) node_4259

theorem node_10319 : Outcome ⟨5, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 2, 2⟩) (by decide) node_9325

theorem node_10320 : Outcome ⟨5, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 8⟩) (by decide) node_6468

theorem node_10321 : Outcome ⟨5, 15, 3, 10⟩ true :=
  Outcome.win (q := ⟨5, 11, 3, 8⟩) (by decide) node_6468

theorem node_10322 : Outcome ⟨5, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 2, 2⟩) (by decide) node_9325

theorem node_10323 : Outcome ⟨5, 16, 2, 10⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 12⟩) (by decide) node_4973

theorem node_10324 : Outcome ⟨5, 17, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 1, 2⟩, ⟨3, 17, 1, 4⟩, ⟨5, 16, 1, 2⟩, ⟨5, 15, 1, 4⟩, ⟨5, 17, 0, 2⟩]
  exact AllWinning.cons node_9262 (AllWinning.cons node_8213 (AllWinning.cons node_9329 (AllWinning.cons node_8336 (AllWinning.cons node_9332 (AllWinning.nil)))))

theorem node_10325 : Outcome ⟨5, 17, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 6⟩) (by decide) node_7191

theorem node_10326 : Outcome ⟨5, 17, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 6⟩) (by decide) node_7191

theorem node_10327 : Outcome ⟨5, 17, 1, 12⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 16⟩) (by decide) node_3679

theorem node_10328 : Outcome ⟨5, 17, 1, 16⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 16⟩) (by decide) node_3679

theorem node_10329 : Outcome ⟨5, 18, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 0, 2⟩, ⟨3, 18, 0, 4⟩, ⟨5, 17, 0, 2⟩, ⟨5, 16, 0, 4⟩]
  exact AllWinning.cons node_9268 (AllWinning.cons node_8216 (AllWinning.cons node_9332 (AllWinning.cons node_8340 (AllWinning.nil))))

theorem node_10330 : Outcome ⟨5, 18, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 0, 2⟩, ⟨3, 18, 0, 4⟩, ⟨2, 18, 0, 6⟩, ⟨1, 18, 0, 8⟩, ⟨5, 17, 0, 2⟩, ⟨5, 16, 0, 4⟩, ⟨5, 15, 0, 6⟩, ⟨5, 14, 0, 8⟩]
  exact AllWinning.cons node_9268 (AllWinning.cons node_8216 (AllWinning.cons node_7197 (AllWinning.cons node_6195 (AllWinning.cons node_9332 (AllWinning.cons node_8340 (AllWinning.cons node_7406 (AllWinning.cons node_6484 (AllWinning.nil))))))))

theorem node_10331 : Outcome ⟨5, 18, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 0, 2⟩, ⟨3, 18, 0, 4⟩, ⟨2, 18, 0, 6⟩, ⟨1, 18, 0, 8⟩, ⟨0, 18, 0, 10⟩, ⟨5, 17, 0, 2⟩, ⟨5, 16, 0, 4⟩, ⟨5, 15, 0, 6⟩, ⟨5, 14, 0, 8⟩, ⟨5, 13, 0, 10⟩, ⟨5, 12, 0, 12⟩]
  exact AllWinning.cons node_9268 (AllWinning.cons node_8216 (AllWinning.cons node_7197 (AllWinning.cons node_6195 (AllWinning.cons node_5388 (AllWinning.cons node_9332 (AllWinning.cons node_8340 (AllWinning.cons node_7406 (AllWinning.cons node_6484 (AllWinning.cons node_5679 (AllWinning.cons node_4986 (AllWinning.nil)))))))))))

theorem node_10332 : Outcome ⟨5, 18, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 0, 2⟩, ⟨3, 18, 0, 4⟩, ⟨2, 18, 0, 6⟩, ⟨1, 18, 0, 8⟩, ⟨0, 18, 0, 10⟩, ⟨5, 17, 0, 2⟩, ⟨5, 16, 0, 4⟩, ⟨5, 15, 0, 6⟩, ⟨5, 14, 0, 8⟩, ⟨5, 13, 0, 10⟩, ⟨5, 12, 0, 12⟩, ⟨5, 11, 0, 14⟩, ⟨5, 10, 0, 16⟩]
  exact AllWinning.cons node_9268 (AllWinning.cons node_8216 (AllWinning.cons node_7197 (AllWinning.cons node_6195 (AllWinning.cons node_5388 (AllWinning.cons node_9332 (AllWinning.cons node_8340 (AllWinning.cons node_7406 (AllWinning.cons node_6484 (AllWinning.cons node_5679 (AllWinning.cons node_4986 (AllWinning.cons node_4281 (AllWinning.cons node_3687 (AllWinning.nil)))))))))))))

theorem node_10333 : Outcome ⟨5, 18, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 0, 2⟩, ⟨3, 18, 0, 4⟩, ⟨2, 18, 0, 6⟩, ⟨1, 18, 0, 8⟩, ⟨0, 18, 0, 10⟩, ⟨5, 17, 0, 2⟩, ⟨5, 16, 0, 4⟩, ⟨5, 15, 0, 6⟩, ⟨5, 14, 0, 8⟩, ⟨5, 13, 0, 10⟩, ⟨5, 12, 0, 12⟩, ⟨5, 11, 0, 14⟩, ⟨5, 10, 0, 16⟩, ⟨5, 9, 0, 18⟩, ⟨5, 8, 0, 20⟩]
  exact AllWinning.cons node_9268 (AllWinning.cons node_8216 (AllWinning.cons node_7197 (AllWinning.cons node_6195 (AllWinning.cons node_5388 (AllWinning.cons node_9332 (AllWinning.cons node_8340 (AllWinning.cons node_7406 (AllWinning.cons node_6484 (AllWinning.cons node_5679 (AllWinning.cons node_4986 (AllWinning.cons node_4281 (AllWinning.cons node_3687 (AllWinning.cons node_3123 (AllWinning.cons node_2665 (AllWinning.nil)))))))))))))))

theorem node_10334 : Outcome ⟨5, 18, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 0, 2⟩, ⟨3, 18, 0, 4⟩, ⟨2, 18, 0, 6⟩, ⟨1, 18, 0, 8⟩, ⟨0, 18, 0, 10⟩, ⟨5, 17, 0, 2⟩, ⟨5, 16, 0, 4⟩, ⟨5, 15, 0, 6⟩, ⟨5, 14, 0, 8⟩, ⟨5, 13, 0, 10⟩, ⟨5, 12, 0, 12⟩, ⟨5, 11, 0, 14⟩, ⟨5, 10, 0, 16⟩, ⟨5, 9, 0, 18⟩, ⟨5, 8, 0, 20⟩, ⟨5, 7, 0, 22⟩, ⟨5, 6, 0, 24⟩]
  exact AllWinning.cons node_9268 (AllWinning.cons node_8216 (AllWinning.cons node_7197 (AllWinning.cons node_6195 (AllWinning.cons node_5388 (AllWinning.cons node_9332 (AllWinning.cons node_8340 (AllWinning.cons node_7406 (AllWinning.cons node_6484 (AllWinning.cons node_5679 (AllWinning.cons node_4986 (AllWinning.cons node_4281 (AllWinning.cons node_3687 (AllWinning.cons node_3123 (AllWinning.cons node_2665 (AllWinning.cons node_2190 (AllWinning.cons node_1777 (AllWinning.nil)))))))))))))))))

theorem node_10335 : Outcome ⟨5, 18, 0, 24⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 26⟩) (by decide) node_1450

theorem node_10336 : Outcome ⟨6, 0, 17, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 4⟩) (by decide) node_8220

theorem node_10337 : Outcome ⟨6, 0, 17, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 4⟩) (by decide) node_8220

theorem node_10338 : Outcome ⟨6, 0, 17, 18⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 22⟩) (by decide) node_2201

theorem node_10339 : Outcome ⟨6, 1, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 16, 2⟩, ⟨4, 1, 16, 4⟩, ⟨6, 0, 16, 2⟩, ⟨6, 1, 15, 2⟩, ⟨6, 1, 14, 4⟩]
  exact AllWinning.cons node_9274 (AllWinning.cons node_8225 (AllWinning.cons node_9335 (AllWinning.cons node_9340 (AllWinning.cons node_8347 (AllWinning.nil)))))

theorem node_10340 : Outcome ⟨6, 1, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 16, 2⟩, ⟨4, 1, 16, 4⟩, ⟨3, 1, 16, 6⟩, ⟨2, 1, 16, 8⟩, ⟨6, 0, 16, 2⟩, ⟨6, 1, 15, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 1, 13, 6⟩, ⟨6, 1, 12, 8⟩]
  exact AllWinning.cons node_9274 (AllWinning.cons node_8225 (AllWinning.cons node_7202 (AllWinning.cons node_6200 (AllWinning.cons node_9335 (AllWinning.cons node_9340 (AllWinning.cons node_8347 (AllWinning.cons node_7416 (AllWinning.cons node_6493 (AllWinning.nil)))))))))

theorem node_10341 : Outcome ⟨6, 1, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 16, 2⟩, ⟨4, 1, 16, 4⟩, ⟨3, 1, 16, 6⟩, ⟨2, 1, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨0, 1, 16, 12⟩, ⟨6, 0, 16, 2⟩, ⟨6, 1, 15, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 1, 13, 6⟩, ⟨6, 1, 12, 8⟩, ⟨6, 1, 11, 10⟩, ⟨6, 1, 10, 12⟩]
  exact AllWinning.cons node_9274 (AllWinning.cons node_8225 (AllWinning.cons node_7202 (AllWinning.cons node_6200 (AllWinning.cons node_5394 (AllWinning.cons node_4573 (AllWinning.cons node_9335 (AllWinning.cons node_9340 (AllWinning.cons node_8347 (AllWinning.cons node_7416 (AllWinning.cons node_6493 (AllWinning.cons node_5688 (AllWinning.cons node_4994 (AllWinning.nil)))))))))))))

theorem node_10342 : Outcome ⟨6, 1, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 16, 2⟩, ⟨4, 1, 16, 4⟩, ⟨3, 1, 16, 6⟩, ⟨2, 1, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨0, 1, 16, 12⟩, ⟨6, 0, 16, 2⟩, ⟨6, 1, 15, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 1, 13, 6⟩, ⟨6, 1, 12, 8⟩, ⟨6, 1, 11, 10⟩, ⟨6, 1, 10, 12⟩, ⟨6, 1, 9, 14⟩, ⟨6, 1, 8, 16⟩]
  exact AllWinning.cons node_9274 (AllWinning.cons node_8225 (AllWinning.cons node_7202 (AllWinning.cons node_6200 (AllWinning.cons node_5394 (AllWinning.cons node_4573 (AllWinning.cons node_9335 (AllWinning.cons node_9340 (AllWinning.cons node_8347 (AllWinning.cons node_7416 (AllWinning.cons node_6493 (AllWinning.cons node_5688 (AllWinning.cons node_4994 (AllWinning.cons node_4287 (AllWinning.cons node_3694 (AllWinning.nil)))))))))))))))

theorem node_10343 : Outcome ⟨6, 1, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 16, 2⟩, ⟨4, 1, 16, 4⟩, ⟨3, 1, 16, 6⟩, ⟨2, 1, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨0, 1, 16, 12⟩, ⟨6, 0, 16, 2⟩, ⟨6, 1, 15, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 1, 13, 6⟩, ⟨6, 1, 12, 8⟩, ⟨6, 1, 11, 10⟩, ⟨6, 1, 10, 12⟩, ⟨6, 1, 9, 14⟩, ⟨6, 1, 8, 16⟩, ⟨6, 1, 7, 18⟩, ⟨6, 1, 6, 20⟩]
  exact AllWinning.cons node_9274 (AllWinning.cons node_8225 (AllWinning.cons node_7202 (AllWinning.cons node_6200 (AllWinning.cons node_5394 (AllWinning.cons node_4573 (AllWinning.cons node_9335 (AllWinning.cons node_9340 (AllWinning.cons node_8347 (AllWinning.cons node_7416 (AllWinning.cons node_6493 (AllWinning.cons node_5688 (AllWinning.cons node_4994 (AllWinning.cons node_4287 (AllWinning.cons node_3694 (AllWinning.cons node_3130 (AllWinning.cons node_2671 (AllWinning.nil)))))))))))))))))

theorem node_10344 : Outcome ⟨6, 1, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 1, 16, 2⟩, ⟨4, 1, 16, 4⟩, ⟨3, 1, 16, 6⟩, ⟨2, 1, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨0, 1, 16, 12⟩, ⟨6, 0, 16, 2⟩, ⟨6, 1, 15, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 1, 13, 6⟩, ⟨6, 1, 12, 8⟩, ⟨6, 1, 11, 10⟩, ⟨6, 1, 10, 12⟩, ⟨6, 1, 9, 14⟩, ⟨6, 1, 8, 16⟩, ⟨6, 1, 7, 18⟩, ⟨6, 1, 6, 20⟩, ⟨6, 1, 5, 22⟩, ⟨6, 1, 4, 24⟩]
  exact AllWinning.cons node_9274 (AllWinning.cons node_8225 (AllWinning.cons node_7202 (AllWinning.cons node_6200 (AllWinning.cons node_5394 (AllWinning.cons node_4573 (AllWinning.cons node_9335 (AllWinning.cons node_9340 (AllWinning.cons node_8347 (AllWinning.cons node_7416 (AllWinning.cons node_6493 (AllWinning.cons node_5688 (AllWinning.cons node_4994 (AllWinning.cons node_4287 (AllWinning.cons node_3694 (AllWinning.cons node_3130 (AllWinning.cons node_2671 (AllWinning.cons node_2207 (AllWinning.cons node_1784 (AllWinning.nil)))))))))))))))))))

theorem node_10345 : Outcome ⟨6, 1, 16, 18⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 26⟩) (by decide) node_1467

theorem node_10346 : Outcome ⟨6, 1, 16, 22⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 26⟩) (by decide) node_1467

theorem node_10347 : Outcome ⟨6, 2, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 8⟩) (by decide) node_6499

theorem node_10348 : Outcome ⟨6, 2, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 12⟩) (by decide) node_4580

theorem node_10349 : Outcome ⟨6, 2, 15, 18⟩ true :=
  Outcome.win (q := ⟨0, 2, 15, 12⟩) (by decide) node_4580

theorem node_10350 : Outcome ⟨6, 3, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 14, 2⟩, ⟨4, 3, 14, 4⟩, ⟨6, 2, 14, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 3, 13, 2⟩, ⟨6, 3, 12, 4⟩]
  exact AllWinning.cons node_9281 (AllWinning.cons node_8231 (AllWinning.cons node_9345 (AllWinning.cons node_8347 (AllWinning.cons node_9349 (AllWinning.cons node_8353 (AllWinning.nil))))))

theorem node_10351 : Outcome ⟨6, 3, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 14, 2⟩, ⟨4, 3, 14, 4⟩, ⟨3, 3, 14, 6⟩, ⟨2, 3, 14, 8⟩, ⟨6, 2, 14, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 0, 14, 6⟩, ⟨6, 3, 13, 2⟩, ⟨6, 3, 12, 4⟩, ⟨6, 3, 11, 6⟩, ⟨6, 3, 10, 8⟩]
  exact AllWinning.cons node_9281 (AllWinning.cons node_8231 (AllWinning.cons node_7212 (AllWinning.cons node_6207 (AllWinning.cons node_9345 (AllWinning.cons node_8347 (AllWinning.cons node_7411 (AllWinning.cons node_9349 (AllWinning.cons node_8353 (AllWinning.cons node_7424 (AllWinning.cons node_6507 (AllWinning.nil)))))))))))

theorem node_10352 : Outcome ⟨6, 3, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 14, 2⟩, ⟨4, 3, 14, 4⟩, ⟨3, 3, 14, 6⟩, ⟨2, 3, 14, 8⟩, ⟨1, 3, 14, 10⟩, ⟨0, 3, 14, 12⟩, ⟨6, 2, 14, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 0, 14, 6⟩, ⟨6, 3, 13, 2⟩, ⟨6, 3, 12, 4⟩, ⟨6, 3, 11, 6⟩, ⟨6, 3, 10, 8⟩, ⟨6, 3, 9, 10⟩, ⟨6, 3, 8, 12⟩]
  exact AllWinning.cons node_9281 (AllWinning.cons node_8231 (AllWinning.cons node_7212 (AllWinning.cons node_6207 (AllWinning.cons node_5402 (AllWinning.cons node_4585 (AllWinning.cons node_9345 (AllWinning.cons node_8347 (AllWinning.cons node_7411 (AllWinning.cons node_9349 (AllWinning.cons node_8353 (AllWinning.cons node_7424 (AllWinning.cons node_6507 (AllWinning.cons node_5695 (AllWinning.cons node_5002 (AllWinning.nil)))))))))))))))

theorem node_10353 : Outcome ⟨6, 3, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 14, 2⟩, ⟨4, 3, 14, 4⟩, ⟨3, 3, 14, 6⟩, ⟨2, 3, 14, 8⟩, ⟨1, 3, 14, 10⟩, ⟨0, 3, 14, 12⟩, ⟨6, 2, 14, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 0, 14, 6⟩, ⟨6, 3, 13, 2⟩, ⟨6, 3, 12, 4⟩, ⟨6, 3, 11, 6⟩, ⟨6, 3, 10, 8⟩, ⟨6, 3, 9, 10⟩, ⟨6, 3, 8, 12⟩, ⟨6, 3, 7, 14⟩, ⟨6, 3, 6, 16⟩]
  exact AllWinning.cons node_9281 (AllWinning.cons node_8231 (AllWinning.cons node_7212 (AllWinning.cons node_6207 (AllWinning.cons node_5402 (AllWinning.cons node_4585 (AllWinning.cons node_9345 (AllWinning.cons node_8347 (AllWinning.cons node_7411 (AllWinning.cons node_9349 (AllWinning.cons node_8353 (AllWinning.cons node_7424 (AllWinning.cons node_6507 (AllWinning.cons node_5695 (AllWinning.cons node_5002 (AllWinning.cons node_4296 (AllWinning.cons node_3702 (AllWinning.nil)))))))))))))))))

theorem node_10354 : Outcome ⟨6, 3, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 3, 14, 2⟩, ⟨4, 3, 14, 4⟩, ⟨3, 3, 14, 6⟩, ⟨2, 3, 14, 8⟩, ⟨1, 3, 14, 10⟩, ⟨0, 3, 14, 12⟩, ⟨6, 2, 14, 2⟩, ⟨6, 1, 14, 4⟩, ⟨6, 0, 14, 6⟩, ⟨6, 3, 13, 2⟩, ⟨6, 3, 12, 4⟩, ⟨6, 3, 11, 6⟩, ⟨6, 3, 10, 8⟩, ⟨6, 3, 9, 10⟩, ⟨6, 3, 8, 12⟩, ⟨6, 3, 7, 14⟩, ⟨6, 3, 6, 16⟩, ⟨6, 3, 5, 18⟩, ⟨6, 3, 4, 20⟩, ⟨6, 3, 3, 22⟩, ⟨6, 3, 2, 24⟩]
  exact AllWinning.cons node_9281 (AllWinning.cons node_8231 (AllWinning.cons node_7212 (AllWinning.cons node_6207 (AllWinning.cons node_5402 (AllWinning.cons node_4585 (AllWinning.cons node_9345 (AllWinning.cons node_8347 (AllWinning.cons node_7411 (AllWinning.cons node_9349 (AllWinning.cons node_8353 (AllWinning.cons node_7424 (AllWinning.cons node_6507 (AllWinning.cons node_5695 (AllWinning.cons node_5002 (AllWinning.cons node_4296 (AllWinning.cons node_3702 (AllWinning.cons node_3140 (AllWinning.cons node_2679 (AllWinning.cons node_2216 (AllWinning.cons node_1790 (AllWinning.nil)))))))))))))))))))))

theorem node_10355 : Outcome ⟨6, 3, 14, 20⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 26⟩) (by decide) node_1487

theorem node_10356 : Outcome ⟨6, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 6⟩) (by decide) node_7428

theorem node_10357 : Outcome ⟨6, 4, 13, 6⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 6⟩) (by decide) node_7428

theorem node_10358 : Outcome ⟨6, 4, 13, 12⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 6⟩) (by decide) node_7428

theorem node_10359 : Outcome ⟨6, 4, 13, 20⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 6⟩) (by decide) node_7428

theorem node_10360 : Outcome ⟨6, 5, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 12, 4⟩) (by decide) node_8240

theorem node_10361 : Outcome ⟨6, 5, 12, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 12, 4⟩) (by decide) node_8240

theorem node_10362 : Outcome ⟨6, 5, 12, 22⟩ true :=
  Outcome.win (q := ⟨4, 5, 12, 4⟩) (by decide) node_8240

theorem node_10363 : Outcome ⟨6, 5, 12, 24⟩ true :=
  Outcome.win (q := ⟨4, 5, 12, 4⟩) (by decide) node_8240

theorem node_10364 : Outcome ⟨6, 6, 11, 2⟩ true :=
  Outcome.win (q := ⟨5, 6, 11, 2⟩) (by decide) node_9291

theorem node_10365 : Outcome ⟨6, 6, 11, 18⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 22⟩) (by decide) node_2235

theorem node_10366 : Outcome ⟨6, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 4⟩) (by decide) node_8368

theorem node_10367 : Outcome ⟨6, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 6⟩) (by decide) node_7225

theorem node_10368 : Outcome ⟨6, 7, 10, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 6⟩) (by decide) node_7225

theorem node_10369 : Outcome ⟨6, 7, 10, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 6⟩) (by decide) node_7225

theorem node_10370 : Outcome ⟨6, 7, 10, 18⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 6⟩) (by decide) node_7225

theorem node_10371 : Outcome ⟨6, 7, 10, 22⟩ true :=
  Outcome.win (q := ⟨3, 7, 10, 6⟩) (by decide) node_7225

theorem node_10372 : Outcome ⟨6, 8, 9, 2⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 4⟩) (by decide) node_8380

theorem node_10373 : Outcome ⟨6, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 4⟩) (by decide) node_8380

theorem node_10374 : Outcome ⟨6, 8, 9, 6⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 4⟩) (by decide) node_8380

theorem node_10375 : Outcome ⟨6, 8, 9, 18⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 4⟩) (by decide) node_8380

theorem node_10376 : Outcome ⟨6, 9, 8, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 4⟩) (by decide) node_8368

theorem node_10377 : Outcome ⟨6, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 4⟩) (by decide) node_8368

theorem node_10378 : Outcome ⟨6, 9, 8, 6⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 4⟩) (by decide) node_8368

theorem node_10379 : Outcome ⟨6, 9, 8, 18⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 4⟩) (by decide) node_8368

theorem node_10380 : Outcome ⟨6, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 4⟩) (by decide) node_8380

theorem node_10381 : Outcome ⟨6, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 6⟩) (by decide) node_7240

theorem node_10382 : Outcome ⟨6, 10, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 6⟩) (by decide) node_7240

theorem node_10383 : Outcome ⟨6, 10, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 6⟩) (by decide) node_7240

theorem node_10384 : Outcome ⟨6, 10, 7, 18⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 6⟩) (by decide) node_7240

theorem node_10385 : Outcome ⟨6, 10, 7, 22⟩ true :=
  Outcome.win (q := ⟨3, 10, 7, 6⟩) (by decide) node_7240

theorem node_10386 : Outcome ⟨6, 11, 6, 2⟩ true :=
  Outcome.win (q := ⟨5, 11, 6, 2⟩) (by decide) node_9312

theorem node_10387 : Outcome ⟨6, 11, 6, 18⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 22⟩) (by decide) node_2201

theorem node_10388 : Outcome ⟨6, 12, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 4⟩) (by decide) node_8264

theorem node_10389 : Outcome ⟨6, 12, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 4⟩) (by decide) node_8264

theorem node_10390 : Outcome ⟨6, 12, 5, 22⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 4⟩) (by decide) node_8264

theorem node_10391 : Outcome ⟨6, 12, 5, 24⟩ true :=
  Outcome.win (q := ⟨4, 12, 5, 4⟩) (by decide) node_8264

theorem node_10392 : Outcome ⟨6, 13, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 6⟩) (by decide) node_7457

theorem node_10393 : Outcome ⟨6, 13, 4, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 6⟩) (by decide) node_7457

theorem node_10394 : Outcome ⟨6, 13, 4, 12⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 6⟩) (by decide) node_7457

theorem node_10395 : Outcome ⟨6, 13, 4, 20⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 6⟩) (by decide) node_7457

theorem node_10396 : Outcome ⟨6, 14, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 3, 2⟩, ⟨4, 14, 3, 4⟩, ⟨6, 13, 3, 2⟩, ⟨6, 12, 3, 4⟩, ⟨6, 14, 2, 2⟩, ⟨6, 14, 1, 4⟩]
  exact AllWinning.cons node_9322 (AllWinning.cons node_8273 (AllWinning.cons node_9387 (AllWinning.cons node_8402 (AllWinning.cons node_9390 (AllWinning.cons node_8408 (AllWinning.nil))))))

theorem node_10397 : Outcome ⟨6, 14, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 3, 2⟩, ⟨4, 14, 3, 4⟩, ⟨3, 14, 3, 6⟩, ⟨2, 14, 3, 8⟩, ⟨6, 13, 3, 2⟩, ⟨6, 12, 3, 4⟩, ⟨6, 11, 3, 6⟩, ⟨6, 10, 3, 8⟩, ⟨6, 14, 2, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 14, 0, 6⟩]
  exact AllWinning.cons node_9322 (AllWinning.cons node_8273 (AllWinning.cons node_7253 (AllWinning.cons node_6259 (AllWinning.cons node_9387 (AllWinning.cons node_8402 (AllWinning.cons node_7467 (AllWinning.cons node_6528 (AllWinning.cons node_9390 (AllWinning.cons node_8408 (AllWinning.cons node_7479 (AllWinning.nil)))))))))))

theorem node_10398 : Outcome ⟨6, 14, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 3, 2⟩, ⟨4, 14, 3, 4⟩, ⟨3, 14, 3, 6⟩, ⟨2, 14, 3, 8⟩, ⟨1, 14, 3, 10⟩, ⟨0, 14, 3, 12⟩, ⟨6, 13, 3, 2⟩, ⟨6, 12, 3, 4⟩, ⟨6, 11, 3, 6⟩, ⟨6, 10, 3, 8⟩, ⟨6, 9, 3, 10⟩, ⟨6, 8, 3, 12⟩, ⟨6, 14, 2, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 14, 0, 6⟩]
  exact AllWinning.cons node_9322 (AllWinning.cons node_8273 (AllWinning.cons node_7253 (AllWinning.cons node_6259 (AllWinning.cons node_5443 (AllWinning.cons node_4632 (AllWinning.cons node_9387 (AllWinning.cons node_8402 (AllWinning.cons node_7467 (AllWinning.cons node_6528 (AllWinning.cons node_5716 (AllWinning.cons node_5017 (AllWinning.cons node_9390 (AllWinning.cons node_8408 (AllWinning.cons node_7479 (AllWinning.nil)))))))))))))))

theorem node_10399 : Outcome ⟨6, 14, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 3, 2⟩, ⟨4, 14, 3, 4⟩, ⟨3, 14, 3, 6⟩, ⟨2, 14, 3, 8⟩, ⟨1, 14, 3, 10⟩, ⟨0, 14, 3, 12⟩, ⟨6, 13, 3, 2⟩, ⟨6, 12, 3, 4⟩, ⟨6, 11, 3, 6⟩, ⟨6, 10, 3, 8⟩, ⟨6, 9, 3, 10⟩, ⟨6, 8, 3, 12⟩, ⟨6, 7, 3, 14⟩, ⟨6, 6, 3, 16⟩, ⟨6, 14, 2, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 14, 0, 6⟩]
  exact AllWinning.cons node_9322 (AllWinning.cons node_8273 (AllWinning.cons node_7253 (AllWinning.cons node_6259 (AllWinning.cons node_5443 (AllWinning.cons node_4632 (AllWinning.cons node_9387 (AllWinning.cons node_8402 (AllWinning.cons node_7467 (AllWinning.cons node_6528 (AllWinning.cons node_5716 (AllWinning.cons node_5017 (AllWinning.cons node_4314 (AllWinning.cons node_3711 (AllWinning.cons node_9390 (AllWinning.cons node_8408 (AllWinning.cons node_7479 (AllWinning.nil)))))))))))))))))

theorem node_10400 : Outcome ⟨6, 14, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 3, 2⟩, ⟨4, 14, 3, 4⟩, ⟨3, 14, 3, 6⟩, ⟨2, 14, 3, 8⟩, ⟨1, 14, 3, 10⟩, ⟨0, 14, 3, 12⟩, ⟨6, 13, 3, 2⟩, ⟨6, 12, 3, 4⟩, ⟨6, 11, 3, 6⟩, ⟨6, 10, 3, 8⟩, ⟨6, 9, 3, 10⟩, ⟨6, 8, 3, 12⟩, ⟨6, 7, 3, 14⟩, ⟨6, 6, 3, 16⟩, ⟨6, 5, 3, 18⟩, ⟨6, 4, 3, 20⟩, ⟨6, 3, 3, 22⟩, ⟨6, 2, 3, 24⟩, ⟨6, 14, 2, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 14, 0, 6⟩]
  exact AllWinning.cons node_9322 (AllWinning.cons node_8273 (AllWinning.cons node_7253 (AllWinning.cons node_6259 (AllWinning.cons node_5443 (AllWinning.cons node_4632 (AllWinning.cons node_9387 (AllWinning.cons node_8402 (AllWinning.cons node_7467 (AllWinning.cons node_6528 (AllWinning.cons node_5716 (AllWinning.cons node_5017 (AllWinning.cons node_4314 (AllWinning.cons node_3711 (AllWinning.cons node_3147 (AllWinning.cons node_2683 (AllWinning.cons node_2216 (AllWinning.cons node_1787 (AllWinning.cons node_9390 (AllWinning.cons node_8408 (AllWinning.cons node_7479 (AllWinning.nil)))))))))))))))))))))

theorem node_10401 : Outcome ⟨6, 14, 3, 20⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 26⟩) (by decide) node_1467

theorem node_10402 : Outcome ⟨6, 15, 2, 4⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 8⟩) (by decide) node_6533

theorem node_10403 : Outcome ⟨6, 15, 2, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 12⟩) (by decide) node_4639

theorem node_10404 : Outcome ⟨6, 15, 2, 18⟩ true :=
  Outcome.win (q := ⟨0, 15, 2, 12⟩) (by decide) node_4639

theorem node_10405 : Outcome ⟨6, 16, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 1, 2⟩, ⟨4, 16, 1, 4⟩, ⟨6, 15, 1, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 16, 0, 2⟩]
  exact AllWinning.cons node_9329 (AllWinning.cons node_8278 (AllWinning.cons node_9395 (AllWinning.cons node_8408 (AllWinning.cons node_9399 (AllWinning.nil)))))

theorem node_10406 : Outcome ⟨6, 16, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 1, 2⟩, ⟨4, 16, 1, 4⟩, ⟨3, 16, 1, 6⟩, ⟨2, 16, 1, 8⟩, ⟨6, 15, 1, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 13, 1, 6⟩, ⟨6, 12, 1, 8⟩, ⟨6, 16, 0, 2⟩]
  exact AllWinning.cons node_9329 (AllWinning.cons node_8278 (AllWinning.cons node_7261 (AllWinning.cons node_6266 (AllWinning.cons node_9395 (AllWinning.cons node_8408 (AllWinning.cons node_7474 (AllWinning.cons node_6541 (AllWinning.cons node_9399 (AllWinning.nil)))))))))

theorem node_10407 : Outcome ⟨6, 16, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 1, 2⟩, ⟨4, 16, 1, 4⟩, ⟨3, 16, 1, 6⟩, ⟨2, 16, 1, 8⟩, ⟨1, 16, 1, 10⟩, ⟨0, 16, 1, 12⟩, ⟨6, 15, 1, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 13, 1, 6⟩, ⟨6, 12, 1, 8⟩, ⟨6, 11, 1, 10⟩, ⟨6, 10, 1, 12⟩, ⟨6, 16, 0, 2⟩]
  exact AllWinning.cons node_9329 (AllWinning.cons node_8278 (AllWinning.cons node_7261 (AllWinning.cons node_6266 (AllWinning.cons node_5451 (AllWinning.cons node_4644 (AllWinning.cons node_9395 (AllWinning.cons node_8408 (AllWinning.cons node_7474 (AllWinning.cons node_6541 (AllWinning.cons node_5723 (AllWinning.cons node_5023 (AllWinning.cons node_9399 (AllWinning.nil)))))))))))))

theorem node_10408 : Outcome ⟨6, 16, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 1, 2⟩, ⟨4, 16, 1, 4⟩, ⟨3, 16, 1, 6⟩, ⟨2, 16, 1, 8⟩, ⟨1, 16, 1, 10⟩, ⟨0, 16, 1, 12⟩, ⟨6, 15, 1, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 13, 1, 6⟩, ⟨6, 12, 1, 8⟩, ⟨6, 11, 1, 10⟩, ⟨6, 10, 1, 12⟩, ⟨6, 9, 1, 14⟩, ⟨6, 8, 1, 16⟩, ⟨6, 16, 0, 2⟩]
  exact AllWinning.cons node_9329 (AllWinning.cons node_8278 (AllWinning.cons node_7261 (AllWinning.cons node_6266 (AllWinning.cons node_5451 (AllWinning.cons node_4644 (AllWinning.cons node_9395 (AllWinning.cons node_8408 (AllWinning.cons node_7474 (AllWinning.cons node_6541 (AllWinning.cons node_5723 (AllWinning.cons node_5023 (AllWinning.cons node_4322 (AllWinning.cons node_3722 (AllWinning.cons node_9399 (AllWinning.nil)))))))))))))))

theorem node_10409 : Outcome ⟨6, 16, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 1, 2⟩, ⟨4, 16, 1, 4⟩, ⟨3, 16, 1, 6⟩, ⟨2, 16, 1, 8⟩, ⟨1, 16, 1, 10⟩, ⟨0, 16, 1, 12⟩, ⟨6, 15, 1, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 13, 1, 6⟩, ⟨6, 12, 1, 8⟩, ⟨6, 11, 1, 10⟩, ⟨6, 10, 1, 12⟩, ⟨6, 9, 1, 14⟩, ⟨6, 8, 1, 16⟩, ⟨6, 7, 1, 18⟩, ⟨6, 6, 1, 20⟩, ⟨6, 16, 0, 2⟩]
  exact AllWinning.cons node_9329 (AllWinning.cons node_8278 (AllWinning.cons node_7261 (AllWinning.cons node_6266 (AllWinning.cons node_5451 (AllWinning.cons node_4644 (AllWinning.cons node_9395 (AllWinning.cons node_8408 (AllWinning.cons node_7474 (AllWinning.cons node_6541 (AllWinning.cons node_5723 (AllWinning.cons node_5023 (AllWinning.cons node_4322 (AllWinning.cons node_3722 (AllWinning.cons node_3157 (AllWinning.cons node_2689 (AllWinning.cons node_9399 (AllWinning.nil)))))))))))))))))

theorem node_10410 : Outcome ⟨6, 16, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 1, 2⟩, ⟨4, 16, 1, 4⟩, ⟨3, 16, 1, 6⟩, ⟨2, 16, 1, 8⟩, ⟨1, 16, 1, 10⟩, ⟨0, 16, 1, 12⟩, ⟨6, 15, 1, 2⟩, ⟨6, 14, 1, 4⟩, ⟨6, 13, 1, 6⟩, ⟨6, 12, 1, 8⟩, ⟨6, 11, 1, 10⟩, ⟨6, 10, 1, 12⟩, ⟨6, 9, 1, 14⟩, ⟨6, 8, 1, 16⟩, ⟨6, 7, 1, 18⟩, ⟨6, 6, 1, 20⟩, ⟨6, 5, 1, 22⟩, ⟨6, 4, 1, 24⟩, ⟨6, 16, 0, 2⟩]
  exact AllWinning.cons node_9329 (AllWinning.cons node_8278 (AllWinning.cons node_7261 (AllWinning.cons node_6266 (AllWinning.cons node_5451 (AllWinning.cons node_4644 (AllWinning.cons node_9395 (AllWinning.cons node_8408 (AllWinning.cons node_7474 (AllWinning.cons node_6541 (AllWinning.cons node_5723 (AllWinning.cons node_5023 (AllWinning.cons node_4322 (AllWinning.cons node_3722 (AllWinning.cons node_3157 (AllWinning.cons node_2689 (AllWinning.cons node_2224 (AllWinning.cons node_1794 (AllWinning.cons node_9399 (AllWinning.nil)))))))))))))))))))

theorem node_10411 : Outcome ⟨6, 16, 1, 18⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 26⟩) (by decide) node_1487

theorem node_10412 : Outcome ⟨6, 16, 1, 22⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 26⟩) (by decide) node_1487

theorem node_10413 : Outcome ⟨6, 17, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 4⟩) (by decide) node_8282

theorem node_10414 : Outcome ⟨6, 17, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 17, 0, 4⟩) (by decide) node_8282

theorem node_10415 : Outcome ⟨6, 17, 0, 18⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 22⟩) (by decide) node_2235

theorem node_10416 : Outcome ⟨7, 0, 16, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 15, 2⟩) (by decide) node_9404

theorem node_10417 : Outcome ⟨7, 0, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 8⟩) (by decide) node_6275

theorem node_10418 : Outcome ⟨7, 0, 16, 18⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 18⟩) (by decide) node_3169

theorem node_10419 : Outcome ⟨7, 0, 16, 22⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 18⟩) (by decide) node_3169

theorem node_10420 : Outcome ⟨7, 1, 15, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 15, 2⟩) (by decide) node_9404

theorem node_10421 : Outcome ⟨7, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 8⟩) (by decide) node_6559

theorem node_10422 : Outcome ⟨7, 1, 15, 8⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 8⟩) (by decide) node_6559

theorem node_10423 : Outcome ⟨7, 1, 15, 18⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 8⟩) (by decide) node_6559

theorem node_10424 : Outcome ⟨7, 1, 15, 22⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 8⟩) (by decide) node_6559

theorem node_10425 : Outcome ⟨7, 2, 14, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 6⟩) (by decide) node_7279

theorem node_10426 : Outcome ⟨7, 2, 14, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 6⟩) (by decide) node_7279

theorem node_10427 : Outcome ⟨7, 2, 14, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 6⟩) (by decide) node_7279

theorem node_10428 : Outcome ⟨7, 3, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 13, 2⟩, ⟨5, 3, 13, 4⟩, ⟨7, 2, 13, 2⟩, ⟨7, 1, 13, 4⟩, ⟨7, 3, 12, 2⟩, ⟨7, 3, 11, 4⟩]
  exact AllWinning.cons node_9349 (AllWinning.cons node_8297 (AllWinning.cons node_9411 (AllWinning.cons node_8420 (AllWinning.cons node_9415 (AllWinning.cons node_8433 (AllWinning.nil))))))

theorem node_10429 : Outcome ⟨7, 3, 13, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 8⟩) (by decide) node_6291

theorem node_10430 : Outcome ⟨7, 3, 13, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 8⟩) (by decide) node_6291

theorem node_10431 : Outcome ⟨7, 3, 13, 12⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 22⟩) (by decide) node_2275

theorem node_10432 : Outcome ⟨7, 4, 12, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 12, 4⟩) (by decide) node_8300

theorem node_10433 : Outcome ⟨7, 4, 12, 4⟩ true :=
  Outcome.win (q := ⟨5, 4, 12, 4⟩) (by decide) node_8300

theorem node_10434 : Outcome ⟨7, 4, 12, 6⟩ true :=
  Outcome.win (q := ⟨5, 4, 12, 4⟩) (by decide) node_8300

theorem node_10435 : Outcome ⟨7, 4, 12, 12⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 14⟩) (by decide) node_4349

theorem node_10436 : Outcome ⟨7, 4, 12, 22⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 14⟩) (by decide) node_4349

theorem node_10437 : Outcome ⟨7, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨6, 5, 11, 2⟩) (by decide) node_9356

theorem node_10438 : Outcome ⟨7, 5, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 8⟩) (by decide) node_6302

theorem node_10439 : Outcome ⟨7, 5, 11, 8⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 14⟩) (by decide) node_4364

theorem node_10440 : Outcome ⟨7, 5, 11, 12⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 14⟩) (by decide) node_4364

theorem node_10441 : Outcome ⟨7, 5, 11, 22⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 14⟩) (by decide) node_4364

theorem node_10442 : Outcome ⟨7, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 4⟩) (by decide) node_8444

theorem node_10443 : Outcome ⟨7, 6, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 6⟩) (by decide) node_7295

theorem node_10444 : Outcome ⟨7, 6, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 6⟩) (by decide) node_7295

theorem node_10445 : Outcome ⟨7, 6, 10, 8⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 6⟩) (by decide) node_7295

theorem node_10446 : Outcome ⟨7, 6, 10, 18⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 6⟩) (by decide) node_7295

theorem node_10447 : Outcome ⟨7, 6, 10, 22⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 6⟩) (by decide) node_7295

theorem node_10448 : Outcome ⟨7, 7, 9, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 4⟩) (by decide) node_8456

theorem node_10449 : Outcome ⟨7, 7, 9, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 4⟩) (by decide) node_8456

theorem node_10450 : Outcome ⟨7, 7, 9, 12⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 18⟩) (by decide) node_3206

theorem node_10451 : Outcome ⟨7, 8, 8, 2⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 4⟩) (by decide) node_8444

theorem node_10452 : Outcome ⟨7, 8, 8, 6⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 4⟩) (by decide) node_8444

theorem node_10453 : Outcome ⟨7, 8, 8, 10⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 14⟩) (by decide) node_3964

theorem node_10454 : Outcome ⟨7, 8, 8, 22⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 14⟩) (by decide) node_3964

theorem node_10455 : Outcome ⟨7, 8, 8, 24⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 14⟩) (by decide) node_3964

theorem node_10456 : Outcome ⟨7, 9, 7, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 4⟩) (by decide) node_8456

theorem node_10457 : Outcome ⟨7, 9, 7, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 7, 4⟩) (by decide) node_8456

theorem node_10458 : Outcome ⟨7, 9, 7, 12⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 18⟩) (by decide) node_3169

theorem node_10459 : Outcome ⟨7, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 4⟩) (by decide) node_8460

theorem node_10460 : Outcome ⟨7, 10, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 6⟩) (by decide) node_7315

theorem node_10461 : Outcome ⟨7, 10, 6, 6⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 6⟩) (by decide) node_7315

theorem node_10462 : Outcome ⟨7, 10, 6, 8⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 6⟩) (by decide) node_7315

theorem node_10463 : Outcome ⟨7, 10, 6, 18⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 6⟩) (by decide) node_7315

theorem node_10464 : Outcome ⟨7, 10, 6, 22⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 6⟩) (by decide) node_7315

theorem node_10465 : Outcome ⟨7, 11, 5, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 5, 2⟩) (by decide) node_9380

theorem node_10466 : Outcome ⟨7, 11, 5, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 8⟩) (by decide) node_6333

theorem node_10467 : Outcome ⟨7, 11, 5, 8⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 14⟩) (by decide) node_4349

theorem node_10468 : Outcome ⟨7, 11, 5, 12⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 14⟩) (by decide) node_4349

theorem node_10469 : Outcome ⟨7, 11, 5, 22⟩ true :=
  Outcome.win (q := ⟨7, 4, 5, 14⟩) (by decide) node_4349

theorem node_10470 : Outcome ⟨7, 12, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 12, 4, 4⟩) (by decide) node_8326

theorem node_10471 : Outcome ⟨7, 12, 4, 4⟩ true :=
  Outcome.win (q := ⟨5, 12, 4, 4⟩) (by decide) node_8326

theorem node_10472 : Outcome ⟨7, 12, 4, 6⟩ true :=
  Outcome.win (q := ⟨5, 12, 4, 4⟩) (by decide) node_8326

theorem node_10473 : Outcome ⟨7, 12, 4, 12⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 14⟩) (by decide) node_4364

theorem node_10474 : Outcome ⟨7, 12, 4, 22⟩ true :=
  Outcome.win (q := ⟨7, 5, 4, 14⟩) (by decide) node_4364

theorem node_10475 : Outcome ⟨7, 13, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 3, 2⟩, ⟨5, 13, 3, 4⟩, ⟨7, 12, 3, 2⟩, ⟨7, 11, 3, 4⟩, ⟨7, 13, 2, 2⟩, ⟨7, 13, 1, 4⟩]
  exact AllWinning.cons node_9387 (AllWinning.cons node_8330 (AllWinning.cons node_9452 (AllWinning.cons node_8479 (AllWinning.cons node_9457 (AllWinning.cons node_8490 (AllWinning.nil))))))

theorem node_10476 : Outcome ⟨7, 13, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 8⟩) (by decide) node_6348

theorem node_10477 : Outcome ⟨7, 13, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 8⟩) (by decide) node_6348

theorem node_10478 : Outcome ⟨7, 13, 3, 12⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 22⟩) (by decide) node_2259

theorem node_10479 : Outcome ⟨7, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 12, 2, 4⟩) (by decide) node_8483

theorem node_10480 : Outcome ⟨7, 14, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 6⟩) (by decide) node_7335

theorem node_10481 : Outcome ⟨7, 14, 2, 8⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 6⟩) (by decide) node_7335

theorem node_10482 : Outcome ⟨7, 14, 2, 10⟩ true :=
  Outcome.win (q := ⟨4, 14, 2, 6⟩) (by decide) node_7335

theorem node_10483 : Outcome ⟨7, 15, 1, 4⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 8⟩) (by decide) node_6606

theorem node_10484 : Outcome ⟨7, 15, 1, 8⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 8⟩) (by decide) node_6606

theorem node_10485 : Outcome ⟨7, 15, 1, 18⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 8⟩) (by decide) node_6606

theorem node_10486 : Outcome ⟨7, 15, 1, 22⟩ true :=
  Outcome.win (q := ⟨7, 11, 1, 8⟩) (by decide) node_6606

theorem node_10487 : Outcome ⟨7, 16, 0, 2⟩ true :=
  Outcome.win (q := ⟨7, 15, 0, 2⟩) (by decide) node_9462

theorem node_10488 : Outcome ⟨7, 16, 0, 8⟩ true :=
  Outcome.win (q := ⟨3, 16, 0, 8⟩) (by decide) node_6363

theorem node_10489 : Outcome ⟨7, 16, 0, 18⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 18⟩) (by decide) node_3206

theorem node_10490 : Outcome ⟨7, 16, 0, 22⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 18⟩) (by decide) node_3206

theorem node_10491 : Outcome ⟨8, 0, 15, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 13, 4⟩) (by decide) node_8500

theorem node_10492 : Outcome ⟨8, 0, 15, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 13, 4⟩) (by decide) node_8500

theorem node_10493 : Outcome ⟨8, 0, 15, 10⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 14⟩) (by decide) node_4396

theorem node_10494 : Outcome ⟨8, 0, 15, 14⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 14⟩) (by decide) node_4396

theorem node_10495 : Outcome ⟨8, 1, 14, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10496 : Outcome ⟨8, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10497 : Outcome ⟨8, 1, 14, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10498 : Outcome ⟨8, 2, 13, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 12⟩) (by decide) node_4735

theorem node_10499 : Outcome ⟨8, 2, 13, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 12⟩) (by decide) node_4735

theorem node_10500 : Outcome ⟨8, 3, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10501 : Outcome ⟨8, 3, 12, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10502 : Outcome ⟨8, 3, 12, 10⟩ true :=
  Outcome.win (q := ⟨8, 1, 12, 4⟩) (by decide) node_8503

theorem node_10503 : Outcome ⟨8, 4, 11, 2⟩ true :=
  Outcome.win (q := ⟨7, 4, 11, 2⟩) (by decide) node_9420

theorem node_10504 : Outcome ⟨8, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨7, 4, 11, 2⟩) (by decide) node_9420

theorem node_10505 : Outcome ⟨8, 4, 11, 6⟩ true :=
  Outcome.win (q := ⟨7, 4, 11, 2⟩) (by decide) node_9420

theorem node_10506 : Outcome ⟨8, 4, 11, 12⟩ true :=
  Outcome.win (q := ⟨7, 4, 11, 2⟩) (by decide) node_9420

theorem node_10507 : Outcome ⟨8, 5, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 10, 2⟩, ⟨6, 5, 10, 4⟩, ⟨8, 4, 10, 2⟩, ⟨8, 3, 10, 4⟩, ⟨8, 5, 9, 2⟩, ⟨8, 5, 8, 4⟩]
  exact AllWinning.cons node_9425 (AllWinning.cons node_8360 (AllWinning.cons node_9481 (AllWinning.cons node_8517 (AllWinning.cons node_9485 (AllWinning.cons node_8525 (AllWinning.nil))))))

theorem node_10508 : Outcome ⟨8, 5, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 10, 2⟩, ⟨6, 5, 10, 4⟩, ⟨5, 5, 10, 6⟩, ⟨4, 5, 10, 8⟩, ⟨8, 4, 10, 2⟩, ⟨8, 3, 10, 4⟩, ⟨8, 2, 10, 6⟩, ⟨8, 1, 10, 8⟩, ⟨8, 5, 9, 2⟩, ⟨8, 5, 8, 4⟩, ⟨8, 5, 7, 6⟩, ⟨8, 5, 6, 8⟩]
  exact AllWinning.cons node_9425 (AllWinning.cons node_8360 (AllWinning.cons node_7369 (AllWinning.cons node_6386 (AllWinning.cons node_9481 (AllWinning.cons node_8517 (AllWinning.cons node_7545 (AllWinning.cons node_6626 (AllWinning.cons node_9485 (AllWinning.cons node_8525 (AllWinning.cons node_7558 (AllWinning.cons node_6641 (AllWinning.nil))))))))))))

theorem node_10509 : Outcome ⟨8, 5, 10, 8⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 12⟩) (by decide) node_4748

theorem node_10510 : Outcome ⟨8, 5, 10, 10⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 12⟩) (by decide) node_4748

theorem node_10511 : Outcome ⟨8, 5, 10, 12⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 12⟩) (by decide) node_4748

theorem node_10512 : Outcome ⟨8, 5, 10, 22⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 12⟩) (by decide) node_4748

theorem node_10513 : Outcome ⟨8, 6, 9, 4⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 4⟩) (by decide) node_8530

theorem node_10514 : Outcome ⟨8, 6, 9, 6⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 4⟩) (by decide) node_8530

theorem node_10515 : Outcome ⟨8, 6, 9, 18⟩ true :=
  Outcome.win (q := ⟨8, 6, 7, 4⟩) (by decide) node_8530

theorem node_10516 : Outcome ⟨8, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 4⟩) (by decide) node_8368

theorem node_10517 : Outcome ⟨8, 7, 8, 6⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 4⟩) (by decide) node_8368

theorem node_10518 : Outcome ⟨8, 7, 8, 10⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 14⟩) (by decide) node_4396

theorem node_10519 : Outcome ⟨8, 7, 8, 22⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 14⟩) (by decide) node_4396

theorem node_10520 : Outcome ⟨8, 7, 8, 24⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 14⟩) (by decide) node_4396

theorem node_10521 : Outcome ⟨8, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 4⟩) (by decide) node_8380

theorem node_10522 : Outcome ⟨8, 8, 7, 6⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 4⟩) (by decide) node_8380

theorem node_10523 : Outcome ⟨8, 8, 7, 10⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 14⟩) (by decide) node_4437

theorem node_10524 : Outcome ⟨8, 8, 7, 22⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 14⟩) (by decide) node_4437

theorem node_10525 : Outcome ⟨8, 8, 7, 24⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 14⟩) (by decide) node_4437

theorem node_10526 : Outcome ⟨8, 9, 6, 4⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 4⟩) (by decide) node_8542

theorem node_10527 : Outcome ⟨8, 9, 6, 6⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 4⟩) (by decide) node_8542

theorem node_10528 : Outcome ⟨8, 9, 6, 18⟩ true :=
  Outcome.win (q := ⟨8, 7, 6, 4⟩) (by decide) node_8542

theorem node_10529 : Outcome ⟨8, 10, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 10, 5, 2⟩, ⟨6, 10, 5, 4⟩, ⟨8, 9, 5, 2⟩, ⟨8, 8, 5, 4⟩, ⟨8, 10, 4, 2⟩, ⟨8, 10, 3, 4⟩]
  exact AllWinning.cons node_9443 (AllWinning.cons node_8396 (AllWinning.cons node_9496 (AllWinning.cons node_8554 (AllWinning.cons node_9499 (AllWinning.cons node_8562 (AllWinning.nil))))))

theorem node_10530 : Outcome ⟨8, 10, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 10, 5, 2⟩, ⟨6, 10, 5, 4⟩, ⟨5, 10, 5, 6⟩, ⟨4, 10, 5, 8⟩, ⟨8, 9, 5, 2⟩, ⟨8, 8, 5, 4⟩, ⟨8, 7, 5, 6⟩, ⟨8, 6, 5, 8⟩, ⟨8, 10, 4, 2⟩, ⟨8, 10, 3, 4⟩, ⟨8, 10, 2, 6⟩, ⟨8, 10, 1, 8⟩]
  exact AllWinning.cons node_9443 (AllWinning.cons node_8396 (AllWinning.cons node_7389 (AllWinning.cons node_6403 (AllWinning.cons node_9496 (AllWinning.cons node_8554 (AllWinning.cons node_7564 (AllWinning.cons node_6644 (AllWinning.cons node_9499 (AllWinning.cons node_8562 (AllWinning.cons node_7577 (AllWinning.cons node_6659 (AllWinning.nil))))))))))))

theorem node_10531 : Outcome ⟨8, 10, 5, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 12⟩) (by decide) node_4777

theorem node_10532 : Outcome ⟨8, 10, 5, 10⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 12⟩) (by decide) node_4777

theorem node_10533 : Outcome ⟨8, 10, 5, 12⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 12⟩) (by decide) node_4777

theorem node_10534 : Outcome ⟨8, 10, 5, 22⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 12⟩) (by decide) node_4777

theorem node_10535 : Outcome ⟨8, 11, 4, 2⟩ true :=
  Outcome.win (q := ⟨7, 11, 4, 2⟩) (by decide) node_9447

theorem node_10536 : Outcome ⟨8, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨7, 11, 4, 2⟩) (by decide) node_9447

theorem node_10537 : Outcome ⟨8, 11, 4, 6⟩ true :=
  Outcome.win (q := ⟨7, 11, 4, 2⟩) (by decide) node_9447

theorem node_10538 : Outcome ⟨8, 11, 4, 12⟩ true :=
  Outcome.win (q := ⟨7, 11, 4, 2⟩) (by decide) node_9447

theorem node_10539 : Outcome ⟨8, 12, 3, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10540 : Outcome ⟨8, 12, 3, 8⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10541 : Outcome ⟨8, 12, 3, 10⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10542 : Outcome ⟨8, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 13, 0, 4⟩) (by decide) node_8580

theorem node_10543 : Outcome ⟨8, 13, 2, 6⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 12⟩) (by decide) node_4797

theorem node_10544 : Outcome ⟨8, 13, 2, 12⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 12⟩) (by decide) node_4797

theorem node_10545 : Outcome ⟨8, 14, 1, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

theorem node_10546 : Outcome ⟨8, 14, 1, 4⟩ true :=
  Outcome.win (q := ⟨8, 12, 1, 4⟩) (by decide) node_8570

end RQ9F1
