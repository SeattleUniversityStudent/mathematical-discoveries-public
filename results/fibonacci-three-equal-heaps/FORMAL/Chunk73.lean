import Chunk72
set_option autoImplicit false
namespace RQ9F1

theorem node_16166 : Outcome ⟨5, 8, 16, 4⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 4⟩) (by decide) node_14110

theorem node_16167 : Outcome ⟨5, 9, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 2⟩) (by decide) node_15162

theorem node_16168 : Outcome ⟨5, 9, 15, 8⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 6⟩) (by decide) node_13092

theorem node_16169 : Outcome ⟨5, 10, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 8⟩) (by decide) node_12035

theorem node_16170 : Outcome ⟨5, 10, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 8⟩) (by decide) node_12035

theorem node_16171 : Outcome ⟨5, 10, 14, 10⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 8⟩) (by decide) node_12035

theorem node_16172 : Outcome ⟨5, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 6⟩) (by decide) node_13101

theorem node_16173 : Outcome ⟨5, 12, 12, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 4⟩) (by decide) node_14228

theorem node_16174 : Outcome ⟨5, 12, 12, 12⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 10⟩) (by decide) node_11003

theorem node_16175 : Outcome ⟨5, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 6⟩) (by decide) node_13107

theorem node_16176 : Outcome ⟨5, 14, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 8⟩) (by decide) node_12055

theorem node_16177 : Outcome ⟨5, 14, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 8⟩) (by decide) node_12055

theorem node_16178 : Outcome ⟨5, 14, 10, 10⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 8⟩) (by decide) node_12055

theorem node_16179 : Outcome ⟨5, 15, 9, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 2⟩) (by decide) node_15189

theorem node_16180 : Outcome ⟨5, 15, 9, 8⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 6⟩) (by decide) node_13111

theorem node_16181 : Outcome ⟨5, 16, 8, 4⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 4⟩) (by decide) node_14143

theorem node_16182 : Outcome ⟨5, 17, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 7, 2⟩, ⟨3, 17, 7, 4⟩, ⟨5, 16, 7, 2⟩, ⟨5, 15, 7, 4⟩, ⟨5, 17, 6, 2⟩, ⟨5, 17, 5, 4⟩]
  exact AllWinning.cons node_15143 (AllWinning.cons node_14151 (AllWinning.cons node_15203 (AllWinning.cons node_14246 (AllWinning.cons node_15205 (AllWinning.cons node_14252 (AllWinning.nil))))))

theorem node_16183 : Outcome ⟨5, 17, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 7, 2⟩, ⟨3, 17, 7, 4⟩, ⟨2, 17, 7, 6⟩, ⟨1, 17, 7, 8⟩, ⟨5, 16, 7, 2⟩, ⟨5, 15, 7, 4⟩, ⟨5, 14, 7, 6⟩, ⟨5, 13, 7, 8⟩, ⟨5, 17, 6, 2⟩, ⟨5, 17, 5, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 17, 3, 8⟩]
  exact AllWinning.cons node_15143 (AllWinning.cons node_14151 (AllWinning.cons node_13122 (AllWinning.cons node_12072 (AllWinning.cons node_15203 (AllWinning.cons node_14246 (AllWinning.cons node_13279 (AllWinning.cons node_12320 (AllWinning.cons node_15205 (AllWinning.cons node_14252 (AllWinning.cons node_13286 (AllWinning.cons node_12330 (AllWinning.nil))))))))))))

theorem node_16184 : Outcome ⟨5, 17, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 7, 2⟩, ⟨3, 17, 7, 4⟩, ⟨2, 17, 7, 6⟩, ⟨1, 17, 7, 8⟩, ⟨0, 17, 7, 10⟩, ⟨5, 16, 7, 2⟩, ⟨5, 15, 7, 4⟩, ⟨5, 14, 7, 6⟩, ⟨5, 13, 7, 8⟩, ⟨5, 12, 7, 10⟩, ⟨5, 11, 7, 12⟩, ⟨5, 17, 6, 2⟩, ⟨5, 17, 5, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 17, 3, 8⟩, ⟨5, 17, 2, 10⟩, ⟨5, 17, 1, 12⟩]
  exact AllWinning.cons node_15143 (AllWinning.cons node_14151 (AllWinning.cons node_13122 (AllWinning.cons node_12072 (AllWinning.cons node_11022 (AllWinning.cons node_15203 (AllWinning.cons node_14246 (AllWinning.cons node_13279 (AllWinning.cons node_12320 (AllWinning.cons node_11342 (AllWinning.cons node_10302 (AllWinning.cons node_15205 (AllWinning.cons node_14252 (AllWinning.cons node_13286 (AllWinning.cons node_12330 (AllWinning.cons node_11356 (AllWinning.cons node_10327 (AllWinning.nil)))))))))))))))))

theorem node_16185 : Outcome ⟨5, 17, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 7, 2⟩, ⟨3, 17, 7, 4⟩, ⟨2, 17, 7, 6⟩, ⟨1, 17, 7, 8⟩, ⟨0, 17, 7, 10⟩, ⟨5, 16, 7, 2⟩, ⟨5, 15, 7, 4⟩, ⟨5, 14, 7, 6⟩, ⟨5, 13, 7, 8⟩, ⟨5, 12, 7, 10⟩, ⟨5, 11, 7, 12⟩, ⟨5, 10, 7, 14⟩, ⟨5, 9, 7, 16⟩, ⟨5, 17, 6, 2⟩, ⟨5, 17, 5, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 17, 3, 8⟩, ⟨5, 17, 2, 10⟩, ⟨5, 17, 1, 12⟩, ⟨5, 17, 0, 14⟩]
  exact AllWinning.cons node_15143 (AllWinning.cons node_14151 (AllWinning.cons node_13122 (AllWinning.cons node_12072 (AllWinning.cons node_11022 (AllWinning.cons node_15203 (AllWinning.cons node_14246 (AllWinning.cons node_13279 (AllWinning.cons node_12320 (AllWinning.cons node_11342 (AllWinning.cons node_10302 (AllWinning.cons node_9310 (AllWinning.cons node_8319 (AllWinning.cons node_15205 (AllWinning.cons node_14252 (AllWinning.cons node_13286 (AllWinning.cons node_12330 (AllWinning.cons node_11356 (AllWinning.cons node_10327 (AllWinning.cons node_9334 (AllWinning.nil))))))))))))))))))))

theorem node_16186 : Outcome ⟨5, 17, 7, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 7, 2⟩, ⟨3, 17, 7, 4⟩, ⟨2, 17, 7, 6⟩, ⟨1, 17, 7, 8⟩, ⟨0, 17, 7, 10⟩, ⟨5, 16, 7, 2⟩, ⟨5, 15, 7, 4⟩, ⟨5, 14, 7, 6⟩, ⟨5, 13, 7, 8⟩, ⟨5, 12, 7, 10⟩, ⟨5, 11, 7, 12⟩, ⟨5, 10, 7, 14⟩, ⟨5, 9, 7, 16⟩, ⟨5, 8, 7, 18⟩, ⟨5, 7, 7, 20⟩, ⟨5, 17, 6, 2⟩, ⟨5, 17, 5, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 17, 3, 8⟩, ⟨5, 17, 2, 10⟩, ⟨5, 17, 1, 12⟩, ⟨5, 17, 0, 14⟩]
  exact AllWinning.cons node_15143 (AllWinning.cons node_14151 (AllWinning.cons node_13122 (AllWinning.cons node_12072 (AllWinning.cons node_11022 (AllWinning.cons node_15203 (AllWinning.cons node_14246 (AllWinning.cons node_13279 (AllWinning.cons node_12320 (AllWinning.cons node_11342 (AllWinning.cons node_10302 (AllWinning.cons node_9310 (AllWinning.cons node_8319 (AllWinning.cons node_7383 (AllWinning.cons node_6455 (AllWinning.cons node_15205 (AllWinning.cons node_14252 (AllWinning.cons node_13286 (AllWinning.cons node_12330 (AllWinning.cons node_11356 (AllWinning.cons node_10327 (AllWinning.cons node_9334 (AllWinning.nil))))))))))))))))))))))

theorem node_16187 : Outcome ⟨5, 17, 7, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 7, 2⟩, ⟨3, 17, 7, 4⟩, ⟨2, 17, 7, 6⟩, ⟨1, 17, 7, 8⟩, ⟨0, 17, 7, 10⟩, ⟨5, 16, 7, 2⟩, ⟨5, 15, 7, 4⟩, ⟨5, 14, 7, 6⟩, ⟨5, 13, 7, 8⟩, ⟨5, 12, 7, 10⟩, ⟨5, 11, 7, 12⟩, ⟨5, 10, 7, 14⟩, ⟨5, 9, 7, 16⟩, ⟨5, 8, 7, 18⟩, ⟨5, 7, 7, 20⟩, ⟨5, 6, 7, 22⟩, ⟨5, 5, 7, 24⟩, ⟨5, 17, 6, 2⟩, ⟨5, 17, 5, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 17, 3, 8⟩, ⟨5, 17, 2, 10⟩, ⟨5, 17, 1, 12⟩, ⟨5, 17, 0, 14⟩]
  exact AllWinning.cons node_15143 (AllWinning.cons node_14151 (AllWinning.cons node_13122 (AllWinning.cons node_12072 (AllWinning.cons node_11022 (AllWinning.cons node_15203 (AllWinning.cons node_14246 (AllWinning.cons node_13279 (AllWinning.cons node_12320 (AllWinning.cons node_11342 (AllWinning.cons node_10302 (AllWinning.cons node_9310 (AllWinning.cons node_8319 (AllWinning.cons node_7383 (AllWinning.cons node_6455 (AllWinning.cons node_5655 (AllWinning.cons node_4953 (AllWinning.cons node_15205 (AllWinning.cons node_14252 (AllWinning.cons node_13286 (AllWinning.cons node_12330 (AllWinning.cons node_11356 (AllWinning.cons node_10327 (AllWinning.cons node_9334 (AllWinning.nil))))))))))))))))))))))))

theorem node_16188 : Outcome ⟨5, 18, 6, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 5, 2⟩) (by decide) node_15207

theorem node_16189 : Outcome ⟨5, 18, 6, 10⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 12⟩) (by decide) node_10334

theorem node_16190 : Outcome ⟨5, 18, 6, 12⟩ true :=
  Outcome.win (q := ⟨5, 18, 0, 12⟩) (by decide) node_10334

theorem node_16191 : Outcome ⟨5, 19, 5, 10⟩ true :=
  Outcome.win (q := ⟨5, 13, 5, 12⟩) (by decide) node_10313

theorem node_16192 : Outcome ⟨5, 20, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 4, 2⟩, ⟨3, 20, 4, 4⟩, ⟨5, 19, 4, 2⟩, ⟨5, 18, 4, 4⟩, ⟨5, 20, 3, 2⟩, ⟨5, 20, 2, 4⟩]
  exact AllWinning.cons node_15150 (AllWinning.cons node_14161 (AllWinning.cons node_15210 (AllWinning.cons node_14254 (AllWinning.cons node_15213 (AllWinning.cons node_14261 (AllWinning.nil))))))

theorem node_16193 : Outcome ⟨5, 20, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 4, 2⟩, ⟨3, 20, 4, 4⟩, ⟨2, 20, 4, 6⟩, ⟨1, 20, 4, 8⟩, ⟨5, 19, 4, 2⟩, ⟨5, 18, 4, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 16, 4, 8⟩, ⟨5, 20, 3, 2⟩, ⟨5, 20, 2, 4⟩, ⟨5, 20, 1, 6⟩, ⟨5, 20, 0, 8⟩]
  exact AllWinning.cons node_15150 (AllWinning.cons node_14161 (AllWinning.cons node_13130 (AllWinning.cons node_12082 (AllWinning.cons node_15210 (AllWinning.cons node_14254 (AllWinning.cons node_13286 (AllWinning.cons node_12327 (AllWinning.cons node_15213 (AllWinning.cons node_14261 (AllWinning.cons node_13294 (AllWinning.cons node_12341 (AllWinning.nil))))))))))))

theorem node_16194 : Outcome ⟨5, 20, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 4, 2⟩, ⟨3, 20, 4, 4⟩, ⟨2, 20, 4, 6⟩, ⟨1, 20, 4, 8⟩, ⟨0, 20, 4, 10⟩, ⟨5, 19, 4, 2⟩, ⟨5, 18, 4, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 16, 4, 8⟩, ⟨5, 15, 4, 10⟩, ⟨5, 14, 4, 12⟩, ⟨5, 20, 3, 2⟩, ⟨5, 20, 2, 4⟩, ⟨5, 20, 1, 6⟩, ⟨5, 20, 0, 8⟩]
  exact AllWinning.cons node_15150 (AllWinning.cons node_14161 (AllWinning.cons node_13130 (AllWinning.cons node_12082 (AllWinning.cons node_11032 (AllWinning.cons node_15210 (AllWinning.cons node_14254 (AllWinning.cons node_13286 (AllWinning.cons node_12327 (AllWinning.cons node_11351 (AllWinning.cons node_10317 (AllWinning.cons node_15213 (AllWinning.cons node_14261 (AllWinning.cons node_13294 (AllWinning.cons node_12341 (AllWinning.nil)))))))))))))))

theorem node_16195 : Outcome ⟨5, 20, 4, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 4, 2⟩, ⟨3, 20, 4, 4⟩, ⟨2, 20, 4, 6⟩, ⟨1, 20, 4, 8⟩, ⟨0, 20, 4, 10⟩, ⟨5, 19, 4, 2⟩, ⟨5, 18, 4, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 16, 4, 8⟩, ⟨5, 15, 4, 10⟩, ⟨5, 14, 4, 12⟩, ⟨5, 13, 4, 14⟩, ⟨5, 12, 4, 16⟩, ⟨5, 20, 3, 2⟩, ⟨5, 20, 2, 4⟩, ⟨5, 20, 1, 6⟩, ⟨5, 20, 0, 8⟩]
  exact AllWinning.cons node_15150 (AllWinning.cons node_14161 (AllWinning.cons node_13130 (AllWinning.cons node_12082 (AllWinning.cons node_11032 (AllWinning.cons node_15210 (AllWinning.cons node_14254 (AllWinning.cons node_13286 (AllWinning.cons node_12327 (AllWinning.cons node_11351 (AllWinning.cons node_10317 (AllWinning.cons node_9321 (AllWinning.cons node_8328 (AllWinning.cons node_15213 (AllWinning.cons node_14261 (AllWinning.cons node_13294 (AllWinning.cons node_12341 (AllWinning.nil)))))))))))))))))

theorem node_16196 : Outcome ⟨5, 20, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 4, 2⟩, ⟨3, 20, 4, 4⟩, ⟨2, 20, 4, 6⟩, ⟨1, 20, 4, 8⟩, ⟨0, 20, 4, 10⟩, ⟨5, 19, 4, 2⟩, ⟨5, 18, 4, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 16, 4, 8⟩, ⟨5, 15, 4, 10⟩, ⟨5, 14, 4, 12⟩, ⟨5, 13, 4, 14⟩, ⟨5, 12, 4, 16⟩, ⟨5, 11, 4, 18⟩, ⟨5, 10, 4, 20⟩, ⟨5, 20, 3, 2⟩, ⟨5, 20, 2, 4⟩, ⟨5, 20, 1, 6⟩, ⟨5, 20, 0, 8⟩]
  exact AllWinning.cons node_15150 (AllWinning.cons node_14161 (AllWinning.cons node_13130 (AllWinning.cons node_12082 (AllWinning.cons node_11032 (AllWinning.cons node_15210 (AllWinning.cons node_14254 (AllWinning.cons node_13286 (AllWinning.cons node_12327 (AllWinning.cons node_11351 (AllWinning.cons node_10317 (AllWinning.cons node_9321 (AllWinning.cons node_8328 (AllWinning.cons node_7393 (AllWinning.cons node_6465 (AllWinning.cons node_15213 (AllWinning.cons node_14261 (AllWinning.cons node_13294 (AllWinning.cons node_12341 (AllWinning.nil)))))))))))))))))))

theorem node_16197 : Outcome ⟨5, 20, 4, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 4, 2⟩, ⟨3, 20, 4, 4⟩, ⟨2, 20, 4, 6⟩, ⟨1, 20, 4, 8⟩, ⟨0, 20, 4, 10⟩, ⟨5, 19, 4, 2⟩, ⟨5, 18, 4, 4⟩, ⟨5, 17, 4, 6⟩, ⟨5, 16, 4, 8⟩, ⟨5, 15, 4, 10⟩, ⟨5, 14, 4, 12⟩, ⟨5, 13, 4, 14⟩, ⟨5, 12, 4, 16⟩, ⟨5, 11, 4, 18⟩, ⟨5, 10, 4, 20⟩, ⟨5, 9, 4, 22⟩, ⟨5, 8, 4, 24⟩, ⟨5, 20, 3, 2⟩, ⟨5, 20, 2, 4⟩, ⟨5, 20, 1, 6⟩, ⟨5, 20, 0, 8⟩]
  exact AllWinning.cons node_15150 (AllWinning.cons node_14161 (AllWinning.cons node_13130 (AllWinning.cons node_12082 (AllWinning.cons node_11032 (AllWinning.cons node_15210 (AllWinning.cons node_14254 (AllWinning.cons node_13286 (AllWinning.cons node_12327 (AllWinning.cons node_11351 (AllWinning.cons node_10317 (AllWinning.cons node_9321 (AllWinning.cons node_8328 (AllWinning.cons node_7393 (AllWinning.cons node_6465 (AllWinning.cons node_5667 (AllWinning.cons node_4963 (AllWinning.cons node_15213 (AllWinning.cons node_14261 (AllWinning.cons node_13294 (AllWinning.cons node_12341 (AllWinning.nil)))))))))))))))))))))

theorem node_16198 : Outcome ⟨6, 3, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 8⟩) (by decide) node_12085

theorem node_16199 : Outcome ⟨6, 3, 20, 6⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 12⟩) (by decide) node_10354

theorem node_16200 : Outcome ⟨6, 3, 20, 12⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 12⟩) (by decide) node_10354

theorem node_16201 : Outcome ⟨6, 4, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 4, 19, 2⟩, ⟨4, 4, 19, 4⟩, ⟨6, 3, 19, 2⟩, ⟨6, 2, 19, 4⟩, ⟨6, 4, 18, 2⟩, ⟨6, 4, 17, 4⟩]
  exact AllWinning.cons node_15152 (AllWinning.cons node_14164 (AllWinning.cons node_15216 (AllWinning.cons node_14265 (AllWinning.cons node_15219 (AllWinning.cons node_14271 (AllWinning.nil))))))

theorem node_16202 : Outcome ⟨6, 4, 19, 6⟩ true :=
  Outcome.win (q := ⟨6, 0, 19, 8⟩) (by decide) node_12345

theorem node_16203 : Outcome ⟨6, 4, 19, 16⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 18⟩) (by decide) node_7434

theorem node_16204 : Outcome ⟨6, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 18, 2⟩) (by decide) node_15155

theorem node_16205 : Outcome ⟨6, 5, 18, 10⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 12⟩) (by decide) node_9880

theorem node_16206 : Outcome ⟨6, 5, 18, 12⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 12⟩) (by decide) node_9880

theorem node_16207 : Outcome ⟨6, 6, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨6, 5, 17, 2⟩, ⟨6, 4, 17, 4⟩, ⟨6, 6, 16, 2⟩, ⟨6, 6, 15, 4⟩]
  exact AllWinning.cons node_15158 (AllWinning.cons node_14170 (AllWinning.cons node_15222 (AllWinning.cons node_14271 (AllWinning.cons node_15224 (AllWinning.cons node_14276 (AllWinning.nil))))))

theorem node_16208 : Outcome ⟨6, 6, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨3, 6, 17, 6⟩, ⟨2, 6, 17, 8⟩, ⟨6, 5, 17, 2⟩, ⟨6, 4, 17, 4⟩, ⟨6, 3, 17, 6⟩, ⟨6, 2, 17, 8⟩, ⟨6, 6, 16, 2⟩, ⟨6, 6, 15, 4⟩, ⟨6, 6, 14, 6⟩, ⟨6, 6, 13, 8⟩]
  exact AllWinning.cons node_15158 (AllWinning.cons node_14170 (AllWinning.cons node_13138 (AllWinning.cons node_12098 (AllWinning.cons node_15222 (AllWinning.cons node_14271 (AllWinning.cons node_13303 (AllWinning.cons node_12353 (AllWinning.cons node_15224 (AllWinning.cons node_14276 (AllWinning.cons node_13313 (AllWinning.cons node_12366 (AllWinning.nil))))))))))))

theorem node_16209 : Outcome ⟨6, 6, 17, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 10⟩) (by decide) node_11384

theorem node_16210 : Outcome ⟨6, 7, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 7, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨3, 7, 16, 6⟩, ⟨2, 7, 16, 8⟩, ⟨6, 6, 16, 2⟩, ⟨6, 5, 16, 4⟩, ⟨6, 4, 16, 6⟩, ⟨6, 3, 16, 8⟩, ⟨6, 7, 15, 2⟩, ⟨6, 7, 14, 4⟩, ⟨6, 7, 13, 6⟩, ⟨6, 7, 12, 8⟩]
  exact AllWinning.cons node_15160 (AllWinning.cons node_14172 (AllWinning.cons node_13142 (AllWinning.cons node_12103 (AllWinning.cons node_15224 (AllWinning.cons node_14274 (AllWinning.cons node_13307 (AllWinning.cons node_12357 (AllWinning.cons node_15227 (AllWinning.cons node_14279 (AllWinning.cons node_13318 (AllWinning.cons node_12370 (AllWinning.nil))))))))))))

theorem node_16211 : Outcome ⟨6, 7, 16, 6⟩ true :=
  Outcome.win (q := ⟨6, 1, 16, 12⟩) (by decide) node_10344

theorem node_16212 : Outcome ⟨6, 7, 16, 10⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 16⟩) (by decide) node_8374

theorem node_16213 : Outcome ⟨6, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 2⟩) (by decide) node_15162

theorem node_16214 : Outcome ⟨6, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 2⟩) (by decide) node_15162

theorem node_16215 : Outcome ⟨6, 8, 15, 6⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 2⟩) (by decide) node_15162

theorem node_16216 : Outcome ⟨6, 8, 15, 16⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 16⟩) (by decide) node_8386

theorem node_16217 : Outcome ⟨6, 9, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 2⟩) (by decide) node_15172

theorem node_16218 : Outcome ⟨6, 9, 14, 4⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 2⟩) (by decide) node_15172

theorem node_16219 : Outcome ⟨6, 9, 14, 6⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 12⟩) (by decide) node_10354

theorem node_16220 : Outcome ⟨6, 9, 14, 8⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 12⟩) (by decide) node_10354

theorem node_16221 : Outcome ⟨6, 9, 14, 16⟩ true :=
  Outcome.win (q := ⟨6, 3, 14, 12⟩) (by decide) node_10354

theorem node_16222 : Outcome ⟨6, 10, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 10, 13, 2⟩, ⟨4, 10, 13, 4⟩, ⟨6, 9, 13, 2⟩, ⟨6, 8, 13, 4⟩, ⟨6, 10, 12, 2⟩, ⟨6, 10, 11, 4⟩]
  exact AllWinning.cons node_15177 (AllWinning.cons node_14180 (AllWinning.cons node_15234 (AllWinning.cons node_14284 (AllWinning.cons node_15238 (AllWinning.cons node_14289 (AllWinning.nil))))))

theorem node_16223 : Outcome ⟨6, 10, 13, 8⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 6⟩) (by decide) node_13152

theorem node_16224 : Outcome ⟨6, 10, 13, 10⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 18⟩) (by decide) node_7463

theorem node_16225 : Outcome ⟨6, 11, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 12, 2⟩, ⟨4, 11, 12, 4⟩, ⟨6, 10, 12, 2⟩, ⟨6, 9, 12, 4⟩, ⟨6, 11, 11, 2⟩, ⟨6, 11, 10, 4⟩]
  exact AllWinning.cons node_15181 (AllWinning.cons node_14182 (AllWinning.cons node_15238 (AllWinning.cons node_14286 (AllWinning.cons node_15240 (AllWinning.cons node_14292 (AllWinning.nil))))))

theorem node_16226 : Outcome ⟨6, 11, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 12, 2⟩, ⟨4, 11, 12, 4⟩, ⟨3, 11, 12, 6⟩, ⟨2, 11, 12, 8⟩, ⟨6, 10, 12, 2⟩, ⟨6, 9, 12, 4⟩, ⟨6, 8, 12, 6⟩, ⟨6, 7, 12, 8⟩, ⟨6, 11, 11, 2⟩, ⟨6, 11, 10, 4⟩, ⟨6, 11, 9, 6⟩, ⟨6, 11, 8, 8⟩]
  exact AllWinning.cons node_15181 (AllWinning.cons node_14182 (AllWinning.cons node_13161 (AllWinning.cons node_12115 (AllWinning.cons node_15238 (AllWinning.cons node_14286 (AllWinning.cons node_13322 (AllWinning.cons node_12370 (AllWinning.cons node_15240 (AllWinning.cons node_14292 (AllWinning.cons node_13330 (AllWinning.cons node_12387 (AllWinning.nil))))))))))))

theorem node_16227 : Outcome ⟨6, 11, 12, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 12, 10⟩) (by decide) node_11384

theorem node_16228 : Outcome ⟨6, 11, 12, 10⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 20⟩) (by decide) node_6538

theorem node_16229 : Outcome ⟨6, 11, 12, 12⟩ true :=
  Outcome.win (q := ⟨6, 11, 2, 20⟩) (by decide) node_6538

theorem node_16230 : Outcome ⟨6, 12, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 11, 2⟩, ⟨4, 12, 11, 4⟩, ⟨6, 11, 11, 2⟩, ⟨6, 10, 11, 4⟩, ⟨6, 12, 10, 2⟩, ⟨6, 12, 9, 4⟩]
  exact AllWinning.cons node_15183 (AllWinning.cons node_14184 (AllWinning.cons node_15240 (AllWinning.cons node_14289 (AllWinning.cons node_15243 (AllWinning.cons node_14295 (AllWinning.nil))))))

theorem node_16231 : Outcome ⟨6, 12, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 11, 2⟩, ⟨4, 12, 11, 4⟩, ⟨3, 12, 11, 6⟩, ⟨2, 12, 11, 8⟩, ⟨6, 11, 11, 2⟩, ⟨6, 10, 11, 4⟩, ⟨6, 9, 11, 6⟩, ⟨6, 8, 11, 8⟩, ⟨6, 12, 10, 2⟩, ⟨6, 12, 9, 4⟩, ⟨6, 12, 8, 6⟩, ⟨6, 12, 7, 8⟩]
  exact AllWinning.cons node_15183 (AllWinning.cons node_14184 (AllWinning.cons node_13166 (AllWinning.cons node_12119 (AllWinning.cons node_15240 (AllWinning.cons node_14289 (AllWinning.cons node_13324 (AllWinning.cons node_12375 (AllWinning.cons node_15243 (AllWinning.cons node_14295 (AllWinning.cons node_13334 (AllWinning.cons node_12390 (AllWinning.nil))))))))))))

theorem node_16232 : Outcome ⟨6, 12, 11, 6⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 10⟩) (by decide) node_11409

theorem node_16233 : Outcome ⟨6, 12, 11, 10⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 20⟩) (by decide) node_6504

theorem node_16234 : Outcome ⟨6, 12, 11, 12⟩ true :=
  Outcome.win (q := ⟨6, 2, 11, 20⟩) (by decide) node_6504

theorem node_16235 : Outcome ⟨6, 13, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 10, 2⟩, ⟨4, 13, 10, 4⟩, ⟨6, 12, 10, 2⟩, ⟨6, 11, 10, 4⟩, ⟨6, 13, 9, 2⟩, ⟨6, 13, 8, 4⟩]
  exact AllWinning.cons node_15185 (AllWinning.cons node_14187 (AllWinning.cons node_15243 (AllWinning.cons node_14292 (AllWinning.cons node_15245 (AllWinning.cons node_14299 (AllWinning.nil))))))

theorem node_16236 : Outcome ⟨6, 13, 10, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 6⟩) (by decide) node_13170

theorem node_16237 : Outcome ⟨6, 13, 10, 10⟩ true :=
  Outcome.win (q := ⟨6, 4, 10, 18⟩) (by decide) node_7434

theorem node_16238 : Outcome ⟨6, 14, 9, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 2⟩) (by decide) node_15189

theorem node_16239 : Outcome ⟨6, 14, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 2⟩) (by decide) node_15189

theorem node_16240 : Outcome ⟨6, 14, 9, 6⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 12⟩) (by decide) node_10400

theorem node_16241 : Outcome ⟨6, 14, 9, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 12⟩) (by decide) node_10400

theorem node_16242 : Outcome ⟨6, 14, 9, 16⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 12⟩) (by decide) node_10400

theorem node_16243 : Outcome ⟨6, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 2⟩) (by decide) node_15194

theorem node_16244 : Outcome ⟨6, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 2⟩) (by decide) node_15194

theorem node_16245 : Outcome ⟨6, 15, 8, 6⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 2⟩) (by decide) node_15194

theorem node_16246 : Outcome ⟨6, 15, 8, 16⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 16⟩) (by decide) node_8374

theorem node_16247 : Outcome ⟨6, 16, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 16, 7, 2⟩, ⟨4, 16, 7, 4⟩, ⟨3, 16, 7, 6⟩, ⟨2, 16, 7, 8⟩, ⟨6, 15, 7, 2⟩, ⟨6, 14, 7, 4⟩, ⟨6, 13, 7, 6⟩, ⟨6, 12, 7, 8⟩, ⟨6, 16, 6, 2⟩, ⟨6, 16, 5, 4⟩, ⟨6, 16, 4, 6⟩, ⟨6, 16, 3, 8⟩]
  exact AllWinning.cons node_15203 (AllWinning.cons node_14194 (AllWinning.cons node_13185 (AllWinning.cons node_12130 (AllWinning.cons node_15252 (AllWinning.cons node_14302 (AllWinning.cons node_13338 (AllWinning.cons node_12390 (AllWinning.cons node_15256 (AllWinning.cons node_14309 (AllWinning.cons node_13349 (AllWinning.cons node_12404 (AllWinning.nil))))))))))))

theorem node_16248 : Outcome ⟨6, 16, 7, 6⟩ true :=
  Outcome.win (q := ⟨6, 16, 1, 12⟩) (by decide) node_10410

theorem node_16249 : Outcome ⟨6, 16, 7, 10⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 16⟩) (by decide) node_8386

theorem node_16250 : Outcome ⟨6, 17, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 17, 6, 2⟩, ⟨4, 17, 6, 4⟩, ⟨6, 16, 6, 2⟩, ⟨6, 15, 6, 4⟩, ⟨6, 17, 5, 2⟩, ⟨6, 17, 4, 4⟩]
  exact AllWinning.cons node_15205 (AllWinning.cons node_14196 (AllWinning.cons node_15256 (AllWinning.cons node_14306 (AllWinning.cons node_15259 (AllWinning.cons node_14311 (AllWinning.nil))))))

theorem node_16251 : Outcome ⟨6, 17, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 17, 6, 2⟩, ⟨4, 17, 6, 4⟩, ⟨3, 17, 6, 6⟩, ⟨2, 17, 6, 8⟩, ⟨6, 16, 6, 2⟩, ⟨6, 15, 6, 4⟩, ⟨6, 14, 6, 6⟩, ⟨6, 13, 6, 8⟩, ⟨6, 17, 5, 2⟩, ⟨6, 17, 4, 4⟩, ⟨6, 17, 3, 6⟩, ⟨6, 17, 2, 8⟩]
  exact AllWinning.cons node_15205 (AllWinning.cons node_14196 (AllWinning.cons node_13188 (AllWinning.cons node_12135 (AllWinning.cons node_15256 (AllWinning.cons node_14306 (AllWinning.cons node_13342 (AllWinning.cons node_12394 (AllWinning.cons node_15259 (AllWinning.cons node_14311 (AllWinning.cons node_13352 (AllWinning.cons node_12408 (AllWinning.nil))))))))))))

theorem node_16252 : Outcome ⟨6, 17, 6, 6⟩ true :=
  Outcome.win (q := ⟨6, 12, 6, 10⟩) (by decide) node_11409

theorem node_16253 : Outcome ⟨6, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 18, 5, 2⟩) (by decide) node_15207

theorem node_16254 : Outcome ⟨6, 18, 5, 10⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 12⟩) (by decide) node_9926

theorem node_16255 : Outcome ⟨6, 18, 5, 12⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 12⟩) (by decide) node_9926

theorem node_16256 : Outcome ⟨6, 19, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 19, 4, 2⟩, ⟨4, 19, 4, 4⟩, ⟨6, 18, 4, 2⟩, ⟨6, 17, 4, 4⟩, ⟨6, 19, 3, 2⟩, ⟨6, 19, 2, 4⟩]
  exact AllWinning.cons node_15210 (AllWinning.cons node_14202 (AllWinning.cons node_15261 (AllWinning.cons node_14311 (AllWinning.cons node_15264 (AllWinning.cons node_14317 (AllWinning.nil))))))

theorem node_16257 : Outcome ⟨6, 19, 4, 6⟩ true :=
  Outcome.win (q := ⟨6, 19, 0, 8⟩) (by decide) node_12416

theorem node_16258 : Outcome ⟨6, 19, 4, 16⟩ true :=
  Outcome.win (q := ⟨6, 10, 4, 18⟩) (by decide) node_7463

theorem node_16259 : Outcome ⟨6, 20, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 8⟩) (by decide) node_12148

theorem node_16260 : Outcome ⟨6, 20, 3, 6⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 12⟩) (by decide) node_10400

theorem node_16261 : Outcome ⟨6, 20, 3, 12⟩ true :=
  Outcome.win (q := ⟨6, 14, 3, 12⟩) (by decide) node_10400

theorem node_16262 : Outcome ⟨7, 2, 20, 4⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 8⟩) (by decide) node_12153

theorem node_16263 : Outcome ⟨7, 2, 20, 12⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 8⟩) (by decide) node_12153

theorem node_16264 : Outcome ⟨7, 3, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 3, 19, 2⟩, ⟨5, 3, 19, 4⟩, ⟨7, 2, 19, 2⟩, ⟨7, 1, 19, 4⟩, ⟨7, 3, 18, 2⟩, ⟨7, 3, 17, 4⟩]
  exact AllWinning.cons node_15216 (AllWinning.cons node_14208 (AllWinning.cons node_15271 (AllWinning.cons node_14327 (AllWinning.cons node_15273 (AllWinning.cons node_14337 (AllWinning.nil))))))

theorem node_16265 : Outcome ⟨7, 3, 19, 6⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 12⟩) (by decide) node_9939

theorem node_16266 : Outcome ⟨7, 3, 19, 8⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 12⟩) (by decide) node_9939

theorem node_16267 : Outcome ⟨7, 4, 18, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 4⟩) (by decide) node_14330

theorem node_16268 : Outcome ⟨7, 4, 18, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 4⟩) (by decide) node_14330

theorem node_16269 : Outcome ⟨7, 5, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 5, 17, 2⟩, ⟨5, 5, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨3, 5, 17, 8⟩, ⟨7, 4, 17, 2⟩, ⟨7, 3, 17, 4⟩, ⟨7, 2, 17, 6⟩, ⟨7, 1, 17, 8⟩, ⟨7, 5, 16, 2⟩, ⟨7, 5, 15, 4⟩, ⟨7, 5, 14, 6⟩, ⟨7, 5, 13, 8⟩]
  exact AllWinning.cons node_15222 (AllWinning.cons node_14216 (AllWinning.cons node_13207 (AllWinning.cons node_12163 (AllWinning.cons node_15277 (AllWinning.cons node_14337 (AllWinning.cons node_13368 (AllWinning.cons node_12424 (AllWinning.cons node_15278 (AllWinning.cons node_14342 (AllWinning.cons node_13375 (AllWinning.cons node_12441 (AllWinning.nil))))))))))))

theorem node_16270 : Outcome ⟨7, 5, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 5, 17, 2⟩, ⟨5, 5, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨3, 5, 17, 8⟩, ⟨2, 5, 17, 10⟩, ⟨1, 5, 17, 12⟩, ⟨7, 4, 17, 2⟩, ⟨7, 3, 17, 4⟩, ⟨7, 2, 17, 6⟩, ⟨7, 1, 17, 8⟩, ⟨7, 0, 17, 10⟩, ⟨7, 5, 16, 2⟩, ⟨7, 5, 15, 4⟩, ⟨7, 5, 14, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 5, 12, 10⟩, ⟨7, 5, 11, 12⟩]
  exact AllWinning.cons node_15222 (AllWinning.cons node_14216 (AllWinning.cons node_13207 (AllWinning.cons node_12163 (AllWinning.cons node_11100 (AllWinning.cons node_9949 (AllWinning.cons node_15277 (AllWinning.cons node_14337 (AllWinning.cons node_13368 (AllWinning.cons node_12424 (AllWinning.cons node_11432 (AllWinning.cons node_15278 (AllWinning.cons node_14342 (AllWinning.cons node_13375 (AllWinning.cons node_12441 (AllWinning.cons node_11450 (AllWinning.cons node_10440 (AllWinning.nil)))))))))))))))))

theorem node_16271 : Outcome ⟨7, 5, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 5, 17, 2⟩, ⟨5, 5, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨3, 5, 17, 8⟩, ⟨2, 5, 17, 10⟩, ⟨1, 5, 17, 12⟩, ⟨0, 5, 17, 14⟩, ⟨7, 4, 17, 2⟩, ⟨7, 3, 17, 4⟩, ⟨7, 2, 17, 6⟩, ⟨7, 1, 17, 8⟩, ⟨7, 0, 17, 10⟩, ⟨7, 5, 16, 2⟩, ⟨7, 5, 15, 4⟩, ⟨7, 5, 14, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 5, 12, 10⟩, ⟨7, 5, 11, 12⟩, ⟨7, 5, 10, 14⟩, ⟨7, 5, 9, 16⟩]
  exact AllWinning.cons node_15222 (AllWinning.cons node_14216 (AllWinning.cons node_13207 (AllWinning.cons node_12163 (AllWinning.cons node_11100 (AllWinning.cons node_9949 (AllWinning.cons node_8917 (AllWinning.cons node_15277 (AllWinning.cons node_14337 (AllWinning.cons node_13368 (AllWinning.cons node_12424 (AllWinning.cons node_11432 (AllWinning.cons node_15278 (AllWinning.cons node_14342 (AllWinning.cons node_13375 (AllWinning.cons node_12441 (AllWinning.cons node_11450 (AllWinning.cons node_10440 (AllWinning.cons node_9427 (AllWinning.cons node_8442 (AllWinning.nil))))))))))))))))))))

theorem node_16272 : Outcome ⟨7, 5, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 5, 17, 2⟩, ⟨5, 5, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨3, 5, 17, 8⟩, ⟨2, 5, 17, 10⟩, ⟨1, 5, 17, 12⟩, ⟨0, 5, 17, 14⟩, ⟨7, 4, 17, 2⟩, ⟨7, 3, 17, 4⟩, ⟨7, 2, 17, 6⟩, ⟨7, 1, 17, 8⟩, ⟨7, 0, 17, 10⟩, ⟨7, 5, 16, 2⟩, ⟨7, 5, 15, 4⟩, ⟨7, 5, 14, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 5, 12, 10⟩, ⟨7, 5, 11, 12⟩, ⟨7, 5, 10, 14⟩, ⟨7, 5, 9, 16⟩, ⟨7, 5, 8, 18⟩, ⟨7, 5, 7, 20⟩]
  exact AllWinning.cons node_15222 (AllWinning.cons node_14216 (AllWinning.cons node_13207 (AllWinning.cons node_12163 (AllWinning.cons node_11100 (AllWinning.cons node_9949 (AllWinning.cons node_8917 (AllWinning.cons node_15277 (AllWinning.cons node_14337 (AllWinning.cons node_13368 (AllWinning.cons node_12424 (AllWinning.cons node_11432 (AllWinning.cons node_15278 (AllWinning.cons node_14342 (AllWinning.cons node_13375 (AllWinning.cons node_12441 (AllWinning.cons node_11450 (AllWinning.cons node_10440 (AllWinning.cons node_9427 (AllWinning.cons node_8442 (AllWinning.cons node_7508 (AllWinning.cons node_6584 (AllWinning.nil))))))))))))))))))))))

theorem node_16273 : Outcome ⟨7, 5, 17, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 5, 17, 2⟩, ⟨5, 5, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨3, 5, 17, 8⟩, ⟨2, 5, 17, 10⟩, ⟨1, 5, 17, 12⟩, ⟨0, 5, 17, 14⟩, ⟨7, 4, 17, 2⟩, ⟨7, 3, 17, 4⟩, ⟨7, 2, 17, 6⟩, ⟨7, 1, 17, 8⟩, ⟨7, 0, 17, 10⟩, ⟨7, 5, 16, 2⟩, ⟨7, 5, 15, 4⟩, ⟨7, 5, 14, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 5, 12, 10⟩, ⟨7, 5, 11, 12⟩, ⟨7, 5, 10, 14⟩, ⟨7, 5, 9, 16⟩, ⟨7, 5, 8, 18⟩, ⟨7, 5, 7, 20⟩, ⟨7, 5, 6, 22⟩, ⟨7, 5, 5, 24⟩]
  exact AllWinning.cons node_15222 (AllWinning.cons node_14216 (AllWinning.cons node_13207 (AllWinning.cons node_12163 (AllWinning.cons node_11100 (AllWinning.cons node_9949 (AllWinning.cons node_8917 (AllWinning.cons node_15277 (AllWinning.cons node_14337 (AllWinning.cons node_13368 (AllWinning.cons node_12424 (AllWinning.cons node_11432 (AllWinning.cons node_15278 (AllWinning.cons node_14342 (AllWinning.cons node_13375 (AllWinning.cons node_12441 (AllWinning.cons node_11450 (AllWinning.cons node_10440 (AllWinning.cons node_9427 (AllWinning.cons node_8442 (AllWinning.cons node_7508 (AllWinning.cons node_6584 (AllWinning.cons node_5751 (AllWinning.cons node_5055 (AllWinning.nil))))))))))))))))))))))))

theorem node_16274 : Outcome ⟨7, 6, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 6, 16, 2⟩, ⟨5, 6, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨3, 6, 16, 8⟩, ⟨7, 5, 16, 2⟩, ⟨7, 4, 16, 4⟩, ⟨7, 3, 16, 6⟩, ⟨7, 2, 16, 8⟩, ⟨7, 6, 15, 2⟩, ⟨7, 6, 14, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 6, 12, 8⟩]
  exact AllWinning.cons node_15224 (AllWinning.cons node_14218 (AllWinning.cons node_13209 (AllWinning.cons node_12166 (AllWinning.cons node_15278 (AllWinning.cons node_14339 (AllWinning.cons node_13371 (AllWinning.cons node_12428 (AllWinning.cons node_15280 (AllWinning.cons node_14345 (AllWinning.cons node_13378 (AllWinning.cons node_12443 (AllWinning.nil))))))))))))

theorem node_16275 : Outcome ⟨7, 6, 16, 6⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 12⟩) (by decide) node_9956

theorem node_16276 : Outcome ⟨7, 6, 16, 10⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 16⟩) (by decide) node_8450

theorem node_16277 : Outcome ⟨7, 7, 15, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 8⟩) (by decide) node_12171

theorem node_16278 : Outcome ⟨7, 7, 15, 10⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 8⟩) (by decide) node_12171

theorem node_16279 : Outcome ⟨7, 8, 14, 4⟩ true :=
  Outcome.win (q := ⟨6, 8, 14, 2⟩) (by decide) node_15231

theorem node_16280 : Outcome ⟨7, 8, 14, 12⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 16⟩) (by decide) node_8466

theorem node_16281 : Outcome ⟨7, 8, 14, 16⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 16⟩) (by decide) node_8466

theorem node_16282 : Outcome ⟨7, 9, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.nil))))))

theorem node_16283 : Outcome ⟨7, 9, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.nil))))))))))))

theorem node_16284 : Outcome ⟨7, 9, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.nil))))))))))))))))))

theorem node_16285 : Outcome ⟨7, 9, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨0, 9, 13, 14⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 2, 13, 14⟩, ⟨7, 1, 13, 16⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩, ⟨7, 9, 6, 14⟩, ⟨7, 9, 5, 16⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_8934 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_9414 (AllWinning.cons node_8422 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.cons node_9441 (AllWinning.cons node_8473 (AllWinning.nil)))))))))))))))))))))))

theorem node_16286 : Outcome ⟨7, 9, 13, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨0, 9, 13, 14⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 2, 13, 14⟩, ⟨7, 1, 13, 16⟩, ⟨7, 0, 13, 18⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩, ⟨7, 9, 6, 14⟩, ⟨7, 9, 5, 16⟩, ⟨7, 9, 4, 18⟩, ⟨7, 9, 3, 20⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_8934 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_9414 (AllWinning.cons node_8422 (AllWinning.cons node_7487 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.cons node_9441 (AllWinning.cons node_8473 (AllWinning.cons node_7519 (AllWinning.cons node_6598 (AllWinning.nil))))))))))))))))))))))))))

theorem node_16287 : Outcome ⟨7, 9, 13, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨0, 9, 13, 14⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 2, 13, 14⟩, ⟨7, 1, 13, 16⟩, ⟨7, 0, 13, 18⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩, ⟨7, 9, 6, 14⟩, ⟨7, 9, 5, 16⟩, ⟨7, 9, 4, 18⟩, ⟨7, 9, 3, 20⟩, ⟨7, 9, 2, 22⟩, ⟨7, 9, 1, 24⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_8934 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_9414 (AllWinning.cons node_8422 (AllWinning.cons node_7487 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.cons node_9441 (AllWinning.cons node_8473 (AllWinning.cons node_7519 (AllWinning.cons node_6598 (AllWinning.cons node_5768 (AllWinning.cons node_5072 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_16288 : Outcome ⟨7, 9, 13, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨0, 9, 13, 14⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 2, 13, 14⟩, ⟨7, 1, 13, 16⟩, ⟨7, 0, 13, 18⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩, ⟨7, 9, 6, 14⟩, ⟨7, 9, 5, 16⟩, ⟨7, 9, 4, 18⟩, ⟨7, 9, 3, 20⟩, ⟨7, 9, 2, 22⟩, ⟨7, 9, 1, 24⟩, ⟨7, 9, 0, 26⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_8934 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_9414 (AllWinning.cons node_8422 (AllWinning.cons node_7487 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.cons node_9441 (AllWinning.cons node_8473 (AllWinning.cons node_7519 (AllWinning.cons node_6598 (AllWinning.cons node_5768 (AllWinning.cons node_5072 (AllWinning.cons node_4389 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16289 : Outcome ⟨7, 9, 13, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨0, 9, 13, 14⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 2, 13, 14⟩, ⟨7, 1, 13, 16⟩, ⟨7, 0, 13, 18⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩, ⟨7, 9, 6, 14⟩, ⟨7, 9, 5, 16⟩, ⟨7, 9, 4, 18⟩, ⟨7, 9, 3, 20⟩, ⟨7, 9, 2, 22⟩, ⟨7, 9, 1, 24⟩, ⟨7, 9, 0, 26⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_8934 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_9414 (AllWinning.cons node_8422 (AllWinning.cons node_7487 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.cons node_9441 (AllWinning.cons node_8473 (AllWinning.cons node_7519 (AllWinning.cons node_6598 (AllWinning.cons node_5768 (AllWinning.cons node_5072 (AllWinning.cons node_4389 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16290 : Outcome ⟨7, 9, 13, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨0, 9, 13, 14⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 2, 13, 14⟩, ⟨7, 1, 13, 16⟩, ⟨7, 0, 13, 18⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩, ⟨7, 9, 6, 14⟩, ⟨7, 9, 5, 16⟩, ⟨7, 9, 4, 18⟩, ⟨7, 9, 3, 20⟩, ⟨7, 9, 2, 22⟩, ⟨7, 9, 1, 24⟩, ⟨7, 9, 0, 26⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_8934 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_9414 (AllWinning.cons node_8422 (AllWinning.cons node_7487 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.cons node_9441 (AllWinning.cons node_8473 (AllWinning.cons node_7519 (AllWinning.cons node_6598 (AllWinning.cons node_5768 (AllWinning.cons node_5072 (AllWinning.cons node_4389 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16291 : Outcome ⟨7, 9, 13, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 9, 13, 2⟩, ⟨5, 9, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨3, 9, 13, 8⟩, ⟨2, 9, 13, 10⟩, ⟨1, 9, 13, 12⟩, ⟨0, 9, 13, 14⟩, ⟨7, 8, 13, 2⟩, ⟨7, 7, 13, 4⟩, ⟨7, 6, 13, 6⟩, ⟨7, 5, 13, 8⟩, ⟨7, 4, 13, 10⟩, ⟨7, 3, 13, 12⟩, ⟨7, 2, 13, 14⟩, ⟨7, 1, 13, 16⟩, ⟨7, 0, 13, 18⟩, ⟨7, 9, 12, 2⟩, ⟨7, 9, 11, 4⟩, ⟨7, 9, 10, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 9, 8, 10⟩, ⟨7, 9, 7, 12⟩, ⟨7, 9, 6, 14⟩, ⟨7, 9, 5, 16⟩, ⟨7, 9, 4, 18⟩, ⟨7, 9, 3, 20⟩, ⟨7, 9, 2, 22⟩, ⟨7, 9, 1, 24⟩, ⟨7, 9, 0, 26⟩]
  exact AllWinning.cons node_15234 (AllWinning.cons node_14225 (AllWinning.cons node_13216 (AllWinning.cons node_12180 (AllWinning.cons node_11113 (AllWinning.cons node_9970 (AllWinning.cons node_8934 (AllWinning.cons node_15286 (AllWinning.cons node_14349 (AllWinning.cons node_13378 (AllWinning.cons node_12441 (AllWinning.cons node_11447 (AllWinning.cons node_10431 (AllWinning.cons node_9414 (AllWinning.cons node_8422 (AllWinning.cons node_7487 (AllWinning.cons node_15289 (AllWinning.cons node_14354 (AllWinning.cons node_13393 (AllWinning.cons node_12453 (AllWinning.cons node_11465 (AllWinning.cons node_10458 (AllWinning.cons node_9441 (AllWinning.cons node_8473 (AllWinning.cons node_7519 (AllWinning.cons node_6598 (AllWinning.cons node_5768 (AllWinning.cons node_5072 (AllWinning.cons node_4389 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16292 : Outcome ⟨7, 10, 12, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 6⟩) (by decide) node_13383

theorem node_16293 : Outcome ⟨7, 10, 12, 10⟩ true :=
  Outcome.win (q := ⟨7, 7, 12, 6⟩) (by decide) node_13383

theorem node_16294 : Outcome ⟨7, 11, 11, 4⟩ true :=
  Outcome.win (q := ⟨5, 11, 11, 4⟩) (by decide) node_14234

theorem node_16295 : Outcome ⟨7, 11, 11, 10⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 20⟩) (by decide) node_6565

theorem node_16296 : Outcome ⟨7, 12, 10, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 6⟩) (by decide) node_13403

theorem node_16297 : Outcome ⟨7, 12, 10, 10⟩ true :=
  Outcome.win (q := ⟨7, 12, 7, 6⟩) (by decide) node_13403

theorem node_16298 : Outcome ⟨7, 13, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 9, 2⟩, ⟨5, 13, 9, 4⟩, ⟨7, 12, 9, 2⟩, ⟨7, 11, 9, 4⟩, ⟨7, 13, 8, 2⟩, ⟨7, 13, 7, 4⟩]
  exact AllWinning.cons node_15245 (AllWinning.cons node_14242 (AllWinning.cons node_15298 (AllWinning.cons node_14363 (AllWinning.cons node_15301 (AllWinning.cons node_14370 (AllWinning.nil))))))

theorem node_16299 : Outcome ⟨7, 13, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 9, 2⟩, ⟨5, 13, 9, 4⟩, ⟨4, 13, 9, 6⟩, ⟨3, 13, 9, 8⟩, ⟨7, 12, 9, 2⟩, ⟨7, 11, 9, 4⟩, ⟨7, 10, 9, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 13, 8, 2⟩, ⟨7, 13, 7, 4⟩, ⟨7, 13, 6, 6⟩, ⟨7, 13, 5, 8⟩]
  exact AllWinning.cons node_15245 (AllWinning.cons node_14242 (AllWinning.cons node_13227 (AllWinning.cons node_12191 (AllWinning.cons node_15298 (AllWinning.cons node_14363 (AllWinning.cons node_13395 (AllWinning.cons node_12453 (AllWinning.cons node_15301 (AllWinning.cons node_14370 (AllWinning.cons node_13409 (AllWinning.cons node_12465 (AllWinning.nil))))))))))))

theorem node_16300 : Outcome ⟨7, 13, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 9, 2⟩, ⟨5, 13, 9, 4⟩, ⟨4, 13, 9, 6⟩, ⟨3, 13, 9, 8⟩, ⟨2, 13, 9, 10⟩, ⟨1, 13, 9, 12⟩, ⟨7, 12, 9, 2⟩, ⟨7, 11, 9, 4⟩, ⟨7, 10, 9, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 8, 9, 10⟩, ⟨7, 7, 9, 12⟩, ⟨7, 13, 8, 2⟩, ⟨7, 13, 7, 4⟩, ⟨7, 13, 6, 6⟩, ⟨7, 13, 5, 8⟩, ⟨7, 13, 4, 10⟩, ⟨7, 13, 3, 12⟩]
  exact AllWinning.cons node_15245 (AllWinning.cons node_14242 (AllWinning.cons node_13227 (AllWinning.cons node_12191 (AllWinning.cons node_11126 (AllWinning.cons node_9987 (AllWinning.cons node_15298 (AllWinning.cons node_14363 (AllWinning.cons node_13395 (AllWinning.cons node_12453 (AllWinning.cons node_11461 (AllWinning.cons node_10450 (AllWinning.cons node_15301 (AllWinning.cons node_14370 (AllWinning.cons node_13409 (AllWinning.cons node_12465 (AllWinning.cons node_11480 (AllWinning.cons node_10478 (AllWinning.nil))))))))))))))))))

theorem node_16301 : Outcome ⟨7, 13, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 9, 2⟩, ⟨5, 13, 9, 4⟩, ⟨4, 13, 9, 6⟩, ⟨3, 13, 9, 8⟩, ⟨2, 13, 9, 10⟩, ⟨1, 13, 9, 12⟩, ⟨0, 13, 9, 14⟩, ⟨7, 12, 9, 2⟩, ⟨7, 11, 9, 4⟩, ⟨7, 10, 9, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 8, 9, 10⟩, ⟨7, 7, 9, 12⟩, ⟨7, 6, 9, 14⟩, ⟨7, 5, 9, 16⟩, ⟨7, 13, 8, 2⟩, ⟨7, 13, 7, 4⟩, ⟨7, 13, 6, 6⟩, ⟨7, 13, 5, 8⟩, ⟨7, 13, 4, 10⟩, ⟨7, 13, 3, 12⟩, ⟨7, 13, 2, 14⟩, ⟨7, 13, 1, 16⟩]
  exact AllWinning.cons node_15245 (AllWinning.cons node_14242 (AllWinning.cons node_13227 (AllWinning.cons node_12191 (AllWinning.cons node_11126 (AllWinning.cons node_9987 (AllWinning.cons node_8952 (AllWinning.cons node_15298 (AllWinning.cons node_14363 (AllWinning.cons node_13395 (AllWinning.cons node_12453 (AllWinning.cons node_11461 (AllWinning.cons node_10450 (AllWinning.cons node_9432 (AllWinning.cons node_8442 (AllWinning.cons node_15301 (AllWinning.cons node_14370 (AllWinning.cons node_13409 (AllWinning.cons node_12465 (AllWinning.cons node_11480 (AllWinning.cons node_10478 (AllWinning.cons node_9460 (AllWinning.cons node_8492 (AllWinning.nil)))))))))))))))))))))))

theorem node_16302 : Outcome ⟨7, 13, 9, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 9, 2⟩, ⟨5, 13, 9, 4⟩, ⟨4, 13, 9, 6⟩, ⟨3, 13, 9, 8⟩, ⟨2, 13, 9, 10⟩, ⟨1, 13, 9, 12⟩, ⟨0, 13, 9, 14⟩, ⟨7, 12, 9, 2⟩, ⟨7, 11, 9, 4⟩, ⟨7, 10, 9, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 8, 9, 10⟩, ⟨7, 7, 9, 12⟩, ⟨7, 6, 9, 14⟩, ⟨7, 5, 9, 16⟩, ⟨7, 4, 9, 18⟩, ⟨7, 3, 9, 20⟩, ⟨7, 13, 8, 2⟩, ⟨7, 13, 7, 4⟩, ⟨7, 13, 6, 6⟩, ⟨7, 13, 5, 8⟩, ⟨7, 13, 4, 10⟩, ⟨7, 13, 3, 12⟩, ⟨7, 13, 2, 14⟩, ⟨7, 13, 1, 16⟩, ⟨7, 13, 0, 18⟩]
  exact AllWinning.cons node_15245 (AllWinning.cons node_14242 (AllWinning.cons node_13227 (AllWinning.cons node_12191 (AllWinning.cons node_11126 (AllWinning.cons node_9987 (AllWinning.cons node_8952 (AllWinning.cons node_15298 (AllWinning.cons node_14363 (AllWinning.cons node_13395 (AllWinning.cons node_12453 (AllWinning.cons node_11461 (AllWinning.cons node_10450 (AllWinning.cons node_9432 (AllWinning.cons node_8442 (AllWinning.cons node_7504 (AllWinning.cons node_6577 (AllWinning.cons node_15301 (AllWinning.cons node_14370 (AllWinning.cons node_13409 (AllWinning.cons node_12465 (AllWinning.cons node_11480 (AllWinning.cons node_10478 (AllWinning.cons node_9460 (AllWinning.cons node_8492 (AllWinning.cons node_7538 (AllWinning.nil))))))))))))))))))))))))))

theorem node_16303 : Outcome ⟨7, 13, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 9, 2⟩, ⟨5, 13, 9, 4⟩, ⟨4, 13, 9, 6⟩, ⟨3, 13, 9, 8⟩, ⟨2, 13, 9, 10⟩, ⟨1, 13, 9, 12⟩, ⟨0, 13, 9, 14⟩, ⟨7, 12, 9, 2⟩, ⟨7, 11, 9, 4⟩, ⟨7, 10, 9, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 8, 9, 10⟩, ⟨7, 7, 9, 12⟩, ⟨7, 6, 9, 14⟩, ⟨7, 5, 9, 16⟩, ⟨7, 4, 9, 18⟩, ⟨7, 3, 9, 20⟩, ⟨7, 2, 9, 22⟩, ⟨7, 1, 9, 24⟩, ⟨7, 13, 8, 2⟩, ⟨7, 13, 7, 4⟩, ⟨7, 13, 6, 6⟩, ⟨7, 13, 5, 8⟩, ⟨7, 13, 4, 10⟩, ⟨7, 13, 3, 12⟩, ⟨7, 13, 2, 14⟩, ⟨7, 13, 1, 16⟩, ⟨7, 13, 0, 18⟩]
  exact AllWinning.cons node_15245 (AllWinning.cons node_14242 (AllWinning.cons node_13227 (AllWinning.cons node_12191 (AllWinning.cons node_11126 (AllWinning.cons node_9987 (AllWinning.cons node_8952 (AllWinning.cons node_15298 (AllWinning.cons node_14363 (AllWinning.cons node_13395 (AllWinning.cons node_12453 (AllWinning.cons node_11461 (AllWinning.cons node_10450 (AllWinning.cons node_9432 (AllWinning.cons node_8442 (AllWinning.cons node_7504 (AllWinning.cons node_6577 (AllWinning.cons node_5739 (AllWinning.cons node_5038 (AllWinning.cons node_15301 (AllWinning.cons node_14370 (AllWinning.cons node_13409 (AllWinning.cons node_12465 (AllWinning.cons node_11480 (AllWinning.cons node_10478 (AllWinning.cons node_9460 (AllWinning.cons node_8492 (AllWinning.cons node_7538 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_16304 : Outcome ⟨7, 13, 9, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 9, 2⟩, ⟨5, 13, 9, 4⟩, ⟨4, 13, 9, 6⟩, ⟨3, 13, 9, 8⟩, ⟨2, 13, 9, 10⟩, ⟨1, 13, 9, 12⟩, ⟨0, 13, 9, 14⟩, ⟨7, 12, 9, 2⟩, ⟨7, 11, 9, 4⟩, ⟨7, 10, 9, 6⟩, ⟨7, 9, 9, 8⟩, ⟨7, 8, 9, 10⟩, ⟨7, 7, 9, 12⟩, ⟨7, 6, 9, 14⟩, ⟨7, 5, 9, 16⟩, ⟨7, 4, 9, 18⟩, ⟨7, 3, 9, 20⟩, ⟨7, 2, 9, 22⟩, ⟨7, 1, 9, 24⟩, ⟨7, 0, 9, 26⟩, ⟨7, 13, 8, 2⟩, ⟨7, 13, 7, 4⟩, ⟨7, 13, 6, 6⟩, ⟨7, 13, 5, 8⟩, ⟨7, 13, 4, 10⟩, ⟨7, 13, 3, 12⟩, ⟨7, 13, 2, 14⟩, ⟨7, 13, 1, 16⟩, ⟨7, 13, 0, 18⟩]
  exact AllWinning.cons node_15245 (AllWinning.cons node_14242 (AllWinning.cons node_13227 (AllWinning.cons node_12191 (AllWinning.cons node_11126 (AllWinning.cons node_9987 (AllWinning.cons node_8952 (AllWinning.cons node_15298 (AllWinning.cons node_14363 (AllWinning.cons node_13395 (AllWinning.cons node_12453 (AllWinning.cons node_11461 (AllWinning.cons node_10450 (AllWinning.cons node_9432 (AllWinning.cons node_8442 (AllWinning.cons node_7504 (AllWinning.cons node_6577 (AllWinning.cons node_5739 (AllWinning.cons node_5038 (AllWinning.cons node_4328 (AllWinning.cons node_15301 (AllWinning.cons node_14370 (AllWinning.cons node_13409 (AllWinning.cons node_12465 (AllWinning.cons node_11480 (AllWinning.cons node_10478 (AllWinning.cons node_9460 (AllWinning.cons node_8492 (AllWinning.cons node_7538 (AllWinning.nil)))))))))))))))))))))))))))))

end RQ9F1
