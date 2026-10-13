import Chunk87
set_option autoImplicit false
namespace RQ9F1

theorem node_19192 : Outcome ⟨9, 17, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 17, 6, 2⟩, ⟨7, 17, 6, 4⟩, ⟨6, 17, 6, 6⟩, ⟨5, 17, 6, 8⟩, ⟨4, 17, 6, 10⟩, ⟨3, 17, 6, 12⟩, ⟨2, 17, 6, 14⟩, ⟨1, 17, 6, 16⟩, ⟨0, 17, 6, 18⟩, ⟨9, 16, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨9, 14, 6, 6⟩, ⟨9, 13, 6, 8⟩, ⟨9, 12, 6, 10⟩, ⟨9, 11, 6, 12⟩, ⟨9, 10, 6, 14⟩, ⟨9, 9, 6, 16⟩, ⟨9, 8, 6, 18⟩, ⟨9, 7, 6, 20⟩, ⟨9, 6, 6, 22⟩, ⟨9, 5, 6, 24⟩, ⟨9, 17, 5, 2⟩, ⟨9, 17, 4, 4⟩, ⟨9, 17, 3, 6⟩, ⟨9, 17, 2, 8⟩, ⟨9, 17, 1, 10⟩, ⟨9, 17, 0, 12⟩]
  exact AllWinning.cons node_18234 (AllWinning.cons node_17291 (AllWinning.cons node_16252 (AllWinning.cons node_15206 (AllWinning.cons node_14197 (AllWinning.cons node_13189 (AllWinning.cons node_12137 (AllWinning.cons node_11081 (AllWinning.cons node_9920 (AllWinning.cons node_18287 (AllWinning.cons node_17389 (AllWinning.cons node_16461 (AllWinning.cons node_15428 (AllWinning.cons node_14493 (AllWinning.cons node_13524 (AllWinning.cons node_12574 (AllWinning.cons node_11586 (AllWinning.cons node_10581 (AllWinning.cons node_9542 (AllWinning.cons node_8605 (AllWinning.cons node_7606 (AllWinning.cons node_18290 (AllWinning.cons node_17393 (AllWinning.cons node_16475 (AllWinning.cons node_15443 (AllWinning.cons node_14510 (AllWinning.cons node_13544 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_19193 : Outcome ⟨9, 17, 6, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 17, 6, 2⟩, ⟨7, 17, 6, 4⟩, ⟨6, 17, 6, 6⟩, ⟨5, 17, 6, 8⟩, ⟨4, 17, 6, 10⟩, ⟨3, 17, 6, 12⟩, ⟨2, 17, 6, 14⟩, ⟨1, 17, 6, 16⟩, ⟨0, 17, 6, 18⟩, ⟨9, 16, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨9, 14, 6, 6⟩, ⟨9, 13, 6, 8⟩, ⟨9, 12, 6, 10⟩, ⟨9, 11, 6, 12⟩, ⟨9, 10, 6, 14⟩, ⟨9, 9, 6, 16⟩, ⟨9, 8, 6, 18⟩, ⟨9, 7, 6, 20⟩, ⟨9, 6, 6, 22⟩, ⟨9, 5, 6, 24⟩, ⟨9, 4, 6, 26⟩, ⟨9, 3, 6, 28⟩, ⟨9, 2, 6, 30⟩, ⟨9, 1, 6, 32⟩, ⟨9, 0, 6, 34⟩, ⟨9, 17, 5, 2⟩, ⟨9, 17, 4, 4⟩, ⟨9, 17, 3, 6⟩, ⟨9, 17, 2, 8⟩, ⟨9, 17, 1, 10⟩, ⟨9, 17, 0, 12⟩]
  exact AllWinning.cons node_18234 (AllWinning.cons node_17291 (AllWinning.cons node_16252 (AllWinning.cons node_15206 (AllWinning.cons node_14197 (AllWinning.cons node_13189 (AllWinning.cons node_12137 (AllWinning.cons node_11081 (AllWinning.cons node_9920 (AllWinning.cons node_18287 (AllWinning.cons node_17389 (AllWinning.cons node_16461 (AllWinning.cons node_15428 (AllWinning.cons node_14493 (AllWinning.cons node_13524 (AllWinning.cons node_12574 (AllWinning.cons node_11586 (AllWinning.cons node_10581 (AllWinning.cons node_9542 (AllWinning.cons node_8605 (AllWinning.cons node_7606 (AllWinning.cons node_6680 (AllWinning.cons node_5847 (AllWinning.cons node_5124 (AllWinning.cons node_4450 (AllWinning.cons node_3794 (AllWinning.cons node_18290 (AllWinning.cons node_17393 (AllWinning.cons node_16475 (AllWinning.cons node_15443 (AllWinning.cons node_14510 (AllWinning.cons node_13544 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19194 : Outcome ⟨9, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 8⟩) (by decide) node_15432

theorem node_19195 : Outcome ⟨9, 18, 5, 6⟩ true :=
  Outcome.win (q := ⟨9, 14, 5, 8⟩) (by decide) node_15432

theorem node_19196 : Outcome ⟨9, 19, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 19, 4, 2⟩, ⟨7, 19, 4, 4⟩, ⟨9, 18, 4, 2⟩, ⟨9, 17, 4, 4⟩, ⟨9, 19, 3, 2⟩, ⟨9, 19, 2, 4⟩]
  exact AllWinning.cons node_18239 (AllWinning.cons node_17297 (AllWinning.cons node_18293 (AllWinning.cons node_17393 (AllWinning.cons node_18295 (AllWinning.cons node_17398 (AllWinning.nil))))))

theorem node_19197 : Outcome ⟨9, 19, 4, 10⟩ true :=
  Outcome.win (q := ⟨9, 16, 4, 6⟩) (by decide) node_16467

theorem node_19198 : Outcome ⟨9, 20, 3, 4⟩ true :=
  Outcome.win (q := ⟨8, 20, 3, 2⟩) (by decide) node_18241

theorem node_19199 : Outcome ⟨9, 20, 3, 6⟩ true :=
  Outcome.win (q := ⟨8, 20, 3, 2⟩) (by decide) node_18241

theorem node_19200 : Outcome ⟨9, 20, 3, 12⟩ true :=
  Outcome.win (q := ⟨9, 12, 3, 16⟩) (by decide) node_11601

theorem node_19201 : Outcome ⟨10, 2, 20, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 8⟩) (by decide) node_15457

theorem node_19202 : Outcome ⟨10, 2, 20, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 8⟩) (by decide) node_15457

theorem node_19203 : Outcome ⟨10, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨10, 3, 18, 2⟩) (by decide) node_18304

theorem node_19204 : Outcome ⟨10, 3, 19, 4⟩ true :=
  Outcome.win (q := ⟨10, 3, 18, 2⟩) (by decide) node_18304

theorem node_19205 : Outcome ⟨10, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨10, 3, 18, 2⟩) (by decide) node_18304

theorem node_19206 : Outcome ⟨10, 4, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 3, 18, 2⟩) (by decide) node_18304

theorem node_19207 : Outcome ⟨10, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 16, 2⟩) (by decide) node_18311

theorem node_19208 : Outcome ⟨10, 5, 17, 4⟩ true :=
  Outcome.win (q := ⟨7, 5, 17, 6⟩) (by decide) node_16270

theorem node_19209 : Outcome ⟨10, 5, 17, 10⟩ true :=
  Outcome.win (q := ⟨7, 5, 17, 6⟩) (by decide) node_16270

theorem node_19210 : Outcome ⟨10, 6, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 8⟩) (by decide) node_15457

theorem node_19211 : Outcome ⟨10, 6, 16, 6⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 8⟩) (by decide) node_15457

theorem node_19212 : Outcome ⟨10, 6, 16, 16⟩ true :=
  Outcome.win (q := ⟨10, 6, 4, 24⟩) (by decide) node_7676

theorem node_19213 : Outcome ⟨10, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨10, 7, 14, 2⟩) (by decide) node_18318

theorem node_19214 : Outcome ⟨10, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨10, 7, 14, 2⟩) (by decide) node_18318

theorem node_19215 : Outcome ⟨10, 7, 15, 16⟩ true :=
  Outcome.win (q := ⟨10, 7, 14, 2⟩) (by decide) node_18318

theorem node_19216 : Outcome ⟨10, 8, 14, 2⟩ true :=
  Outcome.win (q := ⟨9, 8, 14, 2⟩) (by decide) node_18259

theorem node_19217 : Outcome ⟨10, 8, 14, 4⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 6⟩) (by decide) node_16507

theorem node_19218 : Outcome ⟨10, 8, 14, 10⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 14⟩) (by decide) node_12602

theorem node_19219 : Outcome ⟨10, 8, 14, 16⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 14⟩) (by decide) node_12602

theorem node_19220 : Outcome ⟨10, 9, 13, 2⟩ true :=
  Outcome.win (q := ⟨10, 9, 12, 2⟩) (by decide) node_18325

theorem node_19221 : Outcome ⟨10, 9, 13, 4⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 6⟩) (by decide) node_16284

theorem node_19222 : Outcome ⟨10, 9, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 12⟩) (by decide) node_13558

theorem node_19223 : Outcome ⟨10, 9, 13, 10⟩ true :=
  Outcome.win (q := ⟨10, 3, 13, 12⟩) (by decide) node_13558

theorem node_19224 : Outcome ⟨10, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨9, 10, 12, 2⟩) (by decide) node_18266

theorem node_19225 : Outcome ⟨10, 10, 12, 10⟩ true :=
  Outcome.win (q := ⟨9, 10, 12, 2⟩) (by decide) node_18266

theorem node_19226 : Outcome ⟨10, 11, 11, 2⟩ true :=
  Outcome.win (q := ⟨9, 11, 11, 2⟩) (by decide) node_18270

theorem node_19227 : Outcome ⟨10, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨9, 12, 10, 2⟩) (by decide) node_18273

theorem node_19228 : Outcome ⟨10, 12, 10, 10⟩ true :=
  Outcome.win (q := ⟨9, 12, 10, 2⟩) (by decide) node_18273

theorem node_19229 : Outcome ⟨10, 13, 9, 2⟩ true :=
  Outcome.win (q := ⟨10, 12, 9, 2⟩) (by decide) node_18333

theorem node_19230 : Outcome ⟨10, 13, 9, 4⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 6⟩) (by decide) node_16300

theorem node_19231 : Outcome ⟨10, 13, 9, 6⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 12⟩) (by decide) node_13591

theorem node_19232 : Outcome ⟨10, 13, 9, 10⟩ true :=
  Outcome.win (q := ⟨10, 13, 3, 12⟩) (by decide) node_13591

theorem node_19233 : Outcome ⟨10, 14, 8, 2⟩ true :=
  Outcome.win (q := ⟨9, 14, 8, 2⟩) (by decide) node_18281

theorem node_19234 : Outcome ⟨10, 14, 8, 4⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 6⟩) (by decide) node_16519

theorem node_19235 : Outcome ⟨10, 14, 8, 10⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 14⟩) (by decide) node_12645

theorem node_19236 : Outcome ⟨10, 14, 8, 16⟩ true :=
  Outcome.win (q := ⟨10, 14, 1, 14⟩) (by decide) node_12645

theorem node_19237 : Outcome ⟨10, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 7, 2⟩) (by decide) node_18340

theorem node_19238 : Outcome ⟨10, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨10, 14, 7, 2⟩) (by decide) node_18340

theorem node_19239 : Outcome ⟨10, 15, 7, 16⟩ true :=
  Outcome.win (q := ⟨10, 14, 7, 2⟩) (by decide) node_18340

theorem node_19240 : Outcome ⟨10, 16, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 8⟩) (by decide) node_15500

theorem node_19241 : Outcome ⟨10, 16, 6, 6⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 8⟩) (by decide) node_15500

theorem node_19242 : Outcome ⟨10, 16, 6, 16⟩ true :=
  Outcome.win (q := ⟨10, 4, 6, 24⟩) (by decide) node_7662

theorem node_19243 : Outcome ⟨10, 17, 5, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 5, 2⟩) (by decide) node_18347

theorem node_19244 : Outcome ⟨10, 17, 5, 4⟩ true :=
  Outcome.win (q := ⟨7, 17, 5, 6⟩) (by decide) node_16317

theorem node_19245 : Outcome ⟨10, 17, 5, 10⟩ true :=
  Outcome.win (q := ⟨7, 17, 5, 6⟩) (by decide) node_16317

theorem node_19246 : Outcome ⟨10, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 3, 2⟩) (by decide) node_18354

theorem node_19247 : Outcome ⟨10, 18, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 3, 2⟩) (by decide) node_18354

theorem node_19248 : Outcome ⟨10, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 3, 2⟩) (by decide) node_18354

theorem node_19249 : Outcome ⟨10, 19, 3, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 3, 2⟩) (by decide) node_18354

theorem node_19250 : Outcome ⟨10, 20, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 8⟩) (by decide) node_15500

theorem node_19251 : Outcome ⟨10, 20, 2, 8⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 8⟩) (by decide) node_15500

theorem node_19252 : Outcome ⟨11, 1, 20, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 20, 2⟩) (by decide) node_18300

theorem node_19253 : Outcome ⟨11, 2, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 19, 4⟩) (by decide) node_17466

theorem node_19254 : Outcome ⟨11, 2, 19, 4⟩ true :=
  Outcome.win (q := ⟨8, 2, 19, 6⟩) (by decide) node_16332

theorem node_19255 : Outcome ⟨11, 2, 19, 12⟩ true :=
  Outcome.win (q := ⟨8, 2, 19, 6⟩) (by decide) node_16332

theorem node_19256 : Outcome ⟨11, 3, 18, 2⟩ true :=
  Outcome.win (q := ⟨10, 3, 18, 2⟩) (by decide) node_18304

theorem node_19257 : Outcome ⟨11, 3, 18, 8⟩ true :=
  Outcome.win (q := ⟨10, 3, 18, 2⟩) (by decide) node_18304

theorem node_19258 : Outcome ⟨11, 4, 17, 2⟩ true :=
  Outcome.win (q := ⟨11, 2, 17, 4⟩) (by decide) node_17470

theorem node_19259 : Outcome ⟨11, 4, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 6⟩) (by decide) node_16342

theorem node_19260 : Outcome ⟨11, 4, 17, 8⟩ true :=
  Outcome.win (q := ⟨8, 4, 17, 6⟩) (by decide) node_16342

theorem node_19261 : Outcome ⟨11, 5, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 16, 2⟩) (by decide) node_18311

theorem node_19262 : Outcome ⟨11, 5, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 5, 16, 2⟩) (by decide) node_18311

theorem node_19263 : Outcome ⟨11, 6, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 15, 2⟩, ⟨9, 6, 15, 4⟩, ⟨11, 5, 15, 2⟩, ⟨11, 4, 15, 4⟩, ⟨11, 6, 14, 2⟩, ⟨11, 6, 13, 4⟩]
  exact AllWinning.cons node_18315 (AllWinning.cons node_17366 (AllWinning.cons node_18373 (AllWinning.cons node_17478 (AllWinning.cons node_18376 (AllWinning.cons node_17482 (AllWinning.nil))))))

theorem node_19264 : Outcome ⟨11, 6, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 15, 2⟩, ⟨9, 6, 15, 4⟩, ⟨8, 6, 15, 6⟩, ⟨7, 6, 15, 8⟩, ⟨11, 5, 15, 2⟩, ⟨11, 4, 15, 4⟩, ⟨11, 3, 15, 6⟩, ⟨11, 2, 15, 8⟩, ⟨11, 6, 14, 2⟩, ⟨11, 6, 13, 4⟩, ⟨11, 6, 12, 6⟩, ⟨11, 6, 11, 8⟩]
  exact AllWinning.cons node_18315 (AllWinning.cons node_17366 (AllWinning.cons node_16351 (AllWinning.cons node_15282 (AllWinning.cons node_18373 (AllWinning.cons node_17478 (AllWinning.cons node_16551 (AllWinning.cons node_15515 (AllWinning.cons node_18376 (AllWinning.cons node_17482 (AllWinning.cons node_16560 (AllWinning.cons node_15527 (AllWinning.nil))))))))))))

theorem node_19265 : Outcome ⟨11, 6, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 15, 2⟩, ⟨9, 6, 15, 4⟩, ⟨8, 6, 15, 6⟩, ⟨7, 6, 15, 8⟩, ⟨6, 6, 15, 10⟩, ⟨5, 6, 15, 12⟩, ⟨11, 5, 15, 2⟩, ⟨11, 4, 15, 4⟩, ⟨11, 3, 15, 6⟩, ⟨11, 2, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨11, 0, 15, 12⟩, ⟨11, 6, 14, 2⟩, ⟨11, 6, 13, 4⟩, ⟨11, 6, 12, 6⟩, ⟨11, 6, 11, 8⟩, ⟨11, 6, 10, 10⟩, ⟨11, 6, 9, 12⟩]
  exact AllWinning.cons node_18315 (AllWinning.cons node_17366 (AllWinning.cons node_16351 (AllWinning.cons node_15282 (AllWinning.cons node_14277 (AllWinning.cons node_13259 (AllWinning.cons node_18373 (AllWinning.cons node_17478 (AllWinning.cons node_16551 (AllWinning.cons node_15515 (AllWinning.cons node_14581 (AllWinning.cons node_13602 (AllWinning.cons node_18376 (AllWinning.cons node_17482 (AllWinning.cons node_16560 (AllWinning.cons node_15527 (AllWinning.cons node_14592 (AllWinning.cons node_13622 (AllWinning.nil))))))))))))))))))

theorem node_19266 : Outcome ⟨11, 6, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 15, 2⟩, ⟨9, 6, 15, 4⟩, ⟨8, 6, 15, 6⟩, ⟨7, 6, 15, 8⟩, ⟨6, 6, 15, 10⟩, ⟨5, 6, 15, 12⟩, ⟨4, 6, 15, 14⟩, ⟨3, 6, 15, 16⟩, ⟨11, 5, 15, 2⟩, ⟨11, 4, 15, 4⟩, ⟨11, 3, 15, 6⟩, ⟨11, 2, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨11, 0, 15, 12⟩, ⟨11, 6, 14, 2⟩, ⟨11, 6, 13, 4⟩, ⟨11, 6, 12, 6⟩, ⟨11, 6, 11, 8⟩, ⟨11, 6, 10, 10⟩, ⟨11, 6, 9, 12⟩, ⟨11, 6, 8, 14⟩, ⟨11, 6, 7, 16⟩]
  exact AllWinning.cons node_18315 (AllWinning.cons node_17366 (AllWinning.cons node_16351 (AllWinning.cons node_15282 (AllWinning.cons node_14277 (AllWinning.cons node_13259 (AllWinning.cons node_12238 (AllWinning.cons node_11165 (AllWinning.cons node_18373 (AllWinning.cons node_17478 (AllWinning.cons node_16551 (AllWinning.cons node_15515 (AllWinning.cons node_14581 (AllWinning.cons node_13602 (AllWinning.cons node_18376 (AllWinning.cons node_17482 (AllWinning.cons node_16560 (AllWinning.cons node_15527 (AllWinning.cons node_14592 (AllWinning.cons node_13622 (AllWinning.cons node_12675 (AllWinning.cons node_11682 (AllWinning.nil))))))))))))))))))))))

theorem node_19267 : Outcome ⟨11, 6, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 15, 2⟩, ⟨9, 6, 15, 4⟩, ⟨8, 6, 15, 6⟩, ⟨7, 6, 15, 8⟩, ⟨6, 6, 15, 10⟩, ⟨5, 6, 15, 12⟩, ⟨4, 6, 15, 14⟩, ⟨3, 6, 15, 16⟩, ⟨2, 6, 15, 18⟩, ⟨1, 6, 15, 20⟩, ⟨11, 5, 15, 2⟩, ⟨11, 4, 15, 4⟩, ⟨11, 3, 15, 6⟩, ⟨11, 2, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨11, 0, 15, 12⟩, ⟨11, 6, 14, 2⟩, ⟨11, 6, 13, 4⟩, ⟨11, 6, 12, 6⟩, ⟨11, 6, 11, 8⟩, ⟨11, 6, 10, 10⟩, ⟨11, 6, 9, 12⟩, ⟨11, 6, 8, 14⟩, ⟨11, 6, 7, 16⟩, ⟨11, 6, 6, 18⟩, ⟨11, 6, 5, 20⟩]
  exact AllWinning.cons node_18315 (AllWinning.cons node_17366 (AllWinning.cons node_16351 (AllWinning.cons node_15282 (AllWinning.cons node_14277 (AllWinning.cons node_13259 (AllWinning.cons node_12238 (AllWinning.cons node_11165 (AllWinning.cons node_10040 (AllWinning.cons node_9001 (AllWinning.cons node_18373 (AllWinning.cons node_17478 (AllWinning.cons node_16551 (AllWinning.cons node_15515 (AllWinning.cons node_14581 (AllWinning.cons node_13602 (AllWinning.cons node_18376 (AllWinning.cons node_17482 (AllWinning.cons node_16560 (AllWinning.cons node_15527 (AllWinning.cons node_14592 (AllWinning.cons node_13622 (AllWinning.cons node_12675 (AllWinning.cons node_11682 (AllWinning.cons node_10685 (AllWinning.cons node_9642 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19268 : Outcome ⟨11, 6, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 15, 2⟩, ⟨9, 6, 15, 4⟩, ⟨8, 6, 15, 6⟩, ⟨7, 6, 15, 8⟩, ⟨6, 6, 15, 10⟩, ⟨5, 6, 15, 12⟩, ⟨4, 6, 15, 14⟩, ⟨3, 6, 15, 16⟩, ⟨2, 6, 15, 18⟩, ⟨1, 6, 15, 20⟩, ⟨0, 6, 15, 22⟩, ⟨11, 5, 15, 2⟩, ⟨11, 4, 15, 4⟩, ⟨11, 3, 15, 6⟩, ⟨11, 2, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨11, 0, 15, 12⟩, ⟨11, 6, 14, 2⟩, ⟨11, 6, 13, 4⟩, ⟨11, 6, 12, 6⟩, ⟨11, 6, 11, 8⟩, ⟨11, 6, 10, 10⟩, ⟨11, 6, 9, 12⟩, ⟨11, 6, 8, 14⟩, ⟨11, 6, 7, 16⟩, ⟨11, 6, 6, 18⟩, ⟨11, 6, 5, 20⟩, ⟨11, 6, 4, 22⟩, ⟨11, 6, 3, 24⟩]
  exact AllWinning.cons node_18315 (AllWinning.cons node_17366 (AllWinning.cons node_16351 (AllWinning.cons node_15282 (AllWinning.cons node_14277 (AllWinning.cons node_13259 (AllWinning.cons node_12238 (AllWinning.cons node_11165 (AllWinning.cons node_10040 (AllWinning.cons node_9001 (AllWinning.cons node_7928 (AllWinning.cons node_18373 (AllWinning.cons node_17478 (AllWinning.cons node_16551 (AllWinning.cons node_15515 (AllWinning.cons node_14581 (AllWinning.cons node_13602 (AllWinning.cons node_18376 (AllWinning.cons node_17482 (AllWinning.cons node_16560 (AllWinning.cons node_15527 (AllWinning.cons node_14592 (AllWinning.cons node_13622 (AllWinning.cons node_12675 (AllWinning.cons node_11682 (AllWinning.cons node_10685 (AllWinning.cons node_9642 (AllWinning.cons node_8693 (AllWinning.cons node_7721 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19269 : Outcome ⟨11, 7, 14, 4⟩ true :=
  Outcome.win (q := ⟨10, 7, 14, 2⟩) (by decide) node_18318

theorem node_19270 : Outcome ⟨11, 8, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 13, 2⟩, ⟨9, 8, 13, 4⟩, ⟨11, 7, 13, 2⟩, ⟨11, 6, 13, 4⟩, ⟨11, 8, 12, 2⟩, ⟨11, 8, 11, 4⟩]
  exact AllWinning.cons node_18322 (AllWinning.cons node_17371 (AllWinning.cons node_18378 (AllWinning.cons node_17482 (AllWinning.cons node_18381 (AllWinning.cons node_17488 (AllWinning.nil))))))

theorem node_19271 : Outcome ⟨11, 8, 13, 4⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 6⟩) (by decide) node_16567

theorem node_19272 : Outcome ⟨11, 8, 13, 8⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 6⟩) (by decide) node_16567

theorem node_19273 : Outcome ⟨11, 8, 13, 16⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 6⟩) (by decide) node_16567

theorem node_19274 : Outcome ⟨11, 9, 12, 2⟩ true :=
  Outcome.win (q := ⟨10, 9, 12, 2⟩) (by decide) node_18325

theorem node_19275 : Outcome ⟨11, 9, 12, 4⟩ true :=
  Outcome.win (q := ⟨10, 9, 12, 2⟩) (by decide) node_18325

theorem node_19276 : Outcome ⟨11, 9, 12, 6⟩ true :=
  Outcome.win (q := ⟨10, 9, 12, 2⟩) (by decide) node_18325

theorem node_19277 : Outcome ⟨11, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 11, 2⟩) (by decide) node_18385

theorem node_19278 : Outcome ⟨11, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨11, 11, 9, 2⟩) (by decide) node_18390

theorem node_19279 : Outcome ⟨11, 12, 9, 2⟩ true :=
  Outcome.win (q := ⟨10, 12, 9, 2⟩) (by decide) node_18333

theorem node_19280 : Outcome ⟨11, 12, 9, 4⟩ true :=
  Outcome.win (q := ⟨10, 12, 9, 2⟩) (by decide) node_18333

theorem node_19281 : Outcome ⟨11, 12, 9, 6⟩ true :=
  Outcome.win (q := ⟨10, 12, 9, 2⟩) (by decide) node_18333

theorem node_19282 : Outcome ⟨11, 13, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 13, 8, 2⟩, ⟨9, 13, 8, 4⟩, ⟨11, 12, 8, 2⟩, ⟨11, 11, 8, 4⟩, ⟨11, 13, 7, 2⟩, ⟨11, 13, 6, 4⟩]
  exact AllWinning.cons node_18337 (AllWinning.cons node_17384 (AllWinning.cons node_18393 (AllWinning.cons node_17493 (AllWinning.cons node_18397 (AllWinning.cons node_17497 (AllWinning.nil))))))

theorem node_19283 : Outcome ⟨11, 13, 8, 4⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 6⟩) (by decide) node_16575

theorem node_19284 : Outcome ⟨11, 13, 8, 8⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 6⟩) (by decide) node_16575

theorem node_19285 : Outcome ⟨11, 13, 8, 16⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 6⟩) (by decide) node_16575

theorem node_19286 : Outcome ⟨11, 14, 7, 4⟩ true :=
  Outcome.win (q := ⟨10, 14, 7, 2⟩) (by decide) node_18340

theorem node_19287 : Outcome ⟨11, 15, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨11, 14, 6, 2⟩, ⟨11, 13, 6, 4⟩, ⟨11, 15, 5, 2⟩, ⟨11, 15, 4, 4⟩]
  exact AllWinning.cons node_18344 (AllWinning.cons node_17389 (AllWinning.cons node_18400 (AllWinning.cons node_17497 (AllWinning.cons node_18402 (AllWinning.cons node_17502 (AllWinning.nil))))))

theorem node_19288 : Outcome ⟨11, 15, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨8, 15, 6, 6⟩, ⟨7, 15, 6, 8⟩, ⟨11, 14, 6, 2⟩, ⟨11, 13, 6, 4⟩, ⟨11, 12, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨11, 15, 5, 2⟩, ⟨11, 15, 4, 4⟩, ⟨11, 15, 3, 6⟩, ⟨11, 15, 2, 8⟩]
  exact AllWinning.cons node_18344 (AllWinning.cons node_17389 (AllWinning.cons node_16379 (AllWinning.cons node_15308 (AllWinning.cons node_18400 (AllWinning.cons node_17497 (AllWinning.cons node_16583 (AllWinning.cons node_15540 (AllWinning.cons node_18402 (AllWinning.cons node_17502 (AllWinning.cons node_16591 (AllWinning.cons node_15551 (AllWinning.nil))))))))))))

theorem node_19289 : Outcome ⟨11, 15, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨8, 15, 6, 6⟩, ⟨7, 15, 6, 8⟩, ⟨6, 15, 6, 10⟩, ⟨5, 15, 6, 12⟩, ⟨11, 14, 6, 2⟩, ⟨11, 13, 6, 4⟩, ⟨11, 12, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨11, 10, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨11, 15, 5, 2⟩, ⟨11, 15, 4, 4⟩, ⟨11, 15, 3, 6⟩, ⟨11, 15, 2, 8⟩, ⟨11, 15, 1, 10⟩, ⟨11, 15, 0, 12⟩]
  exact AllWinning.cons node_18344 (AllWinning.cons node_17389 (AllWinning.cons node_16379 (AllWinning.cons node_15308 (AllWinning.cons node_14307 (AllWinning.cons node_13282 (AllWinning.cons node_18400 (AllWinning.cons node_17497 (AllWinning.cons node_16583 (AllWinning.cons node_15540 (AllWinning.cons node_14604 (AllWinning.cons node_13633 (AllWinning.cons node_18402 (AllWinning.cons node_17502 (AllWinning.cons node_16591 (AllWinning.cons node_15551 (AllWinning.cons node_14618 (AllWinning.cons node_13653 (AllWinning.nil))))))))))))))))))

theorem node_19290 : Outcome ⟨11, 15, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨8, 15, 6, 6⟩, ⟨7, 15, 6, 8⟩, ⟨6, 15, 6, 10⟩, ⟨5, 15, 6, 12⟩, ⟨4, 15, 6, 14⟩, ⟨3, 15, 6, 16⟩, ⟨11, 14, 6, 2⟩, ⟨11, 13, 6, 4⟩, ⟨11, 12, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨11, 10, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨11, 8, 6, 14⟩, ⟨11, 7, 6, 16⟩, ⟨11, 15, 5, 2⟩, ⟨11, 15, 4, 4⟩, ⟨11, 15, 3, 6⟩, ⟨11, 15, 2, 8⟩, ⟨11, 15, 1, 10⟩, ⟨11, 15, 0, 12⟩]
  exact AllWinning.cons node_18344 (AllWinning.cons node_17389 (AllWinning.cons node_16379 (AllWinning.cons node_15308 (AllWinning.cons node_14307 (AllWinning.cons node_13282 (AllWinning.cons node_12263 (AllWinning.cons node_11210 (AllWinning.cons node_18400 (AllWinning.cons node_17497 (AllWinning.cons node_16583 (AllWinning.cons node_15540 (AllWinning.cons node_14604 (AllWinning.cons node_13633 (AllWinning.cons node_12681 (AllWinning.cons node_11686 (AllWinning.cons node_18402 (AllWinning.cons node_17502 (AllWinning.cons node_16591 (AllWinning.cons node_15551 (AllWinning.cons node_14618 (AllWinning.cons node_13653 (AllWinning.nil))))))))))))))))))))))

theorem node_19291 : Outcome ⟨11, 15, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨8, 15, 6, 6⟩, ⟨7, 15, 6, 8⟩, ⟨6, 15, 6, 10⟩, ⟨5, 15, 6, 12⟩, ⟨4, 15, 6, 14⟩, ⟨3, 15, 6, 16⟩, ⟨2, 15, 6, 18⟩, ⟨1, 15, 6, 20⟩, ⟨11, 14, 6, 2⟩, ⟨11, 13, 6, 4⟩, ⟨11, 12, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨11, 10, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨11, 8, 6, 14⟩, ⟨11, 7, 6, 16⟩, ⟨11, 6, 6, 18⟩, ⟨11, 5, 6, 20⟩, ⟨11, 15, 5, 2⟩, ⟨11, 15, 4, 4⟩, ⟨11, 15, 3, 6⟩, ⟨11, 15, 2, 8⟩, ⟨11, 15, 1, 10⟩, ⟨11, 15, 0, 12⟩]
  exact AllWinning.cons node_18344 (AllWinning.cons node_17389 (AllWinning.cons node_16379 (AllWinning.cons node_15308 (AllWinning.cons node_14307 (AllWinning.cons node_13282 (AllWinning.cons node_12263 (AllWinning.cons node_11210 (AllWinning.cons node_10071 (AllWinning.cons node_9028 (AllWinning.cons node_18400 (AllWinning.cons node_17497 (AllWinning.cons node_16583 (AllWinning.cons node_15540 (AllWinning.cons node_14604 (AllWinning.cons node_13633 (AllWinning.cons node_12681 (AllWinning.cons node_11686 (AllWinning.cons node_10685 (AllWinning.cons node_9639 (AllWinning.cons node_18402 (AllWinning.cons node_17502 (AllWinning.cons node_16591 (AllWinning.cons node_15551 (AllWinning.cons node_14618 (AllWinning.cons node_13653 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19292 : Outcome ⟨11, 15, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 6, 2⟩, ⟨9, 15, 6, 4⟩, ⟨8, 15, 6, 6⟩, ⟨7, 15, 6, 8⟩, ⟨6, 15, 6, 10⟩, ⟨5, 15, 6, 12⟩, ⟨4, 15, 6, 14⟩, ⟨3, 15, 6, 16⟩, ⟨2, 15, 6, 18⟩, ⟨1, 15, 6, 20⟩, ⟨0, 15, 6, 22⟩, ⟨11, 14, 6, 2⟩, ⟨11, 13, 6, 4⟩, ⟨11, 12, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨11, 10, 6, 10⟩, ⟨11, 9, 6, 12⟩, ⟨11, 8, 6, 14⟩, ⟨11, 7, 6, 16⟩, ⟨11, 6, 6, 18⟩, ⟨11, 5, 6, 20⟩, ⟨11, 4, 6, 22⟩, ⟨11, 3, 6, 24⟩, ⟨11, 15, 5, 2⟩, ⟨11, 15, 4, 4⟩, ⟨11, 15, 3, 6⟩, ⟨11, 15, 2, 8⟩, ⟨11, 15, 1, 10⟩, ⟨11, 15, 0, 12⟩]
  exact AllWinning.cons node_18344 (AllWinning.cons node_17389 (AllWinning.cons node_16379 (AllWinning.cons node_15308 (AllWinning.cons node_14307 (AllWinning.cons node_13282 (AllWinning.cons node_12263 (AllWinning.cons node_11210 (AllWinning.cons node_10071 (AllWinning.cons node_9028 (AllWinning.cons node_7960 (AllWinning.cons node_18400 (AllWinning.cons node_17497 (AllWinning.cons node_16583 (AllWinning.cons node_15540 (AllWinning.cons node_14604 (AllWinning.cons node_13633 (AllWinning.cons node_12681 (AllWinning.cons node_11686 (AllWinning.cons node_10685 (AllWinning.cons node_9639 (AllWinning.cons node_8687 (AllWinning.cons node_7712 (AllWinning.cons node_18402 (AllWinning.cons node_17502 (AllWinning.cons node_16591 (AllWinning.cons node_15551 (AllWinning.cons node_14618 (AllWinning.cons node_13653 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19293 : Outcome ⟨11, 16, 5, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 5, 2⟩) (by decide) node_18347

theorem node_19294 : Outcome ⟨11, 16, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 5, 2⟩) (by decide) node_18347

theorem node_19295 : Outcome ⟨11, 17, 4, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 2, 4⟩) (by decide) node_17508

theorem node_19296 : Outcome ⟨11, 17, 4, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 6⟩) (by decide) node_16384

theorem node_19297 : Outcome ⟨11, 17, 4, 8⟩ true :=
  Outcome.win (q := ⟨8, 17, 4, 6⟩) (by decide) node_16384

theorem node_19298 : Outcome ⟨11, 18, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 3, 2⟩) (by decide) node_18354

theorem node_19299 : Outcome ⟨11, 18, 3, 8⟩ true :=
  Outcome.win (q := ⟨10, 18, 3, 2⟩) (by decide) node_18354

theorem node_19300 : Outcome ⟨11, 19, 2, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 2, 4⟩) (by decide) node_17508

theorem node_19301 : Outcome ⟨11, 19, 2, 4⟩ true :=
  Outcome.win (q := ⟨8, 19, 2, 6⟩) (by decide) node_16393

theorem node_19302 : Outcome ⟨11, 19, 2, 12⟩ true :=
  Outcome.win (q := ⟨8, 19, 2, 6⟩) (by decide) node_16393

theorem node_19303 : Outcome ⟨12, 0, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 0, 20, 2⟩, ⟨10, 0, 20, 4⟩, ⟨9, 0, 20, 6⟩, ⟨8, 0, 20, 8⟩, ⟨12, 0, 19, 2⟩, ⟨12, 0, 18, 4⟩, ⟨12, 0, 17, 6⟩, ⟨12, 0, 16, 8⟩]
  exact AllWinning.cons node_18361 (AllWinning.cons node_17404 (AllWinning.cons node_16401 (AllWinning.cons node_15321 (AllWinning.cons node_18417 (AllWinning.cons node_17518 (AllWinning.cons node_16603 (AllWinning.cons node_15559 (AllWinning.nil))))))))

theorem node_19304 : Outcome ⟨12, 0, 20, 6⟩ true :=
  Outcome.win (q := ⟨7, 0, 20, 10⟩) (by decide) node_14325

theorem node_19305 : Outcome ⟨12, 1, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 19, 2⟩, ⟨10, 1, 19, 4⟩, ⟨12, 0, 19, 2⟩, ⟨12, 1, 18, 2⟩, ⟨12, 1, 17, 4⟩]
  exact AllWinning.cons node_18363 (AllWinning.cons node_17407 (AllWinning.cons node_18417 (AllWinning.cons node_18420 (AllWinning.cons node_17521 (AllWinning.nil)))))

theorem node_19306 : Outcome ⟨12, 1, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 19, 2⟩, ⟨10, 1, 19, 4⟩, ⟨9, 1, 19, 6⟩, ⟨8, 1, 19, 8⟩, ⟨12, 0, 19, 2⟩, ⟨12, 1, 18, 2⟩, ⟨12, 1, 17, 4⟩, ⟨12, 1, 16, 6⟩, ⟨12, 1, 15, 8⟩]
  exact AllWinning.cons node_18363 (AllWinning.cons node_17407 (AllWinning.cons node_16405 (AllWinning.cons node_15324 (AllWinning.cons node_18417 (AllWinning.cons node_18420 (AllWinning.cons node_17521 (AllWinning.cons node_16607 (AllWinning.cons node_15563 (AllWinning.nil)))))))))

theorem node_19307 : Outcome ⟨12, 1, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 19, 2⟩, ⟨10, 1, 19, 4⟩, ⟨9, 1, 19, 6⟩, ⟨8, 1, 19, 8⟩, ⟨7, 1, 19, 10⟩, ⟨6, 1, 19, 12⟩, ⟨12, 0, 19, 2⟩, ⟨12, 1, 18, 2⟩, ⟨12, 1, 17, 4⟩, ⟨12, 1, 16, 6⟩, ⟨12, 1, 15, 8⟩, ⟨12, 1, 14, 10⟩, ⟨12, 1, 13, 12⟩]
  exact AllWinning.cons node_18363 (AllWinning.cons node_17407 (AllWinning.cons node_16405 (AllWinning.cons node_15324 (AllWinning.cons node_14328 (AllWinning.cons node_13298 (AllWinning.cons node_18417 (AllWinning.cons node_18420 (AllWinning.cons node_17521 (AllWinning.cons node_16607 (AllWinning.cons node_15563 (AllWinning.cons node_14629 (AllWinning.cons node_13660 (AllWinning.nil)))))))))))))

theorem node_19308 : Outcome ⟨12, 1, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 19, 2⟩, ⟨10, 1, 19, 4⟩, ⟨9, 1, 19, 6⟩, ⟨8, 1, 19, 8⟩, ⟨7, 1, 19, 10⟩, ⟨6, 1, 19, 12⟩, ⟨5, 1, 19, 14⟩, ⟨4, 1, 19, 16⟩, ⟨12, 0, 19, 2⟩, ⟨12, 1, 18, 2⟩, ⟨12, 1, 17, 4⟩, ⟨12, 1, 16, 6⟩, ⟨12, 1, 15, 8⟩, ⟨12, 1, 14, 10⟩, ⟨12, 1, 13, 12⟩, ⟨12, 1, 12, 14⟩, ⟨12, 1, 11, 16⟩]
  exact AllWinning.cons node_18363 (AllWinning.cons node_17407 (AllWinning.cons node_16405 (AllWinning.cons node_15324 (AllWinning.cons node_14328 (AllWinning.cons node_13298 (AllWinning.cons node_12283 (AllWinning.cons node_11230 (AllWinning.cons node_18417 (AllWinning.cons node_18420 (AllWinning.cons node_17521 (AllWinning.cons node_16607 (AllWinning.cons node_15563 (AllWinning.cons node_14629 (AllWinning.cons node_13660 (AllWinning.cons node_12707 (AllWinning.cons node_11721 (AllWinning.nil)))))))))))))))))

theorem node_19309 : Outcome ⟨12, 1, 19, 12⟩ true :=
  Outcome.win (q := ⟨12, 1, 8, 22⟩) (by decide) node_8721

theorem node_19310 : Outcome ⟨12, 2, 18, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 10⟩) (by decide) node_14333

theorem node_19311 : Outcome ⟨12, 2, 18, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 18, 10⟩) (by decide) node_14333

theorem node_19312 : Outcome ⟨12, 3, 17, 4⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 4⟩) (by decide) node_17526

theorem node_19313 : Outcome ⟨12, 3, 17, 6⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 4⟩) (by decide) node_17526

theorem node_19314 : Outcome ⟨12, 4, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 4, 16, 2⟩, ⟨10, 4, 16, 4⟩, ⟨12, 3, 16, 2⟩, ⟨12, 2, 16, 4⟩, ⟨12, 4, 15, 2⟩, ⟨12, 4, 14, 4⟩]
  exact AllWinning.cons node_18370 (AllWinning.cons node_17417 (AllWinning.cons node_18423 (AllWinning.cons node_17522 (AllWinning.cons node_18426 (AllWinning.cons node_17531 (AllWinning.nil))))))

theorem node_19315 : Outcome ⟨12, 4, 16, 4⟩ true :=
  Outcome.win (q := ⟨9, 4, 16, 6⟩) (by decide) node_16413

theorem node_19316 : Outcome ⟨12, 5, 15, 4⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 8⟩) (by decide) node_15334

theorem node_19317 : Outcome ⟨12, 5, 15, 6⟩ true :=
  Outcome.win (q := ⟨8, 5, 15, 8⟩) (by decide) node_15334

theorem node_19318 : Outcome ⟨12, 6, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 5, 14, 2⟩) (by decide) node_18428

theorem node_19319 : Outcome ⟨12, 6, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 8⟩) (by decide) node_15567

theorem node_19320 : Outcome ⟨12, 7, 13, 4⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 6⟩) (by decide) node_16429

theorem node_19321 : Outcome ⟨12, 7, 13, 12⟩ true :=
  Outcome.win (q := ⟨9, 7, 13, 6⟩) (by decide) node_16429

theorem node_19322 : Outcome ⟨12, 8, 12, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 12, 2⟩) (by decide) node_18434

theorem node_19323 : Outcome ⟨12, 8, 12, 6⟩ true :=
  Outcome.win (q := ⟨12, 7, 12, 2⟩) (by decide) node_18434

theorem node_19324 : Outcome ⟨12, 9, 11, 2⟩ true :=
  Outcome.win (q := ⟨11, 9, 11, 2⟩) (by decide) node_18385

theorem node_19325 : Outcome ⟨12, 9, 11, 4⟩ true :=
  Outcome.win (q := ⟨11, 9, 11, 2⟩) (by decide) node_18385

theorem node_19326 : Outcome ⟨12, 9, 11, 6⟩ true :=
  Outcome.win (q := ⟨11, 9, 11, 2⟩) (by decide) node_18385

theorem node_19327 : Outcome ⟨12, 10, 10, 2⟩ true :=
  Outcome.win (q := ⟨12, 9, 10, 2⟩) (by decide) node_18443

theorem node_19328 : Outcome ⟨12, 10, 10, 10⟩ true :=
  Outcome.win (q := ⟨12, 9, 10, 2⟩) (by decide) node_18443

theorem node_19329 : Outcome ⟨12, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨11, 11, 9, 2⟩) (by decide) node_18390

theorem node_19330 : Outcome ⟨12, 11, 9, 4⟩ true :=
  Outcome.win (q := ⟨11, 11, 9, 2⟩) (by decide) node_18390

theorem node_19331 : Outcome ⟨12, 11, 9, 6⟩ true :=
  Outcome.win (q := ⟨11, 11, 9, 2⟩) (by decide) node_18390

theorem node_19332 : Outcome ⟨12, 12, 8, 4⟩ true :=
  Outcome.win (q := ⟨12, 12, 7, 2⟩) (by decide) node_18455

theorem node_19333 : Outcome ⟨12, 12, 8, 6⟩ true :=
  Outcome.win (q := ⟨12, 12, 7, 2⟩) (by decide) node_18455

theorem node_19334 : Outcome ⟨12, 13, 7, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 6⟩) (by decide) node_16452

theorem node_19335 : Outcome ⟨12, 13, 7, 12⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 6⟩) (by decide) node_16452

theorem node_19336 : Outcome ⟨12, 14, 6, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 5, 2⟩) (by decide) node_18461

theorem node_19337 : Outcome ⟨12, 14, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 8⟩) (by decide) node_15601

theorem node_19338 : Outcome ⟨12, 15, 5, 4⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 8⟩) (by decide) node_15371

theorem node_19339 : Outcome ⟨12, 15, 5, 6⟩ true :=
  Outcome.win (q := ⟨8, 15, 5, 8⟩) (by decide) node_15371

theorem node_19340 : Outcome ⟨12, 16, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 16, 4, 2⟩, ⟨10, 16, 4, 4⟩, ⟨12, 15, 4, 2⟩, ⟨12, 14, 4, 4⟩, ⟨12, 16, 3, 2⟩, ⟨12, 16, 2, 4⟩]
  exact AllWinning.cons node_18405 (AllWinning.cons node_17449 (AllWinning.cons node_18465 (AllWinning.cons node_17560 (AllWinning.cons node_18467 (AllWinning.cons node_17568 (AllWinning.nil))))))

theorem node_19341 : Outcome ⟨12, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨9, 16, 4, 6⟩) (by decide) node_16467

theorem node_19342 : Outcome ⟨12, 17, 3, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 4⟩) (by decide) node_17564

theorem node_19343 : Outcome ⟨12, 17, 3, 6⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 4⟩) (by decide) node_17564

theorem node_19344 : Outcome ⟨12, 18, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 18, 2, 2⟩, ⟨10, 18, 2, 4⟩, ⟨12, 17, 2, 2⟩, ⟨12, 16, 2, 4⟩, ⟨12, 18, 1, 2⟩, ⟨12, 18, 0, 4⟩]
  exact AllWinning.cons node_18410 (AllWinning.cons node_17456 (AllWinning.cons node_18470 (AllWinning.cons node_17568 (AllWinning.cons node_18471 (AllWinning.cons node_17574 (AllWinning.nil))))))

theorem node_19345 : Outcome ⟨12, 18, 2, 6⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 10⟩) (by decide) node_14387

theorem node_19346 : Outcome ⟨12, 18, 2, 8⟩ true :=
  Outcome.win (q := ⟨7, 18, 2, 10⟩) (by decide) node_14387

theorem node_19347 : Outcome ⟨12, 19, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 1, 2⟩, ⟨10, 19, 1, 4⟩, ⟨9, 19, 1, 6⟩, ⟨8, 19, 1, 8⟩, ⟨12, 18, 1, 2⟩, ⟨12, 17, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨12, 19, 0, 2⟩]
  exact AllWinning.cons node_18413 (AllWinning.cons node_17460 (AllWinning.cons node_16481 (AllWinning.cons node_15385 (AllWinning.cons node_18471 (AllWinning.cons node_17572 (AllWinning.cons node_16655 (AllWinning.cons node_15607 (AllWinning.cons node_18474 (AllWinning.nil)))))))))

theorem node_19348 : Outcome ⟨12, 19, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 1, 2⟩, ⟨10, 19, 1, 4⟩, ⟨9, 19, 1, 6⟩, ⟨8, 19, 1, 8⟩, ⟨7, 19, 1, 10⟩, ⟨6, 19, 1, 12⟩, ⟨12, 18, 1, 2⟩, ⟨12, 17, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨12, 14, 1, 10⟩, ⟨12, 13, 1, 12⟩, ⟨12, 19, 0, 2⟩]
  exact AllWinning.cons node_18413 (AllWinning.cons node_17460 (AllWinning.cons node_16481 (AllWinning.cons node_15385 (AllWinning.cons node_14392 (AllWinning.cons node_13359 (AllWinning.cons node_18471 (AllWinning.cons node_17572 (AllWinning.cons node_16655 (AllWinning.cons node_15607 (AllWinning.cons node_14669 (AllWinning.cons node_13700 (AllWinning.cons node_18474 (AllWinning.nil)))))))))))))

theorem node_19349 : Outcome ⟨12, 19, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 1, 2⟩, ⟨10, 19, 1, 4⟩, ⟨9, 19, 1, 6⟩, ⟨8, 19, 1, 8⟩, ⟨7, 19, 1, 10⟩, ⟨6, 19, 1, 12⟩, ⟨5, 19, 1, 14⟩, ⟨4, 19, 1, 16⟩, ⟨12, 18, 1, 2⟩, ⟨12, 17, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨12, 15, 1, 8⟩, ⟨12, 14, 1, 10⟩, ⟨12, 13, 1, 12⟩, ⟨12, 12, 1, 14⟩, ⟨12, 11, 1, 16⟩, ⟨12, 19, 0, 2⟩]
  exact AllWinning.cons node_18413 (AllWinning.cons node_17460 (AllWinning.cons node_16481 (AllWinning.cons node_15385 (AllWinning.cons node_14392 (AllWinning.cons node_13359 (AllWinning.cons node_12338 (AllWinning.cons node_11294 (AllWinning.cons node_18471 (AllWinning.cons node_17572 (AllWinning.cons node_16655 (AllWinning.cons node_15607 (AllWinning.cons node_14669 (AllWinning.cons node_13700 (AllWinning.cons node_12742 (AllWinning.cons node_11769 (AllWinning.cons node_18474 (AllWinning.nil)))))))))))))))))

theorem node_19350 : Outcome ⟨12, 20, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 20, 0, 2⟩, ⟨10, 20, 0, 4⟩, ⟨9, 20, 0, 6⟩, ⟨8, 20, 0, 8⟩, ⟨12, 19, 0, 2⟩, ⟨12, 18, 0, 4⟩, ⟨12, 17, 0, 6⟩, ⟨12, 16, 0, 8⟩]
  exact AllWinning.cons node_18415 (AllWinning.cons node_17463 (AllWinning.cons node_16483 (AllWinning.cons node_15386 (AllWinning.cons node_18474 (AllWinning.cons node_17574 (AllWinning.cons node_16659 (AllWinning.cons node_15610 (AllWinning.nil))))))))

theorem node_19351 : Outcome ⟨12, 20, 0, 6⟩ true :=
  Outcome.win (q := ⟨7, 20, 0, 10⟩) (by decide) node_14397

theorem node_19352 : Outcome ⟨13, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 19, 4⟩) (by decide) node_17466

theorem node_19353 : Outcome ⟨13, 0, 19, 4⟩ true :=
  Outcome.win (q := ⟨11, 0, 19, 4⟩) (by decide) node_17466

theorem node_19354 : Outcome ⟨13, 0, 19, 12⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 12⟩) (by decide) node_13708

theorem node_19355 : Outcome ⟨13, 0, 19, 16⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 12⟩) (by decide) node_13708

theorem node_19356 : Outcome ⟨13, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 0, 18, 2⟩) (by decide) node_18477

theorem node_19357 : Outcome ⟨13, 1, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 0, 18, 2⟩) (by decide) node_18477

theorem node_19358 : Outcome ⟨13, 1, 18, 12⟩ true :=
  Outcome.win (q := ⟨13, 0, 18, 2⟩) (by decide) node_18477

theorem node_19359 : Outcome ⟨13, 2, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 2, 17, 4⟩) (by decide) node_17470

theorem node_19360 : Outcome ⟨13, 2, 17, 12⟩ true :=
  Outcome.win (q := ⟨11, 2, 17, 4⟩) (by decide) node_17470

theorem node_19361 : Outcome ⟨13, 3, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 3, 16, 2⟩, ⟨11, 3, 16, 4⟩, ⟨13, 2, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨13, 3, 15, 2⟩, ⟨13, 3, 14, 4⟩]
  exact AllWinning.cons node_18423 (AllWinning.cons node_17474 (AllWinning.cons node_18486 (AllWinning.cons node_17579 (AllWinning.cons node_18489 (AllWinning.cons node_17584 (AllWinning.nil))))))

theorem node_19362 : Outcome ⟨13, 3, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 3, 16, 2⟩, ⟨11, 3, 16, 4⟩, ⟨10, 3, 16, 6⟩, ⟨9, 3, 16, 8⟩, ⟨13, 2, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨13, 0, 16, 6⟩, ⟨13, 3, 15, 2⟩, ⟨13, 3, 14, 4⟩, ⟨13, 3, 13, 6⟩, ⟨13, 3, 12, 8⟩]
  exact AllWinning.cons node_18423 (AllWinning.cons node_17474 (AllWinning.cons node_16495 (AllWinning.cons node_15397 (AllWinning.cons node_18486 (AllWinning.cons node_17579 (AllWinning.cons node_16662 (AllWinning.cons node_18489 (AllWinning.cons node_17584 (AllWinning.cons node_16669 (AllWinning.cons node_15624 (AllWinning.nil)))))))))))

theorem node_19363 : Outcome ⟨13, 4, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 4, 15, 2⟩, ⟨11, 4, 15, 4⟩, ⟨13, 3, 15, 2⟩, ⟨13, 2, 15, 4⟩, ⟨13, 4, 14, 2⟩, ⟨13, 4, 13, 4⟩]
  exact AllWinning.cons node_18426 (AllWinning.cons node_17478 (AllWinning.cons node_18489 (AllWinning.cons node_17581 (AllWinning.cons node_18493 (AllWinning.cons node_17588 (AllWinning.nil))))))

theorem node_19364 : Outcome ⟨13, 4, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 6⟩) (by decide) node_16674

theorem node_19365 : Outcome ⟨13, 4, 15, 8⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 6⟩) (by decide) node_16674

theorem node_19366 : Outcome ⟨13, 4, 15, 10⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 6⟩) (by decide) node_16674

theorem node_19367 : Outcome ⟨13, 5, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 5, 14, 2⟩) (by decide) node_18428

theorem node_19368 : Outcome ⟨13, 6, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 5, 13, 2⟩) (by decide) node_18497

theorem node_19369 : Outcome ⟨13, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 5, 13, 2⟩) (by decide) node_18497

theorem node_19370 : Outcome ⟨13, 6, 13, 14⟩ true :=
  Outcome.win (q := ⟨13, 0, 13, 12⟩) (by decide) node_13708

theorem node_19371 : Outcome ⟨13, 7, 12, 4⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 6⟩) (by decide) node_16674

theorem node_19372 : Outcome ⟨13, 7, 12, 12⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 6⟩) (by decide) node_16674

theorem node_19373 : Outcome ⟨13, 8, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 8, 11, 2⟩, ⟨11, 8, 11, 4⟩, ⟨13, 7, 11, 2⟩, ⟨13, 6, 11, 4⟩, ⟨13, 8, 10, 2⟩, ⟨13, 8, 9, 4⟩]
  exact AllWinning.cons node_18438 (AllWinning.cons node_17488 (AllWinning.cons node_18503 (AllWinning.cons node_17594 (AllWinning.cons node_18506 (AllWinning.cons node_17601 (AllWinning.nil))))))

theorem node_19374 : Outcome ⟨13, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 6⟩) (by decide) node_16507

theorem node_19375 : Outcome ⟨13, 8, 11, 8⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 6⟩) (by decide) node_16507

theorem node_19376 : Outcome ⟨13, 8, 11, 16⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 6⟩) (by decide) node_16507

theorem node_19377 : Outcome ⟨13, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨12, 9, 10, 2⟩) (by decide) node_18443

theorem node_19378 : Outcome ⟨13, 9, 10, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 6⟩) (by decide) node_16699

theorem node_19379 : Outcome ⟨13, 9, 10, 6⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 12⟩) (by decide) node_13724

theorem node_19380 : Outcome ⟨13, 9, 10, 10⟩ true :=
  Outcome.win (q := ⟨13, 3, 10, 12⟩) (by decide) node_13724

theorem node_19381 : Outcome ⟨13, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨12, 10, 9, 2⟩) (by decide) node_18447

theorem node_19382 : Outcome ⟨13, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 6⟩) (by decide) node_16688

theorem node_19383 : Outcome ⟨13, 10, 9, 6⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 12⟩) (by decide) node_13750

theorem node_19384 : Outcome ⟨13, 10, 9, 10⟩ true :=
  Outcome.win (q := ⟨13, 10, 3, 12⟩) (by decide) node_13750

theorem node_19385 : Outcome ⟨13, 11, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 11, 8, 2⟩, ⟨11, 11, 8, 4⟩, ⟨13, 10, 8, 2⟩, ⟨13, 9, 8, 4⟩, ⟨13, 11, 7, 2⟩, ⟨13, 11, 6, 4⟩]
  exact AllWinning.cons node_18451 (AllWinning.cons node_17493 (AllWinning.cons node_18512 (AllWinning.cons node_17604 (AllWinning.cons node_18515 (AllWinning.cons node_17610 (AllWinning.nil))))))

theorem node_19386 : Outcome ⟨13, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 6⟩) (by decide) node_16519

theorem node_19387 : Outcome ⟨13, 11, 8, 8⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 6⟩) (by decide) node_16519

theorem node_19388 : Outcome ⟨13, 11, 8, 16⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 6⟩) (by decide) node_16519

theorem node_19389 : Outcome ⟨13, 12, 7, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 6⟩) (by decide) node_16699

theorem node_19390 : Outcome ⟨13, 12, 7, 12⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 6⟩) (by decide) node_16699

theorem node_19391 : Outcome ⟨13, 13, 6, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 5, 2⟩) (by decide) node_18520

theorem node_19392 : Outcome ⟨13, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 5, 2⟩) (by decide) node_18520

theorem node_19393 : Outcome ⟨13, 13, 6, 14⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 12⟩) (by decide) node_13766

theorem node_19394 : Outcome ⟨13, 14, 5, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 5, 2⟩) (by decide) node_18461

theorem node_19395 : Outcome ⟨13, 15, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 4, 2⟩, ⟨11, 15, 4, 4⟩, ⟨13, 14, 4, 2⟩, ⟨13, 13, 4, 4⟩, ⟨13, 15, 3, 2⟩, ⟨13, 15, 2, 4⟩]
  exact AllWinning.cons node_18465 (AllWinning.cons node_17502 (AllWinning.cons node_18524 (AllWinning.cons node_17616 (AllWinning.cons node_18528 (AllWinning.cons node_17624 (AllWinning.nil))))))

theorem node_19396 : Outcome ⟨13, 15, 4, 4⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 6⟩) (by decide) node_16711

theorem node_19397 : Outcome ⟨13, 15, 4, 8⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 6⟩) (by decide) node_16711

theorem node_19398 : Outcome ⟨13, 15, 4, 10⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 6⟩) (by decide) node_16711

theorem node_19399 : Outcome ⟨13, 16, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 3, 2⟩, ⟨11, 16, 3, 4⟩, ⟨13, 15, 3, 2⟩, ⟨13, 14, 3, 4⟩, ⟨13, 16, 2, 2⟩, ⟨13, 16, 1, 4⟩]
  exact AllWinning.cons node_18467 (AllWinning.cons node_17504 (AllWinning.cons node_18528 (AllWinning.cons node_17620 (AllWinning.cons node_18532 (AllWinning.cons node_17627 (AllWinning.nil))))))

theorem node_19400 : Outcome ⟨13, 16, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 3, 2⟩, ⟨11, 16, 3, 4⟩, ⟨10, 16, 3, 6⟩, ⟨9, 16, 3, 8⟩, ⟨13, 15, 3, 2⟩, ⟨13, 14, 3, 4⟩, ⟨13, 13, 3, 6⟩, ⟨13, 12, 3, 8⟩, ⟨13, 16, 2, 2⟩, ⟨13, 16, 1, 4⟩, ⟨13, 16, 0, 6⟩]
  exact AllWinning.cons node_18467 (AllWinning.cons node_17504 (AllWinning.cons node_16533 (AllWinning.cons node_15439 (AllWinning.cons node_18528 (AllWinning.cons node_17620 (AllWinning.cons node_16718 (AllWinning.cons node_15652 (AllWinning.cons node_18532 (AllWinning.cons node_17627 (AllWinning.cons node_16727 (AllWinning.nil)))))))))))

theorem node_19401 : Outcome ⟨13, 17, 2, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 2, 4⟩) (by decide) node_17508

theorem node_19402 : Outcome ⟨13, 17, 2, 12⟩ true :=
  Outcome.win (q := ⟨11, 17, 2, 4⟩) (by decide) node_17508

theorem node_19403 : Outcome ⟨13, 18, 1, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 2⟩) (by decide) node_18535

theorem node_19404 : Outcome ⟨13, 18, 1, 12⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 2⟩) (by decide) node_18535

theorem node_19405 : Outcome ⟨13, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 0, 4⟩) (by decide) node_17514

theorem node_19406 : Outcome ⟨13, 19, 0, 4⟩ true :=
  Outcome.win (q := ⟨11, 19, 0, 4⟩) (by decide) node_17514

theorem node_19407 : Outcome ⟨13, 19, 0, 12⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 12⟩) (by decide) node_13766

theorem node_19408 : Outcome ⟨13, 19, 0, 16⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 12⟩) (by decide) node_13766

theorem node_19409 : Outcome ⟨14, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 0, 18, 2⟩) (by decide) node_18477

theorem node_19410 : Outcome ⟨14, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 1, 17, 2⟩) (by decide) node_18480

theorem node_19411 : Outcome ⟨14, 1, 17, 4⟩ true :=
  Outcome.win (q := ⟨13, 1, 17, 2⟩) (by decide) node_18480

theorem node_19412 : Outcome ⟨14, 2, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 2, 16, 2⟩, ⟨12, 2, 16, 4⟩, ⟨14, 1, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨14, 2, 15, 2⟩, ⟨14, 2, 14, 4⟩]
  exact AllWinning.cons node_18486 (AllWinning.cons node_17522 (AllWinning.cons node_18546 (AllWinning.cons node_17630 (AllWinning.cons node_18549 (AllWinning.cons node_17638 (AllWinning.nil))))))

theorem node_19413 : Outcome ⟨14, 2, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 8⟩) (by decide) node_15457

theorem node_19414 : Outcome ⟨14, 2, 16, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 8⟩) (by decide) node_15457

theorem node_19415 : Outcome ⟨14, 3, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 4⟩) (by decide) node_17526

theorem node_19416 : Outcome ⟨14, 3, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 4⟩) (by decide) node_17526

theorem node_19417 : Outcome ⟨14, 3, 15, 8⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 4⟩) (by decide) node_17526

theorem node_19418 : Outcome ⟨14, 3, 15, 10⟩ true :=
  Outcome.win (q := ⟨12, 3, 15, 4⟩) (by decide) node_17526

theorem node_19419 : Outcome ⟨14, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨14, 3, 14, 2⟩) (by decide) node_18551

theorem node_19420 : Outcome ⟨14, 4, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 8⟩) (by decide) node_15665

theorem node_19421 : Outcome ⟨14, 4, 14, 10⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 8⟩) (by decide) node_15665

theorem node_19422 : Outcome ⟨14, 4, 14, 20⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 8⟩) (by decide) node_15665

theorem node_19423 : Outcome ⟨14, 5, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 5, 13, 2⟩) (by decide) node_18497

theorem node_19424 : Outcome ⟨14, 6, 12, 2⟩ true :=
  Outcome.win (q := ⟨14, 5, 12, 2⟩) (by decide) node_18560

theorem node_19425 : Outcome ⟨14, 6, 12, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 8⟩) (by decide) node_15677

theorem node_19426 : Outcome ⟨14, 7, 11, 4⟩ true :=
  Outcome.win (q := ⟨14, 7, 10, 2⟩) (by decide) node_18566

theorem node_19427 : Outcome ⟨14, 8, 10, 2⟩ true :=
  Outcome.win (q := ⟨14, 7, 10, 2⟩) (by decide) node_18566

theorem node_19428 : Outcome ⟨14, 8, 10, 4⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 6⟩) (by decide) node_16567

theorem node_19429 : Outcome ⟨14, 8, 10, 10⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 14⟩) (by decide) node_12782

theorem node_19430 : Outcome ⟨14, 9, 9, 2⟩ true :=
  Outcome.win (q := ⟨14, 8, 9, 2⟩) (by decide) node_18569

theorem node_19431 : Outcome ⟨14, 9, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 8⟩) (by decide) node_15692

theorem node_19432 : Outcome ⟨14, 9, 9, 10⟩ true :=
  Outcome.win (q := ⟨14, 5, 9, 8⟩) (by decide) node_15692

theorem node_19433 : Outcome ⟨14, 10, 8, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 8, 2⟩) (by decide) node_18572

theorem node_19434 : Outcome ⟨14, 10, 8, 4⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 6⟩) (by decide) node_16575

theorem node_19435 : Outcome ⟨14, 10, 8, 10⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 14⟩) (by decide) node_12815

theorem node_19436 : Outcome ⟨14, 11, 7, 4⟩ true :=
  Outcome.win (q := ⟨14, 10, 7, 2⟩) (by decide) node_18575

theorem node_19437 : Outcome ⟨14, 12, 6, 2⟩ true :=
  Outcome.win (q := ⟨14, 12, 5, 2⟩) (by decide) node_18580

theorem node_19438 : Outcome ⟨14, 12, 6, 4⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 8⟩) (by decide) node_15714

theorem node_19439 : Outcome ⟨14, 13, 5, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 5, 2⟩) (by decide) node_18520

theorem node_19440 : Outcome ⟨14, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 3, 2⟩) (by decide) node_18588

theorem node_19441 : Outcome ⟨14, 14, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 8⟩) (by decide) node_15725

theorem node_19442 : Outcome ⟨14, 14, 4, 10⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 8⟩) (by decide) node_15725

theorem node_19443 : Outcome ⟨14, 14, 4, 20⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 8⟩) (by decide) node_15725

theorem node_19444 : Outcome ⟨14, 15, 3, 2⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 4⟩) (by decide) node_17564

theorem node_19445 : Outcome ⟨14, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 4⟩) (by decide) node_17564

theorem node_19446 : Outcome ⟨14, 15, 3, 8⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 4⟩) (by decide) node_17564

theorem node_19447 : Outcome ⟨14, 15, 3, 10⟩ true :=
  Outcome.win (q := ⟨12, 15, 3, 4⟩) (by decide) node_17564

theorem node_19448 : Outcome ⟨14, 16, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 16, 2, 2⟩, ⟨12, 16, 2, 4⟩, ⟨14, 15, 2, 2⟩, ⟨14, 14, 2, 4⟩, ⟨14, 16, 1, 2⟩, ⟨14, 16, 0, 4⟩]
  exact AllWinning.cons node_18532 (AllWinning.cons node_17568 (AllWinning.cons node_18593 (AllWinning.cons node_17678 (AllWinning.cons node_18595 (AllWinning.cons node_17686 (AllWinning.nil))))))

theorem node_19449 : Outcome ⟨14, 16, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 8⟩) (by decide) node_15500

end RQ9F1
