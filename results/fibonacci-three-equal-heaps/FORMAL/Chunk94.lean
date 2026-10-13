import Chunk93
set_option autoImplicit false
namespace RQ9F1

theorem node_20229 : Outcome ⟨14, 15, 4, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 4, 2⟩) (by decide) node_19395

theorem node_20230 : Outcome ⟨14, 15, 4, 6⟩ true :=
  Outcome.win (q := ⟨13, 15, 4, 2⟩) (by decide) node_19395

theorem node_20231 : Outcome ⟨14, 15, 4, 8⟩ true :=
  Outcome.win (q := ⟨13, 15, 4, 2⟩) (by decide) node_19395

theorem node_20232 : Outcome ⟨14, 16, 3, 2⟩ true :=
  Outcome.win (q := ⟨13, 16, 3, 2⟩) (by decide) node_19399

theorem node_20233 : Outcome ⟨14, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 2, 2⟩) (by decide) node_19448

theorem node_20234 : Outcome ⟨14, 17, 2, 6⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 10⟩) (by decide) node_15715

theorem node_20235 : Outcome ⟨14, 17, 2, 10⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 10⟩) (by decide) node_15715

theorem node_20236 : Outcome ⟨14, 18, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 1, 2⟩, ⟨12, 18, 1, 4⟩, ⟨14, 17, 1, 2⟩, ⟨14, 16, 1, 4⟩, ⟨14, 18, 0, 2⟩]
  exact AllWinning.cons node_19403 (AllWinning.cons node_18472 (AllWinning.cons node_19451 (AllWinning.cons node_18596 (AllWinning.cons node_19453 (AllWinning.nil)))))

theorem node_20237 : Outcome ⟨14, 18, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 1, 2⟩, ⟨12, 18, 1, 4⟩, ⟨11, 18, 1, 6⟩, ⟨10, 18, 1, 8⟩, ⟨14, 17, 1, 2⟩, ⟨14, 16, 1, 4⟩, ⟨14, 15, 1, 6⟩, ⟨14, 14, 1, 8⟩, ⟨14, 18, 0, 2⟩]
  exact AllWinning.cons node_19403 (AllWinning.cons node_18472 (AllWinning.cons node_17512 (AllWinning.cons node_16537 (AllWinning.cons node_19451 (AllWinning.cons node_18596 (AllWinning.cons node_17684 (AllWinning.cons node_16773 (AllWinning.cons node_19453 (AllWinning.nil)))))))))

theorem node_20238 : Outcome ⟨14, 19, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 0, 2⟩, ⟨12, 19, 0, 4⟩, ⟨14, 18, 0, 2⟩, ⟨14, 17, 0, 4⟩]
  exact AllWinning.cons node_19405 (AllWinning.cons node_18475 (AllWinning.cons node_19453 (AllWinning.cons node_18598 (AllWinning.nil))))

theorem node_20239 : Outcome ⟨14, 19, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 0, 2⟩, ⟨12, 19, 0, 4⟩, ⟨11, 19, 0, 6⟩, ⟨10, 19, 0, 8⟩, ⟨14, 18, 0, 2⟩, ⟨14, 17, 0, 4⟩, ⟨14, 16, 0, 6⟩, ⟨14, 15, 0, 8⟩]
  exact AllWinning.cons node_19405 (AllWinning.cons node_18475 (AllWinning.cons node_17515 (AllWinning.cons node_16540 (AllWinning.cons node_19453 (AllWinning.cons node_18598 (AllWinning.cons node_17687 (AllWinning.cons node_16776 (AllWinning.nil))))))))

theorem node_20240 : Outcome ⟨14, 19, 0, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 10⟩) (by decide) node_15726

theorem node_20241 : Outcome ⟨14, 19, 0, 10⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 10⟩) (by decide) node_15726

theorem node_20242 : Outcome ⟨15, 0, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 6⟩) (by decide) node_17691

theorem node_20243 : Outcome ⟨15, 0, 18, 6⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 6⟩) (by decide) node_17691

theorem node_20244 : Outcome ⟨15, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 1, 17, 4⟩) (by decide) node_18481

theorem node_20245 : Outcome ⟨15, 1, 17, 6⟩ true :=
  Outcome.win (q := ⟨13, 1, 17, 4⟩) (by decide) node_18481

theorem node_20246 : Outcome ⟨15, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 2, 16, 2⟩) (by decide) node_19412

theorem node_20247 : Outcome ⟨15, 2, 16, 6⟩ true :=
  Outcome.win (q := ⟨10, 2, 16, 10⟩) (by decide) node_15458

theorem node_20248 : Outcome ⟨15, 3, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 15, 2⟩, ⟨13, 3, 15, 4⟩, ⟨15, 2, 15, 2⟩, ⟨15, 1, 15, 4⟩, ⟨15, 3, 14, 2⟩, ⟨15, 3, 13, 4⟩]
  exact AllWinning.cons node_19415 (AllWinning.cons node_18490 (AllWinning.cons node_19467 (AllWinning.cons node_18603 (AllWinning.cons node_19471 (AllWinning.cons node_18608 (AllWinning.nil))))))

theorem node_20249 : Outcome ⟨15, 3, 15, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 6⟩) (by decide) node_17691

theorem node_20250 : Outcome ⟨15, 3, 15, 6⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 6⟩) (by decide) node_17691

theorem node_20251 : Outcome ⟨15, 3, 15, 14⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 6⟩) (by decide) node_17691

theorem node_20252 : Outcome ⟨15, 4, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 4, 13, 2⟩) (by decide) node_19475

theorem node_20253 : Outcome ⟨15, 4, 14, 6⟩ true :=
  Outcome.win (q := ⟨15, 4, 13, 2⟩) (by decide) node_19475

theorem node_20254 : Outcome ⟨15, 4, 14, 8⟩ true :=
  Outcome.win (q := ⟨15, 4, 13, 2⟩) (by decide) node_19475

theorem node_20255 : Outcome ⟨15, 5, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 5, 13, 4⟩) (by decide) node_18498

theorem node_20256 : Outcome ⟨15, 5, 13, 8⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 10⟩) (by decide) node_15748

theorem node_20257 : Outcome ⟨15, 6, 12, 2⟩ true :=
  Outcome.win (q := ⟨15, 6, 11, 2⟩) (by decide) node_19481

theorem node_20258 : Outcome ⟨15, 6, 12, 16⟩ true :=
  Outcome.win (q := ⟨15, 6, 11, 2⟩) (by decide) node_19481

theorem node_20259 : Outcome ⟨15, 7, 11, 2⟩ true :=
  Outcome.win (q := ⟨15, 6, 11, 2⟩) (by decide) node_19481

theorem node_20260 : Outcome ⟨15, 8, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 8, 10, 2⟩, ⟨13, 8, 10, 4⟩, ⟨15, 7, 10, 2⟩, ⟨15, 6, 10, 4⟩, ⟨15, 8, 9, 2⟩, ⟨15, 8, 8, 4⟩]
  exact AllWinning.cons node_19427 (AllWinning.cons node_18507 (AllWinning.cons node_19486 (AllWinning.cons node_18618 (AllWinning.cons node_19489 (AllWinning.cons node_18625 (AllWinning.nil))))))

theorem node_20261 : Outcome ⟨15, 8, 10, 8⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 10⟩) (by decide) node_15765

theorem node_20262 : Outcome ⟨15, 8, 10, 14⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 10⟩) (by decide) node_15765

theorem node_20263 : Outcome ⟨15, 9, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 9, 2⟩, ⟨13, 9, 9, 4⟩, ⟨15, 8, 9, 2⟩, ⟨15, 7, 9, 4⟩, ⟨15, 9, 8, 2⟩, ⟨15, 9, 7, 4⟩]
  exact AllWinning.cons node_19430 (AllWinning.cons node_18509 (AllWinning.cons node_19489 (AllWinning.cons node_18621 (AllWinning.cons node_19491 (AllWinning.cons node_18629 (AllWinning.nil))))))

theorem node_20264 : Outcome ⟨15, 9, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 9, 2⟩, ⟨13, 9, 9, 4⟩, ⟨12, 9, 9, 6⟩, ⟨11, 9, 9, 8⟩, ⟨15, 8, 9, 2⟩, ⟨15, 7, 9, 4⟩, ⟨15, 6, 9, 6⟩, ⟨15, 5, 9, 8⟩, ⟨15, 9, 8, 2⟩, ⟨15, 9, 7, 4⟩, ⟨15, 9, 6, 6⟩, ⟨15, 9, 5, 8⟩]
  exact AllWinning.cons node_19430 (AllWinning.cons node_18509 (AllWinning.cons node_17546 (AllWinning.cons node_16573 (AllWinning.cons node_19489 (AllWinning.cons node_18621 (AllWinning.cons node_17713 (AllWinning.cons node_16792 (AllWinning.cons node_19491 (AllWinning.cons node_18629 (AllWinning.cons node_17724 (AllWinning.cons node_16803 (AllWinning.nil))))))))))))

theorem node_20265 : Outcome ⟨15, 9, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 9, 9, 2⟩, ⟨13, 9, 9, 4⟩, ⟨12, 9, 9, 6⟩, ⟨11, 9, 9, 8⟩, ⟨10, 9, 9, 10⟩, ⟨9, 9, 9, 12⟩, ⟨15, 8, 9, 2⟩, ⟨15, 7, 9, 4⟩, ⟨15, 6, 9, 6⟩, ⟨15, 5, 9, 8⟩, ⟨15, 4, 9, 10⟩, ⟨15, 3, 9, 12⟩, ⟨15, 9, 8, 2⟩, ⟨15, 9, 7, 4⟩, ⟨15, 9, 6, 6⟩, ⟨15, 9, 5, 8⟩, ⟨15, 9, 4, 10⟩, ⟨15, 9, 3, 12⟩]
  exact AllWinning.cons node_19430 (AllWinning.cons node_18509 (AllWinning.cons node_17546 (AllWinning.cons node_16573 (AllWinning.cons node_15478 (AllWinning.cons node_14486 (AllWinning.cons node_19489 (AllWinning.cons node_18621 (AllWinning.cons node_17713 (AllWinning.cons node_16792 (AllWinning.cons node_15744 (AllWinning.cons node_14760 (AllWinning.cons node_19491 (AllWinning.cons node_18629 (AllWinning.cons node_17724 (AllWinning.cons node_16803 (AllWinning.cons node_15773 (AllWinning.cons node_14776 (AllWinning.nil))))))))))))))))))

theorem node_20266 : Outcome ⟨15, 9, 9, 8⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 14⟩) (by decide) node_13809

theorem node_20267 : Outcome ⟨15, 10, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 10, 8, 2⟩, ⟨13, 10, 8, 4⟩, ⟨15, 9, 8, 2⟩, ⟨15, 8, 8, 4⟩, ⟨15, 10, 7, 2⟩, ⟨15, 10, 6, 4⟩]
  exact AllWinning.cons node_19433 (AllWinning.cons node_18513 (AllWinning.cons node_19491 (AllWinning.cons node_18625 (AllWinning.cons node_19493 (AllWinning.cons node_18633 (AllWinning.nil))))))

theorem node_20268 : Outcome ⟨15, 10, 8, 8⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 10⟩) (by decide) node_15748

theorem node_20269 : Outcome ⟨15, 10, 8, 14⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 10⟩) (by decide) node_15748

theorem node_20270 : Outcome ⟨15, 11, 7, 2⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 2⟩) (by decide) node_19496

theorem node_20271 : Outcome ⟨15, 12, 6, 2⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 2⟩) (by decide) node_19496

theorem node_20272 : Outcome ⟨15, 12, 6, 16⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 2⟩) (by decide) node_19496

theorem node_20273 : Outcome ⟨15, 13, 5, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 5, 4⟩) (by decide) node_18521

theorem node_20274 : Outcome ⟨15, 13, 5, 8⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 10⟩) (by decide) node_15765

theorem node_20275 : Outcome ⟨15, 14, 4, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 4, 2⟩) (by decide) node_19504

theorem node_20276 : Outcome ⟨15, 14, 4, 6⟩ true :=
  Outcome.win (q := ⟨15, 13, 4, 2⟩) (by decide) node_19504

theorem node_20277 : Outcome ⟨15, 14, 4, 8⟩ true :=
  Outcome.win (q := ⟨15, 13, 4, 2⟩) (by decide) node_19504

theorem node_20278 : Outcome ⟨15, 15, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 3, 2⟩, ⟨13, 15, 3, 4⟩, ⟨15, 14, 3, 2⟩, ⟨15, 13, 3, 4⟩, ⟨15, 15, 2, 2⟩, ⟨15, 15, 1, 4⟩]
  exact AllWinning.cons node_19444 (AllWinning.cons node_18529 (AllWinning.cons node_19508 (AllWinning.cons node_18642 (AllWinning.cons node_19512 (AllWinning.cons node_18648 (AllWinning.nil))))))

theorem node_20279 : Outcome ⟨15, 15, 3, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 6⟩) (by decide) node_17743

theorem node_20280 : Outcome ⟨15, 15, 3, 6⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 6⟩) (by decide) node_17743

theorem node_20281 : Outcome ⟨15, 15, 3, 14⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 6⟩) (by decide) node_17743

theorem node_20282 : Outcome ⟨15, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 2, 2⟩) (by decide) node_19448

theorem node_20283 : Outcome ⟨15, 16, 2, 6⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 10⟩) (by decide) node_15501

theorem node_20284 : Outcome ⟨15, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 4⟩) (by decide) node_18536

theorem node_20285 : Outcome ⟨15, 17, 1, 6⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 4⟩) (by decide) node_18536

theorem node_20286 : Outcome ⟨15, 18, 0, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 6⟩) (by decide) node_17743

theorem node_20287 : Outcome ⟨15, 18, 0, 6⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 6⟩) (by decide) node_17743

theorem node_20288 : Outcome ⟨16, 0, 17, 2⟩ true :=
  Outcome.win (q := ⟨16, 0, 16, 2⟩) (by decide) node_19528

theorem node_20289 : Outcome ⟨16, 1, 16, 8⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 2⟩) (by decide) node_19457

theorem node_20290 : Outcome ⟨16, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨16, 1, 15, 2⟩) (by decide) node_19535

theorem node_20291 : Outcome ⟨16, 2, 15, 6⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 10⟩) (by decide) node_15795

theorem node_20292 : Outcome ⟨16, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨16, 2, 14, 2⟩) (by decide) node_19542

theorem node_20293 : Outcome ⟨16, 3, 14, 14⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 12⟩) (by decide) node_14801

theorem node_20294 : Outcome ⟨16, 4, 13, 2⟩ true :=
  Outcome.win (q := ⟨15, 4, 13, 2⟩) (by decide) node_19475

theorem node_20295 : Outcome ⟨16, 5, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 4, 12, 2⟩) (by decide) node_19547

theorem node_20296 : Outcome ⟨16, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨16, 4, 12, 2⟩) (by decide) node_19547

theorem node_20297 : Outcome ⟨16, 5, 12, 8⟩ true :=
  Outcome.win (q := ⟨16, 4, 12, 2⟩) (by decide) node_19547

theorem node_20298 : Outcome ⟨16, 6, 11, 2⟩ true :=
  Outcome.win (q := ⟨15, 6, 11, 2⟩) (by decide) node_19481

theorem node_20299 : Outcome ⟨16, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨14, 7, 10, 4⟩) (by decide) node_18567

theorem node_20300 : Outcome ⟨16, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨14, 7, 10, 4⟩) (by decide) node_18567

theorem node_20301 : Outcome ⟨16, 7, 10, 14⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 10⟩) (by decide) node_15795

theorem node_20302 : Outcome ⟨16, 8, 9, 4⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 8⟩) (by decide) node_16831

theorem node_20303 : Outcome ⟨16, 9, 8, 4⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 8⟩) (by decide) node_16849

theorem node_20304 : Outcome ⟨16, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨14, 10, 7, 4⟩) (by decide) node_18576

theorem node_20305 : Outcome ⟨16, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨14, 10, 7, 4⟩) (by decide) node_18576

theorem node_20306 : Outcome ⟨16, 10, 7, 14⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 10⟩) (by decide) node_15813

theorem node_20307 : Outcome ⟨16, 11, 6, 2⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 2⟩) (by decide) node_19496

theorem node_20308 : Outcome ⟨16, 12, 5, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 4, 2⟩) (by decide) node_19566

theorem node_20309 : Outcome ⟨16, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 4, 2⟩) (by decide) node_19566

theorem node_20310 : Outcome ⟨16, 12, 5, 8⟩ true :=
  Outcome.win (q := ⟨16, 12, 4, 2⟩) (by decide) node_19566

theorem node_20311 : Outcome ⟨16, 13, 4, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 4, 2⟩) (by decide) node_19504

theorem node_20312 : Outcome ⟨16, 14, 3, 2⟩ true :=
  Outcome.win (q := ⟨16, 13, 3, 2⟩) (by decide) node_19568

theorem node_20313 : Outcome ⟨16, 14, 3, 14⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 12⟩) (by decide) node_14819

theorem node_20314 : Outcome ⟨16, 15, 2, 2⟩ true :=
  Outcome.win (q := ⟨16, 14, 2, 2⟩) (by decide) node_19570

theorem node_20315 : Outcome ⟨16, 15, 2, 6⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 10⟩) (by decide) node_15813

theorem node_20316 : Outcome ⟨16, 16, 1, 8⟩ true :=
  Outcome.win (q := ⟨15, 16, 1, 2⟩) (by decide) node_19516

theorem node_20317 : Outcome ⟨16, 17, 0, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 0, 2⟩) (by decide) node_19580

theorem node_20318 : Outcome ⟨17, 0, 16, 2⟩ true :=
  Outcome.win (q := ⟨16, 0, 16, 2⟩) (by decide) node_19528

theorem node_20319 : Outcome ⟨17, 1, 15, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 4⟩) (by decide) node_18699

theorem node_20320 : Outcome ⟨17, 1, 15, 6⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 4⟩) (by decide) node_18699

theorem node_20321 : Outcome ⟨17, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨16, 2, 14, 2⟩) (by decide) node_19542

theorem node_20322 : Outcome ⟨17, 2, 14, 10⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 10⟩) (by decide) node_15568

theorem node_20323 : Outcome ⟨17, 3, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 4⟩) (by decide) node_18699

theorem node_20324 : Outcome ⟨17, 4, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 4, 12, 2⟩) (by decide) node_19547

theorem node_20325 : Outcome ⟨17, 4, 12, 6⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 8⟩) (by decide) node_16675

theorem node_20326 : Outcome ⟨17, 5, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 5, 11, 2⟩, ⟨15, 5, 11, 4⟩, ⟨17, 4, 11, 2⟩, ⟨17, 3, 11, 4⟩, ⟨17, 5, 10, 2⟩, ⟨17, 5, 9, 4⟩]
  exact AllWinning.cons node_19549 (AllWinning.cons node_18615 (AllWinning.cons node_19594 (AllWinning.cons node_18705 (AllWinning.cons node_19597 (AllWinning.cons node_18711 (AllWinning.nil))))))

theorem node_20327 : Outcome ⟨17, 5, 11, 6⟩ true :=
  Outcome.win (q := ⟨17, 5, 7, 8⟩) (by decide) node_16883

theorem node_20328 : Outcome ⟨17, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 9, 2⟩) (by decide) node_19600

theorem node_20329 : Outcome ⟨17, 6, 10, 8⟩ true :=
  Outcome.win (q := ⟨17, 6, 9, 2⟩) (by decide) node_19600

theorem node_20330 : Outcome ⟨17, 7, 9, 2⟩ true :=
  Outcome.win (q := ⟨16, 7, 9, 2⟩) (by decide) node_19554

theorem node_20331 : Outcome ⟨17, 8, 8, 2⟩ true :=
  Outcome.win (q := ⟨17, 7, 8, 2⟩) (by decide) node_19605

theorem node_20332 : Outcome ⟨17, 8, 8, 6⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 8⟩) (by decide) node_16879

theorem node_20333 : Outcome ⟨17, 9, 7, 2⟩ true :=
  Outcome.win (q := ⟨16, 9, 7, 2⟩) (by decide) node_19558

theorem node_20334 : Outcome ⟨17, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 6, 2⟩) (by decide) node_19611

theorem node_20335 : Outcome ⟨17, 10, 6, 8⟩ true :=
  Outcome.win (q := ⟨17, 9, 6, 2⟩) (by decide) node_19611

theorem node_20336 : Outcome ⟨17, 11, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 5, 2⟩, ⟨15, 11, 5, 4⟩, ⟨17, 10, 5, 2⟩, ⟨17, 9, 5, 4⟩, ⟨17, 11, 4, 2⟩, ⟨17, 11, 3, 4⟩]
  exact AllWinning.cons node_19564 (AllWinning.cons node_18636 (AllWinning.cons node_19617 (AllWinning.cons node_18718 (AllWinning.cons node_19620 (AllWinning.cons node_18721 (AllWinning.nil))))))

theorem node_20337 : Outcome ⟨17, 11, 5, 6⟩ true :=
  Outcome.win (q := ⟨17, 7, 5, 8⟩) (by decide) node_16891

theorem node_20338 : Outcome ⟨17, 12, 4, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 4, 2⟩) (by decide) node_19566

theorem node_20339 : Outcome ⟨17, 12, 4, 6⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 8⟩) (by decide) node_16712

theorem node_20340 : Outcome ⟨17, 13, 3, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 4⟩) (by decide) node_18725

theorem node_20341 : Outcome ⟨17, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨16, 14, 2, 2⟩) (by decide) node_19570

theorem node_20342 : Outcome ⟨17, 14, 2, 10⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 10⟩) (by decide) node_15602

theorem node_20343 : Outcome ⟨17, 15, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 4⟩) (by decide) node_18725

theorem node_20344 : Outcome ⟨17, 15, 1, 6⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 4⟩) (by decide) node_18725

theorem node_20345 : Outcome ⟨17, 16, 0, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 0, 2⟩) (by decide) node_19580

theorem node_20346 : Outcome ⟨18, 0, 15, 6⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 6⟩) (by decide) node_17691

theorem node_20347 : Outcome ⟨18, 1, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 14, 2⟩, ⟨16, 1, 14, 4⟩, ⟨18, 0, 14, 2⟩, ⟨18, 1, 13, 2⟩, ⟨18, 1, 12, 4⟩]
  exact AllWinning.cons node_19589 (AllWinning.cons node_18654 (AllWinning.cons node_19630 (AllWinning.cons node_19631 (AllWinning.cons node_18736 (AllWinning.nil)))))

theorem node_20348 : Outcome ⟨18, 1, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 14, 2⟩, ⟨16, 1, 14, 4⟩, ⟨15, 1, 14, 6⟩, ⟨14, 1, 14, 8⟩, ⟨18, 0, 14, 2⟩, ⟨18, 1, 13, 2⟩, ⟨18, 1, 12, 4⟩, ⟨18, 1, 11, 6⟩, ⟨18, 1, 10, 8⟩]
  exact AllWinning.cons node_19589 (AllWinning.cons node_18654 (AllWinning.cons node_17697 (AllWinning.cons node_16733 (AllWinning.cons node_19630 (AllWinning.cons node_19631 (AllWinning.cons node_18736 (AllWinning.cons node_17824 (AllWinning.cons node_16914 (AllWinning.nil)))))))))

theorem node_20349 : Outcome ⟨18, 1, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 14, 2⟩, ⟨16, 1, 14, 4⟩, ⟨15, 1, 14, 6⟩, ⟨14, 1, 14, 8⟩, ⟨13, 1, 14, 10⟩, ⟨12, 1, 14, 12⟩, ⟨18, 0, 14, 2⟩, ⟨18, 1, 13, 2⟩, ⟨18, 1, 12, 4⟩, ⟨18, 1, 11, 6⟩, ⟨18, 1, 10, 8⟩, ⟨18, 1, 9, 10⟩, ⟨18, 1, 8, 12⟩]
  exact AllWinning.cons node_19589 (AllWinning.cons node_18654 (AllWinning.cons node_17697 (AllWinning.cons node_16733 (AllWinning.cons node_15617 (AllWinning.cons node_14630 (AllWinning.cons node_19630 (AllWinning.cons node_19631 (AllWinning.cons node_18736 (AllWinning.cons node_17824 (AllWinning.cons node_16914 (AllWinning.cons node_15852 (AllWinning.cons node_14865 (AllWinning.nil)))))))))))))

theorem node_20350 : Outcome ⟨18, 1, 14, 10⟩ true :=
  Outcome.win (q := ⟨10, 1, 14, 16⟩) (by decide) node_12603

theorem node_20351 : Outcome ⟨18, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨18, 0, 13, 4⟩) (by decide) node_18733

theorem node_20352 : Outcome ⟨18, 2, 13, 6⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 12⟩) (by decide) node_14872

theorem node_20353 : Outcome ⟨18, 2, 13, 10⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 12⟩) (by decide) node_14872

theorem node_20354 : Outcome ⟨18, 3, 12, 4⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 4⟩) (by decide) node_18743

theorem node_20355 : Outcome ⟨18, 3, 12, 6⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 4⟩) (by decide) node_18743

theorem node_20356 : Outcome ⟨18, 4, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 4, 11, 2⟩, ⟨16, 4, 11, 4⟩, ⟨18, 3, 11, 2⟩, ⟨18, 2, 11, 4⟩, ⟨18, 4, 10, 2⟩, ⟨18, 4, 9, 4⟩]
  exact AllWinning.cons node_19594 (AllWinning.cons node_18663 (AllWinning.cons node_19636 (AllWinning.cons node_18740 (AllWinning.cons node_19638 (AllWinning.cons node_18747 (AllWinning.nil))))))

theorem node_20357 : Outcome ⟨18, 4, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 4, 11, 2⟩, ⟨16, 4, 11, 4⟩, ⟨15, 4, 11, 6⟩, ⟨14, 4, 11, 8⟩, ⟨13, 4, 11, 10⟩, ⟨12, 4, 11, 12⟩, ⟨18, 3, 11, 2⟩, ⟨18, 2, 11, 4⟩, ⟨18, 1, 11, 6⟩, ⟨18, 0, 11, 8⟩, ⟨18, 4, 10, 2⟩, ⟨18, 4, 9, 4⟩, ⟨18, 4, 8, 6⟩, ⟨18, 4, 7, 8⟩, ⟨18, 4, 6, 10⟩, ⟨18, 4, 5, 12⟩]
  exact AllWinning.cons node_19594 (AllWinning.cons node_18663 (AllWinning.cons node_17707 (AllWinning.cons node_16741 (AllWinning.cons node_15627 (AllWinning.cons node_14637 (AllWinning.cons node_19636 (AllWinning.cons node_18740 (AllWinning.cons node_17824 (AllWinning.cons node_16912 (AllWinning.cons node_19638 (AllWinning.cons node_18747 (AllWinning.cons node_17833 (AllWinning.cons node_16919 (AllWinning.cons node_15859 (AllWinning.cons node_14879 (AllWinning.nil))))))))))))))))

theorem node_20358 : Outcome ⟨18, 5, 10, 2⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 4⟩) (by decide) node_18743

theorem node_20359 : Outcome ⟨18, 5, 10, 4⟩ true :=
  Outcome.win (q := ⟨18, 3, 10, 4⟩) (by decide) node_18743

theorem node_20360 : Outcome ⟨18, 6, 9, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 9, 2⟩) (by decide) node_19600

theorem node_20361 : Outcome ⟨18, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨17, 7, 8, 2⟩) (by decide) node_19605

theorem node_20362 : Outcome ⟨18, 7, 8, 10⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 12⟩) (by decide) node_14893

theorem node_20363 : Outcome ⟨18, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨17, 8, 7, 2⟩) (by decide) node_19608

theorem node_20364 : Outcome ⟨18, 8, 7, 10⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 12⟩) (by decide) node_14872

theorem node_20365 : Outcome ⟨18, 9, 6, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 6, 2⟩) (by decide) node_19611

theorem node_20366 : Outcome ⟨18, 10, 5, 2⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 4⟩) (by decide) node_18763

theorem node_20367 : Outcome ⟨18, 10, 5, 4⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 4⟩) (by decide) node_18763

theorem node_20368 : Outcome ⟨18, 11, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 11, 4, 2⟩, ⟨16, 11, 4, 4⟩, ⟨18, 10, 4, 2⟩, ⟨18, 9, 4, 4⟩, ⟨18, 11, 3, 2⟩, ⟨18, 11, 2, 4⟩]
  exact AllWinning.cons node_19620 (AllWinning.cons node_18684 (AllWinning.cons node_19645 (AllWinning.cons node_18761 (AllWinning.cons node_19647 (AllWinning.cons node_18767 (AllWinning.nil))))))

theorem node_20369 : Outcome ⟨18, 11, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 11, 4, 2⟩, ⟨16, 11, 4, 4⟩, ⟨15, 11, 4, 6⟩, ⟨14, 11, 4, 8⟩, ⟨13, 11, 4, 10⟩, ⟨12, 11, 4, 12⟩, ⟨18, 10, 4, 2⟩, ⟨18, 9, 4, 4⟩, ⟨18, 8, 4, 6⟩, ⟨18, 7, 4, 8⟩, ⟨18, 6, 4, 10⟩, ⟨18, 5, 4, 12⟩, ⟨18, 11, 3, 2⟩, ⟨18, 11, 2, 4⟩, ⟨18, 11, 1, 6⟩, ⟨18, 11, 0, 8⟩]
  exact AllWinning.cons node_19620 (AllWinning.cons node_18684 (AllWinning.cons node_17729 (AllWinning.cons node_16764 (AllWinning.cons node_15649 (AllWinning.cons node_14661 (AllWinning.cons node_19645 (AllWinning.cons node_18761 (AllWinning.cons node_17843 (AllWinning.cons node_16926 (AllWinning.cons node_15865 (AllWinning.cons node_14882 (AllWinning.cons node_19647 (AllWinning.cons node_18767 (AllWinning.cons node_17851 (AllWinning.cons node_16935 (AllWinning.nil))))))))))))))))

theorem node_20370 : Outcome ⟨18, 12, 3, 4⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 4⟩) (by decide) node_18763

theorem node_20371 : Outcome ⟨18, 12, 3, 6⟩ true :=
  Outcome.win (q := ⟨18, 10, 3, 4⟩) (by decide) node_18763

theorem node_20372 : Outcome ⟨18, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 0, 4⟩) (by decide) node_18773

theorem node_20373 : Outcome ⟨18, 13, 2, 6⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 12⟩) (by decide) node_14893

theorem node_20374 : Outcome ⟨18, 13, 2, 10⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 12⟩) (by decide) node_14893

theorem node_20375 : Outcome ⟨18, 14, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 14, 1, 2⟩, ⟨16, 14, 1, 4⟩, ⟨18, 13, 1, 2⟩, ⟨18, 12, 1, 4⟩, ⟨18, 14, 0, 2⟩]
  exact AllWinning.cons node_19626 (AllWinning.cons node_18692 (AllWinning.cons node_19652 (AllWinning.cons node_18770 (AllWinning.cons node_19654 (AllWinning.nil)))))

theorem node_20376 : Outcome ⟨18, 14, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 14, 1, 2⟩, ⟨16, 14, 1, 4⟩, ⟨15, 14, 1, 6⟩, ⟨14, 14, 1, 8⟩, ⟨18, 13, 1, 2⟩, ⟨18, 12, 1, 4⟩, ⟨18, 11, 1, 6⟩, ⟨18, 10, 1, 8⟩, ⟨18, 14, 0, 2⟩]
  exact AllWinning.cons node_19626 (AllWinning.cons node_18692 (AllWinning.cons node_17739 (AllWinning.cons node_16773 (AllWinning.cons node_19652 (AllWinning.cons node_18770 (AllWinning.cons node_17851 (AllWinning.cons node_16931 (AllWinning.cons node_19654 (AllWinning.nil)))))))))

theorem node_20377 : Outcome ⟨18, 14, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 14, 1, 2⟩, ⟨16, 14, 1, 4⟩, ⟨15, 14, 1, 6⟩, ⟨14, 14, 1, 8⟩, ⟨13, 14, 1, 10⟩, ⟨12, 14, 1, 12⟩, ⟨18, 13, 1, 2⟩, ⟨18, 12, 1, 4⟩, ⟨18, 11, 1, 6⟩, ⟨18, 10, 1, 8⟩, ⟨18, 9, 1, 10⟩, ⟨18, 8, 1, 12⟩, ⟨18, 14, 0, 2⟩]
  exact AllWinning.cons node_19626 (AllWinning.cons node_18692 (AllWinning.cons node_17739 (AllWinning.cons node_16773 (AllWinning.cons node_15659 (AllWinning.cons node_14670 (AllWinning.cons node_19652 (AllWinning.cons node_18770 (AllWinning.cons node_17851 (AllWinning.cons node_16931 (AllWinning.cons node_15872 (AllWinning.cons node_14896 (AllWinning.cons node_19654 (AllWinning.nil)))))))))))))

theorem node_20378 : Outcome ⟨18, 15, 0, 6⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 6⟩) (by decide) node_17743

theorem node_20379 : Outcome ⟨19, 0, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 0, 14, 2⟩, ⟨17, 0, 14, 4⟩, ⟨16, 0, 14, 6⟩, ⟨15, 0, 14, 8⟩, ⟨19, 0, 13, 2⟩, ⟨19, 0, 12, 4⟩, ⟨19, 0, 11, 6⟩, ⟨19, 0, 10, 8⟩]
  exact AllWinning.cons node_19630 (AllWinning.cons node_18696 (AllWinning.cons node_17748 (AllWinning.cons node_16779 (AllWinning.cons node_19655 (AllWinning.cons node_18776 (AllWinning.cons node_17856 (AllWinning.cons node_16937 (AllWinning.nil))))))))

theorem node_20380 : Outcome ⟨19, 0, 14, 8⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 10⟩) (by decide) node_15666

theorem node_20381 : Outcome ⟨19, 0, 14, 10⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 10⟩) (by decide) node_15666

theorem node_20382 : Outcome ⟨19, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 4⟩) (by decide) node_18699

theorem node_20383 : Outcome ⟨19, 1, 13, 14⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 4⟩) (by decide) node_18699

theorem node_20384 : Outcome ⟨19, 2, 12, 2⟩ true :=
  Outcome.win (q := ⟨18, 2, 12, 2⟩) (by decide) node_19633

theorem node_20385 : Outcome ⟨19, 2, 12, 10⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 10⟩) (by decide) node_15678

theorem node_20386 : Outcome ⟨19, 3, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 3, 11, 2⟩, ⟨17, 3, 11, 4⟩, ⟨16, 3, 11, 6⟩, ⟨15, 3, 11, 8⟩, ⟨19, 2, 11, 2⟩, ⟨19, 1, 11, 4⟩, ⟨19, 0, 11, 6⟩, ⟨19, 3, 10, 2⟩, ⟨19, 3, 9, 4⟩, ⟨19, 3, 8, 6⟩, ⟨19, 3, 7, 8⟩]
  exact AllWinning.cons node_19636 (AllWinning.cons node_18705 (AllWinning.cons node_17757 (AllWinning.cons node_16788 (AllWinning.cons node_19661 (AllWinning.cons node_18779 (AllWinning.cons node_17856 (AllWinning.cons node_19664 (AllWinning.cons node_18782 (AllWinning.cons node_17862 (AllWinning.cons node_16949 (AllWinning.nil)))))))))))

theorem node_20387 : Outcome ⟨19, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨19, 4, 9, 2⟩) (by decide) node_19666

theorem node_20388 : Outcome ⟨19, 4, 10, 8⟩ true :=
  Outcome.win (q := ⟨19, 4, 9, 2⟩) (by decide) node_19666

theorem node_20389 : Outcome ⟨19, 5, 9, 2⟩ true :=
  Outcome.win (q := ⟨19, 4, 9, 2⟩) (by decide) node_19666

theorem node_20390 : Outcome ⟨19, 6, 8, 14⟩ true :=
  Outcome.win (q := ⟨7, 6, 8, 24⟩) (by decide) node_8453

theorem node_20391 : Outcome ⟨19, 8, 6, 14⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 24⟩) (by decide) node_8469

theorem node_20392 : Outcome ⟨19, 9, 5, 2⟩ true :=
  Outcome.win (q := ⟨19, 9, 4, 2⟩) (by decide) node_19676

theorem node_20393 : Outcome ⟨19, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨19, 9, 4, 2⟩) (by decide) node_19676

theorem node_20394 : Outcome ⟨19, 10, 4, 8⟩ true :=
  Outcome.win (q := ⟨19, 9, 4, 2⟩) (by decide) node_19676

theorem node_20395 : Outcome ⟨19, 11, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 11, 3, 2⟩, ⟨17, 11, 3, 4⟩, ⟨16, 11, 3, 6⟩, ⟨15, 11, 3, 8⟩, ⟨19, 10, 3, 2⟩, ⟨19, 9, 3, 4⟩, ⟨19, 8, 3, 6⟩, ⟨19, 7, 3, 8⟩, ⟨19, 11, 2, 2⟩, ⟨19, 11, 1, 4⟩, ⟨19, 11, 0, 6⟩]
  exact AllWinning.cons node_19647 (AllWinning.cons node_18721 (AllWinning.cons node_17776 (AllWinning.cons node_16807 (AllWinning.cons node_19678 (AllWinning.cons node_18793 (AllWinning.cons node_17871 (AllWinning.cons node_16958 (AllWinning.cons node_19680 (AllWinning.cons node_18796 (AllWinning.cons node_17877 (AllWinning.nil)))))))))))

theorem node_20396 : Outcome ⟨19, 12, 2, 2⟩ true :=
  Outcome.win (q := ⟨18, 12, 2, 2⟩) (by decide) node_19649

theorem node_20397 : Outcome ⟨19, 12, 2, 10⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 10⟩) (by decide) node_15715

theorem node_20398 : Outcome ⟨19, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 4⟩) (by decide) node_18725

theorem node_20399 : Outcome ⟨19, 13, 1, 14⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 4⟩) (by decide) node_18725

theorem node_20400 : Outcome ⟨19, 14, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 14, 0, 2⟩, ⟨17, 14, 0, 4⟩, ⟨16, 14, 0, 6⟩, ⟨15, 14, 0, 8⟩, ⟨19, 13, 0, 2⟩, ⟨19, 12, 0, 4⟩, ⟨19, 11, 0, 6⟩, ⟨19, 10, 0, 8⟩]
  exact AllWinning.cons node_19654 (AllWinning.cons node_18730 (AllWinning.cons node_17784 (AllWinning.cons node_16815 (AllWinning.cons node_19685 (AllWinning.cons node_18798 (AllWinning.cons node_17877 (AllWinning.cons node_16967 (AllWinning.nil))))))))

theorem node_20401 : Outcome ⟨19, 14, 0, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 10⟩) (by decide) node_15726

theorem node_20402 : Outcome ⟨19, 14, 0, 10⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 10⟩) (by decide) node_15726

theorem node_20403 : Outcome ⟨0, 14, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 20, 4⟩) (by decide) node_18800

theorem node_20404 : Outcome ⟨0, 14, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 12, 20, 4⟩) (by decide) node_18800

theorem node_20405 : Outcome ⟨0, 14, 20, 12⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 12⟩) (by decide) node_14942

theorem node_20406 : Outcome ⟨0, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 19, 2⟩) (by decide) node_19693

theorem node_20407 : Outcome ⟨0, 15, 19, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 8⟩) (by decide) node_16991

theorem node_20408 : Outcome ⟨0, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 4⟩) (by decide) node_18813

theorem node_20409 : Outcome ⟨0, 17, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 17, 2⟩, ⟨0, 15, 17, 4⟩, ⟨0, 17, 16, 2⟩, ⟨0, 17, 15, 4⟩]
  exact AllWinning.cons node_19699 (AllWinning.cons node_18809 (AllWinning.cons node_19700 (AllWinning.cons node_18820 (AllWinning.nil))))

theorem node_20410 : Outcome ⟨0, 17, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 17, 2⟩, ⟨0, 15, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨0, 13, 17, 8⟩, ⟨0, 17, 16, 2⟩, ⟨0, 17, 15, 4⟩, ⟨0, 17, 14, 6⟩, ⟨0, 17, 13, 8⟩]
  exact AllWinning.cons node_19699 (AllWinning.cons node_18809 (AllWinning.cons node_17890 (AllWinning.cons node_16983 (AllWinning.cons node_19700 (AllWinning.cons node_18820 (AllWinning.cons node_17896 (AllWinning.cons node_16999 (AllWinning.nil))))))))

theorem node_20411 : Outcome ⟨0, 17, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 17, 2⟩, ⟨0, 15, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨0, 13, 17, 8⟩, ⟨0, 12, 17, 10⟩, ⟨0, 11, 17, 12⟩, ⟨0, 17, 16, 2⟩, ⟨0, 17, 15, 4⟩, ⟨0, 17, 14, 6⟩, ⟨0, 17, 13, 8⟩, ⟨0, 17, 12, 10⟩, ⟨0, 17, 11, 12⟩]
  exact AllWinning.cons node_19699 (AllWinning.cons node_18809 (AllWinning.cons node_17890 (AllWinning.cons node_16983 (AllWinning.cons node_15915 (AllWinning.cons node_14931 (AllWinning.cons node_19700 (AllWinning.cons node_18820 (AllWinning.cons node_17896 (AllWinning.cons node_16999 (AllWinning.cons node_15929 (AllWinning.cons node_14953 (AllWinning.nil))))))))))))

theorem node_20412 : Outcome ⟨0, 17, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 17, 2⟩, ⟨0, 15, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨0, 13, 17, 8⟩, ⟨0, 12, 17, 10⟩, ⟨0, 11, 17, 12⟩, ⟨0, 10, 17, 14⟩, ⟨0, 9, 17, 16⟩, ⟨0, 17, 16, 2⟩, ⟨0, 17, 15, 4⟩, ⟨0, 17, 14, 6⟩, ⟨0, 17, 13, 8⟩, ⟨0, 17, 12, 10⟩, ⟨0, 17, 11, 12⟩, ⟨0, 17, 10, 14⟩, ⟨0, 17, 9, 16⟩]
  exact AllWinning.cons node_19699 (AllWinning.cons node_18809 (AllWinning.cons node_17890 (AllWinning.cons node_16983 (AllWinning.cons node_15915 (AllWinning.cons node_14931 (AllWinning.cons node_13957 (AllWinning.cons node_12992 (AllWinning.cons node_19700 (AllWinning.cons node_18820 (AllWinning.cons node_17896 (AllWinning.cons node_16999 (AllWinning.cons node_15929 (AllWinning.cons node_14953 (AllWinning.cons node_13983 (AllWinning.cons node_13021 (AllWinning.nil))))))))))))))))

theorem node_20413 : Outcome ⟨0, 17, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 17, 2⟩, ⟨0, 15, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨0, 13, 17, 8⟩, ⟨0, 12, 17, 10⟩, ⟨0, 11, 17, 12⟩, ⟨0, 10, 17, 14⟩, ⟨0, 9, 17, 16⟩, ⟨0, 8, 17, 18⟩, ⟨0, 7, 17, 20⟩, ⟨0, 17, 16, 2⟩, ⟨0, 17, 15, 4⟩, ⟨0, 17, 14, 6⟩, ⟨0, 17, 13, 8⟩, ⟨0, 17, 12, 10⟩, ⟨0, 17, 11, 12⟩, ⟨0, 17, 10, 14⟩, ⟨0, 17, 9, 16⟩, ⟨0, 17, 8, 18⟩, ⟨0, 17, 7, 20⟩]
  exact AllWinning.cons node_19699 (AllWinning.cons node_18809 (AllWinning.cons node_17890 (AllWinning.cons node_16983 (AllWinning.cons node_15915 (AllWinning.cons node_14931 (AllWinning.cons node_13957 (AllWinning.cons node_12992 (AllWinning.cons node_11972 (AllWinning.cons node_10987 (AllWinning.cons node_19700 (AllWinning.cons node_18820 (AllWinning.cons node_17896 (AllWinning.cons node_16999 (AllWinning.cons node_15929 (AllWinning.cons node_14953 (AllWinning.cons node_13983 (AllWinning.cons node_13021 (AllWinning.cons node_11999 (AllWinning.cons node_11023 (AllWinning.nil))))))))))))))))))))

theorem node_20414 : Outcome ⟨0, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 4⟩) (by decide) node_18813

theorem node_20415 : Outcome ⟨0, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 14, 2⟩) (by decide) node_19703

theorem node_20416 : Outcome ⟨0, 19, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 8⟩) (by decide) node_16991

theorem node_20417 : Outcome ⟨0, 20, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 20, 12, 4⟩) (by decide) node_18829

theorem node_20418 : Outcome ⟨0, 20, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 20, 12, 4⟩) (by decide) node_18829

theorem node_20419 : Outcome ⟨0, 20, 14, 12⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 12⟩) (by decide) node_14942

theorem node_20420 : Outcome ⟨1, 13, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 20, 2⟩, ⟨1, 12, 20, 2⟩, ⟨1, 11, 20, 4⟩, ⟨1, 13, 19, 2⟩, ⟨1, 13, 18, 4⟩]
  exact AllWinning.cons node_19689 (AllWinning.cons node_19711 (AllWinning.cons node_18832 (AllWinning.cons node_19714 (AllWinning.cons node_18840 (AllWinning.nil)))))

theorem node_20421 : Outcome ⟨1, 13, 20, 6⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 6⟩) (by decide) node_17919

theorem node_20422 : Outcome ⟨1, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 4⟩) (by decide) node_18834

theorem node_20423 : Outcome ⟨1, 14, 19, 6⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 4⟩) (by decide) node_18834

theorem node_20424 : Outcome ⟨1, 14, 19, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 4⟩) (by decide) node_18834

theorem node_20425 : Outcome ⟨1, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 4⟩) (by decide) node_18845

theorem node_20426 : Outcome ⟨1, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 4⟩) (by decide) node_18845

theorem node_20427 : Outcome ⟨1, 15, 18, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 4⟩) (by decide) node_18845

theorem node_20428 : Outcome ⟨1, 16, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 6⟩) (by decide) node_17919

theorem node_20429 : Outcome ⟨1, 16, 17, 6⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 6⟩) (by decide) node_17919

theorem node_20430 : Outcome ⟨1, 16, 17, 16⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 6⟩) (by decide) node_17919

theorem node_20431 : Outcome ⟨1, 17, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 6⟩) (by decide) node_17936

theorem node_20432 : Outcome ⟨1, 17, 16, 6⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 6⟩) (by decide) node_17936

theorem node_20433 : Outcome ⟨1, 17, 16, 16⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 6⟩) (by decide) node_17936

theorem node_20434 : Outcome ⟨1, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 4⟩) (by decide) node_18852

theorem node_20435 : Outcome ⟨1, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 4⟩) (by decide) node_18852

theorem node_20436 : Outcome ⟨1, 18, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 4⟩) (by decide) node_18852

theorem node_20437 : Outcome ⟨1, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 12, 4⟩) (by decide) node_18864

theorem node_20438 : Outcome ⟨1, 19, 14, 6⟩ true :=
  Outcome.win (q := ⟨1, 19, 12, 4⟩) (by decide) node_18864

theorem node_20439 : Outcome ⟨1, 19, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 19, 12, 4⟩) (by decide) node_18864

theorem node_20440 : Outcome ⟨1, 20, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 20, 13, 2⟩, ⟨1, 19, 13, 2⟩, ⟨1, 18, 13, 4⟩, ⟨1, 20, 12, 2⟩, ⟨1, 20, 11, 4⟩]
  exact AllWinning.cons node_19707 (AllWinning.cons node_19733 (AllWinning.cons node_18861 (AllWinning.cons node_19737 (AllWinning.cons node_18869 (AllWinning.nil)))))

theorem node_20441 : Outcome ⟨1, 20, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 6⟩) (by decide) node_17936

theorem node_20442 : Outcome ⟨2, 12, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 20, 4⟩) (by decide) node_18800

theorem node_20443 : Outcome ⟨2, 12, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 12, 20, 4⟩) (by decide) node_18800

theorem node_20444 : Outcome ⟨2, 13, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 19, 2⟩, ⟨0, 13, 19, 4⟩, ⟨2, 12, 19, 2⟩, ⟨2, 11, 19, 4⟩, ⟨2, 10, 19, 6⟩, ⟨2, 9, 19, 8⟩, ⟨2, 13, 18, 2⟩, ⟨2, 13, 17, 4⟩, ⟨2, 13, 16, 6⟩, ⟨2, 13, 15, 8⟩]
  exact AllWinning.cons node_19714 (AllWinning.cons node_18804 (AllWinning.cons node_19741 (AllWinning.cons node_18873 (AllWinning.cons node_17954 (AllWinning.cons node_17050 (AllWinning.cons node_19744 (AllWinning.cons node_18877 (AllWinning.cons node_17958 (AllWinning.cons node_17064 (AllWinning.nil))))))))))

theorem node_20445 : Outcome ⟨2, 13, 19, 8⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 10⟩) (by decide) node_15988

theorem node_20446 : Outcome ⟨2, 13, 19, 12⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 10⟩) (by decide) node_15988

theorem node_20447 : Outcome ⟨2, 14, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 18, 2⟩) (by decide) node_19718

theorem node_20448 : Outcome ⟨2, 15, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 17, 2⟩, ⟨0, 15, 17, 4⟩, ⟨2, 14, 17, 2⟩, ⟨2, 13, 17, 4⟩, ⟨2, 15, 16, 2⟩, ⟨2, 15, 15, 4⟩]
  exact AllWinning.cons node_19722 (AllWinning.cons node_18809 (AllWinning.cons node_19747 (AllWinning.cons node_18877 (AllWinning.cons node_19750 (AllWinning.cons node_18884 (AllWinning.nil))))))

theorem node_20449 : Outcome ⟨2, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 8⟩) (by decide) node_17056

theorem node_20450 : Outcome ⟨2, 15, 17, 8⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 16⟩) (by decide) node_13116

theorem node_20451 : Outcome ⟨2, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 4⟩) (by decide) node_18813

theorem node_20452 : Outcome ⟨2, 16, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 4⟩) (by decide) node_18813

theorem node_20453 : Outcome ⟨2, 16, 16, 12⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 4⟩) (by decide) node_18813

theorem node_20454 : Outcome ⟨2, 17, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 15, 2⟩, ⟨0, 17, 15, 4⟩, ⟨2, 16, 15, 2⟩, ⟨2, 15, 15, 4⟩, ⟨2, 17, 14, 2⟩, ⟨2, 17, 13, 4⟩]
  exact AllWinning.cons node_19726 (AllWinning.cons node_18820 (AllWinning.cons node_19752 (AllWinning.cons node_18884 (AllWinning.cons node_19754 (AllWinning.cons node_18891 (AllWinning.nil))))))

theorem node_20455 : Outcome ⟨2, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 8⟩) (by decide) node_17078

theorem node_20456 : Outcome ⟨2, 17, 15, 8⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 16⟩) (by decide) node_13097

theorem node_20457 : Outcome ⟨2, 18, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 18, 14, 2⟩) (by decide) node_19729

theorem node_20458 : Outcome ⟨2, 19, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 13, 2⟩, ⟨0, 19, 13, 4⟩, ⟨2, 18, 13, 2⟩, ⟨2, 17, 13, 4⟩, ⟨2, 16, 13, 6⟩, ⟨2, 15, 13, 8⟩, ⟨2, 19, 12, 2⟩, ⟨2, 19, 11, 4⟩, ⟨2, 19, 10, 6⟩, ⟨2, 19, 9, 8⟩]
  exact AllWinning.cons node_19733 (AllWinning.cons node_18826 (AllWinning.cons node_19757 (AllWinning.cons node_18891 (AllWinning.cons node_17965 (AllWinning.cons node_17072 (AllWinning.cons node_19760 (AllWinning.cons node_18896 (AllWinning.cons node_17969 (AllWinning.cons node_17086 (AllWinning.nil))))))))))

theorem node_20459 : Outcome ⟨2, 19, 13, 8⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 10⟩) (by decide) node_16017

theorem node_20460 : Outcome ⟨2, 19, 13, 12⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 10⟩) (by decide) node_16017

theorem node_20461 : Outcome ⟨2, 20, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 20, 12, 4⟩) (by decide) node_18829

theorem node_20462 : Outcome ⟨2, 20, 12, 4⟩ true :=
  Outcome.win (q := ⟨0, 20, 12, 4⟩) (by decide) node_18829

theorem node_20463 : Outcome ⟨3, 11, 20, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 2⟩) (by decide) node_19766

theorem node_20464 : Outcome ⟨3, 11, 20, 16⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 30⟩) (by decide) node_6340

theorem node_20465 : Outcome ⟨3, 12, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 4⟩) (by decide) node_18834

theorem node_20466 : Outcome ⟨3, 12, 19, 18⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 20⟩) (by decide) node_11202

theorem node_20467 : Outcome ⟨3, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 13, 16, 4⟩) (by decide) node_18910

theorem node_20468 : Outcome ⟨3, 13, 18, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 16⟩) (by decide) node_13175

theorem node_20469 : Outcome ⟨3, 14, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 17, 2⟩, ⟨1, 14, 17, 4⟩, ⟨3, 13, 17, 2⟩, ⟨3, 12, 17, 4⟩, ⟨3, 14, 16, 2⟩, ⟨3, 14, 15, 4⟩]
  exact AllWinning.cons node_19747 (AllWinning.cons node_18843 (AllWinning.cons node_19772 (AllWinning.cons node_18907 (AllWinning.cons node_19773 (AllWinning.cons node_18912 (AllWinning.nil))))))

theorem node_20470 : Outcome ⟨3, 14, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 17, 2⟩, ⟨1, 14, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨3, 13, 17, 2⟩, ⟨3, 12, 17, 4⟩, ⟨3, 11, 17, 6⟩, ⟨3, 10, 17, 8⟩, ⟨3, 14, 16, 2⟩, ⟨3, 14, 15, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 14, 13, 8⟩]
  exact AllWinning.cons node_19747 (AllWinning.cons node_18843 (AllWinning.cons node_17890 (AllWinning.cons node_19772 (AllWinning.cons node_18907 (AllWinning.cons node_17982 (AllWinning.cons node_17095 (AllWinning.cons node_19773 (AllWinning.cons node_18912 (AllWinning.cons node_17993 (AllWinning.cons node_17111 (AllWinning.nil)))))))))))

theorem node_20471 : Outcome ⟨3, 14, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 17, 2⟩, ⟨1, 14, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨3, 13, 17, 2⟩, ⟨3, 12, 17, 4⟩, ⟨3, 11, 17, 6⟩, ⟨3, 10, 17, 8⟩, ⟨3, 9, 17, 10⟩, ⟨3, 8, 17, 12⟩, ⟨3, 14, 16, 2⟩, ⟨3, 14, 15, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 14, 13, 8⟩, ⟨3, 14, 12, 10⟩, ⟨3, 14, 11, 12⟩]
  exact AllWinning.cons node_19747 (AllWinning.cons node_18843 (AllWinning.cons node_17890 (AllWinning.cons node_19772 (AllWinning.cons node_18907 (AllWinning.cons node_17982 (AllWinning.cons node_17095 (AllWinning.cons node_16033 (AllWinning.cons node_15075 (AllWinning.cons node_19773 (AllWinning.cons node_18912 (AllWinning.cons node_17993 (AllWinning.cons node_17111 (AllWinning.cons node_16051 (AllWinning.cons node_15096 (AllWinning.nil)))))))))))))))

theorem node_20472 : Outcome ⟨3, 14, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 17, 2⟩, ⟨1, 14, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨3, 13, 17, 2⟩, ⟨3, 12, 17, 4⟩, ⟨3, 11, 17, 6⟩, ⟨3, 10, 17, 8⟩, ⟨3, 9, 17, 10⟩, ⟨3, 8, 17, 12⟩, ⟨3, 7, 17, 14⟩, ⟨3, 6, 17, 16⟩, ⟨3, 14, 16, 2⟩, ⟨3, 14, 15, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 14, 13, 8⟩, ⟨3, 14, 12, 10⟩, ⟨3, 14, 11, 12⟩, ⟨3, 14, 10, 14⟩, ⟨3, 14, 9, 16⟩]
  exact AllWinning.cons node_19747 (AllWinning.cons node_18843 (AllWinning.cons node_17890 (AllWinning.cons node_19772 (AllWinning.cons node_18907 (AllWinning.cons node_17982 (AllWinning.cons node_17095 (AllWinning.cons node_16033 (AllWinning.cons node_15075 (AllWinning.cons node_14108 (AllWinning.cons node_13140 (AllWinning.cons node_19773 (AllWinning.cons node_18912 (AllWinning.cons node_17993 (AllWinning.cons node_17111 (AllWinning.cons node_16051 (AllWinning.cons node_15096 (AllWinning.cons node_14137 (AllWinning.cons node_13179 (AllWinning.nil)))))))))))))))))))

theorem node_20473 : Outcome ⟨3, 14, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 17, 2⟩, ⟨1, 14, 17, 4⟩, ⟨0, 14, 17, 6⟩, ⟨3, 13, 17, 2⟩, ⟨3, 12, 17, 4⟩, ⟨3, 11, 17, 6⟩, ⟨3, 10, 17, 8⟩, ⟨3, 9, 17, 10⟩, ⟨3, 8, 17, 12⟩, ⟨3, 7, 17, 14⟩, ⟨3, 6, 17, 16⟩, ⟨3, 5, 17, 18⟩, ⟨3, 4, 17, 20⟩, ⟨3, 14, 16, 2⟩, ⟨3, 14, 15, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 14, 13, 8⟩, ⟨3, 14, 12, 10⟩, ⟨3, 14, 11, 12⟩, ⟨3, 14, 10, 14⟩, ⟨3, 14, 9, 16⟩, ⟨3, 14, 8, 18⟩, ⟨3, 14, 7, 20⟩]
  exact AllWinning.cons node_19747 (AllWinning.cons node_18843 (AllWinning.cons node_17890 (AllWinning.cons node_19772 (AllWinning.cons node_18907 (AllWinning.cons node_17982 (AllWinning.cons node_17095 (AllWinning.cons node_16033 (AllWinning.cons node_15075 (AllWinning.cons node_14108 (AllWinning.cons node_13140 (AllWinning.cons node_12164 (AllWinning.cons node_11160 (AllWinning.cons node_19773 (AllWinning.cons node_18912 (AllWinning.cons node_17993 (AllWinning.cons node_17111 (AllWinning.cons node_16051 (AllWinning.cons node_15096 (AllWinning.cons node_14137 (AllWinning.cons node_13179 (AllWinning.cons node_12194 (AllWinning.cons node_11208 (AllWinning.nil)))))))))))))))))))))))

theorem node_20474 : Outcome ⟨3, 15, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 4⟩) (by decide) node_18845

theorem node_20475 : Outcome ⟨3, 16, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 4⟩) (by decide) node_18852

theorem node_20476 : Outcome ⟨3, 17, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 14, 2⟩, ⟨1, 17, 14, 4⟩, ⟨3, 16, 14, 2⟩, ⟨3, 15, 14, 4⟩, ⟨3, 17, 13, 2⟩, ⟨3, 17, 12, 4⟩]
  exact AllWinning.cons node_19754 (AllWinning.cons node_18859 (AllWinning.cons node_19779 (AllWinning.cons node_18916 (AllWinning.cons node_19781 (AllWinning.cons node_18921 (AllWinning.nil))))))

theorem node_20477 : Outcome ⟨3, 17, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 14, 2⟩, ⟨1, 17, 14, 4⟩, ⟨0, 17, 14, 6⟩, ⟨3, 16, 14, 2⟩, ⟨3, 15, 14, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 13, 14, 8⟩, ⟨3, 17, 13, 2⟩, ⟨3, 17, 12, 4⟩, ⟨3, 17, 11, 6⟩, ⟨3, 17, 10, 8⟩]
  exact AllWinning.cons node_19754 (AllWinning.cons node_18859 (AllWinning.cons node_17896 (AllWinning.cons node_19779 (AllWinning.cons node_18916 (AllWinning.cons node_17993 (AllWinning.cons node_17107 (AllWinning.cons node_19781 (AllWinning.cons node_18921 (AllWinning.cons node_18004 (AllWinning.cons node_17120 (AllWinning.nil)))))))))))

theorem node_20478 : Outcome ⟨3, 17, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 14, 2⟩, ⟨1, 17, 14, 4⟩, ⟨0, 17, 14, 6⟩, ⟨3, 16, 14, 2⟩, ⟨3, 15, 14, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 13, 14, 8⟩, ⟨3, 12, 14, 10⟩, ⟨3, 11, 14, 12⟩, ⟨3, 17, 13, 2⟩, ⟨3, 17, 12, 4⟩, ⟨3, 17, 11, 6⟩, ⟨3, 17, 10, 8⟩, ⟨3, 17, 9, 10⟩, ⟨3, 17, 8, 12⟩]
  exact AllWinning.cons node_19754 (AllWinning.cons node_18859 (AllWinning.cons node_17896 (AllWinning.cons node_19779 (AllWinning.cons node_18916 (AllWinning.cons node_17993 (AllWinning.cons node_17107 (AllWinning.cons node_16042 (AllWinning.cons node_15084 (AllWinning.cons node_19781 (AllWinning.cons node_18921 (AllWinning.cons node_18004 (AllWinning.cons node_17120 (AllWinning.cons node_16062 (AllWinning.cons node_15103 (AllWinning.nil)))))))))))))))

theorem node_20479 : Outcome ⟨3, 17, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 14, 2⟩, ⟨1, 17, 14, 4⟩, ⟨0, 17, 14, 6⟩, ⟨3, 16, 14, 2⟩, ⟨3, 15, 14, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 13, 14, 8⟩, ⟨3, 12, 14, 10⟩, ⟨3, 11, 14, 12⟩, ⟨3, 10, 14, 14⟩, ⟨3, 9, 14, 16⟩, ⟨3, 17, 13, 2⟩, ⟨3, 17, 12, 4⟩, ⟨3, 17, 11, 6⟩, ⟨3, 17, 10, 8⟩, ⟨3, 17, 9, 10⟩, ⟨3, 17, 8, 12⟩, ⟨3, 17, 7, 14⟩, ⟨3, 17, 6, 16⟩]
  exact AllWinning.cons node_19754 (AllWinning.cons node_18859 (AllWinning.cons node_17896 (AllWinning.cons node_19779 (AllWinning.cons node_18916 (AllWinning.cons node_17993 (AllWinning.cons node_17107 (AllWinning.cons node_16042 (AllWinning.cons node_15084 (AllWinning.cons node_14124 (AllWinning.cons node_13150 (AllWinning.cons node_19781 (AllWinning.cons node_18921 (AllWinning.cons node_18004 (AllWinning.cons node_17120 (AllWinning.cons node_16062 (AllWinning.cons node_15103 (AllWinning.cons node_14152 (AllWinning.cons node_13190 (AllWinning.nil)))))))))))))))))))

theorem node_20480 : Outcome ⟨3, 17, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 14, 2⟩, ⟨1, 17, 14, 4⟩, ⟨0, 17, 14, 6⟩, ⟨3, 16, 14, 2⟩, ⟨3, 15, 14, 4⟩, ⟨3, 14, 14, 6⟩, ⟨3, 13, 14, 8⟩, ⟨3, 12, 14, 10⟩, ⟨3, 11, 14, 12⟩, ⟨3, 10, 14, 14⟩, ⟨3, 9, 14, 16⟩, ⟨3, 8, 14, 18⟩, ⟨3, 7, 14, 20⟩, ⟨3, 17, 13, 2⟩, ⟨3, 17, 12, 4⟩, ⟨3, 17, 11, 6⟩, ⟨3, 17, 10, 8⟩, ⟨3, 17, 9, 10⟩, ⟨3, 17, 8, 12⟩, ⟨3, 17, 7, 14⟩, ⟨3, 17, 6, 16⟩, ⟨3, 17, 5, 18⟩, ⟨3, 17, 4, 20⟩]
  exact AllWinning.cons node_19754 (AllWinning.cons node_18859 (AllWinning.cons node_17896 (AllWinning.cons node_19779 (AllWinning.cons node_18916 (AllWinning.cons node_17993 (AllWinning.cons node_17107 (AllWinning.cons node_16042 (AllWinning.cons node_15084 (AllWinning.cons node_14124 (AllWinning.cons node_13150 (AllWinning.cons node_12178 (AllWinning.cons node_11169 (AllWinning.cons node_19781 (AllWinning.cons node_18921 (AllWinning.cons node_18004 (AllWinning.cons node_17120 (AllWinning.cons node_16062 (AllWinning.cons node_15103 (AllWinning.cons node_14152 (AllWinning.cons node_13190 (AllWinning.cons node_12209 (AllWinning.cons node_11218 (AllWinning.nil)))))))))))))))))))))))

theorem node_20481 : Outcome ⟨3, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨3, 16, 13, 4⟩) (by decide) node_18920

theorem node_20482 : Outcome ⟨3, 18, 13, 8⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 16⟩) (by decide) node_13157

theorem node_20483 : Outcome ⟨3, 19, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 12, 4⟩) (by decide) node_18864

theorem node_20484 : Outcome ⟨3, 19, 12, 18⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 20⟩) (by decide) node_11181

theorem node_20485 : Outcome ⟨3, 20, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 2⟩) (by decide) node_19784

theorem node_20486 : Outcome ⟨3, 20, 11, 16⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 30⟩) (by decide) node_6309

end RQ9F1
