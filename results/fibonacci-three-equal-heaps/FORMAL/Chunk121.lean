import Chunk120
set_option autoImplicit false
namespace RQ9F1

theorem node_25415 : Outcome ⟨16, 16, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 13, 2⟩, ⟨14, 16, 13, 4⟩, ⟨13, 16, 13, 6⟩, ⟨12, 16, 13, 8⟩, ⟨11, 16, 13, 10⟩, ⟨10, 16, 13, 12⟩, ⟨9, 16, 13, 14⟩, ⟨8, 16, 13, 16⟩, ⟨16, 15, 13, 2⟩, ⟨16, 14, 13, 4⟩, ⟨16, 13, 13, 6⟩, ⟨16, 12, 13, 8⟩, ⟨16, 11, 13, 10⟩, ⟨16, 10, 13, 12⟩, ⟨16, 9, 13, 14⟩, ⟨16, 8, 13, 16⟩, ⟨16, 16, 12, 2⟩, ⟨16, 16, 11, 4⟩, ⟨16, 16, 10, 6⟩, ⟨16, 16, 9, 8⟩, ⟨16, 16, 8, 10⟩, ⟨16, 16, 7, 12⟩, ⟨16, 16, 6, 14⟩, ⟨16, 16, 5, 16⟩]
  exact AllWinning.cons node_25212 (AllWinning.cons node_24962 (AllWinning.cons node_24675 (AllWinning.cons node_24364 (AllWinning.cons node_23975 (AllWinning.cons node_23564 (AllWinning.cons node_23104 (AllWinning.cons node_22551 (AllWinning.cons node_25230 (AllWinning.cons node_25002 (AllWinning.cons node_24756 (AllWinning.cons node_24460 (AllWinning.cons node_24133 (AllWinning.cons node_23727 (AllWinning.cons node_23323 (AllWinning.cons node_22855 (AllWinning.cons node_25232 (AllWinning.cons node_25005 (AllWinning.cons node_24763 (AllWinning.cons node_24469 (AllWinning.cons node_24151 (AllWinning.cons node_23739 (AllWinning.cons node_23339 (AllWinning.cons node_22875 (AllWinning.nil))))))))))))))))))))))))

theorem node_25416 : Outcome ⟨16, 17, 12, 4⟩ true :=
  Outcome.win (q := ⟨13, 17, 12, 6⟩) (by decide) node_24678

theorem node_25417 : Outcome ⟨16, 18, 11, 2⟩ true :=
  Outcome.win (q := ⟨16, 18, 10, 2⟩) (by decide) node_25235

theorem node_25418 : Outcome ⟨16, 18, 11, 8⟩ true :=
  Outcome.win (q := ⟨16, 18, 10, 2⟩) (by decide) node_25235

theorem node_25419 : Outcome ⟨16, 19, 10, 2⟩ true :=
  Outcome.win (q := ⟨15, 19, 10, 2⟩) (by decide) node_25218

theorem node_25420 : Outcome ⟨17, 10, 18, 4⟩ true :=
  Outcome.win (q := ⟨16, 10, 18, 2⟩) (by decide) node_25222

theorem node_25421 : Outcome ⟨17, 11, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 17, 2⟩, ⟨15, 11, 17, 4⟩, ⟨17, 10, 17, 2⟩, ⟨17, 9, 17, 4⟩, ⟨17, 11, 16, 2⟩, ⟨17, 11, 15, 4⟩]
  exact AllWinning.cons node_25224 (AllWinning.cons node_24973 (AllWinning.cons node_25239 (AllWinning.cons node_25013 (AllWinning.cons node_25241 (AllWinning.cons node_25017 (AllWinning.nil))))))

theorem node_25422 : Outcome ⟨17, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨14, 11, 17, 6⟩) (by decide) node_24689

theorem node_25423 : Outcome ⟨17, 12, 16, 4⟩ true :=
  Outcome.win (q := ⟨17, 9, 16, 6⟩) (by decide) node_24773

theorem node_25424 : Outcome ⟨17, 13, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 13, 15, 2⟩, ⟨15, 13, 15, 4⟩, ⟨17, 12, 15, 2⟩, ⟨17, 11, 15, 4⟩, ⟨17, 13, 14, 2⟩, ⟨17, 13, 13, 4⟩]
  exact AllWinning.cons node_25227 (AllWinning.cons node_24978 (AllWinning.cons node_25244 (AllWinning.cons node_25017 (AllWinning.cons node_25246 (AllWinning.cons node_25022 (AllWinning.nil))))))

theorem node_25425 : Outcome ⟨17, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 13, 15, 6⟩) (by decide) node_24695

theorem node_25426 : Outcome ⟨17, 14, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 14, 14, 2⟩, ⟨15, 14, 14, 4⟩, ⟨17, 13, 14, 2⟩, ⟨17, 12, 14, 4⟩, ⟨17, 14, 13, 2⟩, ⟨17, 14, 12, 4⟩]
  exact AllWinning.cons node_25229 (AllWinning.cons node_24980 (AllWinning.cons node_25246 (AllWinning.cons node_25019 (AllWinning.cons node_25248 (AllWinning.cons node_25025 (AllWinning.nil))))))

theorem node_25427 : Outcome ⟨17, 14, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 14, 6⟩) (by decide) node_24698

theorem node_25428 : Outcome ⟨17, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 13, 6⟩) (by decide) node_24701

theorem node_25429 : Outcome ⟨17, 16, 12, 4⟩ true :=
  Outcome.win (q := ⟨17, 13, 12, 6⟩) (by decide) node_24780

theorem node_25430 : Outcome ⟨17, 17, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 17, 11, 2⟩, ⟨15, 17, 11, 4⟩, ⟨17, 16, 11, 2⟩, ⟨17, 15, 11, 4⟩, ⟨17, 17, 10, 2⟩, ⟨17, 17, 9, 4⟩]
  exact AllWinning.cons node_25233 (AllWinning.cons node_24987 (AllWinning.cons node_25251 (AllWinning.cons node_25027 (AllWinning.cons node_25254 (AllWinning.cons node_25030 (AllWinning.nil))))))

theorem node_25431 : Outcome ⟨17, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨14, 17, 11, 6⟩) (by decide) node_24707

theorem node_25432 : Outcome ⟨17, 18, 10, 4⟩ true :=
  Outcome.win (q := ⟨16, 18, 10, 2⟩) (by decide) node_25235

theorem node_25433 : Outcome ⟨18, 8, 19, 2⟩ true :=
  Outcome.win (q := ⟨18, 7, 19, 2⟩) (by decide) node_25257

theorem node_25434 : Outcome ⟨18, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨18, 10, 16, 2⟩) (by decide) node_25260

theorem node_25435 : Outcome ⟨18, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 15, 4⟩) (by decide) node_24998

theorem node_25436 : Outcome ⟨18, 12, 15, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 15, 4⟩) (by decide) node_24998

theorem node_25437 : Outcome ⟨18, 14, 13, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 13, 2⟩) (by decide) node_25263

theorem node_25438 : Outcome ⟨18, 14, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 6⟩) (by decide) node_24729

theorem node_25439 : Outcome ⟨18, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨18, 16, 10, 2⟩) (by decide) node_25266

theorem node_25440 : Outcome ⟨18, 19, 8, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 8, 2⟩) (by decide) node_25267

theorem node_25441 : Outcome ⟨19, 7, 19, 2⟩ true :=
  Outcome.win (q := ⟨19, 5, 19, 4⟩) (by decide) node_25047

theorem node_25442 : Outcome ⟨19, 7, 19, 12⟩ true :=
  Outcome.win (q := ⟨19, 0, 19, 14⟩) (by decide) node_23409

theorem node_25443 : Outcome ⟨19, 8, 18, 2⟩ true :=
  Outcome.win (q := ⟨18, 8, 18, 2⟩) (by decide) node_25258

theorem node_25444 : Outcome ⟨19, 10, 16, 2⟩ true :=
  Outcome.win (q := ⟨18, 10, 16, 2⟩) (by decide) node_25260

theorem node_25445 : Outcome ⟨19, 11, 15, 2⟩ true :=
  Outcome.win (q := ⟨19, 10, 15, 2⟩) (by decide) node_25272

theorem node_25446 : Outcome ⟨19, 12, 14, 2⟩ true :=
  Outcome.win (q := ⟨19, 12, 12, 4⟩) (by decide) node_25053

theorem node_25447 : Outcome ⟨19, 13, 13, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 13, 2⟩) (by decide) node_25263

theorem node_25448 : Outcome ⟨19, 13, 13, 12⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 12⟩) (by decide) node_23640

theorem node_25449 : Outcome ⟨19, 14, 12, 2⟩ true :=
  Outcome.win (q := ⟨19, 12, 12, 4⟩) (by decide) node_25053

theorem node_25450 : Outcome ⟨19, 15, 11, 2⟩ true :=
  Outcome.win (q := ⟨19, 15, 10, 2⟩) (by decide) node_25277

theorem node_25451 : Outcome ⟨19, 16, 10, 2⟩ true :=
  Outcome.win (q := ⟨18, 16, 10, 2⟩) (by decide) node_25266

theorem node_25452 : Outcome ⟨19, 18, 8, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 8, 2⟩) (by decide) node_25267

theorem node_25453 : Outcome ⟨19, 19, 7, 2⟩ true :=
  Outcome.win (q := ⟨19, 19, 5, 4⟩) (by decide) node_25059

theorem node_25454 : Outcome ⟨19, 19, 7, 12⟩ true :=
  Outcome.win (q := ⟨19, 19, 0, 14⟩) (by decide) node_23421

theorem node_25455 : Outcome ⟨6, 20, 20, 4⟩ true :=
  Outcome.win (q := ⟨5, 20, 20, 2⟩) (by decide) node_25281

theorem node_25456 : Outcome ⟨8, 18, 20, 2⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 4⟩) (by decide) node_25084

theorem node_25457 : Outcome ⟨8, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 4⟩) (by decide) node_25084

theorem node_25458 : Outcome ⟨8, 19, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 19, 19, 2⟩, ⟨6, 19, 19, 4⟩, ⟨8, 18, 19, 2⟩, ⟨8, 17, 19, 4⟩, ⟨8, 19, 18, 2⟩, ⟨8, 19, 17, 4⟩]
  exact AllWinning.cons node_25285 (AllWinning.cons node_25066 (AllWinning.cons node_25289 (AllWinning.cons node_25082 (AllWinning.cons node_25291 (AllWinning.cons node_25088 (AllWinning.nil))))))

theorem node_25459 : Outcome ⟨8, 19, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 19, 19, 2⟩, ⟨6, 19, 19, 4⟩, ⟨5, 19, 19, 6⟩, ⟨4, 19, 19, 8⟩, ⟨8, 18, 19, 2⟩, ⟨8, 17, 19, 4⟩, ⟨8, 16, 19, 6⟩, ⟨8, 15, 19, 8⟩, ⟨8, 19, 18, 2⟩, ⟨8, 19, 17, 4⟩, ⟨8, 19, 16, 6⟩, ⟨8, 19, 15, 8⟩]
  exact AllWinning.cons node_25285 (AllWinning.cons node_25066 (AllWinning.cons node_24833 (AllWinning.cons node_24533 (AllWinning.cons node_25289 (AllWinning.cons node_25082 (AllWinning.cons node_24860 (AllWinning.cons node_24562 (AllWinning.cons node_25291 (AllWinning.cons node_25088 (AllWinning.cons node_24865 (AllWinning.cons node_24571 (AllWinning.nil))))))))))))

theorem node_25460 : Outcome ⟨8, 19, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 19, 19, 2⟩, ⟨6, 19, 19, 4⟩, ⟨5, 19, 19, 6⟩, ⟨4, 19, 19, 8⟩, ⟨3, 19, 19, 10⟩, ⟨2, 19, 19, 12⟩, ⟨8, 18, 19, 2⟩, ⟨8, 17, 19, 4⟩, ⟨8, 16, 19, 6⟩, ⟨8, 15, 19, 8⟩, ⟨8, 14, 19, 10⟩, ⟨8, 13, 19, 12⟩, ⟨8, 19, 18, 2⟩, ⟨8, 19, 17, 4⟩, ⟨8, 19, 16, 6⟩, ⟨8, 19, 15, 8⟩, ⟨8, 19, 14, 10⟩, ⟨8, 19, 13, 12⟩]
  exact AllWinning.cons node_25285 (AllWinning.cons node_25066 (AllWinning.cons node_24833 (AllWinning.cons node_24533 (AllWinning.cons node_24235 (AllWinning.cons node_23818 (AllWinning.cons node_25289 (AllWinning.cons node_25082 (AllWinning.cons node_24860 (AllWinning.cons node_24562 (AllWinning.cons node_24289 (AllWinning.cons node_23888 (AllWinning.cons node_25291 (AllWinning.cons node_25088 (AllWinning.cons node_24865 (AllWinning.cons node_24571 (AllWinning.cons node_24301 (AllWinning.cons node_23903 (AllWinning.nil))))))))))))))))))

theorem node_25461 : Outcome ⟨8, 20, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 4⟩) (by decide) node_25084

theorem node_25462 : Outcome ⟨8, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 4⟩) (by decide) node_25084

theorem node_25463 : Outcome ⟨9, 17, 20, 2⟩ true :=
  Outcome.win (q := ⟨8, 17, 20, 2⟩) (by decide) node_25287

theorem node_25464 : Outcome ⟨9, 17, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 17, 16, 8⟩) (by decide) node_24591

theorem node_25465 : Outcome ⟨9, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 19, 4⟩) (by decide) node_25071

theorem node_25466 : Outcome ⟨9, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨7, 19, 18, 4⟩) (by decide) node_25074

theorem node_25467 : Outcome ⟨9, 20, 17, 2⟩ true :=
  Outcome.win (q := ⟨8, 20, 17, 2⟩) (by decide) node_25293

theorem node_25468 : Outcome ⟨9, 20, 17, 4⟩ true :=
  Outcome.win (q := ⟨9, 16, 17, 8⟩) (by decide) node_24586

theorem node_25469 : Outcome ⟨10, 16, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 16, 20, 2⟩, ⟨8, 16, 20, 4⟩, ⟨10, 15, 20, 2⟩, ⟨10, 14, 20, 4⟩, ⟨10, 16, 19, 2⟩, ⟨10, 16, 18, 4⟩]
  exact AllWinning.cons node_25295 (AllWinning.cons node_25079 (AllWinning.cons node_25305 (AllWinning.cons node_25107 (AllWinning.cons node_25307 (AllWinning.cons node_25112 (AllWinning.nil))))))

theorem node_25470 : Outcome ⟨10, 16, 20, 4⟩ true :=
  Outcome.win (q := ⟨7, 16, 20, 6⟩) (by decide) node_24844

theorem node_25471 : Outcome ⟨10, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨9, 17, 19, 2⟩) (by decide) node_25298

theorem node_25472 : Outcome ⟨10, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 4⟩) (by decide) node_25084

theorem node_25473 : Outcome ⟨10, 18, 18, 6⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 4⟩) (by decide) node_25084

theorem node_25474 : Outcome ⟨10, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨9, 19, 17, 2⟩) (by decide) node_25301

theorem node_25475 : Outcome ⟨10, 20, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 20, 16, 2⟩, ⟨8, 20, 16, 4⟩, ⟨10, 19, 16, 2⟩, ⟨10, 18, 16, 4⟩, ⟨10, 20, 15, 2⟩, ⟨10, 20, 14, 4⟩]
  exact AllWinning.cons node_25302 (AllWinning.cons node_25090 (AllWinning.cons node_25311 (AllWinning.cons node_25118 (AllWinning.cons node_25313 (AllWinning.cons node_25125 (AllWinning.nil))))))

theorem node_25476 : Outcome ⟨10, 20, 16, 4⟩ true :=
  Outcome.win (q := ⟨7, 20, 16, 6⟩) (by decide) node_24855

theorem node_25477 : Outcome ⟨11, 15, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 20, 2⟩, ⟨9, 15, 20, 4⟩, ⟨11, 14, 20, 2⟩, ⟨11, 13, 20, 4⟩, ⟨11, 15, 19, 2⟩, ⟨11, 15, 18, 4⟩]
  exact AllWinning.cons node_25305 (AllWinning.cons node_25092 (AllWinning.cons node_25315 (AllWinning.cons node_25126 (AllWinning.cons node_25317 (AllWinning.cons node_25129 (AllWinning.nil))))))

theorem node_25478 : Outcome ⟨11, 15, 20, 4⟩ true :=
  Outcome.win (q := ⟨11, 11, 20, 8⟩) (by decide) node_24615

theorem node_25479 : Outcome ⟨11, 16, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 19, 2⟩, ⟨9, 16, 19, 4⟩, ⟨11, 15, 19, 2⟩, ⟨11, 14, 19, 4⟩, ⟨11, 16, 18, 2⟩, ⟨11, 16, 17, 4⟩]
  exact AllWinning.cons node_25307 (AllWinning.cons node_25096 (AllWinning.cons node_25317 (AllWinning.cons node_25128 (AllWinning.cons node_25318 (AllWinning.cons node_25132 (AllWinning.nil))))))

theorem node_25480 : Outcome ⟨11, 16, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 19, 2⟩, ⟨9, 16, 19, 4⟩, ⟨8, 16, 19, 6⟩, ⟨7, 16, 19, 8⟩, ⟨11, 15, 19, 2⟩, ⟨11, 14, 19, 4⟩, ⟨11, 13, 19, 6⟩, ⟨11, 12, 19, 8⟩, ⟨11, 16, 18, 2⟩, ⟨11, 16, 17, 4⟩, ⟨11, 16, 16, 6⟩, ⟨11, 16, 15, 8⟩]
  exact AllWinning.cons node_25307 (AllWinning.cons node_25096 (AllWinning.cons node_24860 (AllWinning.cons node_24551 (AllWinning.cons node_25317 (AllWinning.cons node_25128 (AllWinning.cons node_24902 (AllWinning.cons node_24617 (AllWinning.cons node_25318 (AllWinning.cons node_25132 (AllWinning.cons node_24907 (AllWinning.cons node_24625 (AllWinning.nil))))))))))))

theorem node_25481 : Outcome ⟨11, 16, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 16, 19, 2⟩, ⟨9, 16, 19, 4⟩, ⟨8, 16, 19, 6⟩, ⟨7, 16, 19, 8⟩, ⟨6, 16, 19, 10⟩, ⟨5, 16, 19, 12⟩, ⟨11, 15, 19, 2⟩, ⟨11, 14, 19, 4⟩, ⟨11, 13, 19, 6⟩, ⟨11, 12, 19, 8⟩, ⟨11, 11, 19, 10⟩, ⟨11, 10, 19, 12⟩, ⟨11, 16, 18, 2⟩, ⟨11, 16, 17, 4⟩, ⟨11, 16, 16, 6⟩, ⟨11, 16, 15, 8⟩, ⟨11, 16, 14, 10⟩, ⟨11, 16, 13, 12⟩]
  exact AllWinning.cons node_25307 (AllWinning.cons node_25096 (AllWinning.cons node_24860 (AllWinning.cons node_24551 (AllWinning.cons node_24263 (AllWinning.cons node_23842 (AllWinning.cons node_25317 (AllWinning.cons node_25128 (AllWinning.cons node_24902 (AllWinning.cons node_24617 (AllWinning.cons node_24333 (AllWinning.cons node_23962 (AllWinning.cons node_25318 (AllWinning.cons node_25132 (AllWinning.cons node_24907 (AllWinning.cons node_24625 (AllWinning.cons node_24342 (AllWinning.cons node_23976 (AllWinning.nil))))))))))))))))))

theorem node_25482 : Outcome ⟨11, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 17, 2⟩) (by decide) node_25321

theorem node_25483 : Outcome ⟨11, 17, 18, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 17, 2⟩) (by decide) node_25321

theorem node_25484 : Outcome ⟨11, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 17, 2⟩) (by decide) node_25321

theorem node_25485 : Outcome ⟨11, 18, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 17, 2⟩) (by decide) node_25321

theorem node_25486 : Outcome ⟨11, 19, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 16, 2⟩, ⟨9, 19, 16, 4⟩, ⟨11, 18, 16, 2⟩, ⟨11, 17, 16, 4⟩, ⟨11, 19, 15, 2⟩, ⟨11, 19, 14, 4⟩]
  exact AllWinning.cons node_25311 (AllWinning.cons node_25102 (AllWinning.cons node_25324 (AllWinning.cons node_25136 (AllWinning.cons node_25327 (AllWinning.cons node_25141 (AllWinning.nil))))))

theorem node_25487 : Outcome ⟨11, 19, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 16, 2⟩, ⟨9, 19, 16, 4⟩, ⟨8, 19, 16, 6⟩, ⟨7, 19, 16, 8⟩, ⟨11, 18, 16, 2⟩, ⟨11, 17, 16, 4⟩, ⟨11, 16, 16, 6⟩, ⟨11, 15, 16, 8⟩, ⟨11, 19, 15, 2⟩, ⟨11, 19, 14, 4⟩, ⟨11, 19, 13, 6⟩, ⟨11, 19, 12, 8⟩]
  exact AllWinning.cons node_25311 (AllWinning.cons node_25102 (AllWinning.cons node_24865 (AllWinning.cons node_24556 (AllWinning.cons node_25324 (AllWinning.cons node_25136 (AllWinning.cons node_24907 (AllWinning.cons node_24623 (AllWinning.cons node_25327 (AllWinning.cons node_25141 (AllWinning.cons node_24910 (AllWinning.cons node_24631 (AllWinning.nil))))))))))))

theorem node_25488 : Outcome ⟨11, 19, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 16, 2⟩, ⟨9, 19, 16, 4⟩, ⟨8, 19, 16, 6⟩, ⟨7, 19, 16, 8⟩, ⟨6, 19, 16, 10⟩, ⟨5, 19, 16, 12⟩, ⟨11, 18, 16, 2⟩, ⟨11, 17, 16, 4⟩, ⟨11, 16, 16, 6⟩, ⟨11, 15, 16, 8⟩, ⟨11, 14, 16, 10⟩, ⟨11, 13, 16, 12⟩, ⟨11, 19, 15, 2⟩, ⟨11, 19, 14, 4⟩, ⟨11, 19, 13, 6⟩, ⟨11, 19, 12, 8⟩, ⟨11, 19, 11, 10⟩, ⟨11, 19, 10, 12⟩]
  exact AllWinning.cons node_25311 (AllWinning.cons node_25102 (AllWinning.cons node_24865 (AllWinning.cons node_24556 (AllWinning.cons node_24267 (AllWinning.cons node_23846 (AllWinning.cons node_25324 (AllWinning.cons node_25136 (AllWinning.cons node_24907 (AllWinning.cons node_24623 (AllWinning.cons node_24338 (AllWinning.cons node_23968 (AllWinning.cons node_25327 (AllWinning.cons node_25141 (AllWinning.cons node_24910 (AllWinning.cons node_24631 (AllWinning.cons node_24346 (AllWinning.cons node_23981 (AllWinning.nil))))))))))))))))))

theorem node_25489 : Outcome ⟨11, 20, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 20, 15, 2⟩, ⟨9, 20, 15, 4⟩, ⟨11, 19, 15, 2⟩, ⟨11, 18, 15, 4⟩, ⟨11, 20, 14, 2⟩, ⟨11, 20, 13, 4⟩]
  exact AllWinning.cons node_25313 (AllWinning.cons node_25103 (AllWinning.cons node_25327 (AllWinning.cons node_25139 (AllWinning.cons node_25328 (AllWinning.cons node_25142 (AllWinning.nil))))))

theorem node_25490 : Outcome ⟨11, 20, 15, 4⟩ true :=
  Outcome.win (q := ⟨11, 20, 11, 8⟩) (by decide) node_24633

theorem node_25491 : Outcome ⟨12, 14, 20, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 18, 4⟩) (by decide) node_25147

theorem node_25492 : Outcome ⟨12, 15, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 15, 19, 2⟩, ⟨10, 15, 19, 4⟩, ⟨12, 14, 19, 2⟩, ⟨12, 13, 19, 4⟩, ⟨12, 15, 18, 2⟩, ⟨12, 15, 17, 4⟩]
  exact AllWinning.cons node_25317 (AllWinning.cons node_25109 (AllWinning.cons node_25331 (AllWinning.cons node_25145 (AllWinning.cons node_25332 (AllWinning.cons node_25150 (AllWinning.nil))))))

theorem node_25493 : Outcome ⟨12, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 18, 4⟩) (by decide) node_25147

theorem node_25494 : Outcome ⟨12, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 6⟩) (by decide) node_24922

theorem node_25495 : Outcome ⟨12, 16, 18, 6⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 6⟩) (by decide) node_24922

theorem node_25496 : Outcome ⟨12, 17, 17, 2⟩ true :=
  Outcome.win (q := ⟨11, 17, 17, 2⟩) (by decide) node_25321

theorem node_25497 : Outcome ⟨12, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 14, 4⟩) (by decide) node_25156

theorem node_25498 : Outcome ⟨12, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 6⟩) (by decide) node_24919

theorem node_25499 : Outcome ⟨12, 18, 16, 6⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 6⟩) (by decide) node_24919

theorem node_25500 : Outcome ⟨12, 19, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 19, 15, 2⟩, ⟨10, 19, 15, 4⟩, ⟨12, 18, 15, 2⟩, ⟨12, 17, 15, 4⟩, ⟨12, 19, 14, 2⟩, ⟨12, 19, 13, 4⟩]
  exact AllWinning.cons node_25327 (AllWinning.cons node_25122 (AllWinning.cons node_25339 (AllWinning.cons node_25154 (AllWinning.cons node_25342 (AllWinning.cons node_25158 (AllWinning.nil))))))

theorem node_25501 : Outcome ⟨12, 20, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 14, 4⟩) (by decide) node_25156

theorem node_25502 : Outcome ⟨13, 13, 20, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 18, 4⟩) (by decide) node_25164

theorem node_25503 : Outcome ⟨13, 14, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 14, 19, 2⟩, ⟨11, 14, 19, 4⟩, ⟨13, 13, 19, 2⟩, ⟨13, 12, 19, 4⟩, ⟨13, 14, 18, 2⟩, ⟨13, 14, 17, 4⟩]
  exact AllWinning.cons node_25331 (AllWinning.cons node_25128 (AllWinning.cons node_25345 (AllWinning.cons node_25162 (AllWinning.cons node_25347 (AllWinning.cons node_25167 (AllWinning.nil))))))

theorem node_25504 : Outcome ⟨13, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 18, 4⟩) (by decide) node_25164

theorem node_25505 : Outcome ⟨13, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 14, 8⟩) (by decide) node_24672

theorem node_25506 : Outcome ⟨13, 15, 18, 6⟩ true :=
  Outcome.win (q := ⟨13, 15, 14, 8⟩) (by decide) node_24672

theorem node_25507 : Outcome ⟨13, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 17, 2⟩) (by decide) node_25350

theorem node_25508 : Outcome ⟨13, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 2⟩) (by decide) node_25353

theorem node_25509 : Outcome ⟨13, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 13, 4⟩) (by decide) node_25177

theorem node_25510 : Outcome ⟨13, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 8⟩) (by decide) node_24667

theorem node_25511 : Outcome ⟨13, 18, 15, 6⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 8⟩) (by decide) node_24667

theorem node_25512 : Outcome ⟨13, 19, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 19, 14, 2⟩, ⟨11, 19, 14, 4⟩, ⟨13, 18, 14, 2⟩, ⟨13, 17, 14, 4⟩, ⟨13, 19, 13, 2⟩, ⟨13, 19, 12, 4⟩]
  exact AllWinning.cons node_25342 (AllWinning.cons node_25141 (AllWinning.cons node_25360 (AllWinning.cons node_25174 (AllWinning.cons node_25363 (AllWinning.cons node_25179 (AllWinning.nil))))))

theorem node_25513 : Outcome ⟨13, 20, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 18, 13, 4⟩) (by decide) node_25177

theorem node_25514 : Outcome ⟨14, 13, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 13, 19, 2⟩, ⟨12, 13, 19, 4⟩, ⟨14, 12, 19, 2⟩, ⟨14, 11, 19, 4⟩, ⟨14, 13, 18, 2⟩, ⟨14, 13, 17, 4⟩]
  exact AllWinning.cons node_25345 (AllWinning.cons node_25145 (AllWinning.cons node_25367 (AllWinning.cons node_25182 (AllWinning.cons node_25368 (AllWinning.cons node_25187 (AllWinning.nil))))))

theorem node_25515 : Outcome ⟨14, 13, 19, 10⟩ true :=
  Outcome.win (q := ⟨14, 4, 19, 18⟩) (by decide) node_22745

theorem node_25516 : Outcome ⟨14, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 18, 4⟩) (by decide) node_25147

theorem node_25517 : Outcome ⟨14, 15, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 17, 2⟩) (by decide) node_25350

theorem node_25518 : Outcome ⟨14, 16, 16, 2⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 2⟩) (by decide) node_25353

theorem node_25519 : Outcome ⟨14, 17, 15, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 15, 2⟩) (by decide) node_25357

theorem node_25520 : Outcome ⟨14, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 14, 4⟩) (by decide) node_25156

theorem node_25521 : Outcome ⟨14, 19, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 19, 13, 2⟩, ⟨12, 19, 13, 4⟩, ⟨14, 18, 13, 2⟩, ⟨14, 17, 13, 4⟩, ⟨14, 19, 12, 2⟩, ⟨14, 19, 11, 4⟩]
  exact AllWinning.cons node_25363 (AllWinning.cons node_25158 (AllWinning.cons node_25376 (AllWinning.cons node_25195 (AllWinning.cons node_25378 (AllWinning.cons node_25200 (AllWinning.nil))))))

theorem node_25522 : Outcome ⟨14, 19, 13, 10⟩ true :=
  Outcome.win (q := ⟨14, 19, 4, 18⟩) (by decide) node_22795

theorem node_25523 : Outcome ⟨15, 11, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 20, 2⟩, ⟨13, 11, 20, 4⟩, ⟨15, 10, 20, 2⟩, ⟨15, 9, 20, 4⟩, ⟨15, 11, 19, 2⟩, ⟨15, 11, 18, 4⟩]
  exact AllWinning.cons node_25366 (AllWinning.cons node_25160 (AllWinning.cons node_25379 (AllWinning.cons node_25201 (AllWinning.cons node_25381 (AllWinning.cons node_25204 (AllWinning.nil))))))

theorem node_25524 : Outcome ⟨15, 11, 20, 4⟩ true :=
  Outcome.win (q := ⟨11, 11, 20, 8⟩) (by decide) node_24615

theorem node_25525 : Outcome ⟨15, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 18, 4⟩) (by decide) node_25164

theorem node_25526 : Outcome ⟨15, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 8⟩) (by decide) node_24726

theorem node_25527 : Outcome ⟨15, 13, 18, 6⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 8⟩) (by decide) node_24726

theorem node_25528 : Outcome ⟨15, 14, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 17, 2⟩) (by decide) node_25370

theorem node_25529 : Outcome ⟨15, 15, 16, 6⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 6⟩) (by decide) node_24919

theorem node_25530 : Outcome ⟨15, 16, 15, 6⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 6⟩) (by decide) node_24922

theorem node_25531 : Outcome ⟨15, 17, 14, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 14, 2⟩) (by decide) node_25374

theorem node_25532 : Outcome ⟨15, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 13, 4⟩) (by decide) node_25177

theorem node_25533 : Outcome ⟨15, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 8⟩) (by decide) node_24730

theorem node_25534 : Outcome ⟨15, 18, 13, 6⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 8⟩) (by decide) node_24730

theorem node_25535 : Outcome ⟨15, 19, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 19, 12, 2⟩, ⟨13, 19, 12, 4⟩, ⟨15, 18, 12, 2⟩, ⟨15, 17, 12, 4⟩, ⟨15, 19, 11, 2⟩, ⟨15, 19, 10, 4⟩]
  exact AllWinning.cons node_25378 (AllWinning.cons node_25179 (AllWinning.cons node_25395 (AllWinning.cons node_25216 (AllWinning.cons node_25398 (AllWinning.cons node_25219 (AllWinning.nil))))))

theorem node_25536 : Outcome ⟨15, 20, 11, 4⟩ true :=
  Outcome.win (q := ⟨11, 20, 11, 8⟩) (by decide) node_24633

theorem node_25537 : Outcome ⟨16, 11, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 11, 19, 2⟩, ⟨14, 11, 19, 4⟩, ⟨16, 10, 19, 2⟩, ⟨16, 9, 19, 4⟩, ⟨16, 11, 18, 2⟩, ⟨16, 11, 17, 4⟩]
  exact AllWinning.cons node_25381 (AllWinning.cons node_25182 (AllWinning.cons node_25400 (AllWinning.cons node_25221 (AllWinning.cons node_25401 (AllWinning.cons node_25225 (AllWinning.nil))))))

theorem node_25538 : Outcome ⟨16, 11, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 11, 19, 2⟩, ⟨14, 11, 19, 4⟩, ⟨13, 11, 19, 6⟩, ⟨12, 11, 19, 8⟩, ⟨16, 10, 19, 2⟩, ⟨16, 9, 19, 4⟩, ⟨16, 8, 19, 6⟩, ⟨16, 7, 19, 8⟩, ⟨16, 11, 18, 2⟩, ⟨16, 11, 17, 4⟩, ⟨16, 11, 16, 6⟩, ⟨16, 11, 15, 8⟩]
  exact AllWinning.cons node_25381 (AllWinning.cons node_25182 (AllWinning.cons node_24933 (AllWinning.cons node_24636 (AllWinning.cons node_25400 (AllWinning.cons node_25221 (AllWinning.cons node_24992 (AllWinning.cons node_24744 (AllWinning.cons node_25401 (AllWinning.cons node_25225 (AllWinning.cons node_24997 (AllWinning.cons node_24751 (AllWinning.nil))))))))))))

theorem node_25539 : Outcome ⟨16, 11, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 11, 19, 2⟩, ⟨14, 11, 19, 4⟩, ⟨13, 11, 19, 6⟩, ⟨12, 11, 19, 8⟩, ⟨11, 11, 19, 10⟩, ⟨10, 11, 19, 12⟩, ⟨16, 10, 19, 2⟩, ⟨16, 9, 19, 4⟩, ⟨16, 8, 19, 6⟩, ⟨16, 7, 19, 8⟩, ⟨16, 6, 19, 10⟩, ⟨16, 5, 19, 12⟩, ⟨16, 11, 18, 2⟩, ⟨16, 11, 17, 4⟩, ⟨16, 11, 16, 6⟩, ⟨16, 11, 15, 8⟩, ⟨16, 11, 14, 10⟩, ⟨16, 11, 13, 12⟩]
  exact AllWinning.cons node_25381 (AllWinning.cons node_25182 (AllWinning.cons node_24933 (AllWinning.cons node_24636 (AllWinning.cons node_24333 (AllWinning.cons node_23931 (AllWinning.cons node_25400 (AllWinning.cons node_25221 (AllWinning.cons node_24992 (AllWinning.cons node_24744 (AllWinning.cons node_24448 (AllWinning.cons node_24117 (AllWinning.cons node_25401 (AllWinning.cons node_25225 (AllWinning.cons node_24997 (AllWinning.cons node_24751 (AllWinning.cons node_24457 (AllWinning.cons node_24134 (AllWinning.nil))))))))))))))))))

theorem node_25540 : Outcome ⟨16, 12, 18, 2⟩ true :=
  Outcome.win (q := ⟨14, 12, 18, 4⟩) (by decide) node_25183

theorem node_25541 : Outcome ⟨16, 12, 18, 6⟩ true :=
  Outcome.win (q := ⟨16, 12, 15, 6⟩) (by decide) node_24999

theorem node_25542 : Outcome ⟨16, 13, 17, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 17, 2⟩) (by decide) node_25384

theorem node_25543 : Outcome ⟨16, 14, 16, 2⟩ true :=
  Outcome.win (q := ⟨16, 13, 16, 2⟩) (by decide) node_25404

theorem node_25544 : Outcome ⟨16, 15, 15, 6⟩ true :=
  Outcome.win (q := ⟨16, 12, 15, 6⟩) (by decide) node_24999

theorem node_25545 : Outcome ⟨16, 16, 14, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 13, 2⟩) (by decide) node_25412

theorem node_25546 : Outcome ⟨16, 17, 13, 2⟩ true :=
  Outcome.win (q := ⟨15, 17, 13, 2⟩) (by decide) node_25392

theorem node_25547 : Outcome ⟨16, 18, 12, 2⟩ true :=
  Outcome.win (q := ⟨14, 18, 12, 4⟩) (by decide) node_25197

theorem node_25548 : Outcome ⟨16, 18, 12, 6⟩ true :=
  Outcome.win (q := ⟨16, 15, 12, 6⟩) (by decide) node_25003

theorem node_25549 : Outcome ⟨16, 19, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 19, 11, 2⟩, ⟨14, 19, 11, 4⟩, ⟨16, 18, 11, 2⟩, ⟨16, 17, 11, 4⟩, ⟨16, 19, 10, 2⟩, ⟨16, 19, 9, 4⟩]
  exact AllWinning.cons node_25398 (AllWinning.cons node_25200 (AllWinning.cons node_25417 (AllWinning.cons node_25234 (AllWinning.cons node_25419 (AllWinning.cons node_25237 (AllWinning.nil))))))

theorem node_25550 : Outcome ⟨16, 19, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 19, 11, 2⟩, ⟨14, 19, 11, 4⟩, ⟨13, 19, 11, 6⟩, ⟨12, 19, 11, 8⟩, ⟨16, 18, 11, 2⟩, ⟨16, 17, 11, 4⟩, ⟨16, 16, 11, 6⟩, ⟨16, 15, 11, 8⟩, ⟨16, 19, 10, 2⟩, ⟨16, 19, 9, 4⟩, ⟨16, 19, 8, 6⟩, ⟨16, 19, 7, 8⟩]
  exact AllWinning.cons node_25398 (AllWinning.cons node_25200 (AllWinning.cons node_24950 (AllWinning.cons node_24654 (AllWinning.cons node_25417 (AllWinning.cons node_25234 (AllWinning.cons node_25006 (AllWinning.cons node_24760 (AllWinning.cons node_25419 (AllWinning.cons node_25237 (AllWinning.cons node_25010 (AllWinning.cons node_24767 (AllWinning.nil))))))))))))

theorem node_25551 : Outcome ⟨16, 19, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 19, 11, 2⟩, ⟨14, 19, 11, 4⟩, ⟨13, 19, 11, 6⟩, ⟨12, 19, 11, 8⟩, ⟨11, 19, 11, 10⟩, ⟨10, 19, 11, 12⟩, ⟨16, 18, 11, 2⟩, ⟨16, 17, 11, 4⟩, ⟨16, 16, 11, 6⟩, ⟨16, 15, 11, 8⟩, ⟨16, 14, 11, 10⟩, ⟨16, 13, 11, 12⟩, ⟨16, 19, 10, 2⟩, ⟨16, 19, 9, 4⟩, ⟨16, 19, 8, 6⟩, ⟨16, 19, 7, 8⟩, ⟨16, 19, 6, 10⟩, ⟨16, 19, 5, 12⟩]
  exact AllWinning.cons node_25398 (AllWinning.cons node_25200 (AllWinning.cons node_24950 (AllWinning.cons node_24654 (AllWinning.cons node_24346 (AllWinning.cons node_23957 (AllWinning.cons node_25417 (AllWinning.cons node_25234 (AllWinning.cons node_25006 (AllWinning.cons node_24760 (AllWinning.cons node_24465 (AllWinning.cons node_24141 (AllWinning.cons node_25419 (AllWinning.cons node_25237 (AllWinning.cons node_25010 (AllWinning.cons node_24767 (AllWinning.cons node_24473 (AllWinning.cons node_24156 (AllWinning.nil))))))))))))))))))

theorem node_25552 : Outcome ⟨17, 11, 18, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 17, 2⟩) (by decide) node_25421

theorem node_25553 : Outcome ⟨17, 12, 17, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 17, 2⟩) (by decide) node_25421

theorem node_25554 : Outcome ⟨17, 13, 16, 2⟩ true :=
  Outcome.win (q := ⟨16, 13, 16, 2⟩) (by decide) node_25404

theorem node_25555 : Outcome ⟨17, 14, 15, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 15, 2⟩) (by decide) node_25424

theorem node_25556 : Outcome ⟨17, 15, 14, 2⟩ true :=
  Outcome.win (q := ⟨17, 14, 14, 2⟩) (by decide) node_25426

theorem node_25557 : Outcome ⟨17, 16, 13, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 13, 2⟩) (by decide) node_25412

theorem node_25558 : Outcome ⟨17, 17, 12, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 11, 2⟩) (by decide) node_25430

theorem node_25559 : Outcome ⟨17, 18, 11, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 11, 2⟩) (by decide) node_25430

theorem node_25560 : Outcome ⟨18, 13, 15, 2⟩ true :=
  Outcome.win (q := ⟨18, 13, 13, 4⟩) (by decide) node_25264

theorem node_25561 : Outcome ⟨18, 14, 14, 2⟩ true :=
  Outcome.win (q := ⟨18, 12, 14, 4⟩) (by decide) node_25261

theorem node_25562 : Outcome ⟨19, 8, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 8, 19, 2⟩, ⟨17, 8, 19, 4⟩, ⟨19, 7, 19, 2⟩, ⟨19, 6, 19, 4⟩, ⟨19, 8, 18, 2⟩, ⟨19, 8, 17, 4⟩]
  exact AllWinning.cons node_25433 (AllWinning.cons node_25238 (AllWinning.cons node_25441 (AllWinning.cons node_25269 (AllWinning.cons node_25443 (AllWinning.cons node_25270 (AllWinning.nil))))))

theorem node_25563 : Outcome ⟨19, 8, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 8, 19, 2⟩, ⟨17, 8, 19, 4⟩, ⟨16, 8, 19, 6⟩, ⟨15, 8, 19, 8⟩, ⟨19, 7, 19, 2⟩, ⟨19, 6, 19, 4⟩, ⟨19, 5, 19, 6⟩, ⟨19, 4, 19, 8⟩, ⟨19, 8, 18, 2⟩, ⟨19, 8, 17, 4⟩, ⟨19, 8, 16, 6⟩, ⟨19, 8, 15, 8⟩]
  exact AllWinning.cons node_25433 (AllWinning.cons node_25238 (AllWinning.cons node_24992 (AllWinning.cons node_24714 (AllWinning.cons node_25441 (AllWinning.cons node_25269 (AllWinning.cons node_25048 (AllWinning.cons node_24805 (AllWinning.cons node_25443 (AllWinning.cons node_25270 (AllWinning.cons node_25049 (AllWinning.cons node_24809 (AllWinning.nil))))))))))))

theorem node_25564 : Outcome ⟨19, 8, 19, 10⟩ true :=
  Outcome.win (q := ⟨19, 0, 19, 16⟩) (by decide) node_23410

theorem node_25565 : Outcome ⟨19, 11, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 11, 16, 2⟩, ⟨17, 11, 16, 4⟩, ⟨19, 10, 16, 2⟩, ⟨19, 9, 16, 4⟩, ⟨19, 11, 15, 2⟩, ⟨19, 11, 14, 4⟩]
  exact AllWinning.cons node_25434 (AllWinning.cons node_25242 (AllWinning.cons node_25444 (AllWinning.cons node_25271 (AllWinning.cons node_25445 (AllWinning.cons node_25274 (AllWinning.nil))))))

theorem node_25566 : Outcome ⟨19, 11, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 11, 16, 2⟩, ⟨17, 11, 16, 4⟩, ⟨16, 11, 16, 6⟩, ⟨15, 11, 16, 8⟩, ⟨19, 10, 16, 2⟩, ⟨19, 9, 16, 4⟩, ⟨19, 8, 16, 6⟩, ⟨19, 7, 16, 8⟩, ⟨19, 11, 15, 2⟩, ⟨19, 11, 14, 4⟩, ⟨19, 11, 13, 6⟩, ⟨19, 11, 12, 8⟩]
  exact AllWinning.cons node_25434 (AllWinning.cons node_25242 (AllWinning.cons node_24997 (AllWinning.cons node_24720 (AllWinning.cons node_25444 (AllWinning.cons node_25271 (AllWinning.cons node_25049 (AllWinning.cons node_24807 (AllWinning.cons node_25445 (AllWinning.cons node_25274 (AllWinning.cons node_25052 (AllWinning.cons node_24813 (AllWinning.nil))))))))))))

theorem node_25567 : Outcome ⟨19, 11, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 11, 16, 2⟩, ⟨17, 11, 16, 4⟩, ⟨16, 11, 16, 6⟩, ⟨15, 11, 16, 8⟩, ⟨14, 11, 16, 10⟩, ⟨13, 11, 16, 12⟩, ⟨19, 10, 16, 2⟩, ⟨19, 9, 16, 4⟩, ⟨19, 8, 16, 6⟩, ⟨19, 7, 16, 8⟩, ⟨19, 6, 16, 10⟩, ⟨19, 5, 16, 12⟩, ⟨19, 11, 15, 2⟩, ⟨19, 11, 14, 4⟩, ⟨19, 11, 13, 6⟩, ⟨19, 11, 12, 8⟩, ⟨19, 11, 11, 10⟩, ⟨19, 11, 10, 12⟩]
  exact AllWinning.cons node_25434 (AllWinning.cons node_25242 (AllWinning.cons node_24997 (AllWinning.cons node_24720 (AllWinning.cons node_24399 (AllWinning.cons node_24022 (AllWinning.cons node_25444 (AllWinning.cons node_25271 (AllWinning.cons node_25049 (AllWinning.cons node_24807 (AllWinning.cons node_24514 (AllWinning.cons node_24204 (AllWinning.cons node_25445 (AllWinning.cons node_25274 (AllWinning.cons node_25052 (AllWinning.cons node_24813 (AllWinning.cons node_24518 (AllWinning.cons node_24216 (AllWinning.nil))))))))))))))))))

theorem node_25568 : Outcome ⟨19, 12, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 12, 15, 2⟩, ⟨17, 12, 15, 4⟩, ⟨19, 11, 15, 2⟩, ⟨19, 10, 15, 4⟩, ⟨19, 12, 14, 2⟩, ⟨19, 12, 13, 4⟩]
  exact AllWinning.cons node_25435 (AllWinning.cons node_25245 (AllWinning.cons node_25445 (AllWinning.cons node_25273 (AllWinning.cons node_25446 (AllWinning.cons node_25275 (AllWinning.nil))))))

theorem node_25569 : Outcome ⟨19, 13, 14, 10⟩ true :=
  Outcome.win (q := ⟨19, 4, 14, 18⟩) (by decide) node_22931

theorem node_25570 : Outcome ⟨19, 14, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 14, 13, 2⟩, ⟨17, 14, 13, 4⟩, ⟨19, 13, 13, 2⟩, ⟨19, 12, 13, 4⟩, ⟨19, 14, 12, 2⟩, ⟨19, 14, 11, 4⟩]
  exact AllWinning.cons node_25437 (AllWinning.cons node_25249 (AllWinning.cons node_25447 (AllWinning.cons node_25275 (AllWinning.cons node_25449 (AllWinning.cons node_25276 (AllWinning.nil))))))

theorem node_25571 : Outcome ⟨19, 14, 13, 10⟩ true :=
  Outcome.win (q := ⟨19, 14, 4, 18⟩) (by decide) node_22941

theorem node_25572 : Outcome ⟨19, 16, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 16, 11, 2⟩, ⟨17, 16, 11, 4⟩, ⟨19, 15, 11, 2⟩, ⟨19, 14, 11, 4⟩, ⟨19, 16, 10, 2⟩, ⟨19, 16, 9, 4⟩]
  exact AllWinning.cons node_25439 (AllWinning.cons node_25252 (AllWinning.cons node_25450 (AllWinning.cons node_25276 (AllWinning.cons node_25451 (AllWinning.cons node_25278 (AllWinning.nil))))))

theorem node_25573 : Outcome ⟨19, 16, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 16, 11, 2⟩, ⟨17, 16, 11, 4⟩, ⟨16, 16, 11, 6⟩, ⟨15, 16, 11, 8⟩, ⟨19, 15, 11, 2⟩, ⟨19, 14, 11, 4⟩, ⟨19, 13, 11, 6⟩, ⟨19, 12, 11, 8⟩, ⟨19, 16, 10, 2⟩, ⟨19, 16, 9, 4⟩, ⟨19, 16, 8, 6⟩, ⟨19, 16, 7, 8⟩]
  exact AllWinning.cons node_25439 (AllWinning.cons node_25252 (AllWinning.cons node_25006 (AllWinning.cons node_24735 (AllWinning.cons node_25450 (AllWinning.cons node_25276 (AllWinning.cons node_25054 (AllWinning.cons node_24815 (AllWinning.cons node_25451 (AllWinning.cons node_25278 (AllWinning.cons node_25057 (AllWinning.cons node_24820 (AllWinning.nil))))))))))))

theorem node_25574 : Outcome ⟨19, 16, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 16, 11, 2⟩, ⟨17, 16, 11, 4⟩, ⟨16, 16, 11, 6⟩, ⟨15, 16, 11, 8⟩, ⟨14, 16, 11, 10⟩, ⟨13, 16, 11, 12⟩, ⟨19, 15, 11, 2⟩, ⟨19, 14, 11, 4⟩, ⟨19, 13, 11, 6⟩, ⟨19, 12, 11, 8⟩, ⟨19, 11, 11, 10⟩, ⟨19, 10, 11, 12⟩, ⟨19, 16, 10, 2⟩, ⟨19, 16, 9, 4⟩, ⟨19, 16, 8, 6⟩, ⟨19, 16, 7, 8⟩, ⟨19, 16, 6, 10⟩, ⟨19, 16, 5, 12⟩]
  exact AllWinning.cons node_25439 (AllWinning.cons node_25252 (AllWinning.cons node_25006 (AllWinning.cons node_24735 (AllWinning.cons node_24410 (AllWinning.cons node_24038 (AllWinning.cons node_25450 (AllWinning.cons node_25276 (AllWinning.cons node_25054 (AllWinning.cons node_24815 (AllWinning.cons node_24518 (AllWinning.cons node_24214 (AllWinning.cons node_25451 (AllWinning.cons node_25278 (AllWinning.cons node_25057 (AllWinning.cons node_24820 (AllWinning.cons node_24522 (AllWinning.cons node_24225 (AllWinning.nil))))))))))))))))))

theorem node_25575 : Outcome ⟨19, 19, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 8, 2⟩, ⟨17, 19, 8, 4⟩, ⟨19, 18, 8, 2⟩, ⟨19, 17, 8, 4⟩, ⟨19, 19, 7, 2⟩, ⟨19, 19, 6, 4⟩]
  exact AllWinning.cons node_25440 (AllWinning.cons node_25256 (AllWinning.cons node_25452 (AllWinning.cons node_25279 (AllWinning.cons node_25453 (AllWinning.cons node_25280 (AllWinning.nil))))))

theorem node_25576 : Outcome ⟨19, 19, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 8, 2⟩, ⟨17, 19, 8, 4⟩, ⟨16, 19, 8, 6⟩, ⟨15, 19, 8, 8⟩, ⟨19, 18, 8, 2⟩, ⟨19, 17, 8, 4⟩, ⟨19, 16, 8, 6⟩, ⟨19, 15, 8, 8⟩, ⟨19, 19, 7, 2⟩, ⟨19, 19, 6, 4⟩, ⟨19, 19, 5, 6⟩, ⟨19, 19, 4, 8⟩]
  exact AllWinning.cons node_25440 (AllWinning.cons node_25256 (AllWinning.cons node_25010 (AllWinning.cons node_24741 (AllWinning.cons node_25452 (AllWinning.cons node_25279 (AllWinning.cons node_25057 (AllWinning.cons node_24819 (AllWinning.cons node_25453 (AllWinning.cons node_25280 (AllWinning.cons node_25060 (AllWinning.cons node_24823 (AllWinning.nil))))))))))))

theorem node_25577 : Outcome ⟨19, 19, 8, 10⟩ true :=
  Outcome.win (q := ⟨19, 19, 0, 16⟩) (by decide) node_23422

theorem node_25578 : Outcome ⟨7, 20, 20, 2⟩ true :=
  Outcome.win (q := ⟨5, 20, 20, 4⟩) (by decide) node_25282

theorem node_25579 : Outcome ⟨8, 19, 20, 2⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 2⟩) (by decide) node_25458

theorem node_25580 : Outcome ⟨8, 19, 20, 8⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 2⟩) (by decide) node_25458

theorem node_25581 : Outcome ⟨8, 20, 19, 2⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 2⟩) (by decide) node_25458

theorem node_25582 : Outcome ⟨8, 20, 19, 8⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 2⟩) (by decide) node_25458

theorem node_25583 : Outcome ⟨9, 18, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 18, 20, 2⟩, ⟨7, 18, 20, 4⟩, ⟨9, 17, 20, 2⟩, ⟨9, 16, 20, 4⟩, ⟨9, 18, 19, 2⟩, ⟨9, 18, 18, 4⟩]
  exact AllWinning.cons node_25456 (AllWinning.cons node_25284 (AllWinning.cons node_25463 (AllWinning.cons node_25296 (AllWinning.cons node_25465 (AllWinning.cons node_25299 (AllWinning.nil))))))

theorem node_25584 : Outcome ⟨9, 18, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 18, 20, 2⟩, ⟨7, 18, 20, 4⟩, ⟨6, 18, 20, 6⟩, ⟨5, 18, 20, 8⟩, ⟨9, 17, 20, 2⟩, ⟨9, 16, 20, 4⟩, ⟨9, 15, 20, 6⟩, ⟨9, 14, 20, 8⟩, ⟨9, 18, 19, 2⟩, ⟨9, 18, 18, 4⟩, ⟨9, 18, 17, 6⟩, ⟨9, 18, 16, 8⟩]
  exact AllWinning.cons node_25456 (AllWinning.cons node_25284 (AllWinning.cons node_25065 (AllWinning.cons node_24830 (AllWinning.cons node_25463 (AllWinning.cons node_25296 (AllWinning.cons node_25093 (AllWinning.cons node_24869 (AllWinning.cons node_25465 (AllWinning.cons node_25299 (AllWinning.cons node_25100 (AllWinning.cons node_24878 (AllWinning.nil))))))))))))

theorem node_25585 : Outcome ⟨9, 18, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 18, 20, 2⟩, ⟨7, 18, 20, 4⟩, ⟨6, 18, 20, 6⟩, ⟨5, 18, 20, 8⟩, ⟨4, 18, 20, 10⟩, ⟨3, 18, 20, 12⟩, ⟨9, 17, 20, 2⟩, ⟨9, 16, 20, 4⟩, ⟨9, 15, 20, 6⟩, ⟨9, 14, 20, 8⟩, ⟨9, 13, 20, 10⟩, ⟨9, 12, 20, 12⟩, ⟨9, 18, 19, 2⟩, ⟨9, 18, 18, 4⟩, ⟨9, 18, 17, 6⟩, ⟨9, 18, 16, 8⟩, ⟨9, 18, 15, 10⟩, ⟨9, 18, 14, 12⟩]
  exact AllWinning.cons node_25456 (AllWinning.cons node_25284 (AllWinning.cons node_25065 (AllWinning.cons node_24830 (AllWinning.cons node_24531 (AllWinning.cons node_24232 (AllWinning.cons node_25463 (AllWinning.cons node_25296 (AllWinning.cons node_25093 (AllWinning.cons node_24869 (AllWinning.cons node_24575 (AllWinning.cons node_24305 (AllWinning.cons node_25465 (AllWinning.cons node_25299 (AllWinning.cons node_25100 (AllWinning.cons node_24878 (AllWinning.cons node_24595 (AllWinning.cons node_24317 (AllWinning.nil))))))))))))))))))

theorem node_25586 : Outcome ⟨9, 18, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 18, 20, 2⟩, ⟨7, 18, 20, 4⟩, ⟨6, 18, 20, 6⟩, ⟨5, 18, 20, 8⟩, ⟨4, 18, 20, 10⟩, ⟨3, 18, 20, 12⟩, ⟨2, 18, 20, 14⟩, ⟨1, 18, 20, 16⟩, ⟨9, 17, 20, 2⟩, ⟨9, 16, 20, 4⟩, ⟨9, 15, 20, 6⟩, ⟨9, 14, 20, 8⟩, ⟨9, 13, 20, 10⟩, ⟨9, 12, 20, 12⟩, ⟨9, 11, 20, 14⟩, ⟨9, 10, 20, 16⟩, ⟨9, 18, 19, 2⟩, ⟨9, 18, 18, 4⟩, ⟨9, 18, 17, 6⟩, ⟨9, 18, 16, 8⟩, ⟨9, 18, 15, 10⟩, ⟨9, 18, 14, 12⟩, ⟨9, 18, 13, 14⟩, ⟨9, 18, 12, 16⟩]
  exact AllWinning.cons node_25456 (AllWinning.cons node_25284 (AllWinning.cons node_25065 (AllWinning.cons node_24830 (AllWinning.cons node_24531 (AllWinning.cons node_24232 (AllWinning.cons node_23815 (AllWinning.cons node_23426 (AllWinning.cons node_25463 (AllWinning.cons node_25296 (AllWinning.cons node_25093 (AllWinning.cons node_24869 (AllWinning.cons node_24575 (AllWinning.cons node_24305 (AllWinning.cons node_23907 (AllWinning.cons node_23527 (AllWinning.cons node_25465 (AllWinning.cons node_25299 (AllWinning.cons node_25100 (AllWinning.cons node_24878 (AllWinning.cons node_24595 (AllWinning.cons node_24317 (AllWinning.cons node_23923 (AllWinning.cons node_23547 (AllWinning.nil))))))))))))))))))))))))

theorem node_25587 : Outcome ⟨9, 19, 19, 4⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 2⟩) (by decide) node_25458

theorem node_25588 : Outcome ⟨9, 19, 19, 8⟩ true :=
  Outcome.win (q := ⟨8, 19, 19, 2⟩) (by decide) node_25458

theorem node_25589 : Outcome ⟨9, 20, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 18, 2⟩, ⟨7, 20, 18, 4⟩, ⟨9, 19, 18, 2⟩, ⟨9, 18, 18, 4⟩, ⟨9, 20, 17, 2⟩, ⟨9, 20, 16, 4⟩]
  exact AllWinning.cons node_25461 (AllWinning.cons node_25286 (AllWinning.cons node_25466 (AllWinning.cons node_25299 (AllWinning.cons node_25467 (AllWinning.cons node_25303 (AllWinning.nil))))))

theorem node_25590 : Outcome ⟨9, 20, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 18, 2⟩, ⟨7, 20, 18, 4⟩, ⟨6, 20, 18, 6⟩, ⟨5, 20, 18, 8⟩, ⟨9, 19, 18, 2⟩, ⟨9, 18, 18, 4⟩, ⟨9, 17, 18, 6⟩, ⟨9, 16, 18, 8⟩, ⟨9, 20, 17, 2⟩, ⟨9, 20, 16, 4⟩, ⟨9, 20, 15, 6⟩, ⟨9, 20, 14, 8⟩]
  exact AllWinning.cons node_25461 (AllWinning.cons node_25286 (AllWinning.cons node_25067 (AllWinning.cons node_24835 (AllWinning.cons node_25466 (AllWinning.cons node_25299 (AllWinning.cons node_25098 (AllWinning.cons node_24873 (AllWinning.cons node_25467 (AllWinning.cons node_25303 (AllWinning.cons node_25104 (AllWinning.cons node_24883 (AllWinning.nil))))))))))))

theorem node_25591 : Outcome ⟨9, 20, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 18, 2⟩, ⟨7, 20, 18, 4⟩, ⟨6, 20, 18, 6⟩, ⟨5, 20, 18, 8⟩, ⟨4, 20, 18, 10⟩, ⟨3, 20, 18, 12⟩, ⟨9, 19, 18, 2⟩, ⟨9, 18, 18, 4⟩, ⟨9, 17, 18, 6⟩, ⟨9, 16, 18, 8⟩, ⟨9, 15, 18, 10⟩, ⟨9, 14, 18, 12⟩, ⟨9, 20, 17, 2⟩, ⟨9, 20, 16, 4⟩, ⟨9, 20, 15, 6⟩, ⟨9, 20, 14, 8⟩, ⟨9, 20, 13, 10⟩, ⟨9, 20, 12, 12⟩]
  exact AllWinning.cons node_25461 (AllWinning.cons node_25286 (AllWinning.cons node_25067 (AllWinning.cons node_24835 (AllWinning.cons node_24535 (AllWinning.cons node_24237 (AllWinning.cons node_25466 (AllWinning.cons node_25299 (AllWinning.cons node_25098 (AllWinning.cons node_24873 (AllWinning.cons node_24581 (AllWinning.cons node_24309 (AllWinning.cons node_25467 (AllWinning.cons node_25303 (AllWinning.cons node_25104 (AllWinning.cons node_24883 (AllWinning.cons node_24600 (AllWinning.cons node_24320 (AllWinning.nil))))))))))))))))))

theorem node_25592 : Outcome ⟨9, 20, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 20, 18, 2⟩, ⟨7, 20, 18, 4⟩, ⟨6, 20, 18, 6⟩, ⟨5, 20, 18, 8⟩, ⟨4, 20, 18, 10⟩, ⟨3, 20, 18, 12⟩, ⟨2, 20, 18, 14⟩, ⟨1, 20, 18, 16⟩, ⟨9, 19, 18, 2⟩, ⟨9, 18, 18, 4⟩, ⟨9, 17, 18, 6⟩, ⟨9, 16, 18, 8⟩, ⟨9, 15, 18, 10⟩, ⟨9, 14, 18, 12⟩, ⟨9, 13, 18, 14⟩, ⟨9, 12, 18, 16⟩, ⟨9, 20, 17, 2⟩, ⟨9, 20, 16, 4⟩, ⟨9, 20, 15, 6⟩, ⟨9, 20, 14, 8⟩, ⟨9, 20, 13, 10⟩, ⟨9, 20, 12, 12⟩, ⟨9, 20, 11, 14⟩, ⟨9, 20, 10, 16⟩]
  exact AllWinning.cons node_25461 (AllWinning.cons node_25286 (AllWinning.cons node_25067 (AllWinning.cons node_24835 (AllWinning.cons node_24535 (AllWinning.cons node_24237 (AllWinning.cons node_23820 (AllWinning.cons node_23430 (AllWinning.cons node_25466 (AllWinning.cons node_25299 (AllWinning.cons node_25098 (AllWinning.cons node_24873 (AllWinning.cons node_24581 (AllWinning.cons node_24309 (AllWinning.cons node_23912 (AllWinning.cons node_23533 (AllWinning.cons node_25467 (AllWinning.cons node_25303 (AllWinning.cons node_25104 (AllWinning.cons node_24883 (AllWinning.cons node_24600 (AllWinning.cons node_24320 (AllWinning.cons node_23927 (AllWinning.cons node_23551 (AllWinning.nil))))))))))))))))))))))))

theorem node_25593 : Outcome ⟨10, 17, 20, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 20, 2⟩) (by decide) node_25469

theorem node_25594 : Outcome ⟨10, 18, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 18, 19, 2⟩, ⟨8, 18, 19, 4⟩, ⟨7, 18, 19, 6⟩, ⟨6, 18, 19, 8⟩, ⟨10, 17, 19, 2⟩, ⟨10, 16, 19, 4⟩, ⟨10, 15, 19, 6⟩, ⟨10, 14, 19, 8⟩, ⟨10, 18, 18, 2⟩, ⟨10, 18, 17, 4⟩, ⟨10, 18, 16, 6⟩, ⟨10, 18, 15, 8⟩]
  exact AllWinning.cons node_25465 (AllWinning.cons node_25290 (AllWinning.cons node_25072 (AllWinning.cons node_24838 (AllWinning.cons node_25471 (AllWinning.cons node_25308 (AllWinning.cons node_25110 (AllWinning.cons node_24887 (AllWinning.cons node_25472 (AllWinning.cons node_25310 (AllWinning.cons node_25119 (AllWinning.cons node_24896 (AllWinning.nil))))))))))))

theorem node_25595 : Outcome ⟨10, 19, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 19, 18, 2⟩, ⟨8, 19, 18, 4⟩, ⟨7, 19, 18, 6⟩, ⟨6, 19, 18, 8⟩, ⟨10, 18, 18, 2⟩, ⟨10, 17, 18, 4⟩, ⟨10, 16, 18, 6⟩, ⟨10, 15, 18, 8⟩, ⟨10, 19, 17, 2⟩, ⟨10, 19, 16, 4⟩, ⟨10, 19, 15, 6⟩, ⟨10, 19, 14, 8⟩]
  exact AllWinning.cons node_25466 (AllWinning.cons node_25292 (AllWinning.cons node_25075 (AllWinning.cons node_24840 (AllWinning.cons node_25472 (AllWinning.cons node_25309 (AllWinning.cons node_25113 (AllWinning.cons node_24889 (AllWinning.cons node_25474 (AllWinning.cons node_25312 (AllWinning.cons node_25123 (AllWinning.cons node_24899 (AllWinning.nil))))))))))))

theorem node_25596 : Outcome ⟨10, 20, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 20, 16, 2⟩) (by decide) node_25475

theorem node_25597 : Outcome ⟨11, 16, 20, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 20, 2⟩) (by decide) node_25469

theorem node_25598 : Outcome ⟨11, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 19, 2⟩) (by decide) node_25479

theorem node_25599 : Outcome ⟨11, 17, 19, 4⟩ true :=
  Outcome.win (q := ⟨11, 16, 19, 2⟩) (by decide) node_25479

theorem node_25600 : Outcome ⟨11, 18, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 18, 18, 2⟩, ⟨9, 18, 18, 4⟩, ⟨11, 17, 18, 2⟩, ⟨11, 16, 18, 4⟩, ⟨11, 18, 17, 2⟩, ⟨11, 18, 16, 4⟩]
  exact AllWinning.cons node_25472 (AllWinning.cons node_25299 (AllWinning.cons node_25482 (AllWinning.cons node_25319 (AllWinning.cons node_25484 (AllWinning.cons node_25325 (AllWinning.nil))))))

theorem node_25601 : Outcome ⟨11, 18, 18, 4⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 6⟩) (by decide) node_25085

theorem node_25602 : Outcome ⟨11, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 16, 2⟩) (by decide) node_25486

theorem node_25603 : Outcome ⟨11, 19, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 19, 16, 2⟩) (by decide) node_25486

theorem node_25604 : Outcome ⟨11, 20, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 20, 16, 2⟩) (by decide) node_25475

theorem node_25605 : Outcome ⟨12, 15, 20, 2⟩ true :=
  Outcome.win (q := ⟨11, 15, 20, 2⟩) (by decide) node_25477

theorem node_25606 : Outcome ⟨12, 15, 20, 8⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 8⟩) (by decide) node_24920

theorem node_25607 : Outcome ⟨12, 16, 19, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 19, 2⟩) (by decide) node_25479

theorem node_25608 : Outcome ⟨12, 16, 19, 8⟩ true :=
  Outcome.win (q := ⟨12, 12, 19, 8⟩) (by decide) node_24913

theorem node_25609 : Outcome ⟨12, 17, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 17, 18, 2⟩, ⟨10, 17, 18, 4⟩, ⟨12, 16, 18, 2⟩, ⟨12, 15, 18, 4⟩, ⟨12, 17, 17, 2⟩, ⟨12, 17, 16, 4⟩]
  exact AllWinning.cons node_25482 (AllWinning.cons node_25309 (AllWinning.cons node_25493 (AllWinning.cons node_25333 (AllWinning.cons node_25496 (AllWinning.cons node_25337 (AllWinning.nil))))))

theorem node_25610 : Outcome ⟨12, 18, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 18, 17, 2⟩, ⟨10, 18, 17, 4⟩, ⟨12, 17, 17, 2⟩, ⟨12, 16, 17, 4⟩, ⟨12, 18, 16, 2⟩, ⟨12, 18, 15, 4⟩]
  exact AllWinning.cons node_25484 (AllWinning.cons node_25310 (AllWinning.cons node_25496 (AllWinning.cons node_25335 (AllWinning.cons node_25497 (AllWinning.cons node_25340 (AllWinning.nil))))))

theorem node_25611 : Outcome ⟨12, 19, 16, 2⟩ true :=
  Outcome.win (q := ⟨11, 19, 16, 2⟩) (by decide) node_25486

theorem node_25612 : Outcome ⟨12, 19, 16, 8⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 8⟩) (by decide) node_24920

theorem node_25613 : Outcome ⟨12, 20, 15, 2⟩ true :=
  Outcome.win (q := ⟨11, 20, 15, 2⟩) (by decide) node_25489

theorem node_25614 : Outcome ⟨12, 20, 15, 8⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 8⟩) (by decide) node_24923

theorem node_25615 : Outcome ⟨13, 14, 20, 2⟩ true :=
  Outcome.win (q := ⟨13, 14, 19, 2⟩) (by decide) node_25503

theorem node_25616 : Outcome ⟨13, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 15, 19, 2⟩) (by decide) node_25492

theorem node_25617 : Outcome ⟨13, 15, 19, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 19, 2⟩) (by decide) node_25492

theorem node_25618 : Outcome ⟨13, 15, 19, 8⟩ true :=
  Outcome.win (q := ⟨12, 15, 19, 2⟩) (by decide) node_25492

theorem node_25619 : Outcome ⟨13, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 16, 16, 4⟩) (by decide) node_25354

theorem node_25620 : Outcome ⟨13, 17, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 17, 2⟩, ⟨11, 17, 17, 4⟩, ⟨13, 16, 17, 2⟩, ⟨13, 15, 17, 4⟩, ⟨13, 17, 16, 2⟩, ⟨13, 17, 15, 4⟩]
  exact AllWinning.cons node_25496 (AllWinning.cons node_25322 (AllWinning.cons node_25507 (AllWinning.cons node_25351 (AllWinning.cons node_25508 (AllWinning.cons node_25358 (AllWinning.nil))))))

end RQ9F1
