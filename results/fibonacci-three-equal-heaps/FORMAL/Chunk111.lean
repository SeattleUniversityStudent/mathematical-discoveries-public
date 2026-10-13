import Chunk110
set_option autoImplicit false
namespace RQ9F1

theorem node_23242 : Outcome ⟨13, 18, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 7, 2⟩, ⟨11, 18, 7, 4⟩, ⟨10, 18, 7, 6⟩, ⟨9, 18, 7, 8⟩, ⟨13, 17, 7, 2⟩, ⟨13, 16, 7, 4⟩, ⟨13, 15, 7, 6⟩, ⟨13, 14, 7, 8⟩, ⟨13, 18, 6, 2⟩, ⟨13, 18, 5, 4⟩, ⟨13, 18, 4, 6⟩, ⟨13, 18, 3, 8⟩]
  exact AllWinning.cons node_22688 (AllWinning.cons node_22079 (AllWinning.cons node_21450 (AllWinning.cons node_20725 (AllWinning.cons node_22732 (AllWinning.cons node_22165 (AllWinning.cons node_21566 (AllWinning.cons node_20914 (AllWinning.cons node_22735 (AllWinning.cons node_22171 (AllWinning.cons node_21575 (AllWinning.cons node_20924 (AllWinning.nil))))))))))))

theorem node_23243 : Outcome ⟨13, 18, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 7, 2⟩, ⟨11, 18, 7, 4⟩, ⟨10, 18, 7, 6⟩, ⟨9, 18, 7, 8⟩, ⟨8, 18, 7, 10⟩, ⟨7, 18, 7, 12⟩, ⟨13, 17, 7, 2⟩, ⟨13, 16, 7, 4⟩, ⟨13, 15, 7, 6⟩, ⟨13, 14, 7, 8⟩, ⟨13, 13, 7, 10⟩, ⟨13, 12, 7, 12⟩, ⟨13, 18, 6, 2⟩, ⟨13, 18, 5, 4⟩, ⟨13, 18, 4, 6⟩, ⟨13, 18, 3, 8⟩, ⟨13, 18, 2, 10⟩, ⟨13, 18, 1, 12⟩]
  exact AllWinning.cons node_22688 (AllWinning.cons node_22079 (AllWinning.cons node_21450 (AllWinning.cons node_20725 (AllWinning.cons node_19944 (AllWinning.cons node_19091 (AllWinning.cons node_22732 (AllWinning.cons node_22165 (AllWinning.cons node_21566 (AllWinning.cons node_20914 (AllWinning.cons node_20163 (AllWinning.cons node_19390 (AllWinning.cons node_22735 (AllWinning.cons node_22171 (AllWinning.cons node_21575 (AllWinning.cons node_20924 (AllWinning.cons node_20178 (AllWinning.cons node_19404 (AllWinning.nil))))))))))))))))))

theorem node_23244 : Outcome ⟨13, 18, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 18, 7, 2⟩, ⟨11, 18, 7, 4⟩, ⟨10, 18, 7, 6⟩, ⟨9, 18, 7, 8⟩, ⟨8, 18, 7, 10⟩, ⟨7, 18, 7, 12⟩, ⟨6, 18, 7, 14⟩, ⟨5, 18, 7, 16⟩, ⟨13, 17, 7, 2⟩, ⟨13, 16, 7, 4⟩, ⟨13, 15, 7, 6⟩, ⟨13, 14, 7, 8⟩, ⟨13, 13, 7, 10⟩, ⟨13, 12, 7, 12⟩, ⟨13, 11, 7, 14⟩, ⟨13, 10, 7, 16⟩, ⟨13, 18, 6, 2⟩, ⟨13, 18, 5, 4⟩, ⟨13, 18, 4, 6⟩, ⟨13, 18, 3, 8⟩, ⟨13, 18, 2, 10⟩, ⟨13, 18, 1, 12⟩, ⟨13, 18, 0, 14⟩]
  exact AllWinning.cons node_22688 (AllWinning.cons node_22079 (AllWinning.cons node_21450 (AllWinning.cons node_20725 (AllWinning.cons node_19944 (AllWinning.cons node_19091 (AllWinning.cons node_18129 (AllWinning.cons node_17204 (AllWinning.cons node_22732 (AllWinning.cons node_22165 (AllWinning.cons node_21566 (AllWinning.cons node_20914 (AllWinning.cons node_20163 (AllWinning.cons node_19390 (AllWinning.cons node_18517 (AllWinning.cons node_17609 (AllWinning.cons node_22735 (AllWinning.cons node_22171 (AllWinning.cons node_21575 (AllWinning.cons node_20924 (AllWinning.cons node_20178 (AllWinning.cons node_19404 (AllWinning.cons node_18543 (AllWinning.nil)))))))))))))))))))))))

theorem node_23245 : Outcome ⟨13, 19, 6, 4⟩ true :=
  Outcome.win (q := ⟨13, 19, 5, 2⟩) (by decide) node_22736

theorem node_23246 : Outcome ⟨13, 20, 5, 2⟩ true :=
  Outcome.win (q := ⟨13, 19, 5, 2⟩) (by decide) node_22736

theorem node_23247 : Outcome ⟨14, 4, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 2, 20, 4⟩) (by decide) node_22175

theorem node_23248 : Outcome ⟨14, 5, 19, 2⟩ true :=
  Outcome.win (q := ⟨13, 5, 19, 2⟩) (by decide) node_22696

theorem node_23249 : Outcome ⟨14, 5, 19, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 8⟩) (by decide) node_20734

theorem node_23250 : Outcome ⟨14, 6, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 18, 8⟩) (by decide) node_20740

theorem node_23251 : Outcome ⟨14, 6, 18, 12⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 10⟩) (by decide) node_20203

theorem node_23252 : Outcome ⟨14, 7, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 7, 16, 2⟩) (by decide) node_22751

theorem node_23253 : Outcome ⟨14, 7, 17, 8⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 8⟩) (by decide) node_20938

theorem node_23254 : Outcome ⟨14, 8, 16, 4⟩ true :=
  Outcome.win (q := ⟨13, 8, 16, 2⟩) (by decide) node_22703

theorem node_23255 : Outcome ⟨14, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 2⟩) (by decide) node_22706

theorem node_23256 : Outcome ⟨14, 9, 15, 8⟩ true :=
  Outcome.win (q := ⟨13, 9, 15, 2⟩) (by decide) node_22706

theorem node_23257 : Outcome ⟨14, 10, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 10, 14, 2⟩) (by decide) node_22710

theorem node_23258 : Outcome ⟨14, 10, 14, 8⟩ true :=
  Outcome.win (q := ⟨13, 10, 14, 2⟩) (by decide) node_22710

theorem node_23259 : Outcome ⟨14, 11, 13, 4⟩ true :=
  Outcome.win (q := ⟨13, 11, 13, 2⟩) (by decide) node_22713

theorem node_23260 : Outcome ⟨14, 11, 13, 8⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 10⟩) (by decide) node_20203

theorem node_23261 : Outcome ⟨14, 12, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 12, 12, 2⟩, ⟨12, 12, 12, 4⟩, ⟨14, 11, 12, 2⟩, ⟨14, 10, 12, 4⟩, ⟨14, 12, 11, 2⟩, ⟨14, 12, 10, 4⟩]
  exact AllWinning.cons node_22716 (AllWinning.cons node_22107 (AllWinning.cons node_22766 (AllWinning.cons node_22192 (AllWinning.cons node_22769 (AllWinning.cons node_22197 (AllWinning.nil))))))

theorem node_23262 : Outcome ⟨14, 12, 12, 4⟩ true :=
  Outcome.win (q := ⟨11, 12, 12, 6⟩) (by decide) node_21472

theorem node_23263 : Outcome ⟨14, 12, 12, 12⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 20⟩) (by decide) node_15682

theorem node_23264 : Outcome ⟨14, 13, 11, 4⟩ true :=
  Outcome.win (q := ⟨13, 13, 11, 2⟩) (by decide) node_22719

theorem node_23265 : Outcome ⟨14, 13, 11, 8⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 10⟩) (by decide) node_20223

theorem node_23266 : Outcome ⟨14, 14, 10, 4⟩ true :=
  Outcome.win (q := ⟨13, 14, 10, 2⟩) (by decide) node_22722

theorem node_23267 : Outcome ⟨14, 14, 10, 8⟩ true :=
  Outcome.win (q := ⟨13, 14, 10, 2⟩) (by decide) node_22722

theorem node_23268 : Outcome ⟨14, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 2⟩) (by decide) node_22725

theorem node_23269 : Outcome ⟨14, 15, 9, 8⟩ true :=
  Outcome.win (q := ⟨13, 15, 9, 2⟩) (by decide) node_22725

theorem node_23270 : Outcome ⟨14, 16, 8, 4⟩ true :=
  Outcome.win (q := ⟨13, 16, 8, 2⟩) (by decide) node_22729

theorem node_23271 : Outcome ⟨14, 17, 7, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 7, 2⟩) (by decide) node_22785

theorem node_23272 : Outcome ⟨14, 17, 7, 8⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 8⟩) (by decide) node_20975

theorem node_23273 : Outcome ⟨14, 18, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 6, 8⟩) (by decide) node_20773

theorem node_23274 : Outcome ⟨14, 18, 6, 12⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 10⟩) (by decide) node_20223

theorem node_23275 : Outcome ⟨14, 19, 5, 2⟩ true :=
  Outcome.win (q := ⟨13, 19, 5, 2⟩) (by decide) node_22736

theorem node_23276 : Outcome ⟨14, 19, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 8⟩) (by decide) node_20777

theorem node_23277 : Outcome ⟨14, 20, 4, 2⟩ true :=
  Outcome.win (q := ⟨14, 20, 2, 4⟩) (by decide) node_22215

theorem node_23278 : Outcome ⟨15, 3, 20, 6⟩ true :=
  Outcome.win (q := ⟨12, 3, 20, 6⟩) (by decide) node_21492

theorem node_23279 : Outcome ⟨15, 4, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 4, 17, 4⟩) (by decide) node_22228

theorem node_23280 : Outcome ⟨15, 5, 18, 2⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 4⟩) (by decide) node_22220

theorem node_23281 : Outcome ⟨15, 5, 18, 6⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 6⟩) (by decide) node_21497

theorem node_23282 : Outcome ⟨15, 5, 18, 8⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 6⟩) (by decide) node_21497

theorem node_23283 : Outcome ⟨15, 6, 17, 2⟩ true :=
  Outcome.win (q := ⟨15, 4, 17, 4⟩) (by decide) node_22228

theorem node_23284 : Outcome ⟨15, 6, 17, 6⟩ true :=
  Outcome.win (q := ⟨9, 6, 17, 12⟩) (by decide) node_19155

theorem node_23285 : Outcome ⟨15, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 7, 16, 2⟩) (by decide) node_22751

theorem node_23286 : Outcome ⟨15, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 8⟩) (by decide) node_20791

theorem node_23287 : Outcome ⟨15, 7, 16, 10⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 12⟩) (by decide) node_19462

theorem node_23288 : Outcome ⟨15, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 8, 15, 2⟩) (by decide) node_22753

theorem node_23289 : Outcome ⟨15, 9, 14, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 2⟩) (by decide) node_22758

theorem node_23290 : Outcome ⟨15, 9, 14, 8⟩ true :=
  Outcome.win (q := ⟨14, 9, 14, 2⟩) (by decide) node_22758

theorem node_23291 : Outcome ⟨15, 10, 13, 4⟩ true :=
  Outcome.win (q := ⟨14, 10, 13, 2⟩) (by decide) node_22763

theorem node_23292 : Outcome ⟨15, 10, 13, 8⟩ true :=
  Outcome.win (q := ⟨14, 10, 13, 2⟩) (by decide) node_22763

theorem node_23293 : Outcome ⟨15, 11, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 12, 2⟩, ⟨13, 11, 12, 4⟩, ⟨15, 10, 12, 2⟩, ⟨15, 9, 12, 4⟩, ⟨15, 11, 11, 2⟩, ⟨15, 11, 10, 4⟩]
  exact AllWinning.cons node_22766 (AllWinning.cons node_22150 (AllWinning.cons node_22817 (AllWinning.cons node_22242 (AllWinning.cons node_22820 (AllWinning.cons node_22248 (AllWinning.nil))))))

theorem node_23294 : Outcome ⟨15, 11, 12, 4⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 8⟩) (by decide) node_21003

theorem node_23295 : Outcome ⟨15, 11, 12, 10⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 12⟩) (by decide) node_19501

theorem node_23296 : Outcome ⟨15, 12, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 12, 11, 2⟩, ⟨13, 12, 11, 4⟩, ⟨15, 11, 11, 2⟩, ⟨15, 10, 11, 4⟩, ⟨15, 12, 10, 2⟩, ⟨15, 12, 9, 4⟩]
  exact AllWinning.cons node_22769 (AllWinning.cons node_22154 (AllWinning.cons node_22820 (AllWinning.cons node_22245 (AllWinning.cons node_22821 (AllWinning.cons node_22251 (AllWinning.nil))))))

theorem node_23297 : Outcome ⟨15, 12, 11, 4⟩ true :=
  Outcome.win (q := ⟨15, 12, 7, 8⟩) (by decide) node_21022

theorem node_23298 : Outcome ⟨15, 12, 11, 10⟩ true :=
  Outcome.win (q := ⟨15, 6, 11, 12⟩) (by decide) node_19485

theorem node_23299 : Outcome ⟨15, 13, 10, 4⟩ true :=
  Outcome.win (q := ⟨14, 13, 10, 2⟩) (by decide) node_22772

theorem node_23300 : Outcome ⟨15, 13, 10, 8⟩ true :=
  Outcome.win (q := ⟨14, 13, 10, 2⟩) (by decide) node_22772

theorem node_23301 : Outcome ⟨15, 14, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 2⟩) (by decide) node_22775

theorem node_23302 : Outcome ⟨15, 14, 9, 8⟩ true :=
  Outcome.win (q := ⟨14, 14, 9, 2⟩) (by decide) node_22775

theorem node_23303 : Outcome ⟨15, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 8, 2⟩) (by decide) node_22780

theorem node_23304 : Outcome ⟨15, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 7, 2⟩) (by decide) node_22785

theorem node_23305 : Outcome ⟨15, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 8⟩) (by decide) node_20813

theorem node_23306 : Outcome ⟨15, 16, 7, 10⟩ true :=
  Outcome.win (q := ⟨15, 16, 1, 12⟩) (by decide) node_19520

theorem node_23307 : Outcome ⟨15, 17, 6, 2⟩ true :=
  Outcome.win (q := ⟨15, 17, 4, 4⟩) (by decide) node_22264

theorem node_23308 : Outcome ⟨15, 17, 6, 6⟩ true :=
  Outcome.win (q := ⟨9, 17, 6, 12⟩) (by decide) node_19192

theorem node_23309 : Outcome ⟨15, 18, 5, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 4⟩) (by decide) node_22267

theorem node_23310 : Outcome ⟨15, 18, 5, 6⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 6⟩) (by decide) node_21528

theorem node_23311 : Outcome ⟨15, 19, 4, 2⟩ true :=
  Outcome.win (q := ⟨15, 17, 4, 4⟩) (by decide) node_22264

theorem node_23312 : Outcome ⟨15, 20, 3, 6⟩ true :=
  Outcome.win (q := ⟨12, 20, 3, 6⟩) (by decide) node_21534

theorem node_23313 : Outcome ⟨16, 3, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 19, 2⟩, ⟨14, 3, 19, 4⟩, ⟨13, 3, 19, 6⟩, ⟨12, 3, 19, 8⟩, ⟨16, 2, 19, 2⟩, ⟨16, 1, 19, 4⟩, ⟨16, 0, 19, 6⟩, ⟨16, 3, 18, 2⟩, ⟨16, 3, 17, 4⟩, ⟨16, 3, 16, 6⟩, ⟨16, 3, 15, 8⟩]
  exact AllWinning.cons node_22798 (AllWinning.cons node_22177 (AllWinning.cons node_21538 (AllWinning.cons node_20825 (AllWinning.cons node_22844 (AllWinning.cons node_22276 (AllWinning.cons node_21665 (AllWinning.cons node_22845 (AllWinning.cons node_22281 (AllWinning.cons node_21671 (AllWinning.cons node_21048 (AllWinning.nil)))))))))))

theorem node_23314 : Outcome ⟨16, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨16, 2, 18, 4⟩) (by decide) node_22278

theorem node_23315 : Outcome ⟨16, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨16, 5, 16, 2⟩) (by decide) node_22847

theorem node_23316 : Outcome ⟨16, 6, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 6, 16, 2⟩) (by decide) node_22802

theorem node_23317 : Outcome ⟨16, 6, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 8⟩) (by decide) node_20833

theorem node_23318 : Outcome ⟨16, 6, 16, 14⟩ true :=
  Outcome.win (q := ⟨16, 0, 16, 12⟩) (by decide) node_19532

theorem node_23319 : Outcome ⟨16, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 8⟩) (by decide) node_20839

theorem node_23320 : Outcome ⟨16, 7, 15, 10⟩ true :=
  Outcome.win (q := ⟨16, 1, 15, 12⟩) (by decide) node_19537

theorem node_23321 : Outcome ⟨16, 8, 14, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 14, 2⟩) (by decide) node_22808

theorem node_23322 : Outcome ⟨16, 9, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 13, 2⟩) (by decide) node_22813

theorem node_23323 : Outcome ⟨16, 9, 13, 14⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 18⟩) (by decide) node_16290

theorem node_23324 : Outcome ⟨16, 10, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 10, 12, 2⟩, ⟨14, 10, 12, 4⟩, ⟨16, 9, 12, 2⟩, ⟨16, 8, 12, 4⟩, ⟨16, 10, 11, 2⟩, ⟨16, 10, 10, 4⟩]
  exact AllWinning.cons node_22817 (AllWinning.cons node_22192 (AllWinning.cons node_22856 (AllWinning.cons node_22291 (AllWinning.cons node_22859 (AllWinning.cons node_22296 (AllWinning.nil))))))

theorem node_23325 : Outcome ⟨16, 10, 12, 4⟩ true :=
  Outcome.win (q := ⟨16, 6, 12, 8⟩) (by decide) node_21057

theorem node_23326 : Outcome ⟨16, 10, 12, 10⟩ true :=
  Outcome.win (q := ⟨16, 6, 12, 8⟩) (by decide) node_21057

theorem node_23327 : Outcome ⟨16, 11, 11, 4⟩ true :=
  Outcome.win (q := ⟨16, 7, 11, 8⟩) (by decide) node_21064

theorem node_23328 : Outcome ⟨16, 12, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 12, 10, 2⟩, ⟨14, 12, 10, 4⟩, ⟨16, 11, 10, 2⟩, ⟨16, 10, 10, 4⟩, ⟨16, 12, 9, 2⟩, ⟨16, 12, 8, 4⟩]
  exact AllWinning.cons node_22821 (AllWinning.cons node_22197 (AllWinning.cons node_22861 (AllWinning.cons node_22296 (AllWinning.cons node_22863 (AllWinning.cons node_22300 (AllWinning.nil))))))

theorem node_23329 : Outcome ⟨16, 12, 10, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 6, 8⟩) (by decide) node_21081

theorem node_23330 : Outcome ⟨16, 12, 10, 10⟩ true :=
  Outcome.win (q := ⟨16, 12, 6, 8⟩) (by decide) node_21081

theorem node_23331 : Outcome ⟨16, 13, 9, 4⟩ true :=
  Outcome.win (q := ⟨15, 13, 9, 2⟩) (by decide) node_22824

theorem node_23332 : Outcome ⟨16, 13, 9, 14⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 18⟩) (by decide) node_16306

theorem node_23333 : Outcome ⟨16, 14, 8, 4⟩ true :=
  Outcome.win (q := ⟨15, 14, 8, 2⟩) (by decide) node_22828

theorem node_23334 : Outcome ⟨16, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨16, 14, 7, 2⟩) (by decide) node_22868

theorem node_23335 : Outcome ⟨16, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 8⟩) (by decide) node_20862

theorem node_23336 : Outcome ⟨16, 15, 7, 10⟩ true :=
  Outcome.win (q := ⟨16, 15, 1, 12⟩) (by decide) node_19575

theorem node_23337 : Outcome ⟨16, 16, 6, 2⟩ true :=
  Outcome.win (q := ⟨15, 16, 6, 2⟩) (by decide) node_22835

theorem node_23338 : Outcome ⟨16, 16, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 8⟩) (by decide) node_20867

theorem node_23339 : Outcome ⟨16, 16, 6, 14⟩ true :=
  Outcome.win (q := ⟨16, 16, 0, 12⟩) (by decide) node_19584

theorem node_23340 : Outcome ⟨16, 17, 5, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 5, 2⟩) (by decide) node_22872

theorem node_23341 : Outcome ⟨16, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨16, 18, 2, 4⟩) (by decide) node_22314

theorem node_23342 : Outcome ⟨16, 19, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 19, 3, 2⟩, ⟨14, 19, 3, 4⟩, ⟨13, 19, 3, 6⟩, ⟨12, 19, 3, 8⟩, ⟨16, 18, 3, 2⟩, ⟨16, 17, 3, 4⟩, ⟨16, 16, 3, 6⟩, ⟨16, 15, 3, 8⟩, ⟨16, 19, 2, 2⟩, ⟨16, 19, 1, 4⟩, ⟨16, 19, 0, 6⟩]
  exact AllWinning.cons node_22841 (AllWinning.cons node_22214 (AllWinning.cons node_21577 (AllWinning.cons node_20874 (AllWinning.cons node_22877 (AllWinning.cons node_22311 (AllWinning.cons node_21694 (AllWinning.cons node_21089 (AllWinning.cons node_22878 (AllWinning.cons node_22317 (AllWinning.cons node_21700 (AllWinning.nil)))))))))))

theorem node_23343 : Outcome ⟨17, 2, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 19, 2⟩, ⟨15, 2, 19, 4⟩, ⟨14, 2, 19, 6⟩, ⟨13, 2, 19, 8⟩, ⟨17, 1, 19, 2⟩, ⟨17, 0, 19, 4⟩, ⟨17, 2, 18, 2⟩, ⟨17, 2, 17, 4⟩, ⟨17, 2, 16, 6⟩, ⟨17, 2, 15, 8⟩]
  exact AllWinning.cons node_22844 (AllWinning.cons node_22217 (AllWinning.cons node_21584 (AllWinning.cons node_20881 (AllWinning.cons node_22879 (AllWinning.cons node_22318 (AllWinning.cons node_22880 (AllWinning.cons node_22320 (AllWinning.cons node_21705 (AllWinning.cons node_21102 (AllWinning.nil))))))))))

theorem node_23344 : Outcome ⟨17, 2, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 2, 19, 2⟩, ⟨15, 2, 19, 4⟩, ⟨14, 2, 19, 6⟩, ⟨13, 2, 19, 8⟩, ⟨12, 2, 19, 10⟩, ⟨11, 2, 19, 12⟩, ⟨17, 1, 19, 2⟩, ⟨17, 0, 19, 4⟩, ⟨17, 2, 18, 2⟩, ⟨17, 2, 17, 4⟩, ⟨17, 2, 16, 6⟩, ⟨17, 2, 15, 8⟩, ⟨17, 2, 14, 10⟩, ⟨17, 2, 13, 12⟩]
  exact AllWinning.cons node_22844 (AllWinning.cons node_22217 (AllWinning.cons node_21584 (AllWinning.cons node_20881 (AllWinning.cons node_20087 (AllWinning.cons node_19255 (AllWinning.cons node_22879 (AllWinning.cons node_22318 (AllWinning.cons node_22880 (AllWinning.cons node_22320 (AllWinning.cons node_21705 (AllWinning.cons node_21102 (AllWinning.cons node_20322 (AllWinning.cons node_19592 (AllWinning.nil))))))))))))))

theorem node_23345 : Outcome ⟨17, 3, 18, 2⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 4⟩) (by decide) node_22220

theorem node_23346 : Outcome ⟨17, 4, 17, 2⟩ true :=
  Outcome.win (q := ⟨15, 4, 17, 4⟩) (by decide) node_22228

theorem node_23347 : Outcome ⟨17, 4, 17, 8⟩ true :=
  Outcome.win (q := ⟨17, 0, 17, 8⟩) (by decide) node_21097

theorem node_23348 : Outcome ⟨17, 5, 16, 2⟩ true :=
  Outcome.win (q := ⟨16, 5, 16, 2⟩) (by decide) node_22847

theorem node_23349 : Outcome ⟨17, 5, 16, 8⟩ true :=
  Outcome.win (q := ⟨16, 5, 16, 2⟩) (by decide) node_22847

theorem node_23350 : Outcome ⟨17, 6, 15, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 15, 4⟩) (by decide) node_22325

theorem node_23351 : Outcome ⟨17, 7, 14, 8⟩ true :=
  Outcome.win (q := ⟨17, 3, 14, 8⟩) (by decide) node_21104

theorem node_23352 : Outcome ⟨17, 8, 13, 4⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 4⟩) (by decide) node_22332

theorem node_23353 : Outcome ⟨17, 8, 13, 8⟩ true :=
  Outcome.win (q := ⟨17, 1, 13, 14⟩) (by decide) node_18703

theorem node_23354 : Outcome ⟨17, 9, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 12, 2⟩, ⟨15, 9, 12, 4⟩, ⟨17, 8, 12, 2⟩, ⟨17, 7, 12, 4⟩, ⟨17, 9, 11, 2⟩, ⟨17, 9, 10, 4⟩]
  exact AllWinning.cons node_22856 (AllWinning.cons node_22242 (AllWinning.cons node_22889 (AllWinning.cons node_22329 (AllWinning.cons node_22891 (AllWinning.cons node_22335 (AllWinning.nil))))))

theorem node_23355 : Outcome ⟨17, 9, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 9, 12, 2⟩, ⟨15, 9, 12, 4⟩, ⟨14, 9, 12, 6⟩, ⟨13, 9, 12, 8⟩, ⟨17, 8, 12, 2⟩, ⟨17, 7, 12, 4⟩, ⟨17, 6, 12, 6⟩, ⟨17, 5, 12, 8⟩, ⟨17, 9, 11, 2⟩, ⟨17, 9, 10, 4⟩, ⟨17, 9, 9, 6⟩, ⟨17, 9, 8, 8⟩]
  exact AllWinning.cons node_22856 (AllWinning.cons node_22242 (AllWinning.cons node_21596 (AllWinning.cons node_20901 (AllWinning.cons node_22889 (AllWinning.cons node_22329 (AllWinning.cons node_21714 (AllWinning.cons node_21109 (AllWinning.cons node_22891 (AllWinning.cons node_22335 (AllWinning.cons node_21719 (AllWinning.cons node_21117 (AllWinning.nil))))))))))))

theorem node_23356 : Outcome ⟨17, 9, 12, 8⟩ true :=
  Outcome.win (q := ⟨17, 9, 6, 12⟩) (by decide) node_19616

theorem node_23357 : Outcome ⟨17, 10, 11, 4⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 4⟩) (by decide) node_22332

theorem node_23358 : Outcome ⟨17, 10, 11, 8⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 4⟩) (by decide) node_22332

theorem node_23359 : Outcome ⟨17, 11, 10, 4⟩ true :=
  Outcome.win (q := ⟨17, 11, 8, 4⟩) (by decide) node_22340

theorem node_23360 : Outcome ⟨17, 11, 10, 8⟩ true :=
  Outcome.win (q := ⟨17, 11, 8, 4⟩) (by decide) node_22340

theorem node_23361 : Outcome ⟨17, 12, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 12, 9, 2⟩, ⟨15, 12, 9, 4⟩, ⟨17, 11, 9, 2⟩, ⟨17, 10, 9, 4⟩, ⟨17, 12, 8, 2⟩, ⟨17, 12, 7, 4⟩]
  exact AllWinning.cons node_22863 (AllWinning.cons node_22251 (AllWinning.cons node_22896 (AllWinning.cons node_22338 (AllWinning.cons node_22897 (AllWinning.cons node_22341 (AllWinning.nil))))))

theorem node_23362 : Outcome ⟨17, 12, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 12, 9, 2⟩, ⟨15, 12, 9, 4⟩, ⟨14, 12, 9, 6⟩, ⟨13, 12, 9, 8⟩, ⟨17, 11, 9, 2⟩, ⟨17, 10, 9, 4⟩, ⟨17, 9, 9, 6⟩, ⟨17, 8, 9, 8⟩, ⟨17, 12, 8, 2⟩, ⟨17, 12, 7, 4⟩, ⟨17, 12, 6, 6⟩, ⟨17, 12, 5, 8⟩]
  exact AllWinning.cons node_22863 (AllWinning.cons node_22251 (AllWinning.cons node_21604 (AllWinning.cons node_20909 (AllWinning.cons node_22896 (AllWinning.cons node_22338 (AllWinning.cons node_21719 (AllWinning.cons node_21115 (AllWinning.cons node_22897 (AllWinning.cons node_22341 (AllWinning.cons node_21724 (AllWinning.cons node_21123 (AllWinning.nil))))))))))))

theorem node_23363 : Outcome ⟨17, 12, 9, 8⟩ true :=
  Outcome.win (q := ⟨17, 6, 9, 12⟩) (by decide) node_19604

theorem node_23364 : Outcome ⟨17, 13, 8, 4⟩ true :=
  Outcome.win (q := ⟨17, 11, 8, 4⟩) (by decide) node_22340

theorem node_23365 : Outcome ⟨17, 13, 8, 8⟩ true :=
  Outcome.win (q := ⟨17, 13, 1, 14⟩) (by decide) node_18729

theorem node_23366 : Outcome ⟨17, 14, 7, 2⟩ true :=
  Outcome.win (q := ⟨16, 14, 7, 2⟩) (by decide) node_22868

theorem node_23367 : Outcome ⟨17, 14, 7, 8⟩ true :=
  Outcome.win (q := ⟨17, 14, 3, 8⟩) (by decide) node_21128

theorem node_23368 : Outcome ⟨17, 15, 6, 2⟩ true :=
  Outcome.win (q := ⟨17, 15, 4, 4⟩) (by decide) node_22347

theorem node_23369 : Outcome ⟨17, 16, 5, 2⟩ true :=
  Outcome.win (q := ⟨16, 16, 5, 2⟩) (by decide) node_22872

theorem node_23370 : Outcome ⟨17, 16, 5, 8⟩ true :=
  Outcome.win (q := ⟨16, 16, 5, 2⟩) (by decide) node_22872

theorem node_23371 : Outcome ⟨17, 17, 4, 2⟩ true :=
  Outcome.win (q := ⟨15, 17, 4, 4⟩) (by decide) node_22264

theorem node_23372 : Outcome ⟨17, 17, 4, 8⟩ true :=
  Outcome.win (q := ⟨17, 17, 0, 8⟩) (by decide) node_21136

theorem node_23373 : Outcome ⟨17, 18, 3, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 4⟩) (by decide) node_22267

theorem node_23374 : Outcome ⟨17, 19, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 19, 2, 2⟩, ⟨15, 19, 2, 4⟩, ⟨14, 19, 2, 6⟩, ⟨13, 19, 2, 8⟩, ⟨17, 18, 2, 2⟩, ⟨17, 17, 2, 4⟩, ⟨17, 16, 2, 6⟩, ⟨17, 15, 2, 8⟩, ⟨17, 19, 1, 2⟩, ⟨17, 19, 0, 4⟩]
  exact AllWinning.cons node_22878 (AllWinning.cons node_22274 (AllWinning.cons node_21617 (AllWinning.cons node_20927 (AllWinning.cons node_22905 (AllWinning.cons node_22349 (AllWinning.cons node_21733 (AllWinning.cons node_21132 (AllWinning.cons node_22907 (AllWinning.cons node_22352 (AllWinning.nil))))))))))

theorem node_23375 : Outcome ⟨17, 19, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 19, 2, 2⟩, ⟨15, 19, 2, 4⟩, ⟨14, 19, 2, 6⟩, ⟨13, 19, 2, 8⟩, ⟨12, 19, 2, 10⟩, ⟨11, 19, 2, 12⟩, ⟨17, 18, 2, 2⟩, ⟨17, 17, 2, 4⟩, ⟨17, 16, 2, 6⟩, ⟨17, 15, 2, 8⟩, ⟨17, 14, 2, 10⟩, ⟨17, 13, 2, 12⟩, ⟨17, 19, 1, 2⟩, ⟨17, 19, 0, 4⟩]
  exact AllWinning.cons node_22878 (AllWinning.cons node_22274 (AllWinning.cons node_21617 (AllWinning.cons node_20927 (AllWinning.cons node_20122 (AllWinning.cons node_19302 (AllWinning.cons node_22905 (AllWinning.cons node_22349 (AllWinning.cons node_21733 (AllWinning.cons node_21132 (AllWinning.cons node_20342 (AllWinning.cons node_19625 (AllWinning.cons node_22907 (AllWinning.cons node_22352 (AllWinning.nil))))))))))))))

theorem node_23376 : Outcome ⟨18, 1, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 19, 2⟩, ⟨16, 1, 19, 4⟩, ⟨18, 0, 19, 2⟩, ⟨18, 1, 18, 2⟩, ⟨18, 1, 17, 4⟩]
  exact AllWinning.cons node_22879 (AllWinning.cons node_22276 (AllWinning.cons node_22908 (AllWinning.cons node_22909 (AllWinning.cons node_22355 (AllWinning.nil)))))

theorem node_23377 : Outcome ⟨18, 1, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 1, 19, 2⟩, ⟨16, 1, 19, 4⟩, ⟨15, 1, 19, 6⟩, ⟨14, 1, 19, 8⟩, ⟨13, 1, 19, 10⟩, ⟨12, 1, 19, 12⟩, ⟨11, 1, 19, 14⟩, ⟨10, 1, 19, 16⟩, ⟨18, 0, 19, 2⟩, ⟨18, 1, 18, 2⟩, ⟨18, 1, 17, 4⟩, ⟨18, 1, 16, 6⟩, ⟨18, 1, 15, 8⟩, ⟨18, 1, 14, 10⟩, ⟨18, 1, 13, 12⟩, ⟨18, 1, 12, 14⟩, ⟨18, 1, 11, 16⟩]
  exact AllWinning.cons node_22879 (AllWinning.cons node_22276 (AllWinning.cons node_21621 (AllWinning.cons node_20933 (AllWinning.cons node_20129 (AllWinning.cons node_19309 (AllWinning.cons node_18365 (AllWinning.cons node_17409 (AllWinning.cons node_22908 (AllWinning.cons node_22909 (AllWinning.cons node_22355 (AllWinning.cons node_21740 (AllWinning.cons node_21140 (AllWinning.cons node_20350 (AllWinning.cons node_19632 (AllWinning.cons node_18738 (AllWinning.cons node_17825 (AllWinning.nil)))))))))))))))))

theorem node_23378 : Outcome ⟨18, 2, 18, 6⟩ true :=
  Outcome.win (q := ⟨16, 2, 18, 4⟩) (by decide) node_22278

theorem node_23379 : Outcome ⟨18, 2, 18, 12⟩ true :=
  Outcome.win (q := ⟨16, 2, 18, 4⟩) (by decide) node_22278

theorem node_23380 : Outcome ⟨18, 5, 15, 6⟩ true :=
  Outcome.win (q := ⟨18, 5, 12, 6⟩) (by decide) node_21746

theorem node_23381 : Outcome ⟨18, 6, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 6, 14, 2⟩, ⟨16, 6, 14, 4⟩, ⟨18, 5, 14, 2⟩, ⟨18, 4, 14, 4⟩, ⟨18, 6, 13, 2⟩, ⟨18, 6, 12, 4⟩]
  exact AllWinning.cons node_22886 (AllWinning.cons node_22286 (AllWinning.cons node_22912 (AllWinning.cons node_22361 (AllWinning.cons node_22914 (AllWinning.cons node_22364 (AllWinning.nil))))))

theorem node_23382 : Outcome ⟨18, 6, 14, 4⟩ true :=
  Outcome.win (q := ⟨18, 6, 10, 8⟩) (by decide) node_21147

theorem node_23383 : Outcome ⟨18, 6, 14, 12⟩ true :=
  Outcome.win (q := ⟨13, 6, 14, 10⟩) (by decide) node_20142

theorem node_23384 : Outcome ⟨18, 7, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 7, 13, 2⟩, ⟨16, 7, 13, 4⟩, ⟨18, 6, 13, 2⟩, ⟨18, 5, 13, 4⟩, ⟨18, 7, 12, 2⟩, ⟨18, 7, 11, 4⟩]
  exact AllWinning.cons node_22888 (AllWinning.cons node_22289 (AllWinning.cons node_22914 (AllWinning.cons node_22363 (AllWinning.cons node_22915 (AllWinning.cons node_22365 (AllWinning.nil))))))

theorem node_23385 : Outcome ⟨18, 7, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 7, 13, 2⟩, ⟨16, 7, 13, 4⟩, ⟨15, 7, 13, 6⟩, ⟨14, 7, 13, 8⟩, ⟨18, 6, 13, 2⟩, ⟨18, 5, 13, 4⟩, ⟨18, 4, 13, 6⟩, ⟨18, 3, 13, 8⟩, ⟨18, 7, 12, 2⟩, ⟨18, 7, 11, 4⟩, ⟨18, 7, 10, 6⟩, ⟨18, 7, 9, 8⟩]
  exact AllWinning.cons node_22888 (AllWinning.cons node_22289 (AllWinning.cons node_21636 (AllWinning.cons node_20950 (AllWinning.cons node_22914 (AllWinning.cons node_22363 (AllWinning.cons node_21743 (AllWinning.cons node_21143 (AllWinning.cons node_22915 (AllWinning.cons node_22365 (AllWinning.cons node_21749 (AllWinning.cons node_21149 (AllWinning.nil))))))))))))

theorem node_23386 : Outcome ⟨18, 7, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 7, 13, 2⟩, ⟨16, 7, 13, 4⟩, ⟨15, 7, 13, 6⟩, ⟨14, 7, 13, 8⟩, ⟨13, 7, 13, 10⟩, ⟨12, 7, 13, 12⟩, ⟨18, 6, 13, 2⟩, ⟨18, 5, 13, 4⟩, ⟨18, 4, 13, 6⟩, ⟨18, 3, 13, 8⟩, ⟨18, 2, 13, 10⟩, ⟨18, 1, 13, 12⟩, ⟨18, 7, 12, 2⟩, ⟨18, 7, 11, 4⟩, ⟨18, 7, 10, 6⟩, ⟨18, 7, 9, 8⟩, ⟨18, 7, 8, 10⟩, ⟨18, 7, 7, 12⟩]
  exact AllWinning.cons node_22888 (AllWinning.cons node_22289 (AllWinning.cons node_21636 (AllWinning.cons node_20950 (AllWinning.cons node_20146 (AllWinning.cons node_19321 (AllWinning.cons node_22914 (AllWinning.cons node_22363 (AllWinning.cons node_21743 (AllWinning.cons node_21143 (AllWinning.cons node_20353 (AllWinning.cons node_19632 (AllWinning.cons node_22915 (AllWinning.cons node_22365 (AllWinning.cons node_21749 (AllWinning.cons node_21149 (AllWinning.cons node_20362 (AllWinning.cons node_19642 (AllWinning.nil))))))))))))))))))

theorem node_23387 : Outcome ⟨18, 7, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 7, 13, 2⟩, ⟨16, 7, 13, 4⟩, ⟨15, 7, 13, 6⟩, ⟨14, 7, 13, 8⟩, ⟨13, 7, 13, 10⟩, ⟨12, 7, 13, 12⟩, ⟨11, 7, 13, 14⟩, ⟨10, 7, 13, 16⟩, ⟨18, 6, 13, 2⟩, ⟨18, 5, 13, 4⟩, ⟨18, 4, 13, 6⟩, ⟨18, 3, 13, 8⟩, ⟨18, 2, 13, 10⟩, ⟨18, 1, 13, 12⟩, ⟨18, 0, 13, 14⟩, ⟨18, 7, 12, 2⟩, ⟨18, 7, 11, 4⟩, ⟨18, 7, 10, 6⟩, ⟨18, 7, 9, 8⟩, ⟨18, 7, 8, 10⟩, ⟨18, 7, 7, 12⟩, ⟨18, 7, 6, 14⟩, ⟨18, 7, 5, 16⟩]
  exact AllWinning.cons node_22888 (AllWinning.cons node_22289 (AllWinning.cons node_21636 (AllWinning.cons node_20950 (AllWinning.cons node_20146 (AllWinning.cons node_19321 (AllWinning.cons node_18380 (AllWinning.cons node_17429 (AllWinning.cons node_22914 (AllWinning.cons node_22363 (AllWinning.cons node_21743 (AllWinning.cons node_21143 (AllWinning.cons node_20353 (AllWinning.cons node_19632 (AllWinning.cons node_18734 (AllWinning.cons node_22915 (AllWinning.cons node_22365 (AllWinning.cons node_21749 (AllWinning.cons node_21149 (AllWinning.cons node_20362 (AllWinning.cons node_19642 (AllWinning.cons node_18756 (AllWinning.cons node_17841 (AllWinning.nil)))))))))))))))))))))))

theorem node_23388 : Outcome ⟨18, 8, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 8, 12, 2⟩, ⟨16, 8, 12, 4⟩, ⟨18, 7, 12, 2⟩, ⟨18, 6, 12, 4⟩, ⟨18, 8, 11, 2⟩, ⟨18, 8, 10, 4⟩]
  exact AllWinning.cons node_22889 (AllWinning.cons node_22291 (AllWinning.cons node_22915 (AllWinning.cons node_22364 (AllWinning.cons node_22916 (AllWinning.cons node_22366 (AllWinning.nil))))))

theorem node_23389 : Outcome ⟨18, 8, 12, 4⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 8⟩) (by decide) node_21151

theorem node_23390 : Outcome ⟨18, 8, 12, 12⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 8⟩) (by decide) node_21151

theorem node_23391 : Outcome ⟨18, 9, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 9, 11, 2⟩, ⟨16, 9, 11, 4⟩, ⟨18, 8, 11, 2⟩, ⟨18, 7, 11, 4⟩, ⟨18, 9, 10, 2⟩, ⟨18, 9, 9, 4⟩]
  exact AllWinning.cons node_22891 (AllWinning.cons node_22293 (AllWinning.cons node_22916 (AllWinning.cons node_22365 (AllWinning.cons node_22917 (AllWinning.cons node_22367 (AllWinning.nil))))))

theorem node_23392 : Outcome ⟨18, 10, 10, 4⟩ true :=
  Outcome.win (q := ⟨18, 6, 10, 8⟩) (by decide) node_21147

theorem node_23393 : Outcome ⟨18, 11, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 11, 9, 2⟩, ⟨16, 11, 9, 4⟩, ⟨18, 10, 9, 2⟩, ⟨18, 9, 9, 4⟩, ⟨18, 11, 8, 2⟩, ⟨18, 11, 7, 4⟩]
  exact AllWinning.cons node_22896 (AllWinning.cons node_22298 (AllWinning.cons node_22918 (AllWinning.cons node_22367 (AllWinning.cons node_22919 (AllWinning.cons node_22369 (AllWinning.nil))))))

theorem node_23394 : Outcome ⟨18, 12, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 12, 8, 2⟩, ⟨16, 12, 8, 4⟩, ⟨18, 11, 8, 2⟩, ⟨18, 10, 8, 4⟩, ⟨18, 12, 7, 2⟩, ⟨18, 12, 6, 4⟩]
  exact AllWinning.cons node_22897 (AllWinning.cons node_22300 (AllWinning.cons node_22919 (AllWinning.cons node_22368 (AllWinning.cons node_22920 (AllWinning.cons node_22370 (AllWinning.nil))))))

theorem node_23395 : Outcome ⟨18, 12, 8, 4⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 8⟩) (by decide) node_21151

theorem node_23396 : Outcome ⟨18, 12, 8, 12⟩ true :=
  Outcome.win (q := ⟨18, 8, 8, 8⟩) (by decide) node_21151

theorem node_23397 : Outcome ⟨18, 13, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 7, 2⟩, ⟨16, 13, 7, 4⟩, ⟨18, 12, 7, 2⟩, ⟨18, 11, 7, 4⟩, ⟨18, 13, 6, 2⟩, ⟨18, 13, 5, 4⟩]
  exact AllWinning.cons node_22898 (AllWinning.cons node_22303 (AllWinning.cons node_22920 (AllWinning.cons node_22369 (AllWinning.cons node_22921 (AllWinning.cons node_22372 (AllWinning.nil))))))

theorem node_23398 : Outcome ⟨18, 13, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 7, 2⟩, ⟨16, 13, 7, 4⟩, ⟨15, 13, 7, 6⟩, ⟨14, 13, 7, 8⟩, ⟨18, 12, 7, 2⟩, ⟨18, 11, 7, 4⟩, ⟨18, 10, 7, 6⟩, ⟨18, 9, 7, 8⟩, ⟨18, 13, 6, 2⟩, ⟨18, 13, 5, 4⟩, ⟨18, 13, 4, 6⟩, ⟨18, 13, 3, 8⟩]
  exact AllWinning.cons node_22898 (AllWinning.cons node_22303 (AllWinning.cons node_21650 (AllWinning.cons node_20963 (AllWinning.cons node_22920 (AllWinning.cons node_22369 (AllWinning.cons node_21750 (AllWinning.cons node_21154 (AllWinning.cons node_22921 (AllWinning.cons node_22372 (AllWinning.cons node_21756 (AllWinning.cons node_21160 (AllWinning.nil))))))))))))

theorem node_23399 : Outcome ⟨18, 13, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 7, 2⟩, ⟨16, 13, 7, 4⟩, ⟨15, 13, 7, 6⟩, ⟨14, 13, 7, 8⟩, ⟨13, 13, 7, 10⟩, ⟨12, 13, 7, 12⟩, ⟨18, 12, 7, 2⟩, ⟨18, 11, 7, 4⟩, ⟨18, 10, 7, 6⟩, ⟨18, 9, 7, 8⟩, ⟨18, 8, 7, 10⟩, ⟨18, 7, 7, 12⟩, ⟨18, 13, 6, 2⟩, ⟨18, 13, 5, 4⟩, ⟨18, 13, 4, 6⟩, ⟨18, 13, 3, 8⟩, ⟨18, 13, 2, 10⟩, ⟨18, 13, 1, 12⟩]
  exact AllWinning.cons node_22898 (AllWinning.cons node_22303 (AllWinning.cons node_21650 (AllWinning.cons node_20963 (AllWinning.cons node_20163 (AllWinning.cons node_19335 (AllWinning.cons node_22920 (AllWinning.cons node_22369 (AllWinning.cons node_21750 (AllWinning.cons node_21154 (AllWinning.cons node_20364 (AllWinning.cons node_19642 (AllWinning.cons node_22921 (AllWinning.cons node_22372 (AllWinning.cons node_21756 (AllWinning.cons node_21160 (AllWinning.cons node_20374 (AllWinning.cons node_19653 (AllWinning.nil))))))))))))))))))

theorem node_23400 : Outcome ⟨18, 13, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 7, 2⟩, ⟨16, 13, 7, 4⟩, ⟨15, 13, 7, 6⟩, ⟨14, 13, 7, 8⟩, ⟨13, 13, 7, 10⟩, ⟨12, 13, 7, 12⟩, ⟨11, 13, 7, 14⟩, ⟨10, 13, 7, 16⟩, ⟨18, 12, 7, 2⟩, ⟨18, 11, 7, 4⟩, ⟨18, 10, 7, 6⟩, ⟨18, 9, 7, 8⟩, ⟨18, 8, 7, 10⟩, ⟨18, 7, 7, 12⟩, ⟨18, 6, 7, 14⟩, ⟨18, 5, 7, 16⟩, ⟨18, 13, 6, 2⟩, ⟨18, 13, 5, 4⟩, ⟨18, 13, 4, 6⟩, ⟨18, 13, 3, 8⟩, ⟨18, 13, 2, 10⟩, ⟨18, 13, 1, 12⟩, ⟨18, 13, 0, 14⟩]
  exact AllWinning.cons node_22898 (AllWinning.cons node_22303 (AllWinning.cons node_21650 (AllWinning.cons node_20963 (AllWinning.cons node_20163 (AllWinning.cons node_19335 (AllWinning.cons node_18399 (AllWinning.cons node_17441 (AllWinning.cons node_22920 (AllWinning.cons node_22369 (AllWinning.cons node_21750 (AllWinning.cons node_21154 (AllWinning.cons node_20364 (AllWinning.cons node_19642 (AllWinning.cons node_18753 (AllWinning.cons node_17837 (AllWinning.cons node_22921 (AllWinning.cons node_22372 (AllWinning.cons node_21756 (AllWinning.cons node_21160 (AllWinning.cons node_20374 (AllWinning.cons node_19653 (AllWinning.cons node_18774 (AllWinning.nil)))))))))))))))))))))))

theorem node_23401 : Outcome ⟨18, 14, 6, 4⟩ true :=
  Outcome.win (q := ⟨18, 10, 6, 8⟩) (by decide) node_21155

theorem node_23402 : Outcome ⟨18, 14, 6, 12⟩ true :=
  Outcome.win (q := ⟨13, 14, 6, 10⟩) (by decide) node_20168

theorem node_23403 : Outcome ⟨18, 15, 5, 6⟩ true :=
  Outcome.win (q := ⟨18, 12, 5, 6⟩) (by decide) node_21753

theorem node_23404 : Outcome ⟨18, 18, 2, 6⟩ true :=
  Outcome.win (q := ⟨16, 18, 2, 4⟩) (by decide) node_22314

theorem node_23405 : Outcome ⟨18, 18, 2, 12⟩ true :=
  Outcome.win (q := ⟨16, 18, 2, 4⟩) (by decide) node_22314

theorem node_23406 : Outcome ⟨18, 19, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 19, 1, 2⟩, ⟨16, 19, 1, 4⟩, ⟨18, 18, 1, 2⟩, ⟨18, 17, 1, 4⟩, ⟨18, 19, 0, 2⟩]
  exact AllWinning.cons node_22907 (AllWinning.cons node_22317 (AllWinning.cons node_22924 (AllWinning.cons node_22379 (AllWinning.cons node_22926 (AllWinning.nil)))))

theorem node_23407 : Outcome ⟨19, 0, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 0, 19, 2⟩, ⟨17, 0, 19, 4⟩, ⟨16, 0, 19, 6⟩, ⟨15, 0, 19, 8⟩, ⟨14, 0, 19, 10⟩, ⟨13, 0, 19, 12⟩, ⟨19, 0, 18, 2⟩, ⟨19, 0, 17, 4⟩, ⟨19, 0, 16, 6⟩, ⟨19, 0, 15, 8⟩, ⟨19, 0, 14, 10⟩, ⟨19, 0, 13, 12⟩]
  exact AllWinning.cons node_22908 (AllWinning.cons node_22318 (AllWinning.cons node_21665 (AllWinning.cons node_20984 (AllWinning.cons node_20186 (AllWinning.cons node_19354 (AllWinning.cons node_22927 (AllWinning.cons node_22381 (AllWinning.cons node_21761 (AllWinning.cons node_21164 (AllWinning.cons node_20381 (AllWinning.cons node_19657 (AllWinning.nil))))))))))))

theorem node_23408 : Outcome ⟨19, 0, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 0, 19, 2⟩, ⟨17, 0, 19, 4⟩, ⟨16, 0, 19, 6⟩, ⟨15, 0, 19, 8⟩, ⟨14, 0, 19, 10⟩, ⟨13, 0, 19, 12⟩, ⟨12, 0, 19, 14⟩, ⟨11, 0, 19, 16⟩, ⟨10, 0, 19, 18⟩, ⟨9, 0, 19, 20⟩, ⟨19, 0, 18, 2⟩, ⟨19, 0, 17, 4⟩, ⟨19, 0, 16, 6⟩, ⟨19, 0, 15, 8⟩, ⟨19, 0, 14, 10⟩, ⟨19, 0, 13, 12⟩, ⟨19, 0, 12, 14⟩, ⟨19, 0, 11, 16⟩, ⟨19, 0, 10, 18⟩, ⟨19, 0, 9, 20⟩]
  exact AllWinning.cons node_22908 (AllWinning.cons node_22318 (AllWinning.cons node_21665 (AllWinning.cons node_20984 (AllWinning.cons node_20186 (AllWinning.cons node_19354 (AllWinning.cons node_18419 (AllWinning.cons node_17468 (AllWinning.cons node_16488 (AllWinning.cons node_15390 (AllWinning.cons node_22927 (AllWinning.cons node_22381 (AllWinning.cons node_21761 (AllWinning.cons node_21164 (AllWinning.cons node_20381 (AllWinning.cons node_19657 (AllWinning.cons node_18777 (AllWinning.cons node_17857 (AllWinning.cons node_16939 (AllWinning.cons node_15879 (AllWinning.nil))))))))))))))))))))

theorem node_23409 : Outcome ⟨19, 0, 19, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 0, 19, 2⟩, ⟨17, 0, 19, 4⟩, ⟨16, 0, 19, 6⟩, ⟨15, 0, 19, 8⟩, ⟨14, 0, 19, 10⟩, ⟨13, 0, 19, 12⟩, ⟨12, 0, 19, 14⟩, ⟨11, 0, 19, 16⟩, ⟨10, 0, 19, 18⟩, ⟨9, 0, 19, 20⟩, ⟨8, 0, 19, 22⟩, ⟨7, 0, 19, 24⟩, ⟨6, 0, 19, 26⟩, ⟨5, 0, 19, 28⟩, ⟨19, 0, 18, 2⟩, ⟨19, 0, 17, 4⟩, ⟨19, 0, 16, 6⟩, ⟨19, 0, 15, 8⟩, ⟨19, 0, 14, 10⟩, ⟨19, 0, 13, 12⟩, ⟨19, 0, 12, 14⟩, ⟨19, 0, 11, 16⟩, ⟨19, 0, 10, 18⟩, ⟨19, 0, 9, 20⟩, ⟨19, 0, 8, 22⟩, ⟨19, 0, 7, 24⟩, ⟨19, 0, 6, 26⟩, ⟨19, 0, 5, 28⟩]
  exact AllWinning.cons node_22908 (AllWinning.cons node_22318 (AllWinning.cons node_21665 (AllWinning.cons node_20984 (AllWinning.cons node_20186 (AllWinning.cons node_19354 (AllWinning.cons node_18419 (AllWinning.cons node_17468 (AllWinning.cons node_16488 (AllWinning.cons node_15390 (AllWinning.cons node_14401 (AllWinning.cons node_13365 (AllWinning.cons node_12348 (AllWinning.cons node_11300 (AllWinning.cons node_22927 (AllWinning.cons node_22381 (AllWinning.cons node_21761 (AllWinning.cons node_21164 (AllWinning.cons node_20381 (AllWinning.cons node_19657 (AllWinning.cons node_18777 (AllWinning.cons node_17857 (AllWinning.cons node_16939 (AllWinning.cons node_15879 (AllWinning.cons node_14902 (AllWinning.cons node_13930 (AllWinning.cons node_12960 (AllWinning.cons node_11947 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_23410 : Outcome ⟨19, 0, 19, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 0, 19, 2⟩, ⟨17, 0, 19, 4⟩, ⟨16, 0, 19, 6⟩, ⟨15, 0, 19, 8⟩, ⟨14, 0, 19, 10⟩, ⟨13, 0, 19, 12⟩, ⟨12, 0, 19, 14⟩, ⟨11, 0, 19, 16⟩, ⟨10, 0, 19, 18⟩, ⟨9, 0, 19, 20⟩, ⟨8, 0, 19, 22⟩, ⟨7, 0, 19, 24⟩, ⟨6, 0, 19, 26⟩, ⟨5, 0, 19, 28⟩, ⟨4, 0, 19, 30⟩, ⟨3, 0, 19, 32⟩, ⟨19, 0, 18, 2⟩, ⟨19, 0, 17, 4⟩, ⟨19, 0, 16, 6⟩, ⟨19, 0, 15, 8⟩, ⟨19, 0, 14, 10⟩, ⟨19, 0, 13, 12⟩, ⟨19, 0, 12, 14⟩, ⟨19, 0, 11, 16⟩, ⟨19, 0, 10, 18⟩, ⟨19, 0, 9, 20⟩, ⟨19, 0, 8, 22⟩, ⟨19, 0, 7, 24⟩, ⟨19, 0, 6, 26⟩, ⟨19, 0, 5, 28⟩, ⟨19, 0, 4, 30⟩, ⟨19, 0, 3, 32⟩]
  exact AllWinning.cons node_22908 (AllWinning.cons node_22318 (AllWinning.cons node_21665 (AllWinning.cons node_20984 (AllWinning.cons node_20186 (AllWinning.cons node_19354 (AllWinning.cons node_18419 (AllWinning.cons node_17468 (AllWinning.cons node_16488 (AllWinning.cons node_15390 (AllWinning.cons node_14401 (AllWinning.cons node_13365 (AllWinning.cons node_12348 (AllWinning.cons node_11300 (AllWinning.cons node_10169 (AllWinning.cons node_9127 (AllWinning.cons node_22927 (AllWinning.cons node_22381 (AllWinning.cons node_21761 (AllWinning.cons node_21164 (AllWinning.cons node_20381 (AllWinning.cons node_19657 (AllWinning.cons node_18777 (AllWinning.cons node_17857 (AllWinning.cons node_16939 (AllWinning.cons node_15879 (AllWinning.cons node_14902 (AllWinning.cons node_13930 (AllWinning.cons node_12960 (AllWinning.cons node_11947 (AllWinning.cons node_10958 (AllWinning.cons node_9862 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_23411 : Outcome ⟨19, 2, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 2, 17, 2⟩, ⟨17, 2, 17, 4⟩, ⟨16, 2, 17, 6⟩, ⟨15, 2, 17, 8⟩, ⟨14, 2, 17, 10⟩, ⟨13, 2, 17, 12⟩, ⟨19, 1, 17, 2⟩, ⟨19, 0, 17, 4⟩, ⟨19, 2, 16, 2⟩, ⟨19, 2, 15, 4⟩, ⟨19, 2, 14, 6⟩, ⟨19, 2, 13, 8⟩, ⟨19, 2, 12, 10⟩, ⟨19, 2, 11, 12⟩]
  exact AllWinning.cons node_22911 (AllWinning.cons node_22320 (AllWinning.cons node_21668 (AllWinning.cons node_20988 (AllWinning.cons node_20191 (AllWinning.cons node_19360 (AllWinning.cons node_22928 (AllWinning.cons node_22381 (AllWinning.cons node_22929 (AllWinning.cons node_22382 (AllWinning.cons node_21763 (AllWinning.cons node_21167 (AllWinning.cons node_20385 (AllWinning.cons node_19663 (AllWinning.nil))))))))))))))

theorem node_23412 : Outcome ⟨19, 6, 13, 4⟩ true :=
  Outcome.win (q := ⟨19, 5, 13, 2⟩) (by decide) node_22932

theorem node_23413 : Outcome ⟨19, 8, 11, 4⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 4⟩) (by decide) node_22332

theorem node_23414 : Outcome ⟨19, 9, 10, 4⟩ true :=
  Outcome.win (q := ⟨19, 5, 10, 8⟩) (by decide) node_21172

theorem node_23415 : Outcome ⟨19, 10, 9, 4⟩ true :=
  Outcome.win (q := ⟨19, 10, 5, 8⟩) (by decide) node_21179

theorem node_23416 : Outcome ⟨19, 11, 8, 4⟩ true :=
  Outcome.win (q := ⟨17, 11, 8, 4⟩) (by decide) node_22340

theorem node_23417 : Outcome ⟨19, 13, 6, 4⟩ true :=
  Outcome.win (q := ⟨19, 13, 5, 2⟩) (by decide) node_22938

theorem node_23418 : Outcome ⟨19, 17, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 17, 2, 2⟩, ⟨17, 17, 2, 4⟩, ⟨16, 17, 2, 6⟩, ⟨15, 17, 2, 8⟩, ⟨14, 17, 2, 10⟩, ⟨13, 17, 2, 12⟩, ⟨19, 16, 2, 2⟩, ⟨19, 15, 2, 4⟩, ⟨19, 14, 2, 6⟩, ⟨19, 13, 2, 8⟩, ⟨19, 12, 2, 10⟩, ⟨19, 11, 2, 12⟩, ⟨19, 17, 1, 2⟩, ⟨19, 17, 0, 4⟩]
  exact AllWinning.cons node_22923 (AllWinning.cons node_22349 (AllWinning.cons node_21697 (AllWinning.cons node_21038 (AllWinning.cons node_20235 (AllWinning.cons node_19402 (AllWinning.cons node_22942 (AllWinning.cons node_22397 (AllWinning.cons node_21774 (AllWinning.cons node_21184 (AllWinning.cons node_20397 (AllWinning.cons node_19682 (AllWinning.cons node_22943 (AllWinning.cons node_22398 (AllWinning.nil))))))))))))))

theorem node_23419 : Outcome ⟨19, 19, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 0, 2⟩, ⟨17, 19, 0, 4⟩, ⟨16, 19, 0, 6⟩, ⟨15, 19, 0, 8⟩, ⟨14, 19, 0, 10⟩, ⟨13, 19, 0, 12⟩, ⟨19, 18, 0, 2⟩, ⟨19, 17, 0, 4⟩, ⟨19, 16, 0, 6⟩, ⟨19, 15, 0, 8⟩, ⟨19, 14, 0, 10⟩, ⟨19, 13, 0, 12⟩]
  exact AllWinning.cons node_22926 (AllWinning.cons node_22352 (AllWinning.cons node_21700 (AllWinning.cons node_21041 (AllWinning.cons node_20241 (AllWinning.cons node_19407 (AllWinning.cons node_22944 (AllWinning.cons node_22398 (AllWinning.cons node_21775 (AllWinning.cons node_21187 (AllWinning.cons node_20402 (AllWinning.cons node_19687 (AllWinning.nil))))))))))))

theorem node_23420 : Outcome ⟨19, 19, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 0, 2⟩, ⟨17, 19, 0, 4⟩, ⟨16, 19, 0, 6⟩, ⟨15, 19, 0, 8⟩, ⟨14, 19, 0, 10⟩, ⟨13, 19, 0, 12⟩, ⟨12, 19, 0, 14⟩, ⟨11, 19, 0, 16⟩, ⟨10, 19, 0, 18⟩, ⟨9, 19, 0, 20⟩, ⟨19, 18, 0, 2⟩, ⟨19, 17, 0, 4⟩, ⟨19, 16, 0, 6⟩, ⟨19, 15, 0, 8⟩, ⟨19, 14, 0, 10⟩, ⟨19, 13, 0, 12⟩, ⟨19, 12, 0, 14⟩, ⟨19, 11, 0, 16⟩, ⟨19, 10, 0, 18⟩, ⟨19, 9, 0, 20⟩]
  exact AllWinning.cons node_22926 (AllWinning.cons node_22352 (AllWinning.cons node_21700 (AllWinning.cons node_21041 (AllWinning.cons node_20241 (AllWinning.cons node_19407 (AllWinning.cons node_18476 (AllWinning.cons node_17516 (AllWinning.cons node_16542 (AllWinning.cons node_15447 (AllWinning.cons node_22944 (AllWinning.cons node_22398 (AllWinning.cons node_21775 (AllWinning.cons node_21187 (AllWinning.cons node_20402 (AllWinning.cons node_19687 (AllWinning.cons node_18799 (AllWinning.cons node_17878 (AllWinning.cons node_16969 (AllWinning.cons node_15900 (AllWinning.nil))))))))))))))))))))

theorem node_23421 : Outcome ⟨19, 19, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 0, 2⟩, ⟨17, 19, 0, 4⟩, ⟨16, 19, 0, 6⟩, ⟨15, 19, 0, 8⟩, ⟨14, 19, 0, 10⟩, ⟨13, 19, 0, 12⟩, ⟨12, 19, 0, 14⟩, ⟨11, 19, 0, 16⟩, ⟨10, 19, 0, 18⟩, ⟨9, 19, 0, 20⟩, ⟨8, 19, 0, 22⟩, ⟨7, 19, 0, 24⟩, ⟨6, 19, 0, 26⟩, ⟨5, 19, 0, 28⟩, ⟨19, 18, 0, 2⟩, ⟨19, 17, 0, 4⟩, ⟨19, 16, 0, 6⟩, ⟨19, 15, 0, 8⟩, ⟨19, 14, 0, 10⟩, ⟨19, 13, 0, 12⟩, ⟨19, 12, 0, 14⟩, ⟨19, 11, 0, 16⟩, ⟨19, 10, 0, 18⟩, ⟨19, 9, 0, 20⟩, ⟨19, 8, 0, 22⟩, ⟨19, 7, 0, 24⟩, ⟨19, 6, 0, 26⟩, ⟨19, 5, 0, 28⟩]
  exact AllWinning.cons node_22926 (AllWinning.cons node_22352 (AllWinning.cons node_21700 (AllWinning.cons node_21041 (AllWinning.cons node_20241 (AllWinning.cons node_19407 (AllWinning.cons node_18476 (AllWinning.cons node_17516 (AllWinning.cons node_16542 (AllWinning.cons node_15447 (AllWinning.cons node_14458 (AllWinning.cons node_13425 (AllWinning.cons node_12419 (AllWinning.cons node_11363 (AllWinning.cons node_22944 (AllWinning.cons node_22398 (AllWinning.cons node_21775 (AllWinning.cons node_21187 (AllWinning.cons node_20402 (AllWinning.cons node_19687 (AllWinning.cons node_18799 (AllWinning.cons node_17878 (AllWinning.cons node_16969 (AllWinning.cons node_15900 (AllWinning.cons node_14918 (AllWinning.cons node_13943 (AllWinning.cons node_12978 (AllWinning.cons node_11958 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_23422 : Outcome ⟨19, 19, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 0, 2⟩, ⟨17, 19, 0, 4⟩, ⟨16, 19, 0, 6⟩, ⟨15, 19, 0, 8⟩, ⟨14, 19, 0, 10⟩, ⟨13, 19, 0, 12⟩, ⟨12, 19, 0, 14⟩, ⟨11, 19, 0, 16⟩, ⟨10, 19, 0, 18⟩, ⟨9, 19, 0, 20⟩, ⟨8, 19, 0, 22⟩, ⟨7, 19, 0, 24⟩, ⟨6, 19, 0, 26⟩, ⟨5, 19, 0, 28⟩, ⟨4, 19, 0, 30⟩, ⟨3, 19, 0, 32⟩, ⟨19, 18, 0, 2⟩, ⟨19, 17, 0, 4⟩, ⟨19, 16, 0, 6⟩, ⟨19, 15, 0, 8⟩, ⟨19, 14, 0, 10⟩, ⟨19, 13, 0, 12⟩, ⟨19, 12, 0, 14⟩, ⟨19, 11, 0, 16⟩, ⟨19, 10, 0, 18⟩, ⟨19, 9, 0, 20⟩, ⟨19, 8, 0, 22⟩, ⟨19, 7, 0, 24⟩, ⟨19, 6, 0, 26⟩, ⟨19, 5, 0, 28⟩, ⟨19, 4, 0, 30⟩, ⟨19, 3, 0, 32⟩]
  exact AllWinning.cons node_22926 (AllWinning.cons node_22352 (AllWinning.cons node_21700 (AllWinning.cons node_21041 (AllWinning.cons node_20241 (AllWinning.cons node_19407 (AllWinning.cons node_18476 (AllWinning.cons node_17516 (AllWinning.cons node_16542 (AllWinning.cons node_15447 (AllWinning.cons node_14458 (AllWinning.cons node_13425 (AllWinning.cons node_12419 (AllWinning.cons node_11363 (AllWinning.cons node_10245 (AllWinning.cons node_9195 (AllWinning.cons node_22944 (AllWinning.cons node_22398 (AllWinning.cons node_21775 (AllWinning.cons node_21187 (AllWinning.cons node_20402 (AllWinning.cons node_19687 (AllWinning.cons node_18799 (AllWinning.cons node_17878 (AllWinning.cons node_16969 (AllWinning.cons node_15900 (AllWinning.cons node_14918 (AllWinning.cons node_13943 (AllWinning.cons node_12978 (AllWinning.cons node_11958 (AllWinning.cons node_10973 (AllWinning.cons node_9870 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_23423 : Outcome ⟨0, 19, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 2⟩) (by decide) node_22946

theorem node_23424 : Outcome ⟨0, 20, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 2⟩) (by decide) node_22946

theorem node_23425 : Outcome ⟨1, 18, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 20, 4⟩) (by decide) node_22404

theorem node_23426 : Outcome ⟨1, 18, 20, 16⟩ true :=
  Outcome.win (q := ⟨1, 16, 20, 4⟩) (by decide) node_22404

theorem node_23427 : Outcome ⟨1, 19, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 2⟩) (by decide) node_22946

theorem node_23428 : Outcome ⟨1, 19, 19, 8⟩ true :=
  Outcome.win (q := ⟨0, 19, 19, 2⟩) (by decide) node_22946

theorem node_23429 : Outcome ⟨1, 20, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 20, 16, 4⟩) (by decide) node_22412

theorem node_23430 : Outcome ⟨1, 20, 18, 16⟩ true :=
  Outcome.win (q := ⟨1, 20, 16, 4⟩) (by decide) node_22412

theorem node_23431 : Outcome ⟨2, 17, 20, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 19, 2⟩) (by decide) node_22965

theorem node_23432 : Outcome ⟨2, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 19, 2⟩) (by decide) node_22952

theorem node_23433 : Outcome ⟨2, 18, 19, 4⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 6⟩) (by decide) node_21816

theorem node_23434 : Outcome ⟨2, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 18, 2⟩) (by decide) node_22957

theorem node_23435 : Outcome ⟨2, 19, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 16, 18, 6⟩) (by decide) node_21806

theorem node_23436 : Outcome ⟨2, 20, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 19, 17, 2⟩) (by decide) node_22972

theorem node_23437 : Outcome ⟨3, 16, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 20, 4⟩) (by decide) node_22404

theorem node_23438 : Outcome ⟨3, 16, 20, 8⟩ true :=
  Outcome.win (q := ⟨3, 12, 20, 8⟩) (by decide) node_21241

theorem node_23439 : Outcome ⟨3, 17, 19, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 19, 2⟩) (by decide) node_22965

theorem node_23440 : Outcome ⟨3, 17, 19, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 19, 2⟩) (by decide) node_22965

theorem node_23441 : Outcome ⟨3, 18, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 18, 18, 2⟩, ⟨1, 18, 18, 4⟩, ⟨3, 17, 18, 2⟩, ⟨3, 16, 18, 4⟩, ⟨3, 18, 17, 2⟩, ⟨3, 18, 16, 4⟩]
  exact AllWinning.cons node_22968 (AllWinning.cons node_22408 (AllWinning.cons node_22980 (AllWinning.cons node_22425 (AllWinning.cons node_22982 (AllWinning.cons node_22429 (AllWinning.nil))))))

theorem node_23442 : Outcome ⟨3, 18, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 6⟩) (by decide) node_21782

theorem node_23443 : Outcome ⟨3, 18, 18, 10⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 6⟩) (by decide) node_21782

theorem node_23444 : Outcome ⟨3, 19, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 19, 17, 2⟩) (by decide) node_22972

theorem node_23445 : Outcome ⟨3, 19, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 19, 17, 2⟩) (by decide) node_22972

theorem node_23446 : Outcome ⟨3, 20, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 20, 16, 4⟩) (by decide) node_22412

theorem node_23447 : Outcome ⟨3, 20, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 20, 12, 8⟩) (by decide) node_21255

theorem node_23448 : Outcome ⟨4, 15, 20, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 20, 4⟩) (by decide) node_22434

theorem node_23449 : Outcome ⟨4, 15, 20, 4⟩ true :=
  Outcome.win (q := ⟨4, 15, 17, 6⟩) (by decide) node_21859

theorem node_23450 : Outcome ⟨4, 15, 20, 18⟩ true :=
  Outcome.win (q := ⟨4, 15, 17, 6⟩) (by decide) node_21859

theorem node_23451 : Outcome ⟨4, 16, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 4⟩) (by decide) node_22437

theorem node_23452 : Outcome ⟨4, 16, 19, 4⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 4⟩) (by decide) node_22437

theorem node_23453 : Outcome ⟨4, 17, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 17, 18, 2⟩, ⟨2, 17, 18, 4⟩, ⟨4, 16, 18, 2⟩, ⟨4, 15, 18, 4⟩, ⟨4, 17, 17, 2⟩, ⟨4, 17, 16, 4⟩]
  exact AllWinning.cons node_22980 (AllWinning.cons node_22417 (AllWinning.cons node_22989 (AllWinning.cons node_22442 (AllWinning.cons node_22991 (AllWinning.cons node_22445 (AllWinning.nil))))))

theorem node_23454 : Outcome ⟨4, 17, 18, 4⟩ true :=
  Outcome.win (q := ⟨4, 17, 15, 6⟩) (by decide) node_21864

end RQ9F1
