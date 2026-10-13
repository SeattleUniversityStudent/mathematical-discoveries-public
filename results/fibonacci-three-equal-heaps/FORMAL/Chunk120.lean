import Chunk119
set_option autoImplicit false
namespace RQ9F1

theorem node_25184 : Outcome ⟨14, 12, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 12, 18, 2⟩, ⟨12, 12, 18, 4⟩, ⟨11, 12, 18, 6⟩, ⟨10, 12, 18, 8⟩, ⟨9, 12, 18, 10⟩, ⟨8, 12, 18, 12⟩, ⟨14, 11, 18, 2⟩, ⟨14, 10, 18, 4⟩, ⟨14, 9, 18, 6⟩, ⟨14, 8, 18, 8⟩, ⟨14, 7, 18, 10⟩, ⟨14, 6, 18, 12⟩, ⟨14, 12, 17, 2⟩, ⟨14, 12, 16, 4⟩, ⟨14, 12, 15, 6⟩, ⟨14, 12, 14, 8⟩, ⟨14, 12, 13, 10⟩, ⟨14, 12, 12, 12⟩]
  exact AllWinning.cons node_24934 (AllWinning.cons node_24638 (AllWinning.cons node_24334 (AllWinning.cons node_23933 (AllWinning.cons node_23532 (AllWinning.cons node_23069 (AllWinning.cons node_24954 (AllWinning.cons node_24686 (AllWinning.cons node_24395 (AllWinning.cons node_24052 (AllWinning.cons node_23659 (AllWinning.cons node_23251 (AllWinning.cons node_24955 (AllWinning.cons node_24692 (AllWinning.cons node_24403 (AllWinning.cons node_24061 (AllWinning.cons node_23670 (AllWinning.cons node_23263 (AllWinning.nil))))))))))))))))))

theorem node_25185 : Outcome ⟨14, 12, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 12, 18, 2⟩, ⟨12, 12, 18, 4⟩, ⟨11, 12, 18, 6⟩, ⟨10, 12, 18, 8⟩, ⟨9, 12, 18, 10⟩, ⟨8, 12, 18, 12⟩, ⟨7, 12, 18, 14⟩, ⟨6, 12, 18, 16⟩, ⟨14, 11, 18, 2⟩, ⟨14, 10, 18, 4⟩, ⟨14, 9, 18, 6⟩, ⟨14, 8, 18, 8⟩, ⟨14, 7, 18, 10⟩, ⟨14, 6, 18, 12⟩, ⟨14, 5, 18, 14⟩, ⟨14, 4, 18, 16⟩, ⟨14, 12, 17, 2⟩, ⟨14, 12, 16, 4⟩, ⟨14, 12, 15, 6⟩, ⟨14, 12, 14, 8⟩, ⟨14, 12, 13, 10⟩, ⟨14, 12, 12, 12⟩, ⟨14, 12, 11, 14⟩, ⟨14, 12, 10, 16⟩]
  exact AllWinning.cons node_24934 (AllWinning.cons node_24638 (AllWinning.cons node_24334 (AllWinning.cons node_23933 (AllWinning.cons node_23532 (AllWinning.cons node_23069 (AllWinning.cons node_22510 (AllWinning.cons node_21904 (AllWinning.cons node_24954 (AllWinning.cons node_24686 (AllWinning.cons node_24395 (AllWinning.cons node_24052 (AllWinning.cons node_23659 (AllWinning.cons node_23251 (AllWinning.cons node_22748 (AllWinning.cons node_22179 (AllWinning.cons node_24955 (AllWinning.cons node_24692 (AllWinning.cons node_24403 (AllWinning.cons node_24061 (AllWinning.cons node_23670 (AllWinning.cons node_23263 (AllWinning.cons node_22771 (AllWinning.cons node_22199 (AllWinning.nil))))))))))))))))))))))))

theorem node_25186 : Outcome ⟨14, 13, 17, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 17, 4⟩) (by decide) node_24640

theorem node_25187 : Outcome ⟨14, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨12, 13, 17, 4⟩) (by decide) node_24640

theorem node_25188 : Outcome ⟨14, 13, 17, 6⟩ true :=
  Outcome.win (q := ⟨12, 13, 17, 4⟩) (by decide) node_24640

theorem node_25189 : Outcome ⟨14, 14, 16, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 14, 4⟩) (by decide) node_24697

theorem node_25190 : Outcome ⟨14, 14, 16, 6⟩ true :=
  Outcome.win (q := ⟨10, 14, 16, 8⟩) (by decide) node_23939

theorem node_25191 : Outcome ⟨14, 15, 15, 2⟩ true :=
  Outcome.win (q := ⟨14, 13, 15, 4⟩) (by decide) node_24694

theorem node_25192 : Outcome ⟨14, 16, 14, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 14, 4⟩) (by decide) node_24697

theorem node_25193 : Outcome ⟨14, 16, 14, 6⟩ true :=
  Outcome.win (q := ⟨10, 16, 14, 8⟩) (by decide) node_23948

theorem node_25194 : Outcome ⟨14, 17, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 17, 13, 4⟩) (by decide) node_24649

theorem node_25195 : Outcome ⟨14, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨12, 17, 13, 4⟩) (by decide) node_24649

theorem node_25196 : Outcome ⟨14, 17, 13, 6⟩ true :=
  Outcome.win (q := ⟨12, 17, 13, 4⟩) (by decide) node_24649

theorem node_25197 : Outcome ⟨14, 18, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 12, 2⟩, ⟨12, 18, 12, 4⟩, ⟨11, 18, 12, 6⟩, ⟨10, 18, 12, 8⟩, ⟨14, 17, 12, 2⟩, ⟨14, 16, 12, 4⟩, ⟨14, 15, 12, 6⟩, ⟨14, 14, 12, 8⟩, ⟨14, 18, 11, 2⟩, ⟨14, 18, 10, 4⟩, ⟨14, 18, 9, 6⟩, ⟨14, 18, 8, 8⟩]
  exact AllWinning.cons node_24948 (AllWinning.cons node_24652 (AllWinning.cons node_24344 (AllWinning.cons node_23954 (AllWinning.cons node_24964 (AllWinning.cons node_24703 (AllWinning.cons node_24408 (AllWinning.cons node_24066 (AllWinning.cons node_24967 (AllWinning.cons node_24709 (AllWinning.cons node_24415 (AllWinning.cons node_24074 (AllWinning.nil))))))))))))

theorem node_25198 : Outcome ⟨14, 18, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 12, 2⟩, ⟨12, 18, 12, 4⟩, ⟨11, 18, 12, 6⟩, ⟨10, 18, 12, 8⟩, ⟨9, 18, 12, 10⟩, ⟨8, 18, 12, 12⟩, ⟨14, 17, 12, 2⟩, ⟨14, 16, 12, 4⟩, ⟨14, 15, 12, 6⟩, ⟨14, 14, 12, 8⟩, ⟨14, 13, 12, 10⟩, ⟨14, 12, 12, 12⟩, ⟨14, 18, 11, 2⟩, ⟨14, 18, 10, 4⟩, ⟨14, 18, 9, 6⟩, ⟨14, 18, 8, 8⟩, ⟨14, 18, 7, 10⟩, ⟨14, 18, 6, 12⟩]
  exact AllWinning.cons node_24948 (AllWinning.cons node_24652 (AllWinning.cons node_24344 (AllWinning.cons node_23954 (AllWinning.cons node_23546 (AllWinning.cons node_23079 (AllWinning.cons node_24964 (AllWinning.cons node_24703 (AllWinning.cons node_24408 (AllWinning.cons node_24066 (AllWinning.cons node_23673 (AllWinning.cons node_23263 (AllWinning.cons node_24967 (AllWinning.cons node_24709 (AllWinning.cons node_24415 (AllWinning.cons node_24074 (AllWinning.cons node_23684 (AllWinning.cons node_23274 (AllWinning.nil))))))))))))))))))

theorem node_25199 : Outcome ⟨14, 18, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 18, 12, 2⟩, ⟨12, 18, 12, 4⟩, ⟨11, 18, 12, 6⟩, ⟨10, 18, 12, 8⟩, ⟨9, 18, 12, 10⟩, ⟨8, 18, 12, 12⟩, ⟨7, 18, 12, 14⟩, ⟨6, 18, 12, 16⟩, ⟨14, 17, 12, 2⟩, ⟨14, 16, 12, 4⟩, ⟨14, 15, 12, 6⟩, ⟨14, 14, 12, 8⟩, ⟨14, 13, 12, 10⟩, ⟨14, 12, 12, 12⟩, ⟨14, 11, 12, 14⟩, ⟨14, 10, 12, 16⟩, ⟨14, 18, 11, 2⟩, ⟨14, 18, 10, 4⟩, ⟨14, 18, 9, 6⟩, ⟨14, 18, 8, 8⟩, ⟨14, 18, 7, 10⟩, ⟨14, 18, 6, 12⟩, ⟨14, 18, 5, 14⟩, ⟨14, 18, 4, 16⟩]
  exact AllWinning.cons node_24948 (AllWinning.cons node_24652 (AllWinning.cons node_24344 (AllWinning.cons node_23954 (AllWinning.cons node_23546 (AllWinning.cons node_23079 (AllWinning.cons node_22524 (AllWinning.cons node_21923 (AllWinning.cons node_24964 (AllWinning.cons node_24703 (AllWinning.cons node_24408 (AllWinning.cons node_24066 (AllWinning.cons node_23673 (AllWinning.cons node_23263 (AllWinning.cons node_22768 (AllWinning.cons node_22194 (AllWinning.cons node_24967 (AllWinning.cons node_24709 (AllWinning.cons node_24415 (AllWinning.cons node_24074 (AllWinning.cons node_23684 (AllWinning.cons node_23274 (AllWinning.cons node_22791 (AllWinning.cons node_22212 (AllWinning.nil))))))))))))))))))))))))

theorem node_25200 : Outcome ⟨14, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨14, 17, 11, 4⟩) (by decide) node_24706

theorem node_25201 : Outcome ⟨15, 9, 20, 4⟩ true :=
  Outcome.win (q := ⟨15, 6, 20, 6⟩) (by decide) node_24418

theorem node_25202 : Outcome ⟨15, 9, 20, 8⟩ true :=
  Outcome.win (q := ⟨9, 9, 20, 12⟩) (by decide) node_23087

theorem node_25203 : Outcome ⟨15, 10, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 10, 19, 2⟩, ⟨13, 10, 19, 4⟩, ⟨15, 9, 19, 2⟩, ⟨15, 8, 19, 4⟩, ⟨15, 10, 18, 2⟩, ⟨15, 10, 17, 4⟩]
  exact AllWinning.cons node_24953 (AllWinning.cons node_24657 (AllWinning.cons node_24970 (AllWinning.cons node_24713 (AllWinning.cons node_24971 (AllWinning.cons node_24718 (AllWinning.nil))))))

theorem node_25204 : Outcome ⟨15, 11, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 18, 4⟩) (by decide) node_24716

theorem node_25205 : Outcome ⟨15, 11, 18, 10⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 16⟩) (by decide) node_22226

theorem node_25206 : Outcome ⟨15, 12, 17, 2⟩ true :=
  Outcome.win (q := ⟨13, 12, 17, 4⟩) (by decide) node_24660

theorem node_25207 : Outcome ⟨15, 13, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 4⟩) (by decide) node_24724

theorem node_25208 : Outcome ⟨15, 13, 16, 8⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 4⟩) (by decide) node_24724

theorem node_25209 : Outcome ⟨15, 13, 16, 10⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 4⟩) (by decide) node_24724

theorem node_25210 : Outcome ⟨15, 14, 15, 2⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 4⟩) (by decide) node_24665

theorem node_25211 : Outcome ⟨15, 15, 14, 2⟩ true :=
  Outcome.win (q := ⟨13, 15, 14, 4⟩) (by decide) node_24670

theorem node_25212 : Outcome ⟨15, 16, 13, 2⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 4⟩) (by decide) node_24728

theorem node_25213 : Outcome ⟨15, 16, 13, 8⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 4⟩) (by decide) node_24728

theorem node_25214 : Outcome ⟨15, 16, 13, 10⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 4⟩) (by decide) node_24728

theorem node_25215 : Outcome ⟨15, 17, 12, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 12, 4⟩) (by decide) node_24677

theorem node_25216 : Outcome ⟨15, 17, 12, 4⟩ true :=
  Outcome.win (q := ⟨13, 17, 12, 4⟩) (by decide) node_24677

theorem node_25217 : Outcome ⟨15, 18, 11, 10⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 16⟩) (by decide) node_22273

theorem node_25218 : Outcome ⟨15, 19, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 19, 10, 2⟩, ⟨13, 19, 10, 4⟩, ⟨15, 18, 10, 2⟩, ⟨15, 17, 10, 4⟩, ⟨15, 19, 9, 2⟩, ⟨15, 19, 8, 4⟩]
  exact AllWinning.cons node_24968 (AllWinning.cons node_24680 (AllWinning.cons node_24988 (AllWinning.cons node_24737 (AllWinning.cons node_24990 (AllWinning.cons node_24740 (AllWinning.nil))))))

theorem node_25219 : Outcome ⟨15, 19, 10, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 10, 8⟩) (by decide) node_24106

theorem node_25220 : Outcome ⟨15, 20, 9, 8⟩ true :=
  Outcome.win (q := ⟨9, 20, 9, 12⟩) (by decide) node_23117

theorem node_25221 : Outcome ⟨16, 9, 19, 4⟩ true :=
  Outcome.win (q := ⟨14, 9, 19, 4⟩) (by decide) node_24685

theorem node_25222 : Outcome ⟨16, 10, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 10, 18, 2⟩, ⟨14, 10, 18, 4⟩, ⟨16, 9, 18, 2⟩, ⟨16, 8, 18, 4⟩, ⟨16, 10, 17, 2⟩, ⟨16, 10, 16, 4⟩]
  exact AllWinning.cons node_24971 (AllWinning.cons node_24686 (AllWinning.cons node_24993 (AllWinning.cons node_24745 (AllWinning.cons node_24995 (AllWinning.cons node_24748 (AllWinning.nil))))))

theorem node_25223 : Outcome ⟨16, 10, 18, 10⟩ true :=
  Outcome.win (q := ⟨16, 2, 18, 16⟩) (by decide) node_22280

theorem node_25224 : Outcome ⟨16, 11, 17, 2⟩ true :=
  Outcome.win (q := ⟨14, 11, 17, 4⟩) (by decide) node_24688

theorem node_25225 : Outcome ⟨16, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨14, 11, 17, 4⟩) (by decide) node_24688

theorem node_25226 : Outcome ⟨16, 12, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 12, 16, 2⟩) (by decide) node_24974

theorem node_25227 : Outcome ⟨16, 13, 15, 2⟩ true :=
  Outcome.win (q := ⟨14, 13, 15, 4⟩) (by decide) node_24694

theorem node_25228 : Outcome ⟨16, 13, 15, 10⟩ true :=
  Outcome.win (q := ⟨14, 13, 15, 4⟩) (by decide) node_24694

theorem node_25229 : Outcome ⟨16, 14, 14, 2⟩ true :=
  Outcome.win (q := ⟨14, 14, 14, 4⟩) (by decide) node_24697

theorem node_25230 : Outcome ⟨16, 15, 13, 2⟩ true :=
  Outcome.win (q := ⟨14, 15, 13, 4⟩) (by decide) node_24700

theorem node_25231 : Outcome ⟨16, 15, 13, 10⟩ true :=
  Outcome.win (q := ⟨14, 15, 13, 4⟩) (by decide) node_24700

theorem node_25232 : Outcome ⟨16, 16, 12, 2⟩ true :=
  Outcome.win (q := ⟨15, 16, 12, 2⟩) (by decide) node_24983

theorem node_25233 : Outcome ⟨16, 17, 11, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 11, 4⟩) (by decide) node_24706

theorem node_25234 : Outcome ⟨16, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨14, 17, 11, 4⟩) (by decide) node_24706

theorem node_25235 : Outcome ⟨16, 18, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 18, 10, 2⟩, ⟨14, 18, 10, 4⟩, ⟨16, 17, 10, 2⟩, ⟨16, 16, 10, 4⟩, ⟨16, 18, 9, 2⟩, ⟨16, 18, 8, 4⟩]
  exact AllWinning.cons node_24988 (AllWinning.cons node_24709 (AllWinning.cons node_25007 (AllWinning.cons node_24762 (AllWinning.cons node_25008 (AllWinning.cons node_24765 (AllWinning.nil))))))

theorem node_25236 : Outcome ⟨16, 18, 10, 10⟩ true :=
  Outcome.win (q := ⟨16, 18, 2, 16⟩) (by decide) node_22316

theorem node_25237 : Outcome ⟨16, 19, 9, 4⟩ true :=
  Outcome.win (q := ⟨14, 19, 9, 4⟩) (by decide) node_24711

theorem node_25238 : Outcome ⟨17, 8, 19, 4⟩ true :=
  Outcome.win (q := ⟨13, 8, 19, 8⟩) (by decide) node_24014

theorem node_25239 : Outcome ⟨17, 10, 17, 2⟩ true :=
  Outcome.win (q := ⟨17, 8, 17, 4⟩) (by decide) node_24770

theorem node_25240 : Outcome ⟨17, 10, 17, 6⟩ true :=
  Outcome.win (q := ⟨17, 8, 17, 4⟩) (by decide) node_24770

theorem node_25241 : Outcome ⟨17, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 16, 4⟩) (by decide) node_24772

theorem node_25242 : Outcome ⟨17, 11, 16, 4⟩ true :=
  Outcome.win (q := ⟨17, 9, 16, 4⟩) (by decide) node_24772

theorem node_25243 : Outcome ⟨17, 11, 16, 6⟩ true :=
  Outcome.win (q := ⟨17, 9, 16, 4⟩) (by decide) node_24772

theorem node_25244 : Outcome ⟨17, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨17, 12, 13, 4⟩) (by decide) node_24778

theorem node_25245 : Outcome ⟨17, 12, 15, 4⟩ true :=
  Outcome.win (q := ⟨17, 12, 13, 4⟩) (by decide) node_24778

theorem node_25246 : Outcome ⟨17, 13, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 4⟩) (by decide) node_24724

theorem node_25247 : Outcome ⟨17, 13, 14, 6⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 4⟩) (by decide) node_24724

theorem node_25248 : Outcome ⟨17, 14, 13, 2⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 4⟩) (by decide) node_24728

theorem node_25249 : Outcome ⟨17, 14, 13, 4⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 4⟩) (by decide) node_24728

theorem node_25250 : Outcome ⟨17, 14, 13, 6⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 4⟩) (by decide) node_24728

theorem node_25251 : Outcome ⟨17, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨17, 14, 11, 4⟩) (by decide) node_24782

theorem node_25252 : Outcome ⟨17, 16, 11, 4⟩ true :=
  Outcome.win (q := ⟨17, 14, 11, 4⟩) (by decide) node_24782

theorem node_25253 : Outcome ⟨17, 16, 11, 6⟩ true :=
  Outcome.win (q := ⟨17, 14, 11, 4⟩) (by decide) node_24782

theorem node_25254 : Outcome ⟨17, 17, 10, 2⟩ true :=
  Outcome.win (q := ⟨17, 17, 8, 4⟩) (by decide) node_24787

theorem node_25255 : Outcome ⟨17, 17, 10, 6⟩ true :=
  Outcome.win (q := ⟨17, 17, 8, 4⟩) (by decide) node_24787

theorem node_25256 : Outcome ⟨17, 19, 8, 4⟩ true :=
  Outcome.win (q := ⟨13, 19, 8, 8⟩) (by decide) node_24046

theorem node_25257 : Outcome ⟨18, 7, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 7, 19, 2⟩, ⟨16, 7, 19, 4⟩, ⟨18, 6, 19, 2⟩, ⟨18, 5, 19, 4⟩, ⟨18, 7, 18, 2⟩, ⟨18, 7, 17, 4⟩]
  exact AllWinning.cons node_25011 (AllWinning.cons node_24743 (AllWinning.cons node_25033 (AllWinning.cons node_24789 (AllWinning.cons node_25034 (AllWinning.cons node_24791 (AllWinning.nil))))))

theorem node_25258 : Outcome ⟨18, 8, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 8, 18, 2⟩, ⟨16, 8, 18, 4⟩, ⟨18, 7, 18, 2⟩, ⟨18, 6, 18, 4⟩, ⟨18, 8, 17, 2⟩, ⟨18, 8, 16, 4⟩]
  exact AllWinning.cons node_25012 (AllWinning.cons node_24745 (AllWinning.cons node_25034 (AllWinning.cons node_24790 (AllWinning.cons node_25035 (AllWinning.cons node_24792 (AllWinning.nil))))))

theorem node_25259 : Outcome ⟨18, 8, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 8, 18, 2⟩, ⟨16, 8, 18, 4⟩, ⟨15, 8, 18, 6⟩, ⟨14, 8, 18, 8⟩, ⟨13, 8, 18, 10⟩, ⟨12, 8, 18, 12⟩, ⟨18, 7, 18, 2⟩, ⟨18, 6, 18, 4⟩, ⟨18, 5, 18, 6⟩, ⟨18, 4, 18, 8⟩, ⟨18, 3, 18, 10⟩, ⟨18, 2, 18, 12⟩, ⟨18, 8, 17, 2⟩, ⟨18, 8, 16, 4⟩, ⟨18, 8, 15, 6⟩, ⟨18, 8, 14, 8⟩, ⟨18, 8, 13, 10⟩, ⟨18, 8, 12, 12⟩]
  exact AllWinning.cons node_25012 (AllWinning.cons node_24745 (AllWinning.cons node_24422 (AllWinning.cons node_24052 (AllWinning.cons node_23625 (AllWinning.cons node_23177 (AllWinning.cons node_25034 (AllWinning.cons node_24790 (AllWinning.cons node_24493 (AllWinning.cons node_24178 (AllWinning.cons node_23772 (AllWinning.cons node_23379 (AllWinning.cons node_25035 (AllWinning.cons node_24792 (AllWinning.cons node_24496 (AllWinning.cons node_24184 (AllWinning.cons node_23779 (AllWinning.cons node_23390 (AllWinning.nil))))))))))))))))))

theorem node_25260 : Outcome ⟨18, 10, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 10, 16, 2⟩, ⟨16, 10, 16, 4⟩, ⟨18, 9, 16, 2⟩, ⟨18, 8, 16, 4⟩, ⟨18, 10, 15, 2⟩, ⟨18, 10, 14, 4⟩]
  exact AllWinning.cons node_25015 (AllWinning.cons node_24748 (AllWinning.cons node_25036 (AllWinning.cons node_24792 (AllWinning.cons node_25037 (AllWinning.cons node_24794 (AllWinning.nil))))))

theorem node_25261 : Outcome ⟨18, 12, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 12, 14, 2⟩, ⟨16, 12, 14, 4⟩, ⟨15, 12, 14, 6⟩, ⟨14, 12, 14, 8⟩, ⟨18, 11, 14, 2⟩, ⟨18, 10, 14, 4⟩, ⟨18, 9, 14, 6⟩, ⟨18, 8, 14, 8⟩, ⟨18, 12, 13, 2⟩, ⟨18, 12, 12, 4⟩, ⟨18, 12, 11, 6⟩, ⟨18, 12, 10, 8⟩]
  exact AllWinning.cons node_25018 (AllWinning.cons node_24754 (AllWinning.cons node_24430 (AllWinning.cons node_24061 (AllWinning.cons node_25038 (AllWinning.cons node_24794 (AllWinning.cons node_24498 (AllWinning.cons node_24184 (AllWinning.cons node_25039 (AllWinning.cons node_24797 (AllWinning.cons node_24501 (AllWinning.cons node_24190 (AllWinning.nil))))))))))))

theorem node_25262 : Outcome ⟨18, 12, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 12, 14, 2⟩, ⟨16, 12, 14, 4⟩, ⟨15, 12, 14, 6⟩, ⟨14, 12, 14, 8⟩, ⟨13, 12, 14, 10⟩, ⟨12, 12, 14, 12⟩, ⟨18, 11, 14, 2⟩, ⟨18, 10, 14, 4⟩, ⟨18, 9, 14, 6⟩, ⟨18, 8, 14, 8⟩, ⟨18, 7, 14, 10⟩, ⟨18, 6, 14, 12⟩, ⟨18, 12, 13, 2⟩, ⟨18, 12, 12, 4⟩, ⟨18, 12, 11, 6⟩, ⟨18, 12, 10, 8⟩, ⟨18, 12, 9, 10⟩, ⟨18, 12, 8, 12⟩]
  exact AllWinning.cons node_25018 (AllWinning.cons node_24754 (AllWinning.cons node_24430 (AllWinning.cons node_24061 (AllWinning.cons node_23634 (AllWinning.cons node_23188 (AllWinning.cons node_25038 (AllWinning.cons node_24794 (AllWinning.cons node_24498 (AllWinning.cons node_24184 (AllWinning.cons node_23777 (AllWinning.cons node_23383 (AllWinning.cons node_25039 (AllWinning.cons node_24797 (AllWinning.cons node_24501 (AllWinning.cons node_24190 (AllWinning.cons node_23785 (AllWinning.cons node_23396 (AllWinning.nil))))))))))))))))))

theorem node_25263 : Outcome ⟨18, 13, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 13, 2⟩, ⟨16, 13, 13, 4⟩, ⟨18, 12, 13, 2⟩, ⟨18, 11, 13, 4⟩, ⟨18, 13, 12, 2⟩, ⟨18, 13, 11, 4⟩]
  exact AllWinning.cons node_25021 (AllWinning.cons node_24755 (AllWinning.cons node_25039 (AllWinning.cons node_24795 (AllWinning.cons node_25040 (AllWinning.cons node_24798 (AllWinning.nil))))))

theorem node_25264 : Outcome ⟨18, 13, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 13, 13, 2⟩, ⟨16, 13, 13, 4⟩, ⟨15, 13, 13, 6⟩, ⟨14, 13, 13, 8⟩, ⟨18, 12, 13, 2⟩, ⟨18, 11, 13, 4⟩, ⟨18, 10, 13, 6⟩, ⟨18, 9, 13, 8⟩, ⟨18, 13, 12, 2⟩, ⟨18, 13, 11, 4⟩, ⟨18, 13, 10, 6⟩, ⟨18, 13, 9, 8⟩]
  exact AllWinning.cons node_25021 (AllWinning.cons node_24755 (AllWinning.cons node_24432 (AllWinning.cons node_24063 (AllWinning.cons node_25039 (AllWinning.cons node_24795 (AllWinning.cons node_24499 (AllWinning.cons node_24186 (AllWinning.cons node_25040 (AllWinning.cons node_24798 (AllWinning.cons node_24502 (AllWinning.cons node_24192 (AllWinning.nil))))))))))))

theorem node_25265 : Outcome ⟨18, 14, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 14, 12, 2⟩, ⟨16, 14, 12, 4⟩, ⟨15, 14, 12, 6⟩, ⟨14, 14, 12, 8⟩, ⟨13, 14, 12, 10⟩, ⟨12, 14, 12, 12⟩, ⟨18, 13, 12, 2⟩, ⟨18, 12, 12, 4⟩, ⟨18, 11, 12, 6⟩, ⟨18, 10, 12, 8⟩, ⟨18, 9, 12, 10⟩, ⟨18, 8, 12, 12⟩, ⟨18, 14, 11, 2⟩, ⟨18, 14, 10, 4⟩, ⟨18, 14, 9, 6⟩, ⟨18, 14, 8, 8⟩, ⟨18, 14, 7, 10⟩, ⟨18, 14, 6, 12⟩]
  exact AllWinning.cons node_25024 (AllWinning.cons node_24758 (AllWinning.cons node_24436 (AllWinning.cons node_24066 (AllWinning.cons node_23643 (AllWinning.cons node_23194 (AllWinning.cons node_25040 (AllWinning.cons node_24797 (AllWinning.cons node_24500 (AllWinning.cons node_24188 (AllWinning.cons node_23781 (AllWinning.cons node_23390 (AllWinning.cons node_25041 (AllWinning.cons node_24799 (AllWinning.cons node_24504 (AllWinning.cons node_24194 (AllWinning.cons node_23790 (AllWinning.cons node_23402 (AllWinning.nil))))))))))))))))))

theorem node_25266 : Outcome ⟨18, 16, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 16, 10, 2⟩, ⟨16, 16, 10, 4⟩, ⟨18, 15, 10, 2⟩, ⟨18, 14, 10, 4⟩, ⟨18, 16, 9, 2⟩, ⟨18, 16, 8, 4⟩]
  exact AllWinning.cons node_25028 (AllWinning.cons node_24762 (AllWinning.cons node_25042 (AllWinning.cons node_24799 (AllWinning.cons node_25043 (AllWinning.cons node_24801 (AllWinning.nil))))))

theorem node_25267 : Outcome ⟨18, 18, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 18, 8, 2⟩, ⟨16, 18, 8, 4⟩, ⟨18, 17, 8, 2⟩, ⟨18, 16, 8, 4⟩, ⟨18, 18, 7, 2⟩, ⟨18, 18, 6, 4⟩]
  exact AllWinning.cons node_25032 (AllWinning.cons node_24765 (AllWinning.cons node_25044 (AllWinning.cons node_24801 (AllWinning.cons node_25045 (AllWinning.cons node_24802 (AllWinning.nil))))))

theorem node_25268 : Outcome ⟨18, 18, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 18, 8, 2⟩, ⟨16, 18, 8, 4⟩, ⟨15, 18, 8, 6⟩, ⟨14, 18, 8, 8⟩, ⟨13, 18, 8, 10⟩, ⟨12, 18, 8, 12⟩, ⟨18, 17, 8, 2⟩, ⟨18, 16, 8, 4⟩, ⟨18, 15, 8, 6⟩, ⟨18, 14, 8, 8⟩, ⟨18, 13, 8, 10⟩, ⟨18, 12, 8, 12⟩, ⟨18, 18, 7, 2⟩, ⟨18, 18, 6, 4⟩, ⟨18, 18, 5, 6⟩, ⟨18, 18, 4, 8⟩, ⟨18, 18, 3, 10⟩, ⟨18, 18, 2, 12⟩]
  exact AllWinning.cons node_25032 (AllWinning.cons node_24765 (AllWinning.cons node_24442 (AllWinning.cons node_24074 (AllWinning.cons node_23652 (AllWinning.cons node_23204 (AllWinning.cons node_25044 (AllWinning.cons node_24801 (AllWinning.cons node_24506 (AllWinning.cons node_24194 (AllWinning.cons node_23787 (AllWinning.cons node_23396 (AllWinning.cons node_25045 (AllWinning.cons node_24802 (AllWinning.cons node_24510 (AllWinning.cons node_24200 (AllWinning.cons node_23794 (AllWinning.cons node_23405 (AllWinning.nil))))))))))))))))))

theorem node_25269 : Outcome ⟨19, 6, 19, 4⟩ true :=
  Outcome.win (q := ⟨19, 5, 19, 2⟩) (by decide) node_25046

theorem node_25270 : Outcome ⟨19, 8, 17, 4⟩ true :=
  Outcome.win (q := ⟨19, 8, 13, 8⟩) (by decide) node_24209

theorem node_25271 : Outcome ⟨19, 9, 16, 4⟩ true :=
  Outcome.win (q := ⟨17, 9, 16, 4⟩) (by decide) node_24772

theorem node_25272 : Outcome ⟨19, 10, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 15, 2⟩, ⟨17, 10, 15, 4⟩, ⟨19, 9, 15, 2⟩, ⟨19, 8, 15, 4⟩, ⟨19, 10, 14, 2⟩, ⟨19, 10, 13, 4⟩]
  exact AllWinning.cons node_25037 (AllWinning.cons node_24774 (AllWinning.cons node_25050 (AllWinning.cons node_24808 (AllWinning.cons node_25051 (AllWinning.cons node_24811 (AllWinning.nil))))))

theorem node_25273 : Outcome ⟨19, 10, 15, 4⟩ true :=
  Outcome.win (q := ⟨15, 10, 15, 8⟩) (by decide) node_24090

theorem node_25274 : Outcome ⟨19, 11, 14, 4⟩ true :=
  Outcome.win (q := ⟨17, 11, 14, 4⟩) (by decide) node_24776

theorem node_25275 : Outcome ⟨19, 12, 13, 4⟩ true :=
  Outcome.win (q := ⟨19, 8, 13, 8⟩) (by decide) node_24209

theorem node_25276 : Outcome ⟨19, 14, 11, 4⟩ true :=
  Outcome.win (q := ⟨17, 14, 11, 4⟩) (by decide) node_24782

theorem node_25277 : Outcome ⟨19, 15, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 15, 10, 2⟩, ⟨17, 15, 10, 4⟩, ⟨19, 14, 10, 2⟩, ⟨19, 13, 10, 4⟩, ⟨19, 15, 9, 2⟩, ⟨19, 15, 8, 4⟩]
  exact AllWinning.cons node_25042 (AllWinning.cons node_24783 (AllWinning.cons node_25055 (AllWinning.cons node_24816 (AllWinning.cons node_25056 (AllWinning.cons node_24818 (AllWinning.nil))))))

theorem node_25278 : Outcome ⟨19, 16, 9, 4⟩ true :=
  Outcome.win (q := ⟨17, 16, 9, 4⟩) (by decide) node_24785

theorem node_25279 : Outcome ⟨19, 17, 8, 4⟩ true :=
  Outcome.win (q := ⟨19, 13, 8, 8⟩) (by decide) node_24222

theorem node_25280 : Outcome ⟨19, 19, 6, 4⟩ true :=
  Outcome.win (q := ⟨19, 19, 5, 2⟩) (by decide) node_25058

theorem node_25281 : Outcome ⟨5, 20, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 20, 2⟩, ⟨3, 20, 20, 4⟩, ⟨5, 19, 20, 2⟩, ⟨5, 18, 20, 4⟩, ⟨5, 20, 19, 2⟩, ⟨5, 20, 18, 4⟩]
  exact AllWinning.cons node_25061 (AllWinning.cons node_24825 (AllWinning.cons node_25063 (AllWinning.cons node_24829 (AllWinning.cons node_25064 (AllWinning.cons node_24834 (AllWinning.nil))))))

theorem node_25282 : Outcome ⟨5, 20, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 20, 2⟩, ⟨3, 20, 20, 4⟩, ⟨2, 20, 20, 6⟩, ⟨1, 20, 20, 8⟩, ⟨5, 19, 20, 2⟩, ⟨5, 18, 20, 4⟩, ⟨5, 17, 20, 6⟩, ⟨5, 16, 20, 8⟩, ⟨5, 20, 19, 2⟩, ⟨5, 20, 18, 4⟩, ⟨5, 20, 17, 6⟩, ⟨5, 20, 16, 8⟩]
  exact AllWinning.cons node_25061 (AllWinning.cons node_24825 (AllWinning.cons node_24526 (AllWinning.cons node_24228 (AllWinning.cons node_25063 (AllWinning.cons node_24829 (AllWinning.cons node_24536 (AllWinning.cons node_24247 (AllWinning.cons node_25064 (AllWinning.cons node_24834 (AllWinning.cons node_24541 (AllWinning.cons node_24256 (AllWinning.nil))))))))))))

theorem node_25283 : Outcome ⟨5, 20, 20, 6⟩ true :=
  Outcome.win (q := ⟨0, 20, 20, 10⟩) (by decide) node_23813

theorem node_25284 : Outcome ⟨7, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨7, 16, 20, 4⟩) (by decide) node_24843

theorem node_25285 : Outcome ⟨7, 19, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 19, 19, 4⟩) (by decide) node_24832

theorem node_25286 : Outcome ⟨7, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨7, 20, 16, 4⟩) (by decide) node_24854

theorem node_25287 : Outcome ⟨8, 17, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 17, 20, 2⟩, ⟨6, 17, 20, 4⟩, ⟨8, 16, 20, 2⟩, ⟨8, 15, 20, 4⟩, ⟨8, 17, 19, 2⟩, ⟨8, 17, 18, 4⟩]
  exact AllWinning.cons node_25068 (AllWinning.cons node_24836 (AllWinning.cons node_25078 (AllWinning.cons node_24858 (AllWinning.cons node_25081 (AllWinning.cons node_24862 (AllWinning.nil))))))

theorem node_25288 : Outcome ⟨8, 17, 20, 6⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 6⟩) (by decide) node_24567

theorem node_25289 : Outcome ⟨8, 18, 19, 2⟩ true :=
  Outcome.win (q := ⟨7, 18, 19, 2⟩) (by decide) node_25070

theorem node_25290 : Outcome ⟨8, 18, 19, 4⟩ true :=
  Outcome.win (q := ⟨7, 18, 19, 2⟩) (by decide) node_25070

theorem node_25291 : Outcome ⟨8, 19, 18, 2⟩ true :=
  Outcome.win (q := ⟨7, 19, 18, 2⟩) (by decide) node_25073

theorem node_25292 : Outcome ⟨8, 19, 18, 4⟩ true :=
  Outcome.win (q := ⟨7, 19, 18, 2⟩) (by decide) node_25073

theorem node_25293 : Outcome ⟨8, 20, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 20, 17, 2⟩, ⟨6, 20, 17, 4⟩, ⟨8, 19, 17, 2⟩, ⟨8, 18, 17, 4⟩, ⟨8, 20, 16, 2⟩, ⟨8, 20, 15, 4⟩]
  exact AllWinning.cons node_25076 (AllWinning.cons node_24841 (AllWinning.cons node_25087 (AllWinning.cons node_24864 (AllWinning.cons node_25089 (AllWinning.cons node_24866 (AllWinning.nil))))))

theorem node_25294 : Outcome ⟨8, 20, 17, 6⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 6⟩) (by decide) node_24567

theorem node_25295 : Outcome ⟨9, 16, 20, 2⟩ true :=
  Outcome.win (q := ⟨7, 16, 20, 4⟩) (by decide) node_24843

theorem node_25296 : Outcome ⟨9, 16, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 16, 17, 6⟩) (by decide) node_24585

theorem node_25297 : Outcome ⟨9, 16, 20, 6⟩ true :=
  Outcome.win (q := ⟨9, 16, 17, 6⟩) (by decide) node_24585

theorem node_25298 : Outcome ⟨9, 17, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 17, 19, 2⟩, ⟨7, 17, 19, 4⟩, ⟨9, 16, 19, 2⟩, ⟨9, 15, 19, 4⟩, ⟨9, 17, 18, 2⟩, ⟨9, 17, 17, 4⟩]
  exact AllWinning.cons node_25081 (AllWinning.cons node_24848 (AllWinning.cons node_25095 (AllWinning.cons node_24871 (AllWinning.cons node_25097 (AllWinning.cons node_24875 (AllWinning.nil))))))

theorem node_25299 : Outcome ⟨9, 18, 18, 4⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 2⟩) (by decide) node_25083

theorem node_25300 : Outcome ⟨9, 18, 18, 8⟩ true :=
  Outcome.win (q := ⟨8, 18, 18, 2⟩) (by decide) node_25083

theorem node_25301 : Outcome ⟨9, 19, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 19, 17, 2⟩, ⟨7, 19, 17, 4⟩, ⟨9, 18, 17, 2⟩, ⟨9, 17, 17, 4⟩, ⟨9, 19, 16, 2⟩, ⟨9, 19, 15, 4⟩]
  exact AllWinning.cons node_25087 (AllWinning.cons node_24852 (AllWinning.cons node_25099 (AllWinning.cons node_24875 (AllWinning.cons node_25101 (AllWinning.cons node_24881 (AllWinning.nil))))))

theorem node_25302 : Outcome ⟨9, 20, 16, 2⟩ true :=
  Outcome.win (q := ⟨7, 20, 16, 4⟩) (by decide) node_24854

theorem node_25303 : Outcome ⟨9, 20, 16, 4⟩ true :=
  Outcome.win (q := ⟨9, 17, 16, 6⟩) (by decide) node_24590

theorem node_25304 : Outcome ⟨9, 20, 16, 6⟩ true :=
  Outcome.win (q := ⟨9, 17, 16, 6⟩) (by decide) node_24590

theorem node_25305 : Outcome ⟨10, 15, 20, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 20, 2⟩) (by decide) node_25106

theorem node_25306 : Outcome ⟨10, 15, 20, 6⟩ true :=
  Outcome.win (q := ⟨6, 15, 20, 8⟩) (by decide) node_24260

theorem node_25307 : Outcome ⟨10, 16, 19, 2⟩ true :=
  Outcome.win (q := ⟨10, 15, 19, 2⟩) (by decide) node_25108

theorem node_25308 : Outcome ⟨10, 16, 19, 4⟩ true :=
  Outcome.win (q := ⟨10, 15, 19, 2⟩) (by decide) node_25108

theorem node_25309 : Outcome ⟨10, 17, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 18, 2⟩) (by decide) node_25111

theorem node_25310 : Outcome ⟨10, 18, 17, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 16, 2⟩) (by decide) node_25117

theorem node_25311 : Outcome ⟨10, 19, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 16, 2⟩) (by decide) node_25117

theorem node_25312 : Outcome ⟨10, 19, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 16, 2⟩) (by decide) node_25117

theorem node_25313 : Outcome ⟨10, 20, 15, 2⟩ true :=
  Outcome.win (q := ⟨10, 19, 15, 2⟩) (by decide) node_25121

theorem node_25314 : Outcome ⟨10, 20, 15, 6⟩ true :=
  Outcome.win (q := ⟨6, 20, 15, 8⟩) (by decide) node_24271

theorem node_25315 : Outcome ⟨11, 14, 20, 2⟩ true :=
  Outcome.win (q := ⟨10, 14, 20, 2⟩) (by decide) node_25106

theorem node_25316 : Outcome ⟨11, 14, 20, 6⟩ true :=
  Outcome.win (q := ⟨11, 11, 20, 6⟩) (by decide) node_24614

theorem node_25317 : Outcome ⟨11, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨10, 15, 19, 2⟩) (by decide) node_25108

theorem node_25318 : Outcome ⟨11, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨10, 16, 18, 2⟩) (by decide) node_25111

theorem node_25319 : Outcome ⟨11, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 16, 18, 2⟩) (by decide) node_25111

theorem node_25320 : Outcome ⟨11, 16, 18, 8⟩ true :=
  Outcome.win (q := ⟨10, 16, 18, 2⟩) (by decide) node_25111

theorem node_25321 : Outcome ⟨11, 17, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 17, 2⟩, ⟨9, 17, 17, 4⟩, ⟨11, 16, 17, 2⟩, ⟨11, 15, 17, 4⟩, ⟨11, 17, 16, 2⟩, ⟨11, 17, 15, 4⟩]
  exact AllWinning.cons node_25115 (AllWinning.cons node_24875 (AllWinning.cons node_25131 (AllWinning.cons node_24904 (AllWinning.cons node_25135 (AllWinning.cons node_24908 (AllWinning.nil))))))

theorem node_25322 : Outcome ⟨11, 17, 17, 4⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 6⟩) (by decide) node_24567

theorem node_25323 : Outcome ⟨11, 17, 17, 6⟩ true :=
  Outcome.win (q := ⟨8, 17, 17, 6⟩) (by decide) node_24567

theorem node_25324 : Outcome ⟨11, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨10, 18, 16, 2⟩) (by decide) node_25117

theorem node_25325 : Outcome ⟨11, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 16, 2⟩) (by decide) node_25117

theorem node_25326 : Outcome ⟨11, 18, 16, 8⟩ true :=
  Outcome.win (q := ⟨10, 18, 16, 2⟩) (by decide) node_25117

theorem node_25327 : Outcome ⟨11, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨10, 19, 15, 2⟩) (by decide) node_25121

theorem node_25328 : Outcome ⟨11, 20, 14, 2⟩ true :=
  Outcome.win (q := ⟨10, 20, 14, 2⟩) (by decide) node_25124

theorem node_25329 : Outcome ⟨11, 20, 14, 6⟩ true :=
  Outcome.win (q := ⟨11, 17, 14, 6⟩) (by decide) node_24628

theorem node_25330 : Outcome ⟨12, 13, 20, 6⟩ true :=
  Outcome.win (q := ⟨12, 13, 17, 6⟩) (by decide) node_24641

theorem node_25331 : Outcome ⟨12, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 12, 19, 4⟩) (by decide) node_24912

theorem node_25332 : Outcome ⟨12, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 4⟩) (by decide) node_24918

theorem node_25333 : Outcome ⟨12, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 4⟩) (by decide) node_24918

theorem node_25334 : Outcome ⟨12, 15, 18, 8⟩ true :=
  Outcome.win (q := ⟨12, 15, 16, 4⟩) (by decide) node_24918

theorem node_25335 : Outcome ⟨12, 16, 17, 4⟩ true :=
  Outcome.win (q := ⟨9, 16, 17, 6⟩) (by decide) node_24585

theorem node_25336 : Outcome ⟨12, 16, 17, 6⟩ true :=
  Outcome.win (q := ⟨9, 16, 17, 6⟩) (by decide) node_24585

theorem node_25337 : Outcome ⟨12, 17, 16, 4⟩ true :=
  Outcome.win (q := ⟨9, 17, 16, 6⟩) (by decide) node_24590

theorem node_25338 : Outcome ⟨12, 17, 16, 6⟩ true :=
  Outcome.win (q := ⟨9, 17, 16, 6⟩) (by decide) node_24590

theorem node_25339 : Outcome ⟨12, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 4⟩) (by decide) node_24921

theorem node_25340 : Outcome ⟨12, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 4⟩) (by decide) node_24921

theorem node_25341 : Outcome ⟨12, 18, 15, 8⟩ true :=
  Outcome.win (q := ⟨12, 16, 15, 4⟩) (by decide) node_24921

theorem node_25342 : Outcome ⟨12, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 19, 12, 4⟩) (by decide) node_24928

theorem node_25343 : Outcome ⟨12, 20, 13, 6⟩ true :=
  Outcome.win (q := ⟨12, 17, 13, 6⟩) (by decide) node_24650

theorem node_25344 : Outcome ⟨13, 12, 20, 6⟩ true :=
  Outcome.win (q := ⟨13, 12, 17, 6⟩) (by decide) node_24661

theorem node_25345 : Outcome ⟨13, 13, 19, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 18, 2⟩) (by decide) node_25163

theorem node_25346 : Outcome ⟨13, 13, 19, 12⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 12⟩) (by decide) node_23640

theorem node_25347 : Outcome ⟨13, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 18, 2⟩) (by decide) node_25146

theorem node_25348 : Outcome ⟨13, 14, 18, 4⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 6⟩) (by decide) node_24666

theorem node_25349 : Outcome ⟨13, 14, 18, 8⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 6⟩) (by decide) node_24666

theorem node_25350 : Outcome ⟨13, 15, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 15, 17, 2⟩, ⟨11, 15, 17, 4⟩, ⟨13, 14, 17, 2⟩, ⟨13, 13, 17, 4⟩, ⟨13, 15, 16, 2⟩, ⟨13, 15, 15, 4⟩]
  exact AllWinning.cons node_25149 (AllWinning.cons node_24904 (AllWinning.cons node_25166 (AllWinning.cons node_24937 (AllWinning.cons node_25169 (AllWinning.cons node_24941 (AllWinning.nil))))))

theorem node_25351 : Outcome ⟨13, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨13, 12, 17, 6⟩) (by decide) node_24661

theorem node_25352 : Outcome ⟨13, 15, 17, 6⟩ true :=
  Outcome.win (q := ⟨13, 12, 17, 6⟩) (by decide) node_24661

theorem node_25353 : Outcome ⟨13, 16, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 16, 2⟩, ⟨11, 16, 16, 4⟩, ⟨13, 15, 16, 2⟩, ⟨13, 14, 16, 4⟩, ⟨13, 16, 15, 2⟩, ⟨13, 16, 14, 4⟩]
  exact AllWinning.cons node_25151 (AllWinning.cons node_24906 (AllWinning.cons node_25169 (AllWinning.cons node_24939 (AllWinning.cons node_25171 (AllWinning.cons node_24943 (AllWinning.nil))))))

theorem node_25354 : Outcome ⟨13, 16, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 16, 2⟩, ⟨11, 16, 16, 4⟩, ⟨10, 16, 16, 6⟩, ⟨9, 16, 16, 8⟩, ⟨13, 15, 16, 2⟩, ⟨13, 14, 16, 4⟩, ⟨13, 13, 16, 6⟩, ⟨13, 12, 16, 8⟩, ⟨13, 16, 15, 2⟩, ⟨13, 16, 14, 4⟩, ⟨13, 16, 13, 6⟩, ⟨13, 16, 12, 8⟩]
  exact AllWinning.cons node_25151 (AllWinning.cons node_24906 (AllWinning.cons node_24608 (AllWinning.cons node_24313 (AllWinning.cons node_25169 (AllWinning.cons node_24939 (AllWinning.cons node_24663 (AllWinning.cons node_24377 (AllWinning.cons node_25171 (AllWinning.cons node_24943 (AllWinning.cons node_24675 (AllWinning.cons node_24387 (AllWinning.nil))))))))))))

theorem node_25355 : Outcome ⟨13, 16, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 16, 2⟩, ⟨11, 16, 16, 4⟩, ⟨10, 16, 16, 6⟩, ⟨9, 16, 16, 8⟩, ⟨8, 16, 16, 10⟩, ⟨7, 16, 16, 12⟩, ⟨13, 15, 16, 2⟩, ⟨13, 14, 16, 4⟩, ⟨13, 13, 16, 6⟩, ⟨13, 12, 16, 8⟩, ⟨13, 11, 16, 10⟩, ⟨13, 10, 16, 12⟩, ⟨13, 16, 15, 2⟩, ⟨13, 16, 14, 4⟩, ⟨13, 16, 13, 6⟩, ⟨13, 16, 12, 8⟩, ⟨13, 16, 11, 10⟩, ⟨13, 16, 10, 12⟩]
  exact AllWinning.cons node_25151 (AllWinning.cons node_24906 (AllWinning.cons node_24608 (AllWinning.cons node_24313 (AllWinning.cons node_23895 (AllWinning.cons node_23499 (AllWinning.cons node_25169 (AllWinning.cons node_24939 (AllWinning.cons node_24663 (AllWinning.cons node_24377 (AllWinning.cons node_24021 (AllWinning.cons node_23629 (AllWinning.cons node_25171 (AllWinning.cons node_24943 (AllWinning.cons node_24675 (AllWinning.cons node_24387 (AllWinning.cons node_24037 (AllWinning.cons node_23648 (AllWinning.nil))))))))))))))))))

theorem node_25356 : Outcome ⟨13, 16, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 16, 16, 2⟩, ⟨11, 16, 16, 4⟩, ⟨10, 16, 16, 6⟩, ⟨9, 16, 16, 8⟩, ⟨8, 16, 16, 10⟩, ⟨7, 16, 16, 12⟩, ⟨6, 16, 16, 14⟩, ⟨5, 16, 16, 16⟩, ⟨13, 15, 16, 2⟩, ⟨13, 14, 16, 4⟩, ⟨13, 13, 16, 6⟩, ⟨13, 12, 16, 8⟩, ⟨13, 11, 16, 10⟩, ⟨13, 10, 16, 12⟩, ⟨13, 9, 16, 14⟩, ⟨13, 8, 16, 16⟩, ⟨13, 16, 15, 2⟩, ⟨13, 16, 14, 4⟩, ⟨13, 16, 13, 6⟩, ⟨13, 16, 12, 8⟩, ⟨13, 16, 11, 10⟩, ⟨13, 16, 10, 12⟩, ⟨13, 16, 9, 14⟩, ⟨13, 16, 8, 16⟩]
  exact AllWinning.cons node_25151 (AllWinning.cons node_24906 (AllWinning.cons node_24608 (AllWinning.cons node_24313 (AllWinning.cons node_23895 (AllWinning.cons node_23499 (AllWinning.cons node_23027 (AllWinning.cons node_22469 (AllWinning.cons node_25169 (AllWinning.cons node_24939 (AllWinning.cons node_24663 (AllWinning.cons node_24377 (AllWinning.cons node_24021 (AllWinning.cons node_23629 (AllWinning.cons node_23220 (AllWinning.cons node_22705 (AllWinning.cons node_25171 (AllWinning.cons node_24943 (AllWinning.cons node_24675 (AllWinning.cons node_24387 (AllWinning.cons node_24037 (AllWinning.cons node_23648 (AllWinning.cons node_23238 (AllWinning.cons node_22731 (AllWinning.nil))))))))))))))))))))))))

theorem node_25357 : Outcome ⟨13, 17, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 15, 2⟩, ⟨11, 17, 15, 4⟩, ⟨13, 16, 15, 2⟩, ⟨13, 15, 15, 4⟩, ⟨13, 17, 14, 2⟩, ⟨13, 17, 13, 4⟩]
  exact AllWinning.cons node_25153 (AllWinning.cons node_24908 (AllWinning.cons node_25171 (AllWinning.cons node_24941 (AllWinning.cons node_25173 (AllWinning.cons node_24946 (AllWinning.nil))))))

theorem node_25358 : Outcome ⟨13, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 6⟩) (by decide) node_24666

theorem node_25359 : Outcome ⟨13, 17, 15, 6⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 6⟩) (by decide) node_24666

theorem node_25360 : Outcome ⟨13, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 14, 2⟩) (by decide) node_25155

theorem node_25361 : Outcome ⟨13, 18, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 14, 6⟩) (by decide) node_24671

theorem node_25362 : Outcome ⟨13, 18, 14, 8⟩ true :=
  Outcome.win (q := ⟨13, 15, 14, 6⟩) (by decide) node_24671

theorem node_25363 : Outcome ⟨13, 19, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 13, 2⟩) (by decide) node_25176

theorem node_25364 : Outcome ⟨13, 19, 13, 12⟩ true :=
  Outcome.win (q := ⟨13, 13, 13, 12⟩) (by decide) node_23640

theorem node_25365 : Outcome ⟨13, 20, 12, 6⟩ true :=
  Outcome.win (q := ⟨13, 17, 12, 6⟩) (by decide) node_24678

theorem node_25366 : Outcome ⟨14, 11, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 10, 20, 2⟩) (by decide) node_25181

theorem node_25367 : Outcome ⟨14, 12, 19, 2⟩ true :=
  Outcome.win (q := ⟨12, 12, 19, 4⟩) (by decide) node_24912

theorem node_25368 : Outcome ⟨14, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 18, 2⟩) (by decide) node_25163

theorem node_25369 : Outcome ⟨14, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨14, 13, 15, 6⟩) (by decide) node_24695

theorem node_25370 : Outcome ⟨14, 14, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 14, 17, 2⟩, ⟨12, 14, 17, 4⟩, ⟨14, 13, 17, 2⟩, ⟨14, 12, 17, 4⟩, ⟨14, 14, 16, 2⟩, ⟨14, 14, 15, 4⟩]
  exact AllWinning.cons node_25166 (AllWinning.cons node_24917 (AllWinning.cons node_25186 (AllWinning.cons node_24956 (AllWinning.cons node_25189 (AllWinning.cons node_24960 (AllWinning.nil))))))

theorem node_25371 : Outcome ⟨14, 14, 17, 4⟩ true :=
  Outcome.win (q := ⟨11, 14, 17, 6⟩) (by decide) node_24621

theorem node_25372 : Outcome ⟨14, 15, 16, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 13, 6⟩) (by decide) node_24701

theorem node_25373 : Outcome ⟨14, 16, 15, 4⟩ true :=
  Outcome.win (q := ⟨14, 13, 15, 6⟩) (by decide) node_24695

theorem node_25374 : Outcome ⟨14, 17, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 17, 14, 2⟩, ⟨12, 17, 14, 4⟩, ⟨14, 16, 14, 2⟩, ⟨14, 15, 14, 4⟩, ⟨14, 17, 13, 2⟩, ⟨14, 17, 12, 4⟩]
  exact AllWinning.cons node_25173 (AllWinning.cons node_24925 (AllWinning.cons node_25192 (AllWinning.cons node_24961 (AllWinning.cons node_25194 (AllWinning.cons node_24965 (AllWinning.nil))))))

theorem node_25375 : Outcome ⟨14, 17, 14, 4⟩ true :=
  Outcome.win (q := ⟨11, 17, 14, 6⟩) (by decide) node_24628

theorem node_25376 : Outcome ⟨14, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 13, 2⟩) (by decide) node_25176

theorem node_25377 : Outcome ⟨14, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨14, 15, 13, 6⟩) (by decide) node_24701

theorem node_25378 : Outcome ⟨14, 19, 12, 2⟩ true :=
  Outcome.win (q := ⟨12, 19, 12, 4⟩) (by decide) node_24928

theorem node_25379 : Outcome ⟨15, 10, 20, 2⟩ true :=
  Outcome.win (q := ⟨14, 10, 20, 2⟩) (by decide) node_25181

theorem node_25380 : Outcome ⟨15, 10, 20, 6⟩ true :=
  Outcome.win (q := ⟨15, 6, 20, 8⟩) (by decide) node_24419

theorem node_25381 : Outcome ⟨15, 11, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 10, 19, 2⟩) (by decide) node_25203

theorem node_25382 : Outcome ⟨15, 12, 18, 4⟩ true :=
  Outcome.win (q := ⟨15, 12, 16, 4⟩) (by decide) node_24975

theorem node_25383 : Outcome ⟨15, 12, 18, 8⟩ true :=
  Outcome.win (q := ⟨15, 12, 16, 4⟩) (by decide) node_24975

theorem node_25384 : Outcome ⟨15, 13, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 17, 2⟩, ⟨13, 13, 17, 4⟩, ⟨15, 12, 17, 2⟩, ⟨15, 11, 17, 4⟩, ⟨15, 13, 16, 2⟩, ⟨15, 13, 15, 4⟩]
  exact AllWinning.cons node_25186 (AllWinning.cons node_24937 (AllWinning.cons node_25206 (AllWinning.cons node_24973 (AllWinning.cons node_25207 (AllWinning.cons node_24978 (AllWinning.nil))))))

theorem node_25385 : Outcome ⟨15, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨12, 13, 17, 6⟩) (by decide) node_24641

theorem node_25386 : Outcome ⟨15, 13, 17, 6⟩ true :=
  Outcome.win (q := ⟨12, 13, 17, 6⟩) (by decide) node_24641

theorem node_25387 : Outcome ⟨15, 14, 16, 4⟩ true :=
  Outcome.win (q := ⟨15, 14, 13, 6⟩) (by decide) node_24729

theorem node_25388 : Outcome ⟨15, 14, 16, 8⟩ true :=
  Outcome.win (q := ⟨10, 14, 16, 10⟩) (by decide) node_23940

theorem node_25389 : Outcome ⟨15, 15, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 15, 15, 2⟩, ⟨13, 15, 15, 4⟩, ⟨12, 15, 15, 6⟩, ⟨11, 15, 15, 8⟩, ⟨15, 14, 15, 2⟩, ⟨15, 13, 15, 4⟩, ⟨15, 12, 15, 6⟩, ⟨15, 11, 15, 8⟩, ⟨15, 15, 14, 2⟩, ⟨15, 15, 13, 4⟩, ⟨15, 15, 12, 6⟩, ⟨15, 15, 11, 8⟩]
  exact AllWinning.cons node_25191 (AllWinning.cons node_24941 (AllWinning.cons node_24645 (AllWinning.cons node_24339 (AllWinning.cons node_25210 (AllWinning.cons node_24978 (AllWinning.cons node_24723 (AllWinning.cons node_24427 (AllWinning.cons node_25211 (AllWinning.cons node_24981 (AllWinning.cons node_24733 (AllWinning.cons node_24437 (AllWinning.nil))))))))))))

theorem node_25390 : Outcome ⟨15, 16, 14, 4⟩ true :=
  Outcome.win (q := ⟨15, 13, 14, 6⟩) (by decide) node_24725

theorem node_25391 : Outcome ⟨15, 16, 14, 8⟩ true :=
  Outcome.win (q := ⟨10, 16, 14, 10⟩) (by decide) node_23949

theorem node_25392 : Outcome ⟨15, 17, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 17, 13, 2⟩, ⟨13, 17, 13, 4⟩, ⟨15, 16, 13, 2⟩, ⟨15, 15, 13, 4⟩, ⟨15, 17, 12, 2⟩, ⟨15, 17, 11, 4⟩]
  exact AllWinning.cons node_25194 (AllWinning.cons node_24946 (AllWinning.cons node_25212 (AllWinning.cons node_24981 (AllWinning.cons node_25215 (AllWinning.cons node_24987 (AllWinning.nil))))))

theorem node_25393 : Outcome ⟨15, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨12, 17, 13, 6⟩) (by decide) node_24650

theorem node_25394 : Outcome ⟨15, 17, 13, 6⟩ true :=
  Outcome.win (q := ⟨12, 17, 13, 6⟩) (by decide) node_24650

theorem node_25395 : Outcome ⟨15, 18, 12, 2⟩ true :=
  Outcome.win (q := ⟨15, 16, 12, 4⟩) (by decide) node_24984

theorem node_25396 : Outcome ⟨15, 18, 12, 4⟩ true :=
  Outcome.win (q := ⟨15, 16, 12, 4⟩) (by decide) node_24984

theorem node_25397 : Outcome ⟨15, 18, 12, 8⟩ true :=
  Outcome.win (q := ⟨15, 16, 12, 4⟩) (by decide) node_24984

theorem node_25398 : Outcome ⟨15, 19, 11, 2⟩ true :=
  Outcome.win (q := ⟨15, 19, 10, 2⟩) (by decide) node_25218

theorem node_25399 : Outcome ⟨15, 20, 10, 6⟩ true :=
  Outcome.win (q := ⟨15, 20, 6, 8⟩) (by decide) node_24445

theorem node_25400 : Outcome ⟨16, 10, 19, 2⟩ true :=
  Outcome.win (q := ⟨15, 10, 19, 2⟩) (by decide) node_25203

theorem node_25401 : Outcome ⟨16, 11, 18, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 18, 2⟩) (by decide) node_25222

theorem node_25402 : Outcome ⟨16, 11, 18, 8⟩ true :=
  Outcome.win (q := ⟨16, 10, 18, 2⟩) (by decide) node_25222

theorem node_25403 : Outcome ⟨16, 12, 17, 4⟩ true :=
  Outcome.win (q := ⟨13, 12, 17, 6⟩) (by decide) node_24661

theorem node_25404 : Outcome ⟨16, 13, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 16, 2⟩, ⟨14, 13, 16, 4⟩, ⟨16, 12, 16, 2⟩, ⟨16, 11, 16, 4⟩, ⟨16, 13, 15, 2⟩, ⟨16, 13, 14, 4⟩]
  exact AllWinning.cons node_25207 (AllWinning.cons node_24958 (AllWinning.cons node_25226 (AllWinning.cons node_24996 (AllWinning.cons node_25227 (AllWinning.cons node_25001 (AllWinning.nil))))))

theorem node_25405 : Outcome ⟨16, 13, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 16, 2⟩, ⟨14, 13, 16, 4⟩, ⟨13, 13, 16, 6⟩, ⟨12, 13, 16, 8⟩, ⟨16, 12, 16, 2⟩, ⟨16, 11, 16, 4⟩, ⟨16, 10, 16, 6⟩, ⟨16, 9, 16, 8⟩, ⟨16, 13, 15, 2⟩, ⟨16, 13, 14, 4⟩, ⟨16, 13, 13, 6⟩, ⟨16, 13, 12, 8⟩]
  exact AllWinning.cons node_25207 (AllWinning.cons node_24958 (AllWinning.cons node_24663 (AllWinning.cons node_24355 (AllWinning.cons node_25226 (AllWinning.cons node_24996 (AllWinning.cons node_24749 (AllWinning.cons node_24453 (AllWinning.cons node_25227 (AllWinning.cons node_25001 (AllWinning.cons node_24756 (AllWinning.cons node_24463 (AllWinning.nil))))))))))))

theorem node_25406 : Outcome ⟨16, 13, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 16, 2⟩, ⟨14, 13, 16, 4⟩, ⟨13, 13, 16, 6⟩, ⟨12, 13, 16, 8⟩, ⟨11, 13, 16, 10⟩, ⟨10, 13, 16, 12⟩, ⟨16, 12, 16, 2⟩, ⟨16, 11, 16, 4⟩, ⟨16, 10, 16, 6⟩, ⟨16, 9, 16, 8⟩, ⟨16, 8, 16, 10⟩, ⟨16, 7, 16, 12⟩, ⟨16, 13, 15, 2⟩, ⟨16, 13, 14, 4⟩, ⟨16, 13, 13, 6⟩, ⟨16, 13, 12, 8⟩, ⟨16, 13, 11, 10⟩, ⟨16, 13, 10, 12⟩]
  exact AllWinning.cons node_25207 (AllWinning.cons node_24958 (AllWinning.cons node_24663 (AllWinning.cons node_24355 (AllWinning.cons node_23967 (AllWinning.cons node_23558 (AllWinning.cons node_25226 (AllWinning.cons node_24996 (AllWinning.cons node_24749 (AllWinning.cons node_24453 (AllWinning.cons node_24123 (AllWinning.cons node_23722 (AllWinning.cons node_25227 (AllWinning.cons node_25001 (AllWinning.cons node_24756 (AllWinning.cons node_24463 (AllWinning.cons node_24140 (AllWinning.cons node_23733 (AllWinning.nil))))))))))))))))))

theorem node_25407 : Outcome ⟨16, 13, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 13, 16, 2⟩, ⟨14, 13, 16, 4⟩, ⟨13, 13, 16, 6⟩, ⟨12, 13, 16, 8⟩, ⟨11, 13, 16, 10⟩, ⟨10, 13, 16, 12⟩, ⟨9, 13, 16, 14⟩, ⟨8, 13, 16, 16⟩, ⟨16, 12, 16, 2⟩, ⟨16, 11, 16, 4⟩, ⟨16, 10, 16, 6⟩, ⟨16, 9, 16, 8⟩, ⟨16, 8, 16, 10⟩, ⟨16, 7, 16, 12⟩, ⟨16, 6, 16, 14⟩, ⟨16, 5, 16, 16⟩, ⟨16, 13, 15, 2⟩, ⟨16, 13, 14, 4⟩, ⟨16, 13, 13, 6⟩, ⟨16, 13, 12, 8⟩, ⟨16, 13, 11, 10⟩, ⟨16, 13, 10, 12⟩, ⟨16, 13, 9, 14⟩, ⟨16, 13, 8, 16⟩]
  exact AllWinning.cons node_25207 (AllWinning.cons node_24958 (AllWinning.cons node_24663 (AllWinning.cons node_24355 (AllWinning.cons node_23967 (AllWinning.cons node_23558 (AllWinning.cons node_23097 (AllWinning.cons node_22538 (AllWinning.cons node_25226 (AllWinning.cons node_24996 (AllWinning.cons node_24749 (AllWinning.cons node_24453 (AllWinning.cons node_24123 (AllWinning.cons node_23722 (AllWinning.cons node_23318 (AllWinning.cons node_22850 (AllWinning.cons node_25227 (AllWinning.cons node_25001 (AllWinning.cons node_24756 (AllWinning.cons node_24463 (AllWinning.cons node_24140 (AllWinning.cons node_23733 (AllWinning.cons node_23332 (AllWinning.cons node_22867 (AllWinning.nil))))))))))))))))))))))))

theorem node_25408 : Outcome ⟨16, 14, 15, 4⟩ true :=
  Outcome.win (q := ⟨13, 14, 15, 6⟩) (by decide) node_24666

theorem node_25409 : Outcome ⟨16, 14, 15, 8⟩ true :=
  Outcome.win (q := ⟨16, 14, 10, 10⟩) (by decide) node_24145

theorem node_25410 : Outcome ⟨16, 15, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 15, 14, 6⟩) (by decide) node_24671

theorem node_25411 : Outcome ⟨16, 15, 14, 8⟩ true :=
  Outcome.win (q := ⟨16, 10, 14, 10⟩) (by decide) node_24130

theorem node_25412 : Outcome ⟨16, 16, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 13, 2⟩, ⟨14, 16, 13, 4⟩, ⟨16, 15, 13, 2⟩, ⟨16, 14, 13, 4⟩, ⟨16, 16, 12, 2⟩, ⟨16, 16, 11, 4⟩]
  exact AllWinning.cons node_25212 (AllWinning.cons node_24962 (AllWinning.cons node_25230 (AllWinning.cons node_25002 (AllWinning.cons node_25232 (AllWinning.cons node_25005 (AllWinning.nil))))))

theorem node_25413 : Outcome ⟨16, 16, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 13, 2⟩, ⟨14, 16, 13, 4⟩, ⟨13, 16, 13, 6⟩, ⟨12, 16, 13, 8⟩, ⟨16, 15, 13, 2⟩, ⟨16, 14, 13, 4⟩, ⟨16, 13, 13, 6⟩, ⟨16, 12, 13, 8⟩, ⟨16, 16, 12, 2⟩, ⟨16, 16, 11, 4⟩, ⟨16, 16, 10, 6⟩, ⟨16, 16, 9, 8⟩]
  exact AllWinning.cons node_25212 (AllWinning.cons node_24962 (AllWinning.cons node_24675 (AllWinning.cons node_24364 (AllWinning.cons node_25230 (AllWinning.cons node_25002 (AllWinning.cons node_24756 (AllWinning.cons node_24460 (AllWinning.cons node_25232 (AllWinning.cons node_25005 (AllWinning.cons node_24763 (AllWinning.cons node_24469 (AllWinning.nil))))))))))))

theorem node_25414 : Outcome ⟨16, 16, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 13, 2⟩, ⟨14, 16, 13, 4⟩, ⟨13, 16, 13, 6⟩, ⟨12, 16, 13, 8⟩, ⟨11, 16, 13, 10⟩, ⟨10, 16, 13, 12⟩, ⟨16, 15, 13, 2⟩, ⟨16, 14, 13, 4⟩, ⟨16, 13, 13, 6⟩, ⟨16, 12, 13, 8⟩, ⟨16, 11, 13, 10⟩, ⟨16, 10, 13, 12⟩, ⟨16, 16, 12, 2⟩, ⟨16, 16, 11, 4⟩, ⟨16, 16, 10, 6⟩, ⟨16, 16, 9, 8⟩, ⟨16, 16, 8, 10⟩, ⟨16, 16, 7, 12⟩]
  exact AllWinning.cons node_25212 (AllWinning.cons node_24962 (AllWinning.cons node_24675 (AllWinning.cons node_24364 (AllWinning.cons node_23975 (AllWinning.cons node_23564 (AllWinning.cons node_25230 (AllWinning.cons node_25002 (AllWinning.cons node_24756 (AllWinning.cons node_24460 (AllWinning.cons node_24133 (AllWinning.cons node_23727 (AllWinning.cons node_25232 (AllWinning.cons node_25005 (AllWinning.cons node_24763 (AllWinning.cons node_24469 (AllWinning.cons node_24151 (AllWinning.cons node_23739 (AllWinning.nil))))))))))))))))))

end RQ9F1
