import Chunk03
set_option autoImplicit false
namespace RQ9F1

theorem node_1151 : Outcome ⟨0, 0, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 4⟩) (by decide) node_681

theorem node_1152 : Outcome ⟨0, 0, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 4⟩) (by decide) node_681

theorem node_1153 : Outcome ⟨0, 0, 10, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 4⟩) (by decide) node_681

theorem node_1154 : Outcome ⟨0, 0, 10, 20⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 20⟩) (by decide) node_9

theorem node_1155 : Outcome ⟨0, 1, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 9, 2⟩, ⟨0, 1, 8, 2⟩, ⟨0, 1, 7, 4⟩]
  exact AllWinning.cons node_907 (AllWinning.cons node_911 (AllWinning.cons node_686 (AllWinning.nil)))

theorem node_1156 : Outcome ⟨0, 1, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 9, 2⟩, ⟨0, 1, 8, 2⟩, ⟨0, 1, 7, 4⟩, ⟨0, 1, 6, 6⟩, ⟨0, 1, 5, 8⟩]
  exact AllWinning.cons node_907 (AllWinning.cons node_911 (AllWinning.cons node_686 (AllWinning.cons node_472 (AllWinning.cons node_330 (AllWinning.nil)))))

theorem node_1157 : Outcome ⟨0, 1, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 9, 2⟩, ⟨0, 1, 8, 2⟩, ⟨0, 1, 7, 4⟩, ⟨0, 1, 6, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 1, 4, 10⟩, ⟨0, 1, 3, 12⟩]
  exact AllWinning.cons node_907 (AllWinning.cons node_911 (AllWinning.cons node_686 (AllWinning.cons node_472 (AllWinning.cons node_330 (AllWinning.cons node_242 (AllWinning.cons node_139 (AllWinning.nil)))))))

theorem node_1158 : Outcome ⟨0, 1, 9, 10⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 16⟩) (by decide) node_39

theorem node_1159 : Outcome ⟨0, 1, 9, 16⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 16⟩) (by decide) node_39

theorem node_1160 : Outcome ⟨0, 2, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 4⟩) (by decide) node_681

theorem node_1161 : Outcome ⟨0, 2, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 4⟩) (by decide) node_681

theorem node_1162 : Outcome ⟨0, 2, 8, 12⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 12⟩) (by decide) node_146

theorem node_1163 : Outcome ⟨0, 2, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 12⟩) (by decide) node_146

theorem node_1164 : Outcome ⟨0, 3, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 7, 2⟩) (by decide) node_916

theorem node_1165 : Outcome ⟨0, 3, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1166 : Outcome ⟨0, 3, 7, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1167 : Outcome ⟨0, 3, 7, 18⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1168 : Outcome ⟨0, 4, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 4⟩) (by decide) node_700

theorem node_1169 : Outcome ⟨0, 4, 6, 12⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 4⟩) (by decide) node_700

theorem node_1170 : Outcome ⟨0, 4, 6, 20⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 4⟩) (by decide) node_700

theorem node_1171 : Outcome ⟨0, 5, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.nil))))

theorem node_1172 : Outcome ⟨0, 5, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.nil))))))))

theorem node_1173 : Outcome ⟨0, 5, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1174 : Outcome ⟨0, 5, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1175 : Outcome ⟨0, 5, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1176 : Outcome ⟨0, 5, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1177 : Outcome ⟨0, 5, 5, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1178 : Outcome ⟨0, 5, 5, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1179 : Outcome ⟨0, 5, 5, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1180 : Outcome ⟨0, 5, 5, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1181 : Outcome ⟨0, 5, 5, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1182 : Outcome ⟨0, 5, 5, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1183 : Outcome ⟨0, 5, 5, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1184 : Outcome ⟨0, 5, 5, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 5, 2⟩, ⟨0, 3, 5, 4⟩, ⟨0, 2, 5, 6⟩, ⟨0, 1, 5, 8⟩, ⟨0, 0, 5, 10⟩, ⟨0, 5, 4, 2⟩, ⟨0, 5, 3, 4⟩, ⟨0, 5, 2, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 5, 0, 10⟩]
  exact AllWinning.cons node_926 (AllWinning.cons node_695 (AllWinning.cons node_476 (AllWinning.cons node_330 (AllWinning.cons node_237 (AllWinning.cons node_929 (AllWinning.cons node_715 (AllWinning.cons node_484 (AllWinning.cons node_359 (AllWinning.cons node_260 (AllWinning.nil))))))))))

theorem node_1185 : Outcome ⟨0, 6, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 4⟩) (by decide) node_700

theorem node_1186 : Outcome ⟨0, 6, 4, 12⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 4⟩) (by decide) node_700

theorem node_1187 : Outcome ⟨0, 6, 4, 20⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 4⟩) (by decide) node_700

theorem node_1188 : Outcome ⟨0, 7, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 2, 2⟩) (by decide) node_937

theorem node_1189 : Outcome ⟨0, 7, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1190 : Outcome ⟨0, 7, 3, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1191 : Outcome ⟨0, 7, 3, 18⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 8⟩) (by decide) node_340

theorem node_1192 : Outcome ⟨0, 8, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 4⟩) (by decide) node_730

theorem node_1193 : Outcome ⟨0, 8, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 4⟩) (by decide) node_730

theorem node_1194 : Outcome ⟨0, 8, 2, 12⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 12⟩) (by decide) node_146

theorem node_1195 : Outcome ⟨0, 8, 2, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 12⟩) (by decide) node_146

theorem node_1196 : Outcome ⟨0, 9, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 1, 2⟩, ⟨0, 7, 1, 4⟩, ⟨0, 9, 0, 2⟩]
  exact AllWinning.cons node_942 (AllWinning.cons node_724 (AllWinning.cons node_947 (AllWinning.nil)))

theorem node_1197 : Outcome ⟨0, 9, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 1, 2⟩, ⟨0, 7, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 9, 0, 2⟩]
  exact AllWinning.cons node_942 (AllWinning.cons node_724 (AllWinning.cons node_489 (AllWinning.cons node_359 (AllWinning.cons node_947 (AllWinning.nil)))))

theorem node_1198 : Outcome ⟨0, 9, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 1, 2⟩, ⟨0, 7, 1, 4⟩, ⟨0, 6, 1, 6⟩, ⟨0, 5, 1, 8⟩, ⟨0, 4, 1, 10⟩, ⟨0, 3, 1, 12⟩, ⟨0, 9, 0, 2⟩]
  exact AllWinning.cons node_942 (AllWinning.cons node_724 (AllWinning.cons node_489 (AllWinning.cons node_359 (AllWinning.cons node_255 (AllWinning.cons node_160 (AllWinning.cons node_947 (AllWinning.nil)))))))

theorem node_1199 : Outcome ⟨0, 9, 1, 10⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 16⟩) (by decide) node_39

theorem node_1200 : Outcome ⟨0, 9, 1, 16⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 16⟩) (by decide) node_39

theorem node_1201 : Outcome ⟨0, 10, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 4⟩) (by decide) node_730

theorem node_1202 : Outcome ⟨0, 10, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 4⟩) (by decide) node_730

theorem node_1203 : Outcome ⟨0, 10, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 4⟩) (by decide) node_730

theorem node_1204 : Outcome ⟨0, 10, 0, 20⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 20⟩) (by decide) node_9

theorem node_1205 : Outcome ⟨1, 0, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 9, 2⟩, ⟨1, 0, 8, 2⟩, ⟨1, 0, 7, 4⟩]
  exact AllWinning.cons node_907 (AllWinning.cons node_951 (AllWinning.cons node_735 (AllWinning.nil)))

theorem node_1206 : Outcome ⟨1, 0, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 9, 2⟩, ⟨1, 0, 8, 2⟩, ⟨1, 0, 7, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 0, 5, 8⟩]
  exact AllWinning.cons node_907 (AllWinning.cons node_951 (AllWinning.cons node_735 (AllWinning.cons node_498 (AllWinning.cons node_366 (AllWinning.nil)))))

theorem node_1207 : Outcome ⟨1, 0, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 9, 2⟩, ⟨1, 0, 8, 2⟩, ⟨1, 0, 7, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 0, 5, 8⟩, ⟨1, 0, 4, 10⟩, ⟨1, 0, 3, 12⟩]
  exact AllWinning.cons node_907 (AllWinning.cons node_951 (AllWinning.cons node_735 (AllWinning.cons node_498 (AllWinning.cons node_366 (AllWinning.cons node_264 (AllWinning.cons node_168 (AllWinning.nil)))))))

theorem node_1208 : Outcome ⟨1, 0, 9, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 16⟩) (by decide) node_61

theorem node_1209 : Outcome ⟨1, 0, 9, 16⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 16⟩) (by decide) node_61

theorem node_1210 : Outcome ⟨1, 1, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 8, 2⟩, ⟨1, 0, 8, 2⟩, ⟨1, 1, 7, 2⟩, ⟨1, 1, 6, 4⟩]
  exact AllWinning.cons node_911 (AllWinning.cons node_951 (AllWinning.cons node_956 (AllWinning.cons node_740 (AllWinning.nil))))

theorem node_1211 : Outcome ⟨1, 1, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 8, 2⟩, ⟨1, 0, 8, 2⟩, ⟨1, 1, 7, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 1, 5, 6⟩, ⟨1, 1, 4, 8⟩]
  exact AllWinning.cons node_911 (AllWinning.cons node_951 (AllWinning.cons node_956 (AllWinning.cons node_740 (AllWinning.cons node_503 (AllWinning.cons node_369 (AllWinning.nil))))))

theorem node_1212 : Outcome ⟨1, 1, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 8, 2⟩, ⟨1, 0, 8, 2⟩, ⟨1, 1, 7, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 1, 5, 6⟩, ⟨1, 1, 4, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 1, 2, 12⟩]
  exact AllWinning.cons node_911 (AllWinning.cons node_951 (AllWinning.cons node_956 (AllWinning.cons node_740 (AllWinning.cons node_503 (AllWinning.cons node_369 (AllWinning.cons node_268 (AllWinning.cons node_172 (AllWinning.nil))))))))

theorem node_1213 : Outcome ⟨1, 1, 8, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 16⟩) (by decide) node_78

theorem node_1214 : Outcome ⟨1, 1, 8, 22⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 16⟩) (by decide) node_78

theorem node_1215 : Outcome ⟨1, 2, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1216 : Outcome ⟨1, 2, 7, 10⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1217 : Outcome ⟨1, 2, 7, 18⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1218 : Outcome ⟨1, 2, 7, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1219 : Outcome ⟨1, 3, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.nil)))))

theorem node_1220 : Outcome ⟨1, 3, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.nil))))))))

theorem node_1221 : Outcome ⟨1, 3, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1222 : Outcome ⟨1, 3, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1223 : Outcome ⟨1, 3, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1224 : Outcome ⟨1, 3, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1225 : Outcome ⟨1, 3, 6, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1226 : Outcome ⟨1, 3, 6, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1227 : Outcome ⟨1, 3, 6, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1228 : Outcome ⟨1, 3, 6, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1229 : Outcome ⟨1, 3, 6, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1230 : Outcome ⟨1, 3, 6, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1231 : Outcome ⟨1, 3, 6, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1232 : Outcome ⟨1, 3, 6, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1233 : Outcome ⟨1, 3, 6, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1234 : Outcome ⟨1, 3, 6, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1235 : Outcome ⟨1, 3, 6, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 6, 2⟩, ⟨1, 2, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨1, 0, 6, 6⟩, ⟨1, 3, 5, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 3, 2, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_921 (AllWinning.cons node_960 (AllWinning.cons node_740 (AllWinning.cons node_498 (AllWinning.cons node_965 (AllWinning.cons node_746 (AllWinning.cons node_523 (AllWinning.cons node_375 (AllWinning.cons node_275 (AllWinning.cons node_181 (AllWinning.nil))))))))))

theorem node_1236 : Outcome ⟨1, 4, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1237 : Outcome ⟨1, 4, 5, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1238 : Outcome ⟨1, 4, 5, 10⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1239 : Outcome ⟨1, 4, 5, 12⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1240 : Outcome ⟨1, 4, 5, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1241 : Outcome ⟨1, 5, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 4, 2⟩, ⟨1, 4, 4, 2⟩, ⟨1, 3, 4, 4⟩, ⟨1, 5, 3, 2⟩, ⟨1, 5, 2, 4⟩]
  exact AllWinning.cons node_929 (AllWinning.cons node_969 (AllWinning.cons node_746 (AllWinning.cons node_975 (AllWinning.cons node_753 (AllWinning.nil)))))

theorem node_1242 : Outcome ⟨1, 5, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1243 : Outcome ⟨1, 5, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1244 : Outcome ⟨1, 5, 4, 10⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1245 : Outcome ⟨1, 5, 4, 12⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1246 : Outcome ⟨1, 5, 4, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 6⟩) (by decide) node_507

theorem node_1247 : Outcome ⟨1, 6, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.nil)))))

theorem node_1248 : Outcome ⟨1, 6, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))

theorem node_1249 : Outcome ⟨1, 6, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1250 : Outcome ⟨1, 6, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1251 : Outcome ⟨1, 6, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1252 : Outcome ⟨1, 6, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1253 : Outcome ⟨1, 6, 3, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1254 : Outcome ⟨1, 6, 3, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1255 : Outcome ⟨1, 6, 3, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1256 : Outcome ⟨1, 6, 3, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1257 : Outcome ⟨1, 6, 3, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1258 : Outcome ⟨1, 6, 3, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1259 : Outcome ⟨1, 6, 3, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1260 : Outcome ⟨1, 6, 3, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1261 : Outcome ⟨1, 6, 3, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1262 : Outcome ⟨1, 6, 3, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1263 : Outcome ⟨1, 6, 3, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 3, 2⟩, ⟨1, 5, 3, 2⟩, ⟨1, 4, 3, 4⟩, ⟨1, 3, 3, 6⟩, ⟨1, 2, 3, 8⟩, ⟨1, 1, 3, 10⟩, ⟨1, 0, 3, 12⟩, ⟨1, 6, 2, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 6, 0, 6⟩]
  exact AllWinning.cons node_932 (AllWinning.cons node_975 (AllWinning.cons node_749 (AllWinning.cons node_523 (AllWinning.cons node_372 (AllWinning.cons node_268 (AllWinning.cons node_168 (AllWinning.cons node_979 (AllWinning.cons node_757 (AllWinning.cons node_549 (AllWinning.nil))))))))))

theorem node_1264 : Outcome ⟨1, 7, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1265 : Outcome ⟨1, 7, 2, 10⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1266 : Outcome ⟨1, 7, 2, 18⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1267 : Outcome ⟨1, 7, 2, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 6⟩) (by decide) node_528

theorem node_1268 : Outcome ⟨1, 8, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 1, 2⟩, ⟨1, 7, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 8, 0, 2⟩]
  exact AllWinning.cons node_942 (AllWinning.cons node_984 (AllWinning.cons node_757 (AllWinning.cons node_988 (AllWinning.nil))))

theorem node_1269 : Outcome ⟨1, 8, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 1, 2⟩, ⟨1, 7, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 5, 1, 6⟩, ⟨1, 4, 1, 8⟩, ⟨1, 8, 0, 2⟩]
  exact AllWinning.cons node_942 (AllWinning.cons node_984 (AllWinning.cons node_757 (AllWinning.cons node_545 (AllWinning.cons node_378 (AllWinning.cons node_988 (AllWinning.nil))))))

theorem node_1270 : Outcome ⟨1, 8, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 1, 2⟩, ⟨1, 7, 1, 2⟩, ⟨1, 6, 1, 4⟩, ⟨1, 5, 1, 6⟩, ⟨1, 4, 1, 8⟩, ⟨1, 3, 1, 10⟩, ⟨1, 2, 1, 12⟩, ⟨1, 8, 0, 2⟩]
  exact AllWinning.cons node_942 (AllWinning.cons node_984 (AllWinning.cons node_757 (AllWinning.cons node_545 (AllWinning.cons node_378 (AllWinning.cons node_275 (AllWinning.cons node_176 (AllWinning.cons node_988 (AllWinning.nil))))))))

theorem node_1271 : Outcome ⟨1, 8, 1, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 16⟩) (by decide) node_61

theorem node_1272 : Outcome ⟨1, 8, 1, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 16⟩) (by decide) node_61

theorem node_1273 : Outcome ⟨1, 9, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 0, 2⟩, ⟨1, 8, 0, 2⟩, ⟨1, 7, 0, 4⟩]
  exact AllWinning.cons node_947 (AllWinning.cons node_988 (AllWinning.cons node_760 (AllWinning.nil)))

theorem node_1274 : Outcome ⟨1, 9, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 0, 2⟩, ⟨1, 8, 0, 2⟩, ⟨1, 7, 0, 4⟩, ⟨1, 6, 0, 6⟩, ⟨1, 5, 0, 8⟩]
  exact AllWinning.cons node_947 (AllWinning.cons node_988 (AllWinning.cons node_760 (AllWinning.cons node_549 (AllWinning.cons node_381 (AllWinning.nil)))))

theorem node_1275 : Outcome ⟨1, 9, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 0, 2⟩, ⟨1, 8, 0, 2⟩, ⟨1, 7, 0, 4⟩, ⟨1, 6, 0, 6⟩, ⟨1, 5, 0, 8⟩, ⟨1, 4, 0, 10⟩, ⟨1, 3, 0, 12⟩]
  exact AllWinning.cons node_947 (AllWinning.cons node_988 (AllWinning.cons node_760 (AllWinning.cons node_549 (AllWinning.cons node_381 (AllWinning.cons node_279 (AllWinning.cons node_181 (AllWinning.nil)))))))

theorem node_1276 : Outcome ⟨1, 9, 0, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 16⟩) (by decide) node_78

theorem node_1277 : Outcome ⟨1, 9, 0, 16⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 16⟩) (by decide) node_78

theorem node_1278 : Outcome ⟨2, 0, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 4⟩) (by decide) node_681

theorem node_1279 : Outcome ⟨2, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 4⟩) (by decide) node_681

theorem node_1280 : Outcome ⟨2, 0, 8, 12⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 12⟩) (by decide) node_188

theorem node_1281 : Outcome ⟨2, 0, 8, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 12⟩) (by decide) node_188

theorem node_1282 : Outcome ⟨2, 1, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1283 : Outcome ⟨2, 1, 7, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1284 : Outcome ⟨2, 1, 7, 18⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1285 : Outcome ⟨2, 1, 7, 20⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1286 : Outcome ⟨2, 2, 6, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1287 : Outcome ⟨2, 2, 6, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1288 : Outcome ⟨2, 2, 6, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1289 : Outcome ⟨2, 3, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1290 : Outcome ⟨2, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1291 : Outcome ⟨2, 3, 5, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1292 : Outcome ⟨2, 3, 5, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1293 : Outcome ⟨2, 4, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 4⟩) (by decide) node_700

theorem node_1294 : Outcome ⟨2, 4, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1295 : Outcome ⟨2, 4, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1296 : Outcome ⟨2, 4, 4, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1297 : Outcome ⟨2, 4, 4, 12⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1298 : Outcome ⟨2, 4, 4, 20⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 6⟩) (by decide) node_558

theorem node_1299 : Outcome ⟨2, 5, 3, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1300 : Outcome ⟨2, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1301 : Outcome ⟨2, 5, 3, 14⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1302 : Outcome ⟨2, 5, 3, 18⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1303 : Outcome ⟨2, 6, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 2⟩) (by decide) node_1015

theorem node_1304 : Outcome ⟨2, 6, 2, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 12⟩) (by decide) node_188

theorem node_1305 : Outcome ⟨2, 6, 2, 18⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 12⟩) (by decide) node_188

theorem node_1306 : Outcome ⟨2, 7, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1307 : Outcome ⟨2, 7, 1, 10⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1308 : Outcome ⟨2, 7, 1, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1309 : Outcome ⟨2, 7, 1, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 6⟩) (by decide) node_580

theorem node_1310 : Outcome ⟨2, 8, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 4⟩) (by decide) node_730

theorem node_1311 : Outcome ⟨2, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 4⟩) (by decide) node_730

theorem node_1312 : Outcome ⟨2, 8, 0, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1313 : Outcome ⟨2, 8, 0, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1314 : Outcome ⟨2, 8, 0, 38⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1315 : Outcome ⟨3, 0, 7, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 7, 2⟩) (by decide) node_993

theorem node_1316 : Outcome ⟨3, 0, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1317 : Outcome ⟨3, 0, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1318 : Outcome ⟨3, 0, 7, 18⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 8⟩) (by decide) node_406

theorem node_1319 : Outcome ⟨3, 1, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.nil)))))

theorem node_1320 : Outcome ⟨3, 1, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.nil))))))))

theorem node_1321 : Outcome ⟨3, 1, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1322 : Outcome ⟨3, 1, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1323 : Outcome ⟨3, 1, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1324 : Outcome ⟨3, 1, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1325 : Outcome ⟨3, 1, 6, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1326 : Outcome ⟨3, 1, 6, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1327 : Outcome ⟨3, 1, 6, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1328 : Outcome ⟨3, 1, 6, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1329 : Outcome ⟨3, 1, 6, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1330 : Outcome ⟨3, 1, 6, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1331 : Outcome ⟨3, 1, 6, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1332 : Outcome ⟨3, 1, 6, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1333 : Outcome ⟨3, 1, 6, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1334 : Outcome ⟨3, 1, 6, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1335 : Outcome ⟨3, 1, 6, 34⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 1, 6, 2⟩, ⟨1, 1, 6, 4⟩, ⟨0, 1, 6, 6⟩, ⟨3, 0, 6, 2⟩, ⟨3, 1, 5, 2⟩, ⟨3, 1, 4, 4⟩, ⟨3, 1, 3, 6⟩, ⟨3, 1, 2, 8⟩, ⟨3, 1, 1, 10⟩, ⟨3, 1, 0, 12⟩]
  exact AllWinning.cons node_998 (AllWinning.cons node_740 (AllWinning.cons node_472 (AllWinning.cons node_1029 (AllWinning.cons node_1034 (AllWinning.cons node_800 (AllWinning.cons node_601 (AllWinning.cons node_421 (AllWinning.cons node_302 (AllWinning.cons node_229 (AllWinning.nil))))))))))

theorem node_1336 : Outcome ⟨3, 2, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1337 : Outcome ⟨3, 2, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1338 : Outcome ⟨3, 2, 5, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1339 : Outcome ⟨3, 2, 5, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 2⟩) (by decide) node_1003

theorem node_1340 : Outcome ⟨3, 3, 4, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 3, 2⟩) (by decide) node_1042

end RQ9F1
