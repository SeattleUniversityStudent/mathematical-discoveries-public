import Chunk12
set_option autoImplicit false
namespace RQ9F1

theorem node_3433 : Outcome ⟨1, 8, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 6, 2⟩, ⟨1, 7, 6, 2⟩, ⟨1, 6, 6, 4⟩, ⟨1, 5, 6, 6⟩, ⟨1, 4, 6, 8⟩, ⟨1, 8, 5, 2⟩, ⟨1, 8, 4, 4⟩, ⟨1, 8, 3, 6⟩, ⟨1, 8, 2, 8⟩]
  exact AllWinning.cons node_2862 (AllWinning.cons node_2914 (AllWinning.cons node_2454 (AllWinning.cons node_1953 (AllWinning.cons node_1611 (AllWinning.cons node_2918 (AllWinning.cons node_2459 (AllWinning.cons node_1966 (AllWinning.cons node_1625 (AllWinning.nil)))))))))

theorem node_3434 : Outcome ⟨1, 8, 6, 12⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 10⟩) (by decide) node_1223

theorem node_3435 : Outcome ⟨1, 8, 6, 16⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 10⟩) (by decide) node_1223

theorem node_3436 : Outcome ⟨1, 9, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.nil)))))

theorem node_3437 : Outcome ⟨1, 9, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.nil)))))))))

theorem node_3438 : Outcome ⟨1, 9, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil))))))))))))

theorem node_3439 : Outcome ⟨1, 9, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil))))))))))))))

theorem node_3440 : Outcome ⟨1, 9, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3441 : Outcome ⟨1, 9, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3442 : Outcome ⟨1, 9, 5, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3443 : Outcome ⟨1, 9, 5, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3444 : Outcome ⟨1, 9, 5, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3445 : Outcome ⟨1, 9, 5, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3446 : Outcome ⟨1, 9, 5, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3447 : Outcome ⟨1, 9, 5, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3448 : Outcome ⟨1, 9, 5, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3449 : Outcome ⟨1, 9, 5, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 5, 2⟩, ⟨1, 8, 5, 2⟩, ⟨1, 7, 5, 4⟩, ⟨1, 6, 5, 6⟩, ⟨1, 5, 5, 8⟩, ⟨1, 4, 5, 10⟩, ⟨1, 3, 5, 12⟩, ⟨1, 2, 5, 14⟩, ⟨1, 1, 5, 16⟩, ⟨1, 0, 5, 18⟩, ⟨1, 9, 4, 2⟩, ⟨1, 9, 3, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 9, 0, 10⟩]
  exact AllWinning.cons node_2865 (AllWinning.cons node_2918 (AllWinning.cons node_2456 (AllWinning.cons node_1956 (AllWinning.cons node_1614 (AllWinning.cons node_1238 (AllWinning.cons node_967 (AllWinning.cons node_743 (AllWinning.cons node_504 (AllWinning.cons node_367 (AllWinning.cons node_2922 (AllWinning.cons node_2465 (AllWinning.cons node_1971 (AllWinning.cons node_1629 (AllWinning.cons node_1276 (AllWinning.nil)))))))))))))))

theorem node_3450 : Outcome ⟨1, 10, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 4, 2⟩, ⟨1, 9, 4, 2⟩, ⟨1, 8, 4, 4⟩, ⟨1, 10, 3, 2⟩, ⟨1, 10, 2, 4⟩]
  exact AllWinning.cons node_2868 (AllWinning.cons node_2922 (AllWinning.cons node_2459 (AllWinning.cons node_2925 (AllWinning.cons node_2469 (AllWinning.nil)))))

theorem node_3451 : Outcome ⟨1, 10, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 4, 2⟩, ⟨1, 9, 4, 2⟩, ⟨1, 8, 4, 4⟩, ⟨1, 7, 4, 6⟩, ⟨1, 6, 4, 8⟩, ⟨1, 10, 3, 2⟩, ⟨1, 10, 2, 4⟩, ⟨1, 10, 1, 6⟩, ⟨1, 10, 0, 8⟩]
  exact AllWinning.cons node_2868 (AllWinning.cons node_2922 (AllWinning.cons node_2459 (AllWinning.cons node_1960 (AllWinning.cons node_1617 (AllWinning.cons node_2925 (AllWinning.cons node_2469 (AllWinning.cons node_1975 (AllWinning.cons node_1631 (AllWinning.nil)))))))))

theorem node_3452 : Outcome ⟨1, 10, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 4, 2⟩, ⟨1, 9, 4, 2⟩, ⟨1, 8, 4, 4⟩, ⟨1, 7, 4, 6⟩, ⟨1, 6, 4, 8⟩, ⟨1, 5, 4, 10⟩, ⟨1, 4, 4, 12⟩, ⟨1, 10, 3, 2⟩, ⟨1, 10, 2, 4⟩, ⟨1, 10, 1, 6⟩, ⟨1, 10, 0, 8⟩]
  exact AllWinning.cons node_2868 (AllWinning.cons node_2922 (AllWinning.cons node_2459 (AllWinning.cons node_1960 (AllWinning.cons node_1617 (AllWinning.cons node_1244 (AllWinning.cons node_973 (AllWinning.cons node_2925 (AllWinning.cons node_2469 (AllWinning.cons node_1975 (AllWinning.cons node_1631 (AllWinning.nil)))))))))))

theorem node_3453 : Outcome ⟨1, 10, 4, 10⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 16⟩) (by decide) node_512

theorem node_3454 : Outcome ⟨1, 10, 4, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 16⟩) (by decide) node_512

theorem node_3455 : Outcome ⟨1, 11, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 3, 2⟩) (by decide) node_2872

theorem node_3456 : Outcome ⟨1, 11, 3, 8⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 10⟩) (by decide) node_1251

theorem node_3457 : Outcome ⟨1, 11, 3, 16⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 10⟩) (by decide) node_1251

theorem node_3458 : Outcome ⟨1, 12, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 2, 2⟩, ⟨1, 11, 2, 2⟩, ⟨1, 10, 2, 4⟩, ⟨1, 12, 1, 2⟩, ⟨1, 12, 0, 4⟩]
  exact AllWinning.cons node_2877 (AllWinning.cons node_2930 (AllWinning.cons node_2469 (AllWinning.cons node_2933 (AllWinning.cons node_2476 (AllWinning.nil)))))

theorem node_3459 : Outcome ⟨1, 12, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 2, 2⟩, ⟨1, 11, 2, 2⟩, ⟨1, 10, 2, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 8, 2, 8⟩, ⟨1, 12, 1, 2⟩, ⟨1, 12, 0, 4⟩]
  exact AllWinning.cons node_2877 (AllWinning.cons node_2930 (AllWinning.cons node_2469 (AllWinning.cons node_1971 (AllWinning.cons node_1625 (AllWinning.cons node_2933 (AllWinning.cons node_2476 (AllWinning.nil)))))))

theorem node_3460 : Outcome ⟨1, 12, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 2, 2⟩, ⟨1, 11, 2, 2⟩, ⟨1, 10, 2, 4⟩, ⟨1, 9, 2, 6⟩, ⟨1, 8, 2, 8⟩, ⟨1, 7, 2, 10⟩, ⟨1, 6, 2, 12⟩, ⟨1, 12, 1, 2⟩, ⟨1, 12, 0, 4⟩]
  exact AllWinning.cons node_2877 (AllWinning.cons node_2930 (AllWinning.cons node_2469 (AllWinning.cons node_1971 (AllWinning.cons node_1625 (AllWinning.cons node_1265 (AllWinning.cons node_981 (AllWinning.cons node_2933 (AllWinning.cons node_2476 (AllWinning.nil)))))))))

theorem node_3461 : Outcome ⟨1, 12, 2, 10⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 16⟩) (by decide) node_533

theorem node_3462 : Outcome ⟨1, 12, 2, 12⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 16⟩) (by decide) node_533

theorem node_3463 : Outcome ⟨1, 12, 2, 26⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 16⟩) (by decide) node_533

theorem node_3464 : Outcome ⟨1, 13, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 1, 2⟩, ⟨1, 12, 1, 2⟩, ⟨1, 11, 1, 4⟩, ⟨1, 13, 0, 2⟩]
  exact AllWinning.cons node_2883 (AllWinning.cons node_2933 (AllWinning.cons node_2474 (AllWinning.cons node_2935 (AllWinning.nil))))

theorem node_3465 : Outcome ⟨1, 13, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 1, 2⟩, ⟨1, 12, 1, 2⟩, ⟨1, 11, 1, 4⟩, ⟨1, 10, 1, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 13, 0, 2⟩]
  exact AllWinning.cons node_2883 (AllWinning.cons node_2933 (AllWinning.cons node_2474 (AllWinning.cons node_1975 (AllWinning.cons node_1629 (AllWinning.cons node_2935 (AllWinning.nil))))))

theorem node_3466 : Outcome ⟨1, 13, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 1, 2⟩, ⟨1, 12, 1, 2⟩, ⟨1, 11, 1, 4⟩, ⟨1, 10, 1, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 8, 1, 10⟩, ⟨1, 7, 1, 12⟩, ⟨1, 13, 0, 2⟩]
  exact AllWinning.cons node_2883 (AllWinning.cons node_2933 (AllWinning.cons node_2474 (AllWinning.cons node_1975 (AllWinning.cons node_1629 (AllWinning.cons node_1271 (AllWinning.cons node_986 (AllWinning.cons node_2935 (AllWinning.nil))))))))

theorem node_3467 : Outcome ⟨1, 13, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 1, 2⟩, ⟨1, 12, 1, 2⟩, ⟨1, 11, 1, 4⟩, ⟨1, 10, 1, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 8, 1, 10⟩, ⟨1, 7, 1, 12⟩, ⟨1, 6, 1, 14⟩, ⟨1, 5, 1, 16⟩, ⟨1, 13, 0, 2⟩]
  exact AllWinning.cons node_2883 (AllWinning.cons node_2933 (AllWinning.cons node_2474 (AllWinning.cons node_1975 (AllWinning.cons node_1629 (AllWinning.cons node_1271 (AllWinning.cons node_986 (AllWinning.cons node_758 (AllWinning.cons node_546 (AllWinning.cons node_2935 (AllWinning.nil))))))))))

theorem node_3468 : Outcome ⟨1, 13, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 1, 2⟩, ⟨1, 12, 1, 2⟩, ⟨1, 11, 1, 4⟩, ⟨1, 10, 1, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 8, 1, 10⟩, ⟨1, 7, 1, 12⟩, ⟨1, 6, 1, 14⟩, ⟨1, 5, 1, 16⟩, ⟨1, 4, 1, 18⟩, ⟨1, 3, 1, 20⟩, ⟨1, 13, 0, 2⟩]
  exact AllWinning.cons node_2883 (AllWinning.cons node_2933 (AllWinning.cons node_2474 (AllWinning.cons node_1975 (AllWinning.cons node_1629 (AllWinning.cons node_1271 (AllWinning.cons node_986 (AllWinning.cons node_758 (AllWinning.cons node_546 (AllWinning.cons node_379 (AllWinning.cons node_276 (AllWinning.cons node_2935 (AllWinning.nil))))))))))))

theorem node_3469 : Outcome ⟨1, 13, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 1, 2⟩, ⟨1, 12, 1, 2⟩, ⟨1, 11, 1, 4⟩, ⟨1, 10, 1, 6⟩, ⟨1, 9, 1, 8⟩, ⟨1, 8, 1, 10⟩, ⟨1, 7, 1, 12⟩, ⟨1, 6, 1, 14⟩, ⟨1, 5, 1, 16⟩, ⟨1, 4, 1, 18⟩, ⟨1, 3, 1, 20⟩, ⟨1, 2, 1, 22⟩, ⟨1, 1, 1, 24⟩, ⟨1, 13, 0, 2⟩]
  exact AllWinning.cons node_2883 (AllWinning.cons node_2933 (AllWinning.cons node_2474 (AllWinning.cons node_1975 (AllWinning.cons node_1629 (AllWinning.cons node_1271 (AllWinning.cons node_986 (AllWinning.cons node_758 (AllWinning.cons node_546 (AllWinning.cons node_379 (AllWinning.cons node_276 (AllWinning.cons node_177 (AllWinning.cons node_116 (AllWinning.cons node_2935 (AllWinning.nil))))))))))))))

theorem node_3470 : Outcome ⟨1, 14, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 0, 2⟩, ⟨1, 13, 0, 2⟩, ⟨1, 12, 0, 4⟩]
  exact AllWinning.cons node_2886 (AllWinning.cons node_2935 (AllWinning.cons node_2476 (AllWinning.nil)))

theorem node_3471 : Outcome ⟨1, 14, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 0, 2⟩, ⟨1, 13, 0, 2⟩, ⟨1, 12, 0, 4⟩, ⟨1, 11, 0, 6⟩, ⟨1, 10, 0, 8⟩]
  exact AllWinning.cons node_2886 (AllWinning.cons node_2935 (AllWinning.cons node_2476 (AllWinning.cons node_1979 (AllWinning.cons node_1631 (AllWinning.nil)))))

theorem node_3472 : Outcome ⟨1, 14, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 0, 2⟩, ⟨1, 13, 0, 2⟩, ⟨1, 12, 0, 4⟩, ⟨1, 11, 0, 6⟩, ⟨1, 10, 0, 8⟩, ⟨1, 9, 0, 10⟩, ⟨1, 8, 0, 12⟩]
  exact AllWinning.cons node_2886 (AllWinning.cons node_2935 (AllWinning.cons node_2476 (AllWinning.cons node_1979 (AllWinning.cons node_1631 (AllWinning.cons node_1276 (AllWinning.cons node_990 (AllWinning.nil)))))))

theorem node_3473 : Outcome ⟨1, 14, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 0, 2⟩, ⟨1, 13, 0, 2⟩, ⟨1, 12, 0, 4⟩, ⟨1, 11, 0, 6⟩, ⟨1, 10, 0, 8⟩, ⟨1, 9, 0, 10⟩, ⟨1, 8, 0, 12⟩, ⟨1, 7, 0, 14⟩, ⟨1, 6, 0, 16⟩]
  exact AllWinning.cons node_2886 (AllWinning.cons node_2935 (AllWinning.cons node_2476 (AllWinning.cons node_1979 (AllWinning.cons node_1631 (AllWinning.cons node_1276 (AllWinning.cons node_990 (AllWinning.cons node_763 (AllWinning.cons node_551 (AllWinning.nil)))))))))

theorem node_3474 : Outcome ⟨1, 14, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 0, 2⟩, ⟨1, 13, 0, 2⟩, ⟨1, 12, 0, 4⟩, ⟨1, 11, 0, 6⟩, ⟨1, 10, 0, 8⟩, ⟨1, 9, 0, 10⟩, ⟨1, 8, 0, 12⟩, ⟨1, 7, 0, 14⟩, ⟨1, 6, 0, 16⟩, ⟨1, 5, 0, 18⟩, ⟨1, 4, 0, 20⟩]
  exact AllWinning.cons node_2886 (AllWinning.cons node_2935 (AllWinning.cons node_2476 (AllWinning.cons node_1979 (AllWinning.cons node_1631 (AllWinning.cons node_1276 (AllWinning.cons node_990 (AllWinning.cons node_763 (AllWinning.cons node_551 (AllWinning.cons node_382 (AllWinning.cons node_280 (AllWinning.nil)))))))))))

theorem node_3475 : Outcome ⟨1, 14, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 0, 2⟩, ⟨1, 13, 0, 2⟩, ⟨1, 12, 0, 4⟩, ⟨1, 11, 0, 6⟩, ⟨1, 10, 0, 8⟩, ⟨1, 9, 0, 10⟩, ⟨1, 8, 0, 12⟩, ⟨1, 7, 0, 14⟩, ⟨1, 6, 0, 16⟩, ⟨1, 5, 0, 18⟩, ⟨1, 4, 0, 20⟩, ⟨1, 3, 0, 22⟩, ⟨1, 2, 0, 24⟩]
  exact AllWinning.cons node_2886 (AllWinning.cons node_2935 (AllWinning.cons node_2476 (AllWinning.cons node_1979 (AllWinning.cons node_1631 (AllWinning.cons node_1276 (AllWinning.cons node_990 (AllWinning.cons node_763 (AllWinning.cons node_551 (AllWinning.cons node_382 (AllWinning.cons node_280 (AllWinning.cons node_182 (AllWinning.cons node_119 (AllWinning.nil)))))))))))))

theorem node_3476 : Outcome ⟨1, 14, 0, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 26⟩) (by decide) node_83

theorem node_3477 : Outcome ⟨1, 14, 0, 26⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 26⟩) (by decide) node_83

theorem node_3478 : Outcome ⟨2, 0, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 10, 6⟩) (by decide) node_1984

theorem node_3479 : Outcome ⟨2, 0, 13, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 10, 6⟩) (by decide) node_1984

theorem node_3480 : Outcome ⟨2, 0, 13, 22⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 22⟩) (by decide) node_193

theorem node_3481 : Outcome ⟨2, 1, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 12, 2⟩, ⟨0, 1, 12, 4⟩, ⟨2, 0, 12, 2⟩, ⟨2, 1, 11, 2⟩, ⟨2, 1, 10, 4⟩]
  exact AllWinning.cons node_2893 (AllWinning.cons node_2368 (AllWinning.cons node_2938 (AllWinning.cons node_2944 (AllWinning.cons node_2484 (AllWinning.nil)))))

theorem node_3482 : Outcome ⟨2, 1, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 12, 2⟩, ⟨0, 1, 12, 4⟩, ⟨2, 0, 12, 2⟩, ⟨2, 1, 11, 2⟩, ⟨2, 1, 10, 4⟩, ⟨2, 1, 9, 6⟩, ⟨2, 1, 8, 8⟩]
  exact AllWinning.cons node_2893 (AllWinning.cons node_2368 (AllWinning.cons node_2938 (AllWinning.cons node_2944 (AllWinning.cons node_2484 (AllWinning.cons node_1988 (AllWinning.cons node_1641 (AllWinning.nil)))))))

theorem node_3483 : Outcome ⟨2, 1, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 1, 12, 2⟩, ⟨0, 1, 12, 4⟩, ⟨2, 0, 12, 2⟩, ⟨2, 1, 11, 2⟩, ⟨2, 1, 10, 4⟩, ⟨2, 1, 9, 6⟩, ⟨2, 1, 8, 8⟩, ⟨2, 1, 7, 10⟩, ⟨2, 1, 6, 12⟩]
  exact AllWinning.cons node_2893 (AllWinning.cons node_2368 (AllWinning.cons node_2938 (AllWinning.cons node_2944 (AllWinning.cons node_2484 (AllWinning.cons node_1988 (AllWinning.cons node_1641 (AllWinning.cons node_1283 (AllWinning.cons node_1000 (AllWinning.nil)))))))))

theorem node_3484 : Outcome ⟨2, 1, 12, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3485 : Outcome ⟨2, 1, 12, 12⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3486 : Outcome ⟨2, 1, 12, 26⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3487 : Outcome ⟨2, 2, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 8, 6⟩) (by decide) node_1993

theorem node_3488 : Outcome ⟨2, 2, 11, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 8, 6⟩) (by decide) node_1993

theorem node_3489 : Outcome ⟨2, 3, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 10, 6⟩) (by decide) node_1984

theorem node_3490 : Outcome ⟨2, 3, 10, 10⟩ true :=
  Outcome.win (q := ⟨2, 0, 10, 6⟩) (by decide) node_1984

theorem node_3491 : Outcome ⟨2, 3, 10, 20⟩ true :=
  Outcome.win (q := ⟨2, 0, 10, 6⟩) (by decide) node_1984

theorem node_3492 : Outcome ⟨2, 3, 10, 22⟩ true :=
  Outcome.win (q := ⟨2, 0, 10, 6⟩) (by decide) node_1984

theorem node_3493 : Outcome ⟨2, 4, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 9, 2⟩, ⟨0, 4, 9, 4⟩, ⟨2, 3, 9, 2⟩, ⟨2, 2, 9, 4⟩, ⟨2, 4, 8, 2⟩, ⟨2, 4, 7, 4⟩]
  exact AllWinning.cons node_2903 (AllWinning.cons node_2382 (AllWinning.cons node_2949 (AllWinning.cons node_2488 (AllWinning.cons node_2954 (AllWinning.cons node_2495 (AllWinning.nil))))))

theorem node_3494 : Outcome ⟨2, 4, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 9, 2⟩, ⟨0, 4, 9, 4⟩, ⟨2, 3, 9, 2⟩, ⟨2, 2, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨2, 0, 9, 8⟩, ⟨2, 4, 8, 2⟩, ⟨2, 4, 7, 4⟩, ⟨2, 4, 6, 6⟩, ⟨2, 4, 5, 8⟩]
  exact AllWinning.cons node_2903 (AllWinning.cons node_2382 (AllWinning.cons node_2949 (AllWinning.cons node_2488 (AllWinning.cons node_1988 (AllWinning.cons node_1636 (AllWinning.cons node_2954 (AllWinning.cons node_2495 (AllWinning.cons node_2012 (AllWinning.cons node_1651 (AllWinning.nil))))))))))

theorem node_3495 : Outcome ⟨2, 4, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 4, 9, 2⟩, ⟨0, 4, 9, 4⟩, ⟨2, 3, 9, 2⟩, ⟨2, 2, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨2, 0, 9, 8⟩, ⟨2, 4, 8, 2⟩, ⟨2, 4, 7, 4⟩, ⟨2, 4, 6, 6⟩, ⟨2, 4, 5, 8⟩, ⟨2, 4, 4, 10⟩, ⟨2, 4, 3, 12⟩]
  exact AllWinning.cons node_2903 (AllWinning.cons node_2382 (AllWinning.cons node_2949 (AllWinning.cons node_2488 (AllWinning.cons node_1988 (AllWinning.cons node_1636 (AllWinning.cons node_2954 (AllWinning.cons node_2495 (AllWinning.cons node_2012 (AllWinning.cons node_1651 (AllWinning.cons node_1296 (AllWinning.cons node_1013 (AllWinning.nil))))))))))))

theorem node_3496 : Outcome ⟨2, 4, 9, 10⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3497 : Outcome ⟨2, 4, 9, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3498 : Outcome ⟨2, 4, 9, 28⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3499 : Outcome ⟨2, 5, 8, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 8, 6⟩) (by decide) node_1993

theorem node_3500 : Outcome ⟨2, 5, 8, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 8, 6⟩) (by decide) node_1993

theorem node_3501 : Outcome ⟨2, 5, 8, 26⟩ true :=
  Outcome.win (q := ⟨2, 2, 8, 6⟩) (by decide) node_1993

theorem node_3502 : Outcome ⟨2, 5, 8, 28⟩ true :=
  Outcome.win (q := ⟨2, 2, 8, 6⟩) (by decide) node_1993

theorem node_3503 : Outcome ⟨2, 6, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 6⟩) (by decide) node_1996

theorem node_3504 : Outcome ⟨2, 6, 7, 8⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 6⟩) (by decide) node_1996

theorem node_3505 : Outcome ⟨2, 6, 7, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 6⟩) (by decide) node_1996

theorem node_3506 : Outcome ⟨2, 6, 7, 24⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 6⟩) (by decide) node_1996

theorem node_3507 : Outcome ⟨2, 7, 6, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3508 : Outcome ⟨2, 7, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3509 : Outcome ⟨2, 7, 6, 12⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3510 : Outcome ⟨2, 7, 6, 24⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3511 : Outcome ⟨2, 8, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 6⟩) (by decide) node_2042

theorem node_3512 : Outcome ⟨2, 8, 5, 6⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 6⟩) (by decide) node_2042

theorem node_3513 : Outcome ⟨2, 8, 5, 26⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 6⟩) (by decide) node_2042

theorem node_3514 : Outcome ⟨2, 8, 5, 28⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 6⟩) (by decide) node_2042

theorem node_3515 : Outcome ⟨2, 9, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 4, 2⟩, ⟨0, 9, 4, 4⟩, ⟨2, 8, 4, 2⟩, ⟨2, 7, 4, 4⟩, ⟨2, 9, 3, 2⟩, ⟨2, 9, 2, 4⟩]
  exact AllWinning.cons node_2922 (AllWinning.cons node_2405 (AllWinning.cons node_2970 (AllWinning.cons node_2507 (AllWinning.cons node_2975 (AllWinning.cons node_2518 (AllWinning.nil))))))

theorem node_3516 : Outcome ⟨2, 9, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 4, 2⟩, ⟨0, 9, 4, 4⟩, ⟨2, 8, 4, 2⟩, ⟨2, 7, 4, 4⟩, ⟨2, 6, 4, 6⟩, ⟨2, 5, 4, 8⟩, ⟨2, 9, 3, 2⟩, ⟨2, 9, 2, 4⟩, ⟨2, 9, 1, 6⟩, ⟨2, 9, 0, 8⟩]
  exact AllWinning.cons node_2922 (AllWinning.cons node_2405 (AllWinning.cons node_2970 (AllWinning.cons node_2507 (AllWinning.cons node_2021 (AllWinning.cons node_1657 (AllWinning.cons node_2975 (AllWinning.cons node_2518 (AllWinning.cons node_2046 (AllWinning.cons node_1673 (AllWinning.nil))))))))))

theorem node_3517 : Outcome ⟨2, 9, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 4, 2⟩, ⟨0, 9, 4, 4⟩, ⟨2, 8, 4, 2⟩, ⟨2, 7, 4, 4⟩, ⟨2, 6, 4, 6⟩, ⟨2, 5, 4, 8⟩, ⟨2, 4, 4, 10⟩, ⟨2, 3, 4, 12⟩, ⟨2, 9, 3, 2⟩, ⟨2, 9, 2, 4⟩, ⟨2, 9, 1, 6⟩, ⟨2, 9, 0, 8⟩]
  exact AllWinning.cons node_2922 (AllWinning.cons node_2405 (AllWinning.cons node_2970 (AllWinning.cons node_2507 (AllWinning.cons node_2021 (AllWinning.cons node_1657 (AllWinning.cons node_1296 (AllWinning.cons node_1009 (AllWinning.cons node_2975 (AllWinning.cons node_2518 (AllWinning.cons node_2046 (AllWinning.cons node_1673 (AllWinning.nil))))))))))))

theorem node_3518 : Outcome ⟨2, 9, 4, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3519 : Outcome ⟨2, 9, 4, 22⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3520 : Outcome ⟨2, 9, 4, 28⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3521 : Outcome ⟨2, 10, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3522 : Outcome ⟨2, 10, 3, 10⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3523 : Outcome ⟨2, 10, 3, 20⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3524 : Outcome ⟨2, 10, 3, 22⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 6⟩) (by decide) node_2026

theorem node_3525 : Outcome ⟨2, 11, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 6⟩) (by decide) node_2042

theorem node_3526 : Outcome ⟨2, 11, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 6⟩) (by decide) node_2042

theorem node_3527 : Outcome ⟨2, 12, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 1, 2⟩, ⟨0, 12, 1, 4⟩, ⟨2, 11, 1, 2⟩, ⟨2, 10, 1, 4⟩, ⟨2, 12, 0, 2⟩]
  exact AllWinning.cons node_2933 (AllWinning.cons node_2420 (AllWinning.cons node_2982 (AllWinning.cons node_2521 (AllWinning.cons node_2985 (AllWinning.nil)))))

theorem node_3528 : Outcome ⟨2, 12, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 1, 2⟩, ⟨0, 12, 1, 4⟩, ⟨2, 11, 1, 2⟩, ⟨2, 10, 1, 4⟩, ⟨2, 9, 1, 6⟩, ⟨2, 8, 1, 8⟩, ⟨2, 12, 0, 2⟩]
  exact AllWinning.cons node_2933 (AllWinning.cons node_2420 (AllWinning.cons node_2982 (AllWinning.cons node_2521 (AllWinning.cons node_2046 (AllWinning.cons node_1667 (AllWinning.cons node_2985 (AllWinning.nil)))))))

theorem node_3529 : Outcome ⟨2, 12, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 1, 2⟩, ⟨0, 12, 1, 4⟩, ⟨2, 11, 1, 2⟩, ⟨2, 10, 1, 4⟩, ⟨2, 9, 1, 6⟩, ⟨2, 8, 1, 8⟩, ⟨2, 7, 1, 10⟩, ⟨2, 6, 1, 12⟩, ⟨2, 12, 0, 2⟩]
  exact AllWinning.cons node_2933 (AllWinning.cons node_2420 (AllWinning.cons node_2982 (AllWinning.cons node_2521 (AllWinning.cons node_2046 (AllWinning.cons node_1667 (AllWinning.cons node_1307 (AllWinning.cons node_1021 (AllWinning.cons node_2985 (AllWinning.nil)))))))))

theorem node_3530 : Outcome ⟨2, 12, 1, 10⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3531 : Outcome ⟨2, 12, 1, 12⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3532 : Outcome ⟨2, 12, 1, 26⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3533 : Outcome ⟨2, 13, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 0, 6⟩) (by decide) node_2051

theorem node_3534 : Outcome ⟨2, 13, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 0, 6⟩) (by decide) node_2051

theorem node_3535 : Outcome ⟨2, 13, 0, 22⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 22⟩) (by decide) node_214

theorem node_3536 : Outcome ⟨3, 0, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 2⟩) (by decide) node_2991

theorem node_3537 : Outcome ⟨3, 0, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 2⟩) (by decide) node_2991

theorem node_3538 : Outcome ⟨3, 0, 12, 18⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 18⟩) (by decide) node_411

theorem node_3539 : Outcome ⟨3, 1, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 2⟩) (by decide) node_2991

theorem node_3540 : Outcome ⟨3, 1, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 10⟩) (by decide) node_1323

theorem node_3541 : Outcome ⟨3, 1, 11, 16⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 10⟩) (by decide) node_1323

theorem node_3542 : Outcome ⟨3, 2, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 2, 10, 2⟩, ⟨1, 2, 10, 4⟩, ⟨3, 1, 10, 2⟩, ⟨3, 0, 10, 4⟩, ⟨3, 2, 9, 2⟩, ⟨3, 2, 8, 4⟩]
  exact AllWinning.cons node_2947 (AllWinning.cons node_2438 (AllWinning.cons node_2996 (AllWinning.cons node_2530 (AllWinning.cons node_3001 (AllWinning.cons node_2540 (AllWinning.nil))))))

theorem node_3543 : Outcome ⟨3, 2, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 6⟩) (by decide) node_1874

theorem node_3544 : Outcome ⟨3, 2, 10, 10⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 6⟩) (by decide) node_1874

theorem node_3545 : Outcome ⟨3, 2, 10, 20⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 6⟩) (by decide) node_1874

theorem node_3546 : Outcome ⟨3, 2, 10, 22⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 6⟩) (by decide) node_1874

theorem node_3547 : Outcome ⟨3, 3, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3548 : Outcome ⟨3, 3, 9, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3549 : Outcome ⟨3, 3, 9, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3550 : Outcome ⟨3, 3, 9, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 18⟩) (by decide) node_434

theorem node_3551 : Outcome ⟨3, 4, 8, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3552 : Outcome ⟨3, 4, 8, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3553 : Outcome ⟨3, 5, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 6, 2⟩) (by decide) node_3014

theorem node_3554 : Outcome ⟨3, 5, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 6⟩) (by decide) node_2067

theorem node_3555 : Outcome ⟨3, 5, 7, 10⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 6⟩) (by decide) node_2067

theorem node_3556 : Outcome ⟨3, 5, 7, 20⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 6⟩) (by decide) node_2067

theorem node_3557 : Outcome ⟨3, 6, 6, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 6, 2⟩) (by decide) node_3014

theorem node_3558 : Outcome ⟨3, 6, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 10⟩) (by decide) node_1323

theorem node_3559 : Outcome ⟨3, 6, 6, 16⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 10⟩) (by decide) node_1323

theorem node_3560 : Outcome ⟨3, 6, 6, 18⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 10⟩) (by decide) node_1323

theorem node_3561 : Outcome ⟨3, 7, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 5, 2⟩) (by decide) node_3018

theorem node_3562 : Outcome ⟨3, 7, 5, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 6⟩) (by decide) node_2098

theorem node_3563 : Outcome ⟨3, 7, 5, 10⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 6⟩) (by decide) node_2098

theorem node_3564 : Outcome ⟨3, 7, 5, 20⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 6⟩) (by decide) node_2098

theorem node_3565 : Outcome ⟨3, 8, 4, 2⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3566 : Outcome ⟨3, 8, 4, 24⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3567 : Outcome ⟨3, 8, 4, 28⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3568 : Outcome ⟨3, 9, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3569 : Outcome ⟨3, 9, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3570 : Outcome ⟨3, 9, 3, 8⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3571 : Outcome ⟨3, 9, 3, 18⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 18⟩) (by decide) node_411

theorem node_3572 : Outcome ⟨3, 10, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 2, 2⟩, ⟨1, 10, 2, 4⟩, ⟨3, 9, 2, 2⟩, ⟨3, 8, 2, 4⟩, ⟨3, 10, 1, 2⟩, ⟨3, 10, 0, 4⟩]
  exact AllWinning.cons node_2980 (AllWinning.cons node_2469 (AllWinning.cons node_3030 (AllWinning.cons node_2564 (AllWinning.cons node_3035 (AllWinning.cons node_2574 (AllWinning.nil))))))

theorem node_3573 : Outcome ⟨3, 10, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 6⟩) (by decide) node_1917

theorem node_3574 : Outcome ⟨3, 10, 2, 10⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 6⟩) (by decide) node_1917

theorem node_3575 : Outcome ⟨3, 10, 2, 20⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 6⟩) (by decide) node_1917

theorem node_3576 : Outcome ⟨3, 10, 2, 22⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 6⟩) (by decide) node_1917

theorem node_3577 : Outcome ⟨3, 11, 1, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 0, 2⟩) (by decide) node_3040

theorem node_3578 : Outcome ⟨3, 11, 1, 8⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 10⟩) (by decide) node_1354

theorem node_3579 : Outcome ⟨3, 11, 1, 16⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 10⟩) (by decide) node_1354

theorem node_3580 : Outcome ⟨3, 12, 0, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 0, 2⟩) (by decide) node_3040

theorem node_3581 : Outcome ⟨3, 12, 0, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 0, 2⟩) (by decide) node_3040

theorem node_3582 : Outcome ⟨3, 12, 0, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 18⟩) (by decide) node_434

theorem node_3583 : Outcome ⟨4, 0, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 2⟩) (by decide) node_2991

theorem node_3584 : Outcome ⟨4, 0, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 2⟩) (by decide) node_2991

theorem node_3585 : Outcome ⟨4, 0, 11, 12⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 14⟩) (by decide) node_826

theorem node_3586 : Outcome ⟨4, 0, 11, 14⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 14⟩) (by decide) node_826

theorem node_3587 : Outcome ⟨4, 0, 11, 36⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 14⟩) (by decide) node_826

theorem node_3588 : Outcome ⟨4, 1, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 10, 2⟩, ⟨2, 1, 10, 4⟩, ⟨4, 0, 10, 2⟩, ⟨4, 1, 9, 2⟩, ⟨4, 1, 8, 4⟩]
  exact AllWinning.cons node_2996 (AllWinning.cons node_2484 (AllWinning.cons node_3045 (AllWinning.cons node_3049 (AllWinning.cons node_2584 (AllWinning.nil)))))

theorem node_3589 : Outcome ⟨4, 1, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 10, 2⟩, ⟨2, 1, 10, 4⟩, ⟨1, 1, 10, 6⟩, ⟨0, 1, 10, 8⟩, ⟨4, 0, 10, 2⟩, ⟨4, 1, 9, 2⟩, ⟨4, 1, 8, 4⟩, ⟨4, 1, 7, 6⟩, ⟨4, 1, 6, 8⟩]
  exact AllWinning.cons node_2996 (AllWinning.cons node_2484 (AllWinning.cons node_1934 (AllWinning.cons node_1546 (AllWinning.cons node_3045 (AllWinning.cons node_3049 (AllWinning.cons node_2584 (AllWinning.cons node_2127 (AllWinning.cons node_1721 (AllWinning.nil)))))))))

theorem node_3590 : Outcome ⟨4, 1, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 1, 10, 2⟩, ⟨2, 1, 10, 4⟩, ⟨1, 1, 10, 6⟩, ⟨0, 1, 10, 8⟩, ⟨4, 0, 10, 2⟩, ⟨4, 1, 9, 2⟩, ⟨4, 1, 8, 4⟩, ⟨4, 1, 7, 6⟩, ⟨4, 1, 6, 8⟩, ⟨4, 1, 5, 10⟩, ⟨4, 1, 4, 12⟩]
  exact AllWinning.cons node_2996 (AllWinning.cons node_2484 (AllWinning.cons node_1934 (AllWinning.cons node_1546 (AllWinning.cons node_3045 (AllWinning.cons node_3049 (AllWinning.cons node_2584 (AllWinning.cons node_2127 (AllWinning.cons node_1721 (AllWinning.cons node_1377 (AllWinning.cons node_1066 (AllWinning.nil)))))))))))

theorem node_3591 : Outcome ⟨4, 1, 10, 10⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3592 : Outcome ⟨4, 1, 10, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3593 : Outcome ⟨4, 2, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 9, 2⟩, ⟨2, 2, 9, 4⟩, ⟨4, 1, 9, 2⟩, ⟨4, 0, 9, 4⟩, ⟨4, 2, 8, 2⟩, ⟨4, 2, 7, 4⟩]
  exact AllWinning.cons node_3001 (AllWinning.cons node_2488 (AllWinning.cons node_3049 (AllWinning.cons node_2579 (AllWinning.cons node_3052 (AllWinning.cons node_2589 (AllWinning.nil))))))

theorem node_3594 : Outcome ⟨4, 2, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 9, 2⟩, ⟨2, 2, 9, 4⟩, ⟨1, 2, 9, 6⟩, ⟨0, 2, 9, 8⟩, ⟨4, 1, 9, 2⟩, ⟨4, 0, 9, 4⟩, ⟨4, 2, 8, 2⟩, ⟨4, 2, 7, 4⟩, ⟨4, 2, 6, 6⟩, ⟨4, 2, 5, 8⟩]
  exact AllWinning.cons node_3001 (AllWinning.cons node_2488 (AllWinning.cons node_1937 (AllWinning.cons node_1551 (AllWinning.cons node_3049 (AllWinning.cons node_2579 (AllWinning.cons node_3052 (AllWinning.cons node_2589 (AllWinning.cons node_2133 (AllWinning.cons node_1726 (AllWinning.nil))))))))))

theorem node_3595 : Outcome ⟨4, 2, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 2, 9, 2⟩, ⟨2, 2, 9, 4⟩, ⟨1, 2, 9, 6⟩, ⟨0, 2, 9, 8⟩, ⟨4, 1, 9, 2⟩, ⟨4, 0, 9, 4⟩, ⟨4, 2, 8, 2⟩, ⟨4, 2, 7, 4⟩, ⟨4, 2, 6, 6⟩, ⟨4, 2, 5, 8⟩, ⟨4, 2, 4, 10⟩, ⟨4, 2, 3, 12⟩]
  exact AllWinning.cons node_3001 (AllWinning.cons node_2488 (AllWinning.cons node_1937 (AllWinning.cons node_1551 (AllWinning.cons node_3049 (AllWinning.cons node_2579 (AllWinning.cons node_3052 (AllWinning.cons node_2589 (AllWinning.cons node_2133 (AllWinning.cons node_1726 (AllWinning.cons node_1383 (AllWinning.cons node_1070 (AllWinning.nil))))))))))))

theorem node_3596 : Outcome ⟨4, 2, 9, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3597 : Outcome ⟨4, 2, 9, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3598 : Outcome ⟨4, 2, 9, 28⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3599 : Outcome ⟨4, 3, 8, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3600 : Outcome ⟨4, 3, 8, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3601 : Outcome ⟨4, 3, 8, 28⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 2⟩) (by decide) node_3006

theorem node_3602 : Outcome ⟨4, 4, 7, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 5, 4⟩) (by decide) node_2600

theorem node_3603 : Outcome ⟨4, 4, 7, 12⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 14⟩) (by decide) node_852

theorem node_3604 : Outcome ⟨4, 5, 6, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 4, 4⟩) (by decide) node_2604

theorem node_3605 : Outcome ⟨4, 5, 6, 10⟩ true :=
  Outcome.win (q := ⟨4, 5, 4, 4⟩) (by decide) node_2604

theorem node_3606 : Outcome ⟨4, 6, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 5, 4⟩) (by decide) node_2600

theorem node_3607 : Outcome ⟨4, 6, 5, 10⟩ true :=
  Outcome.win (q := ⟨4, 4, 5, 4⟩) (by decide) node_2600

theorem node_3608 : Outcome ⟨4, 7, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 4, 4⟩) (by decide) node_2604

theorem node_3609 : Outcome ⟨4, 7, 4, 12⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 14⟩) (by decide) node_826

theorem node_3610 : Outcome ⟨4, 8, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3611 : Outcome ⟨4, 8, 3, 24⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3612 : Outcome ⟨4, 8, 3, 28⟩ true :=
  Outcome.win (q := ⟨3, 8, 3, 2⟩) (by decide) node_3025

theorem node_3613 : Outcome ⟨4, 9, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 2, 2⟩, ⟨2, 9, 2, 4⟩, ⟨4, 8, 2, 2⟩, ⟨4, 7, 2, 4⟩, ⟨4, 9, 1, 2⟩, ⟨4, 9, 0, 4⟩]
  exact AllWinning.cons node_3030 (AllWinning.cons node_2518 (AllWinning.cons node_3072 (AllWinning.cons node_2611 (AllWinning.cons node_3077 (AllWinning.cons node_2623 (AllWinning.nil))))))

theorem node_3614 : Outcome ⟨4, 9, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 2, 2⟩, ⟨2, 9, 2, 4⟩, ⟨1, 9, 2, 6⟩, ⟨0, 9, 2, 8⟩, ⟨4, 8, 2, 2⟩, ⟨4, 7, 2, 4⟩, ⟨4, 6, 2, 6⟩, ⟨4, 5, 2, 8⟩, ⟨4, 9, 1, 2⟩, ⟨4, 9, 0, 4⟩]
  exact AllWinning.cons node_3030 (AllWinning.cons node_2518 (AllWinning.cons node_1971 (AllWinning.cons node_1583 (AllWinning.cons node_3072 (AllWinning.cons node_2611 (AllWinning.cons node_2149 (AllWinning.cons node_1740 (AllWinning.cons node_3077 (AllWinning.cons node_2623 (AllWinning.nil))))))))))

theorem node_3615 : Outcome ⟨4, 9, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 2, 2⟩, ⟨2, 9, 2, 4⟩, ⟨1, 9, 2, 6⟩, ⟨0, 9, 2, 8⟩, ⟨4, 8, 2, 2⟩, ⟨4, 7, 2, 4⟩, ⟨4, 6, 2, 6⟩, ⟨4, 5, 2, 8⟩, ⟨4, 4, 2, 10⟩, ⟨4, 3, 2, 12⟩, ⟨4, 9, 1, 2⟩, ⟨4, 9, 0, 4⟩]
  exact AllWinning.cons node_3030 (AllWinning.cons node_2518 (AllWinning.cons node_1971 (AllWinning.cons node_1583 (AllWinning.cons node_3072 (AllWinning.cons node_2611 (AllWinning.cons node_2149 (AllWinning.cons node_1740 (AllWinning.cons node_1392 (AllWinning.cons node_1074 (AllWinning.cons node_3077 (AllWinning.cons node_2623 (AllWinning.nil))))))))))))

theorem node_3616 : Outcome ⟨4, 9, 2, 10⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3617 : Outcome ⟨4, 9, 2, 22⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3618 : Outcome ⟨4, 9, 2, 28⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3619 : Outcome ⟨4, 10, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 10, 1, 2⟩, ⟨2, 10, 1, 4⟩, ⟨4, 9, 1, 2⟩, ⟨4, 8, 1, 4⟩, ⟨4, 10, 0, 2⟩]
  exact AllWinning.cons node_3035 (AllWinning.cons node_2521 (AllWinning.cons node_3077 (AllWinning.cons node_2617 (AllWinning.cons node_3080 (AllWinning.nil)))))

theorem node_3620 : Outcome ⟨4, 10, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 10, 1, 2⟩, ⟨2, 10, 1, 4⟩, ⟨1, 10, 1, 6⟩, ⟨0, 10, 1, 8⟩, ⟨4, 9, 1, 2⟩, ⟨4, 8, 1, 4⟩, ⟨4, 7, 1, 6⟩, ⟨4, 6, 1, 8⟩, ⟨4, 10, 0, 2⟩]
  exact AllWinning.cons node_3035 (AllWinning.cons node_2521 (AllWinning.cons node_1975 (AllWinning.cons node_1589 (AllWinning.cons node_3077 (AllWinning.cons node_2617 (AllWinning.cons node_2154 (AllWinning.cons node_1745 (AllWinning.cons node_3080 (AllWinning.nil)))))))))

theorem node_3621 : Outcome ⟨4, 10, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 10, 1, 2⟩, ⟨2, 10, 1, 4⟩, ⟨1, 10, 1, 6⟩, ⟨0, 10, 1, 8⟩, ⟨4, 9, 1, 2⟩, ⟨4, 8, 1, 4⟩, ⟨4, 7, 1, 6⟩, ⟨4, 6, 1, 8⟩, ⟨4, 5, 1, 10⟩, ⟨4, 4, 1, 12⟩, ⟨4, 10, 0, 2⟩]
  exact AllWinning.cons node_3035 (AllWinning.cons node_2521 (AllWinning.cons node_1975 (AllWinning.cons node_1589 (AllWinning.cons node_3077 (AllWinning.cons node_2617 (AllWinning.cons node_2154 (AllWinning.cons node_1745 (AllWinning.cons node_1398 (AllWinning.cons node_1080 (AllWinning.cons node_3080 (AllWinning.nil)))))))))))

theorem node_3622 : Outcome ⟨4, 10, 1, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3623 : Outcome ⟨4, 10, 1, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3624 : Outcome ⟨4, 11, 0, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 0, 2⟩) (by decide) node_3040

theorem node_3625 : Outcome ⟨4, 11, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 0, 2⟩) (by decide) node_3040

theorem node_3626 : Outcome ⟨4, 11, 0, 12⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 14⟩) (by decide) node_852

theorem node_3627 : Outcome ⟨4, 11, 0, 14⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 14⟩) (by decide) node_852

theorem node_3628 : Outcome ⟨4, 11, 0, 36⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 14⟩) (by decide) node_852

theorem node_3629 : Outcome ⟨5, 0, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 10, 2⟩, ⟨3, 0, 10, 4⟩, ⟨5, 0, 9, 2⟩, ⟨5, 0, 8, 4⟩]
  exact AllWinning.cons node_3045 (AllWinning.cons node_2530 (AllWinning.cons node_3084 (AllWinning.cons node_2629 (AllWinning.nil))))

theorem node_3630 : Outcome ⟨5, 0, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 10, 6⟩) (by decide) node_1984

theorem node_3631 : Outcome ⟨5, 0, 10, 6⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 10⟩) (by decide) node_1408

theorem node_3632 : Outcome ⟨5, 0, 10, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 10⟩) (by decide) node_1408

theorem node_3633 : Outcome ⟨5, 0, 10, 16⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 10⟩) (by decide) node_1408

theorem node_3634 : Outcome ⟨5, 1, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 9, 2⟩, ⟨3, 1, 9, 4⟩, ⟨5, 0, 9, 2⟩, ⟨5, 1, 8, 2⟩, ⟨5, 1, 7, 4⟩]
  exact AllWinning.cons node_3049 (AllWinning.cons node_2535 (AllWinning.cons node_3084 (AllWinning.cons node_3087 (AllWinning.cons node_2634 (AllWinning.nil)))))

theorem node_3635 : Outcome ⟨5, 1, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 9, 2⟩, ⟨3, 1, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨1, 1, 9, 8⟩, ⟨5, 0, 9, 2⟩, ⟨5, 1, 8, 2⟩, ⟨5, 1, 7, 4⟩, ⟨5, 1, 6, 6⟩, ⟨5, 1, 5, 8⟩]
  exact AllWinning.cons node_3049 (AllWinning.cons node_2535 (AllWinning.cons node_1988 (AllWinning.cons node_1601 (AllWinning.cons node_3084 (AllWinning.cons node_3087 (AllWinning.cons node_2634 (AllWinning.cons node_2166 (AllWinning.cons node_1756 (AllWinning.nil)))))))))

theorem node_3636 : Outcome ⟨5, 1, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 9, 2⟩, ⟨3, 1, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨1, 1, 9, 8⟩, ⟨0, 1, 9, 10⟩, ⟨5, 0, 9, 2⟩, ⟨5, 1, 8, 2⟩, ⟨5, 1, 7, 4⟩, ⟨5, 1, 6, 6⟩, ⟨5, 1, 5, 8⟩, ⟨5, 1, 4, 10⟩, ⟨5, 1, 3, 12⟩]
  exact AllWinning.cons node_3049 (AllWinning.cons node_2535 (AllWinning.cons node_1988 (AllWinning.cons node_1601 (AllWinning.cons node_1158 (AllWinning.cons node_3084 (AllWinning.cons node_3087 (AllWinning.cons node_2634 (AllWinning.cons node_2166 (AllWinning.cons node_1756 (AllWinning.cons node_1421 (AllWinning.cons node_1090 (AllWinning.nil))))))))))))

theorem node_3637 : Outcome ⟨5, 1, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 9, 2⟩, ⟨3, 1, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨1, 1, 9, 8⟩, ⟨0, 1, 9, 10⟩, ⟨5, 0, 9, 2⟩, ⟨5, 1, 8, 2⟩, ⟨5, 1, 7, 4⟩, ⟨5, 1, 6, 6⟩, ⟨5, 1, 5, 8⟩, ⟨5, 1, 4, 10⟩, ⟨5, 1, 3, 12⟩, ⟨5, 1, 2, 14⟩, ⟨5, 1, 1, 16⟩]
  exact AllWinning.cons node_3049 (AllWinning.cons node_2535 (AllWinning.cons node_1988 (AllWinning.cons node_1601 (AllWinning.cons node_1158 (AllWinning.cons node_3084 (AllWinning.cons node_3087 (AllWinning.cons node_2634 (AllWinning.cons node_2166 (AllWinning.cons node_1756 (AllWinning.cons node_1421 (AllWinning.cons node_1090 (AllWinning.cons node_868 (AllWinning.cons node_661 (AllWinning.nil))))))))))))))

theorem node_3638 : Outcome ⟨5, 1, 9, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 9, 2⟩, ⟨3, 1, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨1, 1, 9, 8⟩, ⟨0, 1, 9, 10⟩, ⟨5, 0, 9, 2⟩, ⟨5, 1, 8, 2⟩, ⟨5, 1, 7, 4⟩, ⟨5, 1, 6, 6⟩, ⟨5, 1, 5, 8⟩, ⟨5, 1, 4, 10⟩, ⟨5, 1, 3, 12⟩, ⟨5, 1, 2, 14⟩, ⟨5, 1, 1, 16⟩, ⟨5, 1, 0, 18⟩]
  exact AllWinning.cons node_3049 (AllWinning.cons node_2535 (AllWinning.cons node_1988 (AllWinning.cons node_1601 (AllWinning.cons node_1158 (AllWinning.cons node_3084 (AllWinning.cons node_3087 (AllWinning.cons node_2634 (AllWinning.cons node_2166 (AllWinning.cons node_1756 (AllWinning.cons node_1421 (AllWinning.cons node_1090 (AllWinning.cons node_868 (AllWinning.cons node_661 (AllWinning.cons node_461 (AllWinning.nil)))))))))))))))

theorem node_3639 : Outcome ⟨5, 1, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 9, 2⟩, ⟨3, 1, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨1, 1, 9, 8⟩, ⟨0, 1, 9, 10⟩, ⟨5, 0, 9, 2⟩, ⟨5, 1, 8, 2⟩, ⟨5, 1, 7, 4⟩, ⟨5, 1, 6, 6⟩, ⟨5, 1, 5, 8⟩, ⟨5, 1, 4, 10⟩, ⟨5, 1, 3, 12⟩, ⟨5, 1, 2, 14⟩, ⟨5, 1, 1, 16⟩, ⟨5, 1, 0, 18⟩]
  exact AllWinning.cons node_3049 (AllWinning.cons node_2535 (AllWinning.cons node_1988 (AllWinning.cons node_1601 (AllWinning.cons node_1158 (AllWinning.cons node_3084 (AllWinning.cons node_3087 (AllWinning.cons node_2634 (AllWinning.cons node_2166 (AllWinning.cons node_1756 (AllWinning.cons node_1421 (AllWinning.cons node_1090 (AllWinning.cons node_868 (AllWinning.cons node_661 (AllWinning.cons node_461 (AllWinning.nil)))))))))))))))

theorem node_3640 : Outcome ⟨5, 1, 9, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 1, 9, 2⟩, ⟨3, 1, 9, 4⟩, ⟨2, 1, 9, 6⟩, ⟨1, 1, 9, 8⟩, ⟨0, 1, 9, 10⟩, ⟨5, 0, 9, 2⟩, ⟨5, 1, 8, 2⟩, ⟨5, 1, 7, 4⟩, ⟨5, 1, 6, 6⟩, ⟨5, 1, 5, 8⟩, ⟨5, 1, 4, 10⟩, ⟨5, 1, 3, 12⟩, ⟨5, 1, 2, 14⟩, ⟨5, 1, 1, 16⟩, ⟨5, 1, 0, 18⟩]
  exact AllWinning.cons node_3049 (AllWinning.cons node_2535 (AllWinning.cons node_1988 (AllWinning.cons node_1601 (AllWinning.cons node_1158 (AllWinning.cons node_3084 (AllWinning.cons node_3087 (AllWinning.cons node_2634 (AllWinning.cons node_2166 (AllWinning.cons node_1756 (AllWinning.cons node_1421 (AllWinning.cons node_1090 (AllWinning.cons node_868 (AllWinning.cons node_661 (AllWinning.cons node_461 (AllWinning.nil)))))))))))))))

end RQ9F1
