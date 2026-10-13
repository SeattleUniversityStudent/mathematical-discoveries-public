import Chunk100
set_option autoImplicit false
namespace RQ9F1

theorem node_21174 : Outcome ⟨19, 5, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 5, 10, 2⟩, ⟨17, 5, 10, 4⟩, ⟨16, 5, 10, 6⟩, ⟨15, 5, 10, 8⟩, ⟨14, 5, 10, 10⟩, ⟨13, 5, 10, 12⟩, ⟨12, 5, 10, 14⟩, ⟨11, 5, 10, 16⟩, ⟨10, 5, 10, 18⟩, ⟨9, 5, 10, 20⟩, ⟨8, 5, 10, 22⟩, ⟨7, 5, 10, 24⟩, ⟨19, 4, 10, 2⟩, ⟨19, 3, 10, 4⟩, ⟨19, 2, 10, 6⟩, ⟨19, 1, 10, 8⟩, ⟨19, 0, 10, 10⟩, ⟨19, 5, 9, 2⟩, ⟨19, 5, 8, 4⟩, ⟨19, 5, 7, 6⟩, ⟨19, 5, 6, 8⟩, ⟨19, 5, 5, 10⟩, ⟨19, 5, 4, 12⟩, ⟨19, 5, 3, 14⟩, ⟨19, 5, 2, 16⟩, ⟨19, 5, 1, 18⟩, ⟨19, 5, 0, 20⟩]
  exact AllWinning.cons node_20358 (AllWinning.cons node_19598 (AllWinning.cons node_18666 (AllWinning.cons node_17710 (AllWinning.cons node_16745 (AllWinning.cons node_15631 (AllWinning.cons node_14641 (AllWinning.cons node_13619 (AllWinning.cons node_12613 (AllWinning.cons node_11576 (AllWinning.cons node_10512 (AllWinning.cons node_9428 (AllWinning.cons node_20387 (AllWinning.cons node_19665 (AllWinning.cons node_18780 (AllWinning.cons node_17859 (AllWinning.cons node_16938 (AllWinning.cons node_20389 (AllWinning.cons node_19668 (AllWinning.cons node_18786 (AllWinning.cons node_17866 (AllWinning.cons node_16953 (AllWinning.cons node_15890 (AllWinning.cons node_14911 (AllWinning.cons node_13938 (AllWinning.cons node_12971 (AllWinning.cons node_11957 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_21175 : Outcome ⟨19, 7, 8, 12⟩ true :=
  Outcome.win (q := ⟨19, 2, 8, 10⟩) (by decide) node_16944

theorem node_21176 : Outcome ⟨19, 8, 7, 12⟩ true :=
  Outcome.win (q := ⟨19, 8, 2, 10⟩) (by decide) node_16960

theorem node_21177 : Outcome ⟨19, 10, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 5, 2⟩, ⟨17, 10, 5, 4⟩, ⟨16, 10, 5, 6⟩, ⟨15, 10, 5, 8⟩, ⟨19, 9, 5, 2⟩, ⟨19, 8, 5, 4⟩, ⟨19, 7, 5, 6⟩, ⟨19, 6, 5, 8⟩, ⟨19, 10, 4, 2⟩, ⟨19, 10, 3, 4⟩, ⟨19, 10, 2, 6⟩, ⟨19, 10, 1, 8⟩]
  exact AllWinning.cons node_20366 (AllWinning.cons node_19618 (AllWinning.cons node_18680 (AllWinning.cons node_17726 (AllWinning.cons node_20392 (AllWinning.cons node_19674 (AllWinning.cons node_18789 (AllWinning.cons node_17868 (AllWinning.cons node_20393 (AllWinning.cons node_19679 (AllWinning.cons node_18794 (AllWinning.cons node_17875 (AllWinning.nil))))))))))))

theorem node_21178 : Outcome ⟨19, 10, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 5, 2⟩, ⟨17, 10, 5, 4⟩, ⟨16, 10, 5, 6⟩, ⟨15, 10, 5, 8⟩, ⟨14, 10, 5, 10⟩, ⟨13, 10, 5, 12⟩, ⟨19, 9, 5, 2⟩, ⟨19, 8, 5, 4⟩, ⟨19, 7, 5, 6⟩, ⟨19, 6, 5, 8⟩, ⟨19, 5, 5, 10⟩, ⟨19, 4, 5, 12⟩, ⟨19, 10, 4, 2⟩, ⟨19, 10, 3, 4⟩, ⟨19, 10, 2, 6⟩, ⟨19, 10, 1, 8⟩, ⟨19, 10, 0, 10⟩]
  exact AllWinning.cons node_20366 (AllWinning.cons node_19618 (AllWinning.cons node_18680 (AllWinning.cons node_17726 (AllWinning.cons node_16762 (AllWinning.cons node_15646 (AllWinning.cons node_20392 (AllWinning.cons node_19674 (AllWinning.cons node_18789 (AllWinning.cons node_17868 (AllWinning.cons node_16953 (AllWinning.cons node_15887 (AllWinning.cons node_20393 (AllWinning.cons node_19679 (AllWinning.cons node_18794 (AllWinning.cons node_17875 (AllWinning.cons node_16968 (AllWinning.nil)))))))))))))))))

theorem node_21179 : Outcome ⟨19, 10, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 5, 2⟩, ⟨17, 10, 5, 4⟩, ⟨16, 10, 5, 6⟩, ⟨15, 10, 5, 8⟩, ⟨14, 10, 5, 10⟩, ⟨13, 10, 5, 12⟩, ⟨12, 10, 5, 14⟩, ⟨11, 10, 5, 16⟩, ⟨19, 9, 5, 2⟩, ⟨19, 8, 5, 4⟩, ⟨19, 7, 5, 6⟩, ⟨19, 6, 5, 8⟩, ⟨19, 5, 5, 10⟩, ⟨19, 4, 5, 12⟩, ⟨19, 3, 5, 14⟩, ⟨19, 2, 5, 16⟩, ⟨19, 10, 4, 2⟩, ⟨19, 10, 3, 4⟩, ⟨19, 10, 2, 6⟩, ⟨19, 10, 1, 8⟩, ⟨19, 10, 0, 10⟩]
  exact AllWinning.cons node_20366 (AllWinning.cons node_19618 (AllWinning.cons node_18680 (AllWinning.cons node_17726 (AllWinning.cons node_16762 (AllWinning.cons node_15646 (AllWinning.cons node_14658 (AllWinning.cons node_13636 (AllWinning.cons node_20392 (AllWinning.cons node_19674 (AllWinning.cons node_18789 (AllWinning.cons node_17868 (AllWinning.cons node_16953 (AllWinning.cons node_15887 (AllWinning.cons node_14908 (AllWinning.cons node_13934 (AllWinning.cons node_20393 (AllWinning.cons node_19679 (AllWinning.cons node_18794 (AllWinning.cons node_17875 (AllWinning.cons node_16968 (AllWinning.nil)))))))))))))))))))))

theorem node_21180 : Outcome ⟨19, 10, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 5, 2⟩, ⟨17, 10, 5, 4⟩, ⟨16, 10, 5, 6⟩, ⟨15, 10, 5, 8⟩, ⟨14, 10, 5, 10⟩, ⟨13, 10, 5, 12⟩, ⟨12, 10, 5, 14⟩, ⟨11, 10, 5, 16⟩, ⟨10, 10, 5, 18⟩, ⟨9, 10, 5, 20⟩, ⟨19, 9, 5, 2⟩, ⟨19, 8, 5, 4⟩, ⟨19, 7, 5, 6⟩, ⟨19, 6, 5, 8⟩, ⟨19, 5, 5, 10⟩, ⟨19, 4, 5, 12⟩, ⟨19, 3, 5, 14⟩, ⟨19, 2, 5, 16⟩, ⟨19, 1, 5, 18⟩, ⟨19, 0, 5, 20⟩, ⟨19, 10, 4, 2⟩, ⟨19, 10, 3, 4⟩, ⟨19, 10, 2, 6⟩, ⟨19, 10, 1, 8⟩, ⟨19, 10, 0, 10⟩]
  exact AllWinning.cons node_20366 (AllWinning.cons node_19618 (AllWinning.cons node_18680 (AllWinning.cons node_17726 (AllWinning.cons node_16762 (AllWinning.cons node_15646 (AllWinning.cons node_14658 (AllWinning.cons node_13636 (AllWinning.cons node_12630 (AllWinning.cons node_11590 (AllWinning.cons node_20392 (AllWinning.cons node_19674 (AllWinning.cons node_18789 (AllWinning.cons node_17868 (AllWinning.cons node_16953 (AllWinning.cons node_15887 (AllWinning.cons node_14908 (AllWinning.cons node_13934 (AllWinning.cons node_12962 (AllWinning.cons node_11946 (AllWinning.cons node_20393 (AllWinning.cons node_19679 (AllWinning.cons node_18794 (AllWinning.cons node_17875 (AllWinning.cons node_16968 (AllWinning.nil)))))))))))))))))))))))))

theorem node_21181 : Outcome ⟨19, 10, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 10, 5, 2⟩, ⟨17, 10, 5, 4⟩, ⟨16, 10, 5, 6⟩, ⟨15, 10, 5, 8⟩, ⟨14, 10, 5, 10⟩, ⟨13, 10, 5, 12⟩, ⟨12, 10, 5, 14⟩, ⟨11, 10, 5, 16⟩, ⟨10, 10, 5, 18⟩, ⟨9, 10, 5, 20⟩, ⟨8, 10, 5, 22⟩, ⟨7, 10, 5, 24⟩, ⟨19, 9, 5, 2⟩, ⟨19, 8, 5, 4⟩, ⟨19, 7, 5, 6⟩, ⟨19, 6, 5, 8⟩, ⟨19, 5, 5, 10⟩, ⟨19, 4, 5, 12⟩, ⟨19, 3, 5, 14⟩, ⟨19, 2, 5, 16⟩, ⟨19, 1, 5, 18⟩, ⟨19, 0, 5, 20⟩, ⟨19, 10, 4, 2⟩, ⟨19, 10, 3, 4⟩, ⟨19, 10, 2, 6⟩, ⟨19, 10, 1, 8⟩, ⟨19, 10, 0, 10⟩]
  exact AllWinning.cons node_20366 (AllWinning.cons node_19618 (AllWinning.cons node_18680 (AllWinning.cons node_17726 (AllWinning.cons node_16762 (AllWinning.cons node_15646 (AllWinning.cons node_14658 (AllWinning.cons node_13636 (AllWinning.cons node_12630 (AllWinning.cons node_11590 (AllWinning.cons node_10534 (AllWinning.cons node_9446 (AllWinning.cons node_20392 (AllWinning.cons node_19674 (AllWinning.cons node_18789 (AllWinning.cons node_17868 (AllWinning.cons node_16953 (AllWinning.cons node_15887 (AllWinning.cons node_14908 (AllWinning.cons node_13934 (AllWinning.cons node_12962 (AllWinning.cons node_11946 (AllWinning.cons node_20393 (AllWinning.cons node_19679 (AllWinning.cons node_18794 (AllWinning.cons node_17875 (AllWinning.cons node_16968 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_21182 : Outcome ⟨19, 11, 4, 6⟩ true :=
  Outcome.win (q := ⟨18, 11, 4, 2⟩) (by decide) node_20368

theorem node_21183 : Outcome ⟨19, 13, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 2, 2⟩, ⟨17, 13, 2, 4⟩, ⟨16, 13, 2, 6⟩, ⟨15, 13, 2, 8⟩, ⟨19, 12, 2, 2⟩, ⟨19, 11, 2, 4⟩, ⟨19, 10, 2, 6⟩, ⟨19, 9, 2, 8⟩, ⟨19, 13, 1, 2⟩, ⟨19, 13, 0, 4⟩]
  exact AllWinning.cons node_20372 (AllWinning.cons node_19624 (AllWinning.cons node_18689 (AllWinning.cons node_17737 (AllWinning.cons node_20396 (AllWinning.cons node_19681 (AllWinning.cons node_18794 (AllWinning.cons node_17873 (AllWinning.cons node_20398 (AllWinning.cons node_19686 (AllWinning.nil))))))))))

theorem node_21184 : Outcome ⟨19, 13, 2, 8⟩ true :=
  Outcome.win (q := ⟨19, 8, 2, 10⟩) (by decide) node_16960

theorem node_21185 : Outcome ⟨19, 13, 2, 12⟩ true :=
  Outcome.win (q := ⟨19, 8, 2, 10⟩) (by decide) node_16960

theorem node_21186 : Outcome ⟨19, 14, 1, 6⟩ true :=
  Outcome.win (q := ⟨19, 12, 1, 4⟩) (by decide) node_19683

theorem node_21187 : Outcome ⟨19, 15, 0, 8⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 8⟩) (by decide) node_17744

theorem node_21188 : Outcome ⟨0, 15, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 20, 2⟩, ⟨0, 13, 20, 4⟩, ⟨0, 15, 19, 2⟩, ⟨0, 15, 18, 4⟩]
  exact AllWinning.cons node_20403 (AllWinning.cons node_19690 (AllWinning.cons node_20406 (AllWinning.cons node_19697 (AllWinning.nil))))

theorem node_21189 : Outcome ⟨0, 15, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 20, 2⟩, ⟨0, 13, 20, 4⟩, ⟨0, 12, 20, 6⟩, ⟨0, 11, 20, 8⟩, ⟨0, 15, 19, 2⟩, ⟨0, 15, 18, 4⟩, ⟨0, 15, 17, 6⟩, ⟨0, 15, 16, 8⟩]
  exact AllWinning.cons node_20403 (AllWinning.cons node_19690 (AllWinning.cons node_18801 (AllWinning.cons node_17880 (AllWinning.cons node_20406 (AllWinning.cons node_19697 (AllWinning.cons node_18810 (AllWinning.cons node_17892 (AllWinning.nil))))))))

theorem node_21190 : Outcome ⟨0, 15, 20, 10⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 10⟩) (by decide) node_16992

theorem node_21191 : Outcome ⟨0, 15, 20, 12⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 10⟩) (by decide) node_16992

theorem node_21192 : Outcome ⟨0, 16, 19, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 6⟩) (by decide) node_18814

theorem node_21193 : Outcome ⟨0, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 17, 2⟩) (by decide) node_20409

theorem node_21194 : Outcome ⟨0, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 17, 2⟩) (by decide) node_20409

theorem node_21195 : Outcome ⟨0, 19, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 6⟩) (by decide) node_18814

theorem node_21196 : Outcome ⟨0, 20, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 15, 2⟩, ⟨0, 18, 15, 4⟩, ⟨0, 20, 14, 2⟩, ⟨0, 20, 13, 4⟩]
  exact AllWinning.cons node_20415 (AllWinning.cons node_19701 (AllWinning.cons node_20417 (AllWinning.cons node_19708 (AllWinning.nil))))

theorem node_21197 : Outcome ⟨0, 20, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 15, 2⟩, ⟨0, 18, 15, 4⟩, ⟨0, 17, 15, 6⟩, ⟨0, 16, 15, 8⟩, ⟨0, 20, 14, 2⟩, ⟨0, 20, 13, 4⟩, ⟨0, 20, 12, 6⟩, ⟨0, 20, 11, 8⟩]
  exact AllWinning.cons node_20415 (AllWinning.cons node_19701 (AllWinning.cons node_18821 (AllWinning.cons node_17894 (AllWinning.cons node_20417 (AllWinning.cons node_19708 (AllWinning.cons node_18830 (AllWinning.cons node_17905 (AllWinning.nil))))))))

theorem node_21198 : Outcome ⟨0, 20, 15, 10⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 10⟩) (by decide) node_16992

theorem node_21199 : Outcome ⟨0, 20, 15, 12⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 10⟩) (by decide) node_16992

theorem node_21200 : Outcome ⟨1, 14, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 18, 4⟩) (by decide) node_19719

theorem node_21201 : Outcome ⟨1, 14, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 18, 4⟩) (by decide) node_19719

theorem node_21202 : Outcome ⟨1, 15, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 19, 2⟩, ⟨1, 14, 19, 2⟩, ⟨1, 13, 19, 4⟩, ⟨1, 15, 18, 2⟩, ⟨1, 15, 17, 4⟩]
  exact AllWinning.cons node_20406 (AllWinning.cons node_20422 (AllWinning.cons node_19715 (AllWinning.cons node_20425 (AllWinning.cons node_19723 (AllWinning.nil)))))

theorem node_21203 : Outcome ⟨1, 15, 19, 6⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 6⟩) (by decide) node_18835

theorem node_21204 : Outcome ⟨1, 15, 19, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 6⟩) (by decide) node_18835

theorem node_21205 : Outcome ⟨1, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 18, 4⟩) (by decide) node_19719

theorem node_21206 : Outcome ⟨1, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 6⟩) (by decide) node_18853

theorem node_21207 : Outcome ⟨1, 16, 18, 6⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 6⟩) (by decide) node_18853

theorem node_21208 : Outcome ⟨1, 17, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 17, 2⟩) (by decide) node_20409

theorem node_21209 : Outcome ⟨1, 17, 17, 8⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 8⟩) (by decide) node_17920

theorem node_21210 : Outcome ⟨1, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 14, 4⟩) (by decide) node_19730

theorem node_21211 : Outcome ⟨1, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 6⟩) (by decide) node_18846

theorem node_21212 : Outcome ⟨1, 18, 16, 6⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 6⟩) (by decide) node_18846

theorem node_21213 : Outcome ⟨1, 19, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 15, 2⟩, ⟨1, 18, 15, 2⟩, ⟨1, 17, 15, 4⟩, ⟨1, 19, 14, 2⟩, ⟨1, 19, 13, 4⟩]
  exact AllWinning.cons node_20415 (AllWinning.cons node_20434 (AllWinning.cons node_19727 (AllWinning.cons node_20437 (AllWinning.cons node_19734 (AllWinning.nil)))))

theorem node_21214 : Outcome ⟨1, 19, 15, 6⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 6⟩) (by decide) node_18853

theorem node_21215 : Outcome ⟨1, 19, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 6⟩) (by decide) node_18853

theorem node_21216 : Outcome ⟨1, 20, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 14, 4⟩) (by decide) node_19730

theorem node_21217 : Outcome ⟨1, 20, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 18, 14, 4⟩) (by decide) node_19730

theorem node_21218 : Outcome ⟨2, 13, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 20, 2⟩) (by decide) node_20420

theorem node_21219 : Outcome ⟨2, 13, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 20, 2⟩) (by decide) node_20420

theorem node_21220 : Outcome ⟨2, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 19, 4⟩) (by decide) node_19694

theorem node_21221 : Outcome ⟨2, 14, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 19, 4⟩) (by decide) node_19694

theorem node_21222 : Outcome ⟨2, 14, 19, 6⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 12⟩) (by decide) node_15989

theorem node_21223 : Outcome ⟨2, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 17, 2⟩) (by decide) node_20448

theorem node_21224 : Outcome ⟨2, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 17, 2⟩) (by decide) node_20448

theorem node_21225 : Outcome ⟨2, 16, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 10⟩) (by decide) node_17057

theorem node_21226 : Outcome ⟨2, 16, 17, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 10⟩) (by decide) node_17057

theorem node_21227 : Outcome ⟨2, 16, 17, 14⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 10⟩) (by decide) node_17057

theorem node_21228 : Outcome ⟨2, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 15, 2⟩) (by decide) node_20454

theorem node_21229 : Outcome ⟨2, 17, 16, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 10⟩) (by decide) node_17079

theorem node_21230 : Outcome ⟨2, 17, 16, 8⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 10⟩) (by decide) node_17079

theorem node_21231 : Outcome ⟨2, 17, 16, 14⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 10⟩) (by decide) node_17079

theorem node_21232 : Outcome ⟨2, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 15, 2⟩) (by decide) node_20454

theorem node_21233 : Outcome ⟨2, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 14, 4⟩) (by decide) node_19704

theorem node_21234 : Outcome ⟨2, 19, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 19, 14, 4⟩) (by decide) node_19704

theorem node_21235 : Outcome ⟨2, 19, 14, 6⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 12⟩) (by decide) node_16018

theorem node_21236 : Outcome ⟨2, 20, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 20, 13, 2⟩) (by decide) node_20440

theorem node_21237 : Outcome ⟨2, 20, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 20, 13, 2⟩) (by decide) node_20440

theorem node_21238 : Outcome ⟨3, 12, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 20, 2⟩, ⟨1, 12, 20, 4⟩, ⟨3, 11, 20, 2⟩, ⟨3, 10, 20, 4⟩, ⟨3, 12, 19, 2⟩, ⟨3, 12, 18, 4⟩]
  exact AllWinning.cons node_20442 (AllWinning.cons node_19712 (AllWinning.cons node_20463 (AllWinning.cons node_19765 (AllWinning.cons node_20465 (AllWinning.cons node_19770 (AllWinning.nil))))))

theorem node_21239 : Outcome ⟨3, 12, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 20, 2⟩, ⟨1, 12, 20, 4⟩, ⟨0, 12, 20, 6⟩, ⟨3, 11, 20, 2⟩, ⟨3, 10, 20, 4⟩, ⟨3, 9, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨3, 12, 19, 2⟩, ⟨3, 12, 18, 4⟩, ⟨3, 12, 17, 6⟩, ⟨3, 12, 16, 8⟩]
  exact AllWinning.cons node_20442 (AllWinning.cons node_19712 (AllWinning.cons node_18801 (AllWinning.cons node_20463 (AllWinning.cons node_19765 (AllWinning.cons node_18901 (AllWinning.cons node_17974 (AllWinning.cons node_20465 (AllWinning.cons node_19770 (AllWinning.cons node_18908 (AllWinning.cons node_17986 (AllWinning.nil)))))))))))

theorem node_21240 : Outcome ⟨3, 12, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 20, 2⟩, ⟨1, 12, 20, 4⟩, ⟨0, 12, 20, 6⟩, ⟨3, 11, 20, 2⟩, ⟨3, 10, 20, 4⟩, ⟨3, 9, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨3, 7, 20, 10⟩, ⟨3, 6, 20, 12⟩, ⟨3, 12, 19, 2⟩, ⟨3, 12, 18, 4⟩, ⟨3, 12, 17, 6⟩, ⟨3, 12, 16, 8⟩, ⟨3, 12, 15, 10⟩, ⟨3, 12, 14, 12⟩]
  exact AllWinning.cons node_20442 (AllWinning.cons node_19712 (AllWinning.cons node_18801 (AllWinning.cons node_20463 (AllWinning.cons node_19765 (AllWinning.cons node_18901 (AllWinning.cons node_17974 (AllWinning.cons node_17090 (AllWinning.cons node_16023 (AllWinning.cons node_20465 (AllWinning.cons node_19770 (AllWinning.cons node_18908 (AllWinning.cons node_17986 (AllWinning.cons node_17102 (AllWinning.cons node_16043 (AllWinning.nil)))))))))))))))

theorem node_21241 : Outcome ⟨3, 12, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 20, 2⟩, ⟨1, 12, 20, 4⟩, ⟨0, 12, 20, 6⟩, ⟨3, 11, 20, 2⟩, ⟨3, 10, 20, 4⟩, ⟨3, 9, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨3, 7, 20, 10⟩, ⟨3, 6, 20, 12⟩, ⟨3, 5, 20, 14⟩, ⟨3, 4, 20, 16⟩, ⟨3, 12, 19, 2⟩, ⟨3, 12, 18, 4⟩, ⟨3, 12, 17, 6⟩, ⟨3, 12, 16, 8⟩, ⟨3, 12, 15, 10⟩, ⟨3, 12, 14, 12⟩, ⟨3, 12, 13, 14⟩, ⟨3, 12, 12, 16⟩]
  exact AllWinning.cons node_20442 (AllWinning.cons node_19712 (AllWinning.cons node_18801 (AllWinning.cons node_20463 (AllWinning.cons node_19765 (AllWinning.cons node_18901 (AllWinning.cons node_17974 (AllWinning.cons node_17090 (AllWinning.cons node_16023 (AllWinning.cons node_15066 (AllWinning.cons node_14099 (AllWinning.cons node_20465 (AllWinning.cons node_19770 (AllWinning.cons node_18908 (AllWinning.cons node_17986 (AllWinning.cons node_17102 (AllWinning.cons node_16043 (AllWinning.cons node_15088 (AllWinning.cons node_14131 (AllWinning.nil)))))))))))))))))))

theorem node_21242 : Outcome ⟨3, 13, 19, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 4⟩) (by decide) node_19767

theorem node_21243 : Outcome ⟨3, 13, 19, 10⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 18⟩) (by decide) node_13176

theorem node_21244 : Outcome ⟨3, 14, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 18, 4⟩) (by decide) node_19719

theorem node_21245 : Outcome ⟨3, 15, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 17, 2⟩) (by decide) node_20448

theorem node_21246 : Outcome ⟨3, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 6⟩) (by decide) node_18814

theorem node_21247 : Outcome ⟨3, 16, 16, 10⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 16⟩) (by decide) node_14115

theorem node_21248 : Outcome ⟨3, 17, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 15, 2⟩) (by decide) node_20454

theorem node_21249 : Outcome ⟨3, 18, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 14, 4⟩) (by decide) node_19730

theorem node_21250 : Outcome ⟨3, 19, 13, 4⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 4⟩) (by decide) node_19785

theorem node_21251 : Outcome ⟨3, 19, 13, 10⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 18⟩) (by decide) node_13158

theorem node_21252 : Outcome ⟨3, 20, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 20, 12, 2⟩, ⟨1, 20, 12, 4⟩, ⟨3, 19, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨3, 20, 11, 2⟩, ⟨3, 20, 10, 4⟩]
  exact AllWinning.cons node_20461 (AllWinning.cons node_19738 (AllWinning.cons node_20483 (AllWinning.cons node_19782 (AllWinning.cons node_20485 (AllWinning.cons node_19789 (AllWinning.nil))))))

theorem node_21253 : Outcome ⟨3, 20, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 20, 12, 2⟩, ⟨1, 20, 12, 4⟩, ⟨0, 20, 12, 6⟩, ⟨3, 19, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨3, 17, 12, 6⟩, ⟨3, 16, 12, 8⟩, ⟨3, 20, 11, 2⟩, ⟨3, 20, 10, 4⟩, ⟨3, 20, 9, 6⟩, ⟨3, 20, 8, 8⟩]
  exact AllWinning.cons node_20461 (AllWinning.cons node_19738 (AllWinning.cons node_18830 (AllWinning.cons node_20483 (AllWinning.cons node_19782 (AllWinning.cons node_18922 (AllWinning.cons node_18002 (AllWinning.cons node_20485 (AllWinning.cons node_19789 (AllWinning.cons node_18928 (AllWinning.cons node_18012 (AllWinning.nil)))))))))))

theorem node_21254 : Outcome ⟨3, 20, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 20, 12, 2⟩, ⟨1, 20, 12, 4⟩, ⟨0, 20, 12, 6⟩, ⟨3, 19, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨3, 17, 12, 6⟩, ⟨3, 16, 12, 8⟩, ⟨3, 15, 12, 10⟩, ⟨3, 14, 12, 12⟩, ⟨3, 20, 11, 2⟩, ⟨3, 20, 10, 4⟩, ⟨3, 20, 9, 6⟩, ⟨3, 20, 8, 8⟩, ⟨3, 20, 7, 10⟩, ⟨3, 20, 6, 12⟩]
  exact AllWinning.cons node_20461 (AllWinning.cons node_19738 (AllWinning.cons node_18830 (AllWinning.cons node_20483 (AllWinning.cons node_19782 (AllWinning.cons node_18922 (AllWinning.cons node_18002 (AllWinning.cons node_17114 (AllWinning.cons node_16052 (AllWinning.cons node_20485 (AllWinning.cons node_19789 (AllWinning.cons node_18928 (AllWinning.cons node_18012 (AllWinning.cons node_17126 (AllWinning.cons node_16070 (AllWinning.nil)))))))))))))))

theorem node_21255 : Outcome ⟨3, 20, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 20, 12, 2⟩, ⟨1, 20, 12, 4⟩, ⟨0, 20, 12, 6⟩, ⟨3, 19, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨3, 17, 12, 6⟩, ⟨3, 16, 12, 8⟩, ⟨3, 15, 12, 10⟩, ⟨3, 14, 12, 12⟩, ⟨3, 13, 12, 14⟩, ⟨3, 12, 12, 16⟩, ⟨3, 20, 11, 2⟩, ⟨3, 20, 10, 4⟩, ⟨3, 20, 9, 6⟩, ⟨3, 20, 8, 8⟩, ⟨3, 20, 7, 10⟩, ⟨3, 20, 6, 12⟩, ⟨3, 20, 5, 14⟩, ⟨3, 20, 4, 16⟩]
  exact AllWinning.cons node_20461 (AllWinning.cons node_19738 (AllWinning.cons node_18830 (AllWinning.cons node_20483 (AllWinning.cons node_19782 (AllWinning.cons node_18922 (AllWinning.cons node_18002 (AllWinning.cons node_17114 (AllWinning.cons node_16052 (AllWinning.cons node_15092 (AllWinning.cons node_14131 (AllWinning.cons node_20485 (AllWinning.cons node_19789 (AllWinning.cons node_18928 (AllWinning.cons node_18012 (AllWinning.cons node_17126 (AllWinning.cons node_16070 (AllWinning.cons node_15112 (AllWinning.cons node_14162 (AllWinning.nil)))))))))))))))))))

theorem node_21256 : Outcome ⟨4, 11, 20, 4⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 4⟩) (by decide) node_19796

theorem node_21257 : Outcome ⟨4, 11, 20, 14⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 12⟩) (by decide) node_16076

theorem node_21258 : Outcome ⟨4, 12, 19, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 6⟩) (by decide) node_18835

theorem node_21259 : Outcome ⟨4, 12, 19, 16⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 12⟩) (by decide) node_16106

theorem node_21260 : Outcome ⟨4, 13, 18, 4⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 4⟩) (by decide) node_19796

theorem node_21261 : Outcome ⟨4, 13, 18, 6⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 12⟩) (by decide) node_16116

theorem node_21262 : Outcome ⟨4, 14, 17, 2⟩ true :=
  Outcome.win (q := ⟨3, 14, 17, 2⟩) (by decide) node_20469

theorem node_21263 : Outcome ⟨4, 14, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 14, 17, 2⟩) (by decide) node_20469

theorem node_21264 : Outcome ⟨4, 15, 16, 2⟩ true :=
  Outcome.win (q := ⟨4, 14, 16, 2⟩) (by decide) node_20495

theorem node_21265 : Outcome ⟨4, 15, 16, 16⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 12⟩) (by decide) node_16093

theorem node_21266 : Outcome ⟨4, 16, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 16, 14, 2⟩) (by decide) node_20502

theorem node_21267 : Outcome ⟨4, 16, 15, 16⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 12⟩) (by decide) node_16129

theorem node_21268 : Outcome ⟨4, 17, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 17, 14, 2⟩) (by decide) node_20476

theorem node_21269 : Outcome ⟨4, 17, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 17, 14, 2⟩) (by decide) node_20476

theorem node_21270 : Outcome ⟨4, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 18, 11, 4⟩) (by decide) node_19817

theorem node_21271 : Outcome ⟨4, 18, 13, 6⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 12⟩) (by decide) node_16106

theorem node_21272 : Outcome ⟨4, 19, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 19, 12, 6⟩) (by decide) node_18865

theorem node_21273 : Outcome ⟨4, 19, 12, 16⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 12⟩) (by decide) node_16116

theorem node_21274 : Outcome ⟨4, 20, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 18, 11, 4⟩) (by decide) node_19817

theorem node_21275 : Outcome ⟨4, 20, 11, 14⟩ true :=
  Outcome.win (q := ⟨4, 20, 5, 12⟩) (by decide) node_16149

theorem node_21276 : Outcome ⟨5, 11, 19, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 4⟩) (by decide) node_19767

theorem node_21277 : Outcome ⟨5, 11, 19, 4⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 4⟩) (by decide) node_19767

theorem node_21278 : Outcome ⟨5, 11, 19, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 19, 4⟩) (by decide) node_19767

theorem node_21279 : Outcome ⟨5, 12, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 18, 2⟩, ⟨3, 12, 18, 4⟩, ⟨5, 11, 18, 2⟩, ⟨5, 10, 18, 4⟩, ⟨5, 12, 17, 2⟩, ⟨5, 12, 16, 4⟩]
  exact AllWinning.cons node_20491 (AllWinning.cons node_19770 (AllWinning.cons node_20522 (AllWinning.cons node_19831 (AllWinning.cons node_20524 (AllWinning.cons node_19835 (AllWinning.nil))))))

theorem node_21280 : Outcome ⟨5, 12, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 18, 2⟩, ⟨3, 12, 18, 4⟩, ⟨2, 12, 18, 6⟩, ⟨1, 12, 18, 8⟩, ⟨5, 11, 18, 2⟩, ⟨5, 10, 18, 4⟩, ⟨5, 9, 18, 6⟩, ⟨5, 8, 18, 8⟩, ⟨5, 12, 17, 2⟩, ⟨5, 12, 16, 4⟩, ⟨5, 12, 15, 6⟩, ⟨5, 12, 14, 8⟩]
  exact AllWinning.cons node_20491 (AllWinning.cons node_19770 (AllWinning.cons node_18875 (AllWinning.cons node_17915 (AllWinning.cons node_20522 (AllWinning.cons node_19831 (AllWinning.cons node_18972 (AllWinning.cons node_18061 (AllWinning.cons node_20524 (AllWinning.cons node_19835 (AllWinning.cons node_18979 (AllWinning.cons node_18074 (AllWinning.nil))))))))))))

theorem node_21281 : Outcome ⟨5, 12, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 18, 2⟩, ⟨3, 12, 18, 4⟩, ⟨2, 12, 18, 6⟩, ⟨1, 12, 18, 8⟩, ⟨0, 12, 18, 10⟩, ⟨5, 11, 18, 2⟩, ⟨5, 10, 18, 4⟩, ⟨5, 9, 18, 6⟩, ⟨5, 8, 18, 8⟩, ⟨5, 7, 18, 10⟩, ⟨5, 6, 18, 12⟩, ⟨5, 12, 17, 2⟩, ⟨5, 12, 16, 4⟩, ⟨5, 12, 15, 6⟩, ⟨5, 12, 14, 8⟩, ⟨5, 12, 13, 10⟩, ⟨5, 12, 12, 12⟩]
  exact AllWinning.cons node_20491 (AllWinning.cons node_19770 (AllWinning.cons node_18875 (AllWinning.cons node_17915 (AllWinning.cons node_16980 (AllWinning.cons node_20522 (AllWinning.cons node_19831 (AllWinning.cons node_18972 (AllWinning.cons node_18061 (AllWinning.cons node_17177 (AllWinning.cons node_16159 (AllWinning.cons node_20524 (AllWinning.cons node_19835 (AllWinning.cons node_18979 (AllWinning.cons node_18074 (AllWinning.cons node_17189 (AllWinning.cons node_16174 (AllWinning.nil)))))))))))))))))

theorem node_21282 : Outcome ⟨5, 12, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 18, 2⟩, ⟨3, 12, 18, 4⟩, ⟨2, 12, 18, 6⟩, ⟨1, 12, 18, 8⟩, ⟨0, 12, 18, 10⟩, ⟨5, 11, 18, 2⟩, ⟨5, 10, 18, 4⟩, ⟨5, 9, 18, 6⟩, ⟨5, 8, 18, 8⟩, ⟨5, 7, 18, 10⟩, ⟨5, 6, 18, 12⟩, ⟨5, 5, 18, 14⟩, ⟨5, 4, 18, 16⟩, ⟨5, 12, 17, 2⟩, ⟨5, 12, 16, 4⟩, ⟨5, 12, 15, 6⟩, ⟨5, 12, 14, 8⟩, ⟨5, 12, 13, 10⟩, ⟨5, 12, 12, 12⟩, ⟨5, 12, 11, 14⟩, ⟨5, 12, 10, 16⟩]
  exact AllWinning.cons node_20491 (AllWinning.cons node_19770 (AllWinning.cons node_18875 (AllWinning.cons node_17915 (AllWinning.cons node_16980 (AllWinning.cons node_20522 (AllWinning.cons node_19831 (AllWinning.cons node_18972 (AllWinning.cons node_18061 (AllWinning.cons node_17177 (AllWinning.cons node_16159 (AllWinning.cons node_15157 (AllWinning.cons node_14214 (AllWinning.cons node_20524 (AllWinning.cons node_19835 (AllWinning.cons node_18979 (AllWinning.cons node_18074 (AllWinning.cons node_17189 (AllWinning.cons node_16174 (AllWinning.cons node_15184 (AllWinning.cons node_14240 (AllWinning.nil)))))))))))))))))))))

theorem node_21283 : Outcome ⟨5, 12, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 18, 2⟩, ⟨3, 12, 18, 4⟩, ⟨2, 12, 18, 6⟩, ⟨1, 12, 18, 8⟩, ⟨0, 12, 18, 10⟩, ⟨5, 11, 18, 2⟩, ⟨5, 10, 18, 4⟩, ⟨5, 9, 18, 6⟩, ⟨5, 8, 18, 8⟩, ⟨5, 7, 18, 10⟩, ⟨5, 6, 18, 12⟩, ⟨5, 5, 18, 14⟩, ⟨5, 4, 18, 16⟩, ⟨5, 3, 18, 18⟩, ⟨5, 2, 18, 20⟩, ⟨5, 1, 18, 22⟩, ⟨5, 0, 18, 24⟩, ⟨5, 12, 17, 2⟩, ⟨5, 12, 16, 4⟩, ⟨5, 12, 15, 6⟩, ⟨5, 12, 14, 8⟩, ⟨5, 12, 13, 10⟩, ⟨5, 12, 12, 12⟩, ⟨5, 12, 11, 14⟩, ⟨5, 12, 10, 16⟩, ⟨5, 12, 9, 18⟩, ⟨5, 12, 8, 20⟩, ⟨5, 12, 7, 22⟩, ⟨5, 12, 6, 24⟩]
  exact AllWinning.cons node_20491 (AllWinning.cons node_19770 (AllWinning.cons node_18875 (AllWinning.cons node_17915 (AllWinning.cons node_16980 (AllWinning.cons node_20522 (AllWinning.cons node_19831 (AllWinning.cons node_18972 (AllWinning.cons node_18061 (AllWinning.cons node_17177 (AllWinning.cons node_16159 (AllWinning.cons node_15157 (AllWinning.cons node_14214 (AllWinning.cons node_13251 (AllWinning.cons node_12287 (AllWinning.cons node_11303 (AllWinning.cons node_10252 (AllWinning.cons node_20524 (AllWinning.cons node_19835 (AllWinning.cons node_18979 (AllWinning.cons node_18074 (AllWinning.cons node_17189 (AllWinning.cons node_16174 (AllWinning.cons node_15184 (AllWinning.cons node_14240 (AllWinning.cons node_13275 (AllWinning.cons node_12318 (AllWinning.cons node_11344 (AllWinning.cons node_10307 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_21284 : Outcome ⟨5, 12, 18, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 18, 2⟩, ⟨3, 12, 18, 4⟩, ⟨2, 12, 18, 6⟩, ⟨1, 12, 18, 8⟩, ⟨0, 12, 18, 10⟩, ⟨5, 11, 18, 2⟩, ⟨5, 10, 18, 4⟩, ⟨5, 9, 18, 6⟩, ⟨5, 8, 18, 8⟩, ⟨5, 7, 18, 10⟩, ⟨5, 6, 18, 12⟩, ⟨5, 5, 18, 14⟩, ⟨5, 4, 18, 16⟩, ⟨5, 3, 18, 18⟩, ⟨5, 2, 18, 20⟩, ⟨5, 1, 18, 22⟩, ⟨5, 0, 18, 24⟩, ⟨5, 12, 17, 2⟩, ⟨5, 12, 16, 4⟩, ⟨5, 12, 15, 6⟩, ⟨5, 12, 14, 8⟩, ⟨5, 12, 13, 10⟩, ⟨5, 12, 12, 12⟩, ⟨5, 12, 11, 14⟩, ⟨5, 12, 10, 16⟩, ⟨5, 12, 9, 18⟩, ⟨5, 12, 8, 20⟩, ⟨5, 12, 7, 22⟩, ⟨5, 12, 6, 24⟩, ⟨5, 12, 5, 26⟩, ⟨5, 12, 4, 28⟩, ⟨5, 12, 3, 30⟩, ⟨5, 12, 2, 32⟩]
  exact AllWinning.cons node_20491 (AllWinning.cons node_19770 (AllWinning.cons node_18875 (AllWinning.cons node_17915 (AllWinning.cons node_16980 (AllWinning.cons node_20522 (AllWinning.cons node_19831 (AllWinning.cons node_18972 (AllWinning.cons node_18061 (AllWinning.cons node_17177 (AllWinning.cons node_16159 (AllWinning.cons node_15157 (AllWinning.cons node_14214 (AllWinning.cons node_13251 (AllWinning.cons node_12287 (AllWinning.cons node_11303 (AllWinning.cons node_10252 (AllWinning.cons node_20524 (AllWinning.cons node_19835 (AllWinning.cons node_18979 (AllWinning.cons node_18074 (AllWinning.cons node_17189 (AllWinning.cons node_16174 (AllWinning.cons node_15184 (AllWinning.cons node_14240 (AllWinning.cons node_13275 (AllWinning.cons node_12318 (AllWinning.cons node_11344 (AllWinning.cons node_10307 (AllWinning.cons node_9318 (AllWinning.cons node_8329 (AllWinning.cons node_7397 (AllWinning.cons node_6479 (AllWinning.nil)))))))))))))))))))))))))))))))))

theorem node_21285 : Outcome ⟨5, 13, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 17, 2⟩) (by decide) node_20492

theorem node_21286 : Outcome ⟨5, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 8⟩) (by decide) node_17920

theorem node_21287 : Outcome ⟨5, 13, 17, 8⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 12⟩) (by decide) node_16165

theorem node_21288 : Outcome ⟨5, 14, 16, 4⟩ true :=
  Outcome.win (q := ⟨5, 14, 14, 4⟩) (by decide) node_19840

theorem node_21289 : Outcome ⟨5, 14, 16, 10⟩ true :=
  Outcome.win (q := ⟨5, 14, 14, 4⟩) (by decide) node_19840

theorem node_21290 : Outcome ⟨5, 15, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 15, 2⟩, ⟨3, 15, 15, 4⟩, ⟨5, 14, 15, 2⟩, ⟨5, 13, 15, 4⟩, ⟨5, 15, 14, 2⟩, ⟨5, 15, 13, 4⟩]
  exact AllWinning.cons node_20499 (AllWinning.cons node_19776 (AllWinning.cons node_20527 (AllWinning.cons node_19837 (AllWinning.cons node_20530 (AllWinning.cons node_19843 (AllWinning.nil))))))

theorem node_21291 : Outcome ⟨5, 15, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 15, 15, 2⟩, ⟨3, 15, 15, 4⟩, ⟨2, 15, 15, 6⟩, ⟨1, 15, 15, 8⟩, ⟨5, 14, 15, 2⟩, ⟨5, 13, 15, 4⟩, ⟨5, 12, 15, 6⟩, ⟨5, 11, 15, 8⟩, ⟨5, 15, 14, 2⟩, ⟨5, 15, 13, 4⟩, ⟨5, 15, 12, 6⟩, ⟨5, 15, 11, 8⟩]
  exact AllWinning.cons node_20499 (AllWinning.cons node_19776 (AllWinning.cons node_18885 (AllWinning.cons node_17929 (AllWinning.cons node_20527 (AllWinning.cons node_19837 (AllWinning.cons node_18979 (AllWinning.cons node_18070 (AllWinning.cons node_20530 (AllWinning.cons node_19843 (AllWinning.cons node_18983 (AllWinning.cons node_18085 (AllWinning.nil))))))))))))

theorem node_21292 : Outcome ⟨5, 15, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 14⟩) (by decide) node_15168

theorem node_21293 : Outcome ⟨5, 15, 15, 10⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 14⟩) (by decide) node_15168

theorem node_21294 : Outcome ⟨5, 16, 14, 4⟩ true :=
  Outcome.win (q := ⟨5, 14, 14, 4⟩) (by decide) node_19840

theorem node_21295 : Outcome ⟨5, 16, 14, 10⟩ true :=
  Outcome.win (q := ⟨5, 14, 14, 4⟩) (by decide) node_19840

theorem node_21296 : Outcome ⟨5, 17, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 13, 2⟩) (by decide) node_20506

theorem node_21297 : Outcome ⟨5, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 8⟩) (by decide) node_17937

theorem node_21298 : Outcome ⟨5, 17, 13, 8⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 12⟩) (by decide) node_16187

theorem node_21299 : Outcome ⟨5, 18, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨5, 17, 12, 2⟩, ⟨5, 16, 12, 4⟩, ⟨5, 18, 11, 2⟩, ⟨5, 18, 10, 4⟩]
  exact AllWinning.cons node_20509 (AllWinning.cons node_19782 (AllWinning.cons node_20534 (AllWinning.cons node_19846 (AllWinning.cons node_20536 (AllWinning.cons node_19851 (AllWinning.nil))))))

theorem node_21300 : Outcome ⟨5, 18, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨2, 18, 12, 6⟩, ⟨1, 18, 12, 8⟩, ⟨5, 17, 12, 2⟩, ⟨5, 16, 12, 4⟩, ⟨5, 15, 12, 6⟩, ⟨5, 14, 12, 8⟩, ⟨5, 18, 11, 2⟩, ⟨5, 18, 10, 4⟩, ⟨5, 18, 9, 6⟩, ⟨5, 18, 8, 8⟩]
  exact AllWinning.cons node_20509 (AllWinning.cons node_19782 (AllWinning.cons node_18893 (AllWinning.cons node_17942 (AllWinning.cons node_20534 (AllWinning.cons node_19846 (AllWinning.cons node_18983 (AllWinning.cons node_18082 (AllWinning.cons node_20536 (AllWinning.cons node_19851 (AllWinning.cons node_18990 (AllWinning.cons node_18094 (AllWinning.nil))))))))))))

theorem node_21301 : Outcome ⟨5, 18, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨2, 18, 12, 6⟩, ⟨1, 18, 12, 8⟩, ⟨0, 18, 12, 10⟩, ⟨5, 17, 12, 2⟩, ⟨5, 16, 12, 4⟩, ⟨5, 15, 12, 6⟩, ⟨5, 14, 12, 8⟩, ⟨5, 13, 12, 10⟩, ⟨5, 12, 12, 12⟩, ⟨5, 18, 11, 2⟩, ⟨5, 18, 10, 4⟩, ⟨5, 18, 9, 6⟩, ⟨5, 18, 8, 8⟩, ⟨5, 18, 7, 10⟩, ⟨5, 18, 6, 12⟩]
  exact AllWinning.cons node_20509 (AllWinning.cons node_19782 (AllWinning.cons node_18893 (AllWinning.cons node_17942 (AllWinning.cons node_17002 (AllWinning.cons node_20534 (AllWinning.cons node_19846 (AllWinning.cons node_18983 (AllWinning.cons node_18082 (AllWinning.cons node_17192 (AllWinning.cons node_16174 (AllWinning.cons node_20536 (AllWinning.cons node_19851 (AllWinning.cons node_18990 (AllWinning.cons node_18094 (AllWinning.cons node_17203 (AllWinning.cons node_16190 (AllWinning.nil)))))))))))))))))

theorem node_21302 : Outcome ⟨5, 18, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨2, 18, 12, 6⟩, ⟨1, 18, 12, 8⟩, ⟨0, 18, 12, 10⟩, ⟨5, 17, 12, 2⟩, ⟨5, 16, 12, 4⟩, ⟨5, 15, 12, 6⟩, ⟨5, 14, 12, 8⟩, ⟨5, 13, 12, 10⟩, ⟨5, 12, 12, 12⟩, ⟨5, 11, 12, 14⟩, ⟨5, 10, 12, 16⟩, ⟨5, 18, 11, 2⟩, ⟨5, 18, 10, 4⟩, ⟨5, 18, 9, 6⟩, ⟨5, 18, 8, 8⟩, ⟨5, 18, 7, 10⟩, ⟨5, 18, 6, 12⟩, ⟨5, 18, 5, 14⟩, ⟨5, 18, 4, 16⟩]
  exact AllWinning.cons node_20509 (AllWinning.cons node_19782 (AllWinning.cons node_18893 (AllWinning.cons node_17942 (AllWinning.cons node_17002 (AllWinning.cons node_20534 (AllWinning.cons node_19846 (AllWinning.cons node_18983 (AllWinning.cons node_18082 (AllWinning.cons node_17192 (AllWinning.cons node_16174 (AllWinning.cons node_15182 (AllWinning.cons node_14232 (AllWinning.cons node_20536 (AllWinning.cons node_19851 (AllWinning.cons node_18990 (AllWinning.cons node_18094 (AllWinning.cons node_17203 (AllWinning.cons node_16190 (AllWinning.cons node_15209 (AllWinning.cons node_14256 (AllWinning.nil)))))))))))))))))))))

theorem node_21303 : Outcome ⟨5, 18, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨2, 18, 12, 6⟩, ⟨1, 18, 12, 8⟩, ⟨0, 18, 12, 10⟩, ⟨5, 17, 12, 2⟩, ⟨5, 16, 12, 4⟩, ⟨5, 15, 12, 6⟩, ⟨5, 14, 12, 8⟩, ⟨5, 13, 12, 10⟩, ⟨5, 12, 12, 12⟩, ⟨5, 11, 12, 14⟩, ⟨5, 10, 12, 16⟩, ⟨5, 9, 12, 18⟩, ⟨5, 8, 12, 20⟩, ⟨5, 7, 12, 22⟩, ⟨5, 6, 12, 24⟩, ⟨5, 18, 11, 2⟩, ⟨5, 18, 10, 4⟩, ⟨5, 18, 9, 6⟩, ⟨5, 18, 8, 8⟩, ⟨5, 18, 7, 10⟩, ⟨5, 18, 6, 12⟩, ⟨5, 18, 5, 14⟩, ⟨5, 18, 4, 16⟩, ⟨5, 18, 3, 18⟩, ⟨5, 18, 2, 20⟩, ⟨5, 18, 1, 22⟩, ⟨5, 18, 0, 24⟩]
  exact AllWinning.cons node_20509 (AllWinning.cons node_19782 (AllWinning.cons node_18893 (AllWinning.cons node_17942 (AllWinning.cons node_17002 (AllWinning.cons node_20534 (AllWinning.cons node_19846 (AllWinning.cons node_18983 (AllWinning.cons node_18082 (AllWinning.cons node_17192 (AllWinning.cons node_16174 (AllWinning.cons node_15182 (AllWinning.cons node_14232 (AllWinning.cons node_13266 (AllWinning.cons node_12305 (AllWinning.cons node_11322 (AllWinning.cons node_10277 (AllWinning.cons node_20536 (AllWinning.cons node_19851 (AllWinning.cons node_18990 (AllWinning.cons node_18094 (AllWinning.cons node_17203 (AllWinning.cons node_16190 (AllWinning.cons node_15209 (AllWinning.cons node_14256 (AllWinning.cons node_13289 (AllWinning.cons node_12334 (AllWinning.cons node_11360 (AllWinning.cons node_10335 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_21304 : Outcome ⟨5, 18, 12, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 12, 2⟩, ⟨3, 18, 12, 4⟩, ⟨2, 18, 12, 6⟩, ⟨1, 18, 12, 8⟩, ⟨0, 18, 12, 10⟩, ⟨5, 17, 12, 2⟩, ⟨5, 16, 12, 4⟩, ⟨5, 15, 12, 6⟩, ⟨5, 14, 12, 8⟩, ⟨5, 13, 12, 10⟩, ⟨5, 12, 12, 12⟩, ⟨5, 11, 12, 14⟩, ⟨5, 10, 12, 16⟩, ⟨5, 9, 12, 18⟩, ⟨5, 8, 12, 20⟩, ⟨5, 7, 12, 22⟩, ⟨5, 6, 12, 24⟩, ⟨5, 5, 12, 26⟩, ⟨5, 4, 12, 28⟩, ⟨5, 3, 12, 30⟩, ⟨5, 2, 12, 32⟩, ⟨5, 18, 11, 2⟩, ⟨5, 18, 10, 4⟩, ⟨5, 18, 9, 6⟩, ⟨5, 18, 8, 8⟩, ⟨5, 18, 7, 10⟩, ⟨5, 18, 6, 12⟩, ⟨5, 18, 5, 14⟩, ⟨5, 18, 4, 16⟩, ⟨5, 18, 3, 18⟩, ⟨5, 18, 2, 20⟩, ⟨5, 18, 1, 22⟩, ⟨5, 18, 0, 24⟩]
  exact AllWinning.cons node_20509 (AllWinning.cons node_19782 (AllWinning.cons node_18893 (AllWinning.cons node_17942 (AllWinning.cons node_17002 (AllWinning.cons node_20534 (AllWinning.cons node_19846 (AllWinning.cons node_18983 (AllWinning.cons node_18082 (AllWinning.cons node_17192 (AllWinning.cons node_16174 (AllWinning.cons node_15182 (AllWinning.cons node_14232 (AllWinning.cons node_13266 (AllWinning.cons node_12305 (AllWinning.cons node_11322 (AllWinning.cons node_10277 (AllWinning.cons node_9290 (AllWinning.cons node_8303 (AllWinning.cons node_7365 (AllWinning.cons node_6432 (AllWinning.cons node_20536 (AllWinning.cons node_19851 (AllWinning.cons node_18990 (AllWinning.cons node_18094 (AllWinning.cons node_17203 (AllWinning.cons node_16190 (AllWinning.cons node_15209 (AllWinning.cons node_14256 (AllWinning.cons node_13289 (AllWinning.cons node_12334 (AllWinning.cons node_11360 (AllWinning.cons node_10335 (AllWinning.nil)))))))))))))))))))))))))))))))))

theorem node_21305 : Outcome ⟨5, 19, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 4⟩) (by decide) node_19785

theorem node_21306 : Outcome ⟨5, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 4⟩) (by decide) node_19785

theorem node_21307 : Outcome ⟨5, 19, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 19, 11, 4⟩) (by decide) node_19785

theorem node_21308 : Outcome ⟨6, 9, 20, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 6⟩) (by decide) node_18998

theorem node_21309 : Outcome ⟨6, 9, 20, 12⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 6⟩) (by decide) node_18998

theorem node_21310 : Outcome ⟨6, 10, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 2⟩) (by decide) node_20516

theorem node_21311 : Outcome ⟨6, 11, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 18, 4⟩) (by decide) node_19796

theorem node_21312 : Outcome ⟨6, 11, 18, 6⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 6⟩) (by decide) node_19018

theorem node_21313 : Outcome ⟨6, 12, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 2⟩) (by decide) node_20556

theorem node_21314 : Outcome ⟨6, 12, 17, 6⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 6⟩) (by decide) node_19010

theorem node_21315 : Outcome ⟨6, 12, 17, 8⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 6⟩) (by decide) node_19010

theorem node_21316 : Outcome ⟨6, 13, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 4⟩) (by decide) node_19864

theorem node_21317 : Outcome ⟨6, 13, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 4⟩) (by decide) node_19864

theorem node_21318 : Outcome ⟨6, 13, 16, 8⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 4⟩) (by decide) node_19864

theorem node_21319 : Outcome ⟨6, 14, 15, 4⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 6⟩) (by decide) node_19018

theorem node_21320 : Outcome ⟨6, 14, 15, 12⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 6⟩) (by decide) node_19018

theorem node_21321 : Outcome ⟨6, 14, 15, 14⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 6⟩) (by decide) node_19018

theorem node_21322 : Outcome ⟨6, 15, 14, 4⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 6⟩) (by decide) node_19030

theorem node_21323 : Outcome ⟨6, 15, 14, 12⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 6⟩) (by decide) node_19030

theorem node_21324 : Outcome ⟨6, 15, 14, 14⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 6⟩) (by decide) node_19030

theorem node_21325 : Outcome ⟨6, 16, 13, 2⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 4⟩) (by decide) node_19871

theorem node_21326 : Outcome ⟨6, 16, 13, 4⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 4⟩) (by decide) node_19871

theorem node_21327 : Outcome ⟨6, 16, 13, 8⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 4⟩) (by decide) node_19871

theorem node_21328 : Outcome ⟨6, 17, 12, 2⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 2⟩) (by decide) node_20572

theorem node_21329 : Outcome ⟨6, 17, 12, 6⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 6⟩) (by decide) node_19038

theorem node_21330 : Outcome ⟨6, 17, 12, 8⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 6⟩) (by decide) node_19038

theorem node_21331 : Outcome ⟨6, 18, 11, 2⟩ true :=
  Outcome.win (q := ⟨4, 18, 11, 4⟩) (by decide) node_19817

theorem node_21332 : Outcome ⟨6, 18, 11, 6⟩ true :=
  Outcome.win (q := ⟨6, 15, 11, 6⟩) (by decide) node_19030

theorem node_21333 : Outcome ⟨6, 19, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 2⟩) (by decide) node_20538

theorem node_21334 : Outcome ⟨6, 20, 9, 6⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 6⟩) (by decide) node_19038

theorem node_21335 : Outcome ⟨6, 20, 9, 12⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 6⟩) (by decide) node_19038

theorem node_21336 : Outcome ⟨7, 8, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 20, 2⟩, ⟨5, 8, 20, 4⟩, ⟨4, 8, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨7, 7, 20, 2⟩, ⟨7, 6, 20, 4⟩, ⟨7, 5, 20, 6⟩, ⟨7, 4, 20, 8⟩, ⟨7, 8, 19, 2⟩, ⟨7, 8, 18, 4⟩, ⟨7, 8, 17, 6⟩, ⟨7, 8, 16, 8⟩]
  exact AllWinning.cons node_20546 (AllWinning.cons node_19828 (AllWinning.cons node_18931 (AllWinning.cons node_17974 (AllWinning.cons node_20590 (AllWinning.cons node_19887 (AllWinning.cons node_19055 (AllWinning.cons node_18135 (AllWinning.cons node_20592 (AllWinning.cons node_19891 (AllWinning.cons node_19065 (AllWinning.cons node_18147 (AllWinning.nil))))))))))))

theorem node_21337 : Outcome ⟨7, 8, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 20, 2⟩, ⟨5, 8, 20, 4⟩, ⟨4, 8, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨2, 8, 20, 10⟩, ⟨1, 8, 20, 12⟩, ⟨7, 7, 20, 2⟩, ⟨7, 6, 20, 4⟩, ⟨7, 5, 20, 6⟩, ⟨7, 4, 20, 8⟩, ⟨7, 3, 20, 10⟩, ⟨7, 2, 20, 12⟩, ⟨7, 8, 19, 2⟩, ⟨7, 8, 18, 4⟩, ⟨7, 8, 17, 6⟩, ⟨7, 8, 16, 8⟩, ⟨7, 8, 15, 10⟩, ⟨7, 8, 14, 12⟩]
  exact AllWinning.cons node_20546 (AllWinning.cons node_19828 (AllWinning.cons node_18931 (AllWinning.cons node_17974 (AllWinning.cons node_17047 (AllWinning.cons node_15942 (AllWinning.cons node_20590 (AllWinning.cons node_19887 (AllWinning.cons node_19055 (AllWinning.cons node_18135 (AllWinning.cons node_17250 (AllWinning.cons node_16263 (AllWinning.cons node_20592 (AllWinning.cons node_19891 (AllWinning.cons node_19065 (AllWinning.cons node_18147 (AllWinning.cons node_17264 (AllWinning.cons node_16280 (AllWinning.nil))))))))))))))))))

theorem node_21338 : Outcome ⟨7, 8, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 20, 2⟩, ⟨5, 8, 20, 4⟩, ⟨4, 8, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨2, 8, 20, 10⟩, ⟨1, 8, 20, 12⟩, ⟨0, 8, 20, 14⟩, ⟨7, 7, 20, 2⟩, ⟨7, 6, 20, 4⟩, ⟨7, 5, 20, 6⟩, ⟨7, 4, 20, 8⟩, ⟨7, 3, 20, 10⟩, ⟨7, 2, 20, 12⟩, ⟨7, 1, 20, 14⟩, ⟨7, 0, 20, 16⟩, ⟨7, 8, 19, 2⟩, ⟨7, 8, 18, 4⟩, ⟨7, 8, 17, 6⟩, ⟨7, 8, 16, 8⟩, ⟨7, 8, 15, 10⟩, ⟨7, 8, 14, 12⟩, ⟨7, 8, 13, 14⟩, ⟨7, 8, 12, 16⟩]
  exact AllWinning.cons node_20546 (AllWinning.cons node_19828 (AllWinning.cons node_18931 (AllWinning.cons node_17974 (AllWinning.cons node_17047 (AllWinning.cons node_15942 (AllWinning.cons node_14920 (AllWinning.cons node_20590 (AllWinning.cons node_19887 (AllWinning.cons node_19055 (AllWinning.cons node_18135 (AllWinning.cons node_17250 (AllWinning.cons node_16263 (AllWinning.cons node_15270 (AllWinning.cons node_14326 (AllWinning.cons node_20592 (AllWinning.cons node_19891 (AllWinning.cons node_19065 (AllWinning.cons node_18147 (AllWinning.cons node_17264 (AllWinning.cons node_16280 (AllWinning.cons node_15288 (AllWinning.cons node_14353 (AllWinning.nil)))))))))))))))))))))))

theorem node_21339 : Outcome ⟨7, 8, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 20, 2⟩, ⟨5, 8, 20, 4⟩, ⟨4, 8, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨2, 8, 20, 10⟩, ⟨1, 8, 20, 12⟩, ⟨0, 8, 20, 14⟩, ⟨7, 7, 20, 2⟩, ⟨7, 6, 20, 4⟩, ⟨7, 5, 20, 6⟩, ⟨7, 4, 20, 8⟩, ⟨7, 3, 20, 10⟩, ⟨7, 2, 20, 12⟩, ⟨7, 1, 20, 14⟩, ⟨7, 0, 20, 16⟩, ⟨7, 8, 19, 2⟩, ⟨7, 8, 18, 4⟩, ⟨7, 8, 17, 6⟩, ⟨7, 8, 16, 8⟩, ⟨7, 8, 15, 10⟩, ⟨7, 8, 14, 12⟩, ⟨7, 8, 13, 14⟩, ⟨7, 8, 12, 16⟩, ⟨7, 8, 11, 18⟩, ⟨7, 8, 10, 20⟩]
  exact AllWinning.cons node_20546 (AllWinning.cons node_19828 (AllWinning.cons node_18931 (AllWinning.cons node_17974 (AllWinning.cons node_17047 (AllWinning.cons node_15942 (AllWinning.cons node_14920 (AllWinning.cons node_20590 (AllWinning.cons node_19887 (AllWinning.cons node_19055 (AllWinning.cons node_18135 (AllWinning.cons node_17250 (AllWinning.cons node_16263 (AllWinning.cons node_15270 (AllWinning.cons node_14326 (AllWinning.cons node_20592 (AllWinning.cons node_19891 (AllWinning.cons node_19065 (AllWinning.cons node_18147 (AllWinning.cons node_17264 (AllWinning.cons node_16280 (AllWinning.cons node_15288 (AllWinning.cons node_14353 (AllWinning.cons node_13391 (AllWinning.cons node_12451 (AllWinning.nil)))))))))))))))))))))))))

theorem node_21340 : Outcome ⟨7, 8, 20, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 8, 20, 2⟩, ⟨5, 8, 20, 4⟩, ⟨4, 8, 20, 6⟩, ⟨3, 8, 20, 8⟩, ⟨2, 8, 20, 10⟩, ⟨1, 8, 20, 12⟩, ⟨0, 8, 20, 14⟩, ⟨7, 7, 20, 2⟩, ⟨7, 6, 20, 4⟩, ⟨7, 5, 20, 6⟩, ⟨7, 4, 20, 8⟩, ⟨7, 3, 20, 10⟩, ⟨7, 2, 20, 12⟩, ⟨7, 1, 20, 14⟩, ⟨7, 0, 20, 16⟩, ⟨7, 8, 19, 2⟩, ⟨7, 8, 18, 4⟩, ⟨7, 8, 17, 6⟩, ⟨7, 8, 16, 8⟩, ⟨7, 8, 15, 10⟩, ⟨7, 8, 14, 12⟩, ⟨7, 8, 13, 14⟩, ⟨7, 8, 12, 16⟩, ⟨7, 8, 11, 18⟩, ⟨7, 8, 10, 20⟩, ⟨7, 8, 9, 22⟩, ⟨7, 8, 8, 24⟩]
  exact AllWinning.cons node_20546 (AllWinning.cons node_19828 (AllWinning.cons node_18931 (AllWinning.cons node_17974 (AllWinning.cons node_17047 (AllWinning.cons node_15942 (AllWinning.cons node_14920 (AllWinning.cons node_20590 (AllWinning.cons node_19887 (AllWinning.cons node_19055 (AllWinning.cons node_18135 (AllWinning.cons node_17250 (AllWinning.cons node_16263 (AllWinning.cons node_15270 (AllWinning.cons node_14326 (AllWinning.cons node_20592 (AllWinning.cons node_19891 (AllWinning.cons node_19065 (AllWinning.cons node_18147 (AllWinning.cons node_17264 (AllWinning.cons node_16280 (AllWinning.cons node_15288 (AllWinning.cons node_14353 (AllWinning.cons node_13391 (AllWinning.cons node_12451 (AllWinning.cons node_11462 (AllWinning.cons node_10455 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_21341 : Outcome ⟨7, 8, 20, 16⟩ true :=
  Outcome.win (q := ⟨7, 8, 6, 28⟩) (by decide) node_8470

theorem node_21342 : Outcome ⟨7, 10, 18, 6⟩ true :=
  Outcome.win (q := ⟨6, 10, 18, 2⟩) (by decide) node_20549

theorem node_21343 : Outcome ⟨7, 11, 17, 2⟩ true :=
  Outcome.win (q := ⟨7, 10, 17, 2⟩) (by decide) node_20596

theorem node_21344 : Outcome ⟨7, 12, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 2⟩) (by decide) node_20556

theorem node_21345 : Outcome ⟨7, 12, 16, 16⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 2⟩) (by decide) node_20556

theorem node_21346 : Outcome ⟨7, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 2⟩) (by decide) node_20607

theorem node_21347 : Outcome ⟨7, 13, 15, 6⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 12⟩) (by decide) node_16303

theorem node_21348 : Outcome ⟨7, 14, 14, 4⟩ true :=
  Outcome.win (q := ⟨5, 14, 14, 4⟩) (by decide) node_19840

theorem node_21349 : Outcome ⟨7, 14, 14, 14⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 14⟩) (by decide) node_14943

theorem node_21350 : Outcome ⟨7, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨7, 15, 12, 2⟩) (by decide) node_20618

theorem node_21351 : Outcome ⟨7, 15, 13, 6⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 12⟩) (by decide) node_16287

theorem node_21352 : Outcome ⟨7, 16, 12, 4⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 2⟩) (by decide) node_20572

theorem node_21353 : Outcome ⟨7, 16, 12, 16⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 2⟩) (by decide) node_20572

theorem node_21354 : Outcome ⟨7, 17, 11, 2⟩ true :=
  Outcome.win (q := ⟨7, 16, 11, 2⟩) (by decide) node_20625

theorem node_21355 : Outcome ⟨7, 18, 10, 6⟩ true :=
  Outcome.win (q := ⟨6, 18, 10, 2⟩) (by decide) node_20581

theorem node_21356 : Outcome ⟨7, 20, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 8, 2⟩, ⟨5, 20, 8, 4⟩, ⟨4, 20, 8, 6⟩, ⟨3, 20, 8, 8⟩, ⟨7, 19, 8, 2⟩, ⟨7, 18, 8, 4⟩, ⟨7, 17, 8, 6⟩, ⟨7, 16, 8, 8⟩, ⟨7, 20, 7, 2⟩, ⟨7, 20, 6, 4⟩, ⟨7, 20, 5, 6⟩, ⟨7, 20, 4, 8⟩]
  exact AllWinning.cons node_20588 (AllWinning.cons node_19854 (AllWinning.cons node_18964 (AllWinning.cons node_18012 (AllWinning.cons node_20638 (AllWinning.cons node_19909 (AllWinning.cons node_19087 (AllWinning.cons node_18175 (AllWinning.cons node_20640 (AllWinning.cons node_19911 (AllWinning.cons node_19097 (AllWinning.cons node_18186 (AllWinning.nil))))))))))))

theorem node_21357 : Outcome ⟨7, 20, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 20, 8, 2⟩, ⟨5, 20, 8, 4⟩, ⟨4, 20, 8, 6⟩, ⟨3, 20, 8, 8⟩, ⟨2, 20, 8, 10⟩, ⟨1, 20, 8, 12⟩, ⟨7, 19, 8, 2⟩, ⟨7, 18, 8, 4⟩, ⟨7, 17, 8, 6⟩, ⟨7, 16, 8, 8⟩, ⟨7, 15, 8, 10⟩, ⟨7, 14, 8, 12⟩, ⟨7, 20, 7, 2⟩, ⟨7, 20, 6, 4⟩, ⟨7, 20, 5, 6⟩, ⟨7, 20, 4, 8⟩, ⟨7, 20, 3, 10⟩, ⟨7, 20, 2, 12⟩]
  exact AllWinning.cons node_20588 (AllWinning.cons node_19854 (AllWinning.cons node_18964 (AllWinning.cons node_18012 (AllWinning.cons node_17088 (AllWinning.cons node_15982 (AllWinning.cons node_20638 (AllWinning.cons node_19909 (AllWinning.cons node_19087 (AllWinning.cons node_18175 (AllWinning.cons node_17287 (AllWinning.cons node_16309 (AllWinning.cons node_20640 (AllWinning.cons node_19911 (AllWinning.cons node_19097 (AllWinning.cons node_18186 (AllWinning.cons node_17301 (AllWinning.cons node_16327 (AllWinning.nil))))))))))))))))))

end RQ9F1
