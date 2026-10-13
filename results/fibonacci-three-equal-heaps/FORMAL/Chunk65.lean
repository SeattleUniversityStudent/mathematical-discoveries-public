import Chunk64
set_option autoImplicit false
namespace RQ9F1

theorem node_14893 : Outcome ⟨18, 7, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 7, 2, 2⟩, ⟨16, 7, 2, 4⟩, ⟨15, 7, 2, 6⟩, ⟨14, 7, 2, 8⟩, ⟨13, 7, 2, 10⟩, ⟨12, 7, 2, 12⟩, ⟨11, 7, 2, 14⟩, ⟨10, 7, 2, 16⟩, ⟨9, 7, 2, 18⟩, ⟨8, 7, 2, 20⟩, ⟨7, 7, 2, 22⟩, ⟨6, 7, 2, 24⟩, ⟨18, 6, 2, 2⟩, ⟨18, 5, 2, 4⟩, ⟨18, 4, 2, 6⟩, ⟨18, 3, 2, 8⟩, ⟨18, 2, 2, 10⟩, ⟨18, 1, 2, 12⟩, ⟨18, 0, 2, 14⟩, ⟨18, 7, 1, 2⟩, ⟨18, 7, 0, 4⟩]
  exact AllWinning.cons node_13896 (AllWinning.cons node_12892 (AllWinning.cons node_11860 (AllWinning.cons node_10828 (AllWinning.cons node_9730 (AllWinning.cons node_8750 (AllWinning.cons node_7725 (AllWinning.cons node_6727 (AllWinning.cons node_5865 (AllWinning.cons node_5106 (AllWinning.cons node_4382 (AllWinning.cons node_3718 (AllWinning.cons node_13922 (AllWinning.cons node_12947 (AllWinning.cons node_11939 (AllWinning.cons node_10946 (AllWinning.cons node_9856 (AllWinning.cons node_8895 (AllWinning.cons node_7896 (AllWinning.cons node_13924 (AllWinning.cons node_12952 (AllWinning.nil)))))))))))))))))))))

theorem node_14894 : Outcome ⟨18, 7, 2, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 7, 2, 2⟩, ⟨16, 7, 2, 4⟩, ⟨15, 7, 2, 6⟩, ⟨14, 7, 2, 8⟩, ⟨13, 7, 2, 10⟩, ⟨12, 7, 2, 12⟩, ⟨11, 7, 2, 14⟩, ⟨10, 7, 2, 16⟩, ⟨9, 7, 2, 18⟩, ⟨8, 7, 2, 20⟩, ⟨7, 7, 2, 22⟩, ⟨6, 7, 2, 24⟩, ⟨5, 7, 2, 26⟩, ⟨4, 7, 2, 28⟩, ⟨18, 6, 2, 2⟩, ⟨18, 5, 2, 4⟩, ⟨18, 4, 2, 6⟩, ⟨18, 3, 2, 8⟩, ⟨18, 2, 2, 10⟩, ⟨18, 1, 2, 12⟩, ⟨18, 0, 2, 14⟩, ⟨18, 7, 1, 2⟩, ⟨18, 7, 0, 4⟩]
  exact AllWinning.cons node_13896 (AllWinning.cons node_12892 (AllWinning.cons node_11860 (AllWinning.cons node_10828 (AllWinning.cons node_9730 (AllWinning.cons node_8750 (AllWinning.cons node_7725 (AllWinning.cons node_6727 (AllWinning.cons node_5865 (AllWinning.cons node_5106 (AllWinning.cons node_4382 (AllWinning.cons node_3718 (AllWinning.cons node_3116 (AllWinning.cons node_2616 (AllWinning.cons node_13922 (AllWinning.cons node_12947 (AllWinning.cons node_11939 (AllWinning.cons node_10946 (AllWinning.cons node_9856 (AllWinning.cons node_8895 (AllWinning.cons node_7896 (AllWinning.cons node_13924 (AllWinning.cons node_12952 (AllWinning.nil)))))))))))))))))))))))

theorem node_14895 : Outcome ⟨18, 8, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 8, 1, 2⟩, ⟨16, 8, 1, 4⟩, ⟨18, 7, 1, 2⟩, ⟨18, 6, 1, 4⟩, ⟨18, 8, 0, 2⟩]
  exact AllWinning.cons node_13899 (AllWinning.cons node_12897 (AllWinning.cons node_13924 (AllWinning.cons node_12950 (AllWinning.cons node_13925 (AllWinning.nil)))))

theorem node_14896 : Outcome ⟨18, 8, 1, 12⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 12⟩) (by decide) node_8756

theorem node_14897 : Outcome ⟨18, 8, 1, 14⟩ true :=
  Outcome.win (q := ⟨12, 8, 1, 12⟩) (by decide) node_8756

theorem node_14898 : Outcome ⟨18, 9, 0, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 0, 2⟩) (by decide) node_13902

theorem node_14899 : Outcome ⟨18, 9, 0, 8⟩ true :=
  Outcome.win (q := ⟨18, 5, 0, 8⟩) (by decide) node_10952

theorem node_14900 : Outcome ⟨19, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨19, 0, 6, 4⟩) (by decide) node_12955

theorem node_14901 : Outcome ⟨19, 0, 8, 6⟩ true :=
  Outcome.win (q := ⟨19, 0, 6, 4⟩) (by decide) node_12955

theorem node_14902 : Outcome ⟨19, 0, 8, 22⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 22⟩) (by decide) node_4400

theorem node_14903 : Outcome ⟨19, 1, 7, 4⟩ true :=
  Outcome.win (q := ⟨19, 1, 3, 8⟩) (by decide) node_10962

theorem node_14904 : Outcome ⟨19, 1, 7, 10⟩ true :=
  Outcome.win (q := ⟨11, 1, 7, 16⟩) (by decide) node_6748

theorem node_14905 : Outcome ⟨19, 2, 6, 4⟩ true :=
  Outcome.win (q := ⟨17, 2, 6, 4⟩) (by decide) node_12912

theorem node_14906 : Outcome ⟨19, 2, 6, 10⟩ true :=
  Outcome.win (q := ⟨11, 2, 6, 16⟩) (by decide) node_6758

theorem node_14907 : Outcome ⟨19, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨19, 3, 1, 8⟩) (by decide) node_10969

theorem node_14908 : Outcome ⟨19, 3, 5, 14⟩ true :=
  Outcome.win (q := ⟨11, 3, 5, 16⟩) (by decide) node_6767

theorem node_14909 : Outcome ⟨19, 4, 4, 4⟩ true :=
  Outcome.win (q := ⟨19, 2, 4, 4⟩) (by decide) node_12964

theorem node_14910 : Outcome ⟨19, 4, 4, 20⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 38⟩) (by decide) node_714

theorem node_14911 : Outcome ⟨19, 5, 3, 14⟩ true :=
  Outcome.win (q := ⟨11, 5, 3, 16⟩) (by decide) node_6781

theorem node_14912 : Outcome ⟨19, 6, 2, 4⟩ true :=
  Outcome.win (q := ⟨17, 6, 2, 4⟩) (by decide) node_12925

theorem node_14913 : Outcome ⟨19, 6, 2, 10⟩ true :=
  Outcome.win (q := ⟨11, 6, 2, 16⟩) (by decide) node_6792

theorem node_14914 : Outcome ⟨19, 7, 1, 4⟩ true :=
  Outcome.win (q := ⟨19, 3, 1, 8⟩) (by decide) node_10969

theorem node_14915 : Outcome ⟨19, 7, 1, 10⟩ true :=
  Outcome.win (q := ⟨11, 7, 1, 16⟩) (by decide) node_6801

theorem node_14916 : Outcome ⟨19, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨19, 6, 0, 4⟩) (by decide) node_12973

theorem node_14917 : Outcome ⟨19, 8, 0, 6⟩ true :=
  Outcome.win (q := ⟨19, 6, 0, 4⟩) (by decide) node_12973

theorem node_14918 : Outcome ⟨19, 8, 0, 22⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 22⟩) (by decide) node_4441

theorem node_14919 : Outcome ⟨0, 8, 20, 8⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 2⟩) (by decide) node_13944

theorem node_14920 : Outcome ⟨0, 8, 20, 14⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 24⟩) (by decide) node_3969

theorem node_14921 : Outcome ⟨0, 9, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 17, 4⟩) (by decide) node_12989

theorem node_14922 : Outcome ⟨0, 9, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 19, 6⟩) (by decide) node_11963

theorem node_14923 : Outcome ⟨0, 9, 19, 20⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 20⟩) (by decide) node_5353

theorem node_14924 : Outcome ⟨0, 10, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 18, 2⟩, ⟨0, 8, 18, 4⟩, ⟨0, 10, 17, 2⟩, ⟨0, 10, 16, 4⟩]
  exact AllWinning.cons node_13952 (AllWinning.cons node_12985 (AllWinning.cons node_13955 (AllWinning.cons node_12994 (AllWinning.nil))))

theorem node_14925 : Outcome ⟨0, 10, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 18, 2⟩, ⟨0, 8, 18, 4⟩, ⟨0, 7, 18, 6⟩, ⟨0, 6, 18, 8⟩, ⟨0, 10, 17, 2⟩, ⟨0, 10, 16, 4⟩, ⟨0, 10, 15, 6⟩, ⟨0, 10, 14, 8⟩]
  exact AllWinning.cons node_13952 (AllWinning.cons node_12985 (AllWinning.cons node_11968 (AllWinning.cons node_10980 (AllWinning.cons node_13955 (AllWinning.cons node_12994 (AllWinning.cons node_11979 (AllWinning.cons node_10996 (AllWinning.nil))))))))

theorem node_14926 : Outcome ⟨0, 10, 18, 6⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 10⟩) (by decide) node_9879

theorem node_14927 : Outcome ⟨0, 10, 18, 12⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 16⟩) (by decide) node_6987

theorem node_14928 : Outcome ⟨0, 10, 18, 16⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 16⟩) (by decide) node_6987

theorem node_14929 : Outcome ⟨0, 11, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 17, 4⟩) (by decide) node_12989

theorem node_14930 : Outcome ⟨0, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 17, 4⟩) (by decide) node_12989

theorem node_14931 : Outcome ⟨0, 11, 17, 12⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 12⟩) (by decide) node_8943

theorem node_14932 : Outcome ⟨0, 12, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 16, 2⟩) (by decide) node_13959

theorem node_14933 : Outcome ⟨0, 12, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 8⟩) (by decide) node_11002

theorem node_14934 : Outcome ⟨0, 12, 16, 12⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 8⟩) (by decide) node_11002

theorem node_14935 : Outcome ⟨0, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_14936 : Outcome ⟨0, 13, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_14937 : Outcome ⟨0, 14, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.nil))))

theorem node_14938 : Outcome ⟨0, 14, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.nil))))))))

theorem node_14939 : Outcome ⟨0, 14, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨0, 8, 14, 12⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 14, 9, 10⟩, ⟨0, 14, 8, 12⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_9897 (AllWinning.cons node_8931 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.cons node_9909 (AllWinning.cons node_8955 (AllWinning.nil))))))))))))

theorem node_14940 : Outcome ⟨0, 14, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨0, 8, 14, 12⟩, ⟨0, 7, 14, 14⟩, ⟨0, 6, 14, 16⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 14, 9, 10⟩, ⟨0, 14, 8, 12⟩, ⟨0, 14, 7, 14⟩, ⟨0, 14, 6, 16⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_9897 (AllWinning.cons node_8931 (AllWinning.cons node_7933 (AllWinning.cons node_6969 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.cons node_9909 (AllWinning.cons node_8955 (AllWinning.cons node_7956 (AllWinning.cons node_7005 (AllWinning.nil))))))))))))))))

theorem node_14941 : Outcome ⟨0, 14, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨0, 8, 14, 12⟩, ⟨0, 7, 14, 14⟩, ⟨0, 6, 14, 16⟩, ⟨0, 5, 14, 18⟩, ⟨0, 4, 14, 20⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 14, 9, 10⟩, ⟨0, 14, 8, 12⟩, ⟨0, 14, 7, 14⟩, ⟨0, 14, 6, 16⟩, ⟨0, 14, 5, 18⟩, ⟨0, 14, 4, 20⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_9897 (AllWinning.cons node_8931 (AllWinning.cons node_7933 (AllWinning.cons node_6969 (AllWinning.cons node_6056 (AllWinning.cons node_5327 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.cons node_9909 (AllWinning.cons node_8955 (AllWinning.cons node_7956 (AllWinning.cons node_7005 (AllWinning.cons node_6095 (AllWinning.cons node_5373 (AllWinning.nil))))))))))))))))))))

theorem node_14942 : Outcome ⟨0, 14, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨0, 8, 14, 12⟩, ⟨0, 7, 14, 14⟩, ⟨0, 6, 14, 16⟩, ⟨0, 5, 14, 18⟩, ⟨0, 4, 14, 20⟩, ⟨0, 3, 14, 22⟩, ⟨0, 2, 14, 24⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 14, 9, 10⟩, ⟨0, 14, 8, 12⟩, ⟨0, 14, 7, 14⟩, ⟨0, 14, 6, 16⟩, ⟨0, 14, 5, 18⟩, ⟨0, 14, 4, 20⟩, ⟨0, 14, 3, 22⟩, ⟨0, 14, 2, 24⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_9897 (AllWinning.cons node_8931 (AllWinning.cons node_7933 (AllWinning.cons node_6969 (AllWinning.cons node_6056 (AllWinning.cons node_5327 (AllWinning.cons node_4586 (AllWinning.cons node_3937 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.cons node_9909 (AllWinning.cons node_8955 (AllWinning.cons node_7956 (AllWinning.cons node_7005 (AllWinning.cons node_6095 (AllWinning.cons node_5373 (AllWinning.cons node_4633 (AllWinning.cons node_3993 (AllWinning.nil))))))))))))))))))))))))

theorem node_14943 : Outcome ⟨0, 14, 14, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨0, 8, 14, 12⟩, ⟨0, 7, 14, 14⟩, ⟨0, 6, 14, 16⟩, ⟨0, 5, 14, 18⟩, ⟨0, 4, 14, 20⟩, ⟨0, 3, 14, 22⟩, ⟨0, 2, 14, 24⟩, ⟨0, 1, 14, 26⟩, ⟨0, 0, 14, 28⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 14, 9, 10⟩, ⟨0, 14, 8, 12⟩, ⟨0, 14, 7, 14⟩, ⟨0, 14, 6, 16⟩, ⟨0, 14, 5, 18⟩, ⟨0, 14, 4, 20⟩, ⟨0, 14, 3, 22⟩, ⟨0, 14, 2, 24⟩, ⟨0, 14, 1, 26⟩, ⟨0, 14, 0, 28⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_9897 (AllWinning.cons node_8931 (AllWinning.cons node_7933 (AllWinning.cons node_6969 (AllWinning.cons node_6056 (AllWinning.cons node_5327 (AllWinning.cons node_4586 (AllWinning.cons node_3937 (AllWinning.cons node_3328 (AllWinning.cons node_2824 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.cons node_9909 (AllWinning.cons node_8955 (AllWinning.cons node_7956 (AllWinning.cons node_7005 (AllWinning.cons node_6095 (AllWinning.cons node_5373 (AllWinning.cons node_4633 (AllWinning.cons node_3993 (AllWinning.cons node_3380 (AllWinning.cons node_2889 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_14944 : Outcome ⟨0, 14, 14, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨0, 8, 14, 12⟩, ⟨0, 7, 14, 14⟩, ⟨0, 6, 14, 16⟩, ⟨0, 5, 14, 18⟩, ⟨0, 4, 14, 20⟩, ⟨0, 3, 14, 22⟩, ⟨0, 2, 14, 24⟩, ⟨0, 1, 14, 26⟩, ⟨0, 0, 14, 28⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 14, 9, 10⟩, ⟨0, 14, 8, 12⟩, ⟨0, 14, 7, 14⟩, ⟨0, 14, 6, 16⟩, ⟨0, 14, 5, 18⟩, ⟨0, 14, 4, 20⟩, ⟨0, 14, 3, 22⟩, ⟨0, 14, 2, 24⟩, ⟨0, 14, 1, 26⟩, ⟨0, 14, 0, 28⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_9897 (AllWinning.cons node_8931 (AllWinning.cons node_7933 (AllWinning.cons node_6969 (AllWinning.cons node_6056 (AllWinning.cons node_5327 (AllWinning.cons node_4586 (AllWinning.cons node_3937 (AllWinning.cons node_3328 (AllWinning.cons node_2824 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.cons node_9909 (AllWinning.cons node_8955 (AllWinning.cons node_7956 (AllWinning.cons node_7005 (AllWinning.cons node_6095 (AllWinning.cons node_5373 (AllWinning.cons node_4633 (AllWinning.cons node_3993 (AllWinning.cons node_3380 (AllWinning.cons node_2889 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_14945 : Outcome ⟨0, 14, 14, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨0, 11, 14, 6⟩, ⟨0, 10, 14, 8⟩, ⟨0, 9, 14, 10⟩, ⟨0, 8, 14, 12⟩, ⟨0, 7, 14, 14⟩, ⟨0, 6, 14, 16⟩, ⟨0, 5, 14, 18⟩, ⟨0, 4, 14, 20⟩, ⟨0, 3, 14, 22⟩, ⟨0, 2, 14, 24⟩, ⟨0, 1, 14, 26⟩, ⟨0, 0, 14, 28⟩, ⟨0, 14, 13, 2⟩, ⟨0, 14, 12, 4⟩, ⟨0, 14, 11, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 14, 9, 10⟩, ⟨0, 14, 8, 12⟩, ⟨0, 14, 7, 14⟩, ⟨0, 14, 6, 16⟩, ⟨0, 14, 5, 18⟩, ⟨0, 14, 4, 20⟩, ⟨0, 14, 3, 22⟩, ⟨0, 14, 2, 24⟩, ⟨0, 14, 1, 26⟩, ⟨0, 14, 0, 28⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_12999 (AllWinning.cons node_11982 (AllWinning.cons node_10996 (AllWinning.cons node_9897 (AllWinning.cons node_8931 (AllWinning.cons node_7933 (AllWinning.cons node_6969 (AllWinning.cons node_6056 (AllWinning.cons node_5327 (AllWinning.cons node_4586 (AllWinning.cons node_3937 (AllWinning.cons node_3328 (AllWinning.cons node_2824 (AllWinning.cons node_13970 (AllWinning.cons node_13009 (AllWinning.cons node_11988 (AllWinning.cons node_11011 (AllWinning.cons node_9909 (AllWinning.cons node_8955 (AllWinning.cons node_7956 (AllWinning.cons node_7005 (AllWinning.cons node_6095 (AllWinning.cons node_5373 (AllWinning.cons node_4633 (AllWinning.cons node_3993 (AllWinning.cons node_3380 (AllWinning.cons node_2889 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_14946 : Outcome ⟨0, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_14947 : Outcome ⟨0, 15, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_14948 : Outcome ⟨0, 16, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 11, 2⟩) (by decide) node_13976

theorem node_14949 : Outcome ⟨0, 16, 12, 8⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 8⟩) (by decide) node_11002

theorem node_14950 : Outcome ⟨0, 16, 12, 12⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 8⟩) (by decide) node_11002

theorem node_14951 : Outcome ⟨0, 17, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 9, 4⟩) (by decide) node_13018

theorem node_14952 : Outcome ⟨0, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 17, 9, 4⟩) (by decide) node_13018

theorem node_14953 : Outcome ⟨0, 17, 11, 12⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 12⟩) (by decide) node_8943

theorem node_14954 : Outcome ⟨0, 18, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 10, 2⟩, ⟨0, 16, 10, 4⟩, ⟨0, 18, 9, 2⟩, ⟨0, 18, 8, 4⟩]
  exact AllWinning.cons node_13981 (AllWinning.cons node_13015 (AllWinning.cons node_13985 (AllWinning.cons node_13023 (AllWinning.nil))))

theorem node_14955 : Outcome ⟨0, 18, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 10, 2⟩, ⟨0, 16, 10, 4⟩, ⟨0, 15, 10, 6⟩, ⟨0, 14, 10, 8⟩, ⟨0, 18, 9, 2⟩, ⟨0, 18, 8, 4⟩, ⟨0, 18, 7, 6⟩, ⟨0, 18, 6, 8⟩]
  exact AllWinning.cons node_13981 (AllWinning.cons node_13015 (AllWinning.cons node_11991 (AllWinning.cons node_11011 (AllWinning.cons node_13985 (AllWinning.cons node_13023 (AllWinning.cons node_12001 (AllWinning.cons node_11025 (AllWinning.nil))))))))

theorem node_14956 : Outcome ⟨0, 18, 10, 6⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 10⟩) (by decide) node_9925

theorem node_14957 : Outcome ⟨0, 18, 10, 12⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 16⟩) (by decide) node_6987

theorem node_14958 : Outcome ⟨0, 18, 10, 16⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 16⟩) (by decide) node_6987

theorem node_14959 : Outcome ⟨0, 19, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 9, 4⟩) (by decide) node_13018

theorem node_14960 : Outcome ⟨0, 19, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 19, 6, 6⟩) (by decide) node_12005

theorem node_14961 : Outcome ⟨0, 19, 9, 20⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 20⟩) (by decide) node_5353

theorem node_14962 : Outcome ⟨0, 20, 8, 8⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 2⟩) (by decide) node_13990

theorem node_14963 : Outcome ⟨0, 20, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 24⟩) (by decide) node_3969

theorem node_14964 : Outcome ⟨1, 7, 20, 6⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 2⟩) (by decide) node_13944

theorem node_14965 : Outcome ⟨1, 7, 20, 14⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 18⟩) (by decide) node_6145

theorem node_14966 : Outcome ⟨1, 8, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 2⟩) (by decide) node_14001

theorem node_14967 : Outcome ⟨1, 8, 19, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 14⟩) (by decide) node_8011

theorem node_14968 : Outcome ⟨1, 8, 19, 20⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 14⟩) (by decide) node_8011

theorem node_14969 : Outcome ⟨1, 9, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 2⟩) (by decide) node_14001

theorem node_14970 : Outcome ⟨1, 9, 18, 10⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 2⟩) (by decide) node_14001

theorem node_14971 : Outcome ⟨1, 9, 18, 20⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 26⟩) (by decide) node_3447

theorem node_14972 : Outcome ⟨1, 10, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 17, 2⟩, ⟨1, 9, 17, 2⟩, ⟨1, 8, 17, 4⟩, ⟨1, 10, 16, 2⟩, ⟨1, 10, 15, 4⟩]
  exact AllWinning.cons node_13955 (AllWinning.cons node_14006 (AllWinning.cons node_13038 (AllWinning.cons node_14010 (AllWinning.cons node_13045 (AllWinning.nil)))))

theorem node_14973 : Outcome ⟨1, 10, 17, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 6⟩) (by decide) node_12034

theorem node_14974 : Outcome ⟨1, 10, 17, 18⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 6⟩) (by decide) node_12034

theorem node_14975 : Outcome ⟨1, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 16, 2⟩) (by decide) node_13959

theorem node_14976 : Outcome ⟨1, 11, 16, 8⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 10⟩) (by decide) node_9955

theorem node_14977 : Outcome ⟨1, 11, 16, 12⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 18⟩) (by decide) node_6170

theorem node_14978 : Outcome ⟨1, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 2⟩) (by decide) node_14014

theorem node_14979 : Outcome ⟨1, 12, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 2⟩) (by decide) node_14014

theorem node_14980 : Outcome ⟨1, 12, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 14⟩) (by decide) node_8032

theorem node_14981 : Outcome ⟨1, 12, 15, 12⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 14⟩) (by decide) node_8032

theorem node_14982 : Outcome ⟨1, 13, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 14, 2⟩, ⟨1, 12, 14, 2⟩, ⟨1, 11, 14, 4⟩, ⟨1, 13, 13, 2⟩, ⟨1, 13, 12, 4⟩]
  exact AllWinning.cons node_13967 (AllWinning.cons node_14018 (AllWinning.cons node_13048 (AllWinning.cons node_14022 (AllWinning.cons node_13055 (AllWinning.nil)))))

theorem node_14983 : Outcome ⟨1, 13, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 6⟩) (by decide) node_12034

theorem node_14984 : Outcome ⟨1, 13, 14, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 6⟩) (by decide) node_12034

theorem node_14985 : Outcome ⟨1, 13, 14, 10⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 6⟩) (by decide) node_12034

theorem node_14986 : Outcome ⟨1, 14, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 13, 2⟩, ⟨1, 13, 13, 2⟩, ⟨1, 12, 13, 4⟩, ⟨1, 14, 12, 2⟩, ⟨1, 14, 11, 4⟩]
  exact AllWinning.cons node_13970 (AllWinning.cons node_14022 (AllWinning.cons node_13050 (AllWinning.cons node_14026 (AllWinning.cons node_13060 (AllWinning.nil)))))

theorem node_14987 : Outcome ⟨1, 14, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 6⟩) (by decide) node_12054

theorem node_14988 : Outcome ⟨1, 14, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 6⟩) (by decide) node_12054

theorem node_14989 : Outcome ⟨1, 14, 13, 10⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 6⟩) (by decide) node_12054

theorem node_14990 : Outcome ⟨1, 15, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 2⟩) (by decide) node_14030

theorem node_14991 : Outcome ⟨1, 15, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 2⟩) (by decide) node_14030

theorem node_14992 : Outcome ⟨1, 15, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 14⟩) (by decide) node_8011

theorem node_14993 : Outcome ⟨1, 15, 12, 12⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 14⟩) (by decide) node_8011

theorem node_14994 : Outcome ⟨1, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 11, 2⟩) (by decide) node_13976

theorem node_14995 : Outcome ⟨1, 16, 11, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 10⟩) (by decide) node_10001

theorem node_14996 : Outcome ⟨1, 16, 11, 12⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 18⟩) (by decide) node_6145

theorem node_14997 : Outcome ⟨1, 17, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 10, 2⟩, ⟨1, 16, 10, 2⟩, ⟨1, 15, 10, 4⟩, ⟨1, 17, 9, 2⟩, ⟨1, 17, 8, 4⟩]
  exact AllWinning.cons node_13981 (AllWinning.cons node_14034 (AllWinning.cons node_13062 (AllWinning.cons node_14038 (AllWinning.cons node_13068 (AllWinning.nil)))))

theorem node_14998 : Outcome ⟨1, 17, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 6⟩) (by decide) node_12054

theorem node_14999 : Outcome ⟨1, 17, 10, 18⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 6⟩) (by decide) node_12054

theorem node_15000 : Outcome ⟨1, 18, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 2⟩) (by decide) node_14042

theorem node_15001 : Outcome ⟨1, 18, 9, 10⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 2⟩) (by decide) node_14042

theorem node_15002 : Outcome ⟨1, 18, 9, 20⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 26⟩) (by decide) node_3423

theorem node_15003 : Outcome ⟨1, 19, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 2⟩) (by decide) node_14042

theorem node_15004 : Outcome ⟨1, 19, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 14⟩) (by decide) node_8032

theorem node_15005 : Outcome ⟨1, 19, 8, 20⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 14⟩) (by decide) node_8032

theorem node_15006 : Outcome ⟨1, 20, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 2⟩) (by decide) node_13990

theorem node_15007 : Outcome ⟨1, 20, 7, 14⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 18⟩) (by decide) node_6170

theorem node_15008 : Outcome ⟨2, 6, 20, 6⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 6⟩) (by decide) node_12084

theorem node_15009 : Outcome ⟨2, 6, 20, 8⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 6⟩) (by decide) node_12084

theorem node_15010 : Outcome ⟨2, 7, 19, 2⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 2⟩) (by decide) node_14056

theorem node_15011 : Outcome ⟨2, 7, 19, 8⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 2⟩) (by decide) node_14056

theorem node_15012 : Outcome ⟨2, 8, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 2⟩) (by decide) node_14001

theorem node_15013 : Outcome ⟨2, 8, 18, 12⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 2⟩) (by decide) node_14001

theorem node_15014 : Outcome ⟨2, 8, 18, 16⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 2⟩) (by decide) node_14001

theorem node_15015 : Outcome ⟨2, 9, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 17, 4⟩) (by decide) node_12989

theorem node_15016 : Outcome ⟨2, 9, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 17, 4⟩) (by decide) node_12989

theorem node_15017 : Outcome ⟨2, 9, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 17, 4⟩) (by decide) node_12989

theorem node_15018 : Outcome ⟨2, 9, 17, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 17, 4⟩) (by decide) node_12989

theorem node_15019 : Outcome ⟨2, 10, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 16, 2⟩, ⟨0, 10, 16, 4⟩, ⟨2, 9, 16, 2⟩, ⟨2, 8, 16, 4⟩, ⟨2, 7, 16, 6⟩, ⟨2, 6, 16, 8⟩, ⟨2, 10, 15, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 10, 13, 6⟩, ⟨2, 10, 12, 8⟩]
  exact AllWinning.cons node_14010 (AllWinning.cons node_12994 (AllWinning.cons node_14066 (AllWinning.cons node_13088 (AllWinning.cons node_12102 (AllWinning.cons node_11103 (AllWinning.cons node_14070 (AllWinning.cons node_13098 (AllWinning.cons node_12112 (AllWinning.cons node_11116 (AllWinning.nil))))))))))

theorem node_15020 : Outcome ⟨2, 10, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 16, 2⟩, ⟨0, 10, 16, 4⟩, ⟨2, 9, 16, 2⟩, ⟨2, 8, 16, 4⟩, ⟨2, 7, 16, 6⟩, ⟨2, 6, 16, 8⟩, ⟨2, 5, 16, 10⟩, ⟨2, 4, 16, 12⟩, ⟨2, 10, 15, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 10, 13, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 10, 11, 10⟩, ⟨2, 10, 10, 12⟩]
  exact AllWinning.cons node_14010 (AllWinning.cons node_12994 (AllWinning.cons node_14066 (AllWinning.cons node_13088 (AllWinning.cons node_12102 (AllWinning.cons node_11103 (AllWinning.cons node_10036 (AllWinning.cons node_9062 (AllWinning.cons node_14070 (AllWinning.cons node_13098 (AllWinning.cons node_12112 (AllWinning.cons node_11116 (AllWinning.cons node_10052 (AllWinning.cons node_9086 (AllWinning.nil))))))))))))))

theorem node_15021 : Outcome ⟨2, 10, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 16, 2⟩, ⟨0, 10, 16, 4⟩, ⟨2, 9, 16, 2⟩, ⟨2, 8, 16, 4⟩, ⟨2, 7, 16, 6⟩, ⟨2, 6, 16, 8⟩, ⟨2, 5, 16, 10⟩, ⟨2, 4, 16, 12⟩, ⟨2, 3, 16, 14⟩, ⟨2, 2, 16, 16⟩, ⟨2, 10, 15, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 10, 13, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 10, 11, 10⟩, ⟨2, 10, 10, 12⟩, ⟨2, 10, 9, 14⟩, ⟨2, 10, 8, 16⟩]
  exact AllWinning.cons node_14010 (AllWinning.cons node_12994 (AllWinning.cons node_14066 (AllWinning.cons node_13088 (AllWinning.cons node_12102 (AllWinning.cons node_11103 (AllWinning.cons node_10036 (AllWinning.cons node_9062 (AllWinning.cons node_8079 (AllWinning.cons node_7124 (AllWinning.cons node_14070 (AllWinning.cons node_13098 (AllWinning.cons node_12112 (AllWinning.cons node_11116 (AllWinning.cons node_10052 (AllWinning.cons node_9086 (AllWinning.cons node_8110 (AllWinning.cons node_7160 (AllWinning.nil))))))))))))))))))

theorem node_15022 : Outcome ⟨2, 10, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 16, 2⟩, ⟨0, 10, 16, 4⟩, ⟨2, 9, 16, 2⟩, ⟨2, 8, 16, 4⟩, ⟨2, 7, 16, 6⟩, ⟨2, 6, 16, 8⟩, ⟨2, 5, 16, 10⟩, ⟨2, 4, 16, 12⟩, ⟨2, 3, 16, 14⟩, ⟨2, 2, 16, 16⟩, ⟨2, 1, 16, 18⟩, ⟨2, 0, 16, 20⟩, ⟨2, 10, 15, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 10, 13, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 10, 11, 10⟩, ⟨2, 10, 10, 12⟩, ⟨2, 10, 9, 14⟩, ⟨2, 10, 8, 16⟩, ⟨2, 10, 7, 18⟩, ⟨2, 10, 6, 20⟩]
  exact AllWinning.cons node_14010 (AllWinning.cons node_12994 (AllWinning.cons node_14066 (AllWinning.cons node_13088 (AllWinning.cons node_12102 (AllWinning.cons node_11103 (AllWinning.cons node_10036 (AllWinning.cons node_9062 (AllWinning.cons node_8079 (AllWinning.cons node_7124 (AllWinning.cons node_6201 (AllWinning.cons node_5458 (AllWinning.cons node_14070 (AllWinning.cons node_13098 (AllWinning.cons node_12112 (AllWinning.cons node_11116 (AllWinning.cons node_10052 (AllWinning.cons node_9086 (AllWinning.cons node_8110 (AllWinning.cons node_7160 (AllWinning.cons node_6240 (AllWinning.cons node_5496 (AllWinning.nil))))))))))))))))))))))

theorem node_15023 : Outcome ⟨2, 10, 16, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 22⟩) (by decide) node_4782

theorem node_15024 : Outcome ⟨2, 11, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 4⟩) (by decide) node_13091

theorem node_15025 : Outcome ⟨2, 11, 15, 8⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 4⟩) (by decide) node_13091

theorem node_15026 : Outcome ⟨2, 12, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.nil))))))

theorem node_15027 : Outcome ⟨2, 12, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 12, 11, 6⟩, ⟨2, 12, 10, 8⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_12110 (AllWinning.cons node_11110 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.cons node_12118 (AllWinning.cons node_11124 (AllWinning.nil))))))))))

theorem node_15028 : Outcome ⟨2, 12, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨2, 7, 14, 10⟩, ⟨2, 6, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨2, 4, 14, 16⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 12, 11, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 12, 9, 10⟩, ⟨2, 12, 8, 12⟩, ⟨2, 12, 7, 14⟩, ⟨2, 12, 6, 16⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_12110 (AllWinning.cons node_11110 (AllWinning.cons node_10043 (AllWinning.cons node_9071 (AllWinning.cons node_8085 (AllWinning.cons node_7135 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.cons node_12118 (AllWinning.cons node_11124 (AllWinning.cons node_10063 (AllWinning.cons node_9091 (AllWinning.cons node_8121 (AllWinning.cons node_7170 (AllWinning.nil))))))))))))))))))

theorem node_15029 : Outcome ⟨2, 12, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨2, 7, 14, 10⟩, ⟨2, 6, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨2, 4, 14, 16⟩, ⟨2, 3, 14, 18⟩, ⟨2, 2, 14, 20⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 12, 11, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 12, 9, 10⟩, ⟨2, 12, 8, 12⟩, ⟨2, 12, 7, 14⟩, ⟨2, 12, 6, 16⟩, ⟨2, 12, 5, 18⟩, ⟨2, 12, 4, 20⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_12110 (AllWinning.cons node_11110 (AllWinning.cons node_10043 (AllWinning.cons node_9071 (AllWinning.cons node_8085 (AllWinning.cons node_7135 (AllWinning.cons node_6209 (AllWinning.cons node_5466 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.cons node_12118 (AllWinning.cons node_11124 (AllWinning.cons node_10063 (AllWinning.cons node_9091 (AllWinning.cons node_8121 (AllWinning.cons node_7170 (AllWinning.cons node_6254 (AllWinning.cons node_5502 (AllWinning.nil))))))))))))))))))))))

theorem node_15030 : Outcome ⟨2, 12, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨2, 7, 14, 10⟩, ⟨2, 6, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨2, 4, 14, 16⟩, ⟨2, 3, 14, 18⟩, ⟨2, 2, 14, 20⟩, ⟨2, 1, 14, 22⟩, ⟨2, 0, 14, 24⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 12, 11, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 12, 9, 10⟩, ⟨2, 12, 8, 12⟩, ⟨2, 12, 7, 14⟩, ⟨2, 12, 6, 16⟩, ⟨2, 12, 5, 18⟩, ⟨2, 12, 4, 20⟩, ⟨2, 12, 3, 22⟩, ⟨2, 12, 2, 24⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_12110 (AllWinning.cons node_11110 (AllWinning.cons node_10043 (AllWinning.cons node_9071 (AllWinning.cons node_8085 (AllWinning.cons node_7135 (AllWinning.cons node_6209 (AllWinning.cons node_5466 (AllWinning.cons node_4729 (AllWinning.cons node_4054 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.cons node_12118 (AllWinning.cons node_11124 (AllWinning.cons node_10063 (AllWinning.cons node_9091 (AllWinning.cons node_8121 (AllWinning.cons node_7170 (AllWinning.cons node_6254 (AllWinning.cons node_5502 (AllWinning.cons node_4791 (AllWinning.cons node_4091 (AllWinning.nil))))))))))))))))))))))))))

theorem node_15031 : Outcome ⟨2, 12, 14, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨2, 7, 14, 10⟩, ⟨2, 6, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨2, 4, 14, 16⟩, ⟨2, 3, 14, 18⟩, ⟨2, 2, 14, 20⟩, ⟨2, 1, 14, 22⟩, ⟨2, 0, 14, 24⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 12, 11, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 12, 9, 10⟩, ⟨2, 12, 8, 12⟩, ⟨2, 12, 7, 14⟩, ⟨2, 12, 6, 16⟩, ⟨2, 12, 5, 18⟩, ⟨2, 12, 4, 20⟩, ⟨2, 12, 3, 22⟩, ⟨2, 12, 2, 24⟩, ⟨2, 12, 1, 26⟩, ⟨2, 12, 0, 28⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_12110 (AllWinning.cons node_11110 (AllWinning.cons node_10043 (AllWinning.cons node_9071 (AllWinning.cons node_8085 (AllWinning.cons node_7135 (AllWinning.cons node_6209 (AllWinning.cons node_5466 (AllWinning.cons node_4729 (AllWinning.cons node_4054 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.cons node_12118 (AllWinning.cons node_11124 (AllWinning.cons node_10063 (AllWinning.cons node_9091 (AllWinning.cons node_8121 (AllWinning.cons node_7170 (AllWinning.cons node_6254 (AllWinning.cons node_5502 (AllWinning.cons node_4791 (AllWinning.cons node_4091 (AllWinning.cons node_3532 (AllWinning.cons node_2990 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15032 : Outcome ⟨2, 12, 14, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨2, 7, 14, 10⟩, ⟨2, 6, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨2, 4, 14, 16⟩, ⟨2, 3, 14, 18⟩, ⟨2, 2, 14, 20⟩, ⟨2, 1, 14, 22⟩, ⟨2, 0, 14, 24⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 12, 11, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 12, 9, 10⟩, ⟨2, 12, 8, 12⟩, ⟨2, 12, 7, 14⟩, ⟨2, 12, 6, 16⟩, ⟨2, 12, 5, 18⟩, ⟨2, 12, 4, 20⟩, ⟨2, 12, 3, 22⟩, ⟨2, 12, 2, 24⟩, ⟨2, 12, 1, 26⟩, ⟨2, 12, 0, 28⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_12110 (AllWinning.cons node_11110 (AllWinning.cons node_10043 (AllWinning.cons node_9071 (AllWinning.cons node_8085 (AllWinning.cons node_7135 (AllWinning.cons node_6209 (AllWinning.cons node_5466 (AllWinning.cons node_4729 (AllWinning.cons node_4054 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.cons node_12118 (AllWinning.cons node_11124 (AllWinning.cons node_10063 (AllWinning.cons node_9091 (AllWinning.cons node_8121 (AllWinning.cons node_7170 (AllWinning.cons node_6254 (AllWinning.cons node_5502 (AllWinning.cons node_4791 (AllWinning.cons node_4091 (AllWinning.cons node_3532 (AllWinning.cons node_2990 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15033 : Outcome ⟨2, 12, 14, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 14, 2⟩, ⟨0, 12, 14, 4⟩, ⟨2, 11, 14, 2⟩, ⟨2, 10, 14, 4⟩, ⟨2, 9, 14, 6⟩, ⟨2, 8, 14, 8⟩, ⟨2, 7, 14, 10⟩, ⟨2, 6, 14, 12⟩, ⟨2, 5, 14, 14⟩, ⟨2, 4, 14, 16⟩, ⟨2, 3, 14, 18⟩, ⟨2, 2, 14, 20⟩, ⟨2, 1, 14, 22⟩, ⟨2, 0, 14, 24⟩, ⟨2, 12, 13, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 12, 11, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 12, 9, 10⟩, ⟨2, 12, 8, 12⟩, ⟨2, 12, 7, 14⟩, ⟨2, 12, 6, 16⟩, ⟨2, 12, 5, 18⟩, ⟨2, 12, 4, 20⟩, ⟨2, 12, 3, 22⟩, ⟨2, 12, 2, 24⟩, ⟨2, 12, 1, 26⟩, ⟨2, 12, 0, 28⟩]
  exact AllWinning.cons node_14018 (AllWinning.cons node_12999 (AllWinning.cons node_14071 (AllWinning.cons node_13098 (AllWinning.cons node_12110 (AllWinning.cons node_11110 (AllWinning.cons node_10043 (AllWinning.cons node_9071 (AllWinning.cons node_8085 (AllWinning.cons node_7135 (AllWinning.cons node_6209 (AllWinning.cons node_5466 (AllWinning.cons node_4729 (AllWinning.cons node_4054 (AllWinning.cons node_14073 (AllWinning.cons node_13104 (AllWinning.cons node_12118 (AllWinning.cons node_11124 (AllWinning.cons node_10063 (AllWinning.cons node_9091 (AllWinning.cons node_8121 (AllWinning.cons node_7170 (AllWinning.cons node_6254 (AllWinning.cons node_5502 (AllWinning.cons node_4791 (AllWinning.cons node_4091 (AllWinning.cons node_3532 (AllWinning.cons node_2990 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15034 : Outcome ⟨2, 13, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_15035 : Outcome ⟨2, 13, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_15036 : Outcome ⟨2, 13, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_15037 : Outcome ⟨2, 13, 13, 12⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_15038 : Outcome ⟨2, 13, 13, 22⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 4⟩) (by decide) node_13002

theorem node_15039 : Outcome ⟨2, 14, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.nil))))))

theorem node_15040 : Outcome ⟨2, 14, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 11, 12, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 14, 9, 6⟩, ⟨2, 14, 8, 8⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_12114 (AllWinning.cons node_11116 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.cons node_12124 (AllWinning.cons node_11127 (AllWinning.nil))))))))))

theorem node_15041 : Outcome ⟨2, 14, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 11, 12, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 9, 12, 10⟩, ⟨2, 8, 12, 12⟩, ⟨2, 7, 12, 14⟩, ⟨2, 6, 12, 16⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 14, 9, 6⟩, ⟨2, 14, 8, 8⟩, ⟨2, 14, 7, 10⟩, ⟨2, 14, 6, 12⟩, ⟨2, 14, 5, 14⟩, ⟨2, 14, 4, 16⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_12114 (AllWinning.cons node_11116 (AllWinning.cons node_10048 (AllWinning.cons node_9078 (AllWinning.cons node_8095 (AllWinning.cons node_7142 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.cons node_12124 (AllWinning.cons node_11127 (AllWinning.cons node_10068 (AllWinning.cons node_9099 (AllWinning.cons node_8127 (AllWinning.cons node_7181 (AllWinning.nil))))))))))))))))))

theorem node_15042 : Outcome ⟨2, 14, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 11, 12, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 9, 12, 10⟩, ⟨2, 8, 12, 12⟩, ⟨2, 7, 12, 14⟩, ⟨2, 6, 12, 16⟩, ⟨2, 5, 12, 18⟩, ⟨2, 4, 12, 20⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 14, 9, 6⟩, ⟨2, 14, 8, 8⟩, ⟨2, 14, 7, 10⟩, ⟨2, 14, 6, 12⟩, ⟨2, 14, 5, 14⟩, ⟨2, 14, 4, 16⟩, ⟨2, 14, 3, 18⟩, ⟨2, 14, 2, 20⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_12114 (AllWinning.cons node_11116 (AllWinning.cons node_10048 (AllWinning.cons node_9078 (AllWinning.cons node_8095 (AllWinning.cons node_7142 (AllWinning.cons node_6216 (AllWinning.cons node_5473 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.cons node_12124 (AllWinning.cons node_11127 (AllWinning.cons node_10068 (AllWinning.cons node_9099 (AllWinning.cons node_8127 (AllWinning.cons node_7181 (AllWinning.cons node_6261 (AllWinning.cons node_5509 (AllWinning.nil))))))))))))))))))))))

theorem node_15043 : Outcome ⟨2, 14, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 11, 12, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 9, 12, 10⟩, ⟨2, 8, 12, 12⟩, ⟨2, 7, 12, 14⟩, ⟨2, 6, 12, 16⟩, ⟨2, 5, 12, 18⟩, ⟨2, 4, 12, 20⟩, ⟨2, 3, 12, 22⟩, ⟨2, 2, 12, 24⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 14, 9, 6⟩, ⟨2, 14, 8, 8⟩, ⟨2, 14, 7, 10⟩, ⟨2, 14, 6, 12⟩, ⟨2, 14, 5, 14⟩, ⟨2, 14, 4, 16⟩, ⟨2, 14, 3, 18⟩, ⟨2, 14, 2, 20⟩, ⟨2, 14, 1, 22⟩, ⟨2, 14, 0, 24⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_12114 (AllWinning.cons node_11116 (AllWinning.cons node_10048 (AllWinning.cons node_9078 (AllWinning.cons node_8095 (AllWinning.cons node_7142 (AllWinning.cons node_6216 (AllWinning.cons node_5473 (AllWinning.cons node_4740 (AllWinning.cons node_4060 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.cons node_12124 (AllWinning.cons node_11127 (AllWinning.cons node_10068 (AllWinning.cons node_9099 (AllWinning.cons node_8127 (AllWinning.cons node_7181 (AllWinning.cons node_6261 (AllWinning.cons node_5509 (AllWinning.cons node_4801 (AllWinning.cons node_4097 (AllWinning.nil))))))))))))))))))))))))))

theorem node_15044 : Outcome ⟨2, 14, 12, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 11, 12, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 9, 12, 10⟩, ⟨2, 8, 12, 12⟩, ⟨2, 7, 12, 14⟩, ⟨2, 6, 12, 16⟩, ⟨2, 5, 12, 18⟩, ⟨2, 4, 12, 20⟩, ⟨2, 3, 12, 22⟩, ⟨2, 2, 12, 24⟩, ⟨2, 1, 12, 26⟩, ⟨2, 0, 12, 28⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 14, 9, 6⟩, ⟨2, 14, 8, 8⟩, ⟨2, 14, 7, 10⟩, ⟨2, 14, 6, 12⟩, ⟨2, 14, 5, 14⟩, ⟨2, 14, 4, 16⟩, ⟨2, 14, 3, 18⟩, ⟨2, 14, 2, 20⟩, ⟨2, 14, 1, 22⟩, ⟨2, 14, 0, 24⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_12114 (AllWinning.cons node_11116 (AllWinning.cons node_10048 (AllWinning.cons node_9078 (AllWinning.cons node_8095 (AllWinning.cons node_7142 (AllWinning.cons node_6216 (AllWinning.cons node_5473 (AllWinning.cons node_4740 (AllWinning.cons node_4060 (AllWinning.cons node_3486 (AllWinning.cons node_2943 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.cons node_12124 (AllWinning.cons node_11127 (AllWinning.cons node_10068 (AllWinning.cons node_9099 (AllWinning.cons node_8127 (AllWinning.cons node_7181 (AllWinning.cons node_6261 (AllWinning.cons node_5509 (AllWinning.cons node_4801 (AllWinning.cons node_4097 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15045 : Outcome ⟨2, 14, 12, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 11, 12, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 9, 12, 10⟩, ⟨2, 8, 12, 12⟩, ⟨2, 7, 12, 14⟩, ⟨2, 6, 12, 16⟩, ⟨2, 5, 12, 18⟩, ⟨2, 4, 12, 20⟩, ⟨2, 3, 12, 22⟩, ⟨2, 2, 12, 24⟩, ⟨2, 1, 12, 26⟩, ⟨2, 0, 12, 28⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 14, 9, 6⟩, ⟨2, 14, 8, 8⟩, ⟨2, 14, 7, 10⟩, ⟨2, 14, 6, 12⟩, ⟨2, 14, 5, 14⟩, ⟨2, 14, 4, 16⟩, ⟨2, 14, 3, 18⟩, ⟨2, 14, 2, 20⟩, ⟨2, 14, 1, 22⟩, ⟨2, 14, 0, 24⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_12114 (AllWinning.cons node_11116 (AllWinning.cons node_10048 (AllWinning.cons node_9078 (AllWinning.cons node_8095 (AllWinning.cons node_7142 (AllWinning.cons node_6216 (AllWinning.cons node_5473 (AllWinning.cons node_4740 (AllWinning.cons node_4060 (AllWinning.cons node_3486 (AllWinning.cons node_2943 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.cons node_12124 (AllWinning.cons node_11127 (AllWinning.cons node_10068 (AllWinning.cons node_9099 (AllWinning.cons node_8127 (AllWinning.cons node_7181 (AllWinning.cons node_6261 (AllWinning.cons node_5509 (AllWinning.cons node_4801 (AllWinning.cons node_4097 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15046 : Outcome ⟨2, 14, 12, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 12, 2⟩, ⟨0, 14, 12, 4⟩, ⟨2, 13, 12, 2⟩, ⟨2, 12, 12, 4⟩, ⟨2, 11, 12, 6⟩, ⟨2, 10, 12, 8⟩, ⟨2, 9, 12, 10⟩, ⟨2, 8, 12, 12⟩, ⟨2, 7, 12, 14⟩, ⟨2, 6, 12, 16⟩, ⟨2, 5, 12, 18⟩, ⟨2, 4, 12, 20⟩, ⟨2, 3, 12, 22⟩, ⟨2, 2, 12, 24⟩, ⟨2, 1, 12, 26⟩, ⟨2, 0, 12, 28⟩, ⟨2, 14, 11, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 14, 9, 6⟩, ⟨2, 14, 8, 8⟩, ⟨2, 14, 7, 10⟩, ⟨2, 14, 6, 12⟩, ⟨2, 14, 5, 14⟩, ⟨2, 14, 4, 16⟩, ⟨2, 14, 3, 18⟩, ⟨2, 14, 2, 20⟩, ⟨2, 14, 1, 22⟩, ⟨2, 14, 0, 24⟩]
  exact AllWinning.cons node_14026 (AllWinning.cons node_13009 (AllWinning.cons node_14075 (AllWinning.cons node_13104 (AllWinning.cons node_12114 (AllWinning.cons node_11116 (AllWinning.cons node_10048 (AllWinning.cons node_9078 (AllWinning.cons node_8095 (AllWinning.cons node_7142 (AllWinning.cons node_6216 (AllWinning.cons node_5473 (AllWinning.cons node_4740 (AllWinning.cons node_4060 (AllWinning.cons node_3486 (AllWinning.cons node_2943 (AllWinning.cons node_14077 (AllWinning.cons node_13109 (AllWinning.cons node_12124 (AllWinning.cons node_11127 (AllWinning.cons node_10068 (AllWinning.cons node_9099 (AllWinning.cons node_8127 (AllWinning.cons node_7181 (AllWinning.cons node_6261 (AllWinning.cons node_5509 (AllWinning.cons node_4801 (AllWinning.cons node_4097 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_15047 : Outcome ⟨2, 15, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 4⟩) (by decide) node_13106

theorem node_15048 : Outcome ⟨2, 15, 11, 8⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 4⟩) (by decide) node_13106

theorem node_15049 : Outcome ⟨2, 16, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 16, 10, 2⟩, ⟨0, 16, 10, 4⟩, ⟨2, 15, 10, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 13, 10, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 16, 9, 2⟩, ⟨2, 16, 8, 4⟩, ⟨2, 16, 7, 6⟩, ⟨2, 16, 6, 8⟩]
  exact AllWinning.cons node_14034 (AllWinning.cons node_13015 (AllWinning.cons node_14079 (AllWinning.cons node_13109 (AllWinning.cons node_12122 (AllWinning.cons node_11124 (AllWinning.cons node_14080 (AllWinning.cons node_13118 (AllWinning.cons node_12129 (AllWinning.cons node_11134 (AllWinning.nil))))))))))

theorem node_15050 : Outcome ⟨2, 16, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 16, 10, 2⟩, ⟨0, 16, 10, 4⟩, ⟨2, 15, 10, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 13, 10, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 11, 10, 10⟩, ⟨2, 10, 10, 12⟩, ⟨2, 16, 9, 2⟩, ⟨2, 16, 8, 4⟩, ⟨2, 16, 7, 6⟩, ⟨2, 16, 6, 8⟩, ⟨2, 16, 5, 10⟩, ⟨2, 16, 4, 12⟩]
  exact AllWinning.cons node_14034 (AllWinning.cons node_13015 (AllWinning.cons node_14079 (AllWinning.cons node_13109 (AllWinning.cons node_12122 (AllWinning.cons node_11124 (AllWinning.cons node_10058 (AllWinning.cons node_9086 (AllWinning.cons node_14080 (AllWinning.cons node_13118 (AllWinning.cons node_12129 (AllWinning.cons node_11134 (AllWinning.cons node_10073 (AllWinning.cons node_9107 (AllWinning.nil))))))))))))))

theorem node_15051 : Outcome ⟨2, 16, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 16, 10, 2⟩, ⟨0, 16, 10, 4⟩, ⟨2, 15, 10, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 13, 10, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 11, 10, 10⟩, ⟨2, 10, 10, 12⟩, ⟨2, 9, 10, 14⟩, ⟨2, 8, 10, 16⟩, ⟨2, 16, 9, 2⟩, ⟨2, 16, 8, 4⟩, ⟨2, 16, 7, 6⟩, ⟨2, 16, 6, 8⟩, ⟨2, 16, 5, 10⟩, ⟨2, 16, 4, 12⟩, ⟨2, 16, 3, 14⟩, ⟨2, 16, 2, 16⟩]
  exact AllWinning.cons node_14034 (AllWinning.cons node_13015 (AllWinning.cons node_14079 (AllWinning.cons node_13109 (AllWinning.cons node_12122 (AllWinning.cons node_11124 (AllWinning.cons node_10058 (AllWinning.cons node_9086 (AllWinning.cons node_8105 (AllWinning.cons node_7152 (AllWinning.cons node_14080 (AllWinning.cons node_13118 (AllWinning.cons node_12129 (AllWinning.cons node_11134 (AllWinning.cons node_10073 (AllWinning.cons node_9107 (AllWinning.cons node_8135 (AllWinning.cons node_7187 (AllWinning.nil))))))))))))))))))

theorem node_15052 : Outcome ⟨2, 16, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 16, 10, 2⟩, ⟨0, 16, 10, 4⟩, ⟨2, 15, 10, 2⟩, ⟨2, 14, 10, 4⟩, ⟨2, 13, 10, 6⟩, ⟨2, 12, 10, 8⟩, ⟨2, 11, 10, 10⟩, ⟨2, 10, 10, 12⟩, ⟨2, 9, 10, 14⟩, ⟨2, 8, 10, 16⟩, ⟨2, 7, 10, 18⟩, ⟨2, 6, 10, 20⟩, ⟨2, 16, 9, 2⟩, ⟨2, 16, 8, 4⟩, ⟨2, 16, 7, 6⟩, ⟨2, 16, 6, 8⟩, ⟨2, 16, 5, 10⟩, ⟨2, 16, 4, 12⟩, ⟨2, 16, 3, 14⟩, ⟨2, 16, 2, 16⟩, ⟨2, 16, 1, 18⟩, ⟨2, 16, 0, 20⟩]
  exact AllWinning.cons node_14034 (AllWinning.cons node_13015 (AllWinning.cons node_14079 (AllWinning.cons node_13109 (AllWinning.cons node_12122 (AllWinning.cons node_11124 (AllWinning.cons node_10058 (AllWinning.cons node_9086 (AllWinning.cons node_8105 (AllWinning.cons node_7152 (AllWinning.cons node_6230 (AllWinning.cons node_5479 (AllWinning.cons node_14080 (AllWinning.cons node_13118 (AllWinning.cons node_12129 (AllWinning.cons node_11134 (AllWinning.cons node_10073 (AllWinning.cons node_9107 (AllWinning.cons node_8135 (AllWinning.cons node_7187 (AllWinning.cons node_6267 (AllWinning.cons node_5516 (AllWinning.nil))))))))))))))))))))))

theorem node_15053 : Outcome ⟨2, 16, 10, 16⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 22⟩) (by decide) node_4753

theorem node_15054 : Outcome ⟨2, 17, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 9, 4⟩) (by decide) node_13018

theorem node_15055 : Outcome ⟨2, 17, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 17, 9, 4⟩) (by decide) node_13018

theorem node_15056 : Outcome ⟨2, 17, 9, 6⟩ true :=
  Outcome.win (q := ⟨0, 17, 9, 4⟩) (by decide) node_13018

theorem node_15057 : Outcome ⟨2, 17, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 17, 9, 4⟩) (by decide) node_13018

theorem node_15058 : Outcome ⟨2, 18, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 2⟩) (by decide) node_14042

theorem node_15059 : Outcome ⟨2, 18, 8, 12⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 2⟩) (by decide) node_14042

end RQ9F1
