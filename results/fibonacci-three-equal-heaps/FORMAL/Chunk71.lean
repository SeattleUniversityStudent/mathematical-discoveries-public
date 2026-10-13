import Chunk70
set_option autoImplicit false
namespace RQ9F1

theorem node_15955 : Outcome ⟨1, 12, 16, 6⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 12⟩) (by decide) node_9956

theorem node_15956 : Outcome ⟨1, 12, 16, 10⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 16⟩) (by decide) node_8033

theorem node_15957 : Outcome ⟨1, 13, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 4⟩) (by decide) node_14015

theorem node_15958 : Outcome ⟨1, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 4⟩) (by decide) node_14015

theorem node_15959 : Outcome ⟨1, 13, 15, 6⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 4⟩) (by decide) node_14015

theorem node_15960 : Outcome ⟨1, 14, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 2⟩) (by decide) node_14937

theorem node_15961 : Outcome ⟨1, 14, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 8⟩) (by decide) node_12035

theorem node_15962 : Outcome ⟨1, 14, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 8⟩) (by decide) node_12035

theorem node_15963 : Outcome ⟨1, 14, 14, 16⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 8⟩) (by decide) node_12035

theorem node_15964 : Outcome ⟨1, 15, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 4⟩) (by decide) node_14031

theorem node_15965 : Outcome ⟨1, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 4⟩) (by decide) node_14031

theorem node_15966 : Outcome ⟨1, 15, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 4⟩) (by decide) node_14031

theorem node_15967 : Outcome ⟨1, 16, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 12, 2⟩, ⟨1, 15, 12, 2⟩, ⟨1, 14, 12, 4⟩, ⟨1, 16, 11, 2⟩, ⟨1, 16, 10, 4⟩]
  exact AllWinning.cons node_14948 (AllWinning.cons node_14990 (AllWinning.cons node_14027 (AllWinning.cons node_14994 (AllWinning.cons node_14035 (AllWinning.nil)))))

theorem node_15968 : Outcome ⟨1, 16, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 12, 2⟩, ⟨1, 15, 12, 2⟩, ⟨1, 14, 12, 4⟩, ⟨1, 13, 12, 6⟩, ⟨1, 12, 12, 8⟩, ⟨1, 16, 11, 2⟩, ⟨1, 16, 10, 4⟩, ⟨1, 16, 9, 6⟩, ⟨1, 16, 8, 8⟩]
  exact AllWinning.cons node_14948 (AllWinning.cons node_14990 (AllWinning.cons node_14027 (AllWinning.cons node_13056 (AllWinning.cons node_12047 (AllWinning.cons node_14994 (AllWinning.cons node_14035 (AllWinning.cons node_13065 (AllWinning.cons node_12068 (AllWinning.nil)))))))))

theorem node_15969 : Outcome ⟨1, 16, 12, 6⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 12⟩) (by decide) node_10002

theorem node_15970 : Outcome ⟨1, 16, 12, 10⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 16⟩) (by decide) node_8012

theorem node_15971 : Outcome ⟨1, 17, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 4⟩) (by decide) node_14031

theorem node_15972 : Outcome ⟨1, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 4⟩) (by decide) node_14031

theorem node_15973 : Outcome ⟨1, 18, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 8⟩) (by decide) node_12055

theorem node_15974 : Outcome ⟨1, 18, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 8⟩) (by decide) node_12055

theorem node_15975 : Outcome ⟨1, 18, 10, 10⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 8⟩) (by decide) node_12055

theorem node_15976 : Outcome ⟨1, 18, 10, 18⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 8⟩) (by decide) node_12055

theorem node_15977 : Outcome ⟨1, 19, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 9, 2⟩, ⟨1, 18, 9, 2⟩, ⟨1, 17, 9, 4⟩, ⟨1, 19, 8, 2⟩, ⟨1, 19, 7, 4⟩]
  exact AllWinning.cons node_14959 (AllWinning.cons node_15000 (AllWinning.cons node_14039 (AllWinning.cons node_15003 (AllWinning.cons node_14047 (AllWinning.nil)))))

theorem node_15978 : Outcome ⟨1, 19, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 9, 2⟩, ⟨1, 18, 9, 2⟩, ⟨1, 17, 9, 4⟩, ⟨1, 16, 9, 6⟩, ⟨1, 15, 9, 8⟩, ⟨1, 19, 8, 2⟩, ⟨1, 19, 7, 4⟩, ⟨1, 19, 6, 6⟩, ⟨1, 19, 5, 8⟩]
  exact AllWinning.cons node_14959 (AllWinning.cons node_15000 (AllWinning.cons node_14039 (AllWinning.cons node_13065 (AllWinning.cons node_12064 (AllWinning.cons node_15003 (AllWinning.cons node_14047 (AllWinning.cons node_13073 (AllWinning.cons node_12077 (AllWinning.nil)))))))))

theorem node_15979 : Outcome ⟨1, 19, 9, 6⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 12⟩) (by decide) node_10019

theorem node_15980 : Outcome ⟨1, 19, 9, 18⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 28⟩) (by decide) node_3424

theorem node_15981 : Outcome ⟨1, 20, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 4⟩) (by decide) node_14043

theorem node_15982 : Outcome ⟨1, 20, 8, 12⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 16⟩) (by decide) node_8033

theorem node_15983 : Outcome ⟨2, 7, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 8⟩) (by decide) node_12085

theorem node_15984 : Outcome ⟨2, 7, 20, 12⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 8⟩) (by decide) node_12085

theorem node_15985 : Outcome ⟨2, 8, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 19, 2⟩, ⟨0, 8, 19, 4⟩, ⟨2, 7, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨2, 8, 18, 2⟩, ⟨2, 8, 17, 4⟩]
  exact AllWinning.cons node_14966 (AllWinning.cons node_13950 (AllWinning.cons node_15010 (AllWinning.cons node_14054 (AllWinning.cons node_15012 (AllWinning.cons node_14064 (AllWinning.nil))))))

theorem node_15986 : Outcome ⟨2, 8, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 19, 2⟩, ⟨0, 8, 19, 4⟩, ⟨2, 7, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨2, 5, 19, 6⟩, ⟨2, 4, 19, 8⟩, ⟨2, 8, 18, 2⟩, ⟨2, 8, 17, 4⟩, ⟨2, 8, 16, 6⟩, ⟨2, 8, 15, 8⟩]
  exact AllWinning.cons node_14966 (AllWinning.cons node_13950 (AllWinning.cons node_15010 (AllWinning.cons node_14054 (AllWinning.cons node_13079 (AllWinning.cons node_12090 (AllWinning.cons node_15012 (AllWinning.cons node_14064 (AllWinning.cons node_13089 (AllWinning.cons node_12108 (AllWinning.nil))))))))))

theorem node_15987 : Outcome ⟨2, 8, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 19, 2⟩, ⟨0, 8, 19, 4⟩, ⟨2, 7, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨2, 5, 19, 6⟩, ⟨2, 4, 19, 8⟩, ⟨2, 3, 19, 10⟩, ⟨2, 2, 19, 12⟩, ⟨2, 8, 18, 2⟩, ⟨2, 8, 17, 4⟩, ⟨2, 8, 16, 6⟩, ⟨2, 8, 15, 8⟩, ⟨2, 8, 14, 10⟩, ⟨2, 8, 13, 12⟩]
  exact AllWinning.cons node_14966 (AllWinning.cons node_13950 (AllWinning.cons node_15010 (AllWinning.cons node_14054 (AllWinning.cons node_13079 (AllWinning.cons node_12090 (AllWinning.cons node_11091 (AllWinning.cons node_10025 (AllWinning.cons node_15012 (AllWinning.cons node_14064 (AllWinning.cons node_13089 (AllWinning.cons node_12108 (AllWinning.cons node_11111 (AllWinning.cons node_10045 (AllWinning.nil))))))))))))))

theorem node_15988 : Outcome ⟨2, 8, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 19, 2⟩, ⟨0, 8, 19, 4⟩, ⟨2, 7, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨2, 5, 19, 6⟩, ⟨2, 4, 19, 8⟩, ⟨2, 3, 19, 10⟩, ⟨2, 2, 19, 12⟩, ⟨2, 1, 19, 14⟩, ⟨2, 0, 19, 16⟩, ⟨2, 8, 18, 2⟩, ⟨2, 8, 17, 4⟩, ⟨2, 8, 16, 6⟩, ⟨2, 8, 15, 8⟩, ⟨2, 8, 14, 10⟩, ⟨2, 8, 13, 12⟩, ⟨2, 8, 12, 14⟩, ⟨2, 8, 11, 16⟩, ⟨2, 8, 10, 18⟩, ⟨2, 8, 9, 20⟩]
  exact AllWinning.cons node_14966 (AllWinning.cons node_13950 (AllWinning.cons node_15010 (AllWinning.cons node_14054 (AllWinning.cons node_13079 (AllWinning.cons node_12090 (AllWinning.cons node_11091 (AllWinning.cons node_10025 (AllWinning.cons node_9051 (AllWinning.cons node_8067 (AllWinning.cons node_15012 (AllWinning.cons node_14064 (AllWinning.cons node_13089 (AllWinning.cons node_12108 (AllWinning.cons node_11111 (AllWinning.cons node_10045 (AllWinning.cons node_9079 (AllWinning.cons node_8099 (AllWinning.cons node_7153 (AllWinning.cons node_6233 (AllWinning.nil))))))))))))))))))))

theorem node_15989 : Outcome ⟨2, 8, 19, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 19, 2⟩, ⟨0, 8, 19, 4⟩, ⟨2, 7, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨2, 5, 19, 6⟩, ⟨2, 4, 19, 8⟩, ⟨2, 3, 19, 10⟩, ⟨2, 2, 19, 12⟩, ⟨2, 1, 19, 14⟩, ⟨2, 0, 19, 16⟩, ⟨2, 8, 18, 2⟩, ⟨2, 8, 17, 4⟩, ⟨2, 8, 16, 6⟩, ⟨2, 8, 15, 8⟩, ⟨2, 8, 14, 10⟩, ⟨2, 8, 13, 12⟩, ⟨2, 8, 12, 14⟩, ⟨2, 8, 11, 16⟩, ⟨2, 8, 10, 18⟩, ⟨2, 8, 9, 20⟩, ⟨2, 8, 8, 22⟩, ⟨2, 8, 7, 24⟩]
  exact AllWinning.cons node_14966 (AllWinning.cons node_13950 (AllWinning.cons node_15010 (AllWinning.cons node_14054 (AllWinning.cons node_13079 (AllWinning.cons node_12090 (AllWinning.cons node_11091 (AllWinning.cons node_10025 (AllWinning.cons node_9051 (AllWinning.cons node_8067 (AllWinning.cons node_15012 (AllWinning.cons node_14064 (AllWinning.cons node_13089 (AllWinning.cons node_12108 (AllWinning.cons node_11111 (AllWinning.cons node_10045 (AllWinning.cons node_9079 (AllWinning.cons node_8099 (AllWinning.cons node_7153 (AllWinning.cons node_6233 (AllWinning.cons node_5488 (AllWinning.cons node_4768 (AllWinning.nil))))))))))))))))))))))

theorem node_15990 : Outcome ⟨2, 8, 19, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 19, 2⟩, ⟨0, 8, 19, 4⟩, ⟨2, 7, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨2, 5, 19, 6⟩, ⟨2, 4, 19, 8⟩, ⟨2, 3, 19, 10⟩, ⟨2, 2, 19, 12⟩, ⟨2, 1, 19, 14⟩, ⟨2, 0, 19, 16⟩, ⟨2, 8, 18, 2⟩, ⟨2, 8, 17, 4⟩, ⟨2, 8, 16, 6⟩, ⟨2, 8, 15, 8⟩, ⟨2, 8, 14, 10⟩, ⟨2, 8, 13, 12⟩, ⟨2, 8, 12, 14⟩, ⟨2, 8, 11, 16⟩, ⟨2, 8, 10, 18⟩, ⟨2, 8, 9, 20⟩, ⟨2, 8, 8, 22⟩, ⟨2, 8, 7, 24⟩, ⟨2, 8, 6, 26⟩, ⟨2, 8, 5, 28⟩]
  exact AllWinning.cons node_14966 (AllWinning.cons node_13950 (AllWinning.cons node_15010 (AllWinning.cons node_14054 (AllWinning.cons node_13079 (AllWinning.cons node_12090 (AllWinning.cons node_11091 (AllWinning.cons node_10025 (AllWinning.cons node_9051 (AllWinning.cons node_8067 (AllWinning.cons node_15012 (AllWinning.cons node_14064 (AllWinning.cons node_13089 (AllWinning.cons node_12108 (AllWinning.cons node_11111 (AllWinning.cons node_10045 (AllWinning.cons node_9079 (AllWinning.cons node_8099 (AllWinning.cons node_7153 (AllWinning.cons node_6233 (AllWinning.cons node_5488 (AllWinning.cons node_4768 (AllWinning.cons node_4080 (AllWinning.cons node_3514 (AllWinning.nil))))))))))))))))))))))))

theorem node_15991 : Outcome ⟨2, 8, 19, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 8, 19, 2⟩, ⟨0, 8, 19, 4⟩, ⟨2, 7, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨2, 5, 19, 6⟩, ⟨2, 4, 19, 8⟩, ⟨2, 3, 19, 10⟩, ⟨2, 2, 19, 12⟩, ⟨2, 1, 19, 14⟩, ⟨2, 0, 19, 16⟩, ⟨2, 8, 18, 2⟩, ⟨2, 8, 17, 4⟩, ⟨2, 8, 16, 6⟩, ⟨2, 8, 15, 8⟩, ⟨2, 8, 14, 10⟩, ⟨2, 8, 13, 12⟩, ⟨2, 8, 12, 14⟩, ⟨2, 8, 11, 16⟩, ⟨2, 8, 10, 18⟩, ⟨2, 8, 9, 20⟩, ⟨2, 8, 8, 22⟩, ⟨2, 8, 7, 24⟩, ⟨2, 8, 6, 26⟩, ⟨2, 8, 5, 28⟩, ⟨2, 8, 4, 30⟩, ⟨2, 8, 3, 32⟩, ⟨2, 8, 2, 34⟩, ⟨2, 8, 1, 36⟩, ⟨2, 8, 0, 38⟩]
  exact AllWinning.cons node_14966 (AllWinning.cons node_13950 (AllWinning.cons node_15010 (AllWinning.cons node_14054 (AllWinning.cons node_13079 (AllWinning.cons node_12090 (AllWinning.cons node_11091 (AllWinning.cons node_10025 (AllWinning.cons node_9051 (AllWinning.cons node_8067 (AllWinning.cons node_15012 (AllWinning.cons node_14064 (AllWinning.cons node_13089 (AllWinning.cons node_12108 (AllWinning.cons node_11111 (AllWinning.cons node_10045 (AllWinning.cons node_9079 (AllWinning.cons node_8099 (AllWinning.cons node_7153 (AllWinning.cons node_6233 (AllWinning.cons node_5488 (AllWinning.cons node_4768 (AllWinning.cons node_4080 (AllWinning.cons node_3514 (AllWinning.cons node_2974 (AllWinning.cons node_2517 (AllWinning.cons node_2044 (AllWinning.cons node_1670 (AllWinning.cons node_1314 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_15992 : Outcome ⟨2, 9, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 6⟩) (by decide) node_13092

theorem node_15993 : Outcome ⟨2, 9, 18, 14⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 6⟩) (by decide) node_13092

theorem node_15994 : Outcome ⟨2, 10, 17, 2⟩ true :=
  Outcome.win (q := ⟨1, 10, 17, 2⟩) (by decide) node_14972

theorem node_15995 : Outcome ⟨2, 10, 17, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 24⟩) (by decide) node_4783

theorem node_15996 : Outcome ⟨2, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 16, 4⟩) (by decide) node_13960

theorem node_15997 : Outcome ⟨2, 11, 16, 10⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 20⟩) (by decide) node_6249

theorem node_15998 : Outcome ⟨2, 11, 16, 14⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 20⟩) (by decide) node_6249

theorem node_15999 : Outcome ⟨2, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 2⟩) (by decide) node_15026

theorem node_16000 : Outcome ⟨2, 12, 15, 10⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 6⟩) (by decide) node_13092

theorem node_16001 : Outcome ⟨2, 13, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 14, 2⟩) (by decide) node_14982

theorem node_16002 : Outcome ⟨2, 13, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 13, 11, 6⟩) (by decide) node_13107

theorem node_16003 : Outcome ⟨2, 14, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 13, 2⟩) (by decide) node_14986

theorem node_16004 : Outcome ⟨2, 14, 13, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 13, 6⟩) (by decide) node_13101

theorem node_16005 : Outcome ⟨2, 15, 12, 2⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 2⟩) (by decide) node_15039

theorem node_16006 : Outcome ⟨2, 15, 12, 10⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 6⟩) (by decide) node_13111

theorem node_16007 : Outcome ⟨2, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 11, 4⟩) (by decide) node_13977

theorem node_16008 : Outcome ⟨2, 16, 11, 10⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 20⟩) (by decide) node_6225

theorem node_16009 : Outcome ⟨2, 16, 11, 14⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 20⟩) (by decide) node_6225

theorem node_16010 : Outcome ⟨2, 17, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 10, 2⟩) (by decide) node_14997

theorem node_16011 : Outcome ⟨2, 17, 10, 16⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 24⟩) (by decide) node_4754

theorem node_16012 : Outcome ⟨2, 18, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 6⟩) (by decide) node_13111

theorem node_16013 : Outcome ⟨2, 18, 9, 14⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 6⟩) (by decide) node_13111

theorem node_16014 : Outcome ⟨2, 19, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 8, 2⟩, ⟨0, 19, 8, 4⟩, ⟨2, 18, 8, 2⟩, ⟨2, 17, 8, 4⟩, ⟨2, 19, 7, 2⟩, ⟨2, 19, 6, 4⟩]
  exact AllWinning.cons node_15003 (AllWinning.cons node_13988 (AllWinning.cons node_15058 (AllWinning.cons node_14084 (AllWinning.cons node_15061 (AllWinning.cons node_14094 (AllWinning.nil))))))

theorem node_16015 : Outcome ⟨2, 19, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 8, 2⟩, ⟨0, 19, 8, 4⟩, ⟨2, 18, 8, 2⟩, ⟨2, 17, 8, 4⟩, ⟨2, 16, 8, 6⟩, ⟨2, 15, 8, 8⟩, ⟨2, 19, 7, 2⟩, ⟨2, 19, 6, 4⟩, ⟨2, 19, 5, 6⟩, ⟨2, 19, 4, 8⟩]
  exact AllWinning.cons node_15003 (AllWinning.cons node_13988 (AllWinning.cons node_15058 (AllWinning.cons node_14084 (AllWinning.cons node_13119 (AllWinning.cons node_12127 (AllWinning.cons node_15061 (AllWinning.cons node_14094 (AllWinning.cons node_13128 (AllWinning.cons node_12144 (AllWinning.nil))))))))))

theorem node_16016 : Outcome ⟨2, 19, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 8, 2⟩, ⟨0, 19, 8, 4⟩, ⟨2, 18, 8, 2⟩, ⟨2, 17, 8, 4⟩, ⟨2, 16, 8, 6⟩, ⟨2, 15, 8, 8⟩, ⟨2, 14, 8, 10⟩, ⟨2, 13, 8, 12⟩, ⟨2, 19, 7, 2⟩, ⟨2, 19, 6, 4⟩, ⟨2, 19, 5, 6⟩, ⟨2, 19, 4, 8⟩, ⟨2, 19, 3, 10⟩, ⟨2, 19, 2, 12⟩]
  exact AllWinning.cons node_15003 (AllWinning.cons node_13988 (AllWinning.cons node_15058 (AllWinning.cons node_14084 (AllWinning.cons node_13119 (AllWinning.cons node_12127 (AllWinning.cons node_11128 (AllWinning.cons node_10065 (AllWinning.cons node_15061 (AllWinning.cons node_14094 (AllWinning.cons node_13128 (AllWinning.cons node_12144 (AllWinning.cons node_11147 (AllWinning.cons node_10085 (AllWinning.nil))))))))))))))

theorem node_16017 : Outcome ⟨2, 19, 8, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 8, 2⟩, ⟨0, 19, 8, 4⟩, ⟨2, 18, 8, 2⟩, ⟨2, 17, 8, 4⟩, ⟨2, 16, 8, 6⟩, ⟨2, 15, 8, 8⟩, ⟨2, 14, 8, 10⟩, ⟨2, 13, 8, 12⟩, ⟨2, 12, 8, 14⟩, ⟨2, 11, 8, 16⟩, ⟨2, 10, 8, 18⟩, ⟨2, 9, 8, 20⟩, ⟨2, 19, 7, 2⟩, ⟨2, 19, 6, 4⟩, ⟨2, 19, 5, 6⟩, ⟨2, 19, 4, 8⟩, ⟨2, 19, 3, 10⟩, ⟨2, 19, 2, 12⟩, ⟨2, 19, 1, 14⟩, ⟨2, 19, 0, 16⟩]
  exact AllWinning.cons node_15003 (AllWinning.cons node_13988 (AllWinning.cons node_15058 (AllWinning.cons node_14084 (AllWinning.cons node_13119 (AllWinning.cons node_12127 (AllWinning.cons node_11128 (AllWinning.cons node_10065 (AllWinning.cons node_9092 (AllWinning.cons node_8113 (AllWinning.cons node_7161 (AllWinning.cons node_6236 (AllWinning.cons node_15061 (AllWinning.cons node_14094 (AllWinning.cons node_13128 (AllWinning.cons node_12144 (AllWinning.cons node_11147 (AllWinning.cons node_10085 (AllWinning.cons node_9120 (AllWinning.cons node_8146 (AllWinning.nil))))))))))))))))))))

theorem node_16018 : Outcome ⟨2, 19, 8, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 8, 2⟩, ⟨0, 19, 8, 4⟩, ⟨2, 18, 8, 2⟩, ⟨2, 17, 8, 4⟩, ⟨2, 16, 8, 6⟩, ⟨2, 15, 8, 8⟩, ⟨2, 14, 8, 10⟩, ⟨2, 13, 8, 12⟩, ⟨2, 12, 8, 14⟩, ⟨2, 11, 8, 16⟩, ⟨2, 10, 8, 18⟩, ⟨2, 9, 8, 20⟩, ⟨2, 8, 8, 22⟩, ⟨2, 7, 8, 24⟩, ⟨2, 19, 7, 2⟩, ⟨2, 19, 6, 4⟩, ⟨2, 19, 5, 6⟩, ⟨2, 19, 4, 8⟩, ⟨2, 19, 3, 10⟩, ⟨2, 19, 2, 12⟩, ⟨2, 19, 1, 14⟩, ⟨2, 19, 0, 16⟩]
  exact AllWinning.cons node_15003 (AllWinning.cons node_13988 (AllWinning.cons node_15058 (AllWinning.cons node_14084 (AllWinning.cons node_13119 (AllWinning.cons node_12127 (AllWinning.cons node_11128 (AllWinning.cons node_10065 (AllWinning.cons node_9092 (AllWinning.cons node_8113 (AllWinning.cons node_7161 (AllWinning.cons node_6236 (AllWinning.cons node_5488 (AllWinning.cons node_4763 (AllWinning.cons node_15061 (AllWinning.cons node_14094 (AllWinning.cons node_13128 (AllWinning.cons node_12144 (AllWinning.cons node_11147 (AllWinning.cons node_10085 (AllWinning.cons node_9120 (AllWinning.cons node_8146 (AllWinning.nil))))))))))))))))))))))

theorem node_16019 : Outcome ⟨2, 19, 8, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 8, 2⟩, ⟨0, 19, 8, 4⟩, ⟨2, 18, 8, 2⟩, ⟨2, 17, 8, 4⟩, ⟨2, 16, 8, 6⟩, ⟨2, 15, 8, 8⟩, ⟨2, 14, 8, 10⟩, ⟨2, 13, 8, 12⟩, ⟨2, 12, 8, 14⟩, ⟨2, 11, 8, 16⟩, ⟨2, 10, 8, 18⟩, ⟨2, 9, 8, 20⟩, ⟨2, 8, 8, 22⟩, ⟨2, 7, 8, 24⟩, ⟨2, 6, 8, 26⟩, ⟨2, 5, 8, 28⟩, ⟨2, 19, 7, 2⟩, ⟨2, 19, 6, 4⟩, ⟨2, 19, 5, 6⟩, ⟨2, 19, 4, 8⟩, ⟨2, 19, 3, 10⟩, ⟨2, 19, 2, 12⟩, ⟨2, 19, 1, 14⟩, ⟨2, 19, 0, 16⟩]
  exact AllWinning.cons node_15003 (AllWinning.cons node_13988 (AllWinning.cons node_15058 (AllWinning.cons node_14084 (AllWinning.cons node_13119 (AllWinning.cons node_12127 (AllWinning.cons node_11128 (AllWinning.cons node_10065 (AllWinning.cons node_9092 (AllWinning.cons node_8113 (AllWinning.cons node_7161 (AllWinning.cons node_6236 (AllWinning.cons node_5488 (AllWinning.cons node_4763 (AllWinning.cons node_4072 (AllWinning.cons node_3502 (AllWinning.cons node_15061 (AllWinning.cons node_14094 (AllWinning.cons node_13128 (AllWinning.cons node_12144 (AllWinning.cons node_11147 (AllWinning.cons node_10085 (AllWinning.cons node_9120 (AllWinning.cons node_8146 (AllWinning.nil))))))))))))))))))))))))

theorem node_16020 : Outcome ⟨2, 20, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 8⟩) (by decide) node_12148

theorem node_16021 : Outcome ⟨2, 20, 7, 12⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 8⟩) (by decide) node_12148

theorem node_16022 : Outcome ⟨3, 6, 20, 6⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 12⟩) (by decide) node_10113

theorem node_16023 : Outcome ⟨3, 6, 20, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 12⟩) (by decide) node_10113

theorem node_16024 : Outcome ⟨3, 7, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 7, 19, 2⟩, ⟨1, 7, 19, 4⟩, ⟨3, 6, 19, 2⟩, ⟨3, 5, 19, 4⟩, ⟨3, 7, 18, 2⟩, ⟨3, 7, 17, 4⟩]
  exact AllWinning.cons node_15010 (AllWinning.cons node_13998 (AllWinning.cons node_15067 (AllWinning.cons node_14101 (AllWinning.cons node_15070 (AllWinning.cons node_14107 (AllWinning.nil))))))

theorem node_16025 : Outcome ⟨3, 7, 19, 6⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 12⟩) (by decide) node_10094

theorem node_16026 : Outcome ⟨3, 7, 19, 8⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 12⟩) (by decide) node_10094

theorem node_16027 : Outcome ⟨3, 8, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 4⟩) (by decide) node_14002

theorem node_16028 : Outcome ⟨3, 8, 18, 10⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 4⟩) (by decide) node_14002

theorem node_16029 : Outcome ⟨3, 8, 18, 14⟩ true :=
  Outcome.win (q := ⟨1, 8, 18, 4⟩) (by decide) node_14002

theorem node_16030 : Outcome ⟨3, 9, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 17, 2⟩, ⟨1, 9, 17, 4⟩, ⟨3, 8, 17, 2⟩, ⟨3, 7, 17, 4⟩, ⟨3, 9, 16, 2⟩, ⟨3, 9, 15, 4⟩]
  exact AllWinning.cons node_15015 (AllWinning.cons node_14007 (AllWinning.cons node_15074 (AllWinning.cons node_14107 (AllWinning.cons node_15076 (AllWinning.cons node_14118 (AllWinning.nil))))))

theorem node_16031 : Outcome ⟨3, 9, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 17, 2⟩, ⟨1, 9, 17, 4⟩, ⟨0, 9, 17, 6⟩, ⟨3, 8, 17, 2⟩, ⟨3, 7, 17, 4⟩, ⟨3, 6, 17, 6⟩, ⟨3, 5, 17, 8⟩, ⟨3, 9, 16, 2⟩, ⟨3, 9, 15, 4⟩, ⟨3, 9, 14, 6⟩, ⟨3, 9, 13, 8⟩]
  exact AllWinning.cons node_15015 (AllWinning.cons node_14007 (AllWinning.cons node_12990 (AllWinning.cons node_15074 (AllWinning.cons node_14107 (AllWinning.cons node_13138 (AllWinning.cons node_12163 (AllWinning.cons node_15076 (AllWinning.cons node_14118 (AllWinning.cons node_13149 (AllWinning.cons node_12180 (AllWinning.nil)))))))))))

theorem node_16032 : Outcome ⟨3, 9, 17, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 10⟩) (by decide) node_11176

theorem node_16033 : Outcome ⟨3, 9, 17, 10⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 10⟩) (by decide) node_11176

theorem node_16034 : Outcome ⟨3, 10, 16, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 6⟩) (by decide) node_13152

theorem node_16035 : Outcome ⟨3, 10, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 6⟩) (by decide) node_13152

theorem node_16036 : Outcome ⟨3, 11, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 11, 15, 4⟩) (by decide) node_14015

theorem node_16037 : Outcome ⟨3, 11, 15, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 8⟩) (by decide) node_12171

theorem node_16038 : Outcome ⟨3, 11, 15, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 8⟩) (by decide) node_12171

theorem node_16039 : Outcome ⟨3, 11, 15, 14⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 20⟩) (by decide) node_6339

theorem node_16040 : Outcome ⟨3, 12, 14, 2⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 2⟩) (by decide) node_15026

theorem node_16041 : Outcome ⟨3, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 2⟩) (by decide) node_15026

theorem node_16042 : Outcome ⟨3, 12, 14, 10⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 12⟩) (by decide) node_10113

theorem node_16043 : Outcome ⟨3, 12, 14, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 12⟩) (by decide) node_10113

theorem node_16044 : Outcome ⟨3, 13, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 13, 2⟩, ⟨1, 13, 13, 4⟩, ⟨3, 12, 13, 2⟩, ⟨3, 11, 13, 4⟩, ⟨3, 13, 12, 2⟩, ⟨3, 13, 11, 4⟩]
  exact AllWinning.cons node_15034 (AllWinning.cons node_14023 (AllWinning.cons node_15085 (AllWinning.cons node_14126 (AllWinning.cons node_15089 (AllWinning.cons node_14133 (AllWinning.nil))))))

theorem node_16045 : Outcome ⟨3, 13, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 6⟩) (by decide) node_13003

theorem node_16046 : Outcome ⟨3, 13, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 6⟩) (by decide) node_13003

theorem node_16047 : Outcome ⟨3, 13, 13, 10⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 6⟩) (by decide) node_13003

theorem node_16048 : Outcome ⟨3, 13, 13, 20⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 6⟩) (by decide) node_13003

theorem node_16049 : Outcome ⟨3, 14, 12, 2⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 2⟩) (by decide) node_15039

theorem node_16050 : Outcome ⟨3, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 2⟩) (by decide) node_15039

theorem node_16051 : Outcome ⟨3, 14, 12, 10⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 12⟩) (by decide) node_10145

theorem node_16052 : Outcome ⟨3, 14, 12, 12⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 12⟩) (by decide) node_10145

theorem node_16053 : Outcome ⟨3, 15, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 11, 4⟩) (by decide) node_14031

theorem node_16054 : Outcome ⟨3, 15, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 8⟩) (by decide) node_12198

theorem node_16055 : Outcome ⟨3, 15, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 8⟩) (by decide) node_12198

theorem node_16056 : Outcome ⟨3, 15, 11, 14⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 20⟩) (by decide) node_6308

theorem node_16057 : Outcome ⟨3, 16, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 6⟩) (by decide) node_13170

theorem node_16058 : Outcome ⟨3, 16, 10, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 6⟩) (by decide) node_13170

theorem node_16059 : Outcome ⟨3, 17, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 9, 2⟩, ⟨1, 17, 9, 4⟩, ⟨3, 16, 9, 2⟩, ⟨3, 15, 9, 4⟩, ⟨3, 17, 8, 2⟩, ⟨3, 17, 7, 4⟩]
  exact AllWinning.cons node_15054 (AllWinning.cons node_14039 (AllWinning.cons node_15100 (AllWinning.cons node_14138 (AllWinning.cons node_15102 (AllWinning.cons node_14151 (AllWinning.nil))))))

theorem node_16060 : Outcome ⟨3, 17, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 9, 2⟩, ⟨1, 17, 9, 4⟩, ⟨0, 17, 9, 6⟩, ⟨3, 16, 9, 2⟩, ⟨3, 15, 9, 4⟩, ⟨3, 14, 9, 6⟩, ⟨3, 13, 9, 8⟩, ⟨3, 17, 8, 2⟩, ⟨3, 17, 7, 4⟩, ⟨3, 17, 6, 6⟩, ⟨3, 17, 5, 8⟩]
  exact AllWinning.cons node_15054 (AllWinning.cons node_14039 (AllWinning.cons node_13019 (AllWinning.cons node_15100 (AllWinning.cons node_14138 (AllWinning.cons node_13178 (AllWinning.cons node_12191 (AllWinning.cons node_15102 (AllWinning.cons node_14151 (AllWinning.cons node_13188 (AllWinning.cons node_12208 (AllWinning.nil)))))))))))

theorem node_16061 : Outcome ⟨3, 17, 9, 6⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 10⟩) (by decide) node_11197

theorem node_16062 : Outcome ⟨3, 17, 9, 10⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 10⟩) (by decide) node_11197

theorem node_16063 : Outcome ⟨3, 18, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 4⟩) (by decide) node_14043

theorem node_16064 : Outcome ⟨3, 18, 8, 10⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 4⟩) (by decide) node_14043

theorem node_16065 : Outcome ⟨3, 18, 8, 14⟩ true :=
  Outcome.win (q := ⟨1, 18, 8, 4⟩) (by decide) node_14043

theorem node_16066 : Outcome ⟨3, 19, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 19, 7, 2⟩, ⟨1, 19, 7, 4⟩, ⟨3, 18, 7, 2⟩, ⟨3, 17, 7, 4⟩, ⟨3, 19, 6, 2⟩, ⟨3, 19, 5, 4⟩]
  exact AllWinning.cons node_15061 (AllWinning.cons node_14047 (AllWinning.cons node_15104 (AllWinning.cons node_14151 (AllWinning.cons node_15108 (AllWinning.cons node_14158 (AllWinning.nil))))))

theorem node_16067 : Outcome ⟨3, 19, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 12⟩) (by decide) node_10164

theorem node_16068 : Outcome ⟨3, 19, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 12⟩) (by decide) node_10164

theorem node_16069 : Outcome ⟨3, 20, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 12⟩) (by decide) node_10145

theorem node_16070 : Outcome ⟨3, 20, 6, 12⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 12⟩) (by decide) node_10145

theorem node_16071 : Outcome ⟨4, 5, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 20, 2⟩, ⟨2, 5, 20, 4⟩, ⟨4, 4, 20, 2⟩, ⟨4, 3, 20, 4⟩, ⟨4, 5, 19, 2⟩, ⟨4, 5, 18, 4⟩]
  exact AllWinning.cons node_15065 (AllWinning.cons node_14052 (AllWinning.cons node_15113 (AllWinning.cons node_14163 (AllWinning.cons node_15114 (AllWinning.cons node_14167 (AllWinning.nil))))))

theorem node_16072 : Outcome ⟨4, 5, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 20, 2⟩, ⟨2, 5, 20, 4⟩, ⟨1, 5, 20, 6⟩, ⟨0, 5, 20, 8⟩, ⟨4, 4, 20, 2⟩, ⟨4, 3, 20, 4⟩, ⟨4, 2, 20, 6⟩, ⟨4, 1, 20, 8⟩, ⟨4, 5, 19, 2⟩, ⟨4, 5, 18, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 5, 16, 8⟩]
  exact AllWinning.cons node_15065 (AllWinning.cons node_14052 (AllWinning.cons node_13031 (AllWinning.cons node_11960 (AllWinning.cons node_15113 (AllWinning.cons node_14163 (AllWinning.cons node_13198 (AllWinning.cons node_12222 (AllWinning.cons node_15114 (AllWinning.cons node_14167 (AllWinning.cons node_13207 (AllWinning.cons node_12235 (AllWinning.nil))))))))))))

theorem node_16073 : Outcome ⟨4, 5, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 20, 2⟩, ⟨2, 5, 20, 4⟩, ⟨1, 5, 20, 6⟩, ⟨0, 5, 20, 8⟩, ⟨4, 4, 20, 2⟩, ⟨4, 3, 20, 4⟩, ⟨4, 2, 20, 6⟩, ⟨4, 1, 20, 8⟩, ⟨4, 0, 20, 10⟩, ⟨4, 5, 19, 2⟩, ⟨4, 5, 18, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 5, 15, 10⟩, ⟨4, 5, 14, 12⟩]
  exact AllWinning.cons node_15065 (AllWinning.cons node_14052 (AllWinning.cons node_13031 (AllWinning.cons node_11960 (AllWinning.cons node_15113 (AllWinning.cons node_14163 (AllWinning.cons node_13198 (AllWinning.cons node_12222 (AllWinning.cons node_11228 (AllWinning.cons node_15114 (AllWinning.cons node_14167 (AllWinning.cons node_13207 (AllWinning.cons node_12235 (AllWinning.cons node_11246 (AllWinning.cons node_10189 (AllWinning.nil)))))))))))))))

theorem node_16074 : Outcome ⟨4, 5, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 20, 2⟩, ⟨2, 5, 20, 4⟩, ⟨1, 5, 20, 6⟩, ⟨0, 5, 20, 8⟩, ⟨4, 4, 20, 2⟩, ⟨4, 3, 20, 4⟩, ⟨4, 2, 20, 6⟩, ⟨4, 1, 20, 8⟩, ⟨4, 0, 20, 10⟩, ⟨4, 5, 19, 2⟩, ⟨4, 5, 18, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 5, 15, 10⟩, ⟨4, 5, 14, 12⟩, ⟨4, 5, 13, 14⟩, ⟨4, 5, 12, 16⟩]
  exact AllWinning.cons node_15065 (AllWinning.cons node_14052 (AllWinning.cons node_13031 (AllWinning.cons node_11960 (AllWinning.cons node_15113 (AllWinning.cons node_14163 (AllWinning.cons node_13198 (AllWinning.cons node_12222 (AllWinning.cons node_11228 (AllWinning.cons node_15114 (AllWinning.cons node_14167 (AllWinning.cons node_13207 (AllWinning.cons node_12235 (AllWinning.cons node_11246 (AllWinning.cons node_10189 (AllWinning.cons node_9217 (AllWinning.cons node_8242 (AllWinning.nil)))))))))))))))))

theorem node_16075 : Outcome ⟨4, 5, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 20, 2⟩, ⟨2, 5, 20, 4⟩, ⟨1, 5, 20, 6⟩, ⟨0, 5, 20, 8⟩, ⟨4, 4, 20, 2⟩, ⟨4, 3, 20, 4⟩, ⟨4, 2, 20, 6⟩, ⟨4, 1, 20, 8⟩, ⟨4, 0, 20, 10⟩, ⟨4, 5, 19, 2⟩, ⟨4, 5, 18, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 5, 15, 10⟩, ⟨4, 5, 14, 12⟩, ⟨4, 5, 13, 14⟩, ⟨4, 5, 12, 16⟩, ⟨4, 5, 11, 18⟩, ⟨4, 5, 10, 20⟩]
  exact AllWinning.cons node_15065 (AllWinning.cons node_14052 (AllWinning.cons node_13031 (AllWinning.cons node_11960 (AllWinning.cons node_15113 (AllWinning.cons node_14163 (AllWinning.cons node_13198 (AllWinning.cons node_12222 (AllWinning.cons node_11228 (AllWinning.cons node_15114 (AllWinning.cons node_14167 (AllWinning.cons node_13207 (AllWinning.cons node_12235 (AllWinning.cons node_11246 (AllWinning.cons node_10189 (AllWinning.cons node_9217 (AllWinning.cons node_8242 (AllWinning.cons node_7291 (AllWinning.cons node_6388 (AllWinning.nil)))))))))))))))))))

theorem node_16076 : Outcome ⟨4, 5, 20, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 20, 2⟩, ⟨2, 5, 20, 4⟩, ⟨1, 5, 20, 6⟩, ⟨0, 5, 20, 8⟩, ⟨4, 4, 20, 2⟩, ⟨4, 3, 20, 4⟩, ⟨4, 2, 20, 6⟩, ⟨4, 1, 20, 8⟩, ⟨4, 0, 20, 10⟩, ⟨4, 5, 19, 2⟩, ⟨4, 5, 18, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 5, 15, 10⟩, ⟨4, 5, 14, 12⟩, ⟨4, 5, 13, 14⟩, ⟨4, 5, 12, 16⟩, ⟨4, 5, 11, 18⟩, ⟨4, 5, 10, 20⟩, ⟨4, 5, 9, 22⟩, ⟨4, 5, 8, 24⟩]
  exact AllWinning.cons node_15065 (AllWinning.cons node_14052 (AllWinning.cons node_13031 (AllWinning.cons node_11960 (AllWinning.cons node_15113 (AllWinning.cons node_14163 (AllWinning.cons node_13198 (AllWinning.cons node_12222 (AllWinning.cons node_11228 (AllWinning.cons node_15114 (AllWinning.cons node_14167 (AllWinning.cons node_13207 (AllWinning.cons node_12235 (AllWinning.cons node_11246 (AllWinning.cons node_10189 (AllWinning.cons node_9217 (AllWinning.cons node_8242 (AllWinning.cons node_7291 (AllWinning.cons node_6388 (AllWinning.cons node_5598 (AllWinning.cons node_4895 (AllWinning.nil)))))))))))))))))))))

theorem node_16077 : Outcome ⟨4, 6, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 6, 19, 2⟩, ⟨2, 6, 19, 4⟩, ⟨4, 5, 19, 2⟩, ⟨4, 4, 19, 4⟩, ⟨4, 6, 18, 2⟩, ⟨4, 6, 17, 4⟩]
  exact AllWinning.cons node_15067 (AllWinning.cons node_14054 (AllWinning.cons node_15114 (AllWinning.cons node_14164 (AllWinning.cons node_15117 (AllWinning.cons node_14170 (AllWinning.nil))))))

theorem node_16078 : Outcome ⟨4, 6, 19, 6⟩ true :=
  Outcome.win (q := ⟨0, 6, 19, 8⟩) (by decide) node_11964

theorem node_16079 : Outcome ⟨4, 6, 19, 16⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 18⟩) (by decide) node_7301

theorem node_16080 : Outcome ⟨4, 7, 18, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 4⟩) (by decide) node_14057

theorem node_16081 : Outcome ⟨4, 7, 18, 8⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 4⟩) (by decide) node_14057

theorem node_16082 : Outcome ⟨4, 8, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 17, 2⟩, ⟨2, 8, 17, 4⟩, ⟨4, 7, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨4, 8, 16, 2⟩, ⟨4, 8, 15, 4⟩]
  exact AllWinning.cons node_15074 (AllWinning.cons node_14064 (AllWinning.cons node_15120 (AllWinning.cons node_14170 (AllWinning.cons node_15121 (AllWinning.cons node_14175 (AllWinning.nil))))))

theorem node_16083 : Outcome ⟨4, 8, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 17, 2⟩, ⟨2, 8, 17, 4⟩, ⟨1, 8, 17, 6⟩, ⟨0, 8, 17, 8⟩, ⟨4, 7, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 4, 17, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 8, 15, 4⟩, ⟨4, 8, 14, 6⟩, ⟨4, 8, 13, 8⟩]
  exact AllWinning.cons node_15074 (AllWinning.cons node_14064 (AllWinning.cons node_13039 (AllWinning.cons node_11971 (AllWinning.cons node_15120 (AllWinning.cons node_14170 (AllWinning.cons node_13207 (AllWinning.cons node_12232 (AllWinning.cons node_15121 (AllWinning.cons node_14175 (AllWinning.cons node_13213 (AllWinning.cons node_12243 (AllWinning.nil))))))))))))

theorem node_16084 : Outcome ⟨4, 8, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 17, 2⟩, ⟨2, 8, 17, 4⟩, ⟨1, 8, 17, 6⟩, ⟨0, 8, 17, 8⟩, ⟨4, 7, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 4, 17, 8⟩, ⟨4, 3, 17, 10⟩, ⟨4, 2, 17, 12⟩, ⟨4, 8, 16, 2⟩, ⟨4, 8, 15, 4⟩, ⟨4, 8, 14, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 8, 12, 10⟩, ⟨4, 8, 11, 12⟩]
  exact AllWinning.cons node_15074 (AllWinning.cons node_14064 (AllWinning.cons node_13039 (AllWinning.cons node_11971 (AllWinning.cons node_15120 (AllWinning.cons node_14170 (AllWinning.cons node_13207 (AllWinning.cons node_12232 (AllWinning.cons node_11238 (AllWinning.cons node_10178 (AllWinning.cons node_15121 (AllWinning.cons node_14175 (AllWinning.cons node_13213 (AllWinning.cons node_12243 (AllWinning.cons node_11255 (AllWinning.cons node_10202 (AllWinning.nil))))))))))))))))

theorem node_16085 : Outcome ⟨4, 8, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 17, 2⟩, ⟨2, 8, 17, 4⟩, ⟨1, 8, 17, 6⟩, ⟨0, 8, 17, 8⟩, ⟨4, 7, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 4, 17, 8⟩, ⟨4, 3, 17, 10⟩, ⟨4, 2, 17, 12⟩, ⟨4, 1, 17, 14⟩, ⟨4, 0, 17, 16⟩, ⟨4, 8, 16, 2⟩, ⟨4, 8, 15, 4⟩, ⟨4, 8, 14, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 8, 12, 10⟩, ⟨4, 8, 11, 12⟩, ⟨4, 8, 10, 14⟩, ⟨4, 8, 9, 16⟩]
  exact AllWinning.cons node_15074 (AllWinning.cons node_14064 (AllWinning.cons node_13039 (AllWinning.cons node_11971 (AllWinning.cons node_15120 (AllWinning.cons node_14170 (AllWinning.cons node_13207 (AllWinning.cons node_12232 (AllWinning.cons node_11238 (AllWinning.cons node_10178 (AllWinning.cons node_9203 (AllWinning.cons node_8224 (AllWinning.cons node_15121 (AllWinning.cons node_14175 (AllWinning.cons node_13213 (AllWinning.cons node_12243 (AllWinning.cons node_11255 (AllWinning.cons node_10202 (AllWinning.cons node_9231 (AllWinning.cons node_8252 (AllWinning.nil))))))))))))))))))))

theorem node_16086 : Outcome ⟨4, 8, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 17, 2⟩, ⟨2, 8, 17, 4⟩, ⟨1, 8, 17, 6⟩, ⟨0, 8, 17, 8⟩, ⟨4, 7, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 4, 17, 8⟩, ⟨4, 3, 17, 10⟩, ⟨4, 2, 17, 12⟩, ⟨4, 1, 17, 14⟩, ⟨4, 0, 17, 16⟩, ⟨4, 8, 16, 2⟩, ⟨4, 8, 15, 4⟩, ⟨4, 8, 14, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 8, 12, 10⟩, ⟨4, 8, 11, 12⟩, ⟨4, 8, 10, 14⟩, ⟨4, 8, 9, 16⟩, ⟨4, 8, 8, 18⟩, ⟨4, 8, 7, 20⟩]
  exact AllWinning.cons node_15074 (AllWinning.cons node_14064 (AllWinning.cons node_13039 (AllWinning.cons node_11971 (AllWinning.cons node_15120 (AllWinning.cons node_14170 (AllWinning.cons node_13207 (AllWinning.cons node_12232 (AllWinning.cons node_11238 (AllWinning.cons node_10178 (AllWinning.cons node_9203 (AllWinning.cons node_8224 (AllWinning.cons node_15121 (AllWinning.cons node_14175 (AllWinning.cons node_13213 (AllWinning.cons node_12243 (AllWinning.cons node_11255 (AllWinning.cons node_10202 (AllWinning.cons node_9231 (AllWinning.cons node_8252 (AllWinning.cons node_7309 (AllWinning.cons node_6397 (AllWinning.nil))))))))))))))))))))))

theorem node_16087 : Outcome ⟨4, 8, 17, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 17, 2⟩, ⟨2, 8, 17, 4⟩, ⟨1, 8, 17, 6⟩, ⟨0, 8, 17, 8⟩, ⟨4, 7, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 4, 17, 8⟩, ⟨4, 3, 17, 10⟩, ⟨4, 2, 17, 12⟩, ⟨4, 1, 17, 14⟩, ⟨4, 0, 17, 16⟩, ⟨4, 8, 16, 2⟩, ⟨4, 8, 15, 4⟩, ⟨4, 8, 14, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 8, 12, 10⟩, ⟨4, 8, 11, 12⟩, ⟨4, 8, 10, 14⟩, ⟨4, 8, 9, 16⟩, ⟨4, 8, 8, 18⟩, ⟨4, 8, 7, 20⟩, ⟨4, 8, 6, 22⟩, ⟨4, 8, 5, 24⟩, ⟨4, 8, 4, 26⟩, ⟨4, 8, 3, 28⟩]
  exact AllWinning.cons node_15074 (AllWinning.cons node_14064 (AllWinning.cons node_13039 (AllWinning.cons node_11971 (AllWinning.cons node_15120 (AllWinning.cons node_14170 (AllWinning.cons node_13207 (AllWinning.cons node_12232 (AllWinning.cons node_11238 (AllWinning.cons node_10178 (AllWinning.cons node_9203 (AllWinning.cons node_8224 (AllWinning.cons node_15121 (AllWinning.cons node_14175 (AllWinning.cons node_13213 (AllWinning.cons node_12243 (AllWinning.cons node_11255 (AllWinning.cons node_10202 (AllWinning.cons node_9231 (AllWinning.cons node_8252 (AllWinning.cons node_7309 (AllWinning.cons node_6397 (AllWinning.cons node_5608 (AllWinning.cons node_4903 (AllWinning.cons node_4204 (AllWinning.cons node_3612 (AllWinning.nil))))))))))))))))))))))))))

theorem node_16088 : Outcome ⟨4, 8, 17, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 17, 2⟩, ⟨2, 8, 17, 4⟩, ⟨1, 8, 17, 6⟩, ⟨0, 8, 17, 8⟩, ⟨4, 7, 17, 2⟩, ⟨4, 6, 17, 4⟩, ⟨4, 5, 17, 6⟩, ⟨4, 4, 17, 8⟩, ⟨4, 3, 17, 10⟩, ⟨4, 2, 17, 12⟩, ⟨4, 1, 17, 14⟩, ⟨4, 0, 17, 16⟩, ⟨4, 8, 16, 2⟩, ⟨4, 8, 15, 4⟩, ⟨4, 8, 14, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 8, 12, 10⟩, ⟨4, 8, 11, 12⟩, ⟨4, 8, 10, 14⟩, ⟨4, 8, 9, 16⟩, ⟨4, 8, 8, 18⟩, ⟨4, 8, 7, 20⟩, ⟨4, 8, 6, 22⟩, ⟨4, 8, 5, 24⟩, ⟨4, 8, 4, 26⟩, ⟨4, 8, 3, 28⟩, ⟨4, 8, 2, 30⟩, ⟨4, 8, 1, 32⟩]
  exact AllWinning.cons node_15074 (AllWinning.cons node_14064 (AllWinning.cons node_13039 (AllWinning.cons node_11971 (AllWinning.cons node_15120 (AllWinning.cons node_14170 (AllWinning.cons node_13207 (AllWinning.cons node_12232 (AllWinning.cons node_11238 (AllWinning.cons node_10178 (AllWinning.cons node_9203 (AllWinning.cons node_8224 (AllWinning.cons node_15121 (AllWinning.cons node_14175 (AllWinning.cons node_13213 (AllWinning.cons node_12243 (AllWinning.cons node_11255 (AllWinning.cons node_10202 (AllWinning.cons node_9231 (AllWinning.cons node_8252 (AllWinning.cons node_7309 (AllWinning.cons node_6397 (AllWinning.cons node_5608 (AllWinning.cons node_4903 (AllWinning.cons node_4204 (AllWinning.cons node_3612 (AllWinning.cons node_3076 (AllWinning.cons node_2621 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_16089 : Outcome ⟨4, 9, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.nil))))))))))))

theorem node_16090 : Outcome ⟨4, 9, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 4, 16, 10⟩, ⟨4, 3, 16, 12⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩, ⟨4, 9, 11, 10⟩, ⟨4, 9, 10, 12⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_11242 (AllWinning.cons node_10182 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.cons node_11258 (AllWinning.cons node_10206 (AllWinning.nil))))))))))))))))

theorem node_16091 : Outcome ⟨4, 9, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 4, 16, 10⟩, ⟨4, 3, 16, 12⟩, ⟨4, 2, 16, 14⟩, ⟨4, 1, 16, 16⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩, ⟨4, 9, 11, 10⟩, ⟨4, 9, 10, 12⟩, ⟨4, 9, 9, 14⟩, ⟨4, 9, 8, 16⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_11242 (AllWinning.cons node_10182 (AllWinning.cons node_9208 (AllWinning.cons node_8226 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.cons node_11258 (AllWinning.cons node_10206 (AllWinning.cons node_9234 (AllWinning.cons node_8255 (AllWinning.nil))))))))))))))))))))

theorem node_16092 : Outcome ⟨4, 9, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 4, 16, 10⟩, ⟨4, 3, 16, 12⟩, ⟨4, 2, 16, 14⟩, ⟨4, 1, 16, 16⟩, ⟨4, 0, 16, 18⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩, ⟨4, 9, 11, 10⟩, ⟨4, 9, 10, 12⟩, ⟨4, 9, 9, 14⟩, ⟨4, 9, 8, 16⟩, ⟨4, 9, 7, 18⟩, ⟨4, 9, 6, 20⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_11242 (AllWinning.cons node_10182 (AllWinning.cons node_9208 (AllWinning.cons node_8226 (AllWinning.cons node_7268 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.cons node_11258 (AllWinning.cons node_10206 (AllWinning.cons node_9234 (AllWinning.cons node_8255 (AllWinning.cons node_7312 (AllWinning.cons node_6400 (AllWinning.nil)))))))))))))))))))))))

theorem node_16093 : Outcome ⟨4, 9, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 4, 16, 10⟩, ⟨4, 3, 16, 12⟩, ⟨4, 2, 16, 14⟩, ⟨4, 1, 16, 16⟩, ⟨4, 0, 16, 18⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩, ⟨4, 9, 11, 10⟩, ⟨4, 9, 10, 12⟩, ⟨4, 9, 9, 14⟩, ⟨4, 9, 8, 16⟩, ⟨4, 9, 7, 18⟩, ⟨4, 9, 6, 20⟩, ⟨4, 9, 5, 22⟩, ⟨4, 9, 4, 24⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_11242 (AllWinning.cons node_10182 (AllWinning.cons node_9208 (AllWinning.cons node_8226 (AllWinning.cons node_7268 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.cons node_11258 (AllWinning.cons node_10206 (AllWinning.cons node_9234 (AllWinning.cons node_8255 (AllWinning.cons node_7312 (AllWinning.cons node_6400 (AllWinning.cons node_5612 (AllWinning.cons node_4906 (AllWinning.nil)))))))))))))))))))))))))

theorem node_16094 : Outcome ⟨4, 9, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 4, 16, 10⟩, ⟨4, 3, 16, 12⟩, ⟨4, 2, 16, 14⟩, ⟨4, 1, 16, 16⟩, ⟨4, 0, 16, 18⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩, ⟨4, 9, 11, 10⟩, ⟨4, 9, 10, 12⟩, ⟨4, 9, 9, 14⟩, ⟨4, 9, 8, 16⟩, ⟨4, 9, 7, 18⟩, ⟨4, 9, 6, 20⟩, ⟨4, 9, 5, 22⟩, ⟨4, 9, 4, 24⟩, ⟨4, 9, 3, 26⟩, ⟨4, 9, 2, 28⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_11242 (AllWinning.cons node_10182 (AllWinning.cons node_9208 (AllWinning.cons node_8226 (AllWinning.cons node_7268 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.cons node_11258 (AllWinning.cons node_10206 (AllWinning.cons node_9234 (AllWinning.cons node_8255 (AllWinning.cons node_7312 (AllWinning.cons node_6400 (AllWinning.cons node_5612 (AllWinning.cons node_4906 (AllWinning.cons node_4207 (AllWinning.cons node_3618 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_16095 : Outcome ⟨4, 9, 16, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 4, 16, 10⟩, ⟨4, 3, 16, 12⟩, ⟨4, 2, 16, 14⟩, ⟨4, 1, 16, 16⟩, ⟨4, 0, 16, 18⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩, ⟨4, 9, 11, 10⟩, ⟨4, 9, 10, 12⟩, ⟨4, 9, 9, 14⟩, ⟨4, 9, 8, 16⟩, ⟨4, 9, 7, 18⟩, ⟨4, 9, 6, 20⟩, ⟨4, 9, 5, 22⟩, ⟨4, 9, 4, 24⟩, ⟨4, 9, 3, 26⟩, ⟨4, 9, 2, 28⟩, ⟨4, 9, 1, 30⟩, ⟨4, 9, 0, 32⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_11242 (AllWinning.cons node_10182 (AllWinning.cons node_9208 (AllWinning.cons node_8226 (AllWinning.cons node_7268 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.cons node_11258 (AllWinning.cons node_10206 (AllWinning.cons node_9234 (AllWinning.cons node_8255 (AllWinning.cons node_7312 (AllWinning.cons node_6400 (AllWinning.cons node_5612 (AllWinning.cons node_4906 (AllWinning.cons node_4207 (AllWinning.cons node_3618 (AllWinning.cons node_3079 (AllWinning.cons node_2627 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16096 : Outcome ⟨4, 9, 16, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 16, 2⟩, ⟨2, 9, 16, 4⟩, ⟨1, 9, 16, 6⟩, ⟨0, 9, 16, 8⟩, ⟨4, 8, 16, 2⟩, ⟨4, 7, 16, 4⟩, ⟨4, 6, 16, 6⟩, ⟨4, 5, 16, 8⟩, ⟨4, 4, 16, 10⟩, ⟨4, 3, 16, 12⟩, ⟨4, 2, 16, 14⟩, ⟨4, 1, 16, 16⟩, ⟨4, 0, 16, 18⟩, ⟨4, 9, 15, 2⟩, ⟨4, 9, 14, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 9, 12, 8⟩, ⟨4, 9, 11, 10⟩, ⟨4, 9, 10, 12⟩, ⟨4, 9, 9, 14⟩, ⟨4, 9, 8, 16⟩, ⟨4, 9, 7, 18⟩, ⟨4, 9, 6, 20⟩, ⟨4, 9, 5, 22⟩, ⟨4, 9, 4, 24⟩, ⟨4, 9, 3, 26⟩, ⟨4, 9, 2, 28⟩, ⟨4, 9, 1, 30⟩, ⟨4, 9, 0, 32⟩]
  exact AllWinning.cons node_15076 (AllWinning.cons node_14067 (AllWinning.cons node_13042 (AllWinning.cons node_11975 (AllWinning.cons node_15121 (AllWinning.cons node_14172 (AllWinning.cons node_13209 (AllWinning.cons node_12235 (AllWinning.cons node_11242 (AllWinning.cons node_10182 (AllWinning.cons node_9208 (AllWinning.cons node_8226 (AllWinning.cons node_7268 (AllWinning.cons node_15122 (AllWinning.cons node_14177 (AllWinning.cons node_13216 (AllWinning.cons node_12245 (AllWinning.cons node_11258 (AllWinning.cons node_10206 (AllWinning.cons node_9234 (AllWinning.cons node_8255 (AllWinning.cons node_7312 (AllWinning.cons node_6400 (AllWinning.cons node_5612 (AllWinning.cons node_4906 (AllWinning.cons node_4207 (AllWinning.cons node_3618 (AllWinning.cons node_3079 (AllWinning.cons node_2627 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_16097 : Outcome ⟨4, 10, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 14, 2⟩) (by decide) node_15125

theorem node_16098 : Outcome ⟨4, 11, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 11, 14, 2⟩) (by decide) node_15081

theorem node_16099 : Outcome ⟨4, 11, 14, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 14, 2⟩) (by decide) node_15081

theorem node_16100 : Outcome ⟨4, 11, 14, 16⟩ true :=
  Outcome.win (q := ⟨3, 11, 14, 2⟩) (by decide) node_15081

theorem node_16101 : Outcome ⟨4, 12, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 13, 2⟩, ⟨2, 12, 13, 4⟩, ⟨4, 11, 13, 2⟩, ⟨4, 10, 13, 4⟩, ⟨4, 12, 12, 2⟩, ⟨4, 12, 11, 4⟩]
  exact AllWinning.cons node_15085 (AllWinning.cons node_14074 (AllWinning.cons node_15128 (AllWinning.cons node_14180 (AllWinning.cons node_15131 (AllWinning.cons node_14184 (AllWinning.nil))))))

theorem node_16102 : Outcome ⟨4, 12, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 13, 2⟩, ⟨2, 12, 13, 4⟩, ⟨1, 12, 13, 6⟩, ⟨0, 12, 13, 8⟩, ⟨4, 11, 13, 2⟩, ⟨4, 10, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 12, 12, 2⟩, ⟨4, 12, 11, 4⟩, ⟨4, 12, 10, 6⟩, ⟨4, 12, 9, 8⟩]
  exact AllWinning.cons node_15085 (AllWinning.cons node_14074 (AllWinning.cons node_13051 (AllWinning.cons node_11984 (AllWinning.cons node_15128 (AllWinning.cons node_14180 (AllWinning.cons node_13216 (AllWinning.cons node_12243 (AllWinning.cons node_15131 (AllWinning.cons node_14184 (AllWinning.cons node_13225 (AllWinning.cons node_12255 (AllWinning.nil))))))))))))

theorem node_16103 : Outcome ⟨4, 12, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 13, 2⟩, ⟨2, 12, 13, 4⟩, ⟨1, 12, 13, 6⟩, ⟨0, 12, 13, 8⟩, ⟨4, 11, 13, 2⟩, ⟨4, 10, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 7, 13, 10⟩, ⟨4, 6, 13, 12⟩, ⟨4, 12, 12, 2⟩, ⟨4, 12, 11, 4⟩, ⟨4, 12, 10, 6⟩, ⟨4, 12, 9, 8⟩, ⟨4, 12, 8, 10⟩, ⟨4, 12, 7, 12⟩]
  exact AllWinning.cons node_15085 (AllWinning.cons node_14074 (AllWinning.cons node_13051 (AllWinning.cons node_11984 (AllWinning.cons node_15128 (AllWinning.cons node_14180 (AllWinning.cons node_13216 (AllWinning.cons node_12243 (AllWinning.cons node_11252 (AllWinning.cons node_10192 (AllWinning.cons node_15131 (AllWinning.cons node_14184 (AllWinning.cons node_13225 (AllWinning.cons node_12255 (AllWinning.cons node_11270 (AllWinning.cons node_10218 (AllWinning.nil))))))))))))))))

theorem node_16104 : Outcome ⟨4, 12, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 13, 2⟩, ⟨2, 12, 13, 4⟩, ⟨1, 12, 13, 6⟩, ⟨0, 12, 13, 8⟩, ⟨4, 11, 13, 2⟩, ⟨4, 10, 13, 4⟩, ⟨4, 9, 13, 6⟩, ⟨4, 8, 13, 8⟩, ⟨4, 7, 13, 10⟩, ⟨4, 6, 13, 12⟩, ⟨4, 5, 13, 14⟩, ⟨4, 4, 13, 16⟩, ⟨4, 12, 12, 2⟩, ⟨4, 12, 11, 4⟩, ⟨4, 12, 10, 6⟩, ⟨4, 12, 9, 8⟩, ⟨4, 12, 8, 10⟩, ⟨4, 12, 7, 12⟩, ⟨4, 12, 6, 14⟩, ⟨4, 12, 5, 16⟩]
  exact AllWinning.cons node_15085 (AllWinning.cons node_14074 (AllWinning.cons node_13051 (AllWinning.cons node_11984 (AllWinning.cons node_15128 (AllWinning.cons node_14180 (AllWinning.cons node_13216 (AllWinning.cons node_12243 (AllWinning.cons node_11252 (AllWinning.cons node_10192 (AllWinning.cons node_9217 (AllWinning.cons node_8238 (AllWinning.cons node_15131 (AllWinning.cons node_14184 (AllWinning.cons node_13225 (AllWinning.cons node_12255 (AllWinning.cons node_11270 (AllWinning.cons node_10218 (AllWinning.cons node_9247 (AllWinning.cons node_8266 (AllWinning.nil))))))))))))))))))))

end RQ9F1
