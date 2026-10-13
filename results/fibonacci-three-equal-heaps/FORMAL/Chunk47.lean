import Chunk46
set_option autoImplicit false
namespace RQ9F1

theorem node_11019 : Outcome ⟨0, 17, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 7, 4⟩) (by decide) node_8957

theorem node_11020 : Outcome ⟨0, 17, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 6⟩) (by decide) node_7966

theorem node_11021 : Outcome ⟨0, 17, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 6⟩) (by decide) node_7966

theorem node_11022 : Outcome ⟨0, 17, 7, 10⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 20⟩) (by decide) node_2858

theorem node_11023 : Outcome ⟨0, 17, 7, 20⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 20⟩) (by decide) node_2858

theorem node_11024 : Outcome ⟨0, 18, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 2⟩) (by decide) node_9921

theorem node_11025 : Outcome ⟨0, 18, 6, 8⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 2⟩) (by decide) node_9921

theorem node_11026 : Outcome ⟨0, 18, 6, 20⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 24⟩) (by decide) node_1900

theorem node_11027 : Outcome ⟨0, 18, 6, 24⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 24⟩) (by decide) node_1900

theorem node_11028 : Outcome ⟨0, 19, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 2⟩) (by decide) node_9921

theorem node_11029 : Outcome ⟨0, 19, 5, 20⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 28⟩) (by decide) node_1184

theorem node_11030 : Outcome ⟨0, 20, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 20, 2, 4⟩) (by decide) node_8977

theorem node_11031 : Outcome ⟨0, 20, 4, 6⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 6⟩) (by decide) node_7966

theorem node_11032 : Outcome ⟨0, 20, 4, 10⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 6⟩) (by decide) node_7966

theorem node_11033 : Outcome ⟨1, 3, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 2⟩) (by decide) node_9934

theorem node_11034 : Outcome ⟨1, 4, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 2⟩) (by decide) node_9934

theorem node_11035 : Outcome ⟨1, 4, 19, 16⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 8⟩) (by decide) node_7048

theorem node_11036 : Outcome ⟨1, 4, 19, 26⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 34⟩) (by decide) node_541

theorem node_11037 : Outcome ⟨1, 5, 18, 6⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 2⟩) (by decide) node_9875

theorem node_11038 : Outcome ⟨1, 5, 18, 8⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 2⟩) (by decide) node_9875

theorem node_11039 : Outcome ⟨1, 5, 18, 22⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 18⟩) (by decide) node_3420

theorem node_11040 : Outcome ⟨1, 6, 17, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 17, 2⟩) (by decide) node_9946

theorem node_11041 : Outcome ⟨1, 6, 17, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 28⟩) (by decide) node_1260

theorem node_11042 : Outcome ⟨1, 6, 17, 16⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 28⟩) (by decide) node_1260

theorem node_11043 : Outcome ⟨1, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 2⟩) (by decide) node_9951

theorem node_11044 : Outcome ⟨1, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 2⟩) (by decide) node_9951

theorem node_11045 : Outcome ⟨1, 7, 16, 16⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 10⟩) (by decide) node_6141

theorem node_11046 : Outcome ⟨1, 7, 16, 20⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 10⟩) (by decide) node_6141

theorem node_11047 : Outcome ⟨1, 8, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 15, 2⟩, ⟨1, 7, 15, 2⟩, ⟨1, 6, 15, 4⟩, ⟨1, 8, 14, 2⟩, ⟨1, 8, 13, 4⟩]
  exact AllWinning.cons node_9890 (AllWinning.cons node_9959 (AllWinning.cons node_8998 (AllWinning.cons node_9964 (AllWinning.cons node_9004 (AllWinning.nil)))))

theorem node_11048 : Outcome ⟨1, 8, 15, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 8⟩) (by decide) node_7048

theorem node_11049 : Outcome ⟨1, 8, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 8⟩) (by decide) node_7048

theorem node_11050 : Outcome ⟨1, 8, 15, 16⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 8⟩) (by decide) node_7048

theorem node_11051 : Outcome ⟨1, 9, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 14, 2⟩) (by decide) node_9894

theorem node_11052 : Outcome ⟨1, 9, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 14, 2⟩) (by decide) node_9894

theorem node_11053 : Outcome ⟨1, 9, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 14, 2⟩) (by decide) node_9894

theorem node_11054 : Outcome ⟨1, 10, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 2⟩) (by decide) node_9967

theorem node_11055 : Outcome ⟨1, 10, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 2⟩) (by decide) node_9967

theorem node_11056 : Outcome ⟨1, 10, 13, 14⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 2⟩) (by decide) node_9967

theorem node_11057 : Outcome ⟨1, 11, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 12, 2⟩, ⟨1, 10, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨1, 11, 11, 2⟩, ⟨1, 11, 10, 4⟩]
  exact AllWinning.cons node_9900 (AllWinning.cons node_9972 (AllWinning.cons node_9007 (AllWinning.cons node_9976 (AllWinning.cons node_9013 (AllWinning.nil)))))

theorem node_11058 : Outcome ⟨1, 11, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 6⟩) (by decide) node_8007

theorem node_11059 : Outcome ⟨1, 11, 12, 6⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 10⟩) (by decide) node_6166

theorem node_11060 : Outcome ⟨1, 11, 12, 16⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 10⟩) (by decide) node_6166

theorem node_11061 : Outcome ⟨1, 12, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 11, 2⟩, ⟨1, 11, 11, 2⟩, ⟨1, 10, 11, 4⟩, ⟨1, 12, 10, 2⟩, ⟨1, 12, 9, 4⟩]
  exact AllWinning.cons node_9902 (AllWinning.cons node_9976 (AllWinning.cons node_9009 (AllWinning.cons node_9980 (AllWinning.cons node_9018 (AllWinning.nil)))))

theorem node_11062 : Outcome ⟨1, 12, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 6⟩) (by decide) node_8028

theorem node_11063 : Outcome ⟨1, 12, 11, 6⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 10⟩) (by decide) node_6141

theorem node_11064 : Outcome ⟨1, 12, 11, 16⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 10⟩) (by decide) node_6141

theorem node_11065 : Outcome ⟨1, 13, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 2⟩) (by decide) node_9984

theorem node_11066 : Outcome ⟨1, 13, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 2⟩) (by decide) node_9984

theorem node_11067 : Outcome ⟨1, 13, 10, 14⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 2⟩) (by decide) node_9984

theorem node_11068 : Outcome ⟨1, 14, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 9, 2⟩) (by decide) node_9906

theorem node_11069 : Outcome ⟨1, 14, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 9, 2⟩) (by decide) node_9906

theorem node_11070 : Outcome ⟨1, 14, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 9, 2⟩) (by decide) node_9906

theorem node_11071 : Outcome ⟨1, 15, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 8, 2⟩, ⟨1, 14, 8, 2⟩, ⟨1, 13, 8, 4⟩, ⟨1, 15, 7, 2⟩, ⟨1, 15, 6, 4⟩]
  exact AllWinning.cons node_9910 (AllWinning.cons node_9989 (AllWinning.cons node_9021 (AllWinning.cons node_9992 (AllWinning.cons node_9025 (AllWinning.nil)))))

theorem node_11072 : Outcome ⟨1, 15, 8, 6⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 8⟩) (by decide) node_7090

theorem node_11073 : Outcome ⟨1, 15, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 8⟩) (by decide) node_7090

theorem node_11074 : Outcome ⟨1, 15, 8, 16⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 8⟩) (by decide) node_7090

theorem node_11075 : Outcome ⟨1, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 2⟩) (by decide) node_9997

theorem node_11076 : Outcome ⟨1, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 2⟩) (by decide) node_9997

theorem node_11077 : Outcome ⟨1, 16, 7, 16⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 10⟩) (by decide) node_6166

theorem node_11078 : Outcome ⟨1, 16, 7, 20⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 10⟩) (by decide) node_6166

theorem node_11079 : Outcome ⟨1, 17, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 2⟩) (by decide) node_9997

theorem node_11080 : Outcome ⟨1, 17, 6, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 28⟩) (by decide) node_1232

theorem node_11081 : Outcome ⟨1, 17, 6, 16⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 28⟩) (by decide) node_1232

theorem node_11082 : Outcome ⟨1, 18, 5, 6⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 2⟩) (by decide) node_9921

theorem node_11083 : Outcome ⟨1, 18, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 2⟩) (by decide) node_9921

theorem node_11084 : Outcome ⟨1, 18, 5, 22⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 18⟩) (by decide) node_3444

theorem node_11085 : Outcome ⟨1, 19, 4, 2⟩ true :=
  Outcome.win (q := ⟨1, 18, 4, 2⟩) (by decide) node_10009

theorem node_11086 : Outcome ⟨1, 19, 4, 16⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 8⟩) (by decide) node_7090

theorem node_11087 : Outcome ⟨1, 19, 4, 26⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 34⟩) (by decide) node_520

theorem node_11088 : Outcome ⟨1, 20, 3, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 2⟩) (by decide) node_10014

theorem node_11089 : Outcome ⟨2, 2, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 20, 4⟩) (by decide) node_8905

theorem node_11090 : Outcome ⟨2, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 2⟩) (by decide) node_9934

theorem node_11091 : Outcome ⟨2, 3, 19, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 2⟩) (by decide) node_9934

theorem node_11092 : Outcome ⟨2, 3, 19, 18⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 24⟩) (by decide) node_2005

theorem node_11093 : Outcome ⟨2, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 18, 4⟩) (by decide) node_9053

theorem node_11094 : Outcome ⟨2, 4, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 8⟩) (by decide) node_7132

theorem node_11095 : Outcome ⟨2, 4, 18, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 8⟩) (by decide) node_7132

theorem node_11096 : Outcome ⟨2, 4, 18, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 34⟩) (by decide) node_592

theorem node_11097 : Outcome ⟨2, 4, 18, 24⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 34⟩) (by decide) node_592

theorem node_11098 : Outcome ⟨2, 5, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 15, 4⟩) (by decide) node_9066

theorem node_11099 : Outcome ⟨2, 5, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 8⟩) (by decide) node_7119

theorem node_11100 : Outcome ⟨2, 5, 17, 10⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 14⟩) (by decide) node_4749

theorem node_11101 : Outcome ⟨2, 5, 17, 12⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 14⟩) (by decide) node_4749

theorem node_11102 : Outcome ⟨2, 6, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 16, 2⟩) (by decide) node_9951

theorem node_11103 : Outcome ⟨2, 6, 16, 8⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11104 : Outcome ⟨2, 6, 16, 20⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11105 : Outcome ⟨2, 6, 16, 24⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11106 : Outcome ⟨2, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 15, 4⟩) (by decide) node_8924

theorem node_11107 : Outcome ⟨2, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 6⟩) (by decide) node_8091

theorem node_11108 : Outcome ⟨2, 7, 15, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 6⟩) (by decide) node_8091

theorem node_11109 : Outcome ⟨2, 7, 15, 20⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 24⟩) (by decide) node_2035

theorem node_11110 : Outcome ⟨2, 8, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 8⟩) (by decide) node_7132

theorem node_11111 : Outcome ⟨2, 8, 14, 10⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 8⟩) (by decide) node_7132

theorem node_11112 : Outcome ⟨2, 9, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 2⟩) (by decide) node_9967

theorem node_11113 : Outcome ⟨2, 9, 13, 10⟩ true :=
  Outcome.win (q := ⟨1, 9, 13, 2⟩) (by decide) node_9967

theorem node_11114 : Outcome ⟨2, 10, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 10, 12, 2⟩, ⟨0, 10, 12, 4⟩, ⟨2, 9, 12, 2⟩, ⟨2, 8, 12, 4⟩, ⟨2, 10, 11, 2⟩, ⟨2, 10, 10, 4⟩]
  exact AllWinning.cons node_9972 (AllWinning.cons node_8935 (AllWinning.cons node_10046 (AllWinning.cons node_9077 (AllWinning.cons node_10049 (AllWinning.cons node_9084 (AllWinning.nil))))))

theorem node_11115 : Outcome ⟨2, 10, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 12, 6⟩) (by decide) node_8091

theorem node_11116 : Outcome ⟨2, 10, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 14⟩) (by decide) node_4778

theorem node_11117 : Outcome ⟨2, 11, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 4⟩) (by decide) node_8939

theorem node_11118 : Outcome ⟨2, 11, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 4⟩) (by decide) node_8939

theorem node_11119 : Outcome ⟨2, 11, 11, 6⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11120 : Outcome ⟨2, 11, 11, 12⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11121 : Outcome ⟨2, 11, 11, 14⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 10⟩) (by decide) node_6221

theorem node_11122 : Outcome ⟨2, 12, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 12, 10, 2⟩, ⟨0, 12, 10, 4⟩, ⟨2, 11, 10, 2⟩, ⟨2, 10, 10, 4⟩, ⟨2, 12, 9, 2⟩, ⟨2, 12, 8, 4⟩]
  exact AllWinning.cons node_9980 (AllWinning.cons node_8947 (AllWinning.cons node_10055 (AllWinning.cons node_9084 (AllWinning.cons node_10061 (AllWinning.cons node_9090 (AllWinning.nil))))))

theorem node_11123 : Outcome ⟨2, 12, 10, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 6⟩) (by decide) node_8117

theorem node_11124 : Outcome ⟨2, 12, 10, 8⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 14⟩) (by decide) node_4749

theorem node_11125 : Outcome ⟨2, 13, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 2⟩) (by decide) node_9984

theorem node_11126 : Outcome ⟨2, 13, 9, 10⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 2⟩) (by decide) node_9984

theorem node_11127 : Outcome ⟨2, 14, 8, 8⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 8⟩) (by decide) node_7178

theorem node_11128 : Outcome ⟨2, 14, 8, 10⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 8⟩) (by decide) node_7178

theorem node_11129 : Outcome ⟨2, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 7, 4⟩) (by decide) node_8957

theorem node_11130 : Outcome ⟨2, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 6⟩) (by decide) node_8117

theorem node_11131 : Outcome ⟨2, 15, 7, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 7, 6⟩) (by decide) node_8117

theorem node_11132 : Outcome ⟨2, 15, 7, 20⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 24⟩) (by decide) node_2005

theorem node_11133 : Outcome ⟨2, 16, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 2⟩) (by decide) node_9997

theorem node_11134 : Outcome ⟨2, 16, 6, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 10⟩) (by decide) node_6245

theorem node_11135 : Outcome ⟨2, 16, 6, 20⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 10⟩) (by decide) node_6245

theorem node_11136 : Outcome ⟨2, 16, 6, 24⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 10⟩) (by decide) node_6245

theorem node_11137 : Outcome ⟨2, 17, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 5, 4⟩) (by decide) node_9102

theorem node_11138 : Outcome ⟨2, 17, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 8⟩) (by decide) node_7192

theorem node_11139 : Outcome ⟨2, 17, 5, 10⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 14⟩) (by decide) node_4778

theorem node_11140 : Outcome ⟨2, 17, 5, 12⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 14⟩) (by decide) node_4778

theorem node_11141 : Outcome ⟨2, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨2, 18, 2, 4⟩) (by decide) node_9115

theorem node_11142 : Outcome ⟨2, 18, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 8⟩) (by decide) node_7178

theorem node_11143 : Outcome ⟨2, 18, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 8⟩) (by decide) node_7178

theorem node_11144 : Outcome ⟨2, 18, 4, 18⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 34⟩) (by decide) node_570

theorem node_11145 : Outcome ⟨2, 18, 4, 24⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 34⟩) (by decide) node_570

theorem node_11146 : Outcome ⟨2, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 2⟩) (by decide) node_10014

theorem node_11147 : Outcome ⟨2, 19, 3, 10⟩ true :=
  Outcome.win (q := ⟨1, 19, 3, 2⟩) (by decide) node_10014

theorem node_11148 : Outcome ⟨2, 19, 3, 18⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 24⟩) (by decide) node_2035

theorem node_11149 : Outcome ⟨2, 20, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 20, 2, 4⟩) (by decide) node_8977

theorem node_11150 : Outcome ⟨3, 1, 20, 2⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 2⟩) (by decide) node_10089

theorem node_11151 : Outcome ⟨3, 2, 19, 2⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 2⟩) (by decide) node_10089

theorem node_11152 : Outcome ⟨3, 2, 19, 10⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 2⟩) (by decide) node_10089

theorem node_11153 : Outcome ⟨3, 2, 19, 18⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 24⟩) (by decide) node_2076

theorem node_11154 : Outcome ⟨3, 3, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 3, 18, 2⟩, ⟨1, 3, 18, 4⟩, ⟨3, 2, 18, 2⟩, ⟨3, 1, 18, 4⟩, ⟨3, 3, 17, 2⟩, ⟨3, 3, 16, 4⟩]
  exact AllWinning.cons node_10026 (AllWinning.cons node_8986 (AllWinning.cons node_10096 (AllWinning.cons node_9129 (AllWinning.cons node_10100 (AllWinning.cons node_9135 (AllWinning.nil))))))

theorem node_11155 : Outcome ⟨3, 3, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 3, 18, 2⟩, ⟨1, 3, 18, 4⟩, ⟨0, 3, 18, 6⟩, ⟨3, 2, 18, 2⟩, ⟨3, 1, 18, 4⟩, ⟨3, 0, 18, 6⟩, ⟨3, 3, 17, 2⟩, ⟨3, 3, 16, 4⟩, ⟨3, 3, 15, 6⟩, ⟨3, 3, 14, 8⟩]
  exact AllWinning.cons node_10026 (AllWinning.cons node_8986 (AllWinning.cons node_7914 (AllWinning.cons node_10096 (AllWinning.cons node_9129 (AllWinning.cons node_8148 (AllWinning.cons node_10100 (AllWinning.cons node_9135 (AllWinning.cons node_8159 (AllWinning.cons node_7213 (AllWinning.nil))))))))))

theorem node_11156 : Outcome ⟨3, 3, 18, 24⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 36⟩) (by decide) node_442

theorem node_11157 : Outcome ⟨3, 4, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 4, 17, 2⟩, ⟨1, 4, 17, 4⟩, ⟨3, 3, 17, 2⟩, ⟨3, 2, 17, 4⟩, ⟨3, 4, 16, 2⟩, ⟨3, 4, 15, 4⟩]
  exact AllWinning.cons node_10030 (AllWinning.cons node_8989 (AllWinning.cons node_10100 (AllWinning.cons node_9131 (AllWinning.cons node_10102 (AllWinning.cons node_9137 (AllWinning.nil))))))

theorem node_11158 : Outcome ⟨3, 4, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 6⟩) (by decide) node_7918

theorem node_11159 : Outcome ⟨3, 4, 17, 10⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 6⟩) (by decide) node_7918

theorem node_11160 : Outcome ⟨3, 4, 17, 20⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 6⟩) (by decide) node_7918

theorem node_11161 : Outcome ⟨3, 5, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 5, 16, 2⟩, ⟨1, 5, 16, 4⟩, ⟨3, 4, 16, 2⟩, ⟨3, 3, 16, 4⟩, ⟨3, 5, 15, 2⟩, ⟨3, 5, 14, 4⟩]
  exact AllWinning.cons node_10035 (AllWinning.cons node_8995 (AllWinning.cons node_10102 (AllWinning.cons node_9135 (AllWinning.cons node_10105 (AllWinning.cons node_9141 (AllWinning.nil))))))

theorem node_11162 : Outcome ⟨3, 5, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 5, 16, 2⟩, ⟨1, 5, 16, 4⟩, ⟨0, 5, 16, 6⟩, ⟨3, 4, 16, 2⟩, ⟨3, 3, 16, 4⟩, ⟨3, 2, 16, 6⟩, ⟨3, 1, 16, 8⟩, ⟨3, 5, 15, 2⟩, ⟨3, 5, 14, 4⟩, ⟨3, 5, 13, 6⟩, ⟨3, 5, 12, 8⟩]
  exact AllWinning.cons node_10035 (AllWinning.cons node_8995 (AllWinning.cons node_7923 (AllWinning.cons node_10102 (AllWinning.cons node_9135 (AllWinning.cons node_8154 (AllWinning.cons node_7203 (AllWinning.cons node_10105 (AllWinning.cons node_9141 (AllWinning.cons node_8166 (AllWinning.cons node_7218 (AllWinning.nil)))))))))))

theorem node_11163 : Outcome ⟨3, 5, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 16, 10⟩) (by decide) node_6276

theorem node_11164 : Outcome ⟨3, 6, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 2⟩) (by decide) node_10109

theorem node_11165 : Outcome ⟨3, 6, 15, 16⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 28⟩) (by decide) node_1363

theorem node_11166 : Outcome ⟨3, 6, 15, 24⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 28⟩) (by decide) node_1363

theorem node_11167 : Outcome ⟨3, 7, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 2⟩) (by decide) node_10109

theorem node_11168 : Outcome ⟨3, 7, 14, 8⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 2⟩) (by decide) node_10109

theorem node_11169 : Outcome ⟨3, 7, 14, 20⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 24⟩) (by decide) node_2107

theorem node_11170 : Outcome ⟨3, 8, 13, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 13, 2⟩) (by decide) node_10115

theorem node_11171 : Outcome ⟨3, 8, 13, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 13, 10⟩) (by decide) node_6292

theorem node_11172 : Outcome ⟨3, 9, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.nil))))))

theorem node_11173 : Outcome ⟨3, 9, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.nil)))))))))))

theorem node_11174 : Outcome ⟨3, 9, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.nil)))))))))))))))

theorem node_11175 : Outcome ⟨3, 9, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.nil)))))))))))))))))))

theorem node_11176 : Outcome ⟨3, 9, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 0, 12, 18⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩, ⟨3, 9, 3, 18⟩, ⟨3, 9, 2, 20⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_3538 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.cons node_3571 (AllWinning.cons node_3032 (AllWinning.nil))))))))))))))))))))))

theorem node_11177 : Outcome ⟨3, 9, 12, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 0, 12, 18⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩, ⟨3, 9, 3, 18⟩, ⟨3, 9, 2, 20⟩, ⟨3, 9, 1, 22⟩, ⟨3, 9, 0, 24⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_3538 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.cons node_3571 (AllWinning.cons node_3032 (AllWinning.cons node_2572 (AllWinning.cons node_2121 (AllWinning.nil))))))))))))))))))))))))

theorem node_11178 : Outcome ⟨3, 9, 12, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 0, 12, 18⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩, ⟨3, 9, 3, 18⟩, ⟨3, 9, 2, 20⟩, ⟨3, 9, 1, 22⟩, ⟨3, 9, 0, 24⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_3538 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.cons node_3571 (AllWinning.cons node_3032 (AllWinning.cons node_2572 (AllWinning.cons node_2121 (AllWinning.nil))))))))))))))))))))))))

theorem node_11179 : Outcome ⟨3, 9, 12, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 0, 12, 18⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩, ⟨3, 9, 3, 18⟩, ⟨3, 9, 2, 20⟩, ⟨3, 9, 1, 22⟩, ⟨3, 9, 0, 24⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_3538 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.cons node_3571 (AllWinning.cons node_3032 (AllWinning.cons node_2572 (AllWinning.cons node_2121 (AllWinning.nil))))))))))))))))))))))))

theorem node_11180 : Outcome ⟨3, 9, 12, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 0, 12, 18⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩, ⟨3, 9, 3, 18⟩, ⟨3, 9, 2, 20⟩, ⟨3, 9, 1, 22⟩, ⟨3, 9, 0, 24⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_3538 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.cons node_3571 (AllWinning.cons node_3032 (AllWinning.cons node_2572 (AllWinning.cons node_2121 (AllWinning.nil))))))))))))))))))))))))

theorem node_11181 : Outcome ⟨3, 9, 12, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 0, 12, 18⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩, ⟨3, 9, 3, 18⟩, ⟨3, 9, 2, 20⟩, ⟨3, 9, 1, 22⟩, ⟨3, 9, 0, 24⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_3538 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.cons node_3571 (AllWinning.cons node_3032 (AllWinning.cons node_2572 (AllWinning.cons node_2121 (AllWinning.nil))))))))))))))))))))))))

theorem node_11182 : Outcome ⟨3, 9, 12, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 12, 2⟩, ⟨1, 9, 12, 4⟩, ⟨0, 9, 12, 6⟩, ⟨3, 8, 12, 2⟩, ⟨3, 7, 12, 4⟩, ⟨3, 6, 12, 6⟩, ⟨3, 5, 12, 8⟩, ⟨3, 4, 12, 10⟩, ⟨3, 3, 12, 12⟩, ⟨3, 2, 12, 14⟩, ⟨3, 1, 12, 16⟩, ⟨3, 0, 12, 18⟩, ⟨3, 9, 11, 2⟩, ⟨3, 9, 10, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 9, 8, 8⟩, ⟨3, 9, 7, 10⟩, ⟨3, 9, 6, 12⟩, ⟨3, 9, 5, 14⟩, ⟨3, 9, 4, 16⟩, ⟨3, 9, 3, 18⟩, ⟨3, 9, 2, 20⟩, ⟨3, 9, 1, 22⟩, ⟨3, 9, 0, 24⟩]
  exact AllWinning.cons node_10046 (AllWinning.cons node_9007 (AllWinning.cons node_7939 (AllWinning.cons node_10119 (AllWinning.cons node_9147 (AllWinning.cons node_8169 (AllWinning.cons node_7218 (AllWinning.cons node_6297 (AllWinning.cons node_5532 (AllWinning.cons node_4822 (AllWinning.cons node_4104 (AllWinning.cons node_3538 (AllWinning.cons node_10122 (AllWinning.cons node_9157 (AllWinning.cons node_8183 (AllWinning.cons node_7235 (AllWinning.cons node_6324 (AllWinning.cons node_5556 (AllWinning.cons node_4851 (AllWinning.cons node_4134 (AllWinning.cons node_3571 (AllWinning.cons node_3032 (AllWinning.cons node_2572 (AllWinning.cons node_2121 (AllWinning.nil))))))))))))))))))))))))

theorem node_11183 : Outcome ⟨3, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 10, 2⟩) (by decide) node_10126

theorem node_11184 : Outcome ⟨3, 10, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 10, 2⟩) (by decide) node_10126

theorem node_11185 : Outcome ⟨3, 10, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 10⟩) (by decide) node_6303

theorem node_11186 : Outcome ⟨3, 10, 11, 10⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 10⟩) (by decide) node_6303

theorem node_11187 : Outcome ⟨3, 10, 11, 18⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 10⟩) (by decide) node_6303

theorem node_11188 : Outcome ⟨3, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 10, 2⟩) (by decide) node_10126

theorem node_11189 : Outcome ⟨3, 11, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 10, 2⟩) (by decide) node_10126

theorem node_11190 : Outcome ⟨3, 11, 10, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 10⟩) (by decide) node_6334

theorem node_11191 : Outcome ⟨3, 11, 10, 10⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 10⟩) (by decide) node_6334

theorem node_11192 : Outcome ⟨3, 11, 10, 18⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 10⟩) (by decide) node_6334

theorem node_11193 : Outcome ⟨3, 12, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.nil))))))

theorem node_11194 : Outcome ⟨3, 12, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.nil)))))))))))

theorem node_11195 : Outcome ⟨3, 12, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.nil)))))))))))))))

theorem node_11196 : Outcome ⟨3, 12, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.nil)))))))))))))))))))

theorem node_11197 : Outcome ⟨3, 12, 9, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 3, 9, 18⟩, ⟨3, 2, 9, 20⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩, ⟨3, 12, 0, 18⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_3550 (AllWinning.cons node_3003 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.cons node_3582 (AllWinning.nil))))))))))))))))))))))

theorem node_11198 : Outcome ⟨3, 12, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 3, 9, 18⟩, ⟨3, 2, 9, 20⟩, ⟨3, 1, 9, 22⟩, ⟨3, 0, 9, 24⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩, ⟨3, 12, 0, 18⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_3550 (AllWinning.cons node_3003 (AllWinning.cons node_2538 (AllWinning.cons node_2058 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.cons node_3582 (AllWinning.nil))))))))))))))))))))))))

theorem node_11199 : Outcome ⟨3, 12, 9, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 3, 9, 18⟩, ⟨3, 2, 9, 20⟩, ⟨3, 1, 9, 22⟩, ⟨3, 0, 9, 24⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩, ⟨3, 12, 0, 18⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_3550 (AllWinning.cons node_3003 (AllWinning.cons node_2538 (AllWinning.cons node_2058 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.cons node_3582 (AllWinning.nil))))))))))))))))))))))))

theorem node_11200 : Outcome ⟨3, 12, 9, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 3, 9, 18⟩, ⟨3, 2, 9, 20⟩, ⟨3, 1, 9, 22⟩, ⟨3, 0, 9, 24⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩, ⟨3, 12, 0, 18⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_3550 (AllWinning.cons node_3003 (AllWinning.cons node_2538 (AllWinning.cons node_2058 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.cons node_3582 (AllWinning.nil))))))))))))))))))))))))

theorem node_11201 : Outcome ⟨3, 12, 9, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 3, 9, 18⟩, ⟨3, 2, 9, 20⟩, ⟨3, 1, 9, 22⟩, ⟨3, 0, 9, 24⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩, ⟨3, 12, 0, 18⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_3550 (AllWinning.cons node_3003 (AllWinning.cons node_2538 (AllWinning.cons node_2058 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.cons node_3582 (AllWinning.nil))))))))))))))))))))))))

theorem node_11202 : Outcome ⟨3, 12, 9, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 3, 9, 18⟩, ⟨3, 2, 9, 20⟩, ⟨3, 1, 9, 22⟩, ⟨3, 0, 9, 24⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩, ⟨3, 12, 0, 18⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_3550 (AllWinning.cons node_3003 (AllWinning.cons node_2538 (AllWinning.cons node_2058 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.cons node_3582 (AllWinning.nil))))))))))))))))))))))))

theorem node_11203 : Outcome ⟨3, 12, 9, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 12, 9, 2⟩, ⟨1, 12, 9, 4⟩, ⟨0, 12, 9, 6⟩, ⟨3, 11, 9, 2⟩, ⟨3, 10, 9, 4⟩, ⟨3, 9, 9, 6⟩, ⟨3, 8, 9, 8⟩, ⟨3, 7, 9, 10⟩, ⟨3, 6, 9, 12⟩, ⟨3, 5, 9, 14⟩, ⟨3, 4, 9, 16⟩, ⟨3, 3, 9, 18⟩, ⟨3, 2, 9, 20⟩, ⟨3, 1, 9, 22⟩, ⟨3, 0, 9, 24⟩, ⟨3, 12, 8, 2⟩, ⟨3, 12, 7, 4⟩, ⟨3, 12, 6, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 12, 4, 10⟩, ⟨3, 12, 3, 12⟩, ⟨3, 12, 2, 14⟩, ⟨3, 12, 1, 16⟩, ⟨3, 12, 0, 18⟩]
  exact AllWinning.cons node_10061 (AllWinning.cons node_9018 (AllWinning.cons node_7948 (AllWinning.cons node_10129 (AllWinning.cons node_9161 (AllWinning.cons node_8183 (AllWinning.cons node_7230 (AllWinning.cons node_6315 (AllWinning.cons node_5541 (AllWinning.cons node_4832 (AllWinning.cons node_4113 (AllWinning.cons node_3550 (AllWinning.cons node_3003 (AllWinning.cons node_2538 (AllWinning.cons node_2058 (AllWinning.cons node_10133 (AllWinning.cons node_9170 (AllWinning.cons node_8196 (AllWinning.cons node_7247 (AllWinning.cons node_6343 (AllWinning.cons node_5562 (AllWinning.cons node_4860 (AllWinning.cons node_4146 (AllWinning.cons node_3582 (AllWinning.nil))))))))))))))))))))))))

theorem node_11204 : Outcome ⟨3, 13, 8, 4⟩ true :=
  Outcome.win (q := ⟨3, 13, 7, 2⟩) (by decide) node_10136

theorem node_11205 : Outcome ⟨3, 13, 8, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 3, 10⟩) (by decide) node_6349

theorem node_11206 : Outcome ⟨3, 14, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 13, 7, 2⟩) (by decide) node_10136

theorem node_11207 : Outcome ⟨3, 14, 7, 8⟩ true :=
  Outcome.win (q := ⟨3, 13, 7, 2⟩) (by decide) node_10136

theorem node_11208 : Outcome ⟨3, 14, 7, 20⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 24⟩) (by decide) node_2076

theorem node_11209 : Outcome ⟨3, 15, 6, 2⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 2⟩) (by decide) node_10140

theorem node_11210 : Outcome ⟨3, 15, 6, 16⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 28⟩) (by decide) node_1332

theorem node_11211 : Outcome ⟨3, 15, 6, 24⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 28⟩) (by decide) node_1332

theorem node_11212 : Outcome ⟨3, 16, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 5, 2⟩, ⟨1, 16, 5, 4⟩, ⟨3, 15, 5, 2⟩, ⟨3, 14, 5, 4⟩, ⟨3, 16, 4, 2⟩, ⟨3, 16, 3, 4⟩]
  exact AllWinning.cons node_10072 (AllWinning.cons node_9030 (AllWinning.cons node_10147 (AllWinning.cons node_9178 (AllWinning.cons node_10151 (AllWinning.cons node_9184 (AllWinning.nil))))))

theorem node_11213 : Outcome ⟨3, 16, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 5, 2⟩, ⟨1, 16, 5, 4⟩, ⟨0, 16, 5, 6⟩, ⟨3, 15, 5, 2⟩, ⟨3, 14, 5, 4⟩, ⟨3, 13, 5, 6⟩, ⟨3, 12, 5, 8⟩, ⟨3, 16, 4, 2⟩, ⟨3, 16, 3, 4⟩, ⟨3, 16, 2, 6⟩, ⟨3, 16, 1, 8⟩]
  exact AllWinning.cons node_10072 (AllWinning.cons node_9030 (AllWinning.cons node_7962 (AllWinning.cons node_10147 (AllWinning.cons node_9178 (AllWinning.cons node_8199 (AllWinning.cons node_7247 (AllWinning.cons node_10151 (AllWinning.cons node_9184 (AllWinning.cons node_8209 (AllWinning.cons node_7262 (AllWinning.nil)))))))))))

theorem node_11214 : Outcome ⟨3, 16, 5, 6⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 10⟩) (by decide) node_6334

theorem node_11215 : Outcome ⟨3, 17, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 17, 4, 2⟩, ⟨1, 17, 4, 4⟩, ⟨3, 16, 4, 2⟩, ⟨3, 15, 4, 4⟩, ⟨3, 17, 3, 2⟩, ⟨3, 17, 2, 4⟩]
  exact AllWinning.cons node_10075 (AllWinning.cons node_9033 (AllWinning.cons node_10151 (AllWinning.cons node_9180 (AllWinning.cons node_10154 (AllWinning.cons node_9186 (AllWinning.nil))))))

theorem node_11216 : Outcome ⟨3, 17, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 6⟩) (by decide) node_7966

theorem node_11217 : Outcome ⟨3, 17, 4, 10⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 6⟩) (by decide) node_7966

theorem node_11218 : Outcome ⟨3, 17, 4, 20⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 6⟩) (by decide) node_7966

theorem node_11219 : Outcome ⟨3, 18, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 18, 3, 2⟩, ⟨1, 18, 3, 4⟩, ⟨3, 17, 3, 2⟩, ⟨3, 16, 3, 4⟩, ⟨3, 18, 2, 2⟩, ⟨3, 18, 1, 4⟩]
  exact AllWinning.cons node_10080 (AllWinning.cons node_9039 (AllWinning.cons node_10154 (AllWinning.cons node_9184 (AllWinning.cons node_10156 (AllWinning.cons node_9190 (AllWinning.nil))))))

theorem node_11220 : Outcome ⟨3, 18, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 18, 3, 2⟩, ⟨1, 18, 3, 4⟩, ⟨0, 18, 3, 6⟩, ⟨3, 17, 3, 2⟩, ⟨3, 16, 3, 4⟩, ⟨3, 15, 3, 6⟩, ⟨3, 14, 3, 8⟩, ⟨3, 18, 2, 2⟩, ⟨3, 18, 1, 4⟩, ⟨3, 18, 0, 6⟩]
  exact AllWinning.cons node_10080 (AllWinning.cons node_9039 (AllWinning.cons node_7971 (AllWinning.cons node_10154 (AllWinning.cons node_9184 (AllWinning.cons node_8205 (AllWinning.cons node_7254 (AllWinning.cons node_10156 (AllWinning.cons node_9190 (AllWinning.cons node_8217 (AllWinning.nil))))))))))

theorem node_11221 : Outcome ⟨3, 18, 3, 24⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 36⟩) (by decide) node_419

theorem node_11222 : Outcome ⟨3, 19, 2, 2⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 2⟩) (by decide) node_10160

theorem node_11223 : Outcome ⟨3, 19, 2, 10⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 2⟩) (by decide) node_10160

theorem node_11224 : Outcome ⟨3, 19, 2, 18⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 24⟩) (by decide) node_2107

theorem node_11225 : Outcome ⟨3, 20, 1, 2⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 2⟩) (by decide) node_10160

theorem node_11226 : Outcome ⟨4, 0, 20, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 20, 4⟩) (by decide) node_9046

theorem node_11227 : Outcome ⟨4, 0, 20, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 6⟩) (by decide) node_8221

theorem node_11228 : Outcome ⟨4, 0, 20, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 6⟩) (by decide) node_8221

theorem node_11229 : Outcome ⟨4, 1, 19, 2⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 2⟩) (by decide) node_10089

theorem node_11230 : Outcome ⟨4, 1, 19, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 8⟩) (by decide) node_7273

theorem node_11231 : Outcome ⟨4, 2, 18, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 18, 4⟩) (by decide) node_9053

theorem node_11232 : Outcome ⟨4, 2, 18, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 8⟩) (by decide) node_7280

theorem node_11233 : Outcome ⟨4, 2, 18, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 8⟩) (by decide) node_7280

theorem node_11234 : Outcome ⟨4, 2, 18, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 34⟩) (by decide) node_650

theorem node_11235 : Outcome ⟨4, 2, 18, 24⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 34⟩) (by decide) node_650

theorem node_11236 : Outcome ⟨4, 3, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 3, 17, 2⟩, ⟨2, 3, 17, 4⟩, ⟨4, 2, 17, 2⟩, ⟨4, 1, 17, 4⟩, ⟨4, 3, 16, 2⟩, ⟨4, 3, 15, 4⟩]
  exact AllWinning.cons node_10100 (AllWinning.cons node_9056 (AllWinning.cons node_10175 (AllWinning.cons node_9200 (AllWinning.cons node_10180 (AllWinning.cons node_9209 (AllWinning.nil))))))

theorem node_11237 : Outcome ⟨4, 3, 17, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 6⟩) (by decide) node_8221

theorem node_11238 : Outcome ⟨4, 3, 17, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 6⟩) (by decide) node_8221

theorem node_11239 : Outcome ⟨4, 3, 17, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 6⟩) (by decide) node_8221

theorem node_11240 : Outcome ⟨4, 4, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 16, 2⟩, ⟨2, 4, 16, 4⟩, ⟨4, 3, 16, 2⟩, ⟨4, 2, 16, 4⟩, ⟨4, 4, 15, 2⟩, ⟨4, 4, 14, 4⟩]
  exact AllWinning.cons node_10102 (AllWinning.cons node_9060 (AllWinning.cons node_10180 (AllWinning.cons node_9205 (AllWinning.cons node_10183 (AllWinning.cons node_9211 (AllWinning.nil))))))

theorem node_11241 : Outcome ⟨4, 4, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 6⟩) (by decide) node_8235

theorem node_11242 : Outcome ⟨4, 4, 16, 10⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 6⟩) (by decide) node_8235

theorem node_11243 : Outcome ⟨4, 5, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 15, 4⟩) (by decide) node_9066

theorem node_11244 : Outcome ⟨4, 5, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 15, 8⟩) (by decide) node_7273

theorem node_11245 : Outcome ⟨4, 5, 15, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 16⟩) (by decide) node_4177

theorem node_11246 : Outcome ⟨4, 5, 15, 10⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 16⟩) (by decide) node_4177

theorem node_11247 : Outcome ⟨4, 6, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 2⟩) (by decide) node_10109

theorem node_11248 : Outcome ⟨4, 6, 14, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 8⟩) (by decide) node_7280

theorem node_11249 : Outcome ⟨4, 6, 14, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 8⟩) (by decide) node_7280

theorem node_11250 : Outcome ⟨4, 7, 13, 2⟩ true :=
  Outcome.win (q := ⟨3, 7, 13, 2⟩) (by decide) node_10115

theorem node_11251 : Outcome ⟨4, 7, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 6⟩) (by decide) node_8235

theorem node_11252 : Outcome ⟨4, 7, 13, 10⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 16⟩) (by decide) node_4194

theorem node_11253 : Outcome ⟨4, 8, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 8, 12, 2⟩, ⟨2, 8, 12, 4⟩, ⟨4, 7, 12, 2⟩, ⟨4, 6, 12, 4⟩, ⟨4, 8, 11, 2⟩, ⟨4, 8, 10, 4⟩]
  exact AllWinning.cons node_10119 (AllWinning.cons node_9077 (AllWinning.cons node_10194 (AllWinning.cons node_9218 (AllWinning.cons node_10199 (AllWinning.cons node_9229 (AllWinning.nil))))))

theorem node_11254 : Outcome ⟨4, 8, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 6⟩) (by decide) node_8007

theorem node_11255 : Outcome ⟨4, 8, 12, 10⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 6⟩) (by decide) node_8007

theorem node_11256 : Outcome ⟨4, 9, 11, 2⟩ true :=
  Outcome.win (q := ⟨4, 9, 10, 2⟩) (by decide) node_10204

theorem node_11257 : Outcome ⟨4, 9, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 10, 2⟩) (by decide) node_10204

theorem node_11258 : Outcome ⟨4, 9, 11, 10⟩ true :=
  Outcome.win (q := ⟨4, 9, 10, 2⟩) (by decide) node_10204

end RQ9F1
