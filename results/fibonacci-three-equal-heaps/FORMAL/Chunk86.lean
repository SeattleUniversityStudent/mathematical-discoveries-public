import Chunk85
set_option autoImplicit false
namespace RQ9F1

theorem node_18859 : Outcome ⟨1, 17, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 2⟩) (by decide) node_17934

theorem node_18860 : Outcome ⟨1, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 13, 2⟩) (by decide) node_17897

theorem node_18861 : Outcome ⟨1, 18, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 13, 2⟩) (by decide) node_17897

theorem node_18862 : Outcome ⟨1, 18, 13, 12⟩ true :=
  Outcome.win (q := ⟨0, 18, 13, 2⟩) (by decide) node_17897

theorem node_18863 : Outcome ⟨1, 19, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 12, 2⟩, ⟨1, 18, 12, 2⟩, ⟨1, 17, 12, 4⟩, ⟨1, 19, 11, 2⟩, ⟨1, 19, 10, 4⟩]
  exact AllWinning.cons node_17901 (AllWinning.cons node_17940 (AllWinning.cons node_17036 (AllWinning.cons node_17944 (AllWinning.cons node_17040 (AllWinning.nil)))))

theorem node_18864 : Outcome ⟨1, 19, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 12, 2⟩, ⟨1, 18, 12, 2⟩, ⟨1, 17, 12, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 19, 11, 2⟩, ⟨1, 19, 10, 4⟩, ⟨1, 19, 9, 6⟩, ⟨1, 19, 8, 8⟩]
  exact AllWinning.cons node_17901 (AllWinning.cons node_17940 (AllWinning.cons node_17036 (AllWinning.cons node_15969 (AllWinning.cons node_14992 (AllWinning.cons node_17944 (AllWinning.cons node_17040 (AllWinning.cons node_15979 (AllWinning.cons node_15004 (AllWinning.nil)))))))))

theorem node_18865 : Outcome ⟨1, 19, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 12, 2⟩, ⟨1, 18, 12, 2⟩, ⟨1, 17, 12, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 14, 12, 10⟩, ⟨1, 13, 12, 12⟩, ⟨1, 19, 11, 2⟩, ⟨1, 19, 10, 4⟩, ⟨1, 19, 9, 6⟩, ⟨1, 19, 8, 8⟩, ⟨1, 19, 7, 10⟩, ⟨1, 19, 6, 12⟩]
  exact AllWinning.cons node_17901 (AllWinning.cons node_17940 (AllWinning.cons node_17036 (AllWinning.cons node_15969 (AllWinning.cons node_14992 (AllWinning.cons node_14028 (AllWinning.cons node_13058 (AllWinning.cons node_17944 (AllWinning.cons node_17040 (AllWinning.cons node_15979 (AllWinning.cons node_15004 (AllWinning.cons node_14048 (AllWinning.cons node_13074 (AllWinning.nil)))))))))))))

theorem node_18866 : Outcome ⟨1, 19, 12, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 12, 2⟩, ⟨1, 18, 12, 2⟩, ⟨1, 17, 12, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 14, 12, 10⟩, ⟨1, 13, 12, 12⟩, ⟨1, 12, 12, 14⟩, ⟨1, 11, 12, 16⟩, ⟨1, 19, 11, 2⟩, ⟨1, 19, 10, 4⟩, ⟨1, 19, 9, 6⟩, ⟨1, 19, 8, 8⟩, ⟨1, 19, 7, 10⟩, ⟨1, 19, 6, 12⟩, ⟨1, 19, 5, 14⟩, ⟨1, 19, 4, 16⟩]
  exact AllWinning.cons node_17901 (AllWinning.cons node_17940 (AllWinning.cons node_17036 (AllWinning.cons node_15969 (AllWinning.cons node_14992 (AllWinning.cons node_14028 (AllWinning.cons node_13058 (AllWinning.cons node_12048 (AllWinning.cons node_11060 (AllWinning.cons node_17944 (AllWinning.cons node_17040 (AllWinning.cons node_15979 (AllWinning.cons node_15004 (AllWinning.cons node_14048 (AllWinning.cons node_13074 (AllWinning.cons node_12078 (AllWinning.cons node_11086 (AllWinning.nil)))))))))))))))))

theorem node_18867 : Outcome ⟨1, 19, 12, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 12, 2⟩, ⟨1, 18, 12, 2⟩, ⟨1, 17, 12, 4⟩, ⟨1, 16, 12, 6⟩, ⟨1, 15, 12, 8⟩, ⟨1, 14, 12, 10⟩, ⟨1, 13, 12, 12⟩, ⟨1, 12, 12, 14⟩, ⟨1, 11, 12, 16⟩, ⟨1, 10, 12, 18⟩, ⟨1, 9, 12, 20⟩, ⟨1, 19, 11, 2⟩, ⟨1, 19, 10, 4⟩, ⟨1, 19, 9, 6⟩, ⟨1, 19, 8, 8⟩, ⟨1, 19, 7, 10⟩, ⟨1, 19, 6, 12⟩, ⟨1, 19, 5, 14⟩, ⟨1, 19, 4, 16⟩, ⟨1, 19, 3, 18⟩, ⟨1, 19, 2, 20⟩]
  exact AllWinning.cons node_17901 (AllWinning.cons node_17940 (AllWinning.cons node_17036 (AllWinning.cons node_15969 (AllWinning.cons node_14992 (AllWinning.cons node_14028 (AllWinning.cons node_13058 (AllWinning.cons node_12048 (AllWinning.cons node_11060 (AllWinning.cons node_9975 (AllWinning.cons node_9008 (AllWinning.cons node_17944 (AllWinning.cons node_17040 (AllWinning.cons node_15979 (AllWinning.cons node_15004 (AllWinning.cons node_14048 (AllWinning.cons node_13074 (AllWinning.cons node_12078 (AllWinning.cons node_11086 (AllWinning.cons node_10020 (AllWinning.cons node_9044 (AllWinning.nil)))))))))))))))))))))

theorem node_18868 : Outcome ⟨1, 19, 12, 12⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 22⟩) (by decide) node_8014

theorem node_18869 : Outcome ⟨1, 20, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 20, 10, 2⟩) (by decide) node_17947

theorem node_18870 : Outcome ⟨2, 10, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 8⟩) (by decide) node_15021

theorem node_18871 : Outcome ⟨2, 10, 20, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 8⟩) (by decide) node_15021

theorem node_18872 : Outcome ⟨2, 11, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 19, 4⟩) (by decide) node_16975

theorem node_18873 : Outcome ⟨2, 11, 19, 4⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 6⟩) (by decide) node_15987

theorem node_18874 : Outcome ⟨2, 11, 19, 12⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 6⟩) (by decide) node_15987

theorem node_18875 : Outcome ⟨2, 12, 18, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 10⟩) (by decide) node_14060

theorem node_18876 : Outcome ⟨2, 12, 18, 8⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 10⟩) (by decide) node_14060

theorem node_18877 : Outcome ⟨2, 13, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 4⟩) (by decide) node_17054

theorem node_18878 : Outcome ⟨2, 13, 17, 12⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 4⟩) (by decide) node_17054

theorem node_18879 : Outcome ⟨2, 14, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 14, 16, 2⟩, ⟨0, 14, 16, 4⟩, ⟨2, 13, 16, 2⟩, ⟨2, 12, 16, 4⟩, ⟨2, 14, 15, 2⟩, ⟨2, 14, 14, 4⟩]
  exact AllWinning.cons node_17923 (AllWinning.cons node_16984 (AllWinning.cons node_17957 (AllWinning.cons node_17059 (AllWinning.cons node_17960 (AllWinning.cons node_17066 (AllWinning.nil))))))

theorem node_18880 : Outcome ⟨2, 14, 16, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 8⟩) (by decide) node_15021

theorem node_18881 : Outcome ⟨2, 14, 16, 8⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 8⟩) (by decide) node_15021

theorem node_18882 : Outcome ⟨2, 14, 16, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 8⟩) (by decide) node_15021

theorem node_18883 : Outcome ⟨2, 15, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18884 : Outcome ⟨2, 15, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 4⟩) (by decide) node_16989

theorem node_18885 : Outcome ⟨2, 15, 15, 6⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 12⟩) (by decide) node_13095

theorem node_18886 : Outcome ⟨2, 15, 15, 16⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 12⟩) (by decide) node_13095

theorem node_18887 : Outcome ⟨2, 16, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 16, 14, 2⟩, ⟨0, 16, 14, 4⟩, ⟨2, 15, 14, 2⟩, ⟨2, 14, 14, 4⟩, ⟨2, 16, 13, 2⟩, ⟨2, 16, 12, 4⟩]
  exact AllWinning.cons node_17930 (AllWinning.cons node_16994 (AllWinning.cons node_17962 (AllWinning.cons node_17066 (AllWinning.cons node_17964 (AllWinning.cons node_17073 (AllWinning.nil))))))

theorem node_18888 : Outcome ⟨2, 16, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 8⟩) (by decide) node_15028

theorem node_18889 : Outcome ⟨2, 16, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 8⟩) (by decide) node_15028

theorem node_18890 : Outcome ⟨2, 16, 14, 16⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 8⟩) (by decide) node_15028

theorem node_18891 : Outcome ⟨2, 17, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 4⟩) (by decide) node_17076

theorem node_18892 : Outcome ⟨2, 17, 13, 12⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 4⟩) (by decide) node_17076

theorem node_18893 : Outcome ⟨2, 18, 12, 6⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 10⟩) (by decide) node_14090

theorem node_18894 : Outcome ⟨2, 18, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 10⟩) (by decide) node_14090

theorem node_18895 : Outcome ⟨2, 19, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 11, 4⟩) (by decide) node_17005

theorem node_18896 : Outcome ⟨2, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 6⟩) (by decide) node_16016

theorem node_18897 : Outcome ⟨2, 19, 11, 12⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 6⟩) (by decide) node_16016

theorem node_18898 : Outcome ⟨2, 20, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 8⟩) (by decide) node_15051

theorem node_18899 : Outcome ⟨2, 20, 10, 8⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 8⟩) (by decide) node_15051

theorem node_18900 : Outcome ⟨3, 9, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 9, 20, 2⟩) (by decide) node_17950

theorem node_18901 : Outcome ⟨3, 9, 20, 6⟩ true :=
  Outcome.win (q := ⟨2, 9, 20, 2⟩) (by decide) node_17950

theorem node_18902 : Outcome ⟨3, 9, 20, 12⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 16⟩) (by decide) node_11179

theorem node_18903 : Outcome ⟨3, 10, 19, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 2⟩) (by decide) node_17977

theorem node_18904 : Outcome ⟨3, 10, 19, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 2⟩) (by decide) node_17977

theorem node_18905 : Outcome ⟨3, 11, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 2⟩) (by decide) node_17977

theorem node_18906 : Outcome ⟨3, 11, 18, 8⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 2⟩) (by decide) node_17977

theorem node_18907 : Outcome ⟨3, 12, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 15, 4⟩) (by decide) node_17100

theorem node_18908 : Outcome ⟨3, 12, 17, 6⟩ true :=
  Outcome.win (q := ⟨3, 12, 15, 4⟩) (by decide) node_17100

theorem node_18909 : Outcome ⟨3, 13, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨3, 12, 16, 2⟩, ⟨3, 11, 16, 4⟩, ⟨3, 13, 15, 2⟩, ⟨3, 13, 14, 4⟩]
  exact AllWinning.cons node_17957 (AllWinning.cons node_17024 (AllWinning.cons node_17984 (AllWinning.cons node_17097 (AllWinning.cons node_17987 (AllWinning.cons node_17105 (AllWinning.nil))))))

theorem node_18910 : Outcome ⟨3, 13, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 16, 2⟩, ⟨1, 13, 16, 4⟩, ⟨0, 13, 16, 6⟩, ⟨3, 12, 16, 2⟩, ⟨3, 11, 16, 4⟩, ⟨3, 10, 16, 6⟩, ⟨3, 9, 16, 8⟩, ⟨3, 13, 15, 2⟩, ⟨3, 13, 14, 4⟩, ⟨3, 13, 13, 6⟩, ⟨3, 13, 12, 8⟩]
  exact AllWinning.cons node_17957 (AllWinning.cons node_17024 (AllWinning.cons node_15917 (AllWinning.cons node_17984 (AllWinning.cons node_17097 (AllWinning.cons node_16035 (AllWinning.cons node_15077 (AllWinning.cons node_17987 (AllWinning.cons node_17105 (AllWinning.cons node_16046 (AllWinning.cons node_15091 (AllWinning.nil)))))))))))

theorem node_18911 : Outcome ⟨3, 14, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 12, 15, 4⟩) (by decide) node_17100

theorem node_18912 : Outcome ⟨3, 14, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 15, 4⟩) (by decide) node_17100

theorem node_18913 : Outcome ⟨3, 14, 15, 8⟩ true :=
  Outcome.win (q := ⟨3, 12, 15, 4⟩) (by decide) node_17100

theorem node_18914 : Outcome ⟨3, 14, 15, 10⟩ true :=
  Outcome.win (q := ⟨3, 12, 15, 4⟩) (by decide) node_17100

theorem node_18915 : Outcome ⟨3, 15, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 15, 12, 4⟩) (by decide) node_17112

theorem node_18916 : Outcome ⟨3, 15, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 12, 4⟩) (by decide) node_17112

theorem node_18917 : Outcome ⟨3, 15, 14, 8⟩ true :=
  Outcome.win (q := ⟨3, 15, 12, 4⟩) (by decide) node_17112

theorem node_18918 : Outcome ⟨3, 15, 14, 10⟩ true :=
  Outcome.win (q := ⟨3, 15, 12, 4⟩) (by decide) node_17112

theorem node_18919 : Outcome ⟨3, 16, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 13, 2⟩, ⟨1, 16, 13, 4⟩, ⟨3, 15, 13, 2⟩, ⟨3, 14, 13, 4⟩, ⟨3, 16, 12, 2⟩, ⟨3, 16, 11, 4⟩]
  exact AllWinning.cons node_17964 (AllWinning.cons node_17034 (AllWinning.cons node_17996 (AllWinning.cons node_17109 (AllWinning.cons node_18000 (AllWinning.cons node_17116 (AllWinning.nil))))))

theorem node_18920 : Outcome ⟨3, 16, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 13, 2⟩, ⟨1, 16, 13, 4⟩, ⟨0, 16, 13, 6⟩, ⟨3, 15, 13, 2⟩, ⟨3, 14, 13, 4⟩, ⟨3, 13, 13, 6⟩, ⟨3, 12, 13, 8⟩, ⟨3, 16, 12, 2⟩, ⟨3, 16, 11, 4⟩, ⟨3, 16, 10, 6⟩, ⟨3, 16, 9, 8⟩]
  exact AllWinning.cons node_17964 (AllWinning.cons node_17034 (AllWinning.cons node_15925 (AllWinning.cons node_17996 (AllWinning.cons node_17109 (AllWinning.cons node_16046 (AllWinning.cons node_15087 (AllWinning.cons node_18000 (AllWinning.cons node_17116 (AllWinning.cons node_16058 (AllWinning.cons node_15101 (AllWinning.nil)))))))))))

theorem node_18921 : Outcome ⟨3, 17, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 12, 4⟩) (by decide) node_17112

theorem node_18922 : Outcome ⟨3, 17, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 15, 12, 4⟩) (by decide) node_17112

theorem node_18923 : Outcome ⟨3, 18, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 2⟩) (by decide) node_18006

theorem node_18924 : Outcome ⟨3, 18, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 2⟩) (by decide) node_18006

theorem node_18925 : Outcome ⟨3, 19, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 2⟩) (by decide) node_18006

theorem node_18926 : Outcome ⟨3, 19, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 2⟩) (by decide) node_18006

theorem node_18927 : Outcome ⟨3, 20, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 20, 9, 2⟩) (by decide) node_17970

theorem node_18928 : Outcome ⟨3, 20, 9, 6⟩ true :=
  Outcome.win (q := ⟨2, 20, 9, 2⟩) (by decide) node_17970

theorem node_18929 : Outcome ⟨3, 20, 9, 12⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 16⟩) (by decide) node_11200

theorem node_18930 : Outcome ⟨4, 8, 20, 4⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 6⟩) (by decide) node_16073

theorem node_18931 : Outcome ⟨4, 8, 20, 6⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 6⟩) (by decide) node_16073

theorem node_18932 : Outcome ⟨4, 8, 20, 10⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 6⟩) (by decide) node_16073

theorem node_18933 : Outcome ⟨4, 9, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 19, 2⟩, ⟨2, 9, 19, 4⟩, ⟨4, 8, 19, 2⟩, ⟨4, 7, 19, 4⟩, ⟨4, 9, 18, 2⟩, ⟨4, 9, 17, 4⟩]
  exact AllWinning.cons node_17975 (AllWinning.cons node_17049 (AllWinning.cons node_18017 (AllWinning.cons node_17129 (AllWinning.cons node_18019 (AllWinning.cons node_17134 (AllWinning.nil))))))

theorem node_18934 : Outcome ⟨4, 9, 19, 10⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 6⟩) (by decide) node_16090

theorem node_18935 : Outcome ⟨4, 10, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 2⟩) (by decide) node_17977

theorem node_18936 : Outcome ⟨4, 10, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 2⟩) (by decide) node_17977

theorem node_18937 : Outcome ⟨4, 11, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 4⟩) (by decide) node_17054

theorem node_18938 : Outcome ⟨4, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 6⟩) (by decide) node_16084

theorem node_18939 : Outcome ⟨4, 11, 17, 8⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 6⟩) (by decide) node_16084

theorem node_18940 : Outcome ⟨4, 12, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 16, 2⟩, ⟨2, 12, 16, 4⟩, ⟨4, 11, 16, 2⟩, ⟨4, 10, 16, 4⟩, ⟨4, 12, 15, 2⟩, ⟨4, 12, 14, 4⟩]
  exact AllWinning.cons node_17984 (AllWinning.cons node_17059 (AllWinning.cons node_18024 (AllWinning.cons node_17137 (AllWinning.cons node_18027 (AllWinning.cons node_17144 (AllWinning.nil))))))

theorem node_18941 : Outcome ⟨4, 12, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 6⟩) (by decide) node_16090

theorem node_18942 : Outcome ⟨4, 13, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 13, 15, 2⟩, ⟨2, 13, 15, 4⟩, ⟨4, 12, 15, 2⟩, ⟨4, 11, 15, 4⟩, ⟨4, 13, 14, 2⟩, ⟨4, 13, 13, 4⟩]
  exact AllWinning.cons node_17987 (AllWinning.cons node_17063 (AllWinning.cons node_18027 (AllWinning.cons node_17140 (AllWinning.cons node_18030 (AllWinning.cons node_17148 (AllWinning.nil))))))

theorem node_18943 : Outcome ⟨4, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 6⟩) (by decide) node_16113

theorem node_18944 : Outcome ⟨4, 13, 15, 8⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 6⟩) (by decide) node_16113

theorem node_18945 : Outcome ⟨4, 13, 15, 10⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 6⟩) (by decide) node_16113

theorem node_18946 : Outcome ⟨4, 14, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 14, 14, 2⟩) (by decide) node_17991

theorem node_18947 : Outcome ⟨4, 14, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 8⟩) (by decide) node_14940

theorem node_18948 : Outcome ⟨4, 14, 14, 10⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 8⟩) (by decide) node_14940

theorem node_18949 : Outcome ⟨4, 14, 14, 20⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 8⟩) (by decide) node_14940

theorem node_18950 : Outcome ⟨4, 15, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 15, 13, 2⟩, ⟨2, 15, 13, 4⟩, ⟨4, 14, 13, 2⟩, ⟨4, 13, 13, 4⟩, ⟨4, 15, 12, 2⟩, ⟨4, 15, 11, 4⟩]
  exact AllWinning.cons node_17996 (AllWinning.cons node_17071 (AllWinning.cons node_18034 (AllWinning.cons node_17148 (AllWinning.cons node_18038 (AllWinning.cons node_17156 (AllWinning.nil))))))

theorem node_18951 : Outcome ⟨4, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 6⟩) (by decide) node_16103

theorem node_18952 : Outcome ⟨4, 15, 13, 8⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 6⟩) (by decide) node_16103

theorem node_18953 : Outcome ⟨4, 15, 13, 10⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 6⟩) (by decide) node_16103

theorem node_18954 : Outcome ⟨4, 16, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 16, 12, 2⟩, ⟨2, 16, 12, 4⟩, ⟨4, 15, 12, 2⟩, ⟨4, 14, 12, 4⟩, ⟨4, 16, 11, 2⟩, ⟨4, 16, 10, 4⟩]
  exact AllWinning.cons node_18000 (AllWinning.cons node_17073 (AllWinning.cons node_18038 (AllWinning.cons node_17152 (AllWinning.cons node_18041 (AllWinning.cons node_17160 (AllWinning.nil))))))

theorem node_18955 : Outcome ⟨4, 16, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 6⟩) (by decide) node_16113

theorem node_18956 : Outcome ⟨4, 17, 11, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 4⟩) (by decide) node_17076

theorem node_18957 : Outcome ⟨4, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 6⟩) (by decide) node_16135

theorem node_18958 : Outcome ⟨4, 17, 11, 8⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 6⟩) (by decide) node_16135

theorem node_18959 : Outcome ⟨4, 18, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 2⟩) (by decide) node_18006

theorem node_18960 : Outcome ⟨4, 18, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 2⟩) (by decide) node_18006

theorem node_18961 : Outcome ⟨4, 19, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 19, 9, 2⟩, ⟨2, 19, 9, 4⟩, ⟨4, 18, 9, 2⟩, ⟨4, 17, 9, 4⟩, ⟨4, 19, 8, 2⟩, ⟨4, 19, 7, 4⟩]
  exact AllWinning.cons node_18010 (AllWinning.cons node_17085 (AllWinning.cons node_18047 (AllWinning.cons node_17162 (AllWinning.cons node_18049 (AllWinning.cons node_17167 (AllWinning.nil))))))

theorem node_18962 : Outcome ⟨4, 19, 9, 10⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 6⟩) (by decide) node_16126

theorem node_18963 : Outcome ⟨4, 20, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 6⟩) (by decide) node_16135

theorem node_18964 : Outcome ⟨4, 20, 8, 6⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 6⟩) (by decide) node_16135

theorem node_18965 : Outcome ⟨4, 20, 8, 10⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 6⟩) (by decide) node_16135

theorem node_18966 : Outcome ⟨5, 7, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 7, 20, 2⟩, ⟨3, 7, 20, 4⟩, ⟨5, 6, 20, 2⟩, ⟨5, 5, 20, 4⟩, ⟨5, 7, 19, 2⟩, ⟨5, 7, 18, 4⟩]
  exact AllWinning.cons node_18013 (AllWinning.cons node_17089 (AllWinning.cons node_18055 (AllWinning.cons node_17171 (AllWinning.cons node_18057 (AllWinning.cons node_17176 (AllWinning.nil))))))

theorem node_18967 : Outcome ⟨5, 7, 20, 4⟩ true :=
  Outcome.win (q := ⟨5, 4, 20, 6⟩) (by decide) node_16152

theorem node_18968 : Outcome ⟨5, 7, 20, 6⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 10⟩) (by decide) node_13948

theorem node_18969 : Outcome ⟨5, 8, 19, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 8⟩) (by decide) node_15165

theorem node_18970 : Outcome ⟨5, 8, 19, 16⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 8⟩) (by decide) node_15165

theorem node_18971 : Outcome ⟨5, 9, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 8⟩) (by decide) node_15175

theorem node_18972 : Outcome ⟨5, 9, 18, 6⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 8⟩) (by decide) node_15175

theorem node_18973 : Outcome ⟨5, 10, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 16, 2⟩) (by decide) node_18065

theorem node_18974 : Outcome ⟨5, 10, 17, 4⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 6⟩) (by decide) node_16162

theorem node_18975 : Outcome ⟨5, 10, 17, 10⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 6⟩) (by decide) node_16162

theorem node_18976 : Outcome ⟨5, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 16, 2⟩) (by decide) node_18065

theorem node_18977 : Outcome ⟨5, 11, 16, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 16, 2⟩) (by decide) node_18065

theorem node_18978 : Outcome ⟨5, 12, 15, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 8⟩) (by decide) node_15165

theorem node_18979 : Outcome ⟨5, 12, 15, 6⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 8⟩) (by decide) node_15165

theorem node_18980 : Outcome ⟨5, 13, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 12, 14, 2⟩) (by decide) node_18071

theorem node_18981 : Outcome ⟨5, 14, 13, 2⟩ true :=
  Outcome.win (q := ⟨5, 13, 13, 2⟩) (by decide) node_18075

theorem node_18982 : Outcome ⟨5, 15, 12, 4⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 8⟩) (by decide) node_15197

theorem node_18983 : Outcome ⟨5, 15, 12, 6⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 8⟩) (by decide) node_15197

theorem node_18984 : Outcome ⟨5, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 10, 2⟩) (by decide) node_18086

theorem node_18985 : Outcome ⟨5, 16, 11, 4⟩ true :=
  Outcome.win (q := ⟨5, 16, 10, 2⟩) (by decide) node_18086

theorem node_18986 : Outcome ⟨5, 17, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 10, 2⟩) (by decide) node_18086

theorem node_18987 : Outcome ⟨5, 17, 10, 4⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 6⟩) (by decide) node_16184

theorem node_18988 : Outcome ⟨5, 17, 10, 10⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 6⟩) (by decide) node_16184

theorem node_18989 : Outcome ⟨5, 18, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 8⟩) (by decide) node_15192

theorem node_18990 : Outcome ⟨5, 18, 9, 6⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 8⟩) (by decide) node_15192

theorem node_18991 : Outcome ⟨5, 19, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 8⟩) (by decide) node_15197

theorem node_18992 : Outcome ⟨5, 19, 8, 16⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 8⟩) (by decide) node_15197

theorem node_18993 : Outcome ⟨5, 20, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 20, 7, 2⟩, ⟨3, 20, 7, 4⟩, ⟨5, 19, 7, 2⟩, ⟨5, 18, 7, 4⟩, ⟨5, 20, 6, 2⟩, ⟨5, 20, 5, 4⟩]
  exact AllWinning.cons node_18051 (AllWinning.cons node_17125 (AllWinning.cons node_18095 (AllWinning.cons node_17202 (AllWinning.cons node_18097 (AllWinning.cons node_17207 (AllWinning.nil))))))

theorem node_18994 : Outcome ⟨5, 20, 7, 4⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 6⟩) (by decide) node_16184

theorem node_18995 : Outcome ⟨5, 20, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 10⟩) (by decide) node_13994

theorem node_18996 : Outcome ⟨6, 6, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.nil))))))

theorem node_18997 : Outcome ⟨6, 6, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨3, 6, 20, 6⟩, ⟨2, 6, 20, 8⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 3, 20, 6⟩, ⟨6, 2, 20, 8⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 6, 16, 8⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_16022 (AllWinning.cons node_15009 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_16199 (AllWinning.cons node_15215 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.cons node_16209 (AllWinning.cons node_15225 (AllWinning.nil))))))))))))

theorem node_18998 : Outcome ⟨6, 6, 20, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨3, 6, 20, 6⟩, ⟨2, 6, 20, 8⟩, ⟨1, 6, 20, 10⟩, ⟨0, 6, 20, 12⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 3, 20, 6⟩, ⟨6, 2, 20, 8⟩, ⟨6, 1, 20, 10⟩, ⟨6, 0, 20, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 6, 16, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 6, 14, 12⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_16022 (AllWinning.cons node_15009 (AllWinning.cons node_13997 (AllWinning.cons node_12980 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_16199 (AllWinning.cons node_15215 (AllWinning.cons node_14264 (AllWinning.cons node_13296 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.cons node_16209 (AllWinning.cons node_15225 (AllWinning.cons node_14277 (AllWinning.cons node_13314 (AllWinning.nil))))))))))))))))))

theorem node_18999 : Outcome ⟨6, 6, 20, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨3, 6, 20, 6⟩, ⟨2, 6, 20, 8⟩, ⟨1, 6, 20, 10⟩, ⟨0, 6, 20, 12⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 3, 20, 6⟩, ⟨6, 2, 20, 8⟩, ⟨6, 1, 20, 10⟩, ⟨6, 0, 20, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 6, 16, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 6, 14, 12⟩, ⟨6, 6, 13, 14⟩, ⟨6, 6, 12, 16⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_16022 (AllWinning.cons node_15009 (AllWinning.cons node_13997 (AllWinning.cons node_12980 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_16199 (AllWinning.cons node_15215 (AllWinning.cons node_14264 (AllWinning.cons node_13296 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.cons node_16209 (AllWinning.cons node_15225 (AllWinning.cons node_14277 (AllWinning.cons node_13314 (AllWinning.cons node_12367 (AllWinning.cons node_11385 (AllWinning.nil))))))))))))))))))))

theorem node_19000 : Outcome ⟨6, 6, 20, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨3, 6, 20, 6⟩, ⟨2, 6, 20, 8⟩, ⟨1, 6, 20, 10⟩, ⟨0, 6, 20, 12⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 3, 20, 6⟩, ⟨6, 2, 20, 8⟩, ⟨6, 1, 20, 10⟩, ⟨6, 0, 20, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 6, 16, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 6, 14, 12⟩, ⟨6, 6, 13, 14⟩, ⟨6, 6, 12, 16⟩, ⟨6, 6, 11, 18⟩, ⟨6, 6, 10, 20⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_16022 (AllWinning.cons node_15009 (AllWinning.cons node_13997 (AllWinning.cons node_12980 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_16199 (AllWinning.cons node_15215 (AllWinning.cons node_14264 (AllWinning.cons node_13296 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.cons node_16209 (AllWinning.cons node_15225 (AllWinning.cons node_14277 (AllWinning.cons node_13314 (AllWinning.cons node_12367 (AllWinning.cons node_11385 (AllWinning.cons node_10365 (AllWinning.cons node_9361 (AllWinning.nil))))))))))))))))))))))

theorem node_19001 : Outcome ⟨6, 6, 20, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨3, 6, 20, 6⟩, ⟨2, 6, 20, 8⟩, ⟨1, 6, 20, 10⟩, ⟨0, 6, 20, 12⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 3, 20, 6⟩, ⟨6, 2, 20, 8⟩, ⟨6, 1, 20, 10⟩, ⟨6, 0, 20, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 6, 16, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 6, 14, 12⟩, ⟨6, 6, 13, 14⟩, ⟨6, 6, 12, 16⟩, ⟨6, 6, 11, 18⟩, ⟨6, 6, 10, 20⟩, ⟨6, 6, 9, 22⟩, ⟨6, 6, 8, 24⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_16022 (AllWinning.cons node_15009 (AllWinning.cons node_13997 (AllWinning.cons node_12980 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_16199 (AllWinning.cons node_15215 (AllWinning.cons node_14264 (AllWinning.cons node_13296 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.cons node_16209 (AllWinning.cons node_15225 (AllWinning.cons node_14277 (AllWinning.cons node_13314 (AllWinning.cons node_12367 (AllWinning.cons node_11385 (AllWinning.cons node_10365 (AllWinning.cons node_9361 (AllWinning.cons node_8366 (AllWinning.cons node_7444 (AllWinning.nil))))))))))))))))))))))))

theorem node_19002 : Outcome ⟨6, 6, 20, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨3, 6, 20, 6⟩, ⟨2, 6, 20, 8⟩, ⟨1, 6, 20, 10⟩, ⟨0, 6, 20, 12⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 3, 20, 6⟩, ⟨6, 2, 20, 8⟩, ⟨6, 1, 20, 10⟩, ⟨6, 0, 20, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 6, 16, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 6, 14, 12⟩, ⟨6, 6, 13, 14⟩, ⟨6, 6, 12, 16⟩, ⟨6, 6, 11, 18⟩, ⟨6, 6, 10, 20⟩, ⟨6, 6, 9, 22⟩, ⟨6, 6, 8, 24⟩, ⟨6, 6, 7, 26⟩, ⟨6, 6, 6, 28⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_16022 (AllWinning.cons node_15009 (AllWinning.cons node_13997 (AllWinning.cons node_12980 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_16199 (AllWinning.cons node_15215 (AllWinning.cons node_14264 (AllWinning.cons node_13296 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.cons node_16209 (AllWinning.cons node_15225 (AllWinning.cons node_14277 (AllWinning.cons node_13314 (AllWinning.cons node_12367 (AllWinning.cons node_11385 (AllWinning.cons node_10365 (AllWinning.cons node_9361 (AllWinning.cons node_8366 (AllWinning.cons node_7444 (AllWinning.cons node_6517 (AllWinning.cons node_5706 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19003 : Outcome ⟨6, 6, 20, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 6, 20, 2⟩, ⟨4, 6, 20, 4⟩, ⟨3, 6, 20, 6⟩, ⟨2, 6, 20, 8⟩, ⟨1, 6, 20, 10⟩, ⟨0, 6, 20, 12⟩, ⟨6, 5, 20, 2⟩, ⟨6, 4, 20, 4⟩, ⟨6, 3, 20, 6⟩, ⟨6, 2, 20, 8⟩, ⟨6, 1, 20, 10⟩, ⟨6, 0, 20, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 6, 18, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 6, 16, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 6, 14, 12⟩, ⟨6, 6, 13, 14⟩, ⟨6, 6, 12, 16⟩, ⟨6, 6, 11, 18⟩, ⟨6, 6, 10, 20⟩, ⟨6, 6, 9, 22⟩, ⟨6, 6, 8, 24⟩, ⟨6, 6, 7, 26⟩, ⟨6, 6, 6, 28⟩, ⟨6, 6, 5, 30⟩, ⟨6, 6, 4, 32⟩, ⟨6, 6, 3, 34⟩, ⟨6, 6, 2, 36⟩]
  exact AllWinning.cons node_18055 (AllWinning.cons node_17127 (AllWinning.cons node_16022 (AllWinning.cons node_15009 (AllWinning.cons node_13997 (AllWinning.cons node_12980 (AllWinning.cons node_18099 (AllWinning.cons node_17209 (AllWinning.cons node_16199 (AllWinning.cons node_15215 (AllWinning.cons node_14264 (AllWinning.cons node_13296 (AllWinning.cons node_18101 (AllWinning.cons node_17213 (AllWinning.cons node_16209 (AllWinning.cons node_15225 (AllWinning.cons node_14277 (AllWinning.cons node_13314 (AllWinning.cons node_12367 (AllWinning.cons node_11385 (AllWinning.cons node_10365 (AllWinning.cons node_9361 (AllWinning.cons node_8366 (AllWinning.cons node_7444 (AllWinning.cons node_6517 (AllWinning.cons node_5706 (AllWinning.cons node_5011 (AllWinning.cons node_4309 (AllWinning.cons node_3713 (AllWinning.cons node_3153 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_19004 : Outcome ⟨6, 7, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 7, 19, 2⟩, ⟨4, 7, 19, 4⟩, ⟨3, 7, 19, 6⟩, ⟨2, 7, 19, 8⟩, ⟨6, 6, 19, 2⟩, ⟨6, 5, 19, 4⟩, ⟨6, 4, 19, 6⟩, ⟨6, 3, 19, 8⟩, ⟨6, 7, 18, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 7, 16, 6⟩, ⟨6, 7, 15, 8⟩]
  exact AllWinning.cons node_18057 (AllWinning.cons node_17129 (AllWinning.cons node_16025 (AllWinning.cons node_15011 (AllWinning.cons node_18101 (AllWinning.cons node_17211 (AllWinning.cons node_16202 (AllWinning.cons node_15217 (AllWinning.cons node_18102 (AllWinning.cons node_17215 (AllWinning.cons node_16211 (AllWinning.cons node_15229 (AllWinning.nil))))))))))))

theorem node_19005 : Outcome ⟨6, 7, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 7, 19, 2⟩, ⟨4, 7, 19, 4⟩, ⟨3, 7, 19, 6⟩, ⟨2, 7, 19, 8⟩, ⟨1, 7, 19, 10⟩, ⟨0, 7, 19, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 5, 19, 4⟩, ⟨6, 4, 19, 6⟩, ⟨6, 3, 19, 8⟩, ⟨6, 2, 19, 10⟩, ⟨6, 1, 19, 12⟩, ⟨6, 0, 19, 14⟩, ⟨6, 7, 18, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 7, 16, 6⟩, ⟨6, 7, 15, 8⟩, ⟨6, 7, 14, 10⟩, ⟨6, 7, 13, 12⟩, ⟨6, 7, 12, 14⟩, ⟨6, 7, 11, 16⟩]
  exact AllWinning.cons node_18057 (AllWinning.cons node_17129 (AllWinning.cons node_16025 (AllWinning.cons node_15011 (AllWinning.cons node_13999 (AllWinning.cons node_12983 (AllWinning.cons node_18101 (AllWinning.cons node_17211 (AllWinning.cons node_16202 (AllWinning.cons node_15217 (AllWinning.cons node_14266 (AllWinning.cons node_13298 (AllWinning.cons node_12347 (AllWinning.cons node_18102 (AllWinning.cons node_17215 (AllWinning.cons node_16211 (AllWinning.cons node_15229 (AllWinning.cons node_14281 (AllWinning.cons node_13319 (AllWinning.cons node_12371 (AllWinning.cons node_11389 (AllWinning.nil)))))))))))))))))))))

theorem node_19006 : Outcome ⟨6, 7, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 7, 19, 2⟩, ⟨4, 7, 19, 4⟩, ⟨3, 7, 19, 6⟩, ⟨2, 7, 19, 8⟩, ⟨1, 7, 19, 10⟩, ⟨0, 7, 19, 12⟩, ⟨6, 6, 19, 2⟩, ⟨6, 5, 19, 4⟩, ⟨6, 4, 19, 6⟩, ⟨6, 3, 19, 8⟩, ⟨6, 2, 19, 10⟩, ⟨6, 1, 19, 12⟩, ⟨6, 0, 19, 14⟩, ⟨6, 7, 18, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 7, 16, 6⟩, ⟨6, 7, 15, 8⟩, ⟨6, 7, 14, 10⟩, ⟨6, 7, 13, 12⟩, ⟨6, 7, 12, 14⟩, ⟨6, 7, 11, 16⟩, ⟨6, 7, 10, 18⟩, ⟨6, 7, 9, 20⟩]
  exact AllWinning.cons node_18057 (AllWinning.cons node_17129 (AllWinning.cons node_16025 (AllWinning.cons node_15011 (AllWinning.cons node_13999 (AllWinning.cons node_12983 (AllWinning.cons node_18101 (AllWinning.cons node_17211 (AllWinning.cons node_16202 (AllWinning.cons node_15217 (AllWinning.cons node_14266 (AllWinning.cons node_13298 (AllWinning.cons node_12347 (AllWinning.cons node_18102 (AllWinning.cons node_17215 (AllWinning.cons node_16211 (AllWinning.cons node_15229 (AllWinning.cons node_14281 (AllWinning.cons node_13319 (AllWinning.cons node_12371 (AllWinning.cons node_11389 (AllWinning.cons node_10370 (AllWinning.cons node_9367 (AllWinning.nil)))))))))))))))))))))))

theorem node_19007 : Outcome ⟨6, 8, 18, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 18, 2⟩) (by decide) node_18059

theorem node_19008 : Outcome ⟨6, 9, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 17, 2⟩, ⟨4, 9, 17, 4⟩, ⟨6, 8, 17, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 9, 16, 2⟩, ⟨6, 9, 15, 4⟩]
  exact AllWinning.cons node_18062 (AllWinning.cons node_17134 (AllWinning.cons node_18105 (AllWinning.cons node_17215 (AllWinning.cons node_18106 (AllWinning.cons node_17219 (AllWinning.nil))))))

theorem node_19009 : Outcome ⟨6, 9, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 17, 2⟩, ⟨4, 9, 17, 4⟩, ⟨3, 9, 17, 6⟩, ⟨2, 9, 17, 8⟩, ⟨6, 8, 17, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 5, 17, 8⟩, ⟨6, 9, 16, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 9, 14, 6⟩, ⟨6, 9, 13, 8⟩]
  exact AllWinning.cons node_18062 (AllWinning.cons node_17134 (AllWinning.cons node_16032 (AllWinning.cons node_15018 (AllWinning.cons node_18105 (AllWinning.cons node_17215 (AllWinning.cons node_16209 (AllWinning.cons node_15223 (AllWinning.cons node_18106 (AllWinning.cons node_17219 (AllWinning.cons node_16219 (AllWinning.cons node_15236 (AllWinning.nil))))))))))))

theorem node_19010 : Outcome ⟨6, 9, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 17, 2⟩, ⟨4, 9, 17, 4⟩, ⟨3, 9, 17, 6⟩, ⟨2, 9, 17, 8⟩, ⟨1, 9, 17, 10⟩, ⟨0, 9, 17, 12⟩, ⟨6, 8, 17, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 5, 17, 8⟩, ⟨6, 4, 17, 10⟩, ⟨6, 3, 17, 12⟩, ⟨6, 9, 16, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 9, 14, 6⟩, ⟨6, 9, 13, 8⟩, ⟨6, 9, 12, 10⟩, ⟨6, 9, 11, 12⟩]
  exact AllWinning.cons node_18062 (AllWinning.cons node_17134 (AllWinning.cons node_16032 (AllWinning.cons node_15018 (AllWinning.cons node_14009 (AllWinning.cons node_12991 (AllWinning.cons node_18105 (AllWinning.cons node_17215 (AllWinning.cons node_16209 (AllWinning.cons node_15223 (AllWinning.cons node_14272 (AllWinning.cons node_13304 (AllWinning.cons node_18106 (AllWinning.cons node_17219 (AllWinning.cons node_16219 (AllWinning.cons node_15236 (AllWinning.cons node_14287 (AllWinning.cons node_13326 (AllWinning.nil))))))))))))))))))

theorem node_19011 : Outcome ⟨6, 9, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 17, 2⟩, ⟨4, 9, 17, 4⟩, ⟨3, 9, 17, 6⟩, ⟨2, 9, 17, 8⟩, ⟨1, 9, 17, 10⟩, ⟨0, 9, 17, 12⟩, ⟨6, 8, 17, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 5, 17, 8⟩, ⟨6, 4, 17, 10⟩, ⟨6, 3, 17, 12⟩, ⟨6, 2, 17, 14⟩, ⟨6, 1, 17, 16⟩, ⟨6, 9, 16, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 9, 14, 6⟩, ⟨6, 9, 13, 8⟩, ⟨6, 9, 12, 10⟩, ⟨6, 9, 11, 12⟩, ⟨6, 9, 10, 14⟩, ⟨6, 9, 9, 16⟩]
  exact AllWinning.cons node_18062 (AllWinning.cons node_17134 (AllWinning.cons node_16032 (AllWinning.cons node_15018 (AllWinning.cons node_14009 (AllWinning.cons node_12991 (AllWinning.cons node_18105 (AllWinning.cons node_17215 (AllWinning.cons node_16209 (AllWinning.cons node_15223 (AllWinning.cons node_14272 (AllWinning.cons node_13304 (AllWinning.cons node_12355 (AllWinning.cons node_11369 (AllWinning.cons node_18106 (AllWinning.cons node_17219 (AllWinning.cons node_16219 (AllWinning.cons node_15236 (AllWinning.cons node_14287 (AllWinning.cons node_13326 (AllWinning.cons node_12379 (AllWinning.cons node_11397 (AllWinning.nil))))))))))))))))))))))

theorem node_19012 : Outcome ⟨6, 9, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 17, 2⟩, ⟨4, 9, 17, 4⟩, ⟨3, 9, 17, 6⟩, ⟨2, 9, 17, 8⟩, ⟨1, 9, 17, 10⟩, ⟨0, 9, 17, 12⟩, ⟨6, 8, 17, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 5, 17, 8⟩, ⟨6, 4, 17, 10⟩, ⟨6, 3, 17, 12⟩, ⟨6, 2, 17, 14⟩, ⟨6, 1, 17, 16⟩, ⟨6, 0, 17, 18⟩, ⟨6, 9, 16, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 9, 14, 6⟩, ⟨6, 9, 13, 8⟩, ⟨6, 9, 12, 10⟩, ⟨6, 9, 11, 12⟩, ⟨6, 9, 10, 14⟩, ⟨6, 9, 9, 16⟩, ⟨6, 9, 8, 18⟩, ⟨6, 9, 7, 20⟩]
  exact AllWinning.cons node_18062 (AllWinning.cons node_17134 (AllWinning.cons node_16032 (AllWinning.cons node_15018 (AllWinning.cons node_14009 (AllWinning.cons node_12991 (AllWinning.cons node_18105 (AllWinning.cons node_17215 (AllWinning.cons node_16209 (AllWinning.cons node_15223 (AllWinning.cons node_14272 (AllWinning.cons node_13304 (AllWinning.cons node_12355 (AllWinning.cons node_11369 (AllWinning.cons node_10338 (AllWinning.cons node_18106 (AllWinning.cons node_17219 (AllWinning.cons node_16219 (AllWinning.cons node_15236 (AllWinning.cons node_14287 (AllWinning.cons node_13326 (AllWinning.cons node_12379 (AllWinning.cons node_11397 (AllWinning.cons node_10379 (AllWinning.cons node_9375 (AllWinning.nil)))))))))))))))))))))))))

theorem node_19013 : Outcome ⟨6, 9, 17, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 9, 17, 2⟩, ⟨4, 9, 17, 4⟩, ⟨3, 9, 17, 6⟩, ⟨2, 9, 17, 8⟩, ⟨1, 9, 17, 10⟩, ⟨0, 9, 17, 12⟩, ⟨6, 8, 17, 2⟩, ⟨6, 7, 17, 4⟩, ⟨6, 6, 17, 6⟩, ⟨6, 5, 17, 8⟩, ⟨6, 4, 17, 10⟩, ⟨6, 3, 17, 12⟩, ⟨6, 2, 17, 14⟩, ⟨6, 1, 17, 16⟩, ⟨6, 0, 17, 18⟩, ⟨6, 9, 16, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 9, 14, 6⟩, ⟨6, 9, 13, 8⟩, ⟨6, 9, 12, 10⟩, ⟨6, 9, 11, 12⟩, ⟨6, 9, 10, 14⟩, ⟨6, 9, 9, 16⟩, ⟨6, 9, 8, 18⟩, ⟨6, 9, 7, 20⟩, ⟨6, 9, 6, 22⟩, ⟨6, 9, 5, 24⟩]
  exact AllWinning.cons node_18062 (AllWinning.cons node_17134 (AllWinning.cons node_16032 (AllWinning.cons node_15018 (AllWinning.cons node_14009 (AllWinning.cons node_12991 (AllWinning.cons node_18105 (AllWinning.cons node_17215 (AllWinning.cons node_16209 (AllWinning.cons node_15223 (AllWinning.cons node_14272 (AllWinning.cons node_13304 (AllWinning.cons node_12355 (AllWinning.cons node_11369 (AllWinning.cons node_10338 (AllWinning.cons node_18106 (AllWinning.cons node_17219 (AllWinning.cons node_16219 (AllWinning.cons node_15236 (AllWinning.cons node_14287 (AllWinning.cons node_13326 (AllWinning.cons node_12379 (AllWinning.cons node_11397 (AllWinning.cons node_10379 (AllWinning.cons node_9375 (AllWinning.cons node_8394 (AllWinning.cons node_7454 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_19014 : Outcome ⟨6, 10, 16, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 8⟩) (by decide) node_15021

theorem node_19015 : Outcome ⟨6, 10, 16, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 8⟩) (by decide) node_15021

theorem node_19016 : Outcome ⟨6, 11, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 15, 2⟩, ⟨4, 11, 15, 4⟩, ⟨6, 10, 15, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 11, 14, 2⟩, ⟨6, 11, 13, 4⟩]
  exact AllWinning.cons node_18068 (AllWinning.cons node_17140 (AllWinning.cons node_18109 (AllWinning.cons node_17219 (AllWinning.cons node_18112 (AllWinning.cons node_17225 (AllWinning.nil))))))

theorem node_19017 : Outcome ⟨6, 11, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 15, 2⟩, ⟨4, 11, 15, 4⟩, ⟨3, 11, 15, 6⟩, ⟨2, 11, 15, 8⟩, ⟨6, 10, 15, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 8, 15, 6⟩, ⟨6, 7, 15, 8⟩, ⟨6, 11, 14, 2⟩, ⟨6, 11, 13, 4⟩, ⟨6, 11, 12, 6⟩, ⟨6, 11, 11, 8⟩]
  exact AllWinning.cons node_18068 (AllWinning.cons node_17140 (AllWinning.cons node_16037 (AllWinning.cons node_15025 (AllWinning.cons node_18109 (AllWinning.cons node_17219 (AllWinning.cons node_16215 (AllWinning.cons node_15229 (AllWinning.cons node_18112 (AllWinning.cons node_17225 (AllWinning.cons node_16227 (AllWinning.cons node_15242 (AllWinning.nil))))))))))))

theorem node_19018 : Outcome ⟨6, 11, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 15, 2⟩, ⟨4, 11, 15, 4⟩, ⟨3, 11, 15, 6⟩, ⟨2, 11, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨0, 11, 15, 12⟩, ⟨6, 10, 15, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 8, 15, 6⟩, ⟨6, 7, 15, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 5, 15, 12⟩, ⟨6, 11, 14, 2⟩, ⟨6, 11, 13, 4⟩, ⟨6, 11, 12, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 11, 10, 10⟩, ⟨6, 11, 9, 12⟩]
  exact AllWinning.cons node_18068 (AllWinning.cons node_17140 (AllWinning.cons node_16037 (AllWinning.cons node_15025 (AllWinning.cons node_14017 (AllWinning.cons node_12998 (AllWinning.cons node_18109 (AllWinning.cons node_17219 (AllWinning.cons node_16215 (AllWinning.cons node_15229 (AllWinning.cons node_14277 (AllWinning.cons node_13311 (AllWinning.cons node_18112 (AllWinning.cons node_17225 (AllWinning.cons node_16227 (AllWinning.cons node_15242 (AllWinning.cons node_14293 (AllWinning.cons node_13332 (AllWinning.nil))))))))))))))))))

theorem node_19019 : Outcome ⟨6, 11, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 15, 2⟩, ⟨4, 11, 15, 4⟩, ⟨3, 11, 15, 6⟩, ⟨2, 11, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨0, 11, 15, 12⟩, ⟨6, 10, 15, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 8, 15, 6⟩, ⟨6, 7, 15, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 5, 15, 12⟩, ⟨6, 4, 15, 14⟩, ⟨6, 3, 15, 16⟩, ⟨6, 2, 15, 18⟩, ⟨6, 1, 15, 20⟩, ⟨6, 11, 14, 2⟩, ⟨6, 11, 13, 4⟩, ⟨6, 11, 12, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 11, 10, 10⟩, ⟨6, 11, 9, 12⟩, ⟨6, 11, 8, 14⟩, ⟨6, 11, 7, 16⟩, ⟨6, 11, 6, 18⟩, ⟨6, 11, 5, 20⟩]
  exact AllWinning.cons node_18068 (AllWinning.cons node_17140 (AllWinning.cons node_16037 (AllWinning.cons node_15025 (AllWinning.cons node_14017 (AllWinning.cons node_12998 (AllWinning.cons node_18109 (AllWinning.cons node_17219 (AllWinning.cons node_16215 (AllWinning.cons node_15229 (AllWinning.cons node_14277 (AllWinning.cons node_13311 (AllWinning.cons node_12361 (AllWinning.cons node_11374 (AllWinning.cons node_10349 (AllWinning.cons node_9344 (AllWinning.cons node_18112 (AllWinning.cons node_17225 (AllWinning.cons node_16227 (AllWinning.cons node_15242 (AllWinning.cons node_14293 (AllWinning.cons node_13332 (AllWinning.cons node_12388 (AllWinning.cons node_11404 (AllWinning.cons node_10387 (AllWinning.cons node_9382 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19020 : Outcome ⟨6, 11, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 15, 2⟩, ⟨4, 11, 15, 4⟩, ⟨3, 11, 15, 6⟩, ⟨2, 11, 15, 8⟩, ⟨1, 11, 15, 10⟩, ⟨0, 11, 15, 12⟩, ⟨6, 10, 15, 2⟩, ⟨6, 9, 15, 4⟩, ⟨6, 8, 15, 6⟩, ⟨6, 7, 15, 8⟩, ⟨6, 6, 15, 10⟩, ⟨6, 5, 15, 12⟩, ⟨6, 4, 15, 14⟩, ⟨6, 3, 15, 16⟩, ⟨6, 2, 15, 18⟩, ⟨6, 1, 15, 20⟩, ⟨6, 0, 15, 22⟩, ⟨6, 11, 14, 2⟩, ⟨6, 11, 13, 4⟩, ⟨6, 11, 12, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 11, 10, 10⟩, ⟨6, 11, 9, 12⟩, ⟨6, 11, 8, 14⟩, ⟨6, 11, 7, 16⟩, ⟨6, 11, 6, 18⟩, ⟨6, 11, 5, 20⟩, ⟨6, 11, 4, 22⟩, ⟨6, 11, 3, 24⟩]
  exact AllWinning.cons node_18068 (AllWinning.cons node_17140 (AllWinning.cons node_16037 (AllWinning.cons node_15025 (AllWinning.cons node_14017 (AllWinning.cons node_12998 (AllWinning.cons node_18109 (AllWinning.cons node_17219 (AllWinning.cons node_16215 (AllWinning.cons node_15229 (AllWinning.cons node_14277 (AllWinning.cons node_13311 (AllWinning.cons node_12361 (AllWinning.cons node_11374 (AllWinning.cons node_10349 (AllWinning.cons node_9344 (AllWinning.cons node_8346 (AllWinning.cons node_18112 (AllWinning.cons node_17225 (AllWinning.cons node_16227 (AllWinning.cons node_15242 (AllWinning.cons node_14293 (AllWinning.cons node_13332 (AllWinning.cons node_12388 (AllWinning.cons node_11404 (AllWinning.cons node_10387 (AllWinning.cons node_9382 (AllWinning.cons node_8401 (AllWinning.cons node_7468 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19021 : Outcome ⟨6, 12, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 12, 14, 2⟩) (by decide) node_18071

theorem node_19022 : Outcome ⟨6, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 8⟩) (by decide) node_15028

theorem node_19023 : Outcome ⟨6, 13, 13, 2⟩ true :=
  Outcome.win (q := ⟨5, 13, 13, 2⟩) (by decide) node_18075

theorem node_19024 : Outcome ⟨6, 13, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 13, 2⟩) (by decide) node_18075

theorem node_19025 : Outcome ⟨6, 13, 13, 14⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 12⟩) (by decide) node_13006

theorem node_19026 : Outcome ⟨6, 14, 12, 2⟩ true :=
  Outcome.win (q := ⟨5, 14, 12, 2⟩) (by decide) node_18079

theorem node_19027 : Outcome ⟨6, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 8⟩) (by decide) node_15041

theorem node_19028 : Outcome ⟨6, 15, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 11, 2⟩, ⟨4, 15, 11, 4⟩, ⟨6, 14, 11, 2⟩, ⟨6, 13, 11, 4⟩, ⟨6, 15, 10, 2⟩, ⟨6, 15, 9, 4⟩]
  exact AllWinning.cons node_18083 (AllWinning.cons node_17156 (AllWinning.cons node_18118 (AllWinning.cons node_17230 (AllWinning.cons node_18120 (AllWinning.cons node_17237 (AllWinning.nil))))))

theorem node_19029 : Outcome ⟨6, 15, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 11, 2⟩, ⟨4, 15, 11, 4⟩, ⟨3, 15, 11, 6⟩, ⟨2, 15, 11, 8⟩, ⟨6, 14, 11, 2⟩, ⟨6, 13, 11, 4⟩, ⟨6, 12, 11, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 15, 10, 2⟩, ⟨6, 15, 9, 4⟩, ⟨6, 15, 8, 6⟩, ⟨6, 15, 7, 8⟩]
  exact AllWinning.cons node_18083 (AllWinning.cons node_17156 (AllWinning.cons node_16054 (AllWinning.cons node_15048 (AllWinning.cons node_18118 (AllWinning.cons node_17230 (AllWinning.cons node_16232 (AllWinning.cons node_15242 (AllWinning.cons node_18120 (AllWinning.cons node_17237 (AllWinning.cons node_16245 (AllWinning.cons node_15254 (AllWinning.nil))))))))))))

theorem node_19030 : Outcome ⟨6, 15, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 11, 2⟩, ⟨4, 15, 11, 4⟩, ⟨3, 15, 11, 6⟩, ⟨2, 15, 11, 8⟩, ⟨1, 15, 11, 10⟩, ⟨0, 15, 11, 12⟩, ⟨6, 14, 11, 2⟩, ⟨6, 13, 11, 4⟩, ⟨6, 12, 11, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 10, 11, 10⟩, ⟨6, 9, 11, 12⟩, ⟨6, 15, 10, 2⟩, ⟨6, 15, 9, 4⟩, ⟨6, 15, 8, 6⟩, ⟨6, 15, 7, 8⟩, ⟨6, 15, 6, 10⟩, ⟨6, 15, 5, 12⟩]
  exact AllWinning.cons node_18083 (AllWinning.cons node_17156 (AllWinning.cons node_16054 (AllWinning.cons node_15048 (AllWinning.cons node_14033 (AllWinning.cons node_13013 (AllWinning.cons node_18118 (AllWinning.cons node_17230 (AllWinning.cons node_16232 (AllWinning.cons node_15242 (AllWinning.cons node_14290 (AllWinning.cons node_13326 (AllWinning.cons node_18120 (AllWinning.cons node_17237 (AllWinning.cons node_16245 (AllWinning.cons node_15254 (AllWinning.cons node_14307 (AllWinning.cons node_13347 (AllWinning.nil))))))))))))))))))

theorem node_19031 : Outcome ⟨6, 15, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 11, 2⟩, ⟨4, 15, 11, 4⟩, ⟨3, 15, 11, 6⟩, ⟨2, 15, 11, 8⟩, ⟨1, 15, 11, 10⟩, ⟨0, 15, 11, 12⟩, ⟨6, 14, 11, 2⟩, ⟨6, 13, 11, 4⟩, ⟨6, 12, 11, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 10, 11, 10⟩, ⟨6, 9, 11, 12⟩, ⟨6, 8, 11, 14⟩, ⟨6, 7, 11, 16⟩, ⟨6, 15, 10, 2⟩, ⟨6, 15, 9, 4⟩, ⟨6, 15, 8, 6⟩, ⟨6, 15, 7, 8⟩, ⟨6, 15, 6, 10⟩, ⟨6, 15, 5, 12⟩, ⟨6, 15, 4, 14⟩, ⟨6, 15, 3, 16⟩]
  exact AllWinning.cons node_18083 (AllWinning.cons node_17156 (AllWinning.cons node_16054 (AllWinning.cons node_15048 (AllWinning.cons node_14033 (AllWinning.cons node_13013 (AllWinning.cons node_18118 (AllWinning.cons node_17230 (AllWinning.cons node_16232 (AllWinning.cons node_15242 (AllWinning.cons node_14290 (AllWinning.cons node_13326 (AllWinning.cons node_12376 (AllWinning.cons node_11389 (AllWinning.cons node_18120 (AllWinning.cons node_17237 (AllWinning.cons node_16245 (AllWinning.cons node_15254 (AllWinning.cons node_14307 (AllWinning.cons node_13347 (AllWinning.cons node_12402 (AllWinning.cons node_11419 (AllWinning.nil))))))))))))))))))))))

theorem node_19032 : Outcome ⟨6, 15, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 11, 2⟩, ⟨4, 15, 11, 4⟩, ⟨3, 15, 11, 6⟩, ⟨2, 15, 11, 8⟩, ⟨1, 15, 11, 10⟩, ⟨0, 15, 11, 12⟩, ⟨6, 14, 11, 2⟩, ⟨6, 13, 11, 4⟩, ⟨6, 12, 11, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 10, 11, 10⟩, ⟨6, 9, 11, 12⟩, ⟨6, 8, 11, 14⟩, ⟨6, 7, 11, 16⟩, ⟨6, 6, 11, 18⟩, ⟨6, 5, 11, 20⟩, ⟨6, 15, 10, 2⟩, ⟨6, 15, 9, 4⟩, ⟨6, 15, 8, 6⟩, ⟨6, 15, 7, 8⟩, ⟨6, 15, 6, 10⟩, ⟨6, 15, 5, 12⟩, ⟨6, 15, 4, 14⟩, ⟨6, 15, 3, 16⟩, ⟨6, 15, 2, 18⟩, ⟨6, 15, 1, 20⟩]
  exact AllWinning.cons node_18083 (AllWinning.cons node_17156 (AllWinning.cons node_16054 (AllWinning.cons node_15048 (AllWinning.cons node_14033 (AllWinning.cons node_13013 (AllWinning.cons node_18118 (AllWinning.cons node_17230 (AllWinning.cons node_16232 (AllWinning.cons node_15242 (AllWinning.cons node_14290 (AllWinning.cons node_13326 (AllWinning.cons node_12376 (AllWinning.cons node_11389 (AllWinning.cons node_10365 (AllWinning.cons node_9358 (AllWinning.cons node_18120 (AllWinning.cons node_17237 (AllWinning.cons node_16245 (AllWinning.cons node_15254 (AllWinning.cons node_14307 (AllWinning.cons node_13347 (AllWinning.cons node_12402 (AllWinning.cons node_11419 (AllWinning.cons node_10404 (AllWinning.cons node_9398 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19033 : Outcome ⟨6, 15, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 15, 11, 2⟩, ⟨4, 15, 11, 4⟩, ⟨3, 15, 11, 6⟩, ⟨2, 15, 11, 8⟩, ⟨1, 15, 11, 10⟩, ⟨0, 15, 11, 12⟩, ⟨6, 14, 11, 2⟩, ⟨6, 13, 11, 4⟩, ⟨6, 12, 11, 6⟩, ⟨6, 11, 11, 8⟩, ⟨6, 10, 11, 10⟩, ⟨6, 9, 11, 12⟩, ⟨6, 8, 11, 14⟩, ⟨6, 7, 11, 16⟩, ⟨6, 6, 11, 18⟩, ⟨6, 5, 11, 20⟩, ⟨6, 4, 11, 22⟩, ⟨6, 3, 11, 24⟩, ⟨6, 15, 10, 2⟩, ⟨6, 15, 9, 4⟩, ⟨6, 15, 8, 6⟩, ⟨6, 15, 7, 8⟩, ⟨6, 15, 6, 10⟩, ⟨6, 15, 5, 12⟩, ⟨6, 15, 4, 14⟩, ⟨6, 15, 3, 16⟩, ⟨6, 15, 2, 18⟩, ⟨6, 15, 1, 20⟩, ⟨6, 15, 0, 22⟩]
  exact AllWinning.cons node_18083 (AllWinning.cons node_17156 (AllWinning.cons node_16054 (AllWinning.cons node_15048 (AllWinning.cons node_14033 (AllWinning.cons node_13013 (AllWinning.cons node_18118 (AllWinning.cons node_17230 (AllWinning.cons node_16232 (AllWinning.cons node_15242 (AllWinning.cons node_14290 (AllWinning.cons node_13326 (AllWinning.cons node_12376 (AllWinning.cons node_11389 (AllWinning.cons node_10365 (AllWinning.cons node_9358 (AllWinning.cons node_8358 (AllWinning.cons node_7425 (AllWinning.cons node_18120 (AllWinning.cons node_17237 (AllWinning.cons node_16245 (AllWinning.cons node_15254 (AllWinning.cons node_14307 (AllWinning.cons node_13347 (AllWinning.cons node_12402 (AllWinning.cons node_11419 (AllWinning.cons node_10404 (AllWinning.cons node_9398 (AllWinning.cons node_8414 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19034 : Outcome ⟨6, 16, 10, 4⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 8⟩) (by decide) node_15051

theorem node_19035 : Outcome ⟨6, 16, 10, 6⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 8⟩) (by decide) node_15051

end RQ9F1
