import Chunk108
set_option autoImplicit false
namespace RQ9F1

theorem node_22827 : Outcome ⟨15, 13, 9, 10⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 16⟩) (by decide) node_16305

theorem node_22828 : Outcome ⟨15, 14, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 8, 2⟩, ⟨13, 14, 8, 4⟩, ⟨15, 13, 8, 2⟩, ⟨15, 12, 8, 4⟩, ⟨15, 14, 7, 2⟩, ⟨15, 14, 6, 4⟩]
  exact AllWinning.cons node_22202 (AllWinning.cons node_21562 (AllWinning.cons node_22253 (AllWinning.cons node_21647 (AllWinning.cons node_22256 (AllWinning.cons node_21652 (AllWinning.nil))))))

theorem node_22829 : Outcome ⟨15, 14, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 8, 2⟩, ⟨13, 14, 8, 4⟩, ⟨12, 14, 8, 6⟩, ⟨11, 14, 8, 8⟩, ⟨15, 13, 8, 2⟩, ⟨15, 12, 8, 4⟩, ⟨15, 11, 8, 6⟩, ⟨15, 10, 8, 8⟩, ⟨15, 14, 7, 2⟩, ⟨15, 14, 6, 4⟩, ⟨15, 14, 5, 6⟩, ⟨15, 14, 4, 8⟩]
  exact AllWinning.cons node_22202 (AllWinning.cons node_21562 (AllWinning.cons node_20858 (AllWinning.cons node_20068 (AllWinning.cons node_22253 (AllWinning.cons node_21647 (AllWinning.cons node_21018 (AllWinning.cons node_20268 (AllWinning.cons node_22256 (AllWinning.cons node_21652 (AllWinning.cons node_21030 (AllWinning.cons node_20277 (AllWinning.nil))))))))))))

theorem node_22830 : Outcome ⟨15, 14, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 8, 2⟩, ⟨13, 14, 8, 4⟩, ⟨12, 14, 8, 6⟩, ⟨11, 14, 8, 8⟩, ⟨10, 14, 8, 10⟩, ⟨9, 14, 8, 12⟩, ⟨15, 13, 8, 2⟩, ⟨15, 12, 8, 4⟩, ⟨15, 11, 8, 6⟩, ⟨15, 10, 8, 8⟩, ⟨15, 9, 8, 10⟩, ⟨15, 8, 8, 12⟩, ⟨15, 14, 7, 2⟩, ⟨15, 14, 6, 4⟩, ⟨15, 14, 5, 6⟩, ⟨15, 14, 4, 8⟩, ⟨15, 14, 3, 10⟩, ⟨15, 14, 2, 12⟩]
  exact AllWinning.cons node_22202 (AllWinning.cons node_21562 (AllWinning.cons node_20858 (AllWinning.cons node_20068 (AllWinning.cons node_19235 (AllWinning.cons node_18283 (AllWinning.cons node_22253 (AllWinning.cons node_21647 (AllWinning.cons node_21018 (AllWinning.cons node_20268 (AllWinning.cons node_19492 (AllWinning.cons node_18627 (AllWinning.cons node_22256 (AllWinning.cons node_21652 (AllWinning.cons node_21030 (AllWinning.cons node_20277 (AllWinning.cons node_19511 (AllWinning.cons node_18646 (AllWinning.nil))))))))))))))))))

theorem node_22831 : Outcome ⟨15, 14, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 14, 8, 2⟩, ⟨13, 14, 8, 4⟩, ⟨12, 14, 8, 6⟩, ⟨11, 14, 8, 8⟩, ⟨10, 14, 8, 10⟩, ⟨9, 14, 8, 12⟩, ⟨8, 14, 8, 14⟩, ⟨7, 14, 8, 16⟩, ⟨15, 13, 8, 2⟩, ⟨15, 12, 8, 4⟩, ⟨15, 11, 8, 6⟩, ⟨15, 10, 8, 8⟩, ⟨15, 9, 8, 10⟩, ⟨15, 8, 8, 12⟩, ⟨15, 7, 8, 14⟩, ⟨15, 6, 8, 16⟩, ⟨15, 14, 7, 2⟩, ⟨15, 14, 6, 4⟩, ⟨15, 14, 5, 6⟩, ⟨15, 14, 4, 8⟩, ⟨15, 14, 3, 10⟩, ⟨15, 14, 2, 12⟩, ⟨15, 14, 1, 14⟩, ⟨15, 14, 0, 16⟩]
  exact AllWinning.cons node_22202 (AllWinning.cons node_21562 (AllWinning.cons node_20858 (AllWinning.cons node_20068 (AllWinning.cons node_19235 (AllWinning.cons node_18283 (AllWinning.cons node_17336 (AllWinning.cons node_16310 (AllWinning.cons node_22253 (AllWinning.cons node_21647 (AllWinning.cons node_21018 (AllWinning.cons node_20268 (AllWinning.cons node_19492 (AllWinning.cons node_18627 (AllWinning.cons node_17717 (AllWinning.cons node_16796 (AllWinning.cons node_22256 (AllWinning.cons node_21652 (AllWinning.cons node_21030 (AllWinning.cons node_20277 (AllWinning.cons node_19511 (AllWinning.cons node_18646 (AllWinning.cons node_17740 (AllWinning.cons node_16816 (AllWinning.nil))))))))))))))))))))))))

theorem node_22832 : Outcome ⟨15, 14, 8, 10⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 18⟩) (by decide) node_15751

theorem node_22833 : Outcome ⟨15, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 6⟩) (by decide) node_20861

theorem node_22834 : Outcome ⟨15, 15, 7, 6⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 6⟩) (by decide) node_20861

theorem node_22835 : Outcome ⟨15, 16, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 6, 2⟩, ⟨13, 16, 6, 4⟩, ⟨15, 15, 6, 2⟩, ⟨15, 14, 6, 4⟩, ⟨15, 16, 5, 2⟩, ⟨15, 16, 4, 4⟩]
  exact AllWinning.cons node_22206 (AllWinning.cons node_21569 (AllWinning.cons node_22258 (AllWinning.cons node_21652 (AllWinning.cons node_22261 (AllWinning.cons node_21659 (AllWinning.nil))))))

theorem node_22836 : Outcome ⟨15, 16, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 6⟩) (by decide) node_20866

theorem node_22837 : Outcome ⟨15, 16, 6, 8⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 10⟩) (by decide) node_19500

theorem node_22838 : Outcome ⟨15, 16, 6, 12⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 10⟩) (by decide) node_19500

theorem node_22839 : Outcome ⟨15, 17, 5, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 5, 4⟩) (by decide) node_21656

theorem node_22840 : Outcome ⟨15, 18, 4, 4⟩ true :=
  Outcome.win (q := ⟨11, 18, 4, 8⟩) (by decide) node_20076

theorem node_22841 : Outcome ⟨15, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 2⟩) (by decide) node_22266

theorem node_22842 : Outcome ⟨15, 19, 3, 4⟩ true :=
  Outcome.win (q := ⟨11, 19, 3, 8⟩) (by decide) node_20081

theorem node_22843 : Outcome ⟨15, 20, 2, 8⟩ true :=
  Outcome.win (q := ⟨15, 20, 0, 4⟩) (by decide) node_21663

theorem node_22844 : Outcome ⟨16, 2, 19, 2⟩ true :=
  Outcome.win (q := ⟨16, 2, 18, 2⟩) (by decide) node_22277

theorem node_22845 : Outcome ⟨16, 3, 18, 2⟩ true :=
  Outcome.win (q := ⟨15, 3, 18, 2⟩) (by decide) node_22219

theorem node_22846 : Outcome ⟨16, 4, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 4, 17, 2⟩) (by decide) node_22227

theorem node_22847 : Outcome ⟨16, 5, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 5, 16, 2⟩, ⟨14, 5, 16, 4⟩, ⟨16, 4, 16, 2⟩, ⟨16, 3, 16, 4⟩, ⟨16, 5, 15, 2⟩, ⟨16, 5, 14, 4⟩]
  exact AllWinning.cons node_22230 (AllWinning.cons node_21588 (AllWinning.cons node_22283 (AllWinning.cons node_21670 (AllWinning.cons node_22285 (AllWinning.cons node_21674 (AllWinning.nil))))))

theorem node_22848 : Outcome ⟨16, 5, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 5, 16, 2⟩, ⟨14, 5, 16, 4⟩, ⟨13, 5, 16, 6⟩, ⟨12, 5, 16, 8⟩, ⟨16, 4, 16, 2⟩, ⟨16, 3, 16, 4⟩, ⟨16, 2, 16, 6⟩, ⟨16, 1, 16, 8⟩, ⟨16, 5, 15, 2⟩, ⟨16, 5, 14, 4⟩, ⟨16, 5, 13, 6⟩, ⟨16, 5, 12, 8⟩]
  exact AllWinning.cons node_22230 (AllWinning.cons node_21588 (AllWinning.cons node_20888 (AllWinning.cons node_20095 (AllWinning.cons node_22283 (AllWinning.cons node_21670 (AllWinning.cons node_21045 (AllWinning.cons node_20289 (AllWinning.cons node_22285 (AllWinning.cons node_21674 (AllWinning.cons node_21053 (AllWinning.cons node_20297 (AllWinning.nil))))))))))))

theorem node_22849 : Outcome ⟨16, 5, 16, 6⟩ true :=
  Outcome.win (q := ⟨16, 0, 16, 10⟩) (by decide) node_19531

theorem node_22850 : Outcome ⟨16, 5, 16, 16⟩ true :=
  Outcome.win (q := ⟨16, 0, 16, 10⟩) (by decide) node_19531

theorem node_22851 : Outcome ⟨16, 6, 15, 4⟩ true :=
  Outcome.win (q := ⟨16, 6, 12, 6⟩) (by decide) node_21056

theorem node_22852 : Outcome ⟨16, 6, 15, 12⟩ true :=
  Outcome.win (q := ⟨11, 6, 15, 10⟩) (by decide) node_19267

theorem node_22853 : Outcome ⟨16, 7, 14, 6⟩ true :=
  Outcome.win (q := ⟨16, 7, 11, 6⟩) (by decide) node_21063

theorem node_22854 : Outcome ⟨16, 8, 13, 6⟩ true :=
  Outcome.win (q := ⟨13, 8, 13, 6⟩) (by decide) node_20895

theorem node_22855 : Outcome ⟨16, 8, 13, 16⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 20⟩) (by decide) node_14822

theorem node_22856 : Outcome ⟨16, 9, 12, 2⟩ true :=
  Outcome.win (q := ⟨16, 9, 10, 4⟩) (by decide) node_21681

theorem node_22857 : Outcome ⟨16, 9, 12, 6⟩ true :=
  Outcome.win (q := ⟨16, 6, 12, 6⟩) (by decide) node_21056

theorem node_22858 : Outcome ⟨16, 9, 12, 12⟩ true :=
  Outcome.win (q := ⟨16, 9, 4, 16⟩) (by decide) node_16853

theorem node_22859 : Outcome ⟨16, 10, 11, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 9, 4⟩) (by decide) node_21683

theorem node_22860 : Outcome ⟨16, 10, 11, 6⟩ true :=
  Outcome.win (q := ⟨16, 7, 11, 6⟩) (by decide) node_21063

theorem node_22861 : Outcome ⟨16, 11, 10, 2⟩ true :=
  Outcome.win (q := ⟨16, 9, 10, 4⟩) (by decide) node_21681

theorem node_22862 : Outcome ⟨16, 11, 10, 6⟩ true :=
  Outcome.win (q := ⟨16, 11, 7, 6⟩) (by decide) node_21075

theorem node_22863 : Outcome ⟨16, 12, 9, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 9, 4⟩) (by decide) node_21683

theorem node_22864 : Outcome ⟨16, 12, 9, 6⟩ true :=
  Outcome.win (q := ⟨16, 12, 6, 6⟩) (by decide) node_21080

theorem node_22865 : Outcome ⟨16, 12, 9, 12⟩ true :=
  Outcome.win (q := ⟨16, 4, 9, 16⟩) (by decide) node_16835

theorem node_22866 : Outcome ⟨16, 13, 8, 6⟩ true :=
  Outcome.win (q := ⟨13, 13, 8, 6⟩) (by decide) node_20911

theorem node_22867 : Outcome ⟨16, 13, 8, 16⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 20⟩) (by decide) node_14804

theorem node_22868 : Outcome ⟨16, 14, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 14, 7, 2⟩, ⟨14, 14, 7, 4⟩, ⟨16, 13, 7, 2⟩, ⟨16, 12, 7, 4⟩, ⟨16, 14, 6, 2⟩, ⟨16, 14, 5, 4⟩]
  exact AllWinning.cons node_22256 (AllWinning.cons node_21607 (AllWinning.cons node_22302 (AllWinning.cons node_21687 (AllWinning.cons node_22305 (AllWinning.cons node_21690 (AllWinning.nil))))))

theorem node_22869 : Outcome ⟨16, 14, 7, 6⟩ true :=
  Outcome.win (q := ⟨16, 11, 7, 6⟩) (by decide) node_21075

theorem node_22870 : Outcome ⟨16, 15, 6, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 6, 6⟩) (by decide) node_21080

theorem node_22871 : Outcome ⟨16, 15, 6, 12⟩ true :=
  Outcome.win (q := ⟨11, 15, 6, 10⟩) (by decide) node_19291

theorem node_22872 : Outcome ⟨16, 16, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 5, 2⟩, ⟨14, 16, 5, 4⟩, ⟨16, 15, 5, 2⟩, ⟨16, 14, 5, 4⟩, ⟨16, 16, 4, 2⟩, ⟨16, 16, 3, 4⟩]
  exact AllWinning.cons node_22261 (AllWinning.cons node_21610 (AllWinning.cons node_22308 (AllWinning.cons node_21690 (AllWinning.cons node_22309 (AllWinning.cons node_21693 (AllWinning.nil))))))

theorem node_22873 : Outcome ⟨16, 16, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 16, 5, 2⟩, ⟨14, 16, 5, 4⟩, ⟨13, 16, 5, 6⟩, ⟨12, 16, 5, 8⟩, ⟨16, 15, 5, 2⟩, ⟨16, 14, 5, 4⟩, ⟨16, 13, 5, 6⟩, ⟨16, 12, 5, 8⟩, ⟨16, 16, 4, 2⟩, ⟨16, 16, 3, 4⟩, ⟨16, 16, 2, 6⟩, ⟨16, 16, 1, 8⟩]
  exact AllWinning.cons node_22261 (AllWinning.cons node_21610 (AllWinning.cons node_20919 (AllWinning.cons node_20116 (AllWinning.cons node_22308 (AllWinning.cons node_21690 (AllWinning.cons node_21083 (AllWinning.cons node_20310 (AllWinning.cons node_22309 (AllWinning.cons node_21693 (AllWinning.cons node_21091 (AllWinning.cons node_20316 (AllWinning.nil))))))))))))

theorem node_22874 : Outcome ⟨16, 16, 5, 6⟩ true :=
  Outcome.win (q := ⟨16, 16, 0, 10⟩) (by decide) node_19583

theorem node_22875 : Outcome ⟨16, 16, 5, 16⟩ true :=
  Outcome.win (q := ⟨16, 16, 0, 10⟩) (by decide) node_19583

theorem node_22876 : Outcome ⟨16, 17, 4, 4⟩ true :=
  Outcome.win (q := ⟨15, 17, 4, 2⟩) (by decide) node_22263

theorem node_22877 : Outcome ⟨16, 18, 3, 2⟩ true :=
  Outcome.win (q := ⟨15, 18, 3, 2⟩) (by decide) node_22266

theorem node_22878 : Outcome ⟨16, 19, 2, 2⟩ true :=
  Outcome.win (q := ⟨16, 18, 2, 2⟩) (by decide) node_22313

theorem node_22879 : Outcome ⟨17, 1, 19, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 18, 2⟩) (by decide) node_22319

theorem node_22880 : Outcome ⟨17, 2, 18, 2⟩ true :=
  Outcome.win (q := ⟨16, 2, 18, 2⟩) (by decide) node_22277

theorem node_22881 : Outcome ⟨17, 2, 18, 4⟩ true :=
  Outcome.win (q := ⟨16, 2, 18, 2⟩) (by decide) node_22277

theorem node_22882 : Outcome ⟨17, 3, 17, 4⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 6⟩) (by decide) node_20937

theorem node_22883 : Outcome ⟨17, 4, 16, 4⟩ true :=
  Outcome.win (q := ⟨17, 4, 15, 2⟩) (by decide) node_22324

theorem node_22884 : Outcome ⟨17, 4, 16, 10⟩ true :=
  Outcome.win (q := ⟨9, 4, 16, 16⟩) (by decide) node_16418

theorem node_22885 : Outcome ⟨17, 5, 15, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 15, 4⟩) (by decide) node_21629

theorem node_22886 : Outcome ⟨17, 6, 14, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 13, 2⟩) (by decide) node_22327

theorem node_22887 : Outcome ⟨17, 6, 14, 4⟩ true :=
  Outcome.win (q := ⟨13, 6, 14, 8⟩) (by decide) node_20141

theorem node_22888 : Outcome ⟨17, 7, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 13, 2⟩) (by decide) node_22327

theorem node_22889 : Outcome ⟨17, 8, 12, 2⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 2⟩) (by decide) node_22331

theorem node_22890 : Outcome ⟨17, 8, 12, 10⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 16⟩) (by decide) node_16898

theorem node_22891 : Outcome ⟨17, 9, 11, 2⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 2⟩) (by decide) node_22331

theorem node_22892 : Outcome ⟨17, 9, 11, 10⟩ true :=
  Outcome.win (q := ⟨17, 9, 6, 10⟩) (by decide) node_19615

theorem node_22893 : Outcome ⟨17, 10, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 10, 10, 2⟩, ⟨15, 10, 10, 4⟩, ⟨14, 10, 10, 6⟩, ⟨13, 10, 10, 8⟩, ⟨17, 9, 10, 2⟩, ⟨17, 8, 10, 4⟩, ⟨17, 7, 10, 6⟩, ⟨17, 6, 10, 8⟩, ⟨17, 10, 9, 2⟩, ⟨17, 10, 8, 4⟩, ⟨17, 10, 7, 6⟩, ⟨17, 10, 6, 8⟩]
  exact AllWinning.cons node_22295 (AllWinning.cons node_21643 (AllWinning.cons node_20956 (AllWinning.cons node_20156 (AllWinning.cons node_22334 (AllWinning.cons node_21718 (AllWinning.cons node_21113 (AllWinning.cons node_20329 (AllWinning.cons node_22337 (AllWinning.cons node_21721 (AllWinning.cons node_21120 (AllWinning.cons node_20335 (AllWinning.nil))))))))))))

theorem node_22894 : Outcome ⟨17, 10, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 10, 10, 2⟩, ⟨15, 10, 10, 4⟩, ⟨14, 10, 10, 6⟩, ⟨13, 10, 10, 8⟩, ⟨12, 10, 10, 10⟩, ⟨11, 10, 10, 12⟩, ⟨17, 9, 10, 2⟩, ⟨17, 8, 10, 4⟩, ⟨17, 7, 10, 6⟩, ⟨17, 6, 10, 8⟩, ⟨17, 5, 10, 10⟩, ⟨17, 4, 10, 12⟩, ⟨17, 10, 9, 2⟩, ⟨17, 10, 8, 4⟩, ⟨17, 10, 7, 6⟩, ⟨17, 10, 6, 8⟩, ⟨17, 10, 5, 10⟩, ⟨17, 10, 4, 12⟩]
  exact AllWinning.cons node_22295 (AllWinning.cons node_21643 (AllWinning.cons node_20956 (AllWinning.cons node_20156 (AllWinning.cons node_19328 (AllWinning.cons node_18389 (AllWinning.cons node_22334 (AllWinning.cons node_21718 (AllWinning.cons node_21113 (AllWinning.cons node_20329 (AllWinning.cons node_19599 (AllWinning.cons node_18709 (AllWinning.cons node_22337 (AllWinning.cons node_21721 (AllWinning.cons node_21120 (AllWinning.cons node_20335 (AllWinning.cons node_19619 (AllWinning.cons node_18720 (AllWinning.nil))))))))))))))))))

theorem node_22895 : Outcome ⟨17, 10, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 10, 10, 2⟩, ⟨15, 10, 10, 4⟩, ⟨14, 10, 10, 6⟩, ⟨13, 10, 10, 8⟩, ⟨12, 10, 10, 10⟩, ⟨11, 10, 10, 12⟩, ⟨10, 10, 10, 14⟩, ⟨9, 10, 10, 16⟩, ⟨8, 10, 10, 18⟩, ⟨7, 10, 10, 20⟩, ⟨6, 10, 10, 22⟩, ⟨5, 10, 10, 24⟩, ⟨17, 9, 10, 2⟩, ⟨17, 8, 10, 4⟩, ⟨17, 7, 10, 6⟩, ⟨17, 6, 10, 8⟩, ⟨17, 5, 10, 10⟩, ⟨17, 4, 10, 12⟩, ⟨17, 3, 10, 14⟩, ⟨17, 2, 10, 16⟩, ⟨17, 1, 10, 18⟩, ⟨17, 0, 10, 20⟩, ⟨17, 10, 9, 2⟩, ⟨17, 10, 8, 4⟩, ⟨17, 10, 7, 6⟩, ⟨17, 10, 6, 8⟩, ⟨17, 10, 5, 10⟩, ⟨17, 10, 4, 12⟩, ⟨17, 10, 3, 14⟩, ⟨17, 10, 2, 16⟩, ⟨17, 10, 1, 18⟩, ⟨17, 10, 0, 20⟩]
  exact AllWinning.cons node_22295 (AllWinning.cons node_21643 (AllWinning.cons node_20956 (AllWinning.cons node_20156 (AllWinning.cons node_19328 (AllWinning.cons node_18389 (AllWinning.cons node_17434 (AllWinning.cons node_16444 (AllWinning.cons node_15355 (AllWinning.cons node_14362 (AllWinning.cons node_13329 (AllWinning.cons node_12311 (AllWinning.cons node_22334 (AllWinning.cons node_21718 (AllWinning.cons node_21113 (AllWinning.cons node_20329 (AllWinning.cons node_19599 (AllWinning.cons node_18709 (AllWinning.cons node_17798 (AllWinning.cons node_16871 (AllWinning.cons node_15825 (AllWinning.cons node_14837 (AllWinning.cons node_22337 (AllWinning.cons node_21721 (AllWinning.cons node_21120 (AllWinning.cons node_20335 (AllWinning.cons node_19619 (AllWinning.cons node_18720 (AllWinning.cons node_17812 (AllWinning.cons node_16904 (AllWinning.cons node_15843 (AllWinning.cons node_14861 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_22896 : Outcome ⟨17, 11, 9, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 8, 2⟩) (by decide) node_22339

theorem node_22897 : Outcome ⟨17, 12, 8, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 8, 2⟩) (by decide) node_22339

theorem node_22898 : Outcome ⟨17, 13, 7, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 6, 2⟩) (by decide) node_22342

theorem node_22899 : Outcome ⟨17, 13, 7, 4⟩ true :=
  Outcome.win (q := ⟨17, 13, 6, 2⟩) (by decide) node_22342

theorem node_22900 : Outcome ⟨17, 13, 7, 10⟩ true :=
  Outcome.win (q := ⟨9, 13, 7, 16⟩) (by decide) node_16457

theorem node_22901 : Outcome ⟨17, 14, 6, 4⟩ true :=
  Outcome.win (q := ⟨13, 14, 6, 8⟩) (by decide) node_20167

theorem node_22902 : Outcome ⟨17, 15, 5, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 5, 4⟩) (by decide) node_21656

theorem node_22903 : Outcome ⟨17, 16, 4, 4⟩ true :=
  Outcome.win (q := ⟨17, 15, 4, 2⟩) (by decide) node_22346

theorem node_22904 : Outcome ⟨17, 17, 3, 4⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 6⟩) (by decide) node_20974

theorem node_22905 : Outcome ⟨17, 18, 2, 2⟩ true :=
  Outcome.win (q := ⟨16, 18, 2, 2⟩) (by decide) node_22313

theorem node_22906 : Outcome ⟨17, 18, 2, 4⟩ true :=
  Outcome.win (q := ⟨16, 18, 2, 2⟩) (by decide) node_22313

theorem node_22907 : Outcome ⟨17, 19, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 18, 1, 2⟩) (by decide) node_22351

theorem node_22908 : Outcome ⟨18, 0, 19, 2⟩ true :=
  Outcome.win (q := ⟨18, 0, 18, 2⟩) (by decide) node_22353

theorem node_22909 : Outcome ⟨18, 1, 18, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 18, 2⟩) (by decide) node_22319

theorem node_22910 : Outcome ⟨18, 1, 18, 8⟩ true :=
  Outcome.win (q := ⟨17, 1, 18, 2⟩) (by decide) node_22319

theorem node_22911 : Outcome ⟨18, 2, 17, 2⟩ true :=
  Outcome.win (q := ⟨18, 1, 17, 2⟩) (by decide) node_22354

theorem node_22912 : Outcome ⟨18, 5, 14, 2⟩ true :=
  Outcome.win (q := ⟨18, 5, 12, 4⟩) (by decide) node_21745

theorem node_22913 : Outcome ⟨18, 5, 14, 8⟩ true :=
  Outcome.win (q := ⟨18, 5, 12, 4⟩) (by decide) node_21745

theorem node_22914 : Outcome ⟨18, 6, 13, 2⟩ true :=
  Outcome.win (q := ⟨17, 6, 13, 2⟩) (by decide) node_22327

theorem node_22915 : Outcome ⟨18, 7, 12, 2⟩ true :=
  Outcome.win (q := ⟨18, 5, 12, 4⟩) (by decide) node_21745

theorem node_22916 : Outcome ⟨18, 8, 11, 2⟩ true :=
  Outcome.win (q := ⟨17, 8, 11, 2⟩) (by decide) node_22331

theorem node_22917 : Outcome ⟨18, 9, 10, 2⟩ true :=
  Outcome.win (q := ⟨16, 9, 10, 4⟩) (by decide) node_21681

theorem node_22918 : Outcome ⟨18, 10, 9, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 9, 4⟩) (by decide) node_21683

theorem node_22919 : Outcome ⟨18, 11, 8, 2⟩ true :=
  Outcome.win (q := ⟨17, 11, 8, 2⟩) (by decide) node_22339

theorem node_22920 : Outcome ⟨18, 12, 7, 2⟩ true :=
  Outcome.win (q := ⟨18, 12, 5, 4⟩) (by decide) node_21752

theorem node_22921 : Outcome ⟨18, 13, 6, 2⟩ true :=
  Outcome.win (q := ⟨17, 13, 6, 2⟩) (by decide) node_22342

theorem node_22922 : Outcome ⟨18, 14, 5, 8⟩ true :=
  Outcome.win (q := ⟨18, 12, 5, 4⟩) (by decide) node_21752

theorem node_22923 : Outcome ⟨18, 17, 2, 2⟩ true :=
  Outcome.win (q := ⟨18, 16, 2, 2⟩) (by decide) node_22376

theorem node_22924 : Outcome ⟨18, 18, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 18, 1, 2⟩) (by decide) node_22351

theorem node_22925 : Outcome ⟨18, 18, 1, 8⟩ true :=
  Outcome.win (q := ⟨17, 18, 1, 2⟩) (by decide) node_22351

theorem node_22926 : Outcome ⟨18, 19, 0, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 0, 2⟩) (by decide) node_22380

theorem node_22927 : Outcome ⟨19, 0, 18, 2⟩ true :=
  Outcome.win (q := ⟨18, 0, 18, 2⟩) (by decide) node_22353

theorem node_22928 : Outcome ⟨19, 1, 17, 2⟩ true :=
  Outcome.win (q := ⟨18, 1, 17, 2⟩) (by decide) node_22354

theorem node_22929 : Outcome ⟨19, 2, 16, 2⟩ true :=
  Outcome.win (q := ⟨18, 2, 16, 2⟩) (by decide) node_22356

theorem node_22930 : Outcome ⟨19, 4, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 4, 14, 2⟩, ⟨17, 4, 14, 4⟩, ⟨16, 4, 14, 6⟩, ⟨15, 4, 14, 8⟩, ⟨14, 4, 14, 10⟩, ⟨13, 4, 14, 12⟩, ⟨19, 3, 14, 2⟩, ⟨19, 2, 14, 4⟩, ⟨19, 1, 14, 6⟩, ⟨19, 0, 14, 8⟩, ⟨19, 4, 13, 2⟩, ⟨19, 4, 12, 4⟩, ⟨19, 4, 11, 6⟩, ⟨19, 4, 10, 8⟩, ⟨19, 4, 9, 10⟩, ⟨19, 4, 8, 12⟩]
  exact AllWinning.cons node_22360 (AllWinning.cons node_21709 (AllWinning.cons node_21051 (AllWinning.cons node_20254 (AllWinning.cons node_19421 (AllWinning.cons node_18496 (AllWinning.cons node_22383 (AllWinning.cons node_21762 (AllWinning.cons node_21165 (AllWinning.cons node_20380 (AllWinning.cons node_22384 (AllWinning.cons node_21766 (AllWinning.cons node_21169 (AllWinning.cons node_20388 (AllWinning.cons node_19667 (AllWinning.cons node_18784 (AllWinning.nil))))))))))))))))

theorem node_22931 : Outcome ⟨19, 4, 14, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 4, 14, 2⟩, ⟨17, 4, 14, 4⟩, ⟨16, 4, 14, 6⟩, ⟨15, 4, 14, 8⟩, ⟨14, 4, 14, 10⟩, ⟨13, 4, 14, 12⟩, ⟨12, 4, 14, 14⟩, ⟨11, 4, 14, 16⟩, ⟨10, 4, 14, 18⟩, ⟨9, 4, 14, 20⟩, ⟨8, 4, 14, 22⟩, ⟨7, 4, 14, 24⟩, ⟨6, 4, 14, 26⟩, ⟨5, 4, 14, 28⟩, ⟨4, 4, 14, 30⟩, ⟨3, 4, 14, 32⟩, ⟨2, 4, 14, 34⟩, ⟨1, 4, 14, 36⟩, ⟨19, 3, 14, 2⟩, ⟨19, 2, 14, 4⟩, ⟨19, 1, 14, 6⟩, ⟨19, 0, 14, 8⟩, ⟨19, 4, 13, 2⟩, ⟨19, 4, 12, 4⟩, ⟨19, 4, 11, 6⟩, ⟨19, 4, 10, 8⟩, ⟨19, 4, 9, 10⟩, ⟨19, 4, 8, 12⟩, ⟨19, 4, 7, 14⟩, ⟨19, 4, 6, 16⟩, ⟨19, 4, 5, 18⟩, ⟨19, 4, 4, 20⟩, ⟨19, 4, 3, 22⟩, ⟨19, 4, 2, 24⟩, ⟨19, 4, 1, 26⟩, ⟨19, 4, 0, 28⟩]
  exact AllWinning.cons node_22360 (AllWinning.cons node_21709 (AllWinning.cons node_21051 (AllWinning.cons node_20254 (AllWinning.cons node_19421 (AllWinning.cons node_18496 (AllWinning.cons node_17533 (AllWinning.cons node_16556 (AllWinning.cons node_15464 (AllWinning.cons node_14474 (AllWinning.cons node_13442 (AllWinning.cons node_12439 (AllWinning.cons node_11378 (AllWinning.cons node_10267 (AllWinning.cons node_9214 (AllWinning.cons node_8164 (AllWinning.cons node_7136 (AllWinning.cons node_6129 (AllWinning.cons node_22383 (AllWinning.cons node_21762 (AllWinning.cons node_21165 (AllWinning.cons node_20380 (AllWinning.cons node_22384 (AllWinning.cons node_21766 (AllWinning.cons node_21169 (AllWinning.cons node_20388 (AllWinning.cons node_19667 (AllWinning.cons node_18784 (AllWinning.cons node_17864 (AllWinning.cons node_16952 (AllWinning.cons node_15888 (AllWinning.cons node_14910 (AllWinning.cons node_13936 (AllWinning.cons node_12969 (AllWinning.cons node_11955 (AllWinning.cons node_10972 (AllWinning.nil))))))))))))))))))))))))))))))))))))

theorem node_22932 : Outcome ⟨19, 5, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 5, 13, 2⟩, ⟨17, 5, 13, 4⟩, ⟨19, 4, 13, 2⟩, ⟨19, 3, 13, 4⟩, ⟨19, 5, 12, 2⟩, ⟨19, 5, 11, 4⟩]
  exact AllWinning.cons node_22362 (AllWinning.cons node_21711 (AllWinning.cons node_22384 (AllWinning.cons node_21764 (AllWinning.cons node_22386 (AllWinning.cons node_21767 (AllWinning.nil))))))

theorem node_22933 : Outcome ⟨19, 5, 13, 6⟩ true :=
  Outcome.win (q := ⟨19, 5, 10, 6⟩) (by decide) node_21171

theorem node_22934 : Outcome ⟨19, 7, 11, 6⟩ true :=
  Outcome.win (q := ⟨19, 7, 6, 10⟩) (by decide) node_19673

theorem node_22935 : Outcome ⟨19, 8, 10, 6⟩ true :=
  Outcome.win (q := ⟨19, 5, 10, 6⟩) (by decide) node_21171

theorem node_22936 : Outcome ⟨19, 10, 8, 6⟩ true :=
  Outcome.win (q := ⟨19, 10, 5, 6⟩) (by decide) node_21178

theorem node_22937 : Outcome ⟨19, 11, 7, 6⟩ true :=
  Outcome.win (q := ⟨19, 6, 7, 10⟩) (by decide) node_19671

theorem node_22938 : Outcome ⟨19, 13, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 13, 5, 2⟩, ⟨17, 13, 5, 4⟩, ⟨19, 12, 5, 2⟩, ⟨19, 11, 5, 4⟩, ⟨19, 13, 4, 2⟩, ⟨19, 13, 3, 4⟩]
  exact AllWinning.cons node_22371 (AllWinning.cons node_21727 (AllWinning.cons node_22393 (AllWinning.cons node_21769 (AllWinning.cons node_22394 (AllWinning.cons node_21771 (AllWinning.nil))))))

theorem node_22939 : Outcome ⟨19, 13, 5, 6⟩ true :=
  Outcome.win (q := ⟨19, 10, 5, 6⟩) (by decide) node_21178

theorem node_22940 : Outcome ⟨19, 14, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 14, 4, 2⟩, ⟨17, 14, 4, 4⟩, ⟨16, 14, 4, 6⟩, ⟨15, 14, 4, 8⟩, ⟨14, 14, 4, 10⟩, ⟨13, 14, 4, 12⟩, ⟨19, 13, 4, 2⟩, ⟨19, 12, 4, 4⟩, ⟨19, 11, 4, 6⟩, ⟨19, 10, 4, 8⟩, ⟨19, 9, 4, 10⟩, ⟨19, 8, 4, 12⟩, ⟨19, 14, 3, 2⟩, ⟨19, 14, 2, 4⟩, ⟨19, 14, 1, 6⟩, ⟨19, 14, 0, 8⟩]
  exact AllWinning.cons node_22373 (AllWinning.cons node_21730 (AllWinning.cons node_21086 (AllWinning.cons node_20277 (AllWinning.cons node_19442 (AllWinning.cons node_18527 (AllWinning.cons node_22394 (AllWinning.cons node_21770 (AllWinning.cons node_21182 (AllWinning.cons node_20394 (AllWinning.cons node_19677 (AllWinning.cons node_18791 (AllWinning.cons node_22396 (AllWinning.cons node_21773 (AllWinning.cons node_21186 (AllWinning.cons node_20401 (AllWinning.nil))))))))))))))))

theorem node_22941 : Outcome ⟨19, 14, 4, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 14, 4, 2⟩, ⟨17, 14, 4, 4⟩, ⟨16, 14, 4, 6⟩, ⟨15, 14, 4, 8⟩, ⟨14, 14, 4, 10⟩, ⟨13, 14, 4, 12⟩, ⟨12, 14, 4, 14⟩, ⟨11, 14, 4, 16⟩, ⟨10, 14, 4, 18⟩, ⟨9, 14, 4, 20⟩, ⟨8, 14, 4, 22⟩, ⟨7, 14, 4, 24⟩, ⟨6, 14, 4, 26⟩, ⟨5, 14, 4, 28⟩, ⟨4, 14, 4, 30⟩, ⟨3, 14, 4, 32⟩, ⟨2, 14, 4, 34⟩, ⟨1, 14, 4, 36⟩, ⟨19, 13, 4, 2⟩, ⟨19, 12, 4, 4⟩, ⟨19, 11, 4, 6⟩, ⟨19, 10, 4, 8⟩, ⟨19, 9, 4, 10⟩, ⟨19, 8, 4, 12⟩, ⟨19, 7, 4, 14⟩, ⟨19, 6, 4, 16⟩, ⟨19, 5, 4, 18⟩, ⟨19, 4, 4, 20⟩, ⟨19, 3, 4, 22⟩, ⟨19, 2, 4, 24⟩, ⟨19, 1, 4, 26⟩, ⟨19, 0, 4, 28⟩, ⟨19, 14, 3, 2⟩, ⟨19, 14, 2, 4⟩, ⟨19, 14, 1, 6⟩, ⟨19, 14, 0, 8⟩]
  exact AllWinning.cons node_22373 (AllWinning.cons node_21730 (AllWinning.cons node_21086 (AllWinning.cons node_20277 (AllWinning.cons node_19442 (AllWinning.cons node_18527 (AllWinning.cons node_17562 (AllWinning.cons node_16589 (AllWinning.cons node_15493 (AllWinning.cons node_14500 (AllWinning.cons node_13474 (AllWinning.cons node_12468 (AllWinning.cons node_11417 (AllWinning.cons node_10318 (AllWinning.cons node_9255 (AllWinning.cons node_8203 (AllWinning.cons node_7182 (AllWinning.cons node_6183 (AllWinning.cons node_22394 (AllWinning.cons node_21770 (AllWinning.cons node_21182 (AllWinning.cons node_20394 (AllWinning.cons node_19677 (AllWinning.cons node_18791 (AllWinning.cons node_17870 (AllWinning.cons node_16956 (AllWinning.cons node_15891 (AllWinning.cons node_14910 (AllWinning.cons node_13935 (AllWinning.cons node_12966 (AllWinning.cons node_11949 (AllWinning.cons node_10957 (AllWinning.cons node_22396 (AllWinning.cons node_21773 (AllWinning.cons node_21186 (AllWinning.cons node_20401 (AllWinning.nil))))))))))))))))))))))))))))))))))))

theorem node_22942 : Outcome ⟨19, 16, 2, 2⟩ true :=
  Outcome.win (q := ⟨18, 16, 2, 2⟩) (by decide) node_22376

theorem node_22943 : Outcome ⟨19, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨18, 17, 1, 2⟩) (by decide) node_22378

theorem node_22944 : Outcome ⟨19, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨18, 18, 0, 2⟩) (by decide) node_22380

theorem node_22945 : Outcome ⟨0, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 4⟩) (by decide) node_21781

theorem node_22946 : Outcome ⟨0, 19, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨0, 17, 19, 4⟩, ⟨0, 19, 18, 2⟩, ⟨0, 19, 17, 4⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_21779 (AllWinning.cons node_22401 (AllWinning.cons node_21785 (AllWinning.nil))))

theorem node_22947 : Outcome ⟨0, 19, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨0, 17, 19, 4⟩, ⟨0, 16, 19, 6⟩, ⟨0, 15, 19, 8⟩, ⟨0, 19, 18, 2⟩, ⟨0, 19, 17, 4⟩, ⟨0, 19, 16, 6⟩, ⟨0, 19, 15, 8⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_21779 (AllWinning.cons node_21192 (AllWinning.cons node_20407 (AllWinning.cons node_22401 (AllWinning.cons node_21785 (AllWinning.cons node_21195 (AllWinning.cons node_20416 (AllWinning.nil))))))))

theorem node_22948 : Outcome ⟨0, 19, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨0, 17, 19, 4⟩, ⟨0, 16, 19, 6⟩, ⟨0, 15, 19, 8⟩, ⟨0, 14, 19, 10⟩, ⟨0, 13, 19, 12⟩, ⟨0, 19, 18, 2⟩, ⟨0, 19, 17, 4⟩, ⟨0, 19, 16, 6⟩, ⟨0, 19, 15, 8⟩, ⟨0, 19, 14, 10⟩, ⟨0, 19, 13, 12⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_21779 (AllWinning.cons node_21192 (AllWinning.cons node_20407 (AllWinning.cons node_19696 (AllWinning.cons node_18805 (AllWinning.cons node_22401 (AllWinning.cons node_21785 (AllWinning.cons node_21195 (AllWinning.cons node_20416 (AllWinning.cons node_19706 (AllWinning.cons node_18827 (AllWinning.nil))))))))))))

theorem node_22949 : Outcome ⟨0, 19, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨0, 17, 19, 4⟩, ⟨0, 16, 19, 6⟩, ⟨0, 15, 19, 8⟩, ⟨0, 14, 19, 10⟩, ⟨0, 13, 19, 12⟩, ⟨0, 12, 19, 14⟩, ⟨0, 11, 19, 16⟩, ⟨0, 10, 19, 18⟩, ⟨0, 9, 19, 20⟩, ⟨0, 19, 18, 2⟩, ⟨0, 19, 17, 4⟩, ⟨0, 19, 16, 6⟩, ⟨0, 19, 15, 8⟩, ⟨0, 19, 14, 10⟩, ⟨0, 19, 13, 12⟩, ⟨0, 19, 12, 14⟩, ⟨0, 19, 11, 16⟩, ⟨0, 19, 10, 18⟩, ⟨0, 19, 9, 20⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_21779 (AllWinning.cons node_21192 (AllWinning.cons node_20407 (AllWinning.cons node_19696 (AllWinning.cons node_18805 (AllWinning.cons node_17884 (AllWinning.cons node_16977 (AllWinning.cons node_15907 (AllWinning.cons node_14923 (AllWinning.cons node_22401 (AllWinning.cons node_21785 (AllWinning.cons node_21195 (AllWinning.cons node_20416 (AllWinning.cons node_19706 (AllWinning.cons node_18827 (AllWinning.cons node_17903 (AllWinning.cons node_17007 (AllWinning.cons node_15937 (AllWinning.cons node_14961 (AllWinning.nil))))))))))))))))))))

theorem node_22950 : Outcome ⟨0, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 4⟩) (by decide) node_21781

theorem node_22951 : Outcome ⟨1, 17, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 20, 2⟩) (by decide) node_22403

theorem node_22952 : Outcome ⟨1, 18, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨1, 17, 19, 2⟩, ⟨1, 16, 19, 4⟩, ⟨1, 18, 18, 2⟩, ⟨1, 18, 17, 4⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_22406 (AllWinning.cons node_21792 (AllWinning.cons node_22407 (AllWinning.cons node_21796 (AllWinning.nil)))))

theorem node_22953 : Outcome ⟨1, 18, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨1, 17, 19, 2⟩, ⟨1, 16, 19, 4⟩, ⟨1, 15, 19, 6⟩, ⟨1, 14, 19, 8⟩, ⟨1, 18, 18, 2⟩, ⟨1, 18, 17, 4⟩, ⟨1, 18, 16, 6⟩, ⟨1, 18, 15, 8⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_22406 (AllWinning.cons node_21792 (AllWinning.cons node_21203 (AllWinning.cons node_20424 (AllWinning.cons node_22407 (AllWinning.cons node_21796 (AllWinning.cons node_21212 (AllWinning.cons node_20436 (AllWinning.nil)))))))))

theorem node_22954 : Outcome ⟨1, 18, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨1, 17, 19, 2⟩, ⟨1, 16, 19, 4⟩, ⟨1, 15, 19, 6⟩, ⟨1, 14, 19, 8⟩, ⟨1, 13, 19, 10⟩, ⟨1, 12, 19, 12⟩, ⟨1, 11, 19, 14⟩, ⟨1, 10, 19, 16⟩, ⟨1, 18, 18, 2⟩, ⟨1, 18, 17, 4⟩, ⟨1, 18, 16, 6⟩, ⟨1, 18, 15, 8⟩, ⟨1, 18, 14, 10⟩, ⟨1, 18, 13, 12⟩, ⟨1, 18, 12, 14⟩, ⟨1, 18, 11, 16⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_22406 (AllWinning.cons node_21792 (AllWinning.cons node_21203 (AllWinning.cons node_20424 (AllWinning.cons node_19716 (AllWinning.cons node_18838 (AllWinning.cons node_17912 (AllWinning.cons node_17018 (AllWinning.cons node_22407 (AllWinning.cons node_21796 (AllWinning.cons node_21212 (AllWinning.cons node_20436 (AllWinning.cons node_19732 (AllWinning.cons node_18862 (AllWinning.cons node_17943 (AllWinning.cons node_17038 (AllWinning.nil)))))))))))))))))

theorem node_22955 : Outcome ⟨1, 18, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨1, 17, 19, 2⟩, ⟨1, 16, 19, 4⟩, ⟨1, 15, 19, 6⟩, ⟨1, 14, 19, 8⟩, ⟨1, 13, 19, 10⟩, ⟨1, 12, 19, 12⟩, ⟨1, 11, 19, 14⟩, ⟨1, 10, 19, 16⟩, ⟨1, 9, 19, 18⟩, ⟨1, 8, 19, 20⟩, ⟨1, 18, 18, 2⟩, ⟨1, 18, 17, 4⟩, ⟨1, 18, 16, 6⟩, ⟨1, 18, 15, 8⟩, ⟨1, 18, 14, 10⟩, ⟨1, 18, 13, 12⟩, ⟨1, 18, 12, 14⟩, ⟨1, 18, 11, 16⟩, ⟨1, 18, 10, 18⟩, ⟨1, 18, 9, 20⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_22406 (AllWinning.cons node_21792 (AllWinning.cons node_21203 (AllWinning.cons node_20424 (AllWinning.cons node_19716 (AllWinning.cons node_18838 (AllWinning.cons node_17912 (AllWinning.cons node_17018 (AllWinning.cons node_15946 (AllWinning.cons node_14968 (AllWinning.cons node_22407 (AllWinning.cons node_21796 (AllWinning.cons node_21212 (AllWinning.cons node_20436 (AllWinning.cons node_19732 (AllWinning.cons node_18862 (AllWinning.cons node_17943 (AllWinning.cons node_17038 (AllWinning.cons node_15976 (AllWinning.cons node_15002 (AllWinning.nil)))))))))))))))))))))

theorem node_22956 : Outcome ⟨1, 18, 19, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 19, 2⟩, ⟨1, 17, 19, 2⟩, ⟨1, 16, 19, 4⟩, ⟨1, 15, 19, 6⟩, ⟨1, 14, 19, 8⟩, ⟨1, 13, 19, 10⟩, ⟨1, 12, 19, 12⟩, ⟨1, 11, 19, 14⟩, ⟨1, 10, 19, 16⟩, ⟨1, 9, 19, 18⟩, ⟨1, 8, 19, 20⟩, ⟨1, 7, 19, 22⟩, ⟨1, 6, 19, 24⟩, ⟨1, 18, 18, 2⟩, ⟨1, 18, 17, 4⟩, ⟨1, 18, 16, 6⟩, ⟨1, 18, 15, 8⟩, ⟨1, 18, 14, 10⟩, ⟨1, 18, 13, 12⟩, ⟨1, 18, 12, 14⟩, ⟨1, 18, 11, 16⟩, ⟨1, 18, 10, 18⟩, ⟨1, 18, 9, 20⟩, ⟨1, 18, 8, 22⟩, ⟨1, 18, 7, 24⟩]
  exact AllWinning.cons node_22400 (AllWinning.cons node_22406 (AllWinning.cons node_21792 (AllWinning.cons node_21203 (AllWinning.cons node_20424 (AllWinning.cons node_19716 (AllWinning.cons node_18838 (AllWinning.cons node_17912 (AllWinning.cons node_17018 (AllWinning.cons node_15946 (AllWinning.cons node_14968 (AllWinning.cons node_14000 (AllWinning.cons node_13034 (AllWinning.cons node_22407 (AllWinning.cons node_21796 (AllWinning.cons node_21212 (AllWinning.cons node_20436 (AllWinning.cons node_19732 (AllWinning.cons node_18862 (AllWinning.cons node_17943 (AllWinning.cons node_17038 (AllWinning.cons node_15976 (AllWinning.cons node_15002 (AllWinning.cons node_14046 (AllWinning.cons node_13072 (AllWinning.nil)))))))))))))))))))))))))

theorem node_22957 : Outcome ⟨1, 19, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 18, 2⟩, ⟨1, 18, 18, 2⟩, ⟨1, 17, 18, 4⟩, ⟨1, 19, 17, 2⟩, ⟨1, 19, 16, 4⟩]
  exact AllWinning.cons node_22401 (AllWinning.cons node_22407 (AllWinning.cons node_21794 (AllWinning.cons node_22410 (AllWinning.cons node_21798 (AllWinning.nil)))))

theorem node_22958 : Outcome ⟨1, 19, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 18, 2⟩, ⟨1, 18, 18, 2⟩, ⟨1, 17, 18, 4⟩, ⟨1, 16, 18, 6⟩, ⟨1, 15, 18, 8⟩, ⟨1, 19, 17, 2⟩, ⟨1, 19, 16, 4⟩, ⟨1, 19, 15, 6⟩, ⟨1, 19, 14, 8⟩]
  exact AllWinning.cons node_22401 (AllWinning.cons node_22407 (AllWinning.cons node_21794 (AllWinning.cons node_21207 (AllWinning.cons node_20427 (AllWinning.cons node_22410 (AllWinning.cons node_21798 (AllWinning.cons node_21214 (AllWinning.cons node_20439 (AllWinning.nil)))))))))

theorem node_22959 : Outcome ⟨1, 19, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 18, 2⟩, ⟨1, 18, 18, 2⟩, ⟨1, 17, 18, 4⟩, ⟨1, 16, 18, 6⟩, ⟨1, 15, 18, 8⟩, ⟨1, 14, 18, 10⟩, ⟨1, 13, 18, 12⟩, ⟨1, 12, 18, 14⟩, ⟨1, 11, 18, 16⟩, ⟨1, 19, 17, 2⟩, ⟨1, 19, 16, 4⟩, ⟨1, 19, 15, 6⟩, ⟨1, 19, 14, 8⟩, ⟨1, 19, 13, 10⟩, ⟨1, 19, 12, 12⟩, ⟨1, 19, 11, 14⟩, ⟨1, 19, 10, 16⟩]
  exact AllWinning.cons node_22401 (AllWinning.cons node_22407 (AllWinning.cons node_21794 (AllWinning.cons node_21207 (AllWinning.cons node_20427 (AllWinning.cons node_19721 (AllWinning.cons node_18841 (AllWinning.cons node_17916 (AllWinning.cons node_17020 (AllWinning.cons node_22410 (AllWinning.cons node_21798 (AllWinning.cons node_21214 (AllWinning.cons node_20439 (AllWinning.cons node_19735 (AllWinning.cons node_18868 (AllWinning.cons node_17946 (AllWinning.cons node_17042 (AllWinning.nil)))))))))))))))))

theorem node_22960 : Outcome ⟨1, 19, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 18, 2⟩, ⟨1, 18, 18, 2⟩, ⟨1, 17, 18, 4⟩, ⟨1, 16, 18, 6⟩, ⟨1, 15, 18, 8⟩, ⟨1, 14, 18, 10⟩, ⟨1, 13, 18, 12⟩, ⟨1, 12, 18, 14⟩, ⟨1, 11, 18, 16⟩, ⟨1, 10, 18, 18⟩, ⟨1, 9, 18, 20⟩, ⟨1, 19, 17, 2⟩, ⟨1, 19, 16, 4⟩, ⟨1, 19, 15, 6⟩, ⟨1, 19, 14, 8⟩, ⟨1, 19, 13, 10⟩, ⟨1, 19, 12, 12⟩, ⟨1, 19, 11, 14⟩, ⟨1, 19, 10, 16⟩, ⟨1, 19, 9, 18⟩, ⟨1, 19, 8, 20⟩]
  exact AllWinning.cons node_22401 (AllWinning.cons node_22407 (AllWinning.cons node_21794 (AllWinning.cons node_21207 (AllWinning.cons node_20427 (AllWinning.cons node_19721 (AllWinning.cons node_18841 (AllWinning.cons node_17916 (AllWinning.cons node_17020 (AllWinning.cons node_15950 (AllWinning.cons node_14971 (AllWinning.cons node_22410 (AllWinning.cons node_21798 (AllWinning.cons node_21214 (AllWinning.cons node_20439 (AllWinning.cons node_19735 (AllWinning.cons node_18868 (AllWinning.cons node_17946 (AllWinning.cons node_17042 (AllWinning.cons node_15980 (AllWinning.cons node_15005 (AllWinning.nil)))))))))))))))))))))

theorem node_22961 : Outcome ⟨1, 19, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 18, 2⟩, ⟨1, 18, 18, 2⟩, ⟨1, 17, 18, 4⟩, ⟨1, 16, 18, 6⟩, ⟨1, 15, 18, 8⟩, ⟨1, 14, 18, 10⟩, ⟨1, 13, 18, 12⟩, ⟨1, 12, 18, 14⟩, ⟨1, 11, 18, 16⟩, ⟨1, 10, 18, 18⟩, ⟨1, 9, 18, 20⟩, ⟨1, 8, 18, 22⟩, ⟨1, 7, 18, 24⟩, ⟨1, 19, 17, 2⟩, ⟨1, 19, 16, 4⟩, ⟨1, 19, 15, 6⟩, ⟨1, 19, 14, 8⟩, ⟨1, 19, 13, 10⟩, ⟨1, 19, 12, 12⟩, ⟨1, 19, 11, 14⟩, ⟨1, 19, 10, 16⟩, ⟨1, 19, 9, 18⟩, ⟨1, 19, 8, 20⟩, ⟨1, 19, 7, 22⟩, ⟨1, 19, 6, 24⟩]
  exact AllWinning.cons node_22401 (AllWinning.cons node_22407 (AllWinning.cons node_21794 (AllWinning.cons node_21207 (AllWinning.cons node_20427 (AllWinning.cons node_19721 (AllWinning.cons node_18841 (AllWinning.cons node_17916 (AllWinning.cons node_17020 (AllWinning.cons node_15950 (AllWinning.cons node_14971 (AllWinning.cons node_14005 (AllWinning.cons node_13036 (AllWinning.cons node_22410 (AllWinning.cons node_21798 (AllWinning.cons node_21214 (AllWinning.cons node_20439 (AllWinning.cons node_19735 (AllWinning.cons node_18868 (AllWinning.cons node_17946 (AllWinning.cons node_17042 (AllWinning.cons node_15980 (AllWinning.cons node_15005 (AllWinning.cons node_14049 (AllWinning.cons node_13075 (AllWinning.nil)))))))))))))))))))))))))

theorem node_22962 : Outcome ⟨1, 20, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 20, 16, 2⟩) (by decide) node_22411

theorem node_22963 : Outcome ⟨2, 16, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 20, 4⟩) (by decide) node_21801

theorem node_22964 : Outcome ⟨2, 16, 20, 10⟩ true :=
  Outcome.win (q := ⟨2, 14, 20, 4⟩) (by decide) node_21801

theorem node_22965 : Outcome ⟨2, 17, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 19, 2⟩, ⟨0, 17, 19, 4⟩, ⟨2, 16, 19, 2⟩, ⟨2, 15, 19, 4⟩, ⟨2, 17, 18, 2⟩, ⟨2, 17, 17, 4⟩]
  exact AllWinning.cons node_22406 (AllWinning.cons node_21779 (AllWinning.cons node_22415 (AllWinning.cons node_21802 (AllWinning.cons node_22416 (AllWinning.cons node_21811 (AllWinning.nil))))))

theorem node_22966 : Outcome ⟨2, 17, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 19, 2⟩, ⟨0, 17, 19, 4⟩, ⟨2, 16, 19, 2⟩, ⟨2, 15, 19, 4⟩, ⟨2, 14, 19, 6⟩, ⟨2, 13, 19, 8⟩, ⟨2, 17, 18, 2⟩, ⟨2, 17, 17, 4⟩, ⟨2, 17, 16, 6⟩, ⟨2, 17, 15, 8⟩]
  exact AllWinning.cons node_22406 (AllWinning.cons node_21779 (AllWinning.cons node_22415 (AllWinning.cons node_21802 (AllWinning.cons node_21222 (AllWinning.cons node_20445 (AllWinning.cons node_22416 (AllWinning.cons node_21811 (AllWinning.cons node_21229 (AllWinning.cons node_20456 (AllWinning.nil))))))))))

theorem node_22967 : Outcome ⟨2, 17, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 17, 19, 2⟩, ⟨0, 17, 19, 4⟩, ⟨2, 16, 19, 2⟩, ⟨2, 15, 19, 4⟩, ⟨2, 14, 19, 6⟩, ⟨2, 13, 19, 8⟩, ⟨2, 12, 19, 10⟩, ⟨2, 11, 19, 12⟩, ⟨2, 17, 18, 2⟩, ⟨2, 17, 17, 4⟩, ⟨2, 17, 16, 6⟩, ⟨2, 17, 15, 8⟩, ⟨2, 17, 14, 10⟩, ⟨2, 17, 13, 12⟩]
  exact AllWinning.cons node_22406 (AllWinning.cons node_21779 (AllWinning.cons node_22415 (AllWinning.cons node_21802 (AllWinning.cons node_21222 (AllWinning.cons node_20445 (AllWinning.cons node_19742 (AllWinning.cons node_18874 (AllWinning.cons node_22416 (AllWinning.cons node_21811 (AllWinning.cons node_21229 (AllWinning.cons node_20456 (AllWinning.cons node_19756 (AllWinning.cons node_18892 (AllWinning.nil))))))))))))))

theorem node_22968 : Outcome ⟨2, 18, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 4⟩) (by decide) node_21781

theorem node_22969 : Outcome ⟨2, 18, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 4⟩) (by decide) node_21781

theorem node_22970 : Outcome ⟨2, 18, 18, 6⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 4⟩) (by decide) node_21781

theorem node_22971 : Outcome ⟨2, 18, 18, 12⟩ true :=
  Outcome.win (q := ⟨0, 18, 18, 4⟩) (by decide) node_21781

theorem node_22972 : Outcome ⟨2, 19, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 17, 2⟩, ⟨0, 19, 17, 4⟩, ⟨2, 18, 17, 2⟩, ⟨2, 17, 17, 4⟩, ⟨2, 19, 16, 2⟩, ⟨2, 19, 15, 4⟩]
  exact AllWinning.cons node_22410 (AllWinning.cons node_21785 (AllWinning.cons node_22418 (AllWinning.cons node_21811 (AllWinning.cons node_22420 (AllWinning.cons node_21821 (AllWinning.nil))))))

theorem node_22973 : Outcome ⟨2, 19, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 17, 2⟩, ⟨0, 19, 17, 4⟩, ⟨2, 18, 17, 2⟩, ⟨2, 17, 17, 4⟩, ⟨2, 16, 17, 6⟩, ⟨2, 15, 17, 8⟩, ⟨2, 19, 16, 2⟩, ⟨2, 19, 15, 4⟩, ⟨2, 19, 14, 6⟩, ⟨2, 19, 13, 8⟩]
  exact AllWinning.cons node_22410 (AllWinning.cons node_21785 (AllWinning.cons node_22418 (AllWinning.cons node_21811 (AllWinning.cons node_21225 (AllWinning.cons node_20450 (AllWinning.cons node_22420 (AllWinning.cons node_21821 (AllWinning.cons node_21235 (AllWinning.cons node_20459 (AllWinning.nil))))))))))

theorem node_22974 : Outcome ⟨2, 19, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 19, 17, 2⟩, ⟨0, 19, 17, 4⟩, ⟨2, 18, 17, 2⟩, ⟨2, 17, 17, 4⟩, ⟨2, 16, 17, 6⟩, ⟨2, 15, 17, 8⟩, ⟨2, 14, 17, 10⟩, ⟨2, 13, 17, 12⟩, ⟨2, 19, 16, 2⟩, ⟨2, 19, 15, 4⟩, ⟨2, 19, 14, 6⟩, ⟨2, 19, 13, 8⟩, ⟨2, 19, 12, 10⟩, ⟨2, 19, 11, 12⟩]
  exact AllWinning.cons node_22410 (AllWinning.cons node_21785 (AllWinning.cons node_22418 (AllWinning.cons node_21811 (AllWinning.cons node_21225 (AllWinning.cons node_20450 (AllWinning.cons node_19749 (AllWinning.cons node_18878 (AllWinning.cons node_22420 (AllWinning.cons node_21821 (AllWinning.cons node_21235 (AllWinning.cons node_20459 (AllWinning.cons node_19761 (AllWinning.cons node_18897 (AllWinning.nil))))))))))))))

theorem node_22975 : Outcome ⟨2, 20, 16, 4⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 4⟩) (by decide) node_21815

theorem node_22976 : Outcome ⟨2, 20, 16, 10⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 4⟩) (by decide) node_21815

theorem node_22977 : Outcome ⟨3, 15, 20, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 20, 6⟩) (by decide) node_21240

theorem node_22978 : Outcome ⟨3, 15, 20, 6⟩ true :=
  Outcome.win (q := ⟨3, 12, 20, 6⟩) (by decide) node_21240

theorem node_22979 : Outcome ⟨3, 15, 20, 20⟩ true :=
  Outcome.win (q := ⟨3, 12, 20, 6⟩) (by decide) node_21240

theorem node_22980 : Outcome ⟨3, 17, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 4⟩) (by decide) node_21827

theorem node_22981 : Outcome ⟨3, 17, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 17, 14, 8⟩) (by decide) node_20479

theorem node_22982 : Outcome ⟨3, 18, 17, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 4⟩) (by decide) node_21840

theorem node_22983 : Outcome ⟨3, 18, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 14, 17, 8⟩) (by decide) node_20472

theorem node_22984 : Outcome ⟨3, 20, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 20, 12, 6⟩) (by decide) node_21254

theorem node_22985 : Outcome ⟨3, 20, 15, 6⟩ true :=
  Outcome.win (q := ⟨3, 20, 12, 6⟩) (by decide) node_21254

theorem node_22986 : Outcome ⟨4, 14, 20, 2⟩ true :=
  Outcome.win (q := ⟨2, 14, 20, 4⟩) (by decide) node_21801

theorem node_22987 : Outcome ⟨4, 14, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 14, 20, 4⟩) (by decide) node_21801

theorem node_22988 : Outcome ⟨4, 15, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 17, 4⟩) (by decide) node_21858

theorem node_22989 : Outcome ⟨4, 16, 18, 2⟩ true :=
  Outcome.win (q := ⟨2, 16, 18, 4⟩) (by decide) node_21805

theorem node_22990 : Outcome ⟨4, 16, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 16, 18, 4⟩) (by decide) node_21805

theorem node_22991 : Outcome ⟨4, 17, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 17, 4⟩) (by decide) node_21858

theorem node_22992 : Outcome ⟨4, 17, 17, 8⟩ true :=
  Outcome.win (q := ⟨0, 17, 17, 8⟩) (by decide) node_20412

theorem node_22993 : Outcome ⟨4, 18, 16, 2⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 4⟩) (by decide) node_21815

theorem node_22994 : Outcome ⟨4, 18, 16, 4⟩ true :=
  Outcome.win (q := ⟨2, 18, 16, 4⟩) (by decide) node_21815

theorem node_22995 : Outcome ⟨4, 19, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 15, 4⟩) (by decide) node_21863

theorem node_22996 : Outcome ⟨4, 20, 14, 2⟩ true :=
  Outcome.win (q := ⟨2, 20, 14, 4⟩) (by decide) node_21823

theorem node_22997 : Outcome ⟨4, 20, 14, 4⟩ true :=
  Outcome.win (q := ⟨2, 20, 14, 4⟩) (by decide) node_21823

theorem node_22998 : Outcome ⟨5, 13, 20, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 20, 2⟩) (by decide) node_22433

theorem node_22999 : Outcome ⟨5, 14, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 14, 19, 2⟩) (by decide) node_22436

theorem node_23000 : Outcome ⟨5, 14, 19, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 8⟩) (by decide) node_20519

theorem node_23001 : Outcome ⟨5, 14, 19, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 19, 8⟩) (by decide) node_20519

theorem node_23002 : Outcome ⟨5, 15, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 15, 18, 4⟩) (by decide) node_21827

theorem node_23003 : Outcome ⟨5, 15, 18, 6⟩ true :=
  Outcome.win (q := ⟨5, 12, 18, 6⟩) (by decide) node_21281

theorem node_23004 : Outcome ⟨5, 15, 18, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 18, 6⟩) (by decide) node_21281

theorem node_23005 : Outcome ⟨5, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 16, 2⟩) (by decide) node_22466

theorem node_23006 : Outcome ⟨5, 16, 17, 8⟩ true :=
  Outcome.win (q := ⟨5, 16, 16, 2⟩) (by decide) node_22466

theorem node_23007 : Outcome ⟨5, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 16, 2⟩) (by decide) node_22466

theorem node_23008 : Outcome ⟨5, 17, 16, 8⟩ true :=
  Outcome.win (q := ⟨5, 16, 16, 2⟩) (by decide) node_22466

theorem node_23009 : Outcome ⟨5, 18, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 15, 4⟩) (by decide) node_21840

theorem node_23010 : Outcome ⟨5, 18, 15, 6⟩ true :=
  Outcome.win (q := ⟨5, 18, 12, 6⟩) (by decide) node_21301

theorem node_23011 : Outcome ⟨5, 18, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 18, 12, 6⟩) (by decide) node_21301

theorem node_23012 : Outcome ⟨5, 19, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 19, 14, 2⟩) (by decide) node_22448

theorem node_23013 : Outcome ⟨5, 19, 14, 4⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 8⟩) (by decide) node_20541

theorem node_23014 : Outcome ⟨5, 19, 14, 8⟩ true :=
  Outcome.win (q := ⟨5, 19, 10, 8⟩) (by decide) node_20541

theorem node_23015 : Outcome ⟨5, 20, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 20, 13, 2⟩) (by decide) node_22453

theorem node_23016 : Outcome ⟨6, 12, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 12, 20, 2⟩, ⟨4, 12, 20, 4⟩, ⟨6, 11, 20, 2⟩, ⟨6, 10, 20, 4⟩, ⟨6, 12, 19, 2⟩, ⟨6, 12, 18, 4⟩]
  exact AllWinning.cons node_22456 (AllWinning.cons node_21851 (AllWinning.cons node_22480 (AllWinning.cons node_21898 (AllWinning.cons node_22483 (AllWinning.cons node_21902 (AllWinning.nil))))))

theorem node_23017 : Outcome ⟨6, 12, 20, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 8⟩) (by decide) node_20559

theorem node_23018 : Outcome ⟨6, 12, 20, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 12⟩) (by decide) node_19001

theorem node_23019 : Outcome ⟨6, 13, 19, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 19, 2⟩) (by decide) node_22459

theorem node_23020 : Outcome ⟨6, 14, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 18, 2⟩, ⟨4, 14, 18, 4⟩, ⟨6, 13, 18, 2⟩, ⟨6, 12, 18, 4⟩, ⟨6, 14, 17, 2⟩, ⟨6, 14, 16, 4⟩]
  exact AllWinning.cons node_22462 (AllWinning.cons node_21856 (AllWinning.cons node_22485 (AllWinning.cons node_21902 (AllWinning.cons node_22486 (AllWinning.cons node_21909 (AllWinning.nil))))))

theorem node_23021 : Outcome ⟨6, 14, 18, 4⟩ true :=
  Outcome.win (q := ⟨6, 10, 18, 8⟩) (by decide) node_20552

theorem node_23022 : Outcome ⟨6, 14, 18, 12⟩ true :=
  Outcome.win (q := ⟨6, 14, 13, 10⟩) (by decide) node_19874

theorem node_23023 : Outcome ⟨6, 15, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 17, 4⟩) (by decide) node_21858

theorem node_23024 : Outcome ⟨6, 15, 17, 6⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 12⟩) (by decide) node_19013

theorem node_23025 : Outcome ⟨6, 16, 16, 2⟩ true :=
  Outcome.win (q := ⟨5, 16, 16, 2⟩) (by decide) node_22466

theorem node_23026 : Outcome ⟨6, 16, 16, 4⟩ true :=
  Outcome.win (q := ⟨6, 12, 16, 8⟩) (by decide) node_20559

theorem node_23027 : Outcome ⟨6, 16, 16, 14⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 12⟩) (by decide) node_18817

theorem node_23028 : Outcome ⟨6, 17, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 17, 15, 4⟩) (by decide) node_21863

theorem node_23029 : Outcome ⟨6, 17, 15, 6⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 12⟩) (by decide) node_19020

theorem node_23030 : Outcome ⟨6, 18, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 18, 14, 2⟩, ⟨4, 18, 14, 4⟩, ⟨6, 17, 14, 2⟩, ⟨6, 16, 14, 4⟩, ⟨6, 18, 13, 2⟩, ⟨6, 18, 12, 4⟩]
  exact AllWinning.cons node_22471 (AllWinning.cons node_21866 (AllWinning.cons node_22495 (AllWinning.cons node_21915 (AllWinning.cons node_22498 (AllWinning.cons node_21921 (AllWinning.nil))))))

theorem node_23031 : Outcome ⟨6, 18, 14, 4⟩ true :=
  Outcome.win (q := ⟨6, 18, 10, 8⟩) (by decide) node_20584

theorem node_23032 : Outcome ⟨6, 18, 14, 12⟩ true :=
  Outcome.win (q := ⟨6, 13, 14, 10⟩) (by decide) node_19867

theorem node_23033 : Outcome ⟨6, 19, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 19, 13, 2⟩) (by decide) node_22474

theorem node_23034 : Outcome ⟨6, 20, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 20, 12, 2⟩, ⟨4, 20, 12, 4⟩, ⟨6, 19, 12, 2⟩, ⟨6, 18, 12, 4⟩, ⟨6, 20, 11, 2⟩, ⟨6, 20, 10, 4⟩]
  exact AllWinning.cons node_22477 (AllWinning.cons node_21870 (AllWinning.cons node_22499 (AllWinning.cons node_21921 (AllWinning.cons node_22501 (AllWinning.cons node_21926 (AllWinning.nil))))))

theorem node_23035 : Outcome ⟨6, 20, 12, 4⟩ true :=
  Outcome.win (q := ⟨6, 16, 12, 8⟩) (by decide) node_20575

theorem node_23036 : Outcome ⟨6, 20, 12, 6⟩ true :=
  Outcome.win (q := ⟨6, 20, 6, 12⟩) (by decide) node_19051

theorem node_23037 : Outcome ⟨7, 11, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 11, 20, 2⟩, ⟨5, 11, 20, 4⟩, ⟨7, 10, 20, 2⟩, ⟨7, 9, 20, 4⟩, ⟨7, 11, 19, 2⟩, ⟨7, 11, 18, 4⟩]
  exact AllWinning.cons node_22480 (AllWinning.cons node_21872 (AllWinning.cons node_22504 (AllWinning.cons node_21928 (AllWinning.cons node_22506 (AllWinning.cons node_21932 (AllWinning.nil))))))

theorem node_23038 : Outcome ⟨7, 11, 20, 8⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 8⟩) (by decide) node_20602

theorem node_23039 : Outcome ⟨7, 11, 20, 10⟩ true :=
  Outcome.win (q := ⟨7, 11, 16, 8⟩) (by decide) node_20602

theorem node_23040 : Outcome ⟨7, 12, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 12, 19, 2⟩, ⟨5, 12, 19, 4⟩, ⟨7, 11, 19, 2⟩, ⟨7, 10, 19, 4⟩, ⟨7, 12, 18, 2⟩, ⟨7, 12, 17, 4⟩]
  exact AllWinning.cons node_22483 (AllWinning.cons node_21875 (AllWinning.cons node_22506 (AllWinning.cons node_21930 (AllWinning.cons node_22508 (AllWinning.cons node_21933 (AllWinning.nil))))))

theorem node_23041 : Outcome ⟨7, 12, 19, 4⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 8⟩) (by decide) node_20610

theorem node_23042 : Outcome ⟨7, 12, 19, 10⟩ true :=
  Outcome.win (q := ⟨7, 12, 15, 8⟩) (by decide) node_20610

theorem node_23043 : Outcome ⟨7, 13, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 13, 18, 2⟩, ⟨5, 13, 18, 4⟩, ⟨7, 12, 18, 2⟩, ⟨7, 11, 18, 4⟩, ⟨7, 13, 17, 2⟩, ⟨7, 13, 16, 4⟩]
  exact AllWinning.cons node_22485 (AllWinning.cons node_21879 (AllWinning.cons node_22508 (AllWinning.cons node_21932 (AllWinning.cons node_22511 (AllWinning.cons node_21936 (AllWinning.nil))))))

end RQ9F1
