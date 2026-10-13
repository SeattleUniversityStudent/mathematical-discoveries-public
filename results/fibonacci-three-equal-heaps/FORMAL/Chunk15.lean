import Chunk14
set_option autoImplicit false
namespace RQ9F1

theorem node_3834 : Outcome ⟨9, 5, 1, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 5, 1, 2⟩, ⟨7, 5, 1, 4⟩, ⟨6, 5, 1, 6⟩, ⟨5, 5, 1, 8⟩, ⟨4, 5, 1, 10⟩, ⟨3, 5, 1, 12⟩, ⟨2, 5, 1, 14⟩, ⟨1, 5, 1, 16⟩, ⟨0, 5, 1, 18⟩, ⟨9, 4, 1, 2⟩, ⟨9, 3, 1, 4⟩, ⟨9, 2, 1, 6⟩, ⟨9, 1, 1, 8⟩, ⟨9, 0, 1, 10⟩, ⟨9, 5, 0, 2⟩]
  exact AllWinning.cons node_3233 (AllWinning.cons node_2714 (AllWinning.cons node_2223 (AllWinning.cons node_1773 (AllWinning.cons node_1398 (AllWinning.cons node_1052 (AllWinning.cons node_789 (AllWinning.cons node_546 (AllWinning.cons node_360 (AllWinning.cons node_3254 (AllWinning.cons node_2766 (AllWinning.cons node_2326 (AllWinning.cons node_1844 (AllWinning.cons node_1529 (AllWinning.cons node_3257 (AllWinning.nil)))))))))))))))

theorem node_3835 : Outcome ⟨9, 6, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 6, 0, 2⟩, ⟨7, 6, 0, 4⟩, ⟨9, 5, 0, 2⟩, ⟨9, 4, 0, 4⟩]
  exact AllWinning.cons node_3237 (AllWinning.cons node_2718 (AllWinning.cons node_3257 (AllWinning.cons node_2770 (AllWinning.nil))))

theorem node_3836 : Outcome ⟨9, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 6⟩) (by decide) node_2227

theorem node_3837 : Outcome ⟨9, 6, 0, 6⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 6⟩) (by decide) node_2227

theorem node_3838 : Outcome ⟨9, 6, 0, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 6⟩) (by decide) node_2227

theorem node_3839 : Outcome ⟨9, 6, 0, 34⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 6⟩) (by decide) node_2227

theorem node_3840 : Outcome ⟨10, 0, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 6⟩) (by decide) node_2336

theorem node_3841 : Outcome ⟨10, 0, 5, 6⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 10⟩) (by decide) node_1408

theorem node_3842 : Outcome ⟨10, 0, 5, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 10⟩) (by decide) node_1408

theorem node_3843 : Outcome ⟨10, 0, 5, 16⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 10⟩) (by decide) node_1408

theorem node_3844 : Outcome ⟨10, 1, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 4, 2⟩, ⟨8, 1, 4, 4⟩, ⟨10, 0, 4, 2⟩, ⟨10, 1, 3, 2⟩, ⟨10, 1, 2, 4⟩]
  exact AllWinning.cons node_3243 (AllWinning.cons node_2726 (AllWinning.cons node_3260 (AllWinning.cons node_3264 (AllWinning.cons node_2779 (AllWinning.nil)))))

theorem node_3845 : Outcome ⟨10, 1, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 4, 2⟩, ⟨8, 1, 4, 4⟩, ⟨7, 1, 4, 6⟩, ⟨6, 1, 4, 8⟩, ⟨10, 0, 4, 2⟩, ⟨10, 1, 3, 2⟩, ⟨10, 1, 2, 4⟩, ⟨10, 1, 1, 6⟩, ⟨10, 1, 0, 8⟩]
  exact AllWinning.cons node_3243 (AllWinning.cons node_2726 (AllWinning.cons node_2245 (AllWinning.cons node_1782 (AllWinning.cons node_3260 (AllWinning.cons node_3264 (AllWinning.cons node_2779 (AllWinning.cons node_2340 (AllWinning.cons node_1857 (AllWinning.nil)))))))))

theorem node_3846 : Outcome ⟨10, 1, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 1, 4, 2⟩, ⟨8, 1, 4, 4⟩, ⟨7, 1, 4, 6⟩, ⟨6, 1, 4, 8⟩, ⟨5, 1, 4, 10⟩, ⟨4, 1, 4, 12⟩, ⟨10, 0, 4, 2⟩, ⟨10, 1, 3, 2⟩, ⟨10, 1, 2, 4⟩, ⟨10, 1, 1, 6⟩, ⟨10, 1, 0, 8⟩]
  exact AllWinning.cons node_3243 (AllWinning.cons node_2726 (AllWinning.cons node_2245 (AllWinning.cons node_1782 (AllWinning.cons node_1421 (AllWinning.cons node_1066 (AllWinning.cons node_3260 (AllWinning.cons node_3264 (AllWinning.cons node_2779 (AllWinning.cons node_2340 (AllWinning.cons node_1857 (AllWinning.nil)))))))))))

theorem node_3847 : Outcome ⟨10, 1, 4, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3848 : Outcome ⟨10, 1, 4, 20⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 16⟩) (by decide) node_563

theorem node_3849 : Outcome ⟨10, 2, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 6⟩) (by decide) node_2251

theorem node_3850 : Outcome ⟨10, 2, 3, 22⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 6⟩) (by decide) node_2251

theorem node_3851 : Outcome ⟨10, 3, 2, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 6⟩) (by decide) node_2267

theorem node_3852 : Outcome ⟨10, 3, 2, 10⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 6⟩) (by decide) node_2267

theorem node_3853 : Outcome ⟨10, 3, 2, 22⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 6⟩) (by decide) node_2267

theorem node_3854 : Outcome ⟨10, 4, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 4, 1, 2⟩, ⟨8, 4, 1, 4⟩, ⟨10, 3, 1, 2⟩, ⟨10, 2, 1, 4⟩, ⟨10, 4, 0, 2⟩]
  exact AllWinning.cons node_3254 (AllWinning.cons node_2741 (AllWinning.cons node_3270 (AllWinning.cons node_2783 (AllWinning.cons node_3275 (AllWinning.nil)))))

theorem node_3855 : Outcome ⟨10, 4, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 4, 1, 2⟩, ⟨8, 4, 1, 4⟩, ⟨7, 4, 1, 6⟩, ⟨6, 4, 1, 8⟩, ⟨10, 3, 1, 2⟩, ⟨10, 2, 1, 4⟩, ⟨10, 1, 1, 6⟩, ⟨10, 0, 1, 8⟩, ⟨10, 4, 0, 2⟩]
  exact AllWinning.cons node_3254 (AllWinning.cons node_2741 (AllWinning.cons node_2283 (AllWinning.cons node_1792 (AllWinning.cons node_3270 (AllWinning.cons node_2783 (AllWinning.cons node_2340 (AllWinning.cons node_1852 (AllWinning.cons node_3275 (AllWinning.nil)))))))))

theorem node_3856 : Outcome ⟨10, 4, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 4, 1, 2⟩, ⟨8, 4, 1, 4⟩, ⟨7, 4, 1, 6⟩, ⟨6, 4, 1, 8⟩, ⟨5, 4, 1, 10⟩, ⟨4, 4, 1, 12⟩, ⟨10, 3, 1, 2⟩, ⟨10, 2, 1, 4⟩, ⟨10, 1, 1, 6⟩, ⟨10, 0, 1, 8⟩, ⟨10, 4, 0, 2⟩]
  exact AllWinning.cons node_3254 (AllWinning.cons node_2741 (AllWinning.cons node_2283 (AllWinning.cons node_1792 (AllWinning.cons node_1435 (AllWinning.cons node_1080 (AllWinning.cons node_3270 (AllWinning.cons node_2783 (AllWinning.cons node_2340 (AllWinning.cons node_1852 (AllWinning.cons node_3275 (AllWinning.nil)))))))))))

theorem node_3857 : Outcome ⟨10, 4, 1, 10⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3858 : Outcome ⟨10, 4, 1, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 16⟩) (by decide) node_585

theorem node_3859 : Outcome ⟨10, 5, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 6⟩) (by decide) node_2344

theorem node_3860 : Outcome ⟨10, 5, 0, 6⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 10⟩) (by decide) node_1442

theorem node_3861 : Outcome ⟨10, 5, 0, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 10⟩) (by decide) node_1442

theorem node_3862 : Outcome ⟨10, 5, 0, 16⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 10⟩) (by decide) node_1442

theorem node_3863 : Outcome ⟨11, 0, 4, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 3, 2⟩) (by decide) node_3279

theorem node_3864 : Outcome ⟨11, 0, 4, 4⟩ true :=
  Outcome.win (q := ⟨11, 0, 3, 2⟩) (by decide) node_3279

theorem node_3865 : Outcome ⟨11, 0, 4, 12⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 14⟩) (by decide) node_826

theorem node_3866 : Outcome ⟨11, 0, 4, 14⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 14⟩) (by decide) node_826

theorem node_3867 : Outcome ⟨11, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨11, 0, 3, 2⟩) (by decide) node_3279

theorem node_3868 : Outcome ⟨11, 1, 3, 8⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 10⟩) (by decide) node_1459

theorem node_3869 : Outcome ⟨11, 1, 3, 16⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 10⟩) (by decide) node_1459

theorem node_3870 : Outcome ⟨11, 2, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 2, 2, 2⟩, ⟨9, 2, 2, 4⟩, ⟨11, 1, 2, 2⟩, ⟨11, 0, 2, 4⟩, ⟨11, 2, 1, 2⟩, ⟨11, 2, 0, 4⟩]
  exact AllWinning.cons node_3268 (AllWinning.cons node_2762 (AllWinning.cons node_3284 (AllWinning.cons node_2792 (AllWinning.cons node_3287 (AllWinning.cons node_2800 (AllWinning.nil))))))

theorem node_3871 : Outcome ⟨11, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨8, 2, 2, 6⟩) (by decide) node_2303

theorem node_3872 : Outcome ⟨11, 2, 2, 8⟩ true :=
  Outcome.win (q := ⟨8, 2, 2, 6⟩) (by decide) node_2303

theorem node_3873 : Outcome ⟨11, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 0, 2⟩) (by decide) node_3290

theorem node_3874 : Outcome ⟨11, 3, 1, 8⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 10⟩) (by decide) node_1479

theorem node_3875 : Outcome ⟨11, 3, 1, 16⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 10⟩) (by decide) node_1479

theorem node_3876 : Outcome ⟨11, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 0, 2⟩) (by decide) node_3290

theorem node_3877 : Outcome ⟨11, 4, 0, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 0, 2⟩) (by decide) node_3290

theorem node_3878 : Outcome ⟨11, 4, 0, 12⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 14⟩) (by decide) node_852

theorem node_3879 : Outcome ⟨11, 4, 0, 14⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 14⟩) (by decide) node_852

theorem node_3880 : Outcome ⟨12, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 3, 2⟩) (by decide) node_3279

theorem node_3881 : Outcome ⟨12, 0, 3, 8⟩ true :=
  Outcome.win (q := ⟨11, 0, 3, 2⟩) (by decide) node_3279

theorem node_3882 : Outcome ⟨12, 0, 3, 18⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 18⟩) (by decide) node_411

theorem node_3883 : Outcome ⟨12, 1, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 2, 2⟩, ⟨10, 1, 2, 4⟩, ⟨12, 0, 2, 2⟩, ⟨12, 1, 1, 2⟩, ⟨12, 1, 0, 4⟩]
  exact AllWinning.cons node_3284 (AllWinning.cons node_2779 (AllWinning.cons node_3295 (AllWinning.cons node_3301 (AllWinning.cons node_2810 (AllWinning.nil)))))

theorem node_3884 : Outcome ⟨12, 1, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 2, 2⟩, ⟨10, 1, 2, 4⟩, ⟨9, 1, 2, 6⟩, ⟨8, 1, 2, 8⟩, ⟨12, 0, 2, 2⟩, ⟨12, 1, 1, 2⟩, ⟨12, 1, 0, 4⟩]
  exact AllWinning.cons node_3284 (AllWinning.cons node_2779 (AllWinning.cons node_2322 (AllWinning.cons node_1823 (AllWinning.cons node_3295 (AllWinning.cons node_3301 (AllWinning.cons node_2810 (AllWinning.nil)))))))

theorem node_3885 : Outcome ⟨12, 1, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 2, 2⟩, ⟨10, 1, 2, 4⟩, ⟨9, 1, 2, 6⟩, ⟨8, 1, 2, 8⟩, ⟨7, 1, 2, 10⟩, ⟨6, 1, 2, 12⟩, ⟨12, 0, 2, 2⟩, ⟨12, 1, 1, 2⟩, ⟨12, 1, 0, 4⟩]
  exact AllWinning.cons node_3284 (AllWinning.cons node_2779 (AllWinning.cons node_2322 (AllWinning.cons node_1823 (AllWinning.cons node_1500 (AllWinning.cons node_1110 (AllWinning.cons node_3295 (AllWinning.cons node_3301 (AllWinning.cons node_2810 (AllWinning.nil)))))))))

theorem node_3886 : Outcome ⟨12, 1, 2, 10⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3887 : Outcome ⟨12, 1, 2, 12⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3888 : Outcome ⟨12, 1, 2, 26⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 16⟩) (by decide) node_623

theorem node_3889 : Outcome ⟨12, 2, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 2, 1, 2⟩, ⟨10, 2, 1, 4⟩, ⟨12, 1, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨12, 2, 0, 2⟩]
  exact AllWinning.cons node_3287 (AllWinning.cons node_2783 (AllWinning.cons node_3301 (AllWinning.cons node_2805 (AllWinning.cons node_3303 (AllWinning.nil)))))

theorem node_3890 : Outcome ⟨12, 2, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 2, 1, 2⟩, ⟨10, 2, 1, 4⟩, ⟨9, 2, 1, 6⟩, ⟨8, 2, 1, 8⟩, ⟨12, 1, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨12, 2, 0, 2⟩]
  exact AllWinning.cons node_3287 (AllWinning.cons node_2783 (AllWinning.cons node_2326 (AllWinning.cons node_1828 (AllWinning.cons node_3301 (AllWinning.cons node_2805 (AllWinning.cons node_3303 (AllWinning.nil)))))))

theorem node_3891 : Outcome ⟨12, 2, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 2, 1, 2⟩, ⟨10, 2, 1, 4⟩, ⟨9, 2, 1, 6⟩, ⟨8, 2, 1, 8⟩, ⟨7, 2, 1, 10⟩, ⟨6, 2, 1, 12⟩, ⟨12, 1, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨12, 2, 0, 2⟩]
  exact AllWinning.cons node_3287 (AllWinning.cons node_2783 (AllWinning.cons node_2326 (AllWinning.cons node_1828 (AllWinning.cons node_1504 (AllWinning.cons node_1115 (AllWinning.cons node_3301 (AllWinning.cons node_2805 (AllWinning.cons node_3303 (AllWinning.nil)))))))))

theorem node_3892 : Outcome ⟨12, 2, 1, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3893 : Outcome ⟨12, 2, 1, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3894 : Outcome ⟨12, 2, 1, 26⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 16⟩) (by decide) node_641

theorem node_3895 : Outcome ⟨12, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 0, 2⟩) (by decide) node_3290

theorem node_3896 : Outcome ⟨12, 3, 0, 8⟩ true :=
  Outcome.win (q := ⟨11, 3, 0, 2⟩) (by decide) node_3290

theorem node_3897 : Outcome ⟨12, 3, 0, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 18⟩) (by decide) node_434

theorem node_3898 : Outcome ⟨13, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 6⟩) (by decide) node_2336

theorem node_3899 : Outcome ⟨13, 0, 2, 6⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 6⟩) (by decide) node_2336

theorem node_3900 : Outcome ⟨13, 0, 2, 22⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 22⟩) (by decide) node_193

theorem node_3901 : Outcome ⟨13, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 1, 2⟩, ⟨11, 1, 1, 4⟩, ⟨13, 0, 1, 2⟩, ⟨13, 1, 0, 2⟩]
  exact AllWinning.cons node_3301 (AllWinning.cons node_2797 (AllWinning.cons node_3309 (AllWinning.cons node_3312 (AllWinning.nil))))

theorem node_3902 : Outcome ⟨13, 1, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 1, 2⟩, ⟨11, 1, 1, 4⟩, ⟨10, 1, 1, 6⟩, ⟨9, 1, 1, 8⟩, ⟨13, 0, 1, 2⟩, ⟨13, 1, 0, 2⟩]
  exact AllWinning.cons node_3301 (AllWinning.cons node_2797 (AllWinning.cons node_2340 (AllWinning.cons node_1844 (AllWinning.cons node_3309 (AllWinning.cons node_3312 (AllWinning.nil))))))

theorem node_3903 : Outcome ⟨13, 1, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 1, 2⟩, ⟨11, 1, 1, 4⟩, ⟨10, 1, 1, 6⟩, ⟨9, 1, 1, 8⟩, ⟨8, 1, 1, 10⟩, ⟨7, 1, 1, 12⟩, ⟨13, 0, 1, 2⟩, ⟨13, 1, 0, 2⟩]
  exact AllWinning.cons node_3301 (AllWinning.cons node_2797 (AllWinning.cons node_2340 (AllWinning.cons node_1844 (AllWinning.cons node_1519 (AllWinning.cons node_1130 (AllWinning.cons node_3309 (AllWinning.cons node_3312 (AllWinning.nil))))))))

theorem node_3904 : Outcome ⟨13, 1, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 1, 2⟩, ⟨11, 1, 1, 4⟩, ⟨10, 1, 1, 6⟩, ⟨9, 1, 1, 8⟩, ⟨8, 1, 1, 10⟩, ⟨7, 1, 1, 12⟩, ⟨6, 1, 1, 14⟩, ⟨5, 1, 1, 16⟩, ⟨4, 1, 1, 18⟩, ⟨3, 1, 1, 20⟩, ⟨13, 0, 1, 2⟩, ⟨13, 1, 0, 2⟩]
  exact AllWinning.cons node_3301 (AllWinning.cons node_2797 (AllWinning.cons node_2340 (AllWinning.cons node_1844 (AllWinning.cons node_1519 (AllWinning.cons node_1130 (AllWinning.cons node_885 (AllWinning.cons node_661 (AllWinning.cons node_450 (AllWinning.cons node_303 (AllWinning.cons node_3309 (AllWinning.cons node_3312 (AllWinning.nil))))))))))))

theorem node_3905 : Outcome ⟨13, 1, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 1, 2⟩, ⟨11, 1, 1, 4⟩, ⟨10, 1, 1, 6⟩, ⟨9, 1, 1, 8⟩, ⟨8, 1, 1, 10⟩, ⟨7, 1, 1, 12⟩, ⟨6, 1, 1, 14⟩, ⟨5, 1, 1, 16⟩, ⟨4, 1, 1, 18⟩, ⟨3, 1, 1, 20⟩, ⟨2, 1, 1, 22⟩, ⟨1, 1, 1, 24⟩, ⟨13, 0, 1, 2⟩, ⟨13, 1, 0, 2⟩]
  exact AllWinning.cons node_3301 (AllWinning.cons node_2797 (AllWinning.cons node_2340 (AllWinning.cons node_1844 (AllWinning.cons node_1519 (AllWinning.cons node_1130 (AllWinning.cons node_885 (AllWinning.cons node_661 (AllWinning.cons node_450 (AllWinning.cons node_303 (AllWinning.cons node_203 (AllWinning.cons node_116 (AllWinning.cons node_3309 (AllWinning.cons node_3312 (AllWinning.nil))))))))))))))

theorem node_3906 : Outcome ⟨13, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 6⟩) (by decide) node_2344

theorem node_3907 : Outcome ⟨13, 2, 0, 6⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 6⟩) (by decide) node_2344

theorem node_3908 : Outcome ⟨13, 2, 0, 22⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 22⟩) (by decide) node_214

theorem node_3909 : Outcome ⟨14, 0, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3309 (AllWinning.cons node_2805 (AllWinning.cons node_3315 (AllWinning.nil)))

theorem node_3910 : Outcome ⟨14, 0, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨11, 0, 1, 6⟩, ⟨10, 0, 1, 8⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3309 (AllWinning.cons node_2805 (AllWinning.cons node_2349 (AllWinning.cons node_1852 (AllWinning.cons node_3315 (AllWinning.nil)))))

theorem node_3911 : Outcome ⟨14, 0, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨11, 0, 1, 6⟩, ⟨10, 0, 1, 8⟩, ⟨9, 0, 1, 10⟩, ⟨8, 0, 1, 12⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3309 (AllWinning.cons node_2805 (AllWinning.cons node_2349 (AllWinning.cons node_1852 (AllWinning.cons node_1529 (AllWinning.cons node_1139 (AllWinning.cons node_3315 (AllWinning.nil)))))))

theorem node_3912 : Outcome ⟨14, 0, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨11, 0, 1, 6⟩, ⟨10, 0, 1, 8⟩, ⟨9, 0, 1, 10⟩, ⟨8, 0, 1, 12⟩, ⟨7, 0, 1, 14⟩, ⟨6, 0, 1, 16⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3309 (AllWinning.cons node_2805 (AllWinning.cons node_2349 (AllWinning.cons node_1852 (AllWinning.cons node_1529 (AllWinning.cons node_1139 (AllWinning.cons node_894 (AllWinning.cons node_670 (AllWinning.cons node_3315 (AllWinning.nil)))))))))

theorem node_3913 : Outcome ⟨14, 0, 1, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨11, 0, 1, 6⟩, ⟨10, 0, 1, 8⟩, ⟨9, 0, 1, 10⟩, ⟨8, 0, 1, 12⟩, ⟨7, 0, 1, 14⟩, ⟨6, 0, 1, 16⟩, ⟨5, 0, 1, 18⟩, ⟨4, 0, 1, 20⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3309 (AllWinning.cons node_2805 (AllWinning.cons node_2349 (AllWinning.cons node_1852 (AllWinning.cons node_1529 (AllWinning.cons node_1139 (AllWinning.cons node_894 (AllWinning.cons node_670 (AllWinning.cons node_458 (AllWinning.cons node_313 (AllWinning.cons node_3315 (AllWinning.nil)))))))))))

theorem node_3914 : Outcome ⟨14, 0, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 0, 1, 2⟩, ⟨12, 0, 1, 4⟩, ⟨11, 0, 1, 6⟩, ⟨10, 0, 1, 8⟩, ⟨9, 0, 1, 10⟩, ⟨8, 0, 1, 12⟩, ⟨7, 0, 1, 14⟩, ⟨6, 0, 1, 16⟩, ⟨5, 0, 1, 18⟩, ⟨4, 0, 1, 20⟩, ⟨3, 0, 1, 22⟩, ⟨2, 0, 1, 24⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3309 (AllWinning.cons node_2805 (AllWinning.cons node_2349 (AllWinning.cons node_1852 (AllWinning.cons node_1529 (AllWinning.cons node_1139 (AllWinning.cons node_894 (AllWinning.cons node_670 (AllWinning.cons node_458 (AllWinning.cons node_313 (AllWinning.cons node_225 (AllWinning.cons node_123 (AllWinning.cons node_3315 (AllWinning.nil)))))))))))))

theorem node_3915 : Outcome ⟨14, 0, 1, 20⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 26⟩) (by decide) node_66

theorem node_3916 : Outcome ⟨14, 0, 1, 26⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 26⟩) (by decide) node_66

theorem node_3917 : Outcome ⟨14, 1, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 0, 2⟩, ⟨12, 1, 0, 4⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3312 (AllWinning.cons node_2810 (AllWinning.cons node_3315 (AllWinning.nil)))

theorem node_3918 : Outcome ⟨14, 1, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 0, 2⟩, ⟨12, 1, 0, 4⟩, ⟨11, 1, 0, 6⟩, ⟨10, 1, 0, 8⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3312 (AllWinning.cons node_2810 (AllWinning.cons node_2354 (AllWinning.cons node_1857 (AllWinning.cons node_3315 (AllWinning.nil)))))

theorem node_3919 : Outcome ⟨14, 1, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 0, 2⟩, ⟨12, 1, 0, 4⟩, ⟨11, 1, 0, 6⟩, ⟨10, 1, 0, 8⟩, ⟨9, 1, 0, 10⟩, ⟨8, 1, 0, 12⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3312 (AllWinning.cons node_2810 (AllWinning.cons node_2354 (AllWinning.cons node_1857 (AllWinning.cons node_1534 (AllWinning.cons node_1144 (AllWinning.cons node_3315 (AllWinning.nil)))))))

theorem node_3920 : Outcome ⟨14, 1, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 0, 2⟩, ⟨12, 1, 0, 4⟩, ⟨11, 1, 0, 6⟩, ⟨10, 1, 0, 8⟩, ⟨9, 1, 0, 10⟩, ⟨8, 1, 0, 12⟩, ⟨7, 1, 0, 14⟩, ⟨6, 1, 0, 16⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3312 (AllWinning.cons node_2810 (AllWinning.cons node_2354 (AllWinning.cons node_1857 (AllWinning.cons node_1534 (AllWinning.cons node_1144 (AllWinning.cons node_900 (AllWinning.cons node_675 (AllWinning.cons node_3315 (AllWinning.nil)))))))))

theorem node_3921 : Outcome ⟨14, 1, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 0, 2⟩, ⟨12, 1, 0, 4⟩, ⟨11, 1, 0, 6⟩, ⟨10, 1, 0, 8⟩, ⟨9, 1, 0, 10⟩, ⟨8, 1, 0, 12⟩, ⟨7, 1, 0, 14⟩, ⟨6, 1, 0, 16⟩, ⟨5, 1, 0, 18⟩, ⟨4, 1, 0, 20⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3312 (AllWinning.cons node_2810 (AllWinning.cons node_2354 (AllWinning.cons node_1857 (AllWinning.cons node_1534 (AllWinning.cons node_1144 (AllWinning.cons node_900 (AllWinning.cons node_675 (AllWinning.cons node_461 (AllWinning.cons node_318 (AllWinning.cons node_3315 (AllWinning.nil)))))))))))

theorem node_3922 : Outcome ⟨14, 1, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 0, 2⟩, ⟨12, 1, 0, 4⟩, ⟨11, 1, 0, 6⟩, ⟨10, 1, 0, 8⟩, ⟨9, 1, 0, 10⟩, ⟨8, 1, 0, 12⟩, ⟨7, 1, 0, 14⟩, ⟨6, 1, 0, 16⟩, ⟨5, 1, 0, 18⟩, ⟨4, 1, 0, 20⟩, ⟨3, 1, 0, 22⟩, ⟨2, 1, 0, 24⟩, ⟨14, 0, 0, 2⟩]
  exact AllWinning.cons node_3312 (AllWinning.cons node_2810 (AllWinning.cons node_2354 (AllWinning.cons node_1857 (AllWinning.cons node_1534 (AllWinning.cons node_1144 (AllWinning.cons node_900 (AllWinning.cons node_675 (AllWinning.cons node_461 (AllWinning.cons node_318 (AllWinning.cons node_230 (AllWinning.cons node_127 (AllWinning.cons node_3315 (AllWinning.nil)))))))))))))

theorem node_3923 : Outcome ⟨14, 1, 0, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 26⟩) (by decide) node_83

theorem node_3924 : Outcome ⟨14, 1, 0, 26⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 26⟩) (by decide) node_83

theorem node_3925 : Outcome ⟨15, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨13, 0, 0, 4⟩) (by decide) node_2815

theorem node_3926 : Outcome ⟨15, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨13, 0, 0, 4⟩) (by decide) node_2815

theorem node_3927 : Outcome ⟨0, 0, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 15, 2⟩, ⟨0, 0, 14, 4⟩]
  exact AllWinning.cons node_3318 (AllWinning.cons node_2822 (AllWinning.nil))

theorem node_3928 : Outcome ⟨0, 0, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 6⟩) (by decide) node_2362

theorem node_3929 : Outcome ⟨0, 0, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 6⟩) (by decide) node_2362

theorem node_3930 : Outcome ⟨0, 0, 16, 32⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 32⟩) (by decide) node_14

theorem node_3931 : Outcome ⟨0, 1, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 2⟩) (by decide) node_3321

theorem node_3932 : Outcome ⟨0, 1, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 2⟩) (by decide) node_3321

theorem node_3933 : Outcome ⟨0, 1, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 2⟩) (by decide) node_3321

theorem node_3934 : Outcome ⟨0, 1, 15, 32⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 28⟩) (by decide) node_45

theorem node_3935 : Outcome ⟨0, 2, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 2⟩) (by decide) node_3321

theorem node_3936 : Outcome ⟨0, 2, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 2⟩) (by decide) node_3321

theorem node_3937 : Outcome ⟨0, 2, 14, 24⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 24⟩) (by decide) node_152

theorem node_3938 : Outcome ⟨0, 3, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 6⟩) (by decide) node_2362

theorem node_3939 : Outcome ⟨0, 3, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 6⟩) (by decide) node_2362

theorem node_3940 : Outcome ⟨0, 3, 13, 20⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 20⟩) (by decide) node_346

theorem node_3941 : Outcome ⟨0, 4, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 12, 2⟩, ⟨0, 2, 12, 4⟩, ⟨0, 4, 11, 2⟩, ⟨0, 4, 10, 4⟩]
  exact AllWinning.cons node_3332 (AllWinning.cons node_2829 (AllWinning.cons node_3335 (AllWinning.cons node_2840 (AllWinning.nil))))

theorem node_3942 : Outcome ⟨0, 4, 12, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 12, 2⟩, ⟨0, 2, 12, 4⟩, ⟨0, 1, 12, 6⟩, ⟨0, 0, 12, 8⟩, ⟨0, 4, 11, 2⟩, ⟨0, 4, 10, 4⟩, ⟨0, 4, 9, 6⟩, ⟨0, 4, 8, 8⟩]
  exact AllWinning.cons node_3332 (AllWinning.cons node_2829 (AllWinning.cons node_2369 (AllWinning.cons node_1865 (AllWinning.cons node_3335 (AllWinning.cons node_2840 (AllWinning.cons node_2383 (AllWinning.cons node_1883 (AllWinning.nil))))))))

theorem node_3943 : Outcome ⟨0, 4, 12, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 12, 2⟩, ⟨0, 2, 12, 4⟩, ⟨0, 1, 12, 6⟩, ⟨0, 0, 12, 8⟩, ⟨0, 4, 11, 2⟩, ⟨0, 4, 10, 4⟩, ⟨0, 4, 9, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 4, 7, 10⟩, ⟨0, 4, 6, 12⟩]
  exact AllWinning.cons node_3332 (AllWinning.cons node_2829 (AllWinning.cons node_2369 (AllWinning.cons node_1865 (AllWinning.cons node_3335 (AllWinning.cons node_2840 (AllWinning.cons node_2383 (AllWinning.cons node_1883 (AllWinning.cons node_1564 (AllWinning.cons node_1169 (AllWinning.nil))))))))))

theorem node_3944 : Outcome ⟨0, 4, 12, 10⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 16⟩) (by decide) node_706

theorem node_3945 : Outcome ⟨0, 4, 12, 16⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 16⟩) (by decide) node_706

theorem node_3946 : Outcome ⟨0, 4, 12, 26⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 16⟩) (by decide) node_706

theorem node_3947 : Outcome ⟨0, 5, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 11, 4⟩) (by decide) node_2835

theorem node_3948 : Outcome ⟨0, 5, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 11, 4⟩) (by decide) node_2835

theorem node_3949 : Outcome ⟨0, 5, 11, 6⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 12⟩) (by decide) node_1176

theorem node_3950 : Outcome ⟨0, 5, 11, 12⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 12⟩) (by decide) node_1176

theorem node_3951 : Outcome ⟨0, 5, 11, 14⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 12⟩) (by decide) node_1176

theorem node_3952 : Outcome ⟨0, 6, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 10, 2⟩) (by decide) node_3339

theorem node_3953 : Outcome ⟨0, 6, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 8⟩) (by decide) node_1892

theorem node_3954 : Outcome ⟨0, 6, 10, 18⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 8⟩) (by decide) node_1892

theorem node_3955 : Outcome ⟨0, 7, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 4⟩) (by decide) node_2850

theorem node_3956 : Outcome ⟨0, 7, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 4⟩) (by decide) node_2850

theorem node_3957 : Outcome ⟨0, 7, 9, 26⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 4⟩) (by decide) node_2850

theorem node_3958 : Outcome ⟨0, 8, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.nil))))

theorem node_3959 : Outcome ⟨0, 8, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.nil))))))))

theorem node_3960 : Outcome ⟨0, 8, 8, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.nil))))))))))))

theorem node_3961 : Outcome ⟨0, 8, 8, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3962 : Outcome ⟨0, 8, 8, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3963 : Outcome ⟨0, 8, 8, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3964 : Outcome ⟨0, 8, 8, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3965 : Outcome ⟨0, 8, 8, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3966 : Outcome ⟨0, 8, 8, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3967 : Outcome ⟨0, 8, 8, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3968 : Outcome ⟨0, 8, 8, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3969 : Outcome ⟨0, 8, 8, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3970 : Outcome ⟨0, 8, 8, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 8, 2⟩, ⟨0, 6, 8, 4⟩, ⟨0, 5, 8, 6⟩, ⟨0, 4, 8, 8⟩, ⟨0, 3, 8, 10⟩, ⟨0, 2, 8, 12⟩, ⟨0, 1, 8, 14⟩, ⟨0, 0, 8, 16⟩, ⟨0, 8, 7, 2⟩, ⟨0, 8, 6, 4⟩, ⟨0, 8, 5, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 8, 3, 10⟩, ⟨0, 8, 2, 12⟩, ⟨0, 8, 1, 14⟩, ⟨0, 8, 0, 16⟩]
  exact AllWinning.cons node_3348 (AllWinning.cons node_2847 (AllWinning.cons node_2389 (AllWinning.cons node_1883 (AllWinning.cons node_1558 (AllWinning.cons node_1162 (AllWinning.cons node_914 (AllWinning.cons node_684 (AllWinning.cons node_3351 (AllWinning.cons node_2863 (AllWinning.cons node_2401 (AllWinning.cons node_1908 (AllWinning.cons node_1579 (AllWinning.cons node_1194 (AllWinning.cons node_945 (AllWinning.cons node_733 (AllWinning.nil))))))))))))))))

theorem node_3971 : Outcome ⟨0, 9, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 4⟩) (by decide) node_2850

theorem node_3972 : Outcome ⟨0, 9, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 4⟩) (by decide) node_2850

theorem node_3973 : Outcome ⟨0, 9, 7, 26⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 4⟩) (by decide) node_2850

theorem node_3974 : Outcome ⟨0, 10, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 6, 2⟩) (by decide) node_3354

theorem node_3975 : Outcome ⟨0, 10, 6, 8⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 8⟩) (by decide) node_1892

theorem node_3976 : Outcome ⟨0, 10, 6, 18⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 8⟩) (by decide) node_1892

theorem node_3977 : Outcome ⟨0, 11, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 3, 4⟩) (by decide) node_2873

theorem node_3978 : Outcome ⟨0, 11, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 11, 3, 4⟩) (by decide) node_2873

theorem node_3979 : Outcome ⟨0, 11, 5, 6⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 12⟩) (by decide) node_1176

theorem node_3980 : Outcome ⟨0, 11, 5, 12⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 12⟩) (by decide) node_1176

theorem node_3981 : Outcome ⟨0, 11, 5, 14⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 12⟩) (by decide) node_1176

theorem node_3982 : Outcome ⟨0, 12, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 4, 2⟩, ⟨0, 10, 4, 4⟩, ⟨0, 12, 3, 2⟩, ⟨0, 12, 2, 4⟩]
  exact AllWinning.cons node_3363 (AllWinning.cons node_2869 (AllWinning.cons node_3367 (AllWinning.cons node_2878 (AllWinning.nil))))

theorem node_3983 : Outcome ⟨0, 12, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 4, 2⟩, ⟨0, 10, 4, 4⟩, ⟨0, 9, 4, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 12, 3, 2⟩, ⟨0, 12, 2, 4⟩, ⟨0, 12, 1, 6⟩, ⟨0, 12, 0, 8⟩]
  exact AllWinning.cons node_3363 (AllWinning.cons node_2869 (AllWinning.cons node_2406 (AllWinning.cons node_1908 (AllWinning.cons node_3367 (AllWinning.cons node_2878 (AllWinning.cons node_2421 (AllWinning.cons node_1926 (AllWinning.nil))))))))

theorem node_3984 : Outcome ⟨0, 12, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 11, 4, 2⟩, ⟨0, 10, 4, 4⟩, ⟨0, 9, 4, 6⟩, ⟨0, 8, 4, 8⟩, ⟨0, 7, 4, 10⟩, ⟨0, 6, 4, 12⟩, ⟨0, 12, 3, 2⟩, ⟨0, 12, 2, 4⟩, ⟨0, 12, 1, 6⟩, ⟨0, 12, 0, 8⟩]
  exact AllWinning.cons node_3363 (AllWinning.cons node_2869 (AllWinning.cons node_2406 (AllWinning.cons node_1908 (AllWinning.cons node_1574 (AllWinning.cons node_1186 (AllWinning.cons node_3367 (AllWinning.cons node_2878 (AllWinning.cons node_2421 (AllWinning.cons node_1926 (AllWinning.nil))))))))))

theorem node_3985 : Outcome ⟨0, 12, 4, 10⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 16⟩) (by decide) node_706

theorem node_3986 : Outcome ⟨0, 12, 4, 16⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 16⟩) (by decide) node_706

theorem node_3987 : Outcome ⟨0, 12, 4, 26⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 16⟩) (by decide) node_706

theorem node_3988 : Outcome ⟨0, 13, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 6⟩) (by decide) node_2426

theorem node_3989 : Outcome ⟨0, 13, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 6⟩) (by decide) node_2426

theorem node_3990 : Outcome ⟨0, 13, 3, 20⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 20⟩) (by decide) node_346

theorem node_3991 : Outcome ⟨0, 14, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 2⟩) (by decide) node_3373

theorem node_3992 : Outcome ⟨0, 14, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 2⟩) (by decide) node_3373

theorem node_3993 : Outcome ⟨0, 14, 2, 24⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 24⟩) (by decide) node_152

theorem node_3994 : Outcome ⟨0, 15, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 2⟩) (by decide) node_3373

theorem node_3995 : Outcome ⟨0, 15, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 2⟩) (by decide) node_3373

theorem node_3996 : Outcome ⟨0, 15, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 2⟩) (by decide) node_3373

theorem node_3997 : Outcome ⟨0, 15, 1, 32⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 28⟩) (by decide) node_45

theorem node_3998 : Outcome ⟨0, 16, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 15, 0, 2⟩, ⟨0, 14, 0, 4⟩]
  exact AllWinning.cons node_3381 (AllWinning.cons node_2887 (AllWinning.nil))

theorem node_3999 : Outcome ⟨0, 16, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 6⟩) (by decide) node_2426

theorem node_4000 : Outcome ⟨0, 16, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 6⟩) (by decide) node_2426

theorem node_4001 : Outcome ⟨0, 16, 0, 32⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 32⟩) (by decide) node_14

theorem node_4002 : Outcome ⟨1, 0, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 2⟩) (by decide) node_3384

theorem node_4003 : Outcome ⟨1, 0, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 2⟩) (by decide) node_3384

theorem node_4004 : Outcome ⟨1, 1, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 2⟩) (by decide) node_3321

theorem node_4005 : Outcome ⟨1, 1, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 14, 2⟩) (by decide) node_3321

theorem node_4006 : Outcome ⟨1, 1, 14, 18⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 28⟩) (by decide) node_84

theorem node_4007 : Outcome ⟨1, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 2⟩) (by decide) node_3392

theorem node_4008 : Outcome ⟨1, 2, 13, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 2⟩) (by decide) node_3392

theorem node_4009 : Outcome ⟨1, 3, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 2⟩) (by decide) node_3398

theorem node_4010 : Outcome ⟨1, 3, 12, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 12⟩) (by decide) node_1224

theorem node_4011 : Outcome ⟨1, 3, 12, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 12⟩) (by decide) node_1224

theorem node_4012 : Outcome ⟨1, 3, 12, 16⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 12⟩) (by decide) node_1224

theorem node_4013 : Outcome ⟨1, 4, 11, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 2⟩) (by decide) node_3407

theorem node_4014 : Outcome ⟨1, 4, 11, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 2⟩) (by decide) node_3407

theorem node_4015 : Outcome ⟨1, 5, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 10, 2⟩) (by decide) node_3339

theorem node_4016 : Outcome ⟨1, 5, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 10, 2⟩) (by decide) node_3339

theorem node_4017 : Outcome ⟨1, 5, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 5, 10, 2⟩) (by decide) node_3339

theorem node_4018 : Outcome ⟨1, 5, 10, 18⟩ true :=
  Outcome.win (q := ⟨0, 5, 10, 2⟩) (by decide) node_3339

theorem node_4019 : Outcome ⟨1, 6, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 9, 2⟩) (by decide) node_3344

theorem node_4020 : Outcome ⟨1, 6, 9, 8⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 12⟩) (by decide) node_1252

theorem node_4021 : Outcome ⟨1, 6, 9, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 12⟩) (by decide) node_1252

theorem node_4022 : Outcome ⟨1, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4023 : Outcome ⟨1, 7, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4024 : Outcome ⟨1, 7, 8, 6⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4025 : Outcome ⟨1, 7, 8, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4026 : Outcome ⟨1, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4027 : Outcome ⟨1, 8, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4028 : Outcome ⟨1, 8, 7, 6⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4029 : Outcome ⟨1, 8, 7, 10⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4030 : Outcome ⟨1, 9, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 6, 2⟩) (by decide) node_3354

theorem node_4031 : Outcome ⟨1, 9, 6, 8⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 12⟩) (by decide) node_1224

theorem node_4032 : Outcome ⟨1, 9, 6, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 12⟩) (by decide) node_1224

theorem node_4033 : Outcome ⟨1, 10, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 10, 5, 2⟩) (by decide) node_3358

theorem node_4034 : Outcome ⟨1, 10, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 10, 5, 2⟩) (by decide) node_3358

theorem node_4035 : Outcome ⟨1, 10, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 10, 5, 2⟩) (by decide) node_3358

theorem node_4036 : Outcome ⟨1, 10, 5, 18⟩ true :=
  Outcome.win (q := ⟨0, 10, 5, 2⟩) (by decide) node_3358

theorem node_4037 : Outcome ⟨1, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 2⟩) (by decide) node_3450

theorem node_4038 : Outcome ⟨1, 11, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 2⟩) (by decide) node_3450

theorem node_4039 : Outcome ⟨1, 11, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 2⟩) (by decide) node_3450

theorem node_4040 : Outcome ⟨1, 12, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 2⟩) (by decide) node_3458

theorem node_4041 : Outcome ⟨1, 12, 3, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 12⟩) (by decide) node_1252

theorem node_4042 : Outcome ⟨1, 12, 3, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 12⟩) (by decide) node_1252

theorem node_4043 : Outcome ⟨1, 12, 3, 16⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 12⟩) (by decide) node_1252

theorem node_4044 : Outcome ⟨1, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 2⟩) (by decide) node_3458

theorem node_4045 : Outcome ⟨1, 13, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 2⟩) (by decide) node_3458

theorem node_4046 : Outcome ⟨1, 13, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 2⟩) (by decide) node_3458

theorem node_4047 : Outcome ⟨1, 14, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 2⟩) (by decide) node_3373

theorem node_4048 : Outcome ⟨1, 14, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 1, 2⟩) (by decide) node_3373

theorem node_4049 : Outcome ⟨1, 14, 1, 18⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 28⟩) (by decide) node_67

theorem node_4050 : Outcome ⟨1, 15, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 2⟩) (by decide) node_3470

theorem node_4051 : Outcome ⟨1, 15, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 2⟩) (by decide) node_3470

theorem node_4052 : Outcome ⟨2, 0, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 2⟩) (by decide) node_3384

theorem node_4053 : Outcome ⟨2, 0, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 2⟩) (by decide) node_3384

theorem node_4054 : Outcome ⟨2, 0, 14, 24⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 24⟩) (by decide) node_194

theorem node_4055 : Outcome ⟨2, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 2⟩) (by decide) node_3392

theorem node_4056 : Outcome ⟨2, 1, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 2⟩) (by decide) node_3392

theorem node_4057 : Outcome ⟨2, 1, 13, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 2⟩) (by decide) node_3392

theorem node_4058 : Outcome ⟨2, 2, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 2⟩) (by decide) node_3398

theorem node_4059 : Outcome ⟨2, 2, 12, 10⟩ true :=
  Outcome.win (q := ⟨1, 2, 12, 2⟩) (by decide) node_3398

theorem node_4060 : Outcome ⟨2, 2, 12, 24⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 24⟩) (by decide) node_215

theorem node_4061 : Outcome ⟨2, 3, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 11, 4⟩) (by decide) node_2835

theorem node_4062 : Outcome ⟨2, 3, 11, 6⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 8⟩) (by decide) node_1997

theorem node_4063 : Outcome ⟨2, 3, 11, 18⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 8⟩) (by decide) node_1997

theorem node_4064 : Outcome ⟨2, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 2⟩) (by decide) node_3407

theorem node_4065 : Outcome ⟨2, 4, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 10, 2⟩) (by decide) node_3407

theorem node_4066 : Outcome ⟨2, 5, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 2⟩) (by decide) node_3412

theorem node_4067 : Outcome ⟨2, 5, 9, 20⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 2⟩) (by decide) node_3412

theorem node_4068 : Outcome ⟨2, 5, 9, 24⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 2⟩) (by decide) node_3412

theorem node_4069 : Outcome ⟨2, 6, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4070 : Outcome ⟨2, 6, 8, 6⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4071 : Outcome ⟨2, 6, 8, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4072 : Outcome ⟨2, 6, 8, 26⟩ true :=
  Outcome.win (q := ⟨1, 6, 8, 2⟩) (by decide) node_3426

theorem node_4073 : Outcome ⟨2, 7, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 4⟩) (by decide) node_2850

theorem node_4074 : Outcome ⟨2, 7, 7, 10⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 8⟩) (by decide) node_1997

theorem node_4075 : Outcome ⟨2, 7, 7, 20⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 8⟩) (by decide) node_1997

theorem node_4076 : Outcome ⟨2, 7, 7, 22⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 8⟩) (by decide) node_1997

theorem node_4077 : Outcome ⟨2, 8, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4078 : Outcome ⟨2, 8, 6, 6⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4079 : Outcome ⟨2, 8, 6, 10⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4080 : Outcome ⟨2, 8, 6, 26⟩ true :=
  Outcome.win (q := ⟨1, 8, 6, 2⟩) (by decide) node_3432

theorem node_4081 : Outcome ⟨2, 9, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 2⟩) (by decide) node_3436

theorem node_4082 : Outcome ⟨2, 9, 5, 20⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 2⟩) (by decide) node_3436

theorem node_4083 : Outcome ⟨2, 9, 5, 24⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 2⟩) (by decide) node_3436

theorem node_4084 : Outcome ⟨2, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 2⟩) (by decide) node_3450

theorem node_4085 : Outcome ⟨2, 10, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 10, 4, 2⟩) (by decide) node_3450

theorem node_4086 : Outcome ⟨2, 11, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 3, 4⟩) (by decide) node_2873

theorem node_4087 : Outcome ⟨2, 11, 3, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 8⟩) (by decide) node_2027

theorem node_4088 : Outcome ⟨2, 11, 3, 18⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 8⟩) (by decide) node_2027

theorem node_4089 : Outcome ⟨2, 12, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 2⟩) (by decide) node_3458

theorem node_4090 : Outcome ⟨2, 12, 2, 10⟩ true :=
  Outcome.win (q := ⟨1, 12, 2, 2⟩) (by decide) node_3458

theorem node_4091 : Outcome ⟨2, 12, 2, 24⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 24⟩) (by decide) node_194

theorem node_4092 : Outcome ⟨2, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 2⟩) (by decide) node_3464

theorem node_4093 : Outcome ⟨2, 13, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 2⟩) (by decide) node_3464

theorem node_4094 : Outcome ⟨2, 13, 1, 8⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 2⟩) (by decide) node_3464

theorem node_4095 : Outcome ⟨2, 14, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 2⟩) (by decide) node_3470

theorem node_4096 : Outcome ⟨2, 14, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 2⟩) (by decide) node_3470

theorem node_4097 : Outcome ⟨2, 14, 0, 24⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 24⟩) (by decide) node_215

theorem node_4098 : Outcome ⟨3, 0, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 6⟩) (by decide) node_2362

theorem node_4099 : Outcome ⟨3, 0, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 6⟩) (by decide) node_2362

theorem node_4100 : Outcome ⟨3, 0, 13, 20⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 20⟩) (by decide) node_412

theorem node_4101 : Outcome ⟨3, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 12, 2⟩) (by decide) node_3481

theorem node_4102 : Outcome ⟨3, 1, 12, 10⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 12⟩) (by decide) node_1324

theorem node_4103 : Outcome ⟨3, 1, 12, 14⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 12⟩) (by decide) node_1324

theorem node_4104 : Outcome ⟨3, 1, 12, 16⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 12⟩) (by decide) node_1324

theorem node_4105 : Outcome ⟨3, 2, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 0, 11, 4⟩) (by decide) node_2992

theorem node_4106 : Outcome ⟨3, 2, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 8⟩) (by decide) node_2068

theorem node_4107 : Outcome ⟨3, 2, 11, 18⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 8⟩) (by decide) node_2068

theorem node_4108 : Outcome ⟨3, 3, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 4⟩) (by decide) node_3007

theorem node_4109 : Outcome ⟨3, 3, 10, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 4⟩) (by decide) node_3007

theorem node_4110 : Outcome ⟨3, 3, 10, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 8, 4⟩) (by decide) node_3007

end RQ9F1
