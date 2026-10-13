import Chunk81
set_option autoImplicit false
namespace RQ9F1

theorem node_17813 : Outcome ⟨17, 11, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 2, 2⟩, ⟨15, 11, 2, 4⟩, ⟨17, 10, 2, 2⟩, ⟨17, 9, 2, 4⟩, ⟨17, 11, 1, 2⟩, ⟨17, 11, 0, 4⟩]
  exact AllWinning.cons node_16856 (AllWinning.cons node_15777 (AllWinning.cons node_16903 (AllWinning.cons node_15840 (AllWinning.cons node_16905 (AllWinning.cons node_15845 (AllWinning.nil))))))

theorem node_17814 : Outcome ⟨17, 11, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 2, 2⟩, ⟨15, 11, 2, 4⟩, ⟨14, 11, 2, 6⟩, ⟨13, 11, 2, 8⟩, ⟨17, 10, 2, 2⟩, ⟨17, 9, 2, 4⟩, ⟨17, 8, 2, 6⟩, ⟨17, 7, 2, 8⟩, ⟨17, 11, 1, 2⟩, ⟨17, 11, 0, 4⟩]
  exact AllWinning.cons node_16856 (AllWinning.cons node_15777 (AllWinning.cons node_14743 (AllWinning.cons node_13756 (AllWinning.cons node_16903 (AllWinning.cons node_15840 (AllWinning.cons node_14854 (AllWinning.cons node_13898 (AllWinning.cons node_16905 (AllWinning.cons node_15845 (AllWinning.nil))))))))))

theorem node_17815 : Outcome ⟨17, 11, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 2, 2⟩, ⟨15, 11, 2, 4⟩, ⟨14, 11, 2, 6⟩, ⟨13, 11, 2, 8⟩, ⟨12, 11, 2, 10⟩, ⟨11, 11, 2, 12⟩, ⟨10, 11, 2, 14⟩, ⟨9, 11, 2, 16⟩, ⟨17, 10, 2, 2⟩, ⟨17, 9, 2, 4⟩, ⟨17, 8, 2, 6⟩, ⟨17, 7, 2, 8⟩, ⟨17, 6, 2, 10⟩, ⟨17, 5, 2, 12⟩, ⟨17, 4, 2, 14⟩, ⟨17, 3, 2, 16⟩, ⟨17, 11, 1, 2⟩, ⟨17, 11, 0, 4⟩]
  exact AllWinning.cons node_16856 (AllWinning.cons node_15777 (AllWinning.cons node_14743 (AllWinning.cons node_13756 (AllWinning.cons node_12738 (AllWinning.cons node_11703 (AllWinning.cons node_10654 (AllWinning.cons node_9555 (AllWinning.cons node_16903 (AllWinning.cons node_15840 (AllWinning.cons node_14854 (AllWinning.cons node_13898 (AllWinning.cons node_12927 (AllWinning.cons node_11921 (AllWinning.cons node_10927 (AllWinning.cons node_9841 (AllWinning.cons node_16905 (AllWinning.cons node_15845 (AllWinning.nil))))))))))))))))))

theorem node_17816 : Outcome ⟨17, 11, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨16, 11, 2, 2⟩, ⟨15, 11, 2, 4⟩, ⟨14, 11, 2, 6⟩, ⟨13, 11, 2, 8⟩, ⟨12, 11, 2, 10⟩, ⟨11, 11, 2, 12⟩, ⟨10, 11, 2, 14⟩, ⟨9, 11, 2, 16⟩, ⟨8, 11, 2, 18⟩, ⟨7, 11, 2, 20⟩, ⟨17, 10, 2, 2⟩, ⟨17, 9, 2, 4⟩, ⟨17, 8, 2, 6⟩, ⟨17, 7, 2, 8⟩, ⟨17, 6, 2, 10⟩, ⟨17, 5, 2, 12⟩, ⟨17, 4, 2, 14⟩, ⟨17, 3, 2, 16⟩, ⟨17, 2, 2, 18⟩, ⟨17, 1, 2, 20⟩, ⟨17, 11, 1, 2⟩, ⟨17, 11, 0, 4⟩]
  exact AllWinning.cons node_16856 (AllWinning.cons node_15777 (AllWinning.cons node_14743 (AllWinning.cons node_13756 (AllWinning.cons node_12738 (AllWinning.cons node_11703 (AllWinning.cons node_10654 (AllWinning.cons node_9555 (AllWinning.cons node_8569 (AllWinning.cons node_7529 (AllWinning.cons node_16903 (AllWinning.cons node_15840 (AllWinning.cons node_14854 (AllWinning.cons node_13898 (AllWinning.cons node_12927 (AllWinning.cons node_11921 (AllWinning.cons node_10927 (AllWinning.cons node_9841 (AllWinning.cons node_8882 (AllWinning.cons node_7884 (AllWinning.cons node_16905 (AllWinning.cons node_15845 (AllWinning.nil))))))))))))))))))))))

theorem node_17817 : Outcome ⟨17, 12, 1, 2⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 2⟩) (by decide) node_16859

theorem node_17818 : Outcome ⟨17, 12, 1, 4⟩ true :=
  Outcome.win (q := ⟨16, 12, 1, 2⟩) (by decide) node_16859

theorem node_17819 : Outcome ⟨17, 13, 0, 2⟩ true :=
  Outcome.win (q := ⟨17, 12, 0, 2⟩) (by decide) node_16907

theorem node_17820 : Outcome ⟨17, 13, 0, 8⟩ true :=
  Outcome.win (q := ⟨13, 13, 0, 8⟩) (by decide) node_13764

theorem node_17821 : Outcome ⟨18, 0, 12, 2⟩ true :=
  Outcome.win (q := ⟨18, 0, 10, 4⟩) (by decide) node_15848

theorem node_17822 : Outcome ⟨18, 0, 12, 4⟩ true :=
  Outcome.win (q := ⟨18, 0, 10, 4⟩) (by decide) node_15848

theorem node_17823 : Outcome ⟨18, 0, 12, 10⟩ true :=
  Outcome.win (q := ⟨12, 0, 12, 12⟩) (by decide) node_11714

theorem node_17824 : Outcome ⟨18, 1, 11, 6⟩ true :=
  Outcome.win (q := ⟨15, 1, 11, 6⟩) (by decide) node_14755

theorem node_17825 : Outcome ⟨18, 1, 11, 16⟩ true :=
  Outcome.win (q := ⟨7, 1, 11, 22⟩) (by decide) node_6566

theorem node_17826 : Outcome ⟨18, 2, 10, 2⟩ true :=
  Outcome.win (q := ⟨16, 2, 10, 4⟩) (by decide) node_15792

theorem node_17827 : Outcome ⟨18, 2, 10, 4⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 6⟩) (by decide) node_14869

theorem node_17828 : Outcome ⟨18, 2, 10, 8⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 6⟩) (by decide) node_14869

theorem node_17829 : Outcome ⟨18, 2, 10, 12⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 6⟩) (by decide) node_14869

theorem node_17830 : Outcome ⟨18, 3, 9, 2⟩ true :=
  Outcome.win (q := ⟨17, 3, 9, 2⟩) (by decide) node_16872

theorem node_17831 : Outcome ⟨18, 3, 9, 12⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 12⟩) (by decide) node_11730

theorem node_17832 : Outcome ⟨18, 4, 8, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 2⟩) (by decide) node_16876

theorem node_17833 : Outcome ⟨18, 4, 8, 6⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 2⟩) (by decide) node_16876

theorem node_17834 : Outcome ⟨18, 4, 8, 8⟩ true :=
  Outcome.win (q := ⟨17, 4, 8, 2⟩) (by decide) node_16876

theorem node_17835 : Outcome ⟨18, 5, 7, 2⟩ true :=
  Outcome.win (q := ⟨18, 5, 5, 4⟩) (by decide) node_15862

theorem node_17836 : Outcome ⟨18, 5, 7, 10⟩ true :=
  Outcome.win (q := ⟨18, 2, 7, 6⟩) (by decide) node_14869

theorem node_17837 : Outcome ⟨18, 5, 7, 16⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 28⟩) (by decide) node_4182

theorem node_17838 : Outcome ⟨18, 6, 6, 8⟩ true :=
  Outcome.win (q := ⟨17, 6, 6, 2⟩) (by decide) node_16886

theorem node_17839 : Outcome ⟨18, 7, 5, 2⟩ true :=
  Outcome.win (q := ⟨18, 5, 5, 4⟩) (by decide) node_15862

theorem node_17840 : Outcome ⟨18, 7, 5, 10⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 6⟩) (by decide) node_14890

theorem node_17841 : Outcome ⟨18, 7, 5, 16⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 28⟩) (by decide) node_4199

theorem node_17842 : Outcome ⟨18, 8, 4, 2⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 2⟩) (by decide) node_16894

theorem node_17843 : Outcome ⟨18, 8, 4, 6⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 2⟩) (by decide) node_16894

theorem node_17844 : Outcome ⟨18, 8, 4, 8⟩ true :=
  Outcome.win (q := ⟨17, 8, 4, 2⟩) (by decide) node_16894

theorem node_17845 : Outcome ⟨18, 9, 3, 2⟩ true :=
  Outcome.win (q := ⟨17, 9, 3, 2⟩) (by decide) node_16899

theorem node_17846 : Outcome ⟨18, 9, 3, 12⟩ true :=
  Outcome.win (q := ⟨12, 9, 3, 12⟩) (by decide) node_11760

theorem node_17847 : Outcome ⟨18, 10, 2, 2⟩ true :=
  Outcome.win (q := ⟨16, 10, 2, 4⟩) (by decide) node_15810

theorem node_17848 : Outcome ⟨18, 10, 2, 4⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 6⟩) (by decide) node_14890

theorem node_17849 : Outcome ⟨18, 10, 2, 8⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 6⟩) (by decide) node_14890

theorem node_17850 : Outcome ⟨18, 10, 2, 12⟩ true :=
  Outcome.win (q := ⟨18, 7, 2, 6⟩) (by decide) node_14890

theorem node_17851 : Outcome ⟨18, 11, 1, 6⟩ true :=
  Outcome.win (q := ⟨15, 11, 1, 6⟩) (by decide) node_14781

theorem node_17852 : Outcome ⟨18, 12, 0, 2⟩ true :=
  Outcome.win (q := ⟨18, 10, 0, 4⟩) (by decide) node_15874

theorem node_17853 : Outcome ⟨18, 12, 0, 4⟩ true :=
  Outcome.win (q := ⟨18, 10, 0, 4⟩) (by decide) node_15874

theorem node_17854 : Outcome ⟨18, 12, 0, 10⟩ true :=
  Outcome.win (q := ⟨12, 12, 0, 12⟩) (by decide) node_11775

theorem node_17855 : Outcome ⟨19, 0, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 0, 11, 2⟩, ⟨17, 0, 11, 4⟩, ⟨16, 0, 11, 6⟩, ⟨15, 0, 11, 8⟩, ⟨19, 0, 10, 2⟩, ⟨19, 0, 9, 4⟩, ⟨19, 0, 8, 6⟩, ⟨19, 0, 7, 8⟩]
  exact AllWinning.cons node_16910 (AllWinning.cons node_15822 (AllWinning.cons node_14788 (AllWinning.cons node_13799 (AllWinning.cons node_16936 (AllWinning.cons node_15878 (AllWinning.cons node_14901 (AllWinning.cons node_13928 (AllWinning.nil))))))))

theorem node_17856 : Outcome ⟨19, 0, 11, 6⟩ true :=
  Outcome.win (q := ⟨19, 0, 6, 10⟩) (by decide) node_12958

theorem node_17857 : Outcome ⟨19, 0, 11, 16⟩ true :=
  Outcome.win (q := ⟨11, 0, 11, 16⟩) (by decide) node_9616

theorem node_17858 : Outcome ⟨19, 1, 10, 4⟩ true :=
  Outcome.win (q := ⟨19, 1, 9, 2⟩) (by decide) node_16940

theorem node_17859 : Outcome ⟨19, 1, 10, 8⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 10⟩) (by decide) node_12780

theorem node_17860 : Outcome ⟨19, 2, 9, 4⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 8⟩) (by decide) node_13806

theorem node_17861 : Outcome ⟨19, 2, 9, 8⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 8⟩) (by decide) node_13806

theorem node_17862 : Outcome ⟨19, 3, 8, 6⟩ true :=
  Outcome.win (q := ⟨16, 3, 8, 6⟩) (by decide) node_14799

theorem node_17863 : Outcome ⟨19, 4, 7, 4⟩ true :=
  Outcome.win (q := ⟨19, 3, 7, 2⟩) (by decide) node_16947

theorem node_17864 : Outcome ⟨19, 4, 7, 14⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 28⟩) (by decide) node_4248

theorem node_17865 : Outcome ⟨19, 5, 6, 4⟩ true :=
  Outcome.win (q := ⟨19, 4, 6, 2⟩) (by decide) node_16950

theorem node_17866 : Outcome ⟨19, 5, 6, 8⟩ true :=
  Outcome.win (q := ⟨19, 0, 6, 10⟩) (by decide) node_12958

theorem node_17867 : Outcome ⟨19, 6, 5, 4⟩ true :=
  Outcome.win (q := ⟨19, 6, 4, 2⟩) (by decide) node_16954

theorem node_17868 : Outcome ⟨19, 6, 5, 8⟩ true :=
  Outcome.win (q := ⟨19, 6, 0, 10⟩) (by decide) node_12976

theorem node_17869 : Outcome ⟨19, 7, 4, 4⟩ true :=
  Outcome.win (q := ⟨19, 6, 4, 2⟩) (by decide) node_16954

theorem node_17870 : Outcome ⟨19, 7, 4, 14⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 28⟩) (by decide) node_4265

theorem node_17871 : Outcome ⟨19, 8, 3, 6⟩ true :=
  Outcome.win (q := ⟨16, 8, 3, 6⟩) (by decide) node_14817

theorem node_17872 : Outcome ⟨19, 9, 2, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 8⟩) (by decide) node_13830

theorem node_17873 : Outcome ⟨19, 9, 2, 8⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 8⟩) (by decide) node_13830

theorem node_17874 : Outcome ⟨19, 10, 1, 4⟩ true :=
  Outcome.win (q := ⟨19, 9, 1, 2⟩) (by decide) node_16963

theorem node_17875 : Outcome ⟨19, 10, 1, 8⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 10⟩) (by decide) node_12813

theorem node_17876 : Outcome ⟨19, 11, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 11, 0, 2⟩, ⟨17, 11, 0, 4⟩, ⟨16, 11, 0, 6⟩, ⟨15, 11, 0, 8⟩, ⟨19, 10, 0, 2⟩, ⟨19, 9, 0, 4⟩, ⟨19, 8, 0, 6⟩, ⟨19, 7, 0, 8⟩]
  exact AllWinning.cons node_16933 (AllWinning.cons node_15845 (AllWinning.cons node_14831 (AllWinning.cons node_13837 (AllWinning.cons node_16966 (AllWinning.cons node_15899 (AllWinning.cons node_14917 (AllWinning.cons node_13941 (AllWinning.nil))))))))

theorem node_17877 : Outcome ⟨19, 11, 0, 6⟩ true :=
  Outcome.win (q := ⟨19, 6, 0, 10⟩) (by decide) node_12976

theorem node_17878 : Outcome ⟨19, 11, 0, 16⟩ true :=
  Outcome.win (q := ⟨11, 11, 0, 16⟩) (by decide) node_9668

theorem node_17879 : Outcome ⟨0, 11, 20, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 19, 2⟩) (by decide) node_16974

theorem node_17880 : Outcome ⟨0, 11, 20, 8⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 8⟩) (by decide) node_13947

theorem node_17881 : Outcome ⟨0, 11, 20, 18⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 18⟩) (by decide) node_8946

theorem node_17882 : Outcome ⟨0, 12, 19, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 17, 4⟩) (by decide) node_15913

theorem node_17883 : Outcome ⟨0, 12, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 12, 17, 4⟩) (by decide) node_15913

theorem node_17884 : Outcome ⟨0, 12, 19, 14⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 14⟩) (by decide) node_11005

theorem node_17885 : Outcome ⟨0, 13, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 18, 2⟩, ⟨0, 11, 18, 4⟩, ⟨0, 13, 17, 2⟩, ⟨0, 13, 16, 4⟩]
  exact AllWinning.cons node_16978 (AllWinning.cons node_15909 (AllWinning.cons node_16982 (AllWinning.cons node_15916 (AllWinning.nil))))

theorem node_17886 : Outcome ⟨0, 13, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 12, 18, 2⟩, ⟨0, 11, 18, 4⟩, ⟨0, 10, 18, 6⟩, ⟨0, 9, 18, 8⟩, ⟨0, 13, 17, 2⟩, ⟨0, 13, 16, 4⟩, ⟨0, 13, 15, 6⟩, ⟨0, 13, 14, 8⟩]
  exact AllWinning.cons node_16978 (AllWinning.cons node_15909 (AllWinning.cons node_14926 (AllWinning.cons node_13953 (AllWinning.cons node_16982 (AllWinning.cons node_15916 (AllWinning.cons node_14936 (AllWinning.cons node_13968 (AllWinning.nil))))))))

theorem node_17887 : Outcome ⟨0, 13, 18, 10⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 10⟩) (by decide) node_13005

theorem node_17888 : Outcome ⟨0, 13, 18, 14⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 10⟩) (by decide) node_13005

theorem node_17889 : Outcome ⟨0, 14, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17890 : Outcome ⟨0, 14, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17891 : Outcome ⟨0, 15, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 2⟩) (by decide) node_16988

theorem node_17892 : Outcome ⟨0, 15, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 2⟩) (by decide) node_16988

theorem node_17893 : Outcome ⟨0, 16, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 2⟩) (by decide) node_16988

theorem node_17894 : Outcome ⟨0, 16, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 2⟩) (by decide) node_16988

theorem node_17895 : Outcome ⟨0, 17, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17896 : Outcome ⟨0, 17, 14, 6⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17897 : Outcome ⟨0, 18, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨0, 16, 13, 4⟩, ⟨0, 18, 12, 2⟩, ⟨0, 18, 11, 4⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_15924 (AllWinning.cons node_17000 (AllWinning.cons node_15931 (AllWinning.nil))))

theorem node_17898 : Outcome ⟨0, 18, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨0, 16, 13, 4⟩, ⟨0, 15, 13, 6⟩, ⟨0, 14, 13, 8⟩, ⟨0, 18, 12, 2⟩, ⟨0, 18, 11, 4⟩, ⟨0, 18, 10, 6⟩, ⟨0, 18, 9, 8⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_15924 (AllWinning.cons node_14947 (AllWinning.cons node_13971 (AllWinning.cons node_17000 (AllWinning.cons node_15931 (AllWinning.cons node_14956 (AllWinning.cons node_13986 (AllWinning.nil))))))))

theorem node_17899 : Outcome ⟨0, 18, 13, 10⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 10⟩) (by decide) node_13005

theorem node_17900 : Outcome ⟨0, 18, 13, 14⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 10⟩) (by decide) node_13005

theorem node_17901 : Outcome ⟨0, 19, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 17, 12, 4⟩) (by decide) node_15927

theorem node_17902 : Outcome ⟨0, 19, 12, 4⟩ true :=
  Outcome.win (q := ⟨0, 17, 12, 4⟩) (by decide) node_15927

theorem node_17903 : Outcome ⟨0, 19, 12, 14⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 14⟩) (by decide) node_11005

theorem node_17904 : Outcome ⟨0, 20, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 19, 11, 2⟩) (by decide) node_17004

theorem node_17905 : Outcome ⟨0, 20, 11, 8⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 8⟩) (by decide) node_13993

theorem node_17906 : Outcome ⟨0, 20, 11, 18⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 18⟩) (by decide) node_8946

theorem node_17907 : Outcome ⟨1, 10, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 20, 2⟩, ⟨1, 9, 20, 2⟩, ⟨1, 8, 20, 4⟩, ⟨1, 10, 19, 2⟩, ⟨1, 10, 18, 4⟩]
  exact AllWinning.cons node_16970 (AllWinning.cons node_17012 (AllWinning.cons node_15941 (AllWinning.cons node_17015 (AllWinning.cons node_15947 (AllWinning.nil)))))

theorem node_17908 : Outcome ⟨1, 10, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 20, 2⟩, ⟨1, 9, 20, 2⟩, ⟨1, 8, 20, 4⟩, ⟨1, 7, 20, 6⟩, ⟨1, 6, 20, 8⟩, ⟨1, 10, 19, 2⟩, ⟨1, 10, 18, 4⟩, ⟨1, 10, 17, 6⟩, ⟨1, 10, 16, 8⟩]
  exact AllWinning.cons node_16970 (AllWinning.cons node_17012 (AllWinning.cons node_15941 (AllWinning.cons node_14964 (AllWinning.cons node_13996 (AllWinning.cons node_17015 (AllWinning.cons node_15947 (AllWinning.cons node_14973 (AllWinning.cons node_14012 (AllWinning.nil)))))))))

theorem node_17909 : Outcome ⟨1, 10, 20, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 12⟩) (by decide) node_12037

theorem node_17910 : Outcome ⟨1, 11, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 19, 4⟩) (by decide) node_15944

theorem node_17911 : Outcome ⟨1, 11, 19, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 19, 4⟩) (by decide) node_15944

theorem node_17912 : Outcome ⟨1, 11, 19, 14⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 24⟩) (by decide) node_6173

theorem node_17913 : Outcome ⟨1, 12, 18, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 16, 4⟩) (by decide) node_15954

theorem node_17914 : Outcome ⟨1, 12, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 16, 4⟩) (by decide) node_15954

theorem node_17915 : Outcome ⟨1, 12, 18, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 16, 4⟩) (by decide) node_15954

theorem node_17916 : Outcome ⟨1, 12, 18, 14⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 20⟩) (by decide) node_8034

theorem node_17917 : Outcome ⟨1, 13, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 17, 2⟩, ⟨1, 12, 17, 2⟩, ⟨1, 11, 17, 4⟩, ⟨1, 13, 16, 2⟩, ⟨1, 13, 15, 4⟩]
  exact AllWinning.cons node_16982 (AllWinning.cons node_17021 (AllWinning.cons node_15952 (AllWinning.cons node_17023 (AllWinning.cons node_15958 (AllWinning.nil)))))

theorem node_17918 : Outcome ⟨1, 13, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 17, 2⟩, ⟨1, 12, 17, 2⟩, ⟨1, 11, 17, 4⟩, ⟨1, 10, 17, 6⟩, ⟨1, 9, 17, 8⟩, ⟨1, 13, 16, 2⟩, ⟨1, 13, 15, 4⟩, ⟨1, 13, 14, 6⟩, ⟨1, 13, 13, 8⟩]
  exact AllWinning.cons node_16982 (AllWinning.cons node_17021 (AllWinning.cons node_15952 (AllWinning.cons node_14973 (AllWinning.cons node_14008 (AllWinning.cons node_17023 (AllWinning.cons node_15958 (AllWinning.cons node_14984 (AllWinning.cons node_14024 (AllWinning.nil)))))))))

theorem node_17919 : Outcome ⟨1, 13, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 17, 2⟩, ⟨1, 12, 17, 2⟩, ⟨1, 11, 17, 4⟩, ⟨1, 10, 17, 6⟩, ⟨1, 9, 17, 8⟩, ⟨1, 8, 17, 10⟩, ⟨1, 7, 17, 12⟩, ⟨1, 13, 16, 2⟩, ⟨1, 13, 15, 4⟩, ⟨1, 13, 14, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 13, 12, 10⟩, ⟨1, 13, 11, 12⟩]
  exact AllWinning.cons node_16982 (AllWinning.cons node_17021 (AllWinning.cons node_15952 (AllWinning.cons node_14973 (AllWinning.cons node_14008 (AllWinning.cons node_13040 (AllWinning.cons node_12023 (AllWinning.cons node_17023 (AllWinning.cons node_15958 (AllWinning.cons node_14984 (AllWinning.cons node_14024 (AllWinning.cons node_13057 (AllWinning.cons node_12051 (AllWinning.nil)))))))))))))

theorem node_17920 : Outcome ⟨1, 13, 17, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 17, 2⟩, ⟨1, 12, 17, 2⟩, ⟨1, 11, 17, 4⟩, ⟨1, 10, 17, 6⟩, ⟨1, 9, 17, 8⟩, ⟨1, 8, 17, 10⟩, ⟨1, 7, 17, 12⟩, ⟨1, 6, 17, 14⟩, ⟨1, 5, 17, 16⟩, ⟨1, 13, 16, 2⟩, ⟨1, 13, 15, 4⟩, ⟨1, 13, 14, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 13, 12, 10⟩, ⟨1, 13, 11, 12⟩, ⟨1, 13, 10, 14⟩, ⟨1, 13, 9, 16⟩]
  exact AllWinning.cons node_16982 (AllWinning.cons node_17021 (AllWinning.cons node_15952 (AllWinning.cons node_14973 (AllWinning.cons node_14008 (AllWinning.cons node_13040 (AllWinning.cons node_12023 (AllWinning.cons node_11041 (AllWinning.cons node_9950 (AllWinning.cons node_17023 (AllWinning.cons node_15958 (AllWinning.cons node_14984 (AllWinning.cons node_14024 (AllWinning.cons node_13057 (AllWinning.cons node_12051 (AllWinning.cons node_11067 (AllWinning.cons node_9988 (AllWinning.nil)))))))))))))))))

theorem node_17921 : Outcome ⟨1, 13, 17, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 17, 2⟩, ⟨1, 12, 17, 2⟩, ⟨1, 11, 17, 4⟩, ⟨1, 10, 17, 6⟩, ⟨1, 9, 17, 8⟩, ⟨1, 8, 17, 10⟩, ⟨1, 7, 17, 12⟩, ⟨1, 6, 17, 14⟩, ⟨1, 5, 17, 16⟩, ⟨1, 4, 17, 18⟩, ⟨1, 3, 17, 20⟩, ⟨1, 13, 16, 2⟩, ⟨1, 13, 15, 4⟩, ⟨1, 13, 14, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 13, 12, 10⟩, ⟨1, 13, 11, 12⟩, ⟨1, 13, 10, 14⟩, ⟨1, 13, 9, 16⟩, ⟨1, 13, 8, 18⟩, ⟨1, 13, 7, 20⟩]
  exact AllWinning.cons node_16982 (AllWinning.cons node_17021 (AllWinning.cons node_15952 (AllWinning.cons node_14973 (AllWinning.cons node_14008 (AllWinning.cons node_13040 (AllWinning.cons node_12023 (AllWinning.cons node_11041 (AllWinning.cons node_9950 (AllWinning.cons node_8993 (AllWinning.cons node_7987 (AllWinning.cons node_17023 (AllWinning.cons node_15958 (AllWinning.cons node_14984 (AllWinning.cons node_14024 (AllWinning.cons node_13057 (AllWinning.cons node_12051 (AllWinning.cons node_11067 (AllWinning.cons node_9988 (AllWinning.cons node_9022 (AllWinning.cons node_8041 (AllWinning.nil)))))))))))))))))))))

theorem node_17922 : Outcome ⟨1, 13, 17, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 17, 2⟩, ⟨1, 12, 17, 2⟩, ⟨1, 11, 17, 4⟩, ⟨1, 10, 17, 6⟩, ⟨1, 9, 17, 8⟩, ⟨1, 8, 17, 10⟩, ⟨1, 7, 17, 12⟩, ⟨1, 6, 17, 14⟩, ⟨1, 5, 17, 16⟩, ⟨1, 4, 17, 18⟩, ⟨1, 3, 17, 20⟩, ⟨1, 2, 17, 22⟩, ⟨1, 1, 17, 24⟩, ⟨1, 0, 17, 26⟩, ⟨1, 13, 16, 2⟩, ⟨1, 13, 15, 4⟩, ⟨1, 13, 14, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 13, 12, 10⟩, ⟨1, 13, 11, 12⟩, ⟨1, 13, 10, 14⟩, ⟨1, 13, 9, 16⟩, ⟨1, 13, 8, 18⟩, ⟨1, 13, 7, 20⟩, ⟨1, 13, 6, 22⟩, ⟨1, 13, 5, 24⟩, ⟨1, 13, 4, 26⟩, ⟨1, 13, 3, 28⟩]
  exact AllWinning.cons node_16982 (AllWinning.cons node_17021 (AllWinning.cons node_15952 (AllWinning.cons node_14973 (AllWinning.cons node_14008 (AllWinning.cons node_13040 (AllWinning.cons node_12023 (AllWinning.cons node_11041 (AllWinning.cons node_9950 (AllWinning.cons node_8993 (AllWinning.cons node_7987 (AllWinning.cons node_7039 (AllWinning.cons node_6118 (AllWinning.cons node_5391 (AllWinning.cons node_17023 (AllWinning.cons node_15958 (AllWinning.cons node_14984 (AllWinning.cons node_14024 (AllWinning.cons node_13057 (AllWinning.cons node_12051 (AllWinning.cons node_11067 (AllWinning.cons node_9988 (AllWinning.cons node_9022 (AllWinning.cons node_8041 (AllWinning.cons node_7082 (AllWinning.cons node_6180 (AllWinning.cons node_5440 (AllWinning.cons node_4706 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_17923 : Outcome ⟨1, 14, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 16, 4⟩) (by decide) node_15954

theorem node_17924 : Outcome ⟨1, 14, 16, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 16, 4⟩) (by decide) node_15954

theorem node_17925 : Outcome ⟨1, 14, 16, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 12⟩) (by decide) node_12057

theorem node_17926 : Outcome ⟨1, 14, 16, 18⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 12⟩) (by decide) node_12057

theorem node_17927 : Outcome ⟨1, 15, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 2⟩) (by decide) node_16988

theorem node_17928 : Outcome ⟨1, 15, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 2⟩) (by decide) node_16988

theorem node_17929 : Outcome ⟨1, 15, 15, 8⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 2⟩) (by decide) node_16988

theorem node_17930 : Outcome ⟨1, 16, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 12, 4⟩) (by decide) node_15968

theorem node_17931 : Outcome ⟨1, 16, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 12, 4⟩) (by decide) node_15968

theorem node_17932 : Outcome ⟨1, 16, 14, 6⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 12⟩) (by decide) node_12037

theorem node_17933 : Outcome ⟨1, 16, 14, 18⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 12⟩) (by decide) node_12037

theorem node_17934 : Outcome ⟨1, 17, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨1, 16, 13, 2⟩, ⟨1, 15, 13, 4⟩, ⟨1, 17, 12, 2⟩, ⟨1, 17, 11, 4⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_17033 (AllWinning.cons node_15965 (AllWinning.cons node_17035 (AllWinning.cons node_15972 (AllWinning.nil)))))

theorem node_17935 : Outcome ⟨1, 17, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨1, 16, 13, 2⟩, ⟨1, 15, 13, 4⟩, ⟨1, 14, 13, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 17, 12, 2⟩, ⟨1, 17, 11, 4⟩, ⟨1, 17, 10, 6⟩, ⟨1, 17, 9, 8⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_17033 (AllWinning.cons node_15965 (AllWinning.cons node_14988 (AllWinning.cons node_14024 (AllWinning.cons node_17035 (AllWinning.cons node_15972 (AllWinning.cons node_14998 (AllWinning.cons node_14040 (AllWinning.nil)))))))))

theorem node_17936 : Outcome ⟨1, 17, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨1, 16, 13, 2⟩, ⟨1, 15, 13, 4⟩, ⟨1, 14, 13, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 12, 13, 10⟩, ⟨1, 11, 13, 12⟩, ⟨1, 17, 12, 2⟩, ⟨1, 17, 11, 4⟩, ⟨1, 17, 10, 6⟩, ⟨1, 17, 9, 8⟩, ⟨1, 17, 8, 10⟩, ⟨1, 17, 7, 12⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_17033 (AllWinning.cons node_15965 (AllWinning.cons node_14988 (AllWinning.cons node_14024 (AllWinning.cons node_13052 (AllWinning.cons node_12044 (AllWinning.cons node_17035 (AllWinning.cons node_15972 (AllWinning.cons node_14998 (AllWinning.cons node_14040 (AllWinning.cons node_13070 (AllWinning.cons node_12073 (AllWinning.nil)))))))))))))

theorem node_17937 : Outcome ⟨1, 17, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨1, 16, 13, 2⟩, ⟨1, 15, 13, 4⟩, ⟨1, 14, 13, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 12, 13, 10⟩, ⟨1, 11, 13, 12⟩, ⟨1, 10, 13, 14⟩, ⟨1, 9, 13, 16⟩, ⟨1, 17, 12, 2⟩, ⟨1, 17, 11, 4⟩, ⟨1, 17, 10, 6⟩, ⟨1, 17, 9, 8⟩, ⟨1, 17, 8, 10⟩, ⟨1, 17, 7, 12⟩, ⟨1, 17, 6, 14⟩, ⟨1, 17, 5, 16⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_17033 (AllWinning.cons node_15965 (AllWinning.cons node_14988 (AllWinning.cons node_14024 (AllWinning.cons node_13052 (AllWinning.cons node_12044 (AllWinning.cons node_11056 (AllWinning.cons node_9971 (AllWinning.cons node_17035 (AllWinning.cons node_15972 (AllWinning.cons node_14998 (AllWinning.cons node_14040 (AllWinning.cons node_13070 (AllWinning.cons node_12073 (AllWinning.cons node_11080 (AllWinning.cons node_10008 (AllWinning.nil)))))))))))))))))

theorem node_17938 : Outcome ⟨1, 17, 13, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨1, 16, 13, 2⟩, ⟨1, 15, 13, 4⟩, ⟨1, 14, 13, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 12, 13, 10⟩, ⟨1, 11, 13, 12⟩, ⟨1, 10, 13, 14⟩, ⟨1, 9, 13, 16⟩, ⟨1, 8, 13, 18⟩, ⟨1, 7, 13, 20⟩, ⟨1, 17, 12, 2⟩, ⟨1, 17, 11, 4⟩, ⟨1, 17, 10, 6⟩, ⟨1, 17, 9, 8⟩, ⟨1, 17, 8, 10⟩, ⟨1, 17, 7, 12⟩, ⟨1, 17, 6, 14⟩, ⟨1, 17, 5, 16⟩, ⟨1, 17, 4, 18⟩, ⟨1, 17, 3, 20⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_17033 (AllWinning.cons node_15965 (AllWinning.cons node_14988 (AllWinning.cons node_14024 (AllWinning.cons node_13052 (AllWinning.cons node_12044 (AllWinning.cons node_11056 (AllWinning.cons node_9971 (AllWinning.cons node_9005 (AllWinning.cons node_8004 (AllWinning.cons node_17035 (AllWinning.cons node_15972 (AllWinning.cons node_14998 (AllWinning.cons node_14040 (AllWinning.cons node_13070 (AllWinning.cons node_12073 (AllWinning.cons node_11080 (AllWinning.cons node_10008 (AllWinning.cons node_9037 (AllWinning.cons node_8055 (AllWinning.nil)))))))))))))))))))))

theorem node_17939 : Outcome ⟨1, 17, 13, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 13, 2⟩, ⟨1, 16, 13, 2⟩, ⟨1, 15, 13, 4⟩, ⟨1, 14, 13, 6⟩, ⟨1, 13, 13, 8⟩, ⟨1, 12, 13, 10⟩, ⟨1, 11, 13, 12⟩, ⟨1, 10, 13, 14⟩, ⟨1, 9, 13, 16⟩, ⟨1, 8, 13, 18⟩, ⟨1, 7, 13, 20⟩, ⟨1, 6, 13, 22⟩, ⟨1, 5, 13, 24⟩, ⟨1, 4, 13, 26⟩, ⟨1, 3, 13, 28⟩, ⟨1, 17, 12, 2⟩, ⟨1, 17, 11, 4⟩, ⟨1, 17, 10, 6⟩, ⟨1, 17, 9, 8⟩, ⟨1, 17, 8, 10⟩, ⟨1, 17, 7, 12⟩, ⟨1, 17, 6, 14⟩, ⟨1, 17, 5, 16⟩, ⟨1, 17, 4, 18⟩, ⟨1, 17, 3, 20⟩, ⟨1, 17, 2, 22⟩, ⟨1, 17, 1, 24⟩, ⟨1, 17, 0, 26⟩]
  exact AllWinning.cons node_16998 (AllWinning.cons node_17033 (AllWinning.cons node_15965 (AllWinning.cons node_14988 (AllWinning.cons node_14024 (AllWinning.cons node_13052 (AllWinning.cons node_12044 (AllWinning.cons node_11056 (AllWinning.cons node_9971 (AllWinning.cons node_9005 (AllWinning.cons node_8004 (AllWinning.cons node_7058 (AllWinning.cons node_6132 (AllWinning.cons node_5408 (AllWinning.cons node_4665 (AllWinning.cons node_17035 (AllWinning.cons node_15972 (AllWinning.cons node_14998 (AllWinning.cons node_14040 (AllWinning.cons node_13070 (AllWinning.cons node_12073 (AllWinning.cons node_11080 (AllWinning.cons node_10008 (AllWinning.cons node_9037 (AllWinning.cons node_8055 (AllWinning.cons node_7105 (AllWinning.cons node_6193 (AllWinning.cons node_5455 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_17940 : Outcome ⟨1, 18, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 12, 4⟩) (by decide) node_15968

theorem node_17941 : Outcome ⟨1, 18, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 16, 12, 4⟩) (by decide) node_15968

theorem node_17942 : Outcome ⟨1, 18, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 16, 12, 4⟩) (by decide) node_15968

theorem node_17943 : Outcome ⟨1, 18, 12, 14⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 20⟩) (by decide) node_8013

theorem node_17944 : Outcome ⟨1, 19, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 9, 4⟩) (by decide) node_15978

theorem node_17945 : Outcome ⟨1, 19, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 19, 9, 4⟩) (by decide) node_15978

theorem node_17946 : Outcome ⟨1, 19, 11, 14⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 24⟩) (by decide) node_6148

theorem node_17947 : Outcome ⟨1, 20, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 20, 10, 2⟩, ⟨1, 19, 10, 2⟩, ⟨1, 18, 10, 4⟩, ⟨1, 20, 9, 2⟩, ⟨1, 20, 8, 4⟩]
  exact AllWinning.cons node_17008 (AllWinning.cons node_17039 (AllWinning.cons node_15973 (AllWinning.cons node_17043 (AllWinning.cons node_15981 (AllWinning.nil)))))

theorem node_17948 : Outcome ⟨1, 20, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 20, 10, 2⟩, ⟨1, 19, 10, 2⟩, ⟨1, 18, 10, 4⟩, ⟨1, 17, 10, 6⟩, ⟨1, 16, 10, 8⟩, ⟨1, 20, 9, 2⟩, ⟨1, 20, 8, 4⟩, ⟨1, 20, 7, 6⟩, ⟨1, 20, 6, 8⟩]
  exact AllWinning.cons node_17008 (AllWinning.cons node_17039 (AllWinning.cons node_15973 (AllWinning.cons node_14998 (AllWinning.cons node_14036 (AllWinning.cons node_17043 (AllWinning.cons node_15981 (AllWinning.cons node_15006 (AllWinning.cons node_14050 (AllWinning.nil)))))))))

theorem node_17949 : Outcome ⟨1, 20, 10, 6⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 12⟩) (by decide) node_12057

theorem node_17950 : Outcome ⟨2, 9, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 20, 2⟩, ⟨0, 9, 20, 4⟩, ⟨2, 8, 20, 2⟩, ⟨2, 7, 20, 4⟩, ⟨2, 9, 19, 2⟩, ⟨2, 9, 18, 4⟩]
  exact AllWinning.cons node_17012 (AllWinning.cons node_15901 (AllWinning.cons node_17046 (AllWinning.cons node_15983 (AllWinning.cons node_17048 (AllWinning.cons node_15992 (AllWinning.nil))))))

theorem node_17951 : Outcome ⟨2, 9, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 20, 2⟩, ⟨0, 9, 20, 4⟩, ⟨2, 8, 20, 2⟩, ⟨2, 7, 20, 4⟩, ⟨2, 6, 20, 6⟩, ⟨2, 5, 20, 8⟩, ⟨2, 9, 19, 2⟩, ⟨2, 9, 18, 4⟩, ⟨2, 9, 17, 6⟩, ⟨2, 9, 16, 8⟩]
  exact AllWinning.cons node_17012 (AllWinning.cons node_15901 (AllWinning.cons node_17046 (AllWinning.cons node_15983 (AllWinning.cons node_15008 (AllWinning.cons node_14053 (AllWinning.cons node_17048 (AllWinning.cons node_15992 (AllWinning.cons node_15017 (AllWinning.cons node_14068 (AllWinning.nil))))))))))

theorem node_17952 : Outcome ⟨2, 9, 20, 6⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 12⟩) (by decide) node_12087

theorem node_17953 : Outcome ⟨2, 9, 20, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 20, 12⟩) (by decide) node_12087

theorem node_17954 : Outcome ⟨2, 10, 19, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 6⟩) (by decide) node_15020

theorem node_17955 : Outcome ⟨2, 11, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 8⟩) (by decide) node_14059

theorem node_17956 : Outcome ⟨2, 11, 18, 10⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 8⟩) (by decide) node_14059

theorem node_17957 : Outcome ⟨2, 13, 16, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 15, 2⟩) (by decide) node_17062

theorem node_17958 : Outcome ⟨2, 13, 16, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 6⟩) (by decide) node_15020

theorem node_17959 : Outcome ⟨2, 13, 16, 10⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 6⟩) (by decide) node_15020

theorem node_17960 : Outcome ⟨2, 14, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 15, 2⟩) (by decide) node_17025

theorem node_17961 : Outcome ⟨2, 14, 15, 12⟩ true :=
  Outcome.win (q := ⟨2, 9, 15, 10⟩) (by decide) node_13094

theorem node_17962 : Outcome ⟨2, 15, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 14, 2⟩) (by decide) node_17029

theorem node_17963 : Outcome ⟨2, 15, 14, 12⟩ true :=
  Outcome.win (q := ⟨2, 15, 9, 10⟩) (by decide) node_13113

theorem node_17964 : Outcome ⟨2, 16, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 13, 2⟩) (by decide) node_17070

theorem node_17965 : Outcome ⟨2, 16, 13, 6⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 6⟩) (by decide) node_15050

theorem node_17966 : Outcome ⟨2, 16, 13, 10⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 6⟩) (by decide) node_15050

theorem node_17967 : Outcome ⟨2, 18, 11, 4⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 8⟩) (by decide) node_14089

theorem node_17968 : Outcome ⟨2, 18, 11, 10⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 8⟩) (by decide) node_14089

theorem node_17969 : Outcome ⟨2, 19, 10, 6⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 6⟩) (by decide) node_15050

theorem node_17970 : Outcome ⟨2, 20, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 9, 2⟩, ⟨0, 20, 9, 4⟩, ⟨2, 19, 9, 2⟩, ⟨2, 18, 9, 4⟩, ⟨2, 20, 8, 2⟩, ⟨2, 20, 7, 4⟩]
  exact AllWinning.cons node_17043 (AllWinning.cons node_15938 (AllWinning.cons node_17084 (AllWinning.cons node_16012 (AllWinning.cons node_17087 (AllWinning.cons node_16020 (AllWinning.nil))))))

theorem node_17971 : Outcome ⟨2, 20, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 20, 9, 2⟩, ⟨0, 20, 9, 4⟩, ⟨2, 19, 9, 2⟩, ⟨2, 18, 9, 4⟩, ⟨2, 17, 9, 6⟩, ⟨2, 16, 9, 8⟩, ⟨2, 20, 8, 2⟩, ⟨2, 20, 7, 4⟩, ⟨2, 20, 6, 6⟩, ⟨2, 20, 5, 8⟩]
  exact AllWinning.cons node_17043 (AllWinning.cons node_15938 (AllWinning.cons node_17084 (AllWinning.cons node_16012 (AllWinning.cons node_15056 (AllWinning.cons node_14082 (AllWinning.cons node_17087 (AllWinning.cons node_16020 (AllWinning.cons node_15063 (AllWinning.cons node_14097 (AllWinning.nil))))))))))

theorem node_17972 : Outcome ⟨2, 20, 9, 6⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 12⟩) (by decide) node_12150

theorem node_17973 : Outcome ⟨2, 20, 9, 14⟩ true :=
  Outcome.win (q := ⟨2, 20, 3, 12⟩) (by decide) node_12150

theorem node_17974 : Outcome ⟨3, 8, 20, 8⟩ true :=
  Outcome.win (q := ⟨3, 2, 20, 12⟩) (by decide) node_12155

theorem node_17975 : Outcome ⟨3, 9, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 19, 4⟩) (by decide) node_15944

theorem node_17976 : Outcome ⟨3, 9, 19, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 19, 4⟩) (by decide) node_15944

theorem node_17977 : Outcome ⟨3, 10, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 18, 2⟩, ⟨1, 10, 18, 4⟩, ⟨3, 9, 18, 2⟩, ⟨3, 8, 18, 4⟩, ⟨3, 10, 17, 2⟩, ⟨3, 10, 16, 4⟩]
  exact AllWinning.cons node_17051 (AllWinning.cons node_15947 (AllWinning.cons node_17092 (AllWinning.cons node_16027 (AllWinning.cons node_17094 (AllWinning.cons node_16034 (AllWinning.nil))))))

theorem node_17978 : Outcome ⟨3, 10, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 18, 2⟩, ⟨1, 10, 18, 4⟩, ⟨0, 10, 18, 6⟩, ⟨3, 9, 18, 2⟩, ⟨3, 8, 18, 4⟩, ⟨3, 7, 18, 6⟩, ⟨3, 6, 18, 8⟩, ⟨3, 10, 17, 2⟩, ⟨3, 10, 16, 4⟩, ⟨3, 10, 15, 6⟩, ⟨3, 10, 14, 8⟩]
  exact AllWinning.cons node_17051 (AllWinning.cons node_15947 (AllWinning.cons node_14926 (AllWinning.cons node_17092 (AllWinning.cons node_16027 (AllWinning.cons node_15071 (AllWinning.cons node_14104 (AllWinning.cons node_17094 (AllWinning.cons node_16034 (AllWinning.cons node_15079 (AllWinning.cons node_14123 (AllWinning.nil)))))))))))

theorem node_17979 : Outcome ⟨3, 10, 18, 6⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 10⟩) (by decide) node_13154

theorem node_17980 : Outcome ⟨3, 10, 18, 10⟩ true :=
  Outcome.win (q := ⟨3, 10, 13, 10⟩) (by decide) node_13154

theorem node_17981 : Outcome ⟨3, 11, 17, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 17, 4⟩) (by decide) node_16031

theorem node_17982 : Outcome ⟨3, 11, 17, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 17, 4⟩) (by decide) node_16031

theorem node_17983 : Outcome ⟨3, 11, 17, 10⟩ true :=
  Outcome.win (q := ⟨3, 9, 17, 4⟩) (by decide) node_16031

theorem node_17984 : Outcome ⟨3, 12, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 16, 4⟩) (by decide) node_15954

theorem node_17985 : Outcome ⟨3, 12, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 8⟩) (by decide) node_14112

theorem node_17986 : Outcome ⟨3, 12, 16, 8⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 14⟩) (by decide) node_11199

theorem node_17987 : Outcome ⟨3, 13, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 15, 2⟩) (by decide) node_17062

theorem node_17988 : Outcome ⟨3, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 15, 2⟩) (by decide) node_17062

theorem node_17989 : Outcome ⟨3, 13, 15, 10⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 12⟩) (by decide) node_12173

theorem node_17990 : Outcome ⟨3, 13, 15, 12⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 12⟩) (by decide) node_12173

theorem node_17991 : Outcome ⟨3, 14, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 14, 14, 2⟩, ⟨1, 14, 14, 4⟩, ⟨3, 13, 14, 2⟩, ⟨3, 12, 14, 4⟩, ⟨3, 14, 13, 2⟩, ⟨3, 14, 12, 4⟩]
  exact AllWinning.cons node_17065 (AllWinning.cons node_15961 (AllWinning.cons node_17104 (AllWinning.cons node_16041 (AllWinning.cons node_17108 (AllWinning.cons node_16050 (AllWinning.nil))))))

theorem node_17992 : Outcome ⟨3, 14, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17993 : Outcome ⟨3, 14, 14, 6⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17994 : Outcome ⟨3, 14, 14, 12⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17995 : Outcome ⟨3, 14, 14, 22⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 6⟩) (by decide) node_14939

theorem node_17996 : Outcome ⟨3, 15, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 13, 2⟩) (by decide) node_17070

theorem node_17997 : Outcome ⟨3, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 15, 13, 2⟩) (by decide) node_17070

theorem node_17998 : Outcome ⟨3, 15, 13, 10⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 12⟩) (by decide) node_12200

theorem node_17999 : Outcome ⟨3, 15, 13, 12⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 12⟩) (by decide) node_12200

theorem node_18000 : Outcome ⟨3, 16, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 12, 4⟩) (by decide) node_15968

theorem node_18001 : Outcome ⟨3, 16, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 8⟩) (by decide) node_14145

theorem node_18002 : Outcome ⟨3, 16, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 14⟩) (by decide) node_11178

theorem node_18003 : Outcome ⟨3, 17, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 17, 9, 4⟩) (by decide) node_16060

theorem node_18004 : Outcome ⟨3, 17, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 17, 9, 4⟩) (by decide) node_16060

theorem node_18005 : Outcome ⟨3, 17, 11, 10⟩ true :=
  Outcome.win (q := ⟨3, 17, 9, 4⟩) (by decide) node_16060

theorem node_18006 : Outcome ⟨3, 18, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 18, 10, 2⟩, ⟨1, 18, 10, 4⟩, ⟨3, 17, 10, 2⟩, ⟨3, 16, 10, 4⟩, ⟨3, 18, 9, 2⟩, ⟨3, 18, 8, 4⟩]
  exact AllWinning.cons node_17081 (AllWinning.cons node_15973 (AllWinning.cons node_17119 (AllWinning.cons node_16057 (AllWinning.cons node_17122 (AllWinning.cons node_16063 (AllWinning.nil))))))

theorem node_18007 : Outcome ⟨3, 18, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 18, 10, 2⟩, ⟨1, 18, 10, 4⟩, ⟨0, 18, 10, 6⟩, ⟨3, 17, 10, 2⟩, ⟨3, 16, 10, 4⟩, ⟨3, 15, 10, 6⟩, ⟨3, 14, 10, 8⟩, ⟨3, 18, 9, 2⟩, ⟨3, 18, 8, 4⟩, ⟨3, 18, 7, 6⟩, ⟨3, 18, 6, 8⟩]
  exact AllWinning.cons node_17081 (AllWinning.cons node_15973 (AllWinning.cons node_14956 (AllWinning.cons node_17119 (AllWinning.cons node_16057 (AllWinning.cons node_15098 (AllWinning.cons node_14136 (AllWinning.cons node_17122 (AllWinning.cons node_16063 (AllWinning.cons node_15105 (AllWinning.cons node_14154 (AllWinning.nil)))))))))))

theorem node_18008 : Outcome ⟨3, 18, 10, 6⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 10⟩) (by decide) node_13172

theorem node_18009 : Outcome ⟨3, 18, 10, 10⟩ true :=
  Outcome.win (q := ⟨3, 13, 10, 10⟩) (by decide) node_13172

theorem node_18010 : Outcome ⟨3, 19, 9, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 9, 4⟩) (by decide) node_15978

theorem node_18011 : Outcome ⟨3, 19, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 19, 9, 4⟩) (by decide) node_15978

theorem node_18012 : Outcome ⟨3, 20, 8, 8⟩ true :=
  Outcome.win (q := ⟨3, 20, 2, 12⟩) (by decide) node_12220

theorem node_18013 : Outcome ⟨4, 7, 20, 2⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 4⟩) (by decide) node_16072

theorem node_18014 : Outcome ⟨4, 7, 20, 6⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 8⟩) (by decide) node_13947

theorem node_18015 : Outcome ⟨4, 7, 20, 8⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 8⟩) (by decide) node_13947

theorem node_18016 : Outcome ⟨4, 7, 20, 12⟩ true :=
  Outcome.win (q := ⟨0, 7, 20, 8⟩) (by decide) node_13947

theorem node_18017 : Outcome ⟨4, 8, 19, 2⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 4⟩) (by decide) node_15986

theorem node_18018 : Outcome ⟨4, 8, 19, 12⟩ true :=
  Outcome.win (q := ⟨2, 8, 19, 4⟩) (by decide) node_15986

theorem node_18019 : Outcome ⟨4, 9, 18, 2⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 4⟩) (by decide) node_16089

theorem node_18020 : Outcome ⟨4, 9, 18, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 4⟩) (by decide) node_16089

theorem node_18021 : Outcome ⟨4, 10, 17, 6⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 4⟩) (by decide) node_16083

theorem node_18022 : Outcome ⟨4, 10, 17, 10⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 4⟩) (by decide) node_16083

theorem node_18023 : Outcome ⟨4, 10, 17, 12⟩ true :=
  Outcome.win (q := ⟨4, 10, 6, 22⟩) (by decide) node_7322

theorem node_18024 : Outcome ⟨4, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 4⟩) (by decide) node_16089

theorem node_18025 : Outcome ⟨4, 11, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 4⟩) (by decide) node_16089

theorem node_18026 : Outcome ⟨4, 11, 16, 6⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 4⟩) (by decide) node_16089

theorem node_18027 : Outcome ⟨4, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 4⟩) (by decide) node_16102

theorem node_18028 : Outcome ⟨4, 12, 15, 6⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 4⟩) (by decide) node_16102

theorem node_18029 : Outcome ⟨4, 12, 15, 10⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 4⟩) (by decide) node_16102

theorem node_18030 : Outcome ⟨4, 13, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 4⟩) (by decide) node_16112

theorem node_18031 : Outcome ⟨4, 13, 14, 4⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 4⟩) (by decide) node_16112

theorem node_18032 : Outcome ⟨4, 13, 14, 6⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 4⟩) (by decide) node_16112

theorem node_18033 : Outcome ⟨4, 13, 14, 12⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 4⟩) (by decide) node_16112

theorem node_18034 : Outcome ⟨4, 14, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 4⟩) (by decide) node_16102

theorem node_18035 : Outcome ⟨4, 14, 13, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 4⟩) (by decide) node_16102

theorem node_18036 : Outcome ⟨4, 14, 13, 6⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 4⟩) (by decide) node_16102

theorem node_18037 : Outcome ⟨4, 14, 13, 12⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 4⟩) (by decide) node_16102

theorem node_18038 : Outcome ⟨4, 15, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 4⟩) (by decide) node_16112

theorem node_18039 : Outcome ⟨4, 15, 12, 6⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 4⟩) (by decide) node_16112

theorem node_18040 : Outcome ⟨4, 15, 12, 10⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 4⟩) (by decide) node_16112

theorem node_18041 : Outcome ⟨4, 16, 11, 2⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 4⟩) (by decide) node_16125

theorem node_18042 : Outcome ⟨4, 16, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 4⟩) (by decide) node_16125

theorem node_18043 : Outcome ⟨4, 16, 11, 6⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 4⟩) (by decide) node_16125

theorem node_18044 : Outcome ⟨4, 17, 10, 6⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 4⟩) (by decide) node_16134

theorem node_18045 : Outcome ⟨4, 17, 10, 10⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 4⟩) (by decide) node_16134

theorem node_18046 : Outcome ⟨4, 17, 10, 12⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 22⟩) (by decide) node_7302

theorem node_18047 : Outcome ⟨4, 18, 9, 2⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 4⟩) (by decide) node_16125

theorem node_18048 : Outcome ⟨4, 18, 9, 4⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 4⟩) (by decide) node_16125

theorem node_18049 : Outcome ⟨4, 19, 8, 2⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 4⟩) (by decide) node_16015

theorem node_18050 : Outcome ⟨4, 19, 8, 12⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 4⟩) (by decide) node_16015

theorem node_18051 : Outcome ⟨4, 20, 7, 2⟩ true :=
  Outcome.win (q := ⟨4, 20, 5, 4⟩) (by decide) node_16145

theorem node_18052 : Outcome ⟨4, 20, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 8⟩) (by decide) node_13993

theorem node_18053 : Outcome ⟨4, 20, 7, 8⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 8⟩) (by decide) node_13993

theorem node_18054 : Outcome ⟨4, 20, 7, 12⟩ true :=
  Outcome.win (q := ⟨0, 20, 7, 8⟩) (by decide) node_13993

theorem node_18055 : Outcome ⟨5, 6, 20, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 20, 4⟩) (by decide) node_16151

theorem node_18056 : Outcome ⟨5, 6, 20, 6⟩ true :=
  Outcome.win (q := ⟨5, 4, 20, 4⟩) (by decide) node_16151

theorem node_18057 : Outcome ⟨5, 7, 19, 2⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 4⟩) (by decide) node_16161

theorem node_18058 : Outcome ⟨5, 7, 19, 6⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 4⟩) (by decide) node_16161

theorem node_18059 : Outcome ⟨5, 8, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 18, 2⟩, ⟨3, 8, 18, 4⟩, ⟨5, 7, 18, 2⟩, ⟨5, 6, 18, 4⟩, ⟨5, 8, 17, 2⟩, ⟨5, 8, 16, 4⟩]
  exact AllWinning.cons node_17131 (AllWinning.cons node_16027 (AllWinning.cons node_17175 (AllWinning.cons node_16157 (AllWinning.cons node_17179 (AllWinning.cons node_16166 (AllWinning.nil))))))

theorem node_18060 : Outcome ⟨5, 8, 18, 6⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 6⟩) (by decide) node_15164

theorem node_18061 : Outcome ⟨5, 8, 18, 8⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 6⟩) (by decide) node_15164

theorem node_18062 : Outcome ⟨5, 9, 17, 2⟩ true :=
  Outcome.win (q := ⟨3, 9, 17, 4⟩) (by decide) node_16031

theorem node_18063 : Outcome ⟨5, 9, 17, 4⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 6⟩) (by decide) node_15174

theorem node_18064 : Outcome ⟨5, 9, 17, 6⟩ true :=
  Outcome.win (q := ⟨5, 9, 14, 6⟩) (by decide) node_15174

theorem node_18065 : Outcome ⟨5, 10, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 10, 16, 2⟩, ⟨3, 10, 16, 4⟩, ⟨5, 9, 16, 2⟩, ⟨5, 8, 16, 4⟩, ⟨5, 10, 15, 2⟩, ⟨5, 10, 14, 4⟩]
  exact AllWinning.cons node_17136 (AllWinning.cons node_16034 (AllWinning.cons node_17181 (AllWinning.cons node_16166 (AllWinning.cons node_17183 (AllWinning.cons node_16169 (AllWinning.nil))))))

theorem node_18066 : Outcome ⟨5, 10, 16, 6⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 8⟩) (by decide) node_14230

theorem node_18067 : Outcome ⟨5, 10, 16, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 8⟩) (by decide) node_14230

theorem node_18068 : Outcome ⟨5, 11, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 11, 15, 2⟩) (by decide) node_17139

theorem node_18069 : Outcome ⟨5, 11, 15, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 6⟩) (by decide) node_15164

theorem node_18070 : Outcome ⟨5, 11, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 6⟩) (by decide) node_15164

theorem node_18071 : Outcome ⟨5, 12, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 12, 14, 2⟩, ⟨3, 12, 14, 4⟩, ⟨5, 11, 14, 2⟩, ⟨5, 10, 14, 4⟩, ⟨5, 12, 13, 2⟩, ⟨5, 12, 12, 4⟩]
  exact AllWinning.cons node_17143 (AllWinning.cons node_16041 (AllWinning.cons node_17185 (AllWinning.cons node_16169 (AllWinning.cons node_17187 (AllWinning.cons node_16173 (AllWinning.nil))))))

theorem node_18072 : Outcome ⟨5, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 8⟩) (by decide) node_14238

theorem node_18073 : Outcome ⟨5, 12, 14, 6⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 8⟩) (by decide) node_14238

theorem node_18074 : Outcome ⟨5, 12, 14, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 8⟩) (by decide) node_14238

theorem node_18075 : Outcome ⟨5, 13, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 13, 2⟩, ⟨3, 13, 13, 4⟩, ⟨5, 12, 13, 2⟩, ⟨5, 11, 13, 4⟩, ⟨5, 13, 12, 2⟩, ⟨5, 13, 11, 4⟩]
  exact AllWinning.cons node_17147 (AllWinning.cons node_16045 (AllWinning.cons node_17187 (AllWinning.cons node_16172 (AllWinning.cons node_17190 (AllWinning.cons node_16175 (AllWinning.nil))))))

theorem node_18076 : Outcome ⟨5, 13, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 13, 13, 2⟩, ⟨3, 13, 13, 4⟩, ⟨2, 13, 13, 6⟩, ⟨1, 13, 13, 8⟩, ⟨5, 12, 13, 2⟩, ⟨5, 11, 13, 4⟩, ⟨5, 10, 13, 6⟩, ⟨5, 9, 13, 8⟩, ⟨5, 13, 12, 2⟩, ⟨5, 13, 11, 4⟩, ⟨5, 13, 10, 6⟩, ⟨5, 13, 9, 8⟩]
  exact AllWinning.cons node_17147 (AllWinning.cons node_16045 (AllWinning.cons node_15036 (AllWinning.cons node_14024 (AllWinning.cons node_17187 (AllWinning.cons node_16172 (AllWinning.cons node_15178 (AllWinning.cons node_14226 (AllWinning.cons node_17190 (AllWinning.cons node_16175 (AllWinning.cons node_15186 (AllWinning.cons node_14243 (AllWinning.nil))))))))))))

theorem node_18077 : Outcome ⟨5, 13, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 10⟩) (by decide) node_13005

theorem node_18078 : Outcome ⟨5, 13, 13, 16⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 10⟩) (by decide) node_13005

theorem node_18079 : Outcome ⟨5, 14, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 12, 2⟩, ⟨3, 14, 12, 4⟩, ⟨5, 13, 12, 2⟩, ⟨5, 12, 12, 4⟩, ⟨5, 14, 11, 2⟩, ⟨5, 14, 10, 4⟩]
  exact AllWinning.cons node_17151 (AllWinning.cons node_16050 (AllWinning.cons node_17190 (AllWinning.cons node_16173 (AllWinning.cons node_17193 (AllWinning.cons node_16176 (AllWinning.nil))))))

theorem node_18080 : Outcome ⟨5, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 8⟩) (by decide) node_14230

theorem node_18081 : Outcome ⟨5, 14, 12, 6⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 8⟩) (by decide) node_14230

theorem node_18082 : Outcome ⟨5, 14, 12, 8⟩ true :=
  Outcome.win (q := ⟨5, 10, 12, 8⟩) (by decide) node_14230

theorem node_18083 : Outcome ⟨5, 15, 11, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 11, 2⟩) (by decide) node_17155

theorem node_18084 : Outcome ⟨5, 15, 11, 4⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 6⟩) (by decide) node_15196

theorem node_18085 : Outcome ⟨5, 15, 11, 8⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 6⟩) (by decide) node_15196

theorem node_18086 : Outcome ⟨5, 16, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 16, 10, 2⟩, ⟨3, 16, 10, 4⟩, ⟨5, 15, 10, 2⟩, ⟨5, 14, 10, 4⟩, ⟨5, 16, 9, 2⟩, ⟨5, 16, 8, 4⟩]
  exact AllWinning.cons node_17159 (AllWinning.cons node_16057 (AllWinning.cons node_17195 (AllWinning.cons node_16176 (AllWinning.cons node_17197 (AllWinning.cons node_16181 (AllWinning.nil))))))

theorem node_18087 : Outcome ⟨5, 16, 10, 6⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 8⟩) (by decide) node_14238

theorem node_18088 : Outcome ⟨5, 16, 10, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 10, 8⟩) (by decide) node_14238

theorem node_18089 : Outcome ⟨5, 17, 9, 2⟩ true :=
  Outcome.win (q := ⟨3, 17, 9, 4⟩) (by decide) node_16060

theorem node_18090 : Outcome ⟨5, 17, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 6⟩) (by decide) node_15191

theorem node_18091 : Outcome ⟨5, 17, 9, 6⟩ true :=
  Outcome.win (q := ⟨5, 14, 9, 6⟩) (by decide) node_15191

theorem node_18092 : Outcome ⟨5, 18, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 18, 8, 2⟩, ⟨3, 18, 8, 4⟩, ⟨5, 17, 8, 2⟩, ⟨5, 16, 8, 4⟩, ⟨5, 18, 7, 2⟩, ⟨5, 18, 6, 4⟩]
  exact AllWinning.cons node_17164 (AllWinning.cons node_16063 (AllWinning.cons node_17199 (AllWinning.cons node_16181 (AllWinning.cons node_17201 (AllWinning.cons node_16188 (AllWinning.nil))))))

theorem node_18093 : Outcome ⟨5, 18, 8, 6⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 6⟩) (by decide) node_15196

theorem node_18094 : Outcome ⟨5, 18, 8, 8⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 6⟩) (by decide) node_15196

end RQ9F1
