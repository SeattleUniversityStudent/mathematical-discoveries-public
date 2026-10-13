import Chunk90
set_option autoImplicit false
namespace RQ9F1

theorem node_19694 : Outcome ⟨0, 14, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 19, 2⟩, ⟨0, 12, 19, 4⟩, ⟨0, 11, 19, 6⟩, ⟨0, 10, 19, 8⟩, ⟨0, 14, 18, 2⟩, ⟨0, 14, 17, 4⟩, ⟨0, 14, 16, 6⟩, ⟨0, 14, 15, 8⟩]
  exact AllWinning.cons node_18803 (AllWinning.cons node_17883 (AllWinning.cons node_16976 (AllWinning.cons node_15905 (AllWinning.cons node_18807 (AllWinning.cons node_17889 (AllWinning.cons node_16985 (AllWinning.cons node_15919 (AllWinning.nil))))))))

theorem node_19695 : Outcome ⟨0, 14, 19, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 10⟩) (by decide) node_14941

theorem node_19696 : Outcome ⟨0, 14, 19, 10⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 10⟩) (by decide) node_14941

theorem node_19697 : Outcome ⟨0, 15, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 6⟩) (by decide) node_16990

theorem node_19698 : Outcome ⟨0, 15, 18, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 6⟩) (by decide) node_16990

theorem node_19699 : Outcome ⟨0, 16, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 2⟩) (by decide) node_18812

theorem node_19700 : Outcome ⟨0, 17, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 2⟩) (by decide) node_18812

theorem node_19701 : Outcome ⟨0, 18, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 6⟩) (by decide) node_16990

theorem node_19702 : Outcome ⟨0, 18, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 6⟩) (by decide) node_16990

theorem node_19703 : Outcome ⟨0, 19, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 14, 2⟩, ⟨0, 17, 14, 4⟩, ⟨0, 19, 13, 2⟩, ⟨0, 19, 12, 4⟩]
  exact AllWinning.cons node_18823 (AllWinning.cons node_17895 (AllWinning.cons node_18825 (AllWinning.cons node_17902 (AllWinning.nil))))

theorem node_19704 : Outcome ⟨0, 19, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 14, 2⟩, ⟨0, 17, 14, 4⟩, ⟨0, 16, 14, 6⟩, ⟨0, 15, 14, 8⟩, ⟨0, 19, 13, 2⟩, ⟨0, 19, 12, 4⟩, ⟨0, 19, 11, 6⟩, ⟨0, 19, 10, 8⟩]
  exact AllWinning.cons node_18823 (AllWinning.cons node_17895 (AllWinning.cons node_16995 (AllWinning.cons node_15922 (AllWinning.cons node_18825 (AllWinning.cons node_17902 (AllWinning.cons node_17006 (AllWinning.cons node_15935 (AllWinning.nil))))))))

theorem node_19705 : Outcome ⟨0, 19, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 10⟩) (by decide) node_14941

theorem node_19706 : Outcome ⟨0, 19, 14, 10⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 10⟩) (by decide) node_14941

theorem node_19707 : Outcome ⟨0, 20, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 13, 4⟩) (by decide) node_17898

theorem node_19708 : Outcome ⟨0, 20, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 13, 4⟩) (by decide) node_17898

theorem node_19709 : Outcome ⟨0, 20, 13, 8⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 14⟩) (by decide) node_13007

theorem node_19710 : Outcome ⟨0, 20, 13, 14⟩ true :=
  Outcome.win (q := ⟨0, 13, 13, 14⟩) (by decide) node_13007

theorem node_19711 : Outcome ⟨1, 12, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 10, 20, 4⟩) (by decide) node_17908

theorem node_19712 : Outcome ⟨1, 12, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 20, 4⟩) (by decide) node_17908

theorem node_19713 : Outcome ⟨1, 12, 20, 8⟩ true :=
  Outcome.win (q := ⟨1, 10, 20, 4⟩) (by decide) node_17908

theorem node_19714 : Outcome ⟨1, 13, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19715 : Outcome ⟨1, 13, 19, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19716 : Outcome ⟨1, 13, 19, 10⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19717 : Outcome ⟨1, 13, 19, 14⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19718 : Outcome ⟨1, 14, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 18, 2⟩, ⟨1, 13, 18, 2⟩, ⟨1, 12, 18, 4⟩, ⟨1, 14, 17, 2⟩, ⟨1, 14, 16, 4⟩]
  exact AllWinning.cons node_18807 (AllWinning.cons node_18839 (AllWinning.cons node_17914 (AllWinning.cons node_18842 (AllWinning.cons node_17924 (AllWinning.nil)))))

theorem node_19719 : Outcome ⟨1, 14, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 18, 2⟩, ⟨1, 13, 18, 2⟩, ⟨1, 12, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨1, 10, 18, 8⟩, ⟨1, 14, 17, 2⟩, ⟨1, 14, 16, 4⟩, ⟨1, 14, 15, 6⟩, ⟨1, 14, 14, 8⟩]
  exact AllWinning.cons node_18807 (AllWinning.cons node_18839 (AllWinning.cons node_17914 (AllWinning.cons node_17019 (AllWinning.cons node_15948 (AllWinning.cons node_18842 (AllWinning.cons node_17924 (AllWinning.cons node_17027 (AllWinning.cons node_15962 (AllWinning.nil)))))))))

theorem node_19720 : Outcome ⟨1, 14, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 14, 18, 2⟩, ⟨1, 13, 18, 2⟩, ⟨1, 12, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨1, 10, 18, 8⟩, ⟨1, 9, 18, 10⟩, ⟨1, 8, 18, 12⟩, ⟨1, 14, 17, 2⟩, ⟨1, 14, 16, 4⟩, ⟨1, 14, 15, 6⟩, ⟨1, 14, 14, 8⟩, ⟨1, 14, 13, 10⟩, ⟨1, 14, 12, 12⟩]
  exact AllWinning.cons node_18807 (AllWinning.cons node_18839 (AllWinning.cons node_17914 (AllWinning.cons node_17019 (AllWinning.cons node_15948 (AllWinning.cons node_14970 (AllWinning.cons node_14003 (AllWinning.cons node_18842 (AllWinning.cons node_17924 (AllWinning.cons node_17027 (AllWinning.cons node_15962 (AllWinning.cons node_14989 (AllWinning.cons node_14029 (AllWinning.nil)))))))))))))

theorem node_19721 : Outcome ⟨1, 14, 18, 10⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 16⟩) (by decide) node_12059

theorem node_19722 : Outcome ⟨1, 15, 17, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19723 : Outcome ⟨1, 15, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19724 : Outcome ⟨1, 15, 17, 6⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19725 : Outcome ⟨1, 16, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 16, 16, 2⟩) (by decide) node_18812

theorem node_19726 : Outcome ⟨1, 17, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19727 : Outcome ⟨1, 17, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19728 : Outcome ⟨1, 17, 15, 6⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19729 : Outcome ⟨1, 18, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 14, 2⟩, ⟨1, 17, 14, 2⟩, ⟨1, 16, 14, 4⟩, ⟨1, 18, 13, 2⟩, ⟨1, 18, 12, 4⟩]
  exact AllWinning.cons node_18823 (AllWinning.cons node_18858 (AllWinning.cons node_17931 (AllWinning.cons node_18860 (AllWinning.cons node_17941 (AllWinning.nil)))))

theorem node_19730 : Outcome ⟨1, 18, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 14, 2⟩, ⟨1, 17, 14, 2⟩, ⟨1, 16, 14, 4⟩, ⟨1, 15, 14, 6⟩, ⟨1, 14, 14, 8⟩, ⟨1, 18, 13, 2⟩, ⟨1, 18, 12, 4⟩, ⟨1, 18, 11, 6⟩, ⟨1, 18, 10, 8⟩]
  exact AllWinning.cons node_18823 (AllWinning.cons node_18858 (AllWinning.cons node_17931 (AllWinning.cons node_17031 (AllWinning.cons node_15962 (AllWinning.cons node_18860 (AllWinning.cons node_17941 (AllWinning.cons node_17037 (AllWinning.cons node_15974 (AllWinning.nil)))))))))

theorem node_19731 : Outcome ⟨1, 18, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 14, 2⟩, ⟨1, 17, 14, 2⟩, ⟨1, 16, 14, 4⟩, ⟨1, 15, 14, 6⟩, ⟨1, 14, 14, 8⟩, ⟨1, 13, 14, 10⟩, ⟨1, 12, 14, 12⟩, ⟨1, 18, 13, 2⟩, ⟨1, 18, 12, 4⟩, ⟨1, 18, 11, 6⟩, ⟨1, 18, 10, 8⟩, ⟨1, 18, 9, 10⟩, ⟨1, 18, 8, 12⟩]
  exact AllWinning.cons node_18823 (AllWinning.cons node_18858 (AllWinning.cons node_17931 (AllWinning.cons node_17031 (AllWinning.cons node_15962 (AllWinning.cons node_14985 (AllWinning.cons node_14021 (AllWinning.cons node_18860 (AllWinning.cons node_17941 (AllWinning.cons node_17037 (AllWinning.cons node_15974 (AllWinning.cons node_15001 (AllWinning.cons node_14044 (AllWinning.nil)))))))))))))

theorem node_19732 : Outcome ⟨1, 18, 14, 10⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 16⟩) (by decide) node_12039

theorem node_19733 : Outcome ⟨1, 19, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19734 : Outcome ⟨1, 19, 13, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19735 : Outcome ⟨1, 19, 13, 10⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19736 : Outcome ⟨1, 19, 13, 14⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19737 : Outcome ⟨1, 20, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 20, 10, 4⟩) (by decide) node_17948

theorem node_19738 : Outcome ⟨1, 20, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 20, 10, 4⟩) (by decide) node_17948

theorem node_19739 : Outcome ⟨1, 20, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 20, 10, 4⟩) (by decide) node_17948

theorem node_19740 : Outcome ⟨2, 11, 20, 6⟩ true :=
  Outcome.win (q := ⟨2, 11, 17, 6⟩) (by decide) node_17055

theorem node_19741 : Outcome ⟨2, 12, 19, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 19, 2⟩) (by decide) node_18833

theorem node_19742 : Outcome ⟨2, 12, 19, 10⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 10⟩) (by decide) node_15029

theorem node_19743 : Outcome ⟨2, 12, 19, 20⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 10⟩) (by decide) node_15029

theorem node_19744 : Outcome ⟨2, 13, 18, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 18, 4⟩) (by decide) node_17886

theorem node_19745 : Outcome ⟨2, 13, 18, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 12⟩) (by decide) node_14061

theorem node_19746 : Outcome ⟨2, 13, 18, 10⟩ true :=
  Outcome.win (q := ⟨2, 7, 18, 12⟩) (by decide) node_14061

theorem node_19747 : Outcome ⟨2, 14, 17, 2⟩ true :=
  Outcome.win (q := ⟨2, 14, 16, 2⟩) (by decide) node_18879

theorem node_19748 : Outcome ⟨2, 14, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 10⟩) (by decide) node_15042

theorem node_19749 : Outcome ⟨2, 14, 17, 10⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 10⟩) (by decide) node_15042

theorem node_19750 : Outcome ⟨2, 15, 16, 2⟩ true :=
  Outcome.win (q := ⟨1, 15, 16, 2⟩) (by decide) node_18844

theorem node_19751 : Outcome ⟨2, 15, 16, 6⟩ true :=
  Outcome.win (q := ⟨2, 10, 16, 10⟩) (by decide) node_15022

theorem node_19752 : Outcome ⟨2, 16, 15, 2⟩ true :=
  Outcome.win (q := ⟨1, 16, 15, 2⟩) (by decide) node_18851

theorem node_19753 : Outcome ⟨2, 16, 15, 6⟩ true :=
  Outcome.win (q := ⟨2, 16, 10, 10⟩) (by decide) node_15052

theorem node_19754 : Outcome ⟨2, 17, 14, 2⟩ true :=
  Outcome.win (q := ⟨2, 16, 14, 2⟩) (by decide) node_18887

theorem node_19755 : Outcome ⟨2, 17, 14, 6⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 10⟩) (by decide) node_15029

theorem node_19756 : Outcome ⟨2, 17, 14, 10⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 10⟩) (by decide) node_15029

theorem node_19757 : Outcome ⟨2, 18, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 18, 13, 4⟩) (by decide) node_17898

theorem node_19758 : Outcome ⟨2, 18, 13, 6⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 12⟩) (by decide) node_14091

theorem node_19759 : Outcome ⟨2, 18, 13, 10⟩ true :=
  Outcome.win (q := ⟨2, 18, 7, 12⟩) (by decide) node_14091

theorem node_19760 : Outcome ⟨2, 19, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 19, 12, 2⟩) (by decide) node_18863

theorem node_19761 : Outcome ⟨2, 19, 12, 10⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 10⟩) (by decide) node_15042

theorem node_19762 : Outcome ⟨2, 19, 12, 20⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 10⟩) (by decide) node_15042

theorem node_19763 : Outcome ⟨2, 20, 11, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 11, 6⟩) (by decide) node_17077

theorem node_19764 : Outcome ⟨3, 10, 20, 2⟩ true :=
  Outcome.win (q := ⟨1, 10, 20, 4⟩) (by decide) node_17908

theorem node_19765 : Outcome ⟨3, 10, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 20, 4⟩) (by decide) node_17908

theorem node_19766 : Outcome ⟨3, 11, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 19, 2⟩, ⟨1, 11, 19, 4⟩, ⟨3, 10, 19, 2⟩, ⟨3, 9, 19, 4⟩, ⟨3, 11, 18, 2⟩, ⟨3, 11, 17, 4⟩]
  exact AllWinning.cons node_18872 (AllWinning.cons node_17911 (AllWinning.cons node_18903 (AllWinning.cons node_17976 (AllWinning.cons node_18905 (AllWinning.cons node_17981 (AllWinning.nil))))))

theorem node_19767 : Outcome ⟨3, 11, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 19, 2⟩, ⟨1, 11, 19, 4⟩, ⟨0, 11, 19, 6⟩, ⟨3, 10, 19, 2⟩, ⟨3, 9, 19, 4⟩, ⟨3, 8, 19, 6⟩, ⟨3, 7, 19, 8⟩, ⟨3, 11, 18, 2⟩, ⟨3, 11, 17, 4⟩, ⟨3, 11, 16, 6⟩, ⟨3, 11, 15, 8⟩]
  exact AllWinning.cons node_18872 (AllWinning.cons node_17911 (AllWinning.cons node_16976 (AllWinning.cons node_18903 (AllWinning.cons node_17976 (AllWinning.cons node_17091 (AllWinning.cons node_16026 (AllWinning.cons node_18905 (AllWinning.cons node_17981 (AllWinning.cons node_17098 (AllWinning.cons node_16038 (AllWinning.nil)))))))))))

theorem node_19768 : Outcome ⟨3, 11, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 19, 2⟩, ⟨1, 11, 19, 4⟩, ⟨0, 11, 19, 6⟩, ⟨3, 10, 19, 2⟩, ⟨3, 9, 19, 4⟩, ⟨3, 8, 19, 6⟩, ⟨3, 7, 19, 8⟩, ⟨3, 6, 19, 10⟩, ⟨3, 5, 19, 12⟩, ⟨3, 4, 19, 14⟩, ⟨3, 3, 19, 16⟩, ⟨3, 11, 18, 2⟩, ⟨3, 11, 17, 4⟩, ⟨3, 11, 16, 6⟩, ⟨3, 11, 15, 8⟩, ⟨3, 11, 14, 10⟩, ⟨3, 11, 13, 12⟩, ⟨3, 11, 12, 14⟩, ⟨3, 11, 11, 16⟩]
  exact AllWinning.cons node_18872 (AllWinning.cons node_17911 (AllWinning.cons node_16976 (AllWinning.cons node_18903 (AllWinning.cons node_17976 (AllWinning.cons node_17091 (AllWinning.cons node_16026 (AllWinning.cons node_15069 (AllWinning.cons node_14102 (AllWinning.cons node_13132 (AllWinning.cons node_12157 (AllWinning.cons node_18905 (AllWinning.cons node_17981 (AllWinning.cons node_17098 (AllWinning.cons node_16038 (AllWinning.cons node_15083 (AllWinning.cons node_14127 (AllWinning.cons node_13163 (AllWinning.cons node_12187 (AllWinning.nil)))))))))))))))))))

theorem node_19769 : Outcome ⟨3, 11, 19, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 11, 19, 2⟩, ⟨1, 11, 19, 4⟩, ⟨0, 11, 19, 6⟩, ⟨3, 10, 19, 2⟩, ⟨3, 9, 19, 4⟩, ⟨3, 8, 19, 6⟩, ⟨3, 7, 19, 8⟩, ⟨3, 6, 19, 10⟩, ⟨3, 5, 19, 12⟩, ⟨3, 4, 19, 14⟩, ⟨3, 3, 19, 16⟩, ⟨3, 2, 19, 18⟩, ⟨3, 1, 19, 20⟩, ⟨3, 0, 19, 22⟩, ⟨3, 11, 18, 2⟩, ⟨3, 11, 17, 4⟩, ⟨3, 11, 16, 6⟩, ⟨3, 11, 15, 8⟩, ⟨3, 11, 14, 10⟩, ⟨3, 11, 13, 12⟩, ⟨3, 11, 12, 14⟩, ⟨3, 11, 11, 16⟩, ⟨3, 11, 10, 18⟩, ⟨3, 11, 9, 20⟩, ⟨3, 11, 8, 22⟩, ⟨3, 11, 7, 24⟩]
  exact AllWinning.cons node_18872 (AllWinning.cons node_17911 (AllWinning.cons node_16976 (AllWinning.cons node_18903 (AllWinning.cons node_17976 (AllWinning.cons node_17091 (AllWinning.cons node_16026 (AllWinning.cons node_15069 (AllWinning.cons node_14102 (AllWinning.cons node_13132 (AllWinning.cons node_12157 (AllWinning.cons node_11153 (AllWinning.cons node_10095 (AllWinning.cons node_9126 (AllWinning.cons node_18905 (AllWinning.cons node_17981 (AllWinning.cons node_17098 (AllWinning.cons node_16038 (AllWinning.cons node_15083 (AllWinning.cons node_14127 (AllWinning.cons node_13163 (AllWinning.cons node_12187 (AllWinning.cons node_11192 (AllWinning.cons node_10132 (AllWinning.cons node_9168 (AllWinning.cons node_8193 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19770 : Outcome ⟨3, 12, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 4⟩) (by decide) node_17978

theorem node_19771 : Outcome ⟨3, 12, 18, 6⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 4⟩) (by decide) node_17978

theorem node_19772 : Outcome ⟨3, 13, 17, 2⟩ true :=
  Outcome.win (q := ⟨1, 13, 17, 4⟩) (by decide) node_17918

theorem node_19773 : Outcome ⟨3, 14, 16, 2⟩ true :=
  Outcome.win (q := ⟨2, 14, 16, 2⟩) (by decide) node_18879

theorem node_19774 : Outcome ⟨3, 14, 16, 14⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 12⟩) (by decide) node_14113

theorem node_19775 : Outcome ⟨3, 15, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 15, 15, 2⟩, ⟨1, 15, 15, 4⟩, ⟨3, 14, 15, 2⟩, ⟨3, 13, 15, 4⟩, ⟨3, 15, 14, 2⟩, ⟨3, 15, 13, 4⟩]
  exact AllWinning.cons node_18883 (AllWinning.cons node_17928 (AllWinning.cons node_18911 (AllWinning.cons node_17988 (AllWinning.cons node_18915 (AllWinning.cons node_17997 (AllWinning.nil))))))

theorem node_19776 : Outcome ⟨3, 15, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 6⟩) (by decide) node_16990

theorem node_19777 : Outcome ⟨3, 15, 15, 6⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 6⟩) (by decide) node_16990

theorem node_19778 : Outcome ⟨3, 15, 15, 14⟩ true :=
  Outcome.win (q := ⟨0, 15, 15, 6⟩) (by decide) node_16990

theorem node_19779 : Outcome ⟨3, 16, 14, 2⟩ true :=
  Outcome.win (q := ⟨2, 16, 14, 2⟩) (by decide) node_18887

theorem node_19780 : Outcome ⟨3, 16, 14, 14⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 12⟩) (by decide) node_14146

theorem node_19781 : Outcome ⟨3, 17, 13, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 13, 4⟩) (by decide) node_17935

theorem node_19782 : Outcome ⟨3, 18, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 4⟩) (by decide) node_18007

theorem node_19783 : Outcome ⟨3, 18, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 4⟩) (by decide) node_18007

theorem node_19784 : Outcome ⟨3, 19, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 19, 11, 2⟩, ⟨1, 19, 11, 4⟩, ⟨3, 18, 11, 2⟩, ⟨3, 17, 11, 4⟩, ⟨3, 19, 10, 2⟩, ⟨3, 19, 9, 4⟩]
  exact AllWinning.cons node_18895 (AllWinning.cons node_17945 (AllWinning.cons node_18923 (AllWinning.cons node_18003 (AllWinning.cons node_18925 (AllWinning.cons node_18011 (AllWinning.nil))))))

theorem node_19785 : Outcome ⟨3, 19, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 19, 11, 2⟩, ⟨1, 19, 11, 4⟩, ⟨0, 19, 11, 6⟩, ⟨3, 18, 11, 2⟩, ⟨3, 17, 11, 4⟩, ⟨3, 16, 11, 6⟩, ⟨3, 15, 11, 8⟩, ⟨3, 19, 10, 2⟩, ⟨3, 19, 9, 4⟩, ⟨3, 19, 8, 6⟩, ⟨3, 19, 7, 8⟩]
  exact AllWinning.cons node_18895 (AllWinning.cons node_17945 (AllWinning.cons node_17006 (AllWinning.cons node_18923 (AllWinning.cons node_18003 (AllWinning.cons node_17117 (AllWinning.cons node_16055 (AllWinning.cons node_18925 (AllWinning.cons node_18011 (AllWinning.cons node_17124 (AllWinning.cons node_16068 (AllWinning.nil)))))))))))

theorem node_19786 : Outcome ⟨3, 19, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 19, 11, 2⟩, ⟨1, 19, 11, 4⟩, ⟨0, 19, 11, 6⟩, ⟨3, 18, 11, 2⟩, ⟨3, 17, 11, 4⟩, ⟨3, 16, 11, 6⟩, ⟨3, 15, 11, 8⟩, ⟨3, 14, 11, 10⟩, ⟨3, 13, 11, 12⟩, ⟨3, 12, 11, 14⟩, ⟨3, 11, 11, 16⟩, ⟨3, 19, 10, 2⟩, ⟨3, 19, 9, 4⟩, ⟨3, 19, 8, 6⟩, ⟨3, 19, 7, 8⟩, ⟨3, 19, 6, 10⟩, ⟨3, 19, 5, 12⟩, ⟨3, 19, 4, 14⟩, ⟨3, 19, 3, 16⟩]
  exact AllWinning.cons node_18895 (AllWinning.cons node_17945 (AllWinning.cons node_17006 (AllWinning.cons node_18923 (AllWinning.cons node_18003 (AllWinning.cons node_17117 (AllWinning.cons node_16055 (AllWinning.cons node_15095 (AllWinning.cons node_14134 (AllWinning.cons node_13168 (AllWinning.cons node_12187 (AllWinning.cons node_18925 (AllWinning.cons node_18011 (AllWinning.cons node_17124 (AllWinning.cons node_16068 (AllWinning.cons node_15110 (AllWinning.cons node_14159 (AllWinning.cons node_13196 (AllWinning.cons node_12215 (AllWinning.nil)))))))))))))))))))

theorem node_19787 : Outcome ⟨3, 19, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 19, 11, 2⟩, ⟨1, 19, 11, 4⟩, ⟨0, 19, 11, 6⟩, ⟨3, 18, 11, 2⟩, ⟨3, 17, 11, 4⟩, ⟨3, 16, 11, 6⟩, ⟨3, 15, 11, 8⟩, ⟨3, 14, 11, 10⟩, ⟨3, 13, 11, 12⟩, ⟨3, 12, 11, 14⟩, ⟨3, 11, 11, 16⟩, ⟨3, 10, 11, 18⟩, ⟨3, 9, 11, 20⟩, ⟨3, 8, 11, 22⟩, ⟨3, 7, 11, 24⟩, ⟨3, 19, 10, 2⟩, ⟨3, 19, 9, 4⟩, ⟨3, 19, 8, 6⟩, ⟨3, 19, 7, 8⟩, ⟨3, 19, 6, 10⟩, ⟨3, 19, 5, 12⟩, ⟨3, 19, 4, 14⟩, ⟨3, 19, 3, 16⟩, ⟨3, 19, 2, 18⟩, ⟨3, 19, 1, 20⟩, ⟨3, 19, 0, 22⟩]
  exact AllWinning.cons node_18895 (AllWinning.cons node_17945 (AllWinning.cons node_17006 (AllWinning.cons node_18923 (AllWinning.cons node_18003 (AllWinning.cons node_17117 (AllWinning.cons node_16055 (AllWinning.cons node_15095 (AllWinning.cons node_14134 (AllWinning.cons node_13168 (AllWinning.cons node_12187 (AllWinning.cons node_11187 (AllWinning.cons node_10125 (AllWinning.cons node_9155 (AllWinning.cons node_8174 (AllWinning.cons node_18925 (AllWinning.cons node_18011 (AllWinning.cons node_17124 (AllWinning.cons node_16068 (AllWinning.cons node_15110 (AllWinning.cons node_14159 (AllWinning.cons node_13196 (AllWinning.cons node_12215 (AllWinning.cons node_11224 (AllWinning.cons node_10165 (AllWinning.cons node_9194 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19788 : Outcome ⟨3, 20, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 20, 10, 4⟩) (by decide) node_17948

theorem node_19789 : Outcome ⟨3, 20, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 20, 10, 4⟩) (by decide) node_17948

theorem node_19790 : Outcome ⟨4, 9, 20, 2⟩ true :=
  Outcome.win (q := ⟨2, 9, 20, 4⟩) (by decide) node_17951

theorem node_19791 : Outcome ⟨4, 9, 20, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 8⟩) (by decide) node_16074

theorem node_19792 : Outcome ⟨4, 9, 20, 10⟩ true :=
  Outcome.win (q := ⟨4, 5, 20, 8⟩) (by decide) node_16074

theorem node_19793 : Outcome ⟨4, 10, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 9, 19, 2⟩) (by decide) node_18933

theorem node_19794 : Outcome ⟨4, 10, 19, 8⟩ true :=
  Outcome.win (q := ⟨4, 9, 19, 2⟩) (by decide) node_18933

theorem node_19795 : Outcome ⟨4, 11, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 18, 2⟩, ⟨2, 11, 18, 4⟩, ⟨4, 10, 18, 2⟩, ⟨4, 9, 18, 4⟩, ⟨4, 11, 17, 2⟩, ⟨4, 11, 16, 4⟩]
  exact AllWinning.cons node_18905 (AllWinning.cons node_17955 (AllWinning.cons node_18935 (AllWinning.cons node_18020 (AllWinning.cons node_18937 (AllWinning.cons node_18025 (AllWinning.nil))))))

theorem node_19796 : Outcome ⟨4, 11, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 18, 2⟩, ⟨2, 11, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨0, 11, 18, 8⟩, ⟨4, 10, 18, 2⟩, ⟨4, 9, 18, 4⟩, ⟨4, 8, 18, 6⟩, ⟨4, 7, 18, 8⟩, ⟨4, 11, 17, 2⟩, ⟨4, 11, 16, 4⟩, ⟨4, 11, 15, 6⟩, ⟨4, 11, 14, 8⟩]
  exact AllWinning.cons node_18905 (AllWinning.cons node_17955 (AllWinning.cons node_17019 (AllWinning.cons node_15910 (AllWinning.cons node_18935 (AllWinning.cons node_18020 (AllWinning.cons node_17132 (AllWinning.cons node_16081 (AllWinning.cons node_18937 (AllWinning.cons node_18025 (AllWinning.cons node_17141 (AllWinning.cons node_16099 (AllWinning.nil))))))))))))

theorem node_19797 : Outcome ⟨4, 11, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 18, 2⟩, ⟨2, 11, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨0, 11, 18, 8⟩, ⟨4, 10, 18, 2⟩, ⟨4, 9, 18, 4⟩, ⟨4, 8, 18, 6⟩, ⟨4, 7, 18, 8⟩, ⟨4, 6, 18, 10⟩, ⟨4, 5, 18, 12⟩, ⟨4, 11, 17, 2⟩, ⟨4, 11, 16, 4⟩, ⟨4, 11, 15, 6⟩, ⟨4, 11, 14, 8⟩, ⟨4, 11, 13, 10⟩, ⟨4, 11, 12, 12⟩]
  exact AllWinning.cons node_18905 (AllWinning.cons node_17955 (AllWinning.cons node_17019 (AllWinning.cons node_15910 (AllWinning.cons node_18935 (AllWinning.cons node_18020 (AllWinning.cons node_17132 (AllWinning.cons node_16081 (AllWinning.cons node_15118 (AllWinning.cons node_14168 (AllWinning.cons node_18937 (AllWinning.cons node_18025 (AllWinning.cons node_17141 (AllWinning.cons node_16099 (AllWinning.cons node_15130 (AllWinning.cons node_14183 (AllWinning.nil))))))))))))))))

theorem node_19798 : Outcome ⟨4, 11, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 18, 2⟩, ⟨2, 11, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨0, 11, 18, 8⟩, ⟨4, 10, 18, 2⟩, ⟨4, 9, 18, 4⟩, ⟨4, 8, 18, 6⟩, ⟨4, 7, 18, 8⟩, ⟨4, 6, 18, 10⟩, ⟨4, 5, 18, 12⟩, ⟨4, 4, 18, 14⟩, ⟨4, 3, 18, 16⟩, ⟨4, 11, 17, 2⟩, ⟨4, 11, 16, 4⟩, ⟨4, 11, 15, 6⟩, ⟨4, 11, 14, 8⟩, ⟨4, 11, 13, 10⟩, ⟨4, 11, 12, 12⟩, ⟨4, 11, 11, 14⟩, ⟨4, 11, 10, 16⟩]
  exact AllWinning.cons node_18905 (AllWinning.cons node_17955 (AllWinning.cons node_17019 (AllWinning.cons node_15910 (AllWinning.cons node_18935 (AllWinning.cons node_18020 (AllWinning.cons node_17132 (AllWinning.cons node_16081 (AllWinning.cons node_15118 (AllWinning.cons node_14168 (AllWinning.cons node_13204 (AllWinning.cons node_12229 (AllWinning.cons node_18937 (AllWinning.cons node_18025 (AllWinning.cons node_17141 (AllWinning.cons node_16099 (AllWinning.cons node_15130 (AllWinning.cons node_14183 (AllWinning.cons node_13222 (AllWinning.cons node_12253 (AllWinning.nil))))))))))))))))))))

theorem node_19799 : Outcome ⟨4, 11, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 18, 2⟩, ⟨2, 11, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨0, 11, 18, 8⟩, ⟨4, 10, 18, 2⟩, ⟨4, 9, 18, 4⟩, ⟨4, 8, 18, 6⟩, ⟨4, 7, 18, 8⟩, ⟨4, 6, 18, 10⟩, ⟨4, 5, 18, 12⟩, ⟨4, 4, 18, 14⟩, ⟨4, 3, 18, 16⟩, ⟨4, 2, 18, 18⟩, ⟨4, 1, 18, 20⟩, ⟨4, 11, 17, 2⟩, ⟨4, 11, 16, 4⟩, ⟨4, 11, 15, 6⟩, ⟨4, 11, 14, 8⟩, ⟨4, 11, 13, 10⟩, ⟨4, 11, 12, 12⟩, ⟨4, 11, 11, 14⟩, ⟨4, 11, 10, 16⟩, ⟨4, 11, 9, 18⟩, ⟨4, 11, 8, 20⟩]
  exact AllWinning.cons node_18905 (AllWinning.cons node_17955 (AllWinning.cons node_17019 (AllWinning.cons node_15910 (AllWinning.cons node_18935 (AllWinning.cons node_18020 (AllWinning.cons node_17132 (AllWinning.cons node_16081 (AllWinning.cons node_15118 (AllWinning.cons node_14168 (AllWinning.cons node_13204 (AllWinning.cons node_12229 (AllWinning.cons node_11234 (AllWinning.cons node_10174 (AllWinning.cons node_18937 (AllWinning.cons node_18025 (AllWinning.cons node_17141 (AllWinning.cons node_16099 (AllWinning.cons node_15130 (AllWinning.cons node_14183 (AllWinning.cons node_13222 (AllWinning.cons node_12253 (AllWinning.cons node_11267 (AllWinning.cons node_10214 (AllWinning.nil))))))))))))))))))))))))

theorem node_19800 : Outcome ⟨4, 11, 18, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 18, 2⟩, ⟨2, 11, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨0, 11, 18, 8⟩, ⟨4, 10, 18, 2⟩, ⟨4, 9, 18, 4⟩, ⟨4, 8, 18, 6⟩, ⟨4, 7, 18, 8⟩, ⟨4, 6, 18, 10⟩, ⟨4, 5, 18, 12⟩, ⟨4, 4, 18, 14⟩, ⟨4, 3, 18, 16⟩, ⟨4, 2, 18, 18⟩, ⟨4, 1, 18, 20⟩, ⟨4, 0, 18, 22⟩, ⟨4, 11, 17, 2⟩, ⟨4, 11, 16, 4⟩, ⟨4, 11, 15, 6⟩, ⟨4, 11, 14, 8⟩, ⟨4, 11, 13, 10⟩, ⟨4, 11, 12, 12⟩, ⟨4, 11, 11, 14⟩, ⟨4, 11, 10, 16⟩, ⟨4, 11, 9, 18⟩, ⟨4, 11, 8, 20⟩, ⟨4, 11, 7, 22⟩, ⟨4, 11, 6, 24⟩, ⟨4, 11, 5, 26⟩, ⟨4, 11, 4, 28⟩]
  exact AllWinning.cons node_18905 (AllWinning.cons node_17955 (AllWinning.cons node_17019 (AllWinning.cons node_15910 (AllWinning.cons node_18935 (AllWinning.cons node_18020 (AllWinning.cons node_17132 (AllWinning.cons node_16081 (AllWinning.cons node_15118 (AllWinning.cons node_14168 (AllWinning.cons node_13204 (AllWinning.cons node_12229 (AllWinning.cons node_11234 (AllWinning.cons node_10174 (AllWinning.cons node_9198 (AllWinning.cons node_18937 (AllWinning.cons node_18025 (AllWinning.cons node_17141 (AllWinning.cons node_16099 (AllWinning.cons node_15130 (AllWinning.cons node_14183 (AllWinning.cons node_13222 (AllWinning.cons node_12253 (AllWinning.cons node_11267 (AllWinning.cons node_10214 (AllWinning.cons node_9243 (AllWinning.cons node_8262 (AllWinning.cons node_7327 (AllWinning.cons node_6408 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19801 : Outcome ⟨4, 11, 18, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 18, 2⟩, ⟨2, 11, 18, 4⟩, ⟨1, 11, 18, 6⟩, ⟨0, 11, 18, 8⟩, ⟨4, 10, 18, 2⟩, ⟨4, 9, 18, 4⟩, ⟨4, 8, 18, 6⟩, ⟨4, 7, 18, 8⟩, ⟨4, 6, 18, 10⟩, ⟨4, 5, 18, 12⟩, ⟨4, 4, 18, 14⟩, ⟨4, 3, 18, 16⟩, ⟨4, 2, 18, 18⟩, ⟨4, 1, 18, 20⟩, ⟨4, 0, 18, 22⟩, ⟨4, 11, 17, 2⟩, ⟨4, 11, 16, 4⟩, ⟨4, 11, 15, 6⟩, ⟨4, 11, 14, 8⟩, ⟨4, 11, 13, 10⟩, ⟨4, 11, 12, 12⟩, ⟨4, 11, 11, 14⟩, ⟨4, 11, 10, 16⟩, ⟨4, 11, 9, 18⟩, ⟨4, 11, 8, 20⟩, ⟨4, 11, 7, 22⟩, ⟨4, 11, 6, 24⟩, ⟨4, 11, 5, 26⟩, ⟨4, 11, 4, 28⟩, ⟨4, 11, 3, 30⟩, ⟨4, 11, 2, 32⟩, ⟨4, 11, 1, 34⟩, ⟨4, 11, 0, 36⟩]
  exact AllWinning.cons node_18905 (AllWinning.cons node_17955 (AllWinning.cons node_17019 (AllWinning.cons node_15910 (AllWinning.cons node_18935 (AllWinning.cons node_18020 (AllWinning.cons node_17132 (AllWinning.cons node_16081 (AllWinning.cons node_15118 (AllWinning.cons node_14168 (AllWinning.cons node_13204 (AllWinning.cons node_12229 (AllWinning.cons node_11234 (AllWinning.cons node_10174 (AllWinning.cons node_9198 (AllWinning.cons node_18937 (AllWinning.cons node_18025 (AllWinning.cons node_17141 (AllWinning.cons node_16099 (AllWinning.cons node_15130 (AllWinning.cons node_14183 (AllWinning.cons node_13222 (AllWinning.cons node_12253 (AllWinning.cons node_11267 (AllWinning.cons node_10214 (AllWinning.cons node_9243 (AllWinning.cons node_8262 (AllWinning.cons node_7327 (AllWinning.cons node_6408 (AllWinning.cons node_5617 (AllWinning.cons node_4912 (AllWinning.cons node_4213 (AllWinning.cons node_3628 (AllWinning.nil)))))))))))))))))))))))))))))))))

theorem node_19802 : Outcome ⟨4, 12, 17, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 16, 2⟩) (by decide) node_18940

theorem node_19803 : Outcome ⟨4, 12, 17, 6⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 8⟩) (by decide) node_16085

theorem node_19804 : Outcome ⟨4, 13, 16, 2⟩ true :=
  Outcome.win (q := ⟨3, 13, 16, 2⟩) (by decide) node_18909

theorem node_19805 : Outcome ⟨4, 13, 16, 8⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 8⟩) (by decide) node_16091

theorem node_19806 : Outcome ⟨4, 14, 15, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 15, 2⟩) (by decide) node_18942

theorem node_19807 : Outcome ⟨4, 14, 15, 6⟩ true :=
  Outcome.win (q := ⟨4, 13, 15, 2⟩) (by decide) node_18942

theorem node_19808 : Outcome ⟨4, 14, 15, 8⟩ true :=
  Outcome.win (q := ⟨4, 13, 15, 2⟩) (by decide) node_18942

theorem node_19809 : Outcome ⟨4, 15, 14, 2⟩ true :=
  Outcome.win (q := ⟨4, 15, 13, 2⟩) (by decide) node_18950

theorem node_19810 : Outcome ⟨4, 15, 14, 6⟩ true :=
  Outcome.win (q := ⟨4, 15, 13, 2⟩) (by decide) node_18950

theorem node_19811 : Outcome ⟨4, 15, 14, 8⟩ true :=
  Outcome.win (q := ⟨4, 15, 13, 2⟩) (by decide) node_18950

theorem node_19812 : Outcome ⟨4, 16, 13, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 13, 2⟩) (by decide) node_18919

theorem node_19813 : Outcome ⟨4, 16, 13, 8⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 8⟩) (by decide) node_16104

theorem node_19814 : Outcome ⟨4, 17, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 16, 12, 2⟩) (by decide) node_18954

theorem node_19815 : Outcome ⟨4, 17, 12, 6⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 8⟩) (by decide) node_16114

theorem node_19816 : Outcome ⟨4, 18, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 11, 2⟩, ⟨2, 18, 11, 4⟩, ⟨4, 17, 11, 2⟩, ⟨4, 16, 11, 4⟩, ⟨4, 18, 10, 2⟩, ⟨4, 18, 9, 4⟩]
  exact AllWinning.cons node_18923 (AllWinning.cons node_17967 (AllWinning.cons node_18956 (AllWinning.cons node_18042 (AllWinning.cons node_18959 (AllWinning.cons node_18048 (AllWinning.nil))))))

theorem node_19817 : Outcome ⟨4, 18, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 11, 2⟩, ⟨2, 18, 11, 4⟩, ⟨1, 18, 11, 6⟩, ⟨0, 18, 11, 8⟩, ⟨4, 17, 11, 2⟩, ⟨4, 16, 11, 4⟩, ⟨4, 15, 11, 6⟩, ⟨4, 14, 11, 8⟩, ⟨4, 18, 10, 2⟩, ⟨4, 18, 9, 4⟩, ⟨4, 18, 8, 6⟩, ⟨4, 18, 7, 8⟩]
  exact AllWinning.cons node_18923 (AllWinning.cons node_17967 (AllWinning.cons node_17037 (AllWinning.cons node_15932 (AllWinning.cons node_18956 (AllWinning.cons node_18042 (AllWinning.cons node_17157 (AllWinning.cons node_16122 (AllWinning.cons node_18959 (AllWinning.cons node_18048 (AllWinning.cons node_17165 (AllWinning.cons node_16141 (AllWinning.nil))))))))))))

theorem node_19818 : Outcome ⟨4, 18, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 11, 2⟩, ⟨2, 18, 11, 4⟩, ⟨1, 18, 11, 6⟩, ⟨0, 18, 11, 8⟩, ⟨4, 17, 11, 2⟩, ⟨4, 16, 11, 4⟩, ⟨4, 15, 11, 6⟩, ⟨4, 14, 11, 8⟩, ⟨4, 13, 11, 10⟩, ⟨4, 12, 11, 12⟩, ⟨4, 18, 10, 2⟩, ⟨4, 18, 9, 4⟩, ⟨4, 18, 8, 6⟩, ⟨4, 18, 7, 8⟩, ⟨4, 18, 6, 10⟩, ⟨4, 18, 5, 12⟩]
  exact AllWinning.cons node_18923 (AllWinning.cons node_17967 (AllWinning.cons node_17037 (AllWinning.cons node_15932 (AllWinning.cons node_18956 (AllWinning.cons node_18042 (AllWinning.cons node_17157 (AllWinning.cons node_16122 (AllWinning.cons node_15135 (AllWinning.cons node_14185 (AllWinning.cons node_18959 (AllWinning.cons node_18048 (AllWinning.cons node_17165 (AllWinning.cons node_16141 (AllWinning.cons node_15145 (AllWinning.cons node_14200 (AllWinning.nil))))))))))))))))

theorem node_19819 : Outcome ⟨4, 18, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 11, 2⟩, ⟨2, 18, 11, 4⟩, ⟨1, 18, 11, 6⟩, ⟨0, 18, 11, 8⟩, ⟨4, 17, 11, 2⟩, ⟨4, 16, 11, 4⟩, ⟨4, 15, 11, 6⟩, ⟨4, 14, 11, 8⟩, ⟨4, 13, 11, 10⟩, ⟨4, 12, 11, 12⟩, ⟨4, 11, 11, 14⟩, ⟨4, 10, 11, 16⟩, ⟨4, 18, 10, 2⟩, ⟨4, 18, 9, 4⟩, ⟨4, 18, 8, 6⟩, ⟨4, 18, 7, 8⟩, ⟨4, 18, 6, 10⟩, ⟨4, 18, 5, 12⟩, ⟨4, 18, 4, 14⟩, ⟨4, 18, 3, 16⟩]
  exact AllWinning.cons node_18923 (AllWinning.cons node_17967 (AllWinning.cons node_17037 (AllWinning.cons node_15932 (AllWinning.cons node_18956 (AllWinning.cons node_18042 (AllWinning.cons node_17157 (AllWinning.cons node_16122 (AllWinning.cons node_15135 (AllWinning.cons node_14185 (AllWinning.cons node_13222 (AllWinning.cons node_12249 (AllWinning.cons node_18959 (AllWinning.cons node_18048 (AllWinning.cons node_17165 (AllWinning.cons node_16141 (AllWinning.cons node_15145 (AllWinning.cons node_14200 (AllWinning.cons node_13240 (AllWinning.cons node_12271 (AllWinning.nil))))))))))))))))))))

theorem node_19820 : Outcome ⟨4, 18, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 11, 2⟩, ⟨2, 18, 11, 4⟩, ⟨1, 18, 11, 6⟩, ⟨0, 18, 11, 8⟩, ⟨4, 17, 11, 2⟩, ⟨4, 16, 11, 4⟩, ⟨4, 15, 11, 6⟩, ⟨4, 14, 11, 8⟩, ⟨4, 13, 11, 10⟩, ⟨4, 12, 11, 12⟩, ⟨4, 11, 11, 14⟩, ⟨4, 10, 11, 16⟩, ⟨4, 9, 11, 18⟩, ⟨4, 8, 11, 20⟩, ⟨4, 18, 10, 2⟩, ⟨4, 18, 9, 4⟩, ⟨4, 18, 8, 6⟩, ⟨4, 18, 7, 8⟩, ⟨4, 18, 6, 10⟩, ⟨4, 18, 5, 12⟩, ⟨4, 18, 4, 14⟩, ⟨4, 18, 3, 16⟩, ⟨4, 18, 2, 18⟩, ⟨4, 18, 1, 20⟩]
  exact AllWinning.cons node_18923 (AllWinning.cons node_17967 (AllWinning.cons node_17037 (AllWinning.cons node_15932 (AllWinning.cons node_18956 (AllWinning.cons node_18042 (AllWinning.cons node_17157 (AllWinning.cons node_16122 (AllWinning.cons node_15135 (AllWinning.cons node_14185 (AllWinning.cons node_13222 (AllWinning.cons node_12249 (AllWinning.cons node_11260 (AllWinning.cons node_10203 (AllWinning.cons node_18959 (AllWinning.cons node_18048 (AllWinning.cons node_17165 (AllWinning.cons node_16141 (AllWinning.cons node_15145 (AllWinning.cons node_14200 (AllWinning.cons node_13240 (AllWinning.cons node_12271 (AllWinning.cons node_11291 (AllWinning.cons node_10243 (AllWinning.nil))))))))))))))))))))))))

theorem node_19821 : Outcome ⟨4, 18, 11, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 18, 11, 2⟩, ⟨2, 18, 11, 4⟩, ⟨1, 18, 11, 6⟩, ⟨0, 18, 11, 8⟩, ⟨4, 17, 11, 2⟩, ⟨4, 16, 11, 4⟩, ⟨4, 15, 11, 6⟩, ⟨4, 14, 11, 8⟩, ⟨4, 13, 11, 10⟩, ⟨4, 12, 11, 12⟩, ⟨4, 11, 11, 14⟩, ⟨4, 10, 11, 16⟩, ⟨4, 9, 11, 18⟩, ⟨4, 8, 11, 20⟩, ⟨4, 7, 11, 22⟩, ⟨4, 6, 11, 24⟩, ⟨4, 5, 11, 26⟩, ⟨4, 4, 11, 28⟩, ⟨4, 3, 11, 30⟩, ⟨4, 2, 11, 32⟩, ⟨4, 1, 11, 34⟩, ⟨4, 0, 11, 36⟩, ⟨4, 18, 10, 2⟩, ⟨4, 18, 9, 4⟩, ⟨4, 18, 8, 6⟩, ⟨4, 18, 7, 8⟩, ⟨4, 18, 6, 10⟩, ⟨4, 18, 5, 12⟩, ⟨4, 18, 4, 14⟩, ⟨4, 18, 3, 16⟩, ⟨4, 18, 2, 18⟩, ⟨4, 18, 1, 20⟩, ⟨4, 18, 0, 22⟩]
  exact AllWinning.cons node_18923 (AllWinning.cons node_17967 (AllWinning.cons node_17037 (AllWinning.cons node_15932 (AllWinning.cons node_18956 (AllWinning.cons node_18042 (AllWinning.cons node_17157 (AllWinning.cons node_16122 (AllWinning.cons node_15135 (AllWinning.cons node_14185 (AllWinning.cons node_13222 (AllWinning.cons node_12249 (AllWinning.cons node_11260 (AllWinning.cons node_10203 (AllWinning.cons node_9226 (AllWinning.cons node_8246 (AllWinning.cons node_7292 (AllWinning.cons node_6383 (AllWinning.cons node_5591 (AllWinning.cons node_4885 (AllWinning.cons node_4159 (AllWinning.cons node_3587 (AllWinning.cons node_18959 (AllWinning.cons node_18048 (AllWinning.cons node_17165 (AllWinning.cons node_16141 (AllWinning.cons node_15145 (AllWinning.cons node_14200 (AllWinning.cons node_13240 (AllWinning.cons node_12271 (AllWinning.cons node_11291 (AllWinning.cons node_10243 (AllWinning.cons node_9270 (AllWinning.nil)))))))))))))))))))))))))))))))))

theorem node_19822 : Outcome ⟨4, 19, 10, 2⟩ true :=
  Outcome.win (q := ⟨4, 19, 9, 2⟩) (by decide) node_18961

theorem node_19823 : Outcome ⟨4, 19, 10, 8⟩ true :=
  Outcome.win (q := ⟨4, 19, 9, 2⟩) (by decide) node_18961

theorem node_19824 : Outcome ⟨4, 20, 9, 2⟩ true :=
  Outcome.win (q := ⟨2, 20, 9, 4⟩) (by decide) node_17971

theorem node_19825 : Outcome ⟨4, 20, 9, 8⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 8⟩) (by decide) node_16127

theorem node_19826 : Outcome ⟨4, 20, 9, 10⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 8⟩) (by decide) node_16127

theorem node_19827 : Outcome ⟨5, 8, 20, 2⟩ true :=
  Outcome.win (q := ⟨5, 7, 20, 2⟩) (by decide) node_18966

theorem node_19828 : Outcome ⟨5, 8, 20, 4⟩ true :=
  Outcome.win (q := ⟨5, 4, 20, 8⟩) (by decide) node_16153

theorem node_19829 : Outcome ⟨5, 9, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 9, 19, 2⟩) (by decide) node_18933

theorem node_19830 : Outcome ⟨5, 10, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 4⟩) (by decide) node_17978

theorem node_19831 : Outcome ⟨5, 10, 18, 4⟩ true :=
  Outcome.win (q := ⟨3, 10, 18, 4⟩) (by decide) node_17978

theorem node_19832 : Outcome ⟨5, 11, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 17, 2⟩, ⟨3, 11, 17, 4⟩, ⟨5, 10, 17, 2⟩, ⟨5, 9, 17, 4⟩, ⟨5, 11, 16, 2⟩, ⟨5, 11, 15, 4⟩]
  exact AllWinning.cons node_18937 (AllWinning.cons node_17981 (AllWinning.cons node_18973 (AllWinning.cons node_18063 (AllWinning.cons node_18976 (AllWinning.cons node_18069 (AllWinning.nil))))))

theorem node_19833 : Outcome ⟨5, 11, 17, 6⟩ true :=
  Outcome.win (q := ⟨5, 7, 17, 8⟩) (by decide) node_16163

theorem node_19834 : Outcome ⟨5, 12, 16, 2⟩ true :=
  Outcome.win (q := ⟨4, 12, 16, 2⟩) (by decide) node_18940

theorem node_19835 : Outcome ⟨5, 12, 16, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 16, 2⟩) (by decide) node_18940

theorem node_19836 : Outcome ⟨5, 12, 16, 8⟩ true :=
  Outcome.win (q := ⟨4, 12, 16, 2⟩) (by decide) node_18940

theorem node_19837 : Outcome ⟨5, 13, 15, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 13, 4⟩) (by decide) node_18076

theorem node_19838 : Outcome ⟨5, 13, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 10⟩) (by decide) node_15166

theorem node_19839 : Outcome ⟨5, 14, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 14, 2⟩, ⟨3, 14, 14, 4⟩, ⟨5, 13, 14, 2⟩, ⟨5, 12, 14, 4⟩, ⟨5, 14, 13, 2⟩, ⟨5, 14, 12, 4⟩]
  exact AllWinning.cons node_18946 (AllWinning.cons node_17992 (AllWinning.cons node_18980 (AllWinning.cons node_18072 (AllWinning.cons node_18981 (AllWinning.cons node_18080 (AllWinning.nil))))))

theorem node_19840 : Outcome ⟨5, 14, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 14, 14, 2⟩, ⟨3, 14, 14, 4⟩, ⟨2, 14, 14, 6⟩, ⟨1, 14, 14, 8⟩, ⟨5, 13, 14, 2⟩, ⟨5, 12, 14, 4⟩, ⟨5, 11, 14, 6⟩, ⟨5, 10, 14, 8⟩, ⟨5, 14, 13, 2⟩, ⟨5, 14, 12, 4⟩, ⟨5, 14, 11, 6⟩, ⟨5, 14, 10, 8⟩]
  exact AllWinning.cons node_18946 (AllWinning.cons node_17992 (AllWinning.cons node_17067 (AllWinning.cons node_15962 (AllWinning.cons node_18980 (AllWinning.cons node_18072 (AllWinning.cons node_17186 (AllWinning.cons node_16170 (AllWinning.cons node_18981 (AllWinning.cons node_18080 (AllWinning.cons node_17194 (AllWinning.cons node_16177 (AllWinning.nil))))))))))))

theorem node_19841 : Outcome ⟨5, 14, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 10⟩) (by decide) node_14941

theorem node_19842 : Outcome ⟨5, 14, 14, 18⟩ true :=
  Outcome.win (q := ⟨0, 14, 14, 10⟩) (by decide) node_14941

theorem node_19843 : Outcome ⟨5, 15, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 13, 13, 4⟩) (by decide) node_18076

theorem node_19844 : Outcome ⟨5, 15, 13, 8⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 10⟩) (by decide) node_15198

theorem node_19845 : Outcome ⟨5, 16, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 16, 12, 2⟩) (by decide) node_18954

theorem node_19846 : Outcome ⟨5, 16, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 16, 12, 2⟩) (by decide) node_18954

theorem node_19847 : Outcome ⟨5, 16, 12, 8⟩ true :=
  Outcome.win (q := ⟨4, 16, 12, 2⟩) (by decide) node_18954

theorem node_19848 : Outcome ⟨5, 17, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 17, 11, 2⟩, ⟨3, 17, 11, 4⟩, ⟨5, 16, 11, 2⟩, ⟨5, 15, 11, 4⟩, ⟨5, 17, 10, 2⟩, ⟨5, 17, 9, 4⟩]
  exact AllWinning.cons node_18956 (AllWinning.cons node_18003 (AllWinning.cons node_18984 (AllWinning.cons node_18084 (AllWinning.cons node_18986 (AllWinning.cons node_18090 (AllWinning.nil))))))

theorem node_19849 : Outcome ⟨5, 17, 11, 6⟩ true :=
  Outcome.win (q := ⟨5, 17, 7, 8⟩) (by decide) node_16185

theorem node_19850 : Outcome ⟨5, 18, 10, 2⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 4⟩) (by decide) node_18007

theorem node_19851 : Outcome ⟨5, 18, 10, 4⟩ true :=
  Outcome.win (q := ⟨3, 18, 10, 4⟩) (by decide) node_18007

theorem node_19852 : Outcome ⟨5, 19, 9, 2⟩ true :=
  Outcome.win (q := ⟨4, 19, 9, 2⟩) (by decide) node_18961

theorem node_19853 : Outcome ⟨5, 20, 8, 2⟩ true :=
  Outcome.win (q := ⟨5, 20, 7, 2⟩) (by decide) node_18993

theorem node_19854 : Outcome ⟨5, 20, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 20, 4, 8⟩) (by decide) node_16195

theorem node_19855 : Outcome ⟨6, 7, 20, 4⟩ true :=
  Outcome.win (q := ⟨5, 7, 20, 2⟩) (by decide) node_18966

theorem node_19856 : Outcome ⟨6, 7, 20, 16⟩ true :=
  Outcome.win (q := ⟨6, 7, 8, 24⟩) (by decide) node_8377

theorem node_19857 : Outcome ⟨6, 8, 19, 14⟩ true :=
  Outcome.win (q := ⟨6, 8, 7, 24⟩) (by decide) node_8389

theorem node_19858 : Outcome ⟨6, 9, 18, 2⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 2⟩) (by decide) node_19008

theorem node_19859 : Outcome ⟨6, 10, 17, 2⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 2⟩) (by decide) node_19008

theorem node_19860 : Outcome ⟨6, 10, 17, 8⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 2⟩) (by decide) node_19008

theorem node_19861 : Outcome ⟨6, 11, 16, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 2⟩) (by decide) node_19016

theorem node_19862 : Outcome ⟨6, 12, 15, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 2⟩) (by decide) node_19016

theorem node_19863 : Outcome ⟨6, 12, 15, 16⟩ true :=
  Outcome.win (q := ⟨6, 11, 15, 2⟩) (by decide) node_19016

theorem node_19864 : Outcome ⟨6, 13, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 14, 2⟩, ⟨4, 13, 14, 4⟩, ⟨3, 13, 14, 6⟩, ⟨2, 13, 14, 8⟩, ⟨6, 12, 14, 2⟩, ⟨6, 11, 14, 4⟩, ⟨6, 10, 14, 6⟩, ⟨6, 9, 14, 8⟩, ⟨6, 13, 13, 2⟩, ⟨6, 13, 12, 4⟩, ⟨6, 13, 11, 6⟩, ⟨6, 13, 10, 8⟩]
  exact AllWinning.cons node_18980 (AllWinning.cons node_18031 (AllWinning.cons node_17106 (AllWinning.cons node_16002 (AllWinning.cons node_19021 (AllWinning.cons node_18113 (AllWinning.cons node_17222 (AllWinning.cons node_16220 (AllWinning.cons node_19023 (AllWinning.cons node_18116 (AllWinning.cons node_17231 (AllWinning.cons node_16236 (AllWinning.nil))))))))))))

theorem node_19865 : Outcome ⟨6, 13, 14, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 14, 2⟩, ⟨4, 13, 14, 4⟩, ⟨3, 13, 14, 6⟩, ⟨2, 13, 14, 8⟩, ⟨1, 13, 14, 10⟩, ⟨0, 13, 14, 12⟩, ⟨6, 12, 14, 2⟩, ⟨6, 11, 14, 4⟩, ⟨6, 10, 14, 6⟩, ⟨6, 9, 14, 8⟩, ⟨6, 8, 14, 10⟩, ⟨6, 7, 14, 12⟩, ⟨6, 13, 13, 2⟩, ⟨6, 13, 12, 4⟩, ⟨6, 13, 11, 6⟩, ⟨6, 13, 10, 8⟩, ⟨6, 13, 9, 10⟩, ⟨6, 13, 8, 12⟩]
  exact AllWinning.cons node_18980 (AllWinning.cons node_18031 (AllWinning.cons node_17106 (AllWinning.cons node_16002 (AllWinning.cons node_14985 (AllWinning.cons node_13969 (AllWinning.cons node_19021 (AllWinning.cons node_18113 (AllWinning.cons node_17222 (AllWinning.cons node_16220 (AllWinning.cons node_15233 (AllWinning.cons node_14282 (AllWinning.cons node_19023 (AllWinning.cons node_18116 (AllWinning.cons node_17231 (AllWinning.cons node_16236 (AllWinning.cons node_15248 (AllWinning.cons node_14300 (AllWinning.nil))))))))))))))))))

theorem node_19866 : Outcome ⟨6, 13, 14, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 14, 2⟩, ⟨4, 13, 14, 4⟩, ⟨3, 13, 14, 6⟩, ⟨2, 13, 14, 8⟩, ⟨1, 13, 14, 10⟩, ⟨0, 13, 14, 12⟩, ⟨6, 12, 14, 2⟩, ⟨6, 11, 14, 4⟩, ⟨6, 10, 14, 6⟩, ⟨6, 9, 14, 8⟩, ⟨6, 8, 14, 10⟩, ⟨6, 7, 14, 12⟩, ⟨6, 6, 14, 14⟩, ⟨6, 5, 14, 16⟩, ⟨6, 13, 13, 2⟩, ⟨6, 13, 12, 4⟩, ⟨6, 13, 11, 6⟩, ⟨6, 13, 10, 8⟩, ⟨6, 13, 9, 10⟩, ⟨6, 13, 8, 12⟩, ⟨6, 13, 7, 14⟩, ⟨6, 13, 6, 16⟩]
  exact AllWinning.cons node_18980 (AllWinning.cons node_18031 (AllWinning.cons node_17106 (AllWinning.cons node_16002 (AllWinning.cons node_14985 (AllWinning.cons node_13969 (AllWinning.cons node_19021 (AllWinning.cons node_18113 (AllWinning.cons node_17222 (AllWinning.cons node_16220 (AllWinning.cons node_15233 (AllWinning.cons node_14282 (AllWinning.cons node_13315 (AllWinning.cons node_12364 (AllWinning.cons node_19023 (AllWinning.cons node_18116 (AllWinning.cons node_17231 (AllWinning.cons node_16236 (AllWinning.cons node_15248 (AllWinning.cons node_14300 (AllWinning.cons node_13340 (AllWinning.cons node_12396 (AllWinning.nil))))))))))))))))))))))

theorem node_19867 : Outcome ⟨6, 13, 14, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 14, 2⟩, ⟨4, 13, 14, 4⟩, ⟨3, 13, 14, 6⟩, ⟨2, 13, 14, 8⟩, ⟨1, 13, 14, 10⟩, ⟨0, 13, 14, 12⟩, ⟨6, 12, 14, 2⟩, ⟨6, 11, 14, 4⟩, ⟨6, 10, 14, 6⟩, ⟨6, 9, 14, 8⟩, ⟨6, 8, 14, 10⟩, ⟨6, 7, 14, 12⟩, ⟨6, 6, 14, 14⟩, ⟨6, 5, 14, 16⟩, ⟨6, 4, 14, 18⟩, ⟨6, 3, 14, 20⟩, ⟨6, 13, 13, 2⟩, ⟨6, 13, 12, 4⟩, ⟨6, 13, 11, 6⟩, ⟨6, 13, 10, 8⟩, ⟨6, 13, 9, 10⟩, ⟨6, 13, 8, 12⟩, ⟨6, 13, 7, 14⟩, ⟨6, 13, 6, 16⟩, ⟨6, 13, 5, 18⟩, ⟨6, 13, 4, 20⟩]
  exact AllWinning.cons node_18980 (AllWinning.cons node_18031 (AllWinning.cons node_17106 (AllWinning.cons node_16002 (AllWinning.cons node_14985 (AllWinning.cons node_13969 (AllWinning.cons node_19021 (AllWinning.cons node_18113 (AllWinning.cons node_17222 (AllWinning.cons node_16220 (AllWinning.cons node_15233 (AllWinning.cons node_14282 (AllWinning.cons node_13315 (AllWinning.cons node_12364 (AllWinning.cons node_11377 (AllWinning.cons node_10355 (AllWinning.cons node_19023 (AllWinning.cons node_18116 (AllWinning.cons node_17231 (AllWinning.cons node_16236 (AllWinning.cons node_15248 (AllWinning.cons node_14300 (AllWinning.cons node_13340 (AllWinning.cons node_12396 (AllWinning.cons node_11413 (AllWinning.cons node_10395 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19868 : Outcome ⟨6, 13, 14, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 14, 2⟩, ⟨4, 13, 14, 4⟩, ⟨3, 13, 14, 6⟩, ⟨2, 13, 14, 8⟩, ⟨1, 13, 14, 10⟩, ⟨0, 13, 14, 12⟩, ⟨6, 12, 14, 2⟩, ⟨6, 11, 14, 4⟩, ⟨6, 10, 14, 6⟩, ⟨6, 9, 14, 8⟩, ⟨6, 8, 14, 10⟩, ⟨6, 7, 14, 12⟩, ⟨6, 6, 14, 14⟩, ⟨6, 5, 14, 16⟩, ⟨6, 4, 14, 18⟩, ⟨6, 3, 14, 20⟩, ⟨6, 2, 14, 22⟩, ⟨6, 1, 14, 24⟩, ⟨6, 13, 13, 2⟩, ⟨6, 13, 12, 4⟩, ⟨6, 13, 11, 6⟩, ⟨6, 13, 10, 8⟩, ⟨6, 13, 9, 10⟩, ⟨6, 13, 8, 12⟩, ⟨6, 13, 7, 14⟩, ⟨6, 13, 6, 16⟩, ⟨6, 13, 5, 18⟩, ⟨6, 13, 4, 20⟩, ⟨6, 13, 3, 22⟩, ⟨6, 13, 2, 24⟩]
  exact AllWinning.cons node_18980 (AllWinning.cons node_18031 (AllWinning.cons node_17106 (AllWinning.cons node_16002 (AllWinning.cons node_14985 (AllWinning.cons node_13969 (AllWinning.cons node_19021 (AllWinning.cons node_18113 (AllWinning.cons node_17222 (AllWinning.cons node_16220 (AllWinning.cons node_15233 (AllWinning.cons node_14282 (AllWinning.cons node_13315 (AllWinning.cons node_12364 (AllWinning.cons node_11377 (AllWinning.cons node_10355 (AllWinning.cons node_9348 (AllWinning.cons node_8349 (AllWinning.cons node_19023 (AllWinning.cons node_18116 (AllWinning.cons node_17231 (AllWinning.cons node_16236 (AllWinning.cons node_15248 (AllWinning.cons node_14300 (AllWinning.cons node_13340 (AllWinning.cons node_12396 (AllWinning.cons node_11413 (AllWinning.cons node_10395 (AllWinning.cons node_9389 (AllWinning.cons node_8407 (AllWinning.nil))))))))))))))))))))))))))))))

theorem node_19869 : Outcome ⟨6, 13, 14, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 14, 2⟩, ⟨4, 13, 14, 4⟩, ⟨3, 13, 14, 6⟩, ⟨2, 13, 14, 8⟩, ⟨1, 13, 14, 10⟩, ⟨0, 13, 14, 12⟩, ⟨6, 12, 14, 2⟩, ⟨6, 11, 14, 4⟩, ⟨6, 10, 14, 6⟩, ⟨6, 9, 14, 8⟩, ⟨6, 8, 14, 10⟩, ⟨6, 7, 14, 12⟩, ⟨6, 6, 14, 14⟩, ⟨6, 5, 14, 16⟩, ⟨6, 4, 14, 18⟩, ⟨6, 3, 14, 20⟩, ⟨6, 2, 14, 22⟩, ⟨6, 1, 14, 24⟩, ⟨6, 0, 14, 26⟩, ⟨6, 13, 13, 2⟩, ⟨6, 13, 12, 4⟩, ⟨6, 13, 11, 6⟩, ⟨6, 13, 10, 8⟩, ⟨6, 13, 9, 10⟩, ⟨6, 13, 8, 12⟩, ⟨6, 13, 7, 14⟩, ⟨6, 13, 6, 16⟩, ⟨6, 13, 5, 18⟩, ⟨6, 13, 4, 20⟩, ⟨6, 13, 3, 22⟩, ⟨6, 13, 2, 24⟩, ⟨6, 13, 1, 26⟩, ⟨6, 13, 0, 28⟩]
  exact AllWinning.cons node_18980 (AllWinning.cons node_18031 (AllWinning.cons node_17106 (AllWinning.cons node_16002 (AllWinning.cons node_14985 (AllWinning.cons node_13969 (AllWinning.cons node_19021 (AllWinning.cons node_18113 (AllWinning.cons node_17222 (AllWinning.cons node_16220 (AllWinning.cons node_15233 (AllWinning.cons node_14282 (AllWinning.cons node_13315 (AllWinning.cons node_12364 (AllWinning.cons node_11377 (AllWinning.cons node_10355 (AllWinning.cons node_9348 (AllWinning.cons node_8349 (AllWinning.cons node_7414 (AllWinning.cons node_19023 (AllWinning.cons node_18116 (AllWinning.cons node_17231 (AllWinning.cons node_16236 (AllWinning.cons node_15248 (AllWinning.cons node_14300 (AllWinning.cons node_13340 (AllWinning.cons node_12396 (AllWinning.cons node_11413 (AllWinning.cons node_10395 (AllWinning.cons node_9389 (AllWinning.cons node_8407 (AllWinning.cons node_7476 (AllWinning.cons node_6548 (AllWinning.nil)))))))))))))))))))))))))))))))))

theorem node_19870 : Outcome ⟨6, 13, 14, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 13, 14, 2⟩, ⟨4, 13, 14, 4⟩, ⟨3, 13, 14, 6⟩, ⟨2, 13, 14, 8⟩, ⟨1, 13, 14, 10⟩, ⟨0, 13, 14, 12⟩, ⟨6, 12, 14, 2⟩, ⟨6, 11, 14, 4⟩, ⟨6, 10, 14, 6⟩, ⟨6, 9, 14, 8⟩, ⟨6, 8, 14, 10⟩, ⟨6, 7, 14, 12⟩, ⟨6, 6, 14, 14⟩, ⟨6, 5, 14, 16⟩, ⟨6, 4, 14, 18⟩, ⟨6, 3, 14, 20⟩, ⟨6, 2, 14, 22⟩, ⟨6, 1, 14, 24⟩, ⟨6, 0, 14, 26⟩, ⟨6, 13, 13, 2⟩, ⟨6, 13, 12, 4⟩, ⟨6, 13, 11, 6⟩, ⟨6, 13, 10, 8⟩, ⟨6, 13, 9, 10⟩, ⟨6, 13, 8, 12⟩, ⟨6, 13, 7, 14⟩, ⟨6, 13, 6, 16⟩, ⟨6, 13, 5, 18⟩, ⟨6, 13, 4, 20⟩, ⟨6, 13, 3, 22⟩, ⟨6, 13, 2, 24⟩, ⟨6, 13, 1, 26⟩, ⟨6, 13, 0, 28⟩]
  exact AllWinning.cons node_18980 (AllWinning.cons node_18031 (AllWinning.cons node_17106 (AllWinning.cons node_16002 (AllWinning.cons node_14985 (AllWinning.cons node_13969 (AllWinning.cons node_19021 (AllWinning.cons node_18113 (AllWinning.cons node_17222 (AllWinning.cons node_16220 (AllWinning.cons node_15233 (AllWinning.cons node_14282 (AllWinning.cons node_13315 (AllWinning.cons node_12364 (AllWinning.cons node_11377 (AllWinning.cons node_10355 (AllWinning.cons node_9348 (AllWinning.cons node_8349 (AllWinning.cons node_7414 (AllWinning.cons node_19023 (AllWinning.cons node_18116 (AllWinning.cons node_17231 (AllWinning.cons node_16236 (AllWinning.cons node_15248 (AllWinning.cons node_14300 (AllWinning.cons node_13340 (AllWinning.cons node_12396 (AllWinning.cons node_11413 (AllWinning.cons node_10395 (AllWinning.cons node_9389 (AllWinning.cons node_8407 (AllWinning.cons node_7476 (AllWinning.cons node_6548 (AllWinning.nil)))))))))))))))))))))))))))))))))

theorem node_19871 : Outcome ⟨6, 14, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 14, 13, 2⟩, ⟨4, 14, 13, 4⟩, ⟨3, 14, 13, 6⟩, ⟨2, 14, 13, 8⟩, ⟨6, 13, 13, 2⟩, ⟨6, 12, 13, 4⟩, ⟨6, 11, 13, 6⟩, ⟨6, 10, 13, 8⟩, ⟨6, 14, 12, 2⟩, ⟨6, 14, 11, 4⟩, ⟨6, 14, 10, 6⟩, ⟨6, 14, 9, 8⟩]
  exact AllWinning.cons node_18981 (AllWinning.cons node_18035 (AllWinning.cons node_17110 (AllWinning.cons node_16004 (AllWinning.cons node_19023 (AllWinning.cons node_18114 (AllWinning.cons node_17226 (AllWinning.cons node_16223 (AllWinning.cons node_19026 (AllWinning.cons node_18119 (AllWinning.cons node_17233 (AllWinning.cons node_16241 (AllWinning.nil))))))))))))

end RQ9F1
