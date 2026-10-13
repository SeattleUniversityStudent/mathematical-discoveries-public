import Chunk02
set_option autoImplicit false
namespace RQ9F1

theorem node_813 : Outcome ⟨3, 4, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 2⟩) (by decide) node_578

theorem node_814 : Outcome ⟨3, 4, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 2⟩) (by decide) node_578

theorem node_815 : Outcome ⟨3, 4, 1, 24⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 2⟩) (by decide) node_578

theorem node_816 : Outcome ⟨3, 5, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_817 : Outcome ⟨3, 5, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_818 : Outcome ⟨3, 5, 0, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_819 : Outcome ⟨3, 5, 0, 22⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_820 : Outcome ⟨4, 0, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.nil))))

theorem node_821 : Outcome ⟨4, 0, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_822 : Outcome ⟨4, 0, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_823 : Outcome ⟨4, 0, 4, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_824 : Outcome ⟨4, 0, 4, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_825 : Outcome ⟨4, 0, 4, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_826 : Outcome ⟨4, 0, 4, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_827 : Outcome ⟨4, 0, 4, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_828 : Outcome ⟨4, 0, 4, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_829 : Outcome ⟨4, 0, 4, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_830 : Outcome ⟨4, 0, 4, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_831 : Outcome ⟨4, 0, 4, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_832 : Outcome ⟨4, 0, 4, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_833 : Outcome ⟨4, 0, 4, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_834 : Outcome ⟨4, 0, 4, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_835 : Outcome ⟨4, 0, 4, 38⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 4, 2⟩, ⟨2, 0, 4, 4⟩, ⟨1, 0, 4, 6⟩, ⟨0, 0, 4, 8⟩, ⟨4, 0, 3, 2⟩, ⟨4, 0, 2, 4⟩, ⟨4, 0, 1, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_598 (AllWinning.cons node_384 (AllWinning.cons node_263 (AllWinning.cons node_134 (AllWinning.cons node_614 (AllWinning.cons node_444 (AllWinning.cons node_311 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_836 : Outcome ⟨4, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_837 : Outcome ⟨4, 1, 3, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_838 : Outcome ⟨4, 1, 3, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_839 : Outcome ⟨4, 2, 2, 2⟩ true :=
  Outcome.win (q := ⟨3, 2, 2, 2⟩) (by decide) node_604

theorem node_840 : Outcome ⟨4, 2, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_841 : Outcome ⟨4, 2, 2, 18⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_842 : Outcome ⟨4, 2, 2, 24⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 8⟩) (by decide) node_144

theorem node_843 : Outcome ⟨4, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_844 : Outcome ⟨4, 3, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_845 : Outcome ⟨4, 3, 1, 24⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_846 : Outcome ⟨4, 4, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.nil))))

theorem node_847 : Outcome ⟨4, 4, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_848 : Outcome ⟨4, 4, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_849 : Outcome ⟨4, 4, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_850 : Outcome ⟨4, 4, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_851 : Outcome ⟨4, 4, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_852 : Outcome ⟨4, 4, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_853 : Outcome ⟨4, 4, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_854 : Outcome ⟨4, 4, 0, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_855 : Outcome ⟨4, 4, 0, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_856 : Outcome ⟨4, 4, 0, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_857 : Outcome ⟨4, 4, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_858 : Outcome ⟨4, 4, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_859 : Outcome ⟨4, 4, 0, 28⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_860 : Outcome ⟨4, 4, 0, 30⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_861 : Outcome ⟨4, 4, 0, 38⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 0, 2⟩, ⟨2, 4, 0, 4⟩, ⟨1, 4, 0, 6⟩, ⟨0, 4, 0, 8⟩, ⟨4, 3, 0, 2⟩, ⟨4, 2, 0, 4⟩, ⟨4, 1, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_612 (AllWinning.cons node_399 (AllWinning.cons node_278 (AllWinning.cons node_163 (AllWinning.cons node_652 (AllWinning.cons node_452 (AllWinning.cons node_316 (AllWinning.cons node_232 (AllWinning.nil))))))))

theorem node_862 : Outcome ⟨5, 0, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_863 : Outcome ⟨5, 0, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_864 : Outcome ⟨5, 0, 3, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_865 : Outcome ⟨5, 0, 3, 22⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 4⟩) (by decide) node_404

theorem node_866 : Outcome ⟨5, 1, 2, 2⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_867 : Outcome ⟨5, 1, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_868 : Outcome ⟨5, 1, 2, 14⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_869 : Outcome ⟨5, 1, 2, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_870 : Outcome ⟨5, 1, 2, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 2⟩) (by decide) node_616

theorem node_871 : Outcome ⟨5, 2, 1, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_872 : Outcome ⟨5, 2, 1, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_873 : Outcome ⟨5, 2, 1, 14⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_874 : Outcome ⟨5, 2, 1, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_875 : Outcome ⟨5, 2, 1, 24⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 2⟩) (by decide) node_634

theorem node_876 : Outcome ⟨5, 3, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_877 : Outcome ⟨5, 3, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_878 : Outcome ⟨5, 3, 0, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_879 : Outcome ⟨5, 3, 0, 22⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 4⟩) (by decide) node_427

theorem node_880 : Outcome ⟨6, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 1, 2⟩) (by decide) node_666

theorem node_881 : Outcome ⟨6, 0, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_882 : Outcome ⟨6, 0, 2, 18⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_883 : Outcome ⟨6, 0, 2, 22⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 8⟩) (by decide) node_186

theorem node_884 : Outcome ⟨6, 1, 1, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 2⟩) (by decide) node_658

theorem node_885 : Outcome ⟨6, 1, 1, 14⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 12⟩) (by decide) node_37

theorem node_886 : Outcome ⟨6, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 0, 2⟩) (by decide) node_671

theorem node_887 : Outcome ⟨6, 2, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_888 : Outcome ⟨6, 2, 0, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_889 : Outcome ⟨6, 2, 0, 22⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 8⟩) (by decide) node_207

theorem node_890 : Outcome ⟨7, 0, 1, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 1, 2⟩) (by decide) node_666

theorem node_891 : Outcome ⟨7, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 1, 2⟩) (by decide) node_666

theorem node_892 : Outcome ⟨7, 0, 1, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_893 : Outcome ⟨7, 0, 1, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_894 : Outcome ⟨7, 0, 1, 14⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_895 : Outcome ⟨7, 0, 1, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 12⟩) (by decide) node_59

theorem node_896 : Outcome ⟨7, 1, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 0, 2⟩) (by decide) node_671

theorem node_897 : Outcome ⟨7, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 0, 2⟩) (by decide) node_671

theorem node_898 : Outcome ⟨7, 1, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_899 : Outcome ⟨7, 1, 0, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_900 : Outcome ⟨7, 1, 0, 14⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_901 : Outcome ⟨7, 1, 0, 22⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 12⟩) (by decide) node_76

theorem node_902 : Outcome ⟨8, 0, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 0, 0, 2⟩, ⟨6, 0, 0, 4⟩]
  exact AllWinning.cons node_676 (AllWinning.cons node_463 (AllWinning.nil))

theorem node_903 : Outcome ⟨8, 0, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 0, 0, 2⟩, ⟨6, 0, 0, 4⟩, ⟨5, 0, 0, 6⟩, ⟨4, 0, 0, 8⟩]
  exact AllWinning.cons node_676 (AllWinning.cons node_463 (AllWinning.cons node_321 (AllWinning.cons node_232 (AllWinning.nil))))

theorem node_904 : Outcome ⟨8, 0, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 0, 0, 2⟩, ⟨6, 0, 0, 4⟩, ⟨5, 0, 0, 6⟩, ⟨4, 0, 0, 8⟩, ⟨3, 0, 0, 10⟩, ⟨2, 0, 0, 12⟩]
  exact AllWinning.cons node_676 (AllWinning.cons node_463 (AllWinning.cons node_321 (AllWinning.cons node_232 (AllWinning.cons node_131 (AllWinning.cons node_91 (AllWinning.nil))))))

theorem node_905 : Outcome ⟨8, 0, 0, 10⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 16⟩) (by decide) node_7

theorem node_906 : Outcome ⟨8, 0, 0, 16⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 16⟩) (by decide) node_7

theorem node_907 : Outcome ⟨0, 0, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 2⟩) (by decide) node_680

theorem node_908 : Outcome ⟨0, 0, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 2⟩) (by decide) node_680

theorem node_909 : Outcome ⟨0, 0, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 2⟩) (by decide) node_680

theorem node_910 : Outcome ⟨0, 0, 9, 18⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 18⟩) (by decide) node_8

theorem node_911 : Outcome ⟨0, 1, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_912 : Outcome ⟨0, 1, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_913 : Outcome ⟨0, 1, 8, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_914 : Outcome ⟨0, 1, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_915 : Outcome ⟨0, 1, 8, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_916 : Outcome ⟨0, 2, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 7, 2⟩, ⟨0, 0, 7, 4⟩, ⟨0, 2, 6, 2⟩, ⟨0, 2, 5, 4⟩]
  exact AllWinning.cons node_685 (AllWinning.cons node_467 (AllWinning.cons node_691 (AllWinning.cons node_475 (AllWinning.nil))))

theorem node_917 : Outcome ⟨0, 2, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 7, 2⟩, ⟨0, 0, 7, 4⟩, ⟨0, 2, 6, 2⟩, ⟨0, 2, 5, 4⟩, ⟨0, 2, 4, 6⟩, ⟨0, 2, 3, 8⟩]
  exact AllWinning.cons node_685 (AllWinning.cons node_467 (AllWinning.cons node_691 (AllWinning.cons node_475 (AllWinning.cons node_334 (AllWinning.cons node_245 (AllWinning.nil))))))

theorem node_918 : Outcome ⟨0, 2, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_919 : Outcome ⟨0, 2, 7, 10⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_920 : Outcome ⟨0, 2, 7, 16⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_921 : Outcome ⟨0, 3, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_922 : Outcome ⟨0, 3, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_923 : Outcome ⟨0, 3, 6, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_924 : Outcome ⟨0, 3, 6, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_925 : Outcome ⟨0, 3, 6, 20⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_926 : Outcome ⟨0, 4, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 2⟩) (by decide) node_699

theorem node_927 : Outcome ⟨0, 4, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 2⟩) (by decide) node_699

theorem node_928 : Outcome ⟨0, 4, 5, 14⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 2⟩) (by decide) node_699

theorem node_929 : Outcome ⟨0, 5, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 2⟩) (by decide) node_699

theorem node_930 : Outcome ⟨0, 5, 4, 8⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 2⟩) (by decide) node_699

theorem node_931 : Outcome ⟨0, 5, 4, 14⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 2⟩) (by decide) node_699

theorem node_932 : Outcome ⟨0, 6, 3, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_933 : Outcome ⟨0, 6, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_934 : Outcome ⟨0, 6, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_935 : Outcome ⟨0, 6, 3, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_936 : Outcome ⟨0, 6, 3, 20⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_937 : Outcome ⟨0, 7, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 2, 2⟩, ⟨0, 5, 2, 4⟩, ⟨0, 7, 1, 2⟩, ⟨0, 7, 0, 4⟩]
  exact AllWinning.cons node_719 (AllWinning.cons node_483 (AllWinning.cons node_723 (AllWinning.cons node_493 (AllWinning.nil))))

theorem node_938 : Outcome ⟨0, 7, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 2, 2⟩, ⟨0, 5, 2, 4⟩, ⟨0, 4, 2, 6⟩, ⟨0, 3, 2, 8⟩, ⟨0, 7, 1, 2⟩, ⟨0, 7, 0, 4⟩]
  exact AllWinning.cons node_719 (AllWinning.cons node_483 (AllWinning.cons node_355 (AllWinning.cons node_249 (AllWinning.cons node_723 (AllWinning.cons node_493 (AllWinning.nil))))))

theorem node_939 : Outcome ⟨0, 7, 2, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_940 : Outcome ⟨0, 7, 2, 10⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_941 : Outcome ⟨0, 7, 2, 16⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_942 : Outcome ⟨0, 8, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_943 : Outcome ⟨0, 8, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_944 : Outcome ⟨0, 8, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_945 : Outcome ⟨0, 8, 1, 14⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_946 : Outcome ⟨0, 8, 1, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_947 : Outcome ⟨0, 9, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 2⟩) (by decide) node_729

theorem node_948 : Outcome ⟨0, 9, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 2⟩) (by decide) node_729

theorem node_949 : Outcome ⟨0, 9, 0, 8⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 2⟩) (by decide) node_729

theorem node_950 : Outcome ⟨0, 9, 0, 18⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 18⟩) (by decide) node_8

theorem node_951 : Outcome ⟨1, 0, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_952 : Outcome ⟨1, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_953 : Outcome ⟨1, 0, 8, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_954 : Outcome ⟨1, 0, 8, 14⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_955 : Outcome ⟨1, 0, 8, 24⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_956 : Outcome ⟨1, 1, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_957 : Outcome ⟨1, 1, 7, 6⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_958 : Outcome ⟨1, 1, 7, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_959 : Outcome ⟨1, 1, 7, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_960 : Outcome ⟨1, 2, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_961 : Outcome ⟨1, 2, 6, 6⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_962 : Outcome ⟨1, 2, 6, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_963 : Outcome ⟨1, 2, 6, 20⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_964 : Outcome ⟨1, 2, 6, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_965 : Outcome ⟨1, 3, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_966 : Outcome ⟨1, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_967 : Outcome ⟨1, 3, 5, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_968 : Outcome ⟨1, 3, 5, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_969 : Outcome ⟨1, 4, 4, 2⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_970 : Outcome ⟨1, 4, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_971 : Outcome ⟨1, 4, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_972 : Outcome ⟨1, 4, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_973 : Outcome ⟨1, 4, 4, 12⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_974 : Outcome ⟨1, 4, 4, 22⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_975 : Outcome ⟨1, 5, 3, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_976 : Outcome ⟨1, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_977 : Outcome ⟨1, 5, 3, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_978 : Outcome ⟨1, 5, 3, 20⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_979 : Outcome ⟨1, 6, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_980 : Outcome ⟨1, 6, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_981 : Outcome ⟨1, 6, 2, 12⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_982 : Outcome ⟨1, 6, 2, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_983 : Outcome ⟨1, 6, 2, 22⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_984 : Outcome ⟨1, 7, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_985 : Outcome ⟨1, 7, 1, 6⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_986 : Outcome ⟨1, 7, 1, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_987 : Outcome ⟨1, 7, 1, 20⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_988 : Outcome ⟨1, 8, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 0, 4⟩) (by decide) node_548

theorem node_989 : Outcome ⟨1, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 0, 4⟩) (by decide) node_548

theorem node_990 : Outcome ⟨1, 8, 0, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_991 : Outcome ⟨1, 8, 0, 14⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_992 : Outcome ⟨1, 8, 0, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_993 : Outcome ⟨2, 0, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 7, 2⟩, ⟨0, 0, 7, 4⟩, ⟨2, 0, 6, 2⟩, ⟨2, 0, 5, 4⟩]
  exact AllWinning.cons node_734 (AllWinning.cons node_467 (AllWinning.cons node_765 (AllWinning.cons node_552 (AllWinning.nil))))

theorem node_994 : Outcome ⟨2, 0, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 0, 7, 2⟩, ⟨0, 0, 7, 4⟩, ⟨2, 0, 6, 2⟩, ⟨2, 0, 5, 4⟩, ⟨2, 0, 4, 6⟩, ⟨2, 0, 3, 8⟩]
  exact AllWinning.cons node_734 (AllWinning.cons node_467 (AllWinning.cons node_765 (AllWinning.cons node_552 (AllWinning.cons node_385 (AllWinning.cons node_282 (AllWinning.nil))))))

theorem node_995 : Outcome ⟨2, 0, 7, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_996 : Outcome ⟨2, 0, 7, 10⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_997 : Outcome ⟨2, 0, 7, 16⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_998 : Outcome ⟨2, 1, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_999 : Outcome ⟨2, 1, 6, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_1000 : Outcome ⟨2, 1, 6, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_1001 : Outcome ⟨2, 1, 6, 20⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_1002 : Outcome ⟨2, 1, 6, 22⟩ true :=
  Outcome.win (q := ⟨0, 1, 6, 4⟩) (by decide) node_471

theorem node_1003 : Outcome ⟨2, 2, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 5, 2⟩, ⟨0, 2, 5, 4⟩, ⟨2, 1, 5, 2⟩, ⟨2, 0, 5, 4⟩, ⟨2, 2, 4, 2⟩, ⟨2, 2, 3, 4⟩]
  exact AllWinning.cons node_742 (AllWinning.cons node_475 (AllWinning.cons node_769 (AllWinning.cons node_552 (AllWinning.cons node_774 (AllWinning.cons node_572 (AllWinning.nil))))))

theorem node_1004 : Outcome ⟨2, 2, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 2, 5, 2⟩, ⟨0, 2, 5, 4⟩, ⟨2, 1, 5, 2⟩, ⟨2, 0, 5, 4⟩, ⟨2, 2, 4, 2⟩, ⟨2, 2, 3, 4⟩, ⟨2, 2, 2, 6⟩, ⟨2, 2, 1, 8⟩]
  exact AllWinning.cons node_742 (AllWinning.cons node_475 (AllWinning.cons node_769 (AllWinning.cons node_552 (AllWinning.cons node_774 (AllWinning.cons node_572 (AllWinning.cons node_392 (AllWinning.cons node_289 (AllWinning.nil))))))))

theorem node_1005 : Outcome ⟨2, 2, 5, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1006 : Outcome ⟨2, 2, 5, 16⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1007 : Outcome ⟨2, 3, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1008 : Outcome ⟨2, 3, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1009 : Outcome ⟨2, 3, 4, 12⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1010 : Outcome ⟨2, 3, 4, 22⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1011 : Outcome ⟨2, 4, 3, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1012 : Outcome ⟨2, 4, 3, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1013 : Outcome ⟨2, 4, 3, 12⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1014 : Outcome ⟨2, 4, 3, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1015 : Outcome ⟨2, 5, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 2, 2⟩, ⟨0, 5, 2, 4⟩, ⟨2, 4, 2, 2⟩, ⟨2, 3, 2, 4⟩, ⟨2, 5, 1, 2⟩, ⟨2, 5, 0, 4⟩]
  exact AllWinning.cons node_752 (AllWinning.cons node_483 (AllWinning.cons node_783 (AllWinning.cons node_575 (AllWinning.cons node_787 (AllWinning.cons node_594 (AllWinning.nil))))))

theorem node_1016 : Outcome ⟨2, 5, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 5, 2, 2⟩, ⟨0, 5, 2, 4⟩, ⟨2, 4, 2, 2⟩, ⟨2, 3, 2, 4⟩, ⟨2, 2, 2, 6⟩, ⟨2, 1, 2, 8⟩, ⟨2, 5, 1, 2⟩, ⟨2, 5, 0, 4⟩]
  exact AllWinning.cons node_752 (AllWinning.cons node_483 (AllWinning.cons node_783 (AllWinning.cons node_575 (AllWinning.cons node_392 (AllWinning.cons node_286 (AllWinning.cons node_787 (AllWinning.cons node_594 (AllWinning.nil))))))))

theorem node_1017 : Outcome ⟨2, 5, 2, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_1018 : Outcome ⟨2, 5, 2, 16⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_1019 : Outcome ⟨2, 6, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_1020 : Outcome ⟨2, 6, 1, 6⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_1021 : Outcome ⟨2, 6, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_1022 : Outcome ⟨2, 6, 1, 20⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_1023 : Outcome ⟨2, 6, 1, 22⟩ true :=
  Outcome.win (q := ⟨0, 6, 1, 4⟩) (by decide) node_488

theorem node_1024 : Outcome ⟨2, 7, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 0, 2⟩, ⟨0, 7, 0, 4⟩, ⟨2, 6, 0, 2⟩, ⟨2, 5, 0, 4⟩]
  exact AllWinning.cons node_759 (AllWinning.cons node_493 (AllWinning.cons node_792 (AllWinning.cons node_594 (AllWinning.nil))))

theorem node_1025 : Outcome ⟨2, 7, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 7, 0, 2⟩, ⟨0, 7, 0, 4⟩, ⟨2, 6, 0, 2⟩, ⟨2, 5, 0, 4⟩, ⟨2, 4, 0, 6⟩, ⟨2, 3, 0, 8⟩]
  exact AllWinning.cons node_759 (AllWinning.cons node_493 (AllWinning.cons node_792 (AllWinning.cons node_594 (AllWinning.cons node_400 (AllWinning.cons node_292 (AllWinning.nil))))))

theorem node_1026 : Outcome ⟨2, 7, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1027 : Outcome ⟨2, 7, 0, 10⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1028 : Outcome ⟨2, 7, 0, 16⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1029 : Outcome ⟨3, 0, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 6, 4⟩) (by decide) node_497

theorem node_1030 : Outcome ⟨3, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1031 : Outcome ⟨3, 0, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1032 : Outcome ⟨3, 0, 6, 10⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1033 : Outcome ⟨3, 0, 6, 20⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1034 : Outcome ⟨3, 1, 5, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_1035 : Outcome ⟨3, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_1036 : Outcome ⟨3, 1, 5, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_1037 : Outcome ⟨3, 1, 5, 20⟩ true :=
  Outcome.win (q := ⟨1, 1, 5, 4⟩) (by decide) node_502

theorem node_1038 : Outcome ⟨3, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_1039 : Outcome ⟨3, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_1040 : Outcome ⟨3, 2, 4, 12⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_1041 : Outcome ⟨3, 2, 4, 22⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 4⟩) (by decide) node_506

theorem node_1042 : Outcome ⟨3, 3, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 3, 3, 2⟩, ⟨1, 3, 3, 4⟩, ⟨3, 2, 3, 2⟩, ⟨3, 1, 3, 4⟩, ⟨3, 3, 2, 2⟩, ⟨3, 3, 1, 4⟩]
  exact AllWinning.cons node_778 (AllWinning.cons node_522 (AllWinning.cons node_803 (AllWinning.cons node_600 (AllWinning.cons node_808 (AllWinning.cons node_608 (AllWinning.nil))))))

theorem node_1043 : Outcome ⟨3, 3, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_1044 : Outcome ⟨3, 3, 3, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_1045 : Outcome ⟨3, 3, 3, 20⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 6⟩) (by decide) node_339

theorem node_1046 : Outcome ⟨3, 4, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_1047 : Outcome ⟨3, 4, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_1048 : Outcome ⟨3, 4, 2, 12⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_1049 : Outcome ⟨3, 4, 2, 22⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 4⟩) (by decide) node_527

theorem node_1050 : Outcome ⟨3, 5, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_1051 : Outcome ⟨3, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_1052 : Outcome ⟨3, 5, 1, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_1053 : Outcome ⟨3, 5, 1, 20⟩ true :=
  Outcome.win (q := ⟨1, 5, 1, 4⟩) (by decide) node_544

theorem node_1054 : Outcome ⟨3, 6, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 0, 4⟩) (by decide) node_548

theorem node_1055 : Outcome ⟨3, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1056 : Outcome ⟨3, 6, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1057 : Outcome ⟨3, 6, 0, 10⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1058 : Outcome ⟨3, 6, 0, 20⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1059 : Outcome ⟨4, 0, 5, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 2⟩) (by decide) node_820

theorem node_1060 : Outcome ⟨4, 0, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 2⟩) (by decide) node_820

theorem node_1061 : Outcome ⟨4, 0, 5, 14⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 2⟩) (by decide) node_820

theorem node_1062 : Outcome ⟨4, 1, 4, 2⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1063 : Outcome ⟨4, 1, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1064 : Outcome ⟨4, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1065 : Outcome ⟨4, 1, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1066 : Outcome ⟨4, 1, 4, 12⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1067 : Outcome ⟨4, 1, 4, 22⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 4⟩) (by decide) node_557

theorem node_1068 : Outcome ⟨4, 2, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1069 : Outcome ⟨4, 2, 3, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1070 : Outcome ⟨4, 2, 3, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1071 : Outcome ⟨4, 2, 3, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1072 : Outcome ⟨4, 3, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1073 : Outcome ⟨4, 3, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1074 : Outcome ⟨4, 3, 2, 12⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1075 : Outcome ⟨4, 3, 2, 22⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1076 : Outcome ⟨4, 4, 1, 2⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1077 : Outcome ⟨4, 4, 1, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1078 : Outcome ⟨4, 4, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1079 : Outcome ⟨4, 4, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1080 : Outcome ⟨4, 4, 1, 12⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1081 : Outcome ⟨4, 4, 1, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 4⟩) (by decide) node_579

theorem node_1082 : Outcome ⟨4, 5, 0, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 2⟩) (by decide) node_846

theorem node_1083 : Outcome ⟨4, 5, 0, 8⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 2⟩) (by decide) node_846

theorem node_1084 : Outcome ⟨4, 5, 0, 14⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 2⟩) (by decide) node_846

theorem node_1085 : Outcome ⟨5, 0, 4, 2⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 2⟩) (by decide) node_820

theorem node_1086 : Outcome ⟨5, 0, 4, 8⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 2⟩) (by decide) node_820

theorem node_1087 : Outcome ⟨5, 0, 4, 14⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 2⟩) (by decide) node_820

theorem node_1088 : Outcome ⟨5, 1, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1089 : Outcome ⟨5, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1090 : Outcome ⟨5, 1, 3, 12⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1091 : Outcome ⟨5, 1, 3, 20⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1092 : Outcome ⟨5, 2, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 2, 2⟩, ⟨3, 2, 2, 4⟩, ⟨5, 1, 2, 2⟩, ⟨5, 0, 2, 4⟩, ⟨5, 2, 1, 2⟩, ⟨5, 2, 0, 4⟩]
  exact AllWinning.cons node_839 (AllWinning.cons node_605 (AllWinning.cons node_866 (AllWinning.cons node_654 (AllWinning.cons node_871 (AllWinning.cons node_662 (AllWinning.nil))))))

theorem node_1093 : Outcome ⟨5, 2, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 2, 2, 2⟩, ⟨3, 2, 2, 4⟩, ⟨2, 2, 2, 6⟩, ⟨1, 2, 2, 8⟩, ⟨5, 1, 2, 2⟩, ⟨5, 0, 2, 4⟩, ⟨5, 2, 1, 2⟩, ⟨5, 2, 0, 4⟩]
  exact AllWinning.cons node_839 (AllWinning.cons node_605 (AllWinning.cons node_392 (AllWinning.cons node_271 (AllWinning.cons node_866 (AllWinning.cons node_654 (AllWinning.cons node_871 (AllWinning.cons node_662 (AllWinning.nil))))))))

theorem node_1094 : Outcome ⟨5, 2, 2, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_1095 : Outcome ⟨5, 2, 2, 16⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 10⟩) (by decide) node_145

theorem node_1096 : Outcome ⟨5, 3, 1, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1097 : Outcome ⟨5, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1098 : Outcome ⟨5, 3, 1, 12⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1099 : Outcome ⟨5, 3, 1, 20⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1100 : Outcome ⟨5, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 2⟩) (by decide) node_846

theorem node_1101 : Outcome ⟨5, 4, 0, 8⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 2⟩) (by decide) node_846

theorem node_1102 : Outcome ⟨5, 4, 0, 14⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 2⟩) (by decide) node_846

theorem node_1103 : Outcome ⟨6, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 1, 4⟩) (by decide) node_667

theorem node_1104 : Outcome ⟨6, 0, 3, 4⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1105 : Outcome ⟨6, 0, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1106 : Outcome ⟨6, 0, 3, 10⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1107 : Outcome ⟨6, 0, 3, 20⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 6⟩) (by decide) node_405

theorem node_1108 : Outcome ⟨6, 1, 2, 2⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1109 : Outcome ⟨6, 1, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1110 : Outcome ⟨6, 1, 2, 12⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1111 : Outcome ⟨6, 1, 2, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1112 : Outcome ⟨6, 1, 2, 22⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 4⟩) (by decide) node_617

theorem node_1113 : Outcome ⟨6, 2, 1, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1114 : Outcome ⟨6, 2, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1115 : Outcome ⟨6, 2, 1, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1116 : Outcome ⟨6, 2, 1, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1117 : Outcome ⟨6, 2, 1, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 4⟩) (by decide) node_635

theorem node_1118 : Outcome ⟨6, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 0, 4⟩) (by decide) node_672

theorem node_1119 : Outcome ⟨6, 3, 0, 4⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1120 : Outcome ⟨6, 3, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1121 : Outcome ⟨6, 3, 0, 10⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1122 : Outcome ⟨6, 3, 0, 20⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 6⟩) (by decide) node_428

theorem node_1123 : Outcome ⟨7, 0, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 2, 2⟩, ⟨5, 0, 2, 4⟩, ⟨7, 0, 1, 2⟩, ⟨7, 0, 0, 4⟩]
  exact AllWinning.cons node_880 (AllWinning.cons node_654 (AllWinning.cons node_890 (AllWinning.cons node_677 (AllWinning.nil))))

theorem node_1124 : Outcome ⟨7, 0, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 0, 2, 2⟩, ⟨5, 0, 2, 4⟩, ⟨4, 0, 2, 6⟩, ⟨3, 0, 2, 8⟩, ⟨7, 0, 1, 2⟩, ⟨7, 0, 0, 4⟩]
  exact AllWinning.cons node_880 (AllWinning.cons node_654 (AllWinning.cons node_445 (AllWinning.cons node_297 (AllWinning.cons node_890 (AllWinning.cons node_677 (AllWinning.nil))))))

theorem node_1125 : Outcome ⟨7, 0, 2, 6⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_1126 : Outcome ⟨7, 0, 2, 10⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_1127 : Outcome ⟨7, 0, 2, 16⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 10⟩) (by decide) node_187

theorem node_1128 : Outcome ⟨7, 1, 1, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1129 : Outcome ⟨7, 1, 1, 6⟩ true :=
  Outcome.win (q := ⟨5, 1, 1, 4⟩) (by decide) node_659

theorem node_1130 : Outcome ⟨7, 1, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_1131 : Outcome ⟨7, 1, 1, 20⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 14⟩) (by decide) node_38

theorem node_1132 : Outcome ⟨7, 2, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 0, 2⟩, ⟨5, 2, 0, 4⟩, ⟨7, 1, 0, 2⟩, ⟨7, 0, 0, 4⟩]
  exact AllWinning.cons node_886 (AllWinning.cons node_662 (AllWinning.cons node_896 (AllWinning.cons node_677 (AllWinning.nil))))

theorem node_1133 : Outcome ⟨7, 2, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨6, 2, 0, 2⟩, ⟨5, 2, 0, 4⟩, ⟨4, 2, 0, 6⟩, ⟨3, 2, 0, 8⟩, ⟨7, 1, 0, 2⟩, ⟨7, 0, 0, 4⟩]
  exact AllWinning.cons node_886 (AllWinning.cons node_662 (AllWinning.cons node_453 (AllWinning.cons node_306 (AllWinning.cons node_896 (AllWinning.cons node_677 (AllWinning.nil))))))

theorem node_1134 : Outcome ⟨7, 2, 0, 6⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1135 : Outcome ⟨7, 2, 0, 10⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1136 : Outcome ⟨7, 2, 0, 16⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 10⟩) (by decide) node_208

theorem node_1137 : Outcome ⟨8, 0, 1, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 1, 4⟩) (by decide) node_667

theorem node_1138 : Outcome ⟨8, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 1, 4⟩) (by decide) node_667

theorem node_1139 : Outcome ⟨8, 0, 1, 12⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_1140 : Outcome ⟨8, 0, 1, 14⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_1141 : Outcome ⟨8, 0, 1, 24⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 14⟩) (by decide) node_60

theorem node_1142 : Outcome ⟨8, 1, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 0, 4⟩) (by decide) node_672

theorem node_1143 : Outcome ⟨8, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 0, 4⟩) (by decide) node_672

theorem node_1144 : Outcome ⟨8, 1, 0, 12⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_1145 : Outcome ⟨8, 1, 0, 14⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_1146 : Outcome ⟨8, 1, 0, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 14⟩) (by decide) node_77

theorem node_1147 : Outcome ⟨9, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 2⟩) (by decide) node_902

theorem node_1148 : Outcome ⟨9, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 2⟩) (by decide) node_902

theorem node_1149 : Outcome ⟨9, 0, 0, 8⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 2⟩) (by decide) node_902

theorem node_1150 : Outcome ⟨9, 0, 0, 18⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 18⟩) (by decide) node_8

end RQ9F1
