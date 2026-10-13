import Chunk22
set_option autoImplicit false
namespace RQ9F1

theorem node_5755 : Outcome ⟨7, 7, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 4⟩) (by decide) node_4254

theorem node_5756 : Outcome ⟨7, 7, 4, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 8⟩) (by decide) node_3201

theorem node_5757 : Outcome ⟨7, 7, 4, 6⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 8⟩) (by decide) node_3201

theorem node_5758 : Outcome ⟨7, 7, 4, 16⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 8⟩) (by decide) node_3201

theorem node_5759 : Outcome ⟨7, 8, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 3, 2⟩) (by decide) node_5058

theorem node_5760 : Outcome ⟨7, 8, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 3, 2⟩) (by decide) node_5058

theorem node_5761 : Outcome ⟨7, 8, 3, 6⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5762 : Outcome ⟨7, 8, 3, 14⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5763 : Outcome ⟨7, 8, 3, 18⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5764 : Outcome ⟨7, 9, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 9, 2, 6⟩) (by decide) node_3615

theorem node_5765 : Outcome ⟨7, 9, 2, 6⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5766 : Outcome ⟨7, 9, 2, 16⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5767 : Outcome ⟨7, 9, 2, 18⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5768 : Outcome ⟨7, 9, 2, 22⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5769 : Outcome ⟨7, 10, 1, 2⟩ true :=
  Outcome.win (q := ⟨7, 10, 0, 2⟩) (by decide) node_5073

theorem node_5770 : Outcome ⟨7, 10, 1, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 1, 6⟩) (by decide) node_3621

theorem node_5771 : Outcome ⟨7, 10, 1, 14⟩ true :=
  Outcome.win (q := ⟨4, 10, 1, 6⟩) (by decide) node_3621

theorem node_5772 : Outcome ⟨7, 11, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 11, 0, 2⟩) (by decide) node_5025

theorem node_5773 : Outcome ⟨7, 11, 0, 8⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 8⟩) (by decide) node_3201

theorem node_5774 : Outcome ⟨7, 11, 0, 18⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 8⟩) (by decide) node_3201

theorem node_5775 : Outcome ⟨8, 0, 10, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5776 : Outcome ⟨8, 0, 10, 6⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5777 : Outcome ⟨8, 0, 10, 22⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5778 : Outcome ⟨8, 1, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 1, 9, 2⟩, ⟨6, 1, 9, 4⟩, ⟨8, 0, 9, 2⟩, ⟨8, 1, 8, 2⟩, ⟨8, 1, 7, 4⟩]
  exact AllWinning.cons node_5034 (AllWinning.cons node_4285 (AllWinning.cons node_5077 (AllWinning.cons node_5079 (AllWinning.cons node_4404 (AllWinning.nil)))))

theorem node_5779 : Outcome ⟨8, 1, 9, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 6⟩) (by decide) node_3636

theorem node_5780 : Outcome ⟨8, 1, 9, 6⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 6⟩) (by decide) node_3636

theorem node_5781 : Outcome ⟨8, 1, 9, 10⟩ true :=
  Outcome.win (q := ⟨5, 1, 9, 6⟩) (by decide) node_3636

theorem node_5782 : Outcome ⟨8, 2, 8, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5783 : Outcome ⟨8, 2, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5784 : Outcome ⟨8, 2, 8, 12⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5785 : Outcome ⟨8, 2, 8, 22⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5786 : Outcome ⟨8, 2, 8, 32⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5787 : Outcome ⟨8, 3, 7, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 7, 2⟩) (by decide) node_5044

theorem node_5788 : Outcome ⟨8, 3, 7, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 7, 2⟩) (by decide) node_5044

theorem node_5789 : Outcome ⟨8, 3, 7, 6⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5790 : Outcome ⟨8, 3, 7, 14⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5791 : Outcome ⟨8, 3, 7, 18⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 12⟩) (by decide) node_1999

theorem node_5792 : Outcome ⟨8, 4, 6, 4⟩ true :=
  Outcome.win (q := ⟨8, 4, 4, 4⟩) (by decide) node_4415

theorem node_5793 : Outcome ⟨8, 4, 6, 6⟩ true :=
  Outcome.win (q := ⟨8, 4, 4, 4⟩) (by decide) node_4415

theorem node_5794 : Outcome ⟨8, 4, 6, 22⟩ true :=
  Outcome.win (q := ⟨8, 4, 4, 4⟩) (by decide) node_4415

theorem node_5795 : Outcome ⟨8, 5, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 5, 2⟩, ⟨6, 5, 5, 4⟩, ⟨8, 4, 5, 2⟩, ⟨8, 3, 5, 4⟩, ⟨8, 5, 4, 2⟩, ⟨8, 5, 3, 4⟩]
  exact AllWinning.cons node_5052 (AllWinning.cons node_4303 (AllWinning.cons node_5091 (AllWinning.cons node_4411 (AllWinning.cons node_5095 (AllWinning.cons node_4419 (AllWinning.nil))))))

theorem node_5796 : Outcome ⟨8, 5, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 5, 2⟩, ⟨6, 5, 5, 4⟩, ⟨5, 5, 5, 6⟩, ⟨4, 5, 5, 8⟩, ⟨8, 4, 5, 2⟩, ⟨8, 3, 5, 4⟩, ⟨8, 2, 5, 6⟩, ⟨8, 1, 5, 8⟩, ⟨8, 5, 4, 2⟩, ⟨8, 5, 3, 4⟩, ⟨8, 5, 2, 6⟩, ⟨8, 5, 1, 8⟩]
  exact AllWinning.cons node_5052 (AllWinning.cons node_4303 (AllWinning.cons node_3659 (AllWinning.cons node_3065 (AllWinning.cons node_5091 (AllWinning.cons node_4411 (AllWinning.cons node_3769 (AllWinning.cons node_3215 (AllWinning.cons node_5095 (AllWinning.cons node_4419 (AllWinning.cons node_3780 (AllWinning.cons node_3234 (AllWinning.nil))))))))))))

theorem node_5797 : Outcome ⟨8, 5, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 5, 2⟩, ⟨6, 5, 5, 4⟩, ⟨5, 5, 5, 6⟩, ⟨4, 5, 5, 8⟩, ⟨3, 5, 5, 10⟩, ⟨2, 5, 5, 12⟩, ⟨8, 4, 5, 2⟩, ⟨8, 3, 5, 4⟩, ⟨8, 2, 5, 6⟩, ⟨8, 1, 5, 8⟩, ⟨8, 0, 5, 10⟩, ⟨8, 5, 4, 2⟩, ⟨8, 5, 3, 4⟩, ⟨8, 5, 2, 6⟩, ⟨8, 5, 1, 8⟩, ⟨8, 5, 0, 10⟩]
  exact AllWinning.cons node_5052 (AllWinning.cons node_4303 (AllWinning.cons node_3659 (AllWinning.cons node_3065 (AllWinning.cons node_2553 (AllWinning.cons node_2017 (AllWinning.cons node_5091 (AllWinning.cons node_4411 (AllWinning.cons node_3769 (AllWinning.cons node_3215 (AllWinning.cons node_2723 (AllWinning.cons node_5095 (AllWinning.cons node_4419 (AllWinning.cons node_3780 (AllWinning.cons node_3234 (AllWinning.cons node_2749 (AllWinning.nil))))))))))))))))

theorem node_5798 : Outcome ⟨8, 5, 5, 10⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 16⟩) (by decide) node_1178

theorem node_5799 : Outcome ⟨8, 5, 5, 20⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 16⟩) (by decide) node_1178

theorem node_5800 : Outcome ⟨8, 6, 4, 4⟩ true :=
  Outcome.win (q := ⟨8, 4, 4, 4⟩) (by decide) node_4415

theorem node_5801 : Outcome ⟨8, 6, 4, 6⟩ true :=
  Outcome.win (q := ⟨8, 4, 4, 4⟩) (by decide) node_4415

theorem node_5802 : Outcome ⟨8, 6, 4, 22⟩ true :=
  Outcome.win (q := ⟨8, 4, 4, 4⟩) (by decide) node_4415

theorem node_5803 : Outcome ⟨8, 7, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 7, 3, 2⟩) (by decide) node_5058

theorem node_5804 : Outcome ⟨8, 7, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 7, 3, 2⟩) (by decide) node_5058

theorem node_5805 : Outcome ⟨8, 7, 3, 6⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5806 : Outcome ⟨8, 7, 3, 14⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5807 : Outcome ⟨8, 7, 3, 18⟩ true :=
  Outcome.win (q := ⟨2, 7, 3, 12⟩) (by decide) node_2029

theorem node_5808 : Outcome ⟨8, 8, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5809 : Outcome ⟨8, 8, 2, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5810 : Outcome ⟨8, 8, 2, 12⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5811 : Outcome ⟨8, 8, 2, 22⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5812 : Outcome ⟨8, 8, 2, 32⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5813 : Outcome ⟨8, 9, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 9, 1, 2⟩, ⟨6, 9, 1, 4⟩, ⟨8, 8, 1, 2⟩, ⟨8, 7, 1, 4⟩, ⟨8, 9, 0, 2⟩]
  exact AllWinning.cons node_5068 (AllWinning.cons node_4320 (AllWinning.cons node_5108 (AllWinning.cons node_4428 (AllWinning.cons node_5111 (AllWinning.nil)))))

theorem node_5814 : Outcome ⟨8, 9, 1, 4⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 6⟩) (by decide) node_3674

theorem node_5815 : Outcome ⟨8, 9, 1, 6⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 6⟩) (by decide) node_3674

theorem node_5816 : Outcome ⟨8, 9, 1, 10⟩ true :=
  Outcome.win (q := ⟨5, 9, 1, 6⟩) (by decide) node_3674

theorem node_5817 : Outcome ⟨8, 10, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5818 : Outcome ⟨8, 10, 0, 6⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5819 : Outcome ⟨8, 10, 0, 22⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5820 : Outcome ⟨9, 0, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.nil))))

theorem node_5821 : Outcome ⟨9, 0, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.nil))))))))

theorem node_5822 : Outcome ⟨9, 0, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.nil))))))))))))

theorem node_5823 : Outcome ⟨9, 0, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.nil))))))))))))))))

theorem node_5824 : Outcome ⟨9, 0, 9, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5825 : Outcome ⟨9, 0, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5826 : Outcome ⟨9, 0, 9, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5827 : Outcome ⟨9, 0, 9, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5828 : Outcome ⟨9, 0, 9, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5829 : Outcome ⟨9, 0, 9, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5830 : Outcome ⟨9, 0, 9, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5831 : Outcome ⟨9, 0, 9, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5832 : Outcome ⟨9, 0, 9, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 9, 2⟩, ⟨7, 0, 9, 4⟩, ⟨6, 0, 9, 6⟩, ⟨5, 0, 9, 8⟩, ⟨4, 0, 9, 10⟩, ⟨3, 0, 9, 12⟩, ⟨2, 0, 9, 14⟩, ⟨1, 0, 9, 16⟩, ⟨0, 0, 9, 18⟩, ⟨9, 0, 8, 2⟩, ⟨9, 0, 7, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 0, 5, 8⟩, ⟨9, 0, 4, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 0, 2, 14⟩, ⟨9, 0, 1, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5077 (AllWinning.cons node_4327 (AllWinning.cons node_3689 (AllWinning.cons node_3085 (AllWinning.cons node_2581 (AllWinning.cons node_2056 (AllWinning.cons node_1638 (AllWinning.cons node_1209 (AllWinning.cons node_910 (AllWinning.cons node_5113 (AllWinning.cons node_4445 (AllWinning.cons node_3792 (AllWinning.cons node_3241 (AllWinning.cons node_2754 (AllWinning.cons node_2318 (AllWinning.cons node_1841 (AllWinning.cons node_1530 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5833 : Outcome ⟨9, 1, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 8, 2⟩, ⟨7, 1, 8, 4⟩, ⟨9, 0, 8, 2⟩, ⟨9, 1, 7, 2⟩, ⟨9, 1, 6, 4⟩]
  exact AllWinning.cons node_5079 (AllWinning.cons node_4330 (AllWinning.cons node_5113 (AllWinning.cons node_5116 (AllWinning.cons node_4447 (AllWinning.nil)))))

theorem node_5834 : Outcome ⟨9, 1, 8, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5835 : Outcome ⟨9, 1, 8, 6⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5836 : Outcome ⟨9, 1, 8, 10⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5837 : Outcome ⟨9, 2, 7, 4⟩ true :=
  Outcome.win (q := ⟨9, 2, 4, 6⟩) (by decide) node_3809

theorem node_5838 : Outcome ⟨9, 2, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5839 : Outcome ⟨9, 2, 7, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5840 : Outcome ⟨9, 2, 7, 18⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5841 : Outcome ⟨9, 2, 7, 22⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 12⟩) (by decide) node_2070

theorem node_5842 : Outcome ⟨9, 3, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 6, 2⟩, ⟨7, 3, 6, 4⟩, ⟨9, 2, 6, 2⟩, ⟨9, 1, 6, 4⟩, ⟨9, 3, 5, 2⟩, ⟨9, 3, 4, 4⟩]
  exact AllWinning.cons node_5086 (AllWinning.cons node_4338 (AllWinning.cons node_5121 (AllWinning.cons node_4447 (AllWinning.cons node_5125 (AllWinning.cons node_4454 (AllWinning.nil))))))

theorem node_5843 : Outcome ⟨9, 3, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 6, 2⟩, ⟨7, 3, 6, 4⟩, ⟨6, 3, 6, 6⟩, ⟨5, 3, 6, 8⟩, ⟨9, 2, 6, 2⟩, ⟨9, 1, 6, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 3, 5, 2⟩, ⟨9, 3, 4, 4⟩, ⟨9, 3, 3, 6⟩, ⟨9, 3, 2, 8⟩]
  exact AllWinning.cons node_5086 (AllWinning.cons node_4338 (AllWinning.cons node_3701 (AllWinning.cons node_3097 (AllWinning.cons node_5121 (AllWinning.cons node_4447 (AllWinning.cons node_3792 (AllWinning.cons node_5125 (AllWinning.cons node_4454 (AllWinning.cons node_3814 (AllWinning.cons node_3251 (AllWinning.nil)))))))))))

theorem node_5844 : Outcome ⟨9, 3, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 6, 2⟩, ⟨7, 3, 6, 4⟩, ⟨6, 3, 6, 6⟩, ⟨5, 3, 6, 8⟩, ⟨4, 3, 6, 10⟩, ⟨3, 3, 6, 12⟩, ⟨9, 2, 6, 2⟩, ⟨9, 1, 6, 4⟩, ⟨9, 0, 6, 6⟩, ⟨9, 3, 5, 2⟩, ⟨9, 3, 4, 4⟩, ⟨9, 3, 3, 6⟩, ⟨9, 3, 2, 8⟩, ⟨9, 3, 1, 10⟩, ⟨9, 3, 0, 12⟩]
  exact AllWinning.cons node_5086 (AllWinning.cons node_4338 (AllWinning.cons node_3701 (AllWinning.cons node_3097 (AllWinning.cons node_2596 (AllWinning.cons node_2081 (AllWinning.cons node_5121 (AllWinning.cons node_4447 (AllWinning.cons node_3792 (AllWinning.cons node_5125 (AllWinning.cons node_4454 (AllWinning.cons node_3814 (AllWinning.cons node_3251 (AllWinning.cons node_2767 (AllWinning.cons node_2331 (AllWinning.nil)))))))))))))))

theorem node_5845 : Outcome ⟨9, 3, 6, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 16⟩) (by decide) node_1226

theorem node_5846 : Outcome ⟨9, 3, 6, 12⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 16⟩) (by decide) node_1226

theorem node_5847 : Outcome ⟨9, 3, 6, 28⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 16⟩) (by decide) node_1226

theorem node_5848 : Outcome ⟨9, 4, 5, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5849 : Outcome ⟨9, 4, 5, 6⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5850 : Outcome ⟨9, 4, 5, 20⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5851 : Outcome ⟨9, 4, 5, 22⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5852 : Outcome ⟨9, 5, 4, 4⟩ true :=
  Outcome.win (q := ⟨9, 2, 4, 6⟩) (by decide) node_3809

theorem node_5853 : Outcome ⟨9, 5, 4, 6⟩ true :=
  Outcome.win (q := ⟨9, 2, 4, 6⟩) (by decide) node_3809

theorem node_5854 : Outcome ⟨9, 5, 4, 20⟩ true :=
  Outcome.win (q := ⟨9, 2, 4, 6⟩) (by decide) node_3809

theorem node_5855 : Outcome ⟨9, 5, 4, 22⟩ true :=
  Outcome.win (q := ⟨9, 2, 4, 6⟩) (by decide) node_3809

theorem node_5856 : Outcome ⟨9, 6, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 6, 3, 2⟩, ⟨7, 6, 3, 4⟩, ⟨9, 5, 3, 2⟩, ⟨9, 4, 3, 4⟩, ⟨9, 6, 2, 2⟩, ⟨9, 6, 1, 4⟩]
  exact AllWinning.cons node_5099 (AllWinning.cons node_4374 (AllWinning.cons node_5132 (AllWinning.cons node_4457 (AllWinning.cons node_5136 (AllWinning.cons node_4463 (AllWinning.nil))))))

theorem node_5857 : Outcome ⟨9, 6, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 6, 3, 2⟩, ⟨7, 6, 3, 4⟩, ⟨6, 6, 3, 6⟩, ⟨5, 6, 3, 8⟩, ⟨9, 5, 3, 2⟩, ⟨9, 4, 3, 4⟩, ⟨9, 3, 3, 6⟩, ⟨9, 2, 3, 8⟩, ⟨9, 6, 2, 2⟩, ⟨9, 6, 1, 4⟩, ⟨9, 6, 0, 6⟩]
  exact AllWinning.cons node_5099 (AllWinning.cons node_4374 (AllWinning.cons node_3710 (AllWinning.cons node_3109 (AllWinning.cons node_5132 (AllWinning.cons node_4457 (AllWinning.cons node_3814 (AllWinning.cons node_3247 (AllWinning.cons node_5136 (AllWinning.cons node_4463 (AllWinning.cons node_3837 (AllWinning.nil)))))))))))

theorem node_5858 : Outcome ⟨9, 6, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 6, 3, 2⟩, ⟨7, 6, 3, 4⟩, ⟨6, 6, 3, 6⟩, ⟨5, 6, 3, 8⟩, ⟨4, 6, 3, 10⟩, ⟨3, 6, 3, 12⟩, ⟨9, 5, 3, 2⟩, ⟨9, 4, 3, 4⟩, ⟨9, 3, 3, 6⟩, ⟨9, 2, 3, 8⟩, ⟨9, 1, 3, 10⟩, ⟨9, 0, 3, 12⟩, ⟨9, 6, 2, 2⟩, ⟨9, 6, 1, 4⟩, ⟨9, 6, 0, 6⟩]
  exact AllWinning.cons node_5099 (AllWinning.cons node_4374 (AllWinning.cons node_3710 (AllWinning.cons node_3109 (AllWinning.cons node_2608 (AllWinning.cons node_2093 (AllWinning.cons node_5132 (AllWinning.cons node_4457 (AllWinning.cons node_3814 (AllWinning.cons node_3247 (AllWinning.cons node_2759 (AllWinning.cons node_2318 (AllWinning.cons node_5136 (AllWinning.cons node_4463 (AllWinning.cons node_3837 (AllWinning.nil)))))))))))))))

theorem node_5859 : Outcome ⟨9, 6, 3, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 16⟩) (by decide) node_1254

theorem node_5860 : Outcome ⟨9, 6, 3, 12⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 16⟩) (by decide) node_1254

theorem node_5861 : Outcome ⟨9, 6, 3, 28⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 16⟩) (by decide) node_1254

theorem node_5862 : Outcome ⟨9, 7, 2, 4⟩ true :=
  Outcome.win (q := ⟨9, 4, 2, 6⟩) (by decide) node_3819

theorem node_5863 : Outcome ⟨9, 7, 2, 6⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5864 : Outcome ⟨9, 7, 2, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5865 : Outcome ⟨9, 7, 2, 18⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5866 : Outcome ⟨9, 7, 2, 22⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 12⟩) (by decide) node_2101

theorem node_5867 : Outcome ⟨9, 8, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 8, 1, 2⟩, ⟨7, 8, 1, 4⟩, ⟨9, 7, 1, 2⟩, ⟨9, 6, 1, 4⟩, ⟨9, 8, 0, 2⟩]
  exact AllWinning.cons node_5108 (AllWinning.cons node_4384 (AllWinning.cons node_5140 (AllWinning.cons node_4463 (AllWinning.cons node_5144 (AllWinning.nil)))))

theorem node_5868 : Outcome ⟨9, 8, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 6⟩) (by decide) node_3825

theorem node_5869 : Outcome ⟨9, 8, 1, 6⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 6⟩) (by decide) node_3825

theorem node_5870 : Outcome ⟨9, 9, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.nil))))

theorem node_5871 : Outcome ⟨9, 9, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.nil))))))))

theorem node_5872 : Outcome ⟨9, 9, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.nil))))))))))))

theorem node_5873 : Outcome ⟨9, 9, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.nil))))))))))))))))

theorem node_5874 : Outcome ⟨9, 9, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5875 : Outcome ⟨9, 9, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5876 : Outcome ⟨9, 9, 0, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5877 : Outcome ⟨9, 9, 0, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5878 : Outcome ⟨9, 9, 0, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5879 : Outcome ⟨9, 9, 0, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5880 : Outcome ⟨9, 9, 0, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5881 : Outcome ⟨9, 9, 0, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5882 : Outcome ⟨9, 9, 0, 32⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 9, 0, 2⟩, ⟨7, 9, 0, 4⟩, ⟨6, 9, 0, 6⟩, ⟨5, 9, 0, 8⟩, ⟨4, 9, 0, 10⟩, ⟨3, 9, 0, 12⟩, ⟨2, 9, 0, 14⟩, ⟨1, 9, 0, 16⟩, ⟨0, 9, 0, 18⟩, ⟨9, 8, 0, 2⟩, ⟨9, 7, 0, 4⟩, ⟨9, 6, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨9, 4, 0, 10⟩, ⟨9, 3, 0, 12⟩, ⟨9, 2, 0, 14⟩, ⟨9, 1, 0, 16⟩, ⟨9, 0, 0, 18⟩]
  exact AllWinning.cons node_5111 (AllWinning.cons node_4388 (AllWinning.cons node_3724 (AllWinning.cons node_3122 (AllWinning.cons node_2625 (AllWinning.cons node_2119 (AllWinning.cons node_1675 (AllWinning.cons node_1277 (AllWinning.cons node_950 (AllWinning.cons node_5144 (AllWinning.cons node_4468 (AllWinning.cons node_3837 (AllWinning.cons node_3258 (AllWinning.cons node_2772 (AllWinning.cons node_2331 (AllWinning.cons node_1848 (AllWinning.cons node_1535 (AllWinning.cons node_1150 (AllWinning.nil))))))))))))))))))

theorem node_5883 : Outcome ⟨10, 0, 8, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5884 : Outcome ⟨10, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5885 : Outcome ⟨10, 0, 8, 6⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5886 : Outcome ⟨10, 0, 8, 22⟩ true :=
  Outcome.win (q := ⟨8, 0, 8, 4⟩) (by decide) node_4391

theorem node_5887 : Outcome ⟨10, 1, 7, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 7, 2⟩) (by decide) node_5147

theorem node_5888 : Outcome ⟨10, 1, 7, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 4, 6⟩) (by decide) node_3846

theorem node_5889 : Outcome ⟨10, 1, 7, 14⟩ true :=
  Outcome.win (q := ⟨10, 1, 4, 6⟩) (by decide) node_3846

theorem node_5890 : Outcome ⟨10, 2, 6, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5891 : Outcome ⟨10, 2, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5892 : Outcome ⟨10, 2, 6, 20⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5893 : Outcome ⟨10, 3, 5, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5894 : Outcome ⟨10, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5895 : Outcome ⟨10, 3, 5, 16⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5896 : Outcome ⟨10, 4, 4, 2⟩ true :=
  Outcome.win (q := ⟨8, 4, 4, 4⟩) (by decide) node_4415

theorem node_5897 : Outcome ⟨10, 4, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 4, 6⟩) (by decide) node_3846

theorem node_5898 : Outcome ⟨10, 4, 4, 6⟩ true :=
  Outcome.win (q := ⟨10, 1, 4, 6⟩) (by decide) node_3846

theorem node_5899 : Outcome ⟨10, 5, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5900 : Outcome ⟨10, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5901 : Outcome ⟨10, 5, 3, 16⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5902 : Outcome ⟨10, 6, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5903 : Outcome ⟨10, 6, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5904 : Outcome ⟨10, 6, 2, 20⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5905 : Outcome ⟨10, 7, 1, 2⟩ true :=
  Outcome.win (q := ⟨10, 7, 0, 2⟩) (by decide) node_5187

theorem node_5906 : Outcome ⟨10, 7, 1, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 1, 6⟩) (by decide) node_3856

theorem node_5907 : Outcome ⟨10, 7, 1, 14⟩ true :=
  Outcome.win (q := ⟨10, 4, 1, 6⟩) (by decide) node_3856

theorem node_5908 : Outcome ⟨10, 8, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5909 : Outcome ⟨10, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5910 : Outcome ⟨10, 8, 0, 6⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5911 : Outcome ⟨10, 8, 0, 22⟩ true :=
  Outcome.win (q := ⟨8, 8, 0, 4⟩) (by decide) node_4432

theorem node_5912 : Outcome ⟨11, 0, 7, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 7, 2⟩) (by decide) node_5147

theorem node_5913 : Outcome ⟨11, 0, 7, 8⟩ true :=
  Outcome.win (q := ⟨7, 0, 7, 8⟩) (by decide) node_3164

theorem node_5914 : Outcome ⟨11, 1, 6, 2⟩ true :=
  Outcome.win (q := ⟨11, 0, 6, 2⟩) (by decide) node_5189

theorem node_5915 : Outcome ⟨11, 1, 6, 4⟩ true :=
  Outcome.win (q := ⟨11, 0, 6, 2⟩) (by decide) node_5189

theorem node_5916 : Outcome ⟨11, 1, 6, 10⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 16⟩) (by decide) node_1326

theorem node_5917 : Outcome ⟨11, 2, 5, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5918 : Outcome ⟨11, 2, 5, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 5, 2⟩) (by decide) node_5152

theorem node_5919 : Outcome ⟨11, 3, 4, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 3, 2⟩) (by decide) node_5199

theorem node_5920 : Outcome ⟨11, 4, 3, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 3, 2⟩) (by decide) node_5199

theorem node_5921 : Outcome ⟨11, 5, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5922 : Outcome ⟨11, 5, 2, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 2⟩) (by decide) node_5171

theorem node_5923 : Outcome ⟨11, 6, 1, 2⟩ true :=
  Outcome.win (q := ⟨11, 6, 0, 2⟩) (by decide) node_5206

theorem node_5924 : Outcome ⟨11, 6, 1, 4⟩ true :=
  Outcome.win (q := ⟨11, 6, 0, 2⟩) (by decide) node_5206

theorem node_5925 : Outcome ⟨11, 6, 1, 10⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 16⟩) (by decide) node_1357

theorem node_5926 : Outcome ⟨11, 7, 0, 2⟩ true :=
  Outcome.win (q := ⟨10, 7, 0, 2⟩) (by decide) node_5187

theorem node_5927 : Outcome ⟨11, 7, 0, 8⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 8⟩) (by decide) node_3201

theorem node_5928 : Outcome ⟨12, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨12, 0, 4, 4⟩) (by decide) node_4513

theorem node_5929 : Outcome ⟨12, 0, 6, 12⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 12⟩) (by decide) node_2196

theorem node_5930 : Outcome ⟨12, 0, 6, 14⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 12⟩) (by decide) node_2196

theorem node_5931 : Outcome ⟨12, 1, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 5, 2⟩, ⟨10, 1, 5, 4⟩, ⟨12, 0, 5, 2⟩, ⟨12, 1, 4, 2⟩, ⟨12, 1, 3, 4⟩]
  exact AllWinning.cons node_5194 (AllWinning.cons node_4474 (AllWinning.cons node_5211 (AllWinning.cons node_5215 (AllWinning.cons node_4518 (AllWinning.nil)))))

theorem node_5932 : Outcome ⟨12, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5933 : Outcome ⟨12, 1, 5, 6⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 6⟩) (by decide) node_3797

theorem node_5934 : Outcome ⟨12, 2, 4, 2⟩ true :=
  Outcome.win (q := ⟨12, 0, 4, 4⟩) (by decide) node_4513

theorem node_5935 : Outcome ⟨12, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨9, 2, 4, 6⟩) (by decide) node_3809

theorem node_5936 : Outcome ⟨12, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨9, 2, 4, 6⟩) (by decide) node_3809

theorem node_5937 : Outcome ⟨12, 2, 4, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 22⟩) (by decide) node_514

theorem node_5938 : Outcome ⟨12, 2, 4, 22⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 22⟩) (by decide) node_514

theorem node_5939 : Outcome ⟨12, 3, 3, 2⟩ true :=
  Outcome.win (q := ⟨11, 3, 3, 2⟩) (by decide) node_5199

theorem node_5940 : Outcome ⟨12, 3, 3, 12⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 24⟩) (by decide) node_348

theorem node_5941 : Outcome ⟨12, 4, 2, 2⟩ true :=
  Outcome.win (q := ⟨12, 4, 0, 4⟩) (by decide) node_4530

theorem node_5942 : Outcome ⟨12, 4, 2, 4⟩ true :=
  Outcome.win (q := ⟨9, 4, 2, 6⟩) (by decide) node_3819

theorem node_5943 : Outcome ⟨12, 4, 2, 6⟩ true :=
  Outcome.win (q := ⟨9, 4, 2, 6⟩) (by decide) node_3819

theorem node_5944 : Outcome ⟨12, 4, 2, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 22⟩) (by decide) node_535

theorem node_5945 : Outcome ⟨12, 4, 2, 22⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 22⟩) (by decide) node_535

theorem node_5946 : Outcome ⟨12, 5, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 5, 1, 2⟩, ⟨10, 5, 1, 4⟩, ⟨12, 4, 1, 2⟩, ⟨12, 3, 1, 4⟩, ⟨12, 5, 0, 2⟩]
  exact AllWinning.cons node_5203 (AllWinning.cons node_4486 (AllWinning.cons node_5228 (AllWinning.cons node_4525 (AllWinning.cons node_5233 (AllWinning.nil)))))

theorem node_5947 : Outcome ⟨12, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 6⟩) (by decide) node_3825

theorem node_5948 : Outcome ⟨12, 5, 1, 6⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 6⟩) (by decide) node_3825

theorem node_5949 : Outcome ⟨12, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨12, 4, 0, 4⟩) (by decide) node_4530

theorem node_5950 : Outcome ⟨12, 6, 0, 12⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 12⟩) (by decide) node_2230

theorem node_5951 : Outcome ⟨12, 6, 0, 14⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 12⟩) (by decide) node_2230

theorem node_5952 : Outcome ⟨13, 0, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 5, 2⟩, ⟨11, 0, 5, 4⟩, ⟨13, 0, 4, 2⟩, ⟨13, 0, 3, 4⟩]
  exact AllWinning.cons node_5211 (AllWinning.cons node_4493 (AllWinning.cons node_5237 (AllWinning.cons node_4535 (AllWinning.nil))))

theorem node_5953 : Outcome ⟨13, 0, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 5, 2⟩, ⟨11, 0, 5, 4⟩, ⟨10, 0, 5, 6⟩, ⟨9, 0, 5, 8⟩, ⟨13, 0, 4, 2⟩, ⟨13, 0, 3, 4⟩, ⟨13, 0, 2, 6⟩, ⟨13, 0, 1, 8⟩]
  exact AllWinning.cons node_5211 (AllWinning.cons node_4493 (AllWinning.cons node_3841 (AllWinning.cons node_3241 (AllWinning.cons node_5237 (AllWinning.cons node_4535 (AllWinning.cons node_3899 (AllWinning.cons node_3310 (AllWinning.nil))))))))

theorem node_5954 : Outcome ⟨13, 0, 5, 6⟩ true :=
  Outcome.win (q := ⟨13, 0, 0, 10⟩) (by decide) node_2818

theorem node_5955 : Outcome ⟨13, 0, 5, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 16⟩) (by decide) node_1411

theorem node_5956 : Outcome ⟨13, 0, 5, 16⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 16⟩) (by decide) node_1411

theorem node_5957 : Outcome ⟨13, 1, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 1, 4, 2⟩, ⟨11, 1, 4, 4⟩, ⟨13, 0, 4, 2⟩, ⟨13, 1, 3, 2⟩, ⟨13, 1, 2, 4⟩]
  exact AllWinning.cons node_5215 (AllWinning.cons node_4497 (AllWinning.cons node_5237 (AllWinning.cons node_5241 (AllWinning.cons node_4539 (AllWinning.nil)))))

theorem node_5958 : Outcome ⟨13, 1, 4, 4⟩ true :=
  Outcome.win (q := ⟨10, 1, 4, 6⟩) (by decide) node_3846

theorem node_5959 : Outcome ⟨13, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨10, 1, 4, 6⟩) (by decide) node_3846

theorem node_5960 : Outcome ⟨13, 1, 4, 10⟩ true :=
  Outcome.win (q := ⟨10, 1, 4, 6⟩) (by decide) node_3846

theorem node_5961 : Outcome ⟨13, 1, 4, 22⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 22⟩) (by decide) node_565

theorem node_5962 : Outcome ⟨13, 1, 4, 26⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 22⟩) (by decide) node_565

theorem node_5963 : Outcome ⟨13, 2, 3, 2⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 2⟩) (by decide) node_5247

theorem node_5964 : Outcome ⟨13, 2, 3, 16⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 12⟩) (by decide) node_2254

theorem node_5965 : Outcome ⟨13, 3, 2, 2⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 2⟩) (by decide) node_5247

theorem node_5966 : Outcome ⟨13, 3, 2, 16⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 12⟩) (by decide) node_2270

theorem node_5967 : Outcome ⟨13, 4, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 4, 1, 2⟩, ⟨11, 4, 1, 4⟩, ⟨13, 3, 1, 2⟩, ⟨13, 2, 1, 4⟩, ⟨13, 4, 0, 2⟩]
  exact AllWinning.cons node_5228 (AllWinning.cons node_4504 (AllWinning.cons node_5253 (AllWinning.cons node_4542 (AllWinning.cons node_5259 (AllWinning.nil)))))

theorem node_5968 : Outcome ⟨13, 4, 1, 4⟩ true :=
  Outcome.win (q := ⟨10, 4, 1, 6⟩) (by decide) node_3856

theorem node_5969 : Outcome ⟨13, 4, 1, 6⟩ true :=
  Outcome.win (q := ⟨10, 4, 1, 6⟩) (by decide) node_3856

theorem node_5970 : Outcome ⟨13, 4, 1, 10⟩ true :=
  Outcome.win (q := ⟨10, 4, 1, 6⟩) (by decide) node_3856

theorem node_5971 : Outcome ⟨13, 4, 1, 22⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 22⟩) (by decide) node_587

theorem node_5972 : Outcome ⟨13, 4, 1, 26⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 22⟩) (by decide) node_587

theorem node_5973 : Outcome ⟨13, 5, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 0, 2⟩, ⟨11, 5, 0, 4⟩, ⟨13, 4, 0, 2⟩, ⟨13, 3, 0, 4⟩]
  exact AllWinning.cons node_5233 (AllWinning.cons node_4508 (AllWinning.cons node_5259 (AllWinning.cons node_4544 (AllWinning.nil))))

theorem node_5974 : Outcome ⟨13, 5, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 5, 0, 2⟩, ⟨11, 5, 0, 4⟩, ⟨10, 5, 0, 6⟩, ⟨9, 5, 0, 8⟩, ⟨13, 4, 0, 2⟩, ⟨13, 3, 0, 4⟩, ⟨13, 2, 0, 6⟩, ⟨13, 1, 0, 8⟩]
  exact AllWinning.cons node_5233 (AllWinning.cons node_4508 (AllWinning.cons node_3860 (AllWinning.cons node_3258 (AllWinning.cons node_5259 (AllWinning.cons node_4544 (AllWinning.cons node_3907 (AllWinning.cons node_3313 (AllWinning.nil))))))))

theorem node_5975 : Outcome ⟨13, 5, 0, 6⟩ true :=
  Outcome.win (q := ⟨13, 0, 0, 10⟩) (by decide) node_2818

theorem node_5976 : Outcome ⟨13, 5, 0, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 16⟩) (by decide) node_1445

theorem node_5977 : Outcome ⟨13, 5, 0, 16⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 16⟩) (by decide) node_1445

theorem node_5978 : Outcome ⟨14, 0, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 6⟩) (by decide) node_3911

theorem node_5979 : Outcome ⟨14, 0, 4, 6⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 6⟩) (by decide) node_3911

theorem node_5980 : Outcome ⟨14, 0, 4, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 20⟩) (by decide) node_829

theorem node_5981 : Outcome ⟨14, 1, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 1, 3, 2⟩, ⟨12, 1, 3, 4⟩, ⟨14, 0, 3, 2⟩, ⟨14, 1, 2, 2⟩, ⟨14, 1, 1, 4⟩]
  exact AllWinning.cons node_5241 (AllWinning.cons node_4518 (AllWinning.cons node_5263 (AllWinning.cons node_5268 (AllWinning.cons node_4550 (AllWinning.nil)))))

theorem node_5982 : Outcome ⟨14, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 6⟩) (by decide) node_3919

theorem node_5983 : Outcome ⟨14, 1, 3, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 16⟩) (by decide) node_1462

theorem node_5984 : Outcome ⟨14, 1, 3, 14⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 16⟩) (by decide) node_1462

theorem node_5985 : Outcome ⟨14, 1, 3, 32⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 16⟩) (by decide) node_1462

theorem node_5986 : Outcome ⟨14, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 2⟩) (by decide) node_5247

theorem node_5987 : Outcome ⟨14, 2, 2, 8⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 2⟩) (by decide) node_5247

theorem node_5988 : Outcome ⟨14, 2, 2, 20⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 28⟩) (by decide) node_154

theorem node_5989 : Outcome ⟨14, 3, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 3, 1, 2⟩, ⟨12, 3, 1, 4⟩, ⟨14, 2, 1, 2⟩, ⟨14, 1, 1, 4⟩, ⟨14, 3, 0, 2⟩]
  exact AllWinning.cons node_5253 (AllWinning.cons node_4525 (AllWinning.cons node_5272 (AllWinning.cons node_4550 (AllWinning.cons node_5276 (AllWinning.nil)))))

theorem node_5990 : Outcome ⟨14, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨14, 0, 1, 6⟩) (by decide) node_3911

theorem node_5991 : Outcome ⟨14, 3, 1, 10⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 16⟩) (by decide) node_1482

theorem node_5992 : Outcome ⟨14, 3, 1, 14⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 16⟩) (by decide) node_1482

theorem node_5993 : Outcome ⟨14, 3, 1, 32⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 16⟩) (by decide) node_1482

theorem node_5994 : Outcome ⟨14, 4, 0, 4⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 6⟩) (by decide) node_3919

theorem node_5995 : Outcome ⟨14, 4, 0, 6⟩ true :=
  Outcome.win (q := ⟨14, 1, 0, 6⟩) (by decide) node_3919

theorem node_5996 : Outcome ⟨14, 4, 0, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 20⟩) (by decide) node_855

theorem node_5997 : Outcome ⟨15, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨15, 0, 2, 2⟩) (by decide) node_5281

end RQ9F1
