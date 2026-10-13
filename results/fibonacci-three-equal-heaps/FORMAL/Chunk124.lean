import Chunk123
set_option autoImplicit false
namespace RQ9F1

theorem node_26032 : Outcome ⟨19, 19, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 19, 18, 2⟩, ⟨17, 19, 18, 4⟩, ⟨16, 19, 18, 6⟩, ⟨15, 19, 18, 8⟩, ⟨19, 18, 18, 2⟩, ⟨19, 17, 18, 4⟩, ⟨19, 16, 18, 6⟩, ⟨19, 15, 18, 8⟩, ⟨19, 19, 17, 2⟩, ⟨19, 19, 16, 4⟩, ⟨19, 19, 15, 6⟩, ⟨19, 19, 14, 8⟩]
  exact AllWinning.cons node_26023 (AllWinning.cons node_26011 (AllWinning.cons node_25990 (AllWinning.cons node_25958 (AllWinning.cons node_26025 (AllWinning.cons node_26015 (AllWinning.cons node_26000 (AllWinning.cons node_25975 (AllWinning.cons node_26026 (AllWinning.cons node_26018 (AllWinning.cons node_26004 (AllWinning.cons node_25980 (AllWinning.nil))))))))))))

theorem node_26033 : Outcome ⟨17, 20, 20, 4⟩ true :=
  Outcome.win (q := ⟨16, 20, 20, 2⟩) (by decide) node_26027

theorem node_26034 : Outcome ⟨19, 18, 20, 4⟩ true :=
  Outcome.win (q := ⟨19, 18, 19, 2⟩) (by decide) node_26029

theorem node_26035 : Outcome ⟨19, 20, 18, 4⟩ true :=
  Outcome.win (q := ⟨19, 19, 18, 2⟩) (by decide) node_26031

theorem node_26036 : Outcome ⟨18, 20, 20, 2⟩ true :=
  Outcome.win (q := ⟨16, 20, 20, 4⟩) (by decide) node_26028

theorem node_26037 : Outcome ⟨19, 19, 20, 2⟩ true :=
  Outcome.win (q := ⟨19, 19, 18, 4⟩) (by decide) node_26032

theorem node_26038 : Outcome ⟨19, 20, 19, 2⟩ true :=
  Outcome.win (q := ⟨19, 18, 19, 4⟩) (by decide) node_26030

theorem node_26039 : Outcome ⟨19, 20, 20, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨18, 20, 20, 2⟩, ⟨17, 20, 20, 4⟩, ⟨19, 19, 20, 2⟩, ⟨19, 18, 20, 4⟩, ⟨19, 20, 19, 2⟩, ⟨19, 20, 18, 4⟩]
  exact AllWinning.cons node_26036 (AllWinning.cons node_26033 (AllWinning.cons node_26037 (AllWinning.cons node_26034 (AllWinning.cons node_26038 (AllWinning.cons node_26035 (AllWinning.nil))))))

theorem node_26040 : Outcome ⟨20, 20, 20, 1⟩ true :=
  Outcome.win (q := ⟨19, 20, 20, 2⟩) (by decide) node_26039

end RQ9F1
