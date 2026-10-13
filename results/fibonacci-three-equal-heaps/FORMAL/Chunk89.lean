import Chunk88
set_option autoImplicit false
namespace RQ9F1

theorem node_19450 : Outcome ⟨14, 16, 2, 8⟩ true :=
  Outcome.win (q := ⟨10, 16, 2, 8⟩) (by decide) node_15500

theorem node_19451 : Outcome ⟨14, 17, 1, 2⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 2⟩) (by decide) node_18535

theorem node_19452 : Outcome ⟨14, 17, 1, 4⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 2⟩) (by decide) node_18535

theorem node_19453 : Outcome ⟨14, 18, 0, 2⟩ true :=
  Outcome.win (q := ⟨13, 18, 0, 2⟩) (by decide) node_18541

theorem node_19454 : Outcome ⟨15, 0, 17, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 4⟩) (by decide) node_17690

theorem node_19455 : Outcome ⟨15, 0, 17, 6⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 4⟩) (by decide) node_17690

theorem node_19456 : Outcome ⟨15, 0, 17, 8⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 4⟩) (by decide) node_17690

theorem node_19457 : Outcome ⟨15, 1, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.nil)))))

theorem node_19458 : Outcome ⟨15, 1, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.nil)))))))))

theorem node_19459 : Outcome ⟨15, 1, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.nil)))))))))))))

theorem node_19460 : Outcome ⟨15, 1, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨8, 1, 16, 14⟩, ⟨7, 1, 16, 16⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩, ⟨15, 1, 9, 14⟩, ⟨15, 1, 8, 16⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_12492 (AllWinning.cons node_11436 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.cons node_12828 (AllWinning.cons node_11841 (AllWinning.nil)))))))))))))))))

theorem node_19461 : Outcome ⟨15, 1, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨8, 1, 16, 14⟩, ⟨7, 1, 16, 16⟩, ⟨6, 1, 16, 18⟩, ⟨5, 1, 16, 20⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩, ⟨15, 1, 9, 14⟩, ⟨15, 1, 8, 16⟩, ⟨15, 1, 7, 18⟩, ⟨15, 1, 6, 20⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_12492 (AllWinning.cons node_11436 (AllWinning.cons node_10345 (AllWinning.cons node_9276 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.cons node_12828 (AllWinning.cons node_11841 (AllWinning.cons node_10842 (AllWinning.cons node_9775 (AllWinning.nil)))))))))))))))))))))

theorem node_19462 : Outcome ⟨15, 1, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨8, 1, 16, 14⟩, ⟨7, 1, 16, 16⟩, ⟨6, 1, 16, 18⟩, ⟨5, 1, 16, 20⟩, ⟨4, 1, 16, 22⟩, ⟨3, 1, 16, 24⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩, ⟨15, 1, 9, 14⟩, ⟨15, 1, 8, 16⟩, ⟨15, 1, 7, 18⟩, ⟨15, 1, 6, 20⟩, ⟨15, 1, 5, 22⟩, ⟨15, 1, 4, 24⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_12492 (AllWinning.cons node_11436 (AllWinning.cons node_10345 (AllWinning.cons node_9276 (AllWinning.cons node_8227 (AllWinning.cons node_7205 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.cons node_12828 (AllWinning.cons node_11841 (AllWinning.cons node_10842 (AllWinning.cons node_9775 (AllWinning.cons node_8830 (AllWinning.cons node_7836 (AllWinning.nil)))))))))))))))))))))))))

theorem node_19463 : Outcome ⟨15, 1, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨8, 1, 16, 14⟩, ⟨7, 1, 16, 16⟩, ⟨6, 1, 16, 18⟩, ⟨5, 1, 16, 20⟩, ⟨4, 1, 16, 22⟩, ⟨3, 1, 16, 24⟩, ⟨2, 1, 16, 26⟩, ⟨1, 1, 16, 28⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩, ⟨15, 1, 9, 14⟩, ⟨15, 1, 8, 16⟩, ⟨15, 1, 7, 18⟩, ⟨15, 1, 6, 20⟩, ⟨15, 1, 5, 22⟩, ⟨15, 1, 4, 24⟩, ⟨15, 1, 3, 26⟩, ⟨15, 1, 2, 28⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_12492 (AllWinning.cons node_11436 (AllWinning.cons node_10345 (AllWinning.cons node_9276 (AllWinning.cons node_8227 (AllWinning.cons node_7205 (AllWinning.cons node_6202 (AllWinning.cons node_5395 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.cons node_12828 (AllWinning.cons node_11841 (AllWinning.cons node_10842 (AllWinning.cons node_9775 (AllWinning.cons node_8830 (AllWinning.cons node_7836 (AllWinning.cons node_6896 (AllWinning.cons node_6004 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19464 : Outcome ⟨15, 1, 16, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨8, 1, 16, 14⟩, ⟨7, 1, 16, 16⟩, ⟨6, 1, 16, 18⟩, ⟨5, 1, 16, 20⟩, ⟨4, 1, 16, 22⟩, ⟨3, 1, 16, 24⟩, ⟨2, 1, 16, 26⟩, ⟨1, 1, 16, 28⟩, ⟨0, 1, 16, 30⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩, ⟨15, 1, 9, 14⟩, ⟨15, 1, 8, 16⟩, ⟨15, 1, 7, 18⟩, ⟨15, 1, 6, 20⟩, ⟨15, 1, 5, 22⟩, ⟨15, 1, 4, 24⟩, ⟨15, 1, 3, 26⟩, ⟨15, 1, 2, 28⟩, ⟨15, 1, 1, 30⟩, ⟨15, 1, 0, 32⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_12492 (AllWinning.cons node_11436 (AllWinning.cons node_10345 (AllWinning.cons node_9276 (AllWinning.cons node_8227 (AllWinning.cons node_7205 (AllWinning.cons node_6202 (AllWinning.cons node_5395 (AllWinning.cons node_4574 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.cons node_12828 (AllWinning.cons node_11841 (AllWinning.cons node_10842 (AllWinning.cons node_9775 (AllWinning.cons node_8830 (AllWinning.cons node_7836 (AllWinning.cons node_6896 (AllWinning.cons node_6004 (AllWinning.cons node_5290 (AllWinning.cons node_4563 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19465 : Outcome ⟨15, 1, 16, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨8, 1, 16, 14⟩, ⟨7, 1, 16, 16⟩, ⟨6, 1, 16, 18⟩, ⟨5, 1, 16, 20⟩, ⟨4, 1, 16, 22⟩, ⟨3, 1, 16, 24⟩, ⟨2, 1, 16, 26⟩, ⟨1, 1, 16, 28⟩, ⟨0, 1, 16, 30⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩, ⟨15, 1, 9, 14⟩, ⟨15, 1, 8, 16⟩, ⟨15, 1, 7, 18⟩, ⟨15, 1, 6, 20⟩, ⟨15, 1, 5, 22⟩, ⟨15, 1, 4, 24⟩, ⟨15, 1, 3, 26⟩, ⟨15, 1, 2, 28⟩, ⟨15, 1, 1, 30⟩, ⟨15, 1, 0, 32⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_12492 (AllWinning.cons node_11436 (AllWinning.cons node_10345 (AllWinning.cons node_9276 (AllWinning.cons node_8227 (AllWinning.cons node_7205 (AllWinning.cons node_6202 (AllWinning.cons node_5395 (AllWinning.cons node_4574 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.cons node_12828 (AllWinning.cons node_11841 (AllWinning.cons node_10842 (AllWinning.cons node_9775 (AllWinning.cons node_8830 (AllWinning.cons node_7836 (AllWinning.cons node_6896 (AllWinning.cons node_6004 (AllWinning.cons node_5290 (AllWinning.cons node_4563 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19466 : Outcome ⟨15, 1, 16, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 1, 16, 2⟩, ⟨13, 1, 16, 4⟩, ⟨12, 1, 16, 6⟩, ⟨11, 1, 16, 8⟩, ⟨10, 1, 16, 10⟩, ⟨9, 1, 16, 12⟩, ⟨8, 1, 16, 14⟩, ⟨7, 1, 16, 16⟩, ⟨6, 1, 16, 18⟩, ⟨5, 1, 16, 20⟩, ⟨4, 1, 16, 22⟩, ⟨3, 1, 16, 24⟩, ⟨2, 1, 16, 26⟩, ⟨1, 1, 16, 28⟩, ⟨0, 1, 16, 30⟩, ⟨15, 0, 16, 2⟩, ⟨15, 1, 15, 2⟩, ⟨15, 1, 14, 4⟩, ⟨15, 1, 13, 6⟩, ⟨15, 1, 12, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 1, 10, 12⟩, ⟨15, 1, 9, 14⟩, ⟨15, 1, 8, 16⟩, ⟨15, 1, 7, 18⟩, ⟨15, 1, 6, 20⟩, ⟨15, 1, 5, 22⟩, ⟨15, 1, 4, 24⟩, ⟨15, 1, 3, 26⟩, ⟨15, 1, 2, 28⟩, ⟨15, 1, 1, 30⟩, ⟨15, 1, 0, 32⟩]
  exact AllWinning.cons node_18546 (AllWinning.cons node_17579 (AllWinning.cons node_16607 (AllWinning.cons node_15512 (AllWinning.cons node_14520 (AllWinning.cons node_13495 (AllWinning.cons node_12492 (AllWinning.cons node_11436 (AllWinning.cons node_10345 (AllWinning.cons node_9276 (AllWinning.cons node_8227 (AllWinning.cons node_7205 (AllWinning.cons node_6202 (AllWinning.cons node_5395 (AllWinning.cons node_4574 (AllWinning.cons node_18600 (AllWinning.cons node_18602 (AllWinning.cons node_17696 (AllWinning.cons node_16783 (AllWinning.cons node_15735 (AllWinning.cons node_14756 (AllWinning.cons node_13802 (AllWinning.cons node_12828 (AllWinning.cons node_11841 (AllWinning.cons node_10842 (AllWinning.cons node_9775 (AllWinning.cons node_8830 (AllWinning.cons node_7836 (AllWinning.cons node_6896 (AllWinning.cons node_6004 (AllWinning.cons node_5290 (AllWinning.cons node_4563 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19467 : Outcome ⟨15, 2, 15, 2⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 4⟩) (by decide) node_17690

theorem node_19468 : Outcome ⟨15, 2, 15, 4⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 4⟩) (by decide) node_17690

theorem node_19469 : Outcome ⟨15, 2, 15, 6⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 12⟩) (by decide) node_13500

theorem node_19470 : Outcome ⟨15, 2, 15, 16⟩ true :=
  Outcome.win (q := ⟨9, 2, 15, 12⟩) (by decide) node_13500

theorem node_19471 : Outcome ⟨15, 3, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 3, 12, 4⟩) (by decide) node_17702

theorem node_19472 : Outcome ⟨15, 3, 14, 4⟩ true :=
  Outcome.win (q := ⟨15, 3, 12, 4⟩) (by decide) node_17702

theorem node_19473 : Outcome ⟨15, 3, 14, 8⟩ true :=
  Outcome.win (q := ⟨15, 3, 12, 4⟩) (by decide) node_17702

theorem node_19474 : Outcome ⟨15, 3, 14, 10⟩ true :=
  Outcome.win (q := ⟨15, 3, 12, 4⟩) (by decide) node_17702

theorem node_19475 : Outcome ⟨15, 4, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 13, 2⟩, ⟨13, 4, 13, 4⟩, ⟨15, 3, 13, 2⟩, ⟨15, 2, 13, 4⟩, ⟨15, 4, 12, 2⟩, ⟨15, 4, 11, 4⟩]
  exact AllWinning.cons node_18556 (AllWinning.cons node_17588 (AllWinning.cons node_18607 (AllWinning.cons node_17700 (AllWinning.cons node_18611 (AllWinning.cons node_17706 (AllWinning.nil))))))

theorem node_19476 : Outcome ⟨15, 4, 13, 4⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 6⟩) (by decide) node_16617

theorem node_19477 : Outcome ⟨15, 4, 13, 8⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 6⟩) (by decide) node_16617

theorem node_19478 : Outcome ⟨15, 4, 13, 10⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 6⟩) (by decide) node_16617

theorem node_19479 : Outcome ⟨15, 5, 12, 4⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 8⟩) (by decide) node_15747

theorem node_19480 : Outcome ⟨15, 5, 12, 6⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 8⟩) (by decide) node_15747

theorem node_19481 : Outcome ⟨15, 6, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 6, 11, 2⟩, ⟨13, 6, 11, 4⟩, ⟨15, 5, 11, 2⟩, ⟨15, 4, 11, 4⟩, ⟨15, 6, 10, 2⟩, ⟨15, 6, 9, 4⟩]
  exact AllWinning.cons node_18564 (AllWinning.cons node_17594 (AllWinning.cons node_18614 (AllWinning.cons node_17706 (AllWinning.cons node_18617 (AllWinning.cons node_17712 (AllWinning.nil))))))

theorem node_19482 : Outcome ⟨15, 6, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 6, 11, 2⟩, ⟨13, 6, 11, 4⟩, ⟨12, 6, 11, 6⟩, ⟨11, 6, 11, 8⟩, ⟨15, 5, 11, 2⟩, ⟨15, 4, 11, 4⟩, ⟨15, 3, 11, 6⟩, ⟨15, 2, 11, 8⟩, ⟨15, 6, 10, 2⟩, ⟨15, 6, 9, 4⟩, ⟨15, 6, 8, 6⟩, ⟨15, 6, 7, 8⟩]
  exact AllWinning.cons node_18564 (AllWinning.cons node_17594 (AllWinning.cons node_16625 (AllWinning.cons node_15527 (AllWinning.cons node_18614 (AllWinning.cons node_17706 (AllWinning.cons node_16787 (AllWinning.cons node_15738 (AllWinning.cons node_18617 (AllWinning.cons node_17712 (AllWinning.cons node_16795 (AllWinning.cons node_15756 (AllWinning.nil))))))))))))

theorem node_19483 : Outcome ⟨15, 6, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 6, 11, 2⟩, ⟨13, 6, 11, 4⟩, ⟨12, 6, 11, 6⟩, ⟨11, 6, 11, 8⟩, ⟨10, 6, 11, 10⟩, ⟨9, 6, 11, 12⟩, ⟨15, 5, 11, 2⟩, ⟨15, 4, 11, 4⟩, ⟨15, 3, 11, 6⟩, ⟨15, 2, 11, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 0, 11, 12⟩, ⟨15, 6, 10, 2⟩, ⟨15, 6, 9, 4⟩, ⟨15, 6, 8, 6⟩, ⟨15, 6, 7, 8⟩, ⟨15, 6, 6, 10⟩, ⟨15, 6, 5, 12⟩]
  exact AllWinning.cons node_18564 (AllWinning.cons node_17594 (AllWinning.cons node_16625 (AllWinning.cons node_15527 (AllWinning.cons node_14535 (AllWinning.cons node_13511 (AllWinning.cons node_18614 (AllWinning.cons node_17706 (AllWinning.cons node_16787 (AllWinning.cons node_15738 (AllWinning.cons node_14756 (AllWinning.cons node_13800 (AllWinning.cons node_18617 (AllWinning.cons node_17712 (AllWinning.cons node_16795 (AllWinning.cons node_15756 (AllWinning.cons node_14768 (AllWinning.cons node_13821 (AllWinning.nil))))))))))))))))))

theorem node_19484 : Outcome ⟨15, 6, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 6, 11, 2⟩, ⟨13, 6, 11, 4⟩, ⟨12, 6, 11, 6⟩, ⟨11, 6, 11, 8⟩, ⟨10, 6, 11, 10⟩, ⟨9, 6, 11, 12⟩, ⟨8, 6, 11, 14⟩, ⟨7, 6, 11, 16⟩, ⟨15, 5, 11, 2⟩, ⟨15, 4, 11, 4⟩, ⟨15, 3, 11, 6⟩, ⟨15, 2, 11, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 0, 11, 12⟩, ⟨15, 6, 10, 2⟩, ⟨15, 6, 9, 4⟩, ⟨15, 6, 8, 6⟩, ⟨15, 6, 7, 8⟩, ⟨15, 6, 6, 10⟩, ⟨15, 6, 5, 12⟩, ⟨15, 6, 4, 14⟩, ⟨15, 6, 3, 16⟩]
  exact AllWinning.cons node_18564 (AllWinning.cons node_17594 (AllWinning.cons node_16625 (AllWinning.cons node_15527 (AllWinning.cons node_14535 (AllWinning.cons node_13511 (AllWinning.cons node_12508 (AllWinning.cons node_11455 (AllWinning.cons node_18614 (AllWinning.cons node_17706 (AllWinning.cons node_16787 (AllWinning.cons node_15738 (AllWinning.cons node_14756 (AllWinning.cons node_13800 (AllWinning.cons node_18617 (AllWinning.cons node_17712 (AllWinning.cons node_16795 (AllWinning.cons node_15756 (AllWinning.cons node_14768 (AllWinning.cons node_13821 (AllWinning.cons node_12846 (AllWinning.cons node_11856 (AllWinning.nil))))))))))))))))))))))

theorem node_19485 : Outcome ⟨15, 6, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 6, 11, 2⟩, ⟨13, 6, 11, 4⟩, ⟨12, 6, 11, 6⟩, ⟨11, 6, 11, 8⟩, ⟨10, 6, 11, 10⟩, ⟨9, 6, 11, 12⟩, ⟨8, 6, 11, 14⟩, ⟨7, 6, 11, 16⟩, ⟨6, 6, 11, 18⟩, ⟨5, 6, 11, 20⟩, ⟨4, 6, 11, 22⟩, ⟨3, 6, 11, 24⟩, ⟨15, 5, 11, 2⟩, ⟨15, 4, 11, 4⟩, ⟨15, 3, 11, 6⟩, ⟨15, 2, 11, 8⟩, ⟨15, 1, 11, 10⟩, ⟨15, 0, 11, 12⟩, ⟨15, 6, 10, 2⟩, ⟨15, 6, 9, 4⟩, ⟨15, 6, 8, 6⟩, ⟨15, 6, 7, 8⟩, ⟨15, 6, 6, 10⟩, ⟨15, 6, 5, 12⟩, ⟨15, 6, 4, 14⟩, ⟨15, 6, 3, 16⟩, ⟨15, 6, 2, 18⟩, ⟨15, 6, 1, 20⟩, ⟨15, 6, 0, 22⟩]
  exact AllWinning.cons node_18564 (AllWinning.cons node_17594 (AllWinning.cons node_16625 (AllWinning.cons node_15527 (AllWinning.cons node_14535 (AllWinning.cons node_13511 (AllWinning.cons node_12508 (AllWinning.cons node_11455 (AllWinning.cons node_10365 (AllWinning.cons node_9293 (AllWinning.cons node_8245 (AllWinning.cons node_7222 (AllWinning.cons node_18614 (AllWinning.cons node_17706 (AllWinning.cons node_16787 (AllWinning.cons node_15738 (AllWinning.cons node_14756 (AllWinning.cons node_13800 (AllWinning.cons node_18617 (AllWinning.cons node_17712 (AllWinning.cons node_16795 (AllWinning.cons node_15756 (AllWinning.cons node_14768 (AllWinning.cons node_13821 (AllWinning.cons node_12846 (AllWinning.cons node_11856 (AllWinning.cons node_10860 (AllWinning.cons node_9793 (AllWinning.cons node_8848 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19486 : Outcome ⟨15, 7, 10, 2⟩ true :=
  Outcome.win (q := ⟨14, 7, 10, 2⟩) (by decide) node_18566

theorem node_19487 : Outcome ⟨15, 7, 10, 4⟩ true :=
  Outcome.win (q := ⟨14, 7, 10, 2⟩) (by decide) node_18566

theorem node_19488 : Outcome ⟨15, 7, 10, 16⟩ true :=
  Outcome.win (q := ⟨14, 7, 10, 2⟩) (by decide) node_18566

theorem node_19489 : Outcome ⟨15, 8, 9, 2⟩ true :=
  Outcome.win (q := ⟨14, 8, 9, 2⟩) (by decide) node_18569

theorem node_19490 : Outcome ⟨15, 8, 9, 10⟩ true :=
  Outcome.win (q := ⟨15, 2, 9, 12⟩) (by decide) node_13808

theorem node_19491 : Outcome ⟨15, 9, 8, 2⟩ true :=
  Outcome.win (q := ⟨14, 9, 8, 2⟩) (by decide) node_18572

theorem node_19492 : Outcome ⟨15, 9, 8, 10⟩ true :=
  Outcome.win (q := ⟨15, 9, 2, 12⟩) (by decide) node_13832

theorem node_19493 : Outcome ⟨15, 10, 7, 2⟩ true :=
  Outcome.win (q := ⟨14, 10, 7, 2⟩) (by decide) node_18575

theorem node_19494 : Outcome ⟨15, 10, 7, 4⟩ true :=
  Outcome.win (q := ⟨14, 10, 7, 2⟩) (by decide) node_18575

theorem node_19495 : Outcome ⟨15, 10, 7, 16⟩ true :=
  Outcome.win (q := ⟨14, 10, 7, 2⟩) (by decide) node_18575

theorem node_19496 : Outcome ⟨15, 11, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 6, 2⟩, ⟨13, 11, 6, 4⟩, ⟨15, 10, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨15, 11, 5, 2⟩, ⟨15, 11, 4, 4⟩]
  exact AllWinning.cons node_18578 (AllWinning.cons node_17610 (AllWinning.cons node_18632 (AllWinning.cons node_17723 (AllWinning.cons node_18635 (AllWinning.cons node_17728 (AllWinning.nil))))))

theorem node_19497 : Outcome ⟨15, 11, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 6, 2⟩, ⟨13, 11, 6, 4⟩, ⟨12, 11, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨15, 10, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨15, 8, 6, 6⟩, ⟨15, 7, 6, 8⟩, ⟨15, 11, 5, 2⟩, ⟨15, 11, 4, 4⟩, ⟨15, 11, 3, 6⟩, ⟨15, 11, 2, 8⟩]
  exact AllWinning.cons node_18578 (AllWinning.cons node_17610 (AllWinning.cons node_16636 (AllWinning.cons node_15540 (AllWinning.cons node_18632 (AllWinning.cons node_17723 (AllWinning.cons node_16800 (AllWinning.cons node_15760 (AllWinning.cons node_18635 (AllWinning.cons node_17728 (AllWinning.cons node_16806 (AllWinning.cons node_15778 (AllWinning.nil))))))))))))

theorem node_19498 : Outcome ⟨15, 11, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 6, 2⟩, ⟨13, 11, 6, 4⟩, ⟨12, 11, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨10, 11, 6, 10⟩, ⟨9, 11, 6, 12⟩, ⟨15, 10, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨15, 8, 6, 6⟩, ⟨15, 7, 6, 8⟩, ⟨15, 6, 6, 10⟩, ⟨15, 5, 6, 12⟩, ⟨15, 11, 5, 2⟩, ⟨15, 11, 4, 4⟩, ⟨15, 11, 3, 6⟩, ⟨15, 11, 2, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 11, 0, 12⟩]
  exact AllWinning.cons node_18578 (AllWinning.cons node_17610 (AllWinning.cons node_16636 (AllWinning.cons node_15540 (AllWinning.cons node_14550 (AllWinning.cons node_13524 (AllWinning.cons node_18632 (AllWinning.cons node_17723 (AllWinning.cons node_16800 (AllWinning.cons node_15760 (AllWinning.cons node_14768 (AllWinning.cons node_13818 (AllWinning.cons node_18635 (AllWinning.cons node_17728 (AllWinning.cons node_16806 (AllWinning.cons node_15778 (AllWinning.cons node_14782 (AllWinning.cons node_13838 (AllWinning.nil))))))))))))))))))

theorem node_19499 : Outcome ⟨15, 11, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 6, 2⟩, ⟨13, 11, 6, 4⟩, ⟨12, 11, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨10, 11, 6, 10⟩, ⟨9, 11, 6, 12⟩, ⟨8, 11, 6, 14⟩, ⟨7, 11, 6, 16⟩, ⟨15, 10, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨15, 8, 6, 6⟩, ⟨15, 7, 6, 8⟩, ⟨15, 6, 6, 10⟩, ⟨15, 5, 6, 12⟩, ⟨15, 4, 6, 14⟩, ⟨15, 3, 6, 16⟩, ⟨15, 11, 5, 2⟩, ⟨15, 11, 4, 4⟩, ⟨15, 11, 3, 6⟩, ⟨15, 11, 2, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 11, 0, 12⟩]
  exact AllWinning.cons node_18578 (AllWinning.cons node_17610 (AllWinning.cons node_16636 (AllWinning.cons node_15540 (AllWinning.cons node_14550 (AllWinning.cons node_13524 (AllWinning.cons node_12526 (AllWinning.cons node_11471 (AllWinning.cons node_18632 (AllWinning.cons node_17723 (AllWinning.cons node_16800 (AllWinning.cons node_15760 (AllWinning.cons node_14768 (AllWinning.cons node_13818 (AllWinning.cons node_12842 (AllWinning.cons node_11847 (AllWinning.cons node_18635 (AllWinning.cons node_17728 (AllWinning.cons node_16806 (AllWinning.cons node_15778 (AllWinning.cons node_14782 (AllWinning.cons node_13838 (AllWinning.nil))))))))))))))))))))))

theorem node_19500 : Outcome ⟨15, 11, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 6, 2⟩, ⟨13, 11, 6, 4⟩, ⟨12, 11, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨10, 11, 6, 10⟩, ⟨9, 11, 6, 12⟩, ⟨8, 11, 6, 14⟩, ⟨7, 11, 6, 16⟩, ⟨6, 11, 6, 18⟩, ⟨5, 11, 6, 20⟩, ⟨15, 10, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨15, 8, 6, 6⟩, ⟨15, 7, 6, 8⟩, ⟨15, 6, 6, 10⟩, ⟨15, 5, 6, 12⟩, ⟨15, 4, 6, 14⟩, ⟨15, 3, 6, 16⟩, ⟨15, 2, 6, 18⟩, ⟨15, 1, 6, 20⟩, ⟨15, 11, 5, 2⟩, ⟨15, 11, 4, 4⟩, ⟨15, 11, 3, 6⟩, ⟨15, 11, 2, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 11, 0, 12⟩]
  exact AllWinning.cons node_18578 (AllWinning.cons node_17610 (AllWinning.cons node_16636 (AllWinning.cons node_15540 (AllWinning.cons node_14550 (AllWinning.cons node_13524 (AllWinning.cons node_12526 (AllWinning.cons node_11471 (AllWinning.cons node_10387 (AllWinning.cons node_9314 (AllWinning.cons node_18632 (AllWinning.cons node_17723 (AllWinning.cons node_16800 (AllWinning.cons node_15760 (AllWinning.cons node_14768 (AllWinning.cons node_13818 (AllWinning.cons node_12842 (AllWinning.cons node_11847 (AllWinning.cons node_10846 (AllWinning.cons node_9775 (AllWinning.cons node_18635 (AllWinning.cons node_17728 (AllWinning.cons node_16806 (AllWinning.cons node_15778 (AllWinning.cons node_14782 (AllWinning.cons node_13838 (AllWinning.nil))))))))))))))))))))))))))

theorem node_19501 : Outcome ⟨15, 11, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 6, 2⟩, ⟨13, 11, 6, 4⟩, ⟨12, 11, 6, 6⟩, ⟨11, 11, 6, 8⟩, ⟨10, 11, 6, 10⟩, ⟨9, 11, 6, 12⟩, ⟨8, 11, 6, 14⟩, ⟨7, 11, 6, 16⟩, ⟨6, 11, 6, 18⟩, ⟨5, 11, 6, 20⟩, ⟨4, 11, 6, 22⟩, ⟨3, 11, 6, 24⟩, ⟨15, 10, 6, 2⟩, ⟨15, 9, 6, 4⟩, ⟨15, 8, 6, 6⟩, ⟨15, 7, 6, 8⟩, ⟨15, 6, 6, 10⟩, ⟨15, 5, 6, 12⟩, ⟨15, 4, 6, 14⟩, ⟨15, 3, 6, 16⟩, ⟨15, 2, 6, 18⟩, ⟨15, 1, 6, 20⟩, ⟨15, 0, 6, 22⟩, ⟨15, 11, 5, 2⟩, ⟨15, 11, 4, 4⟩, ⟨15, 11, 3, 6⟩, ⟨15, 11, 2, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 11, 0, 12⟩]
  exact AllWinning.cons node_18578 (AllWinning.cons node_17610 (AllWinning.cons node_16636 (AllWinning.cons node_15540 (AllWinning.cons node_14550 (AllWinning.cons node_13524 (AllWinning.cons node_12526 (AllWinning.cons node_11471 (AllWinning.cons node_10387 (AllWinning.cons node_9314 (AllWinning.cons node_8261 (AllWinning.cons node_7245 (AllWinning.cons node_18632 (AllWinning.cons node_17723 (AllWinning.cons node_16800 (AllWinning.cons node_15760 (AllWinning.cons node_14768 (AllWinning.cons node_13818 (AllWinning.cons node_12842 (AllWinning.cons node_11847 (AllWinning.cons node_10846 (AllWinning.cons node_9775 (AllWinning.cons node_8825 (AllWinning.cons node_18635 (AllWinning.cons node_17728 (AllWinning.cons node_16806 (AllWinning.cons node_15778 (AllWinning.cons node_14782 (AllWinning.cons node_13838 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19502 : Outcome ⟨15, 12, 5, 4⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 8⟩) (by decide) node_15764

theorem node_19503 : Outcome ⟨15, 12, 5, 6⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 8⟩) (by decide) node_15764

theorem node_19504 : Outcome ⟨15, 13, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 13, 4, 2⟩, ⟨13, 13, 4, 4⟩, ⟨15, 12, 4, 2⟩, ⟨15, 11, 4, 4⟩, ⟨15, 13, 3, 2⟩, ⟨15, 13, 2, 4⟩]
  exact AllWinning.cons node_18584 (AllWinning.cons node_17616 (AllWinning.cons node_18638 (AllWinning.cons node_17728 (AllWinning.cons node_18641 (AllWinning.cons node_17736 (AllWinning.nil))))))

theorem node_19505 : Outcome ⟨15, 13, 4, 4⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 6⟩) (by decide) node_16643

theorem node_19506 : Outcome ⟨15, 13, 4, 8⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 6⟩) (by decide) node_16643

theorem node_19507 : Outcome ⟨15, 13, 4, 10⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 6⟩) (by decide) node_16643

theorem node_19508 : Outcome ⟨15, 14, 3, 2⟩ true :=
  Outcome.win (q := ⟨15, 12, 3, 4⟩) (by decide) node_17732

theorem node_19509 : Outcome ⟨15, 14, 3, 4⟩ true :=
  Outcome.win (q := ⟨15, 12, 3, 4⟩) (by decide) node_17732

theorem node_19510 : Outcome ⟨15, 14, 3, 8⟩ true :=
  Outcome.win (q := ⟨15, 12, 3, 4⟩) (by decide) node_17732

theorem node_19511 : Outcome ⟨15, 14, 3, 10⟩ true :=
  Outcome.win (q := ⟨15, 12, 3, 4⟩) (by decide) node_17732

theorem node_19512 : Outcome ⟨15, 15, 2, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 4⟩) (by decide) node_17742

theorem node_19513 : Outcome ⟨15, 15, 2, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 4⟩) (by decide) node_17742

theorem node_19514 : Outcome ⟨15, 15, 2, 6⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 12⟩) (by decide) node_13537

theorem node_19515 : Outcome ⟨15, 15, 2, 16⟩ true :=
  Outcome.win (q := ⟨9, 15, 2, 12⟩) (by decide) node_13537

theorem node_19516 : Outcome ⟨15, 16, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_18650 (AllWinning.nil)))))

theorem node_19517 : Outcome ⟨15, 16, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_18650 (AllWinning.nil)))))))))

theorem node_19518 : Outcome ⟨15, 16, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨10, 16, 1, 10⟩, ⟨9, 16, 1, 12⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 10, 1, 12⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_14568 (AllWinning.cons node_13540 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_14782 (AllWinning.cons node_13835 (AllWinning.cons node_18650 (AllWinning.nil)))))))))))))

theorem node_19519 : Outcome ⟨15, 16, 1, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨10, 16, 1, 10⟩, ⟨9, 16, 1, 12⟩, ⟨8, 16, 1, 14⟩, ⟨7, 16, 1, 16⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 10, 1, 12⟩, ⟨15, 9, 1, 14⟩, ⟨15, 8, 1, 16⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_14568 (AllWinning.cons node_13540 (AllWinning.cons node_12541 (AllWinning.cons node_11489 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_14782 (AllWinning.cons node_13835 (AllWinning.cons node_12861 (AllWinning.cons node_11864 (AllWinning.cons node_18650 (AllWinning.nil)))))))))))))))))

theorem node_19520 : Outcome ⟨15, 16, 1, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨10, 16, 1, 10⟩, ⟨9, 16, 1, 12⟩, ⟨8, 16, 1, 14⟩, ⟨7, 16, 1, 16⟩, ⟨6, 16, 1, 18⟩, ⟨5, 16, 1, 20⟩, ⟨4, 16, 1, 22⟩, ⟨3, 16, 1, 24⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 10, 1, 12⟩, ⟨15, 9, 1, 14⟩, ⟨15, 8, 1, 16⟩, ⟨15, 7, 1, 18⟩, ⟨15, 6, 1, 20⟩, ⟨15, 5, 1, 22⟩, ⟨15, 4, 1, 24⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_14568 (AllWinning.cons node_13540 (AllWinning.cons node_12541 (AllWinning.cons node_11489 (AllWinning.cons node_10411 (AllWinning.cons node_9331 (AllWinning.cons node_8280 (AllWinning.cons node_7264 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_14782 (AllWinning.cons node_13835 (AllWinning.cons node_12861 (AllWinning.cons node_11864 (AllWinning.cons node_10863 (AllWinning.cons node_9793 (AllWinning.cons node_8844 (AllWinning.cons node_7851 (AllWinning.cons node_18650 (AllWinning.nil)))))))))))))))))))))))))

theorem node_19521 : Outcome ⟨15, 16, 1, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨10, 16, 1, 10⟩, ⟨9, 16, 1, 12⟩, ⟨8, 16, 1, 14⟩, ⟨7, 16, 1, 16⟩, ⟨6, 16, 1, 18⟩, ⟨5, 16, 1, 20⟩, ⟨4, 16, 1, 22⟩, ⟨3, 16, 1, 24⟩, ⟨2, 16, 1, 26⟩, ⟨1, 16, 1, 28⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 10, 1, 12⟩, ⟨15, 9, 1, 14⟩, ⟨15, 8, 1, 16⟩, ⟨15, 7, 1, 18⟩, ⟨15, 6, 1, 20⟩, ⟨15, 5, 1, 22⟩, ⟨15, 4, 1, 24⟩, ⟨15, 3, 1, 26⟩, ⟨15, 2, 1, 28⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_14568 (AllWinning.cons node_13540 (AllWinning.cons node_12541 (AllWinning.cons node_11489 (AllWinning.cons node_10411 (AllWinning.cons node_9331 (AllWinning.cons node_8280 (AllWinning.cons node_7264 (AllWinning.cons node_6268 (AllWinning.cons node_5452 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_14782 (AllWinning.cons node_13835 (AllWinning.cons node_12861 (AllWinning.cons node_11864 (AllWinning.cons node_10863 (AllWinning.cons node_9793 (AllWinning.cons node_8844 (AllWinning.cons node_7851 (AllWinning.cons node_6903 (AllWinning.cons node_6008 (AllWinning.cons node_18650 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19522 : Outcome ⟨15, 16, 1, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨10, 16, 1, 10⟩, ⟨9, 16, 1, 12⟩, ⟨8, 16, 1, 14⟩, ⟨7, 16, 1, 16⟩, ⟨6, 16, 1, 18⟩, ⟨5, 16, 1, 20⟩, ⟨4, 16, 1, 22⟩, ⟨3, 16, 1, 24⟩, ⟨2, 16, 1, 26⟩, ⟨1, 16, 1, 28⟩, ⟨0, 16, 1, 30⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 10, 1, 12⟩, ⟨15, 9, 1, 14⟩, ⟨15, 8, 1, 16⟩, ⟨15, 7, 1, 18⟩, ⟨15, 6, 1, 20⟩, ⟨15, 5, 1, 22⟩, ⟨15, 4, 1, 24⟩, ⟨15, 3, 1, 26⟩, ⟨15, 2, 1, 28⟩, ⟨15, 1, 1, 30⟩, ⟨15, 0, 1, 32⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_14568 (AllWinning.cons node_13540 (AllWinning.cons node_12541 (AllWinning.cons node_11489 (AllWinning.cons node_10411 (AllWinning.cons node_9331 (AllWinning.cons node_8280 (AllWinning.cons node_7264 (AllWinning.cons node_6268 (AllWinning.cons node_5452 (AllWinning.cons node_4645 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_14782 (AllWinning.cons node_13835 (AllWinning.cons node_12861 (AllWinning.cons node_11864 (AllWinning.cons node_10863 (AllWinning.cons node_9793 (AllWinning.cons node_8844 (AllWinning.cons node_7851 (AllWinning.cons node_6903 (AllWinning.cons node_6008 (AllWinning.cons node_5290 (AllWinning.cons node_4559 (AllWinning.cons node_18650 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19523 : Outcome ⟨15, 16, 1, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨10, 16, 1, 10⟩, ⟨9, 16, 1, 12⟩, ⟨8, 16, 1, 14⟩, ⟨7, 16, 1, 16⟩, ⟨6, 16, 1, 18⟩, ⟨5, 16, 1, 20⟩, ⟨4, 16, 1, 22⟩, ⟨3, 16, 1, 24⟩, ⟨2, 16, 1, 26⟩, ⟨1, 16, 1, 28⟩, ⟨0, 16, 1, 30⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 10, 1, 12⟩, ⟨15, 9, 1, 14⟩, ⟨15, 8, 1, 16⟩, ⟨15, 7, 1, 18⟩, ⟨15, 6, 1, 20⟩, ⟨15, 5, 1, 22⟩, ⟨15, 4, 1, 24⟩, ⟨15, 3, 1, 26⟩, ⟨15, 2, 1, 28⟩, ⟨15, 1, 1, 30⟩, ⟨15, 0, 1, 32⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_14568 (AllWinning.cons node_13540 (AllWinning.cons node_12541 (AllWinning.cons node_11489 (AllWinning.cons node_10411 (AllWinning.cons node_9331 (AllWinning.cons node_8280 (AllWinning.cons node_7264 (AllWinning.cons node_6268 (AllWinning.cons node_5452 (AllWinning.cons node_4645 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_14782 (AllWinning.cons node_13835 (AllWinning.cons node_12861 (AllWinning.cons node_11864 (AllWinning.cons node_10863 (AllWinning.cons node_9793 (AllWinning.cons node_8844 (AllWinning.cons node_7851 (AllWinning.cons node_6903 (AllWinning.cons node_6008 (AllWinning.cons node_5290 (AllWinning.cons node_4559 (AllWinning.cons node_18650 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19524 : Outcome ⟨15, 16, 1, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 16, 1, 2⟩, ⟨13, 16, 1, 4⟩, ⟨12, 16, 1, 6⟩, ⟨11, 16, 1, 8⟩, ⟨10, 16, 1, 10⟩, ⟨9, 16, 1, 12⟩, ⟨8, 16, 1, 14⟩, ⟨7, 16, 1, 16⟩, ⟨6, 16, 1, 18⟩, ⟨5, 16, 1, 20⟩, ⟨4, 16, 1, 22⟩, ⟨3, 16, 1, 24⟩, ⟨2, 16, 1, 26⟩, ⟨1, 16, 1, 28⟩, ⟨0, 16, 1, 30⟩, ⟨15, 15, 1, 2⟩, ⟨15, 14, 1, 4⟩, ⟨15, 13, 1, 6⟩, ⟨15, 12, 1, 8⟩, ⟨15, 11, 1, 10⟩, ⟨15, 10, 1, 12⟩, ⟨15, 9, 1, 14⟩, ⟨15, 8, 1, 16⟩, ⟨15, 7, 1, 18⟩, ⟨15, 6, 1, 20⟩, ⟨15, 5, 1, 22⟩, ⟨15, 4, 1, 24⟩, ⟨15, 3, 1, 26⟩, ⟨15, 2, 1, 28⟩, ⟨15, 1, 1, 30⟩, ⟨15, 0, 1, 32⟩, ⟨15, 16, 0, 2⟩]
  exact AllWinning.cons node_18595 (AllWinning.cons node_17627 (AllWinning.cons node_16655 (AllWinning.cons node_15553 (AllWinning.cons node_14568 (AllWinning.cons node_13540 (AllWinning.cons node_12541 (AllWinning.cons node_11489 (AllWinning.cons node_10411 (AllWinning.cons node_9331 (AllWinning.cons node_8280 (AllWinning.cons node_7264 (AllWinning.cons node_6268 (AllWinning.cons node_5452 (AllWinning.cons node_4645 (AllWinning.cons node_18647 (AllWinning.cons node_17738 (AllWinning.cons node_16813 (AllWinning.cons node_15781 (AllWinning.cons node_14782 (AllWinning.cons node_13835 (AllWinning.cons node_12861 (AllWinning.cons node_11864 (AllWinning.cons node_10863 (AllWinning.cons node_9793 (AllWinning.cons node_8844 (AllWinning.cons node_7851 (AllWinning.cons node_6903 (AllWinning.cons node_6008 (AllWinning.cons node_5290 (AllWinning.cons node_4559 (AllWinning.cons node_18650 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19525 : Outcome ⟨15, 17, 0, 4⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 4⟩) (by decide) node_17742

theorem node_19526 : Outcome ⟨15, 17, 0, 6⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 4⟩) (by decide) node_17742

theorem node_19527 : Outcome ⟨15, 17, 0, 8⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 4⟩) (by decide) node_17742

theorem node_19528 : Outcome ⟨16, 0, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨16, 0, 15, 2⟩, ⟨16, 0, 14, 4⟩]
  exact AllWinning.cons node_18600 (AllWinning.cons node_17630 (AllWinning.cons node_18652 (AllWinning.cons node_17747 (AllWinning.nil))))

theorem node_19529 : Outcome ⟨16, 0, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨13, 0, 16, 6⟩, ⟨12, 0, 16, 8⟩, ⟨16, 0, 15, 2⟩, ⟨16, 0, 14, 4⟩, ⟨16, 0, 13, 6⟩, ⟨16, 0, 12, 8⟩]
  exact AllWinning.cons node_18600 (AllWinning.cons node_17630 (AllWinning.cons node_16662 (AllWinning.cons node_15559 (AllWinning.cons node_18652 (AllWinning.cons node_17747 (AllWinning.cons node_16818 (AllWinning.cons node_15786 (AllWinning.nil))))))))

theorem node_19530 : Outcome ⟨16, 0, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨13, 0, 16, 6⟩, ⟨12, 0, 16, 8⟩, ⟨11, 0, 16, 10⟩, ⟨10, 0, 16, 12⟩, ⟨16, 0, 15, 2⟩, ⟨16, 0, 14, 4⟩, ⟨16, 0, 13, 6⟩, ⟨16, 0, 12, 8⟩, ⟨16, 0, 11, 10⟩, ⟨16, 0, 10, 12⟩]
  exact AllWinning.cons node_18600 (AllWinning.cons node_17630 (AllWinning.cons node_16662 (AllWinning.cons node_15559 (AllWinning.cons node_14576 (AllWinning.cons node_13548 (AllWinning.cons node_18652 (AllWinning.cons node_17747 (AllWinning.cons node_16818 (AllWinning.cons node_15786 (AllWinning.cons node_14789 (AllWinning.cons node_13841 (AllWinning.nil))))))))))))

theorem node_19531 : Outcome ⟨16, 0, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨13, 0, 16, 6⟩, ⟨12, 0, 16, 8⟩, ⟨11, 0, 16, 10⟩, ⟨10, 0, 16, 12⟩, ⟨9, 0, 16, 14⟩, ⟨8, 0, 16, 16⟩, ⟨7, 0, 16, 18⟩, ⟨6, 0, 16, 20⟩, ⟨16, 0, 15, 2⟩, ⟨16, 0, 14, 4⟩, ⟨16, 0, 13, 6⟩, ⟨16, 0, 12, 8⟩, ⟨16, 0, 11, 10⟩, ⟨16, 0, 10, 12⟩, ⟨16, 0, 9, 14⟩, ⟨16, 0, 8, 16⟩, ⟨16, 0, 7, 18⟩, ⟨16, 0, 6, 20⟩]
  exact AllWinning.cons node_18600 (AllWinning.cons node_17630 (AllWinning.cons node_16662 (AllWinning.cons node_15559 (AllWinning.cons node_14576 (AllWinning.cons node_13548 (AllWinning.cons node_12548 (AllWinning.cons node_11499 (AllWinning.cons node_10418 (AllWinning.cons node_9338 (AllWinning.cons node_18652 (AllWinning.cons node_17747 (AllWinning.cons node_16818 (AllWinning.cons node_15786 (AllWinning.cons node_14789 (AllWinning.cons node_13841 (AllWinning.cons node_12869 (AllWinning.cons node_11871 (AllWinning.cons node_10872 (AllWinning.cons node_9802 (AllWinning.nil))))))))))))))))))))

theorem node_19532 : Outcome ⟨16, 0, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨13, 0, 16, 6⟩, ⟨12, 0, 16, 8⟩, ⟨11, 0, 16, 10⟩, ⟨10, 0, 16, 12⟩, ⟨9, 0, 16, 14⟩, ⟨8, 0, 16, 16⟩, ⟨7, 0, 16, 18⟩, ⟨6, 0, 16, 20⟩, ⟨5, 0, 16, 22⟩, ⟨4, 0, 16, 24⟩, ⟨16, 0, 15, 2⟩, ⟨16, 0, 14, 4⟩, ⟨16, 0, 13, 6⟩, ⟨16, 0, 12, 8⟩, ⟨16, 0, 11, 10⟩, ⟨16, 0, 10, 12⟩, ⟨16, 0, 9, 14⟩, ⟨16, 0, 8, 16⟩, ⟨16, 0, 7, 18⟩, ⟨16, 0, 6, 20⟩, ⟨16, 0, 5, 22⟩, ⟨16, 0, 4, 24⟩]
  exact AllWinning.cons node_18600 (AllWinning.cons node_17630 (AllWinning.cons node_16662 (AllWinning.cons node_15559 (AllWinning.cons node_14576 (AllWinning.cons node_13548 (AllWinning.cons node_12548 (AllWinning.cons node_11499 (AllWinning.cons node_10418 (AllWinning.cons node_9338 (AllWinning.cons node_8289 (AllWinning.cons node_7269 (AllWinning.cons node_18652 (AllWinning.cons node_17747 (AllWinning.cons node_16818 (AllWinning.cons node_15786 (AllWinning.cons node_14789 (AllWinning.cons node_13841 (AllWinning.cons node_12869 (AllWinning.cons node_11871 (AllWinning.cons node_10872 (AllWinning.cons node_9802 (AllWinning.cons node_8851 (AllWinning.cons node_7859 (AllWinning.nil))))))))))))))))))))))))

theorem node_19533 : Outcome ⟨16, 0, 16, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨13, 0, 16, 6⟩, ⟨12, 0, 16, 8⟩, ⟨11, 0, 16, 10⟩, ⟨10, 0, 16, 12⟩, ⟨9, 0, 16, 14⟩, ⟨8, 0, 16, 16⟩, ⟨7, 0, 16, 18⟩, ⟨6, 0, 16, 20⟩, ⟨5, 0, 16, 22⟩, ⟨4, 0, 16, 24⟩, ⟨3, 0, 16, 26⟩, ⟨2, 0, 16, 28⟩, ⟨16, 0, 15, 2⟩, ⟨16, 0, 14, 4⟩, ⟨16, 0, 13, 6⟩, ⟨16, 0, 12, 8⟩, ⟨16, 0, 11, 10⟩, ⟨16, 0, 10, 12⟩, ⟨16, 0, 9, 14⟩, ⟨16, 0, 8, 16⟩, ⟨16, 0, 7, 18⟩, ⟨16, 0, 6, 20⟩, ⟨16, 0, 5, 22⟩, ⟨16, 0, 4, 24⟩, ⟨16, 0, 3, 26⟩, ⟨16, 0, 2, 28⟩]
  exact AllWinning.cons node_18600 (AllWinning.cons node_17630 (AllWinning.cons node_16662 (AllWinning.cons node_15559 (AllWinning.cons node_14576 (AllWinning.cons node_13548 (AllWinning.cons node_12548 (AllWinning.cons node_11499 (AllWinning.cons node_10418 (AllWinning.cons node_9338 (AllWinning.cons node_8289 (AllWinning.cons node_7269 (AllWinning.cons node_6279 (AllWinning.cons node_5459 (AllWinning.cons node_18652 (AllWinning.cons node_17747 (AllWinning.cons node_16818 (AllWinning.cons node_15786 (AllWinning.cons node_14789 (AllWinning.cons node_13841 (AllWinning.cons node_12869 (AllWinning.cons node_11871 (AllWinning.cons node_10872 (AllWinning.cons node_9802 (AllWinning.cons node_8851 (AllWinning.cons node_7859 (AllWinning.cons node_6915 (AllWinning.cons node_6016 (AllWinning.nil))))))))))))))))))))))))))))

theorem node_19534 : Outcome ⟨16, 0, 16, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 0, 16, 2⟩, ⟨14, 0, 16, 4⟩, ⟨13, 0, 16, 6⟩, ⟨12, 0, 16, 8⟩, ⟨11, 0, 16, 10⟩, ⟨10, 0, 16, 12⟩, ⟨9, 0, 16, 14⟩, ⟨8, 0, 16, 16⟩, ⟨7, 0, 16, 18⟩, ⟨6, 0, 16, 20⟩, ⟨5, 0, 16, 22⟩, ⟨4, 0, 16, 24⟩, ⟨3, 0, 16, 26⟩, ⟨2, 0, 16, 28⟩, ⟨1, 0, 16, 30⟩, ⟨0, 0, 16, 32⟩, ⟨16, 0, 15, 2⟩, ⟨16, 0, 14, 4⟩, ⟨16, 0, 13, 6⟩, ⟨16, 0, 12, 8⟩, ⟨16, 0, 11, 10⟩, ⟨16, 0, 10, 12⟩, ⟨16, 0, 9, 14⟩, ⟨16, 0, 8, 16⟩, ⟨16, 0, 7, 18⟩, ⟨16, 0, 6, 20⟩, ⟨16, 0, 5, 22⟩, ⟨16, 0, 4, 24⟩, ⟨16, 0, 3, 26⟩, ⟨16, 0, 2, 28⟩, ⟨16, 0, 1, 30⟩, ⟨16, 0, 0, 32⟩]
  exact AllWinning.cons node_18600 (AllWinning.cons node_17630 (AllWinning.cons node_16662 (AllWinning.cons node_15559 (AllWinning.cons node_14576 (AllWinning.cons node_13548 (AllWinning.cons node_12548 (AllWinning.cons node_11499 (AllWinning.cons node_10418 (AllWinning.cons node_9338 (AllWinning.cons node_8289 (AllWinning.cons node_7269 (AllWinning.cons node_6279 (AllWinning.cons node_5459 (AllWinning.cons node_4652 (AllWinning.cons node_3930 (AllWinning.cons node_18652 (AllWinning.cons node_17747 (AllWinning.cons node_16818 (AllWinning.cons node_15786 (AllWinning.cons node_14789 (AllWinning.cons node_13841 (AllWinning.cons node_12869 (AllWinning.cons node_11871 (AllWinning.cons node_10872 (AllWinning.cons node_9802 (AllWinning.cons node_8851 (AllWinning.cons node_7859 (AllWinning.cons node_6915 (AllWinning.cons node_6016 (AllWinning.cons node_5302 (AllWinning.cons node_4567 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19535 : Outcome ⟨16, 1, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 15, 2⟩, ⟨14, 1, 15, 4⟩, ⟨16, 0, 15, 2⟩, ⟨16, 1, 14, 2⟩, ⟨16, 1, 13, 4⟩]
  exact AllWinning.cons node_18602 (AllWinning.cons node_17634 (AllWinning.cons node_18652 (AllWinning.cons node_18653 (AllWinning.cons node_17752 (AllWinning.nil)))))

theorem node_19536 : Outcome ⟨16, 1, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 15, 2⟩, ⟨14, 1, 15, 4⟩, ⟨13, 1, 15, 6⟩, ⟨12, 1, 15, 8⟩, ⟨16, 0, 15, 2⟩, ⟨16, 1, 14, 2⟩, ⟨16, 1, 13, 4⟩, ⟨16, 1, 12, 6⟩, ⟨16, 1, 11, 8⟩]
  exact AllWinning.cons node_18602 (AllWinning.cons node_17634 (AllWinning.cons node_16665 (AllWinning.cons node_15563 (AllWinning.cons node_18652 (AllWinning.cons node_18653 (AllWinning.cons node_17752 (AllWinning.cons node_16821 (AllWinning.cons node_15789 (AllWinning.nil)))))))))

theorem node_19537 : Outcome ⟨16, 1, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 15, 2⟩, ⟨14, 1, 15, 4⟩, ⟨13, 1, 15, 6⟩, ⟨12, 1, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨10, 1, 15, 12⟩, ⟨9, 1, 15, 14⟩, ⟨8, 1, 15, 16⟩, ⟨7, 1, 15, 18⟩, ⟨6, 1, 15, 20⟩, ⟨5, 1, 15, 22⟩, ⟨4, 1, 15, 24⟩, ⟨16, 0, 15, 2⟩, ⟨16, 1, 14, 2⟩, ⟨16, 1, 13, 4⟩, ⟨16, 1, 12, 6⟩, ⟨16, 1, 11, 8⟩, ⟨16, 1, 10, 10⟩, ⟨16, 1, 9, 12⟩, ⟨16, 1, 8, 14⟩, ⟨16, 1, 7, 16⟩, ⟨16, 1, 6, 18⟩, ⟨16, 1, 5, 20⟩, ⟨16, 1, 4, 22⟩, ⟨16, 1, 3, 24⟩]
  exact AllWinning.cons node_18602 (AllWinning.cons node_17634 (AllWinning.cons node_16665 (AllWinning.cons node_15563 (AllWinning.cons node_14581 (AllWinning.cons node_13551 (AllWinning.cons node_12552 (AllWinning.cons node_11503 (AllWinning.cons node_10423 (AllWinning.cons node_9344 (AllWinning.cons node_8294 (AllWinning.cons node_7276 (AllWinning.cons node_18652 (AllWinning.cons node_18653 (AllWinning.cons node_17752 (AllWinning.cons node_16821 (AllWinning.cons node_15789 (AllWinning.cons node_14793 (AllWinning.cons node_13843 (AllWinning.cons node_12872 (AllWinning.cons node_11873 (AllWinning.cons node_10880 (AllWinning.cons node_9806 (AllWinning.cons node_8854 (AllWinning.cons node_7864 (AllWinning.nil)))))))))))))))))))))))))

theorem node_19538 : Outcome ⟨16, 1, 15, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 15, 2⟩, ⟨14, 1, 15, 4⟩, ⟨13, 1, 15, 6⟩, ⟨12, 1, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨10, 1, 15, 12⟩, ⟨9, 1, 15, 14⟩, ⟨8, 1, 15, 16⟩, ⟨7, 1, 15, 18⟩, ⟨6, 1, 15, 20⟩, ⟨5, 1, 15, 22⟩, ⟨4, 1, 15, 24⟩, ⟨3, 1, 15, 26⟩, ⟨2, 1, 15, 28⟩, ⟨16, 0, 15, 2⟩, ⟨16, 1, 14, 2⟩, ⟨16, 1, 13, 4⟩, ⟨16, 1, 12, 6⟩, ⟨16, 1, 11, 8⟩, ⟨16, 1, 10, 10⟩, ⟨16, 1, 9, 12⟩, ⟨16, 1, 8, 14⟩, ⟨16, 1, 7, 16⟩, ⟨16, 1, 6, 18⟩, ⟨16, 1, 5, 20⟩, ⟨16, 1, 4, 22⟩, ⟨16, 1, 3, 24⟩, ⟨16, 1, 2, 26⟩, ⟨16, 1, 1, 28⟩]
  exact AllWinning.cons node_18602 (AllWinning.cons node_17634 (AllWinning.cons node_16665 (AllWinning.cons node_15563 (AllWinning.cons node_14581 (AllWinning.cons node_13551 (AllWinning.cons node_12552 (AllWinning.cons node_11503 (AllWinning.cons node_10423 (AllWinning.cons node_9344 (AllWinning.cons node_8294 (AllWinning.cons node_7276 (AllWinning.cons node_6283 (AllWinning.cons node_5463 (AllWinning.cons node_18652 (AllWinning.cons node_18653 (AllWinning.cons node_17752 (AllWinning.cons node_16821 (AllWinning.cons node_15789 (AllWinning.cons node_14793 (AllWinning.cons node_13843 (AllWinning.cons node_12872 (AllWinning.cons node_11873 (AllWinning.cons node_10880 (AllWinning.cons node_9806 (AllWinning.cons node_8854 (AllWinning.cons node_7864 (AllWinning.cons node_6919 (AllWinning.cons node_6020 (AllWinning.nil)))))))))))))))))))))))))))))

theorem node_19539 : Outcome ⟨16, 1, 15, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 15, 2⟩, ⟨14, 1, 15, 4⟩, ⟨13, 1, 15, 6⟩, ⟨12, 1, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨10, 1, 15, 12⟩, ⟨9, 1, 15, 14⟩, ⟨8, 1, 15, 16⟩, ⟨7, 1, 15, 18⟩, ⟨6, 1, 15, 20⟩, ⟨5, 1, 15, 22⟩, ⟨4, 1, 15, 24⟩, ⟨3, 1, 15, 26⟩, ⟨2, 1, 15, 28⟩, ⟨1, 1, 15, 30⟩, ⟨0, 1, 15, 32⟩, ⟨16, 0, 15, 2⟩, ⟨16, 1, 14, 2⟩, ⟨16, 1, 13, 4⟩, ⟨16, 1, 12, 6⟩, ⟨16, 1, 11, 8⟩, ⟨16, 1, 10, 10⟩, ⟨16, 1, 9, 12⟩, ⟨16, 1, 8, 14⟩, ⟨16, 1, 7, 16⟩, ⟨16, 1, 6, 18⟩, ⟨16, 1, 5, 20⟩, ⟨16, 1, 4, 22⟩, ⟨16, 1, 3, 24⟩, ⟨16, 1, 2, 26⟩, ⟨16, 1, 1, 28⟩, ⟨16, 1, 0, 30⟩]
  exact AllWinning.cons node_18602 (AllWinning.cons node_17634 (AllWinning.cons node_16665 (AllWinning.cons node_15563 (AllWinning.cons node_14581 (AllWinning.cons node_13551 (AllWinning.cons node_12552 (AllWinning.cons node_11503 (AllWinning.cons node_10423 (AllWinning.cons node_9344 (AllWinning.cons node_8294 (AllWinning.cons node_7276 (AllWinning.cons node_6283 (AllWinning.cons node_5463 (AllWinning.cons node_4655 (AllWinning.cons node_3934 (AllWinning.cons node_18652 (AllWinning.cons node_18653 (AllWinning.cons node_17752 (AllWinning.cons node_16821 (AllWinning.cons node_15789 (AllWinning.cons node_14793 (AllWinning.cons node_13843 (AllWinning.cons node_12872 (AllWinning.cons node_11873 (AllWinning.cons node_10880 (AllWinning.cons node_9806 (AllWinning.cons node_8854 (AllWinning.cons node_7864 (AllWinning.cons node_6919 (AllWinning.cons node_6020 (AllWinning.cons node_5307 (AllWinning.nil))))))))))))))))))))))))))))))))

theorem node_19540 : Outcome ⟨16, 1, 15, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 1, 15, 2⟩, ⟨14, 1, 15, 4⟩, ⟨13, 1, 15, 6⟩, ⟨12, 1, 15, 8⟩, ⟨11, 1, 15, 10⟩, ⟨10, 1, 15, 12⟩, ⟨9, 1, 15, 14⟩, ⟨8, 1, 15, 16⟩, ⟨7, 1, 15, 18⟩, ⟨6, 1, 15, 20⟩, ⟨5, 1, 15, 22⟩, ⟨4, 1, 15, 24⟩, ⟨3, 1, 15, 26⟩, ⟨2, 1, 15, 28⟩, ⟨1, 1, 15, 30⟩, ⟨0, 1, 15, 32⟩, ⟨16, 0, 15, 2⟩, ⟨16, 1, 14, 2⟩, ⟨16, 1, 13, 4⟩, ⟨16, 1, 12, 6⟩, ⟨16, 1, 11, 8⟩, ⟨16, 1, 10, 10⟩, ⟨16, 1, 9, 12⟩, ⟨16, 1, 8, 14⟩, ⟨16, 1, 7, 16⟩, ⟨16, 1, 6, 18⟩, ⟨16, 1, 5, 20⟩, ⟨16, 1, 4, 22⟩, ⟨16, 1, 3, 24⟩, ⟨16, 1, 2, 26⟩, ⟨16, 1, 1, 28⟩, ⟨16, 1, 0, 30⟩]
  exact AllWinning.cons node_18602 (AllWinning.cons node_17634 (AllWinning.cons node_16665 (AllWinning.cons node_15563 (AllWinning.cons node_14581 (AllWinning.cons node_13551 (AllWinning.cons node_12552 (AllWinning.cons node_11503 (AllWinning.cons node_10423 (AllWinning.cons node_9344 (AllWinning.cons node_8294 (AllWinning.cons node_7276 (AllWinning.cons node_6283 (AllWinning.cons node_5463 (AllWinning.cons node_4655 (AllWinning.cons node_3934 (AllWinning.cons node_18652 (AllWinning.cons node_18653 (AllWinning.cons node_17752 (AllWinning.cons node_16821 (AllWinning.cons node_15789 (AllWinning.cons node_14793 (AllWinning.cons node_13843 (AllWinning.cons node_12872 (AllWinning.cons node_11873 (AllWinning.cons node_10880 (AllWinning.cons node_9806 (AllWinning.cons node_8854 (AllWinning.cons node_7864 (AllWinning.cons node_6919 (AllWinning.cons node_6020 (AllWinning.cons node_5307 (AllWinning.nil))))))))))))))))))))))))))))))))

end RQ9F1
