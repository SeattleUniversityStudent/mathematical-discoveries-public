import Chunk25
set_option autoImplicit false
namespace RQ9F1

theorem node_6353 : Outcome ⟨3, 14, 2, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 14⟩) (by decide) node_2102

theorem node_6354 : Outcome ⟨3, 14, 2, 12⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 14⟩) (by decide) node_2102

theorem node_6355 : Outcome ⟨3, 14, 2, 18⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 14⟩) (by decide) node_2102

theorem node_6356 : Outcome ⟨3, 15, 1, 2⟩ true :=
  Outcome.win (q := ⟨3, 14, 1, 2⟩) (by decide) node_5567

theorem node_6357 : Outcome ⟨3, 15, 1, 8⟩ true :=
  Outcome.win (q := ⟨3, 14, 1, 2⟩) (by decide) node_5567

theorem node_6358 : Outcome ⟨3, 15, 1, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 18⟩) (by decide) node_1358

theorem node_6359 : Outcome ⟨3, 15, 1, 26⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 18⟩) (by decide) node_1358

theorem node_6360 : Outcome ⟨3, 16, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 0, 2⟩, ⟨1, 16, 0, 4⟩, ⟨3, 15, 0, 2⟩, ⟨3, 14, 0, 4⟩]
  exact AllWinning.cons node_5514 (AllWinning.cons node_4715 (AllWinning.cons node_5571 (AllWinning.cons node_4870 (AllWinning.nil))))

theorem node_6361 : Outcome ⟨3, 16, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 0, 2⟩, ⟨1, 16, 0, 4⟩, ⟨0, 16, 0, 6⟩, ⟨3, 15, 0, 2⟩, ⟨3, 14, 0, 4⟩, ⟨3, 13, 0, 6⟩, ⟨3, 12, 0, 8⟩]
  exact AllWinning.cons node_5514 (AllWinning.cons node_4715 (AllWinning.cons node_4000 (AllWinning.cons node_5571 (AllWinning.cons node_4870 (AllWinning.cons node_4148 (AllWinning.cons node_3581 (AllWinning.nil)))))))

theorem node_6362 : Outcome ⟨3, 16, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 0, 2⟩, ⟨1, 16, 0, 4⟩, ⟨0, 16, 0, 6⟩, ⟨3, 15, 0, 2⟩, ⟨3, 14, 0, 4⟩, ⟨3, 13, 0, 6⟩, ⟨3, 12, 0, 8⟩, ⟨3, 11, 0, 10⟩, ⟨3, 10, 0, 12⟩]
  exact AllWinning.cons node_5514 (AllWinning.cons node_4715 (AllWinning.cons node_4000 (AllWinning.cons node_5571 (AllWinning.cons node_4870 (AllWinning.cons node_4148 (AllWinning.cons node_3581 (AllWinning.cons node_3043 (AllWinning.cons node_2575 (AllWinning.nil)))))))))

theorem node_6363 : Outcome ⟨3, 16, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 0, 2⟩, ⟨1, 16, 0, 4⟩, ⟨0, 16, 0, 6⟩, ⟨3, 15, 0, 2⟩, ⟨3, 14, 0, 4⟩, ⟨3, 13, 0, 6⟩, ⟨3, 12, 0, 8⟩, ⟨3, 11, 0, 10⟩, ⟨3, 10, 0, 12⟩, ⟨3, 9, 0, 14⟩, ⟨3, 8, 0, 16⟩]
  exact AllWinning.cons node_5514 (AllWinning.cons node_4715 (AllWinning.cons node_4000 (AllWinning.cons node_5571 (AllWinning.cons node_4870 (AllWinning.cons node_4148 (AllWinning.cons node_3581 (AllWinning.cons node_3043 (AllWinning.cons node_2575 (AllWinning.cons node_2120 (AllWinning.cons node_1713 (AllWinning.nil)))))))))))

theorem node_6364 : Outcome ⟨3, 16, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 0, 2⟩, ⟨1, 16, 0, 4⟩, ⟨0, 16, 0, 6⟩, ⟨3, 15, 0, 2⟩, ⟨3, 14, 0, 4⟩, ⟨3, 13, 0, 6⟩, ⟨3, 12, 0, 8⟩, ⟨3, 11, 0, 10⟩, ⟨3, 10, 0, 12⟩, ⟨3, 9, 0, 14⟩, ⟨3, 8, 0, 16⟩, ⟨3, 7, 0, 18⟩, ⟨3, 6, 0, 20⟩]
  exact AllWinning.cons node_5514 (AllWinning.cons node_4715 (AllWinning.cons node_4000 (AllWinning.cons node_5571 (AllWinning.cons node_4870 (AllWinning.cons node_4148 (AllWinning.cons node_3581 (AllWinning.cons node_3043 (AllWinning.cons node_2575 (AllWinning.cons node_2120 (AllWinning.cons node_1713 (AllWinning.cons node_1370 (AllWinning.cons node_1058 (AllWinning.nil)))))))))))))

theorem node_6365 : Outcome ⟨3, 16, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 16, 0, 2⟩, ⟨1, 16, 0, 4⟩, ⟨0, 16, 0, 6⟩, ⟨3, 15, 0, 2⟩, ⟨3, 14, 0, 4⟩, ⟨3, 13, 0, 6⟩, ⟨3, 12, 0, 8⟩, ⟨3, 11, 0, 10⟩, ⟨3, 10, 0, 12⟩, ⟨3, 9, 0, 14⟩, ⟨3, 8, 0, 16⟩, ⟨3, 7, 0, 18⟩, ⟨3, 6, 0, 20⟩, ⟨3, 5, 0, 22⟩, ⟨3, 4, 0, 24⟩]
  exact AllWinning.cons node_5514 (AllWinning.cons node_4715 (AllWinning.cons node_4000 (AllWinning.cons node_5571 (AllWinning.cons node_4870 (AllWinning.cons node_4148 (AllWinning.cons node_3581 (AllWinning.cons node_3043 (AllWinning.cons node_2575 (AllWinning.cons node_2120 (AllWinning.cons node_1713 (AllWinning.cons node_1370 (AllWinning.cons node_1058 (AllWinning.cons node_819 (AllWinning.cons node_613 (AllWinning.nil)))))))))))))))

theorem node_6366 : Outcome ⟨3, 16, 0, 16⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 26⟩) (by decide) node_438

theorem node_6367 : Outcome ⟨3, 16, 0, 26⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 26⟩) (by decide) node_438

theorem node_6368 : Outcome ⟨4, 0, 15, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 15, 4⟩) (by decide) node_4720

theorem node_6369 : Outcome ⟨4, 0, 15, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 6⟩) (by decide) node_4152

theorem node_6370 : Outcome ⟨4, 0, 15, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 6⟩) (by decide) node_4152

theorem node_6371 : Outcome ⟨4, 0, 15, 22⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 22⟩) (by decide) node_830

theorem node_6372 : Outcome ⟨4, 1, 14, 2⟩ true :=
  Outcome.win (q := ⟨3, 1, 14, 2⟩) (by decide) node_5523

theorem node_6373 : Outcome ⟨4, 1, 14, 12⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 24⟩) (by decide) node_627

theorem node_6374 : Outcome ⟨4, 2, 13, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 4⟩) (by decide) node_4731

theorem node_6375 : Outcome ⟨4, 2, 13, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 4⟩) (by decide) node_4731

theorem node_6376 : Outcome ⟨4, 2, 13, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 24⟩) (by decide) node_645

theorem node_6377 : Outcome ⟨4, 3, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 3, 12, 2⟩, ⟨2, 3, 12, 4⟩, ⟨4, 2, 12, 2⟩, ⟨4, 1, 12, 4⟩, ⟨4, 3, 11, 2⟩, ⟨4, 3, 10, 4⟩]
  exact AllWinning.cons node_5531 (AllWinning.cons node_4736 (AllWinning.cons node_5585 (AllWinning.cons node_4879 (AllWinning.cons node_5590 (AllWinning.cons node_4886 (AllWinning.nil))))))

theorem node_6378 : Outcome ⟨4, 3, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 6⟩) (by decide) node_4152

theorem node_6379 : Outcome ⟨4, 3, 12, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 6⟩) (by decide) node_4152

theorem node_6380 : Outcome ⟨4, 3, 12, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 12, 6⟩) (by decide) node_4152

theorem node_6381 : Outcome ⟨4, 4, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 11, 2⟩, ⟨2, 4, 11, 4⟩, ⟨4, 3, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨4, 4, 10, 2⟩, ⟨4, 4, 9, 4⟩]
  exact AllWinning.cons node_5533 (AllWinning.cons node_4741 (AllWinning.cons node_5590 (AllWinning.cons node_4883 (AllWinning.cons node_5592 (AllWinning.cons node_4889 (AllWinning.nil))))))

theorem node_6382 : Outcome ⟨4, 4, 11, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 6⟩) (by decide) node_4167

theorem node_6383 : Outcome ⟨4, 4, 11, 28⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 22⟩) (by decide) node_856

theorem node_6384 : Outcome ⟨4, 5, 10, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 4⟩) (by decide) node_4744

theorem node_6385 : Outcome ⟨4, 5, 10, 4⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 6⟩) (by decide) node_4172

theorem node_6386 : Outcome ⟨4, 5, 10, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 6⟩) (by decide) node_4172

theorem node_6387 : Outcome ⟨4, 5, 10, 16⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 6⟩) (by decide) node_4172

theorem node_6388 : Outcome ⟨4, 5, 10, 20⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 6⟩) (by decide) node_4172

theorem node_6389 : Outcome ⟨4, 6, 9, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 2⟩) (by decide) node_5537

theorem node_6390 : Outcome ⟨4, 6, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 2⟩) (by decide) node_5537

theorem node_6391 : Outcome ⟨4, 6, 9, 20⟩ true :=
  Outcome.win (q := ⟨3, 6, 9, 2⟩) (by decide) node_5537

theorem node_6392 : Outcome ⟨4, 7, 8, 2⟩ true :=
  Outcome.win (q := ⟨2, 7, 8, 4⟩) (by decide) node_4760

theorem node_6393 : Outcome ⟨4, 7, 8, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 6⟩) (by decide) node_4167

theorem node_6394 : Outcome ⟨4, 7, 8, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 8, 6⟩) (by decide) node_4167

theorem node_6395 : Outcome ⟨4, 8, 7, 2⟩ true :=
  Outcome.win (q := ⟨2, 8, 7, 4⟩) (by decide) node_4765

theorem node_6396 : Outcome ⟨4, 8, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 6⟩) (by decide) node_4172

theorem node_6397 : Outcome ⟨4, 8, 7, 20⟩ true :=
  Outcome.win (q := ⟨4, 5, 7, 6⟩) (by decide) node_4172

theorem node_6398 : Outcome ⟨4, 9, 6, 2⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 2⟩) (by decide) node_5552

theorem node_6399 : Outcome ⟨4, 9, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 2⟩) (by decide) node_5552

theorem node_6400 : Outcome ⟨4, 9, 6, 20⟩ true :=
  Outcome.win (q := ⟨3, 9, 6, 2⟩) (by decide) node_5552

theorem node_6401 : Outcome ⟨4, 10, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 4⟩) (by decide) node_4773

theorem node_6402 : Outcome ⟨4, 10, 5, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 6⟩) (by decide) node_4189

theorem node_6403 : Outcome ⟨4, 10, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 6⟩) (by decide) node_4189

theorem node_6404 : Outcome ⟨4, 10, 5, 16⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 6⟩) (by decide) node_4189

theorem node_6405 : Outcome ⟨4, 10, 5, 20⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 6⟩) (by decide) node_4189

theorem node_6406 : Outcome ⟨4, 11, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 11, 4, 2⟩, ⟨2, 11, 4, 4⟩, ⟨4, 10, 4, 2⟩, ⟨4, 9, 4, 4⟩, ⟨4, 11, 3, 2⟩, ⟨4, 11, 2, 4⟩]
  exact AllWinning.cons node_5560 (AllWinning.cons node_4785 (AllWinning.cons node_5613 (AllWinning.cons node_4904 (AllWinning.cons node_5616 (AllWinning.cons node_4910 (AllWinning.nil))))))

theorem node_6407 : Outcome ⟨4, 11, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 8, 4, 6⟩) (by decide) node_4202

theorem node_6408 : Outcome ⟨4, 11, 4, 28⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 22⟩) (by decide) node_830

theorem node_6409 : Outcome ⟨4, 12, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 12, 3, 2⟩, ⟨2, 12, 3, 4⟩, ⟨4, 11, 3, 2⟩, ⟨4, 10, 3, 4⟩, ⟨4, 12, 2, 2⟩, ⟨4, 12, 1, 4⟩]
  exact AllWinning.cons node_5561 (AllWinning.cons node_4787 (AllWinning.cons node_5616 (AllWinning.cons node_4907 (AllWinning.cons node_5618 (AllWinning.cons node_4914 (AllWinning.nil))))))

theorem node_6410 : Outcome ⟨4, 12, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 6⟩) (by decide) node_4216

theorem node_6411 : Outcome ⟨4, 12, 3, 10⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 6⟩) (by decide) node_4216

theorem node_6412 : Outcome ⟨4, 12, 3, 20⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 6⟩) (by decide) node_4216

theorem node_6413 : Outcome ⟨4, 13, 2, 2⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 4⟩) (by decide) node_4793

theorem node_6414 : Outcome ⟨4, 13, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 13, 2, 4⟩) (by decide) node_4793

theorem node_6415 : Outcome ⟨4, 13, 2, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 24⟩) (by decide) node_627

theorem node_6416 : Outcome ⟨4, 14, 1, 2⟩ true :=
  Outcome.win (q := ⟨3, 14, 1, 2⟩) (by decide) node_5567

theorem node_6417 : Outcome ⟨4, 14, 1, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 24⟩) (by decide) node_645

theorem node_6418 : Outcome ⟨4, 15, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 15, 0, 4⟩) (by decide) node_4803

theorem node_6419 : Outcome ⟨4, 15, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 6⟩) (by decide) node_4216

theorem node_6420 : Outcome ⟨4, 15, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 12, 0, 6⟩) (by decide) node_4216

theorem node_6421 : Outcome ⟨4, 15, 0, 22⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 22⟩) (by decide) node_856

theorem node_6422 : Outcome ⟨5, 0, 14, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 13, 2⟩) (by decide) node_5631

theorem node_6423 : Outcome ⟨5, 0, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 14, 8⟩) (by decide) node_3387

theorem node_6424 : Outcome ⟨5, 0, 14, 18⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 18⟩) (by decide) node_1412

theorem node_6425 : Outcome ⟨5, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨4, 1, 13, 2⟩) (by decide) node_5579

theorem node_6426 : Outcome ⟨5, 1, 13, 8⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 8⟩) (by decide) node_3395

theorem node_6427 : Outcome ⟨5, 1, 13, 24⟩ true :=
  Outcome.win (q := ⟨1, 1, 13, 8⟩) (by decide) node_3395

theorem node_6428 : Outcome ⟨5, 2, 12, 4⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6429 : Outcome ⟨5, 2, 12, 6⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6430 : Outcome ⟨5, 2, 12, 16⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6431 : Outcome ⟨5, 2, 12, 18⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6432 : Outcome ⟨5, 2, 12, 32⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6433 : Outcome ⟨5, 3, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.nil)))))))))))

theorem node_6434 : Outcome ⟨5, 3, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.nil))))))))))))))

theorem node_6435 : Outcome ⟨5, 3, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩, ⟨5, 3, 4, 14⟩, ⟨5, 3, 3, 16⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.cons node_2175 (AllWinning.cons node_1766 (AllWinning.nil))))))))))))))))

theorem node_6436 : Outcome ⟨5, 3, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩, ⟨5, 3, 4, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 3, 2, 18⟩, ⟨5, 3, 1, 20⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.cons node_2175 (AllWinning.cons node_1766 (AllWinning.cons node_1431 (AllWinning.cons node_1099 (AllWinning.nil))))))))))))))))))

theorem node_6437 : Outcome ⟨5, 3, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩, ⟨5, 3, 4, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 3, 2, 18⟩, ⟨5, 3, 1, 20⟩, ⟨5, 3, 0, 22⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.cons node_2175 (AllWinning.cons node_1766 (AllWinning.cons node_1431 (AllWinning.cons node_1099 (AllWinning.cons node_879 (AllWinning.nil)))))))))))))))))))

theorem node_6438 : Outcome ⟨5, 3, 11, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩, ⟨5, 3, 4, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 3, 2, 18⟩, ⟨5, 3, 1, 20⟩, ⟨5, 3, 0, 22⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.cons node_2175 (AllWinning.cons node_1766 (AllWinning.cons node_1431 (AllWinning.cons node_1099 (AllWinning.cons node_879 (AllWinning.nil)))))))))))))))))))

theorem node_6439 : Outcome ⟨5, 3, 11, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩, ⟨5, 3, 4, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 3, 2, 18⟩, ⟨5, 3, 1, 20⟩, ⟨5, 3, 0, 22⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.cons node_2175 (AllWinning.cons node_1766 (AllWinning.cons node_1431 (AllWinning.cons node_1099 (AllWinning.cons node_879 (AllWinning.nil)))))))))))))))))))

theorem node_6440 : Outcome ⟨5, 3, 11, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩, ⟨5, 3, 4, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 3, 2, 18⟩, ⟨5, 3, 1, 20⟩, ⟨5, 3, 0, 22⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.cons node_2175 (AllWinning.cons node_1766 (AllWinning.cons node_1431 (AllWinning.cons node_1099 (AllWinning.cons node_879 (AllWinning.nil)))))))))))))))))))

theorem node_6441 : Outcome ⟨5, 3, 11, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 11, 2⟩, ⟨3, 3, 11, 4⟩, ⟨2, 3, 11, 6⟩, ⟨1, 3, 11, 8⟩, ⟨0, 3, 11, 10⟩, ⟨5, 2, 11, 2⟩, ⟨5, 1, 11, 4⟩, ⟨5, 0, 11, 6⟩, ⟨5, 3, 10, 2⟩, ⟨5, 3, 9, 4⟩, ⟨5, 3, 8, 6⟩, ⟨5, 3, 7, 8⟩, ⟨5, 3, 6, 10⟩, ⟨5, 3, 5, 12⟩, ⟨5, 3, 4, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 3, 2, 18⟩, ⟨5, 3, 1, 20⟩, ⟨5, 3, 0, 22⟩]
  exact AllWinning.cons node_5590 (AllWinning.cons node_4826 (AllWinning.cons node_4062 (AllWinning.cons node_3405 (AllWinning.cons node_2837 (AllWinning.cons node_5639 (AllWinning.cons node_4928 (AllWinning.cons node_4222 (AllWinning.cons node_5641 (AllWinning.cons node_4943 (AllWinning.cons node_4233 (AllWinning.cons node_3652 (AllWinning.cons node_3098 (AllWinning.cons node_2644 (AllWinning.cons node_2175 (AllWinning.cons node_1766 (AllWinning.cons node_1431 (AllWinning.cons node_1099 (AllWinning.cons node_879 (AllWinning.nil)))))))))))))))))))

theorem node_6442 : Outcome ⟨5, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 10, 4⟩) (by decide) node_4931

theorem node_6443 : Outcome ⟨5, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 6⟩) (by decide) node_4238

theorem node_6444 : Outcome ⟨5, 4, 10, 8⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 6⟩) (by decide) node_4238

theorem node_6445 : Outcome ⟨5, 4, 10, 16⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 6⟩) (by decide) node_4238

theorem node_6446 : Outcome ⟨5, 4, 10, 20⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 6⟩) (by decide) node_4238

theorem node_6447 : Outcome ⟨5, 5, 9, 8⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 8⟩) (by decide) node_3415

theorem node_6448 : Outcome ⟨5, 5, 9, 18⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 18⟩) (by decide) node_1446

theorem node_6449 : Outcome ⟨5, 6, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 2⟩) (by decide) node_5648

theorem node_6450 : Outcome ⟨5, 6, 8, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 2⟩) (by decide) node_5648

theorem node_6451 : Outcome ⟨5, 6, 8, 18⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 2⟩) (by decide) node_5648

theorem node_6452 : Outcome ⟨5, 7, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 7, 7, 2⟩, ⟨3, 7, 7, 4⟩, ⟨5, 6, 7, 2⟩, ⟨5, 5, 7, 4⟩, ⟨5, 7, 6, 2⟩, ⟨5, 7, 5, 4⟩]
  exact AllWinning.cons node_5602 (AllWinning.cons node_4839 (AllWinning.cons node_5653 (AllWinning.cons node_4951 (AllWinning.cons node_5656 (AllWinning.cons node_4957 (AllWinning.nil))))))

theorem node_6453 : Outcome ⟨5, 7, 7, 4⟩ true :=
  Outcome.win (q := ⟨5, 4, 7, 6⟩) (by decide) node_4238

theorem node_6454 : Outcome ⟨5, 7, 7, 14⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6455 : Outcome ⟨5, 7, 7, 20⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 10⟩) (by decide) node_2853

theorem node_6456 : Outcome ⟨5, 8, 6, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 5, 2⟩) (by decide) node_5659

theorem node_6457 : Outcome ⟨5, 8, 6, 8⟩ true :=
  Outcome.win (q := ⟨5, 8, 5, 2⟩) (by decide) node_5659

theorem node_6458 : Outcome ⟨5, 8, 6, 18⟩ true :=
  Outcome.win (q := ⟨5, 8, 5, 2⟩) (by decide) node_5659

theorem node_6459 : Outcome ⟨5, 9, 5, 8⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 8⟩) (by decide) node_3439

theorem node_6460 : Outcome ⟨5, 9, 5, 18⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 18⟩) (by decide) node_1412

theorem node_6461 : Outcome ⟨5, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6462 : Outcome ⟨5, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 6⟩) (by decide) node_4255

theorem node_6463 : Outcome ⟨5, 10, 4, 8⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 6⟩) (by decide) node_4255

theorem node_6464 : Outcome ⟨5, 10, 4, 16⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 6⟩) (by decide) node_4255

theorem node_6465 : Outcome ⟨5, 10, 4, 20⟩ true :=
  Outcome.win (q := ⟨5, 7, 4, 6⟩) (by decide) node_4255

theorem node_6466 : Outcome ⟨5, 11, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil)))))))))))

theorem node_6467 : Outcome ⟨5, 11, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil))))))))))))))

theorem node_6468 : Outcome ⟨5, 11, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 4, 3, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_2179 (AllWinning.cons node_1766 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil))))))))))))))))

theorem node_6469 : Outcome ⟨5, 11, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 4, 3, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 2, 3, 18⟩, ⟨5, 1, 3, 20⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_2179 (AllWinning.cons node_1766 (AllWinning.cons node_1427 (AllWinning.cons node_1091 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil))))))))))))))))))

theorem node_6470 : Outcome ⟨5, 11, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 4, 3, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 2, 3, 18⟩, ⟨5, 1, 3, 20⟩, ⟨5, 0, 3, 22⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_2179 (AllWinning.cons node_1766 (AllWinning.cons node_1427 (AllWinning.cons node_1091 (AllWinning.cons node_865 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil)))))))))))))))))))

theorem node_6471 : Outcome ⟨5, 11, 3, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 4, 3, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 2, 3, 18⟩, ⟨5, 1, 3, 20⟩, ⟨5, 0, 3, 22⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_2179 (AllWinning.cons node_1766 (AllWinning.cons node_1427 (AllWinning.cons node_1091 (AllWinning.cons node_865 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil)))))))))))))))))))

theorem node_6472 : Outcome ⟨5, 11, 3, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 4, 3, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 2, 3, 18⟩, ⟨5, 1, 3, 20⟩, ⟨5, 0, 3, 22⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_2179 (AllWinning.cons node_1766 (AllWinning.cons node_1427 (AllWinning.cons node_1091 (AllWinning.cons node_865 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil)))))))))))))))))))

theorem node_6473 : Outcome ⟨5, 11, 3, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 4, 3, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 2, 3, 18⟩, ⟨5, 1, 3, 20⟩, ⟨5, 0, 3, 22⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_2179 (AllWinning.cons node_1766 (AllWinning.cons node_1427 (AllWinning.cons node_1091 (AllWinning.cons node_865 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil)))))))))))))))))))

theorem node_6474 : Outcome ⟨5, 11, 3, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 11, 3, 2⟩, ⟨3, 11, 3, 4⟩, ⟨2, 11, 3, 6⟩, ⟨1, 11, 3, 8⟩, ⟨0, 11, 3, 10⟩, ⟨5, 10, 3, 2⟩, ⟨5, 9, 3, 4⟩, ⟨5, 8, 3, 6⟩, ⟨5, 7, 3, 8⟩, ⟨5, 6, 3, 10⟩, ⟨5, 5, 3, 12⟩, ⟨5, 4, 3, 14⟩, ⟨5, 3, 3, 16⟩, ⟨5, 2, 3, 18⟩, ⟨5, 1, 3, 20⟩, ⟨5, 0, 3, 22⟩, ⟨5, 11, 2, 2⟩, ⟨5, 11, 1, 4⟩, ⟨5, 11, 0, 6⟩]
  exact AllWinning.cons node_5616 (AllWinning.cons node_4857 (AllWinning.cons node_4087 (AllWinning.cons node_3456 (AllWinning.cons node_2875 (AllWinning.cons node_5668 (AllWinning.cons node_4965 (AllWinning.cons node_4267 (AllWinning.cons node_3665 (AllWinning.cons node_3110 (AllWinning.cons node_2652 (AllWinning.cons node_2179 (AllWinning.cons node_1766 (AllWinning.cons node_1427 (AllWinning.cons node_1091 (AllWinning.cons node_865 (AllWinning.cons node_5671 (AllWinning.cons node_4981 (AllWinning.cons node_4279 (AllWinning.nil)))))))))))))))))))

theorem node_6475 : Outcome ⟨5, 12, 2, 4⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6476 : Outcome ⟨5, 12, 2, 6⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6477 : Outcome ⟨5, 12, 2, 16⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6478 : Outcome ⟨5, 12, 2, 18⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6479 : Outcome ⟨5, 12, 2, 32⟩ true :=
  Outcome.win (q := ⟨5, 10, 2, 4⟩) (by decide) node_4969

theorem node_6480 : Outcome ⟨5, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨4, 13, 1, 2⟩) (by decide) node_5623

theorem node_6481 : Outcome ⟨5, 13, 1, 8⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 8⟩) (by decide) node_3467

theorem node_6482 : Outcome ⟨5, 13, 1, 24⟩ true :=
  Outcome.win (q := ⟨1, 13, 1, 8⟩) (by decide) node_3467

theorem node_6483 : Outcome ⟨5, 14, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 13, 0, 2⟩) (by decide) node_5676

theorem node_6484 : Outcome ⟨5, 14, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 14, 0, 8⟩) (by decide) node_3473

theorem node_6485 : Outcome ⟨5, 14, 0, 18⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 18⟩) (by decide) node_1446

theorem node_6486 : Outcome ⟨6, 0, 13, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 13, 2⟩) (by decide) node_5631

theorem node_6487 : Outcome ⟨6, 0, 13, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 13, 2⟩) (by decide) node_5631

theorem node_6488 : Outcome ⟨6, 0, 13, 12⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 14⟩) (by decide) node_2197

theorem node_6489 : Outcome ⟨6, 0, 13, 14⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 14⟩) (by decide) node_2197

theorem node_6490 : Outcome ⟨6, 0, 13, 28⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 14⟩) (by decide) node_2197

theorem node_6491 : Outcome ⟨6, 1, 12, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 12, 2⟩) (by decide) node_5636

theorem node_6492 : Outcome ⟨6, 1, 12, 4⟩ true :=
  Outcome.win (q := ⟨5, 1, 12, 2⟩) (by decide) node_5636

theorem node_6493 : Outcome ⟨6, 1, 12, 8⟩ true :=
  Outcome.win (q := ⟨5, 1, 12, 2⟩) (by decide) node_5636

theorem node_6494 : Outcome ⟨6, 1, 12, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 18⟩) (by decide) node_1463

theorem node_6495 : Outcome ⟨6, 1, 12, 30⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 18⟩) (by decide) node_1463

theorem node_6496 : Outcome ⟨6, 2, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.nil))))))

theorem node_6497 : Outcome ⟨6, 2, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.nil))))))))))

theorem node_6498 : Outcome ⟨6, 2, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.nil))))))))))))))

theorem node_6499 : Outcome ⟨6, 2, 11, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩, ⟨6, 2, 4, 14⟩, ⟨6, 2, 3, 16⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.cons node_2211 (AllWinning.cons node_1786 (AllWinning.nil))))))))))))))))

theorem node_6500 : Outcome ⟨6, 2, 11, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩, ⟨6, 2, 4, 14⟩, ⟨6, 2, 3, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 2, 1, 20⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.cons node_2211 (AllWinning.cons node_1786 (AllWinning.cons node_1474 (AllWinning.cons node_1116 (AllWinning.nil))))))))))))))))))

theorem node_6501 : Outcome ⟨6, 2, 11, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩, ⟨6, 2, 4, 14⟩, ⟨6, 2, 3, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 2, 1, 20⟩, ⟨6, 2, 0, 22⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.cons node_2211 (AllWinning.cons node_1786 (AllWinning.cons node_1474 (AllWinning.cons node_1116 (AllWinning.cons node_889 (AllWinning.nil)))))))))))))))))))

theorem node_6502 : Outcome ⟨6, 2, 11, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩, ⟨6, 2, 4, 14⟩, ⟨6, 2, 3, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 2, 1, 20⟩, ⟨6, 2, 0, 22⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.cons node_2211 (AllWinning.cons node_1786 (AllWinning.cons node_1474 (AllWinning.cons node_1116 (AllWinning.cons node_889 (AllWinning.nil)))))))))))))))))))

theorem node_6503 : Outcome ⟨6, 2, 11, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩, ⟨6, 2, 4, 14⟩, ⟨6, 2, 3, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 2, 1, 20⟩, ⟨6, 2, 0, 22⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.cons node_2211 (AllWinning.cons node_1786 (AllWinning.cons node_1474 (AllWinning.cons node_1116 (AllWinning.cons node_889 (AllWinning.nil)))))))))))))))))))

theorem node_6504 : Outcome ⟨6, 2, 11, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩, ⟨6, 2, 4, 14⟩, ⟨6, 2, 3, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 2, 1, 20⟩, ⟨6, 2, 0, 22⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.cons node_2211 (AllWinning.cons node_1786 (AllWinning.cons node_1474 (AllWinning.cons node_1116 (AllWinning.cons node_889 (AllWinning.nil)))))))))))))))))))

theorem node_6505 : Outcome ⟨6, 2, 11, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 2, 11, 2⟩, ⟨4, 2, 11, 4⟩, ⟨3, 2, 11, 6⟩, ⟨2, 2, 11, 8⟩, ⟨1, 2, 11, 10⟩, ⟨0, 2, 11, 12⟩, ⟨6, 1, 11, 2⟩, ⟨6, 0, 11, 4⟩, ⟨6, 2, 10, 2⟩, ⟨6, 2, 9, 4⟩, ⟨6, 2, 8, 6⟩, ⟨6, 2, 7, 8⟩, ⟨6, 2, 6, 10⟩, ⟨6, 2, 5, 12⟩, ⟨6, 2, 4, 14⟩, ⟨6, 2, 3, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 2, 1, 20⟩, ⟨6, 2, 0, 22⟩]
  exact AllWinning.cons node_5639 (AllWinning.cons node_4883 (AllWinning.cons node_4106 (AllWinning.cons node_3488 (AllWinning.cons node_2896 (AllWinning.cons node_2374 (AllWinning.cons node_5686 (AllWinning.cons node_4989 (AllWinning.cons node_5689 (AllWinning.cons node_4997 (AllWinning.cons node_4289 (AllWinning.cons node_3697 (AllWinning.cons node_3134 (AllWinning.cons node_2675 (AllWinning.cons node_2211 (AllWinning.cons node_1786 (AllWinning.cons node_1474 (AllWinning.cons node_1116 (AllWinning.cons node_889 (AllWinning.nil)))))))))))))))))))

theorem node_6506 : Outcome ⟨6, 3, 10, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 9, 2⟩) (by decide) node_5692

theorem node_6507 : Outcome ⟨6, 3, 10, 8⟩ true :=
  Outcome.win (q := ⟨6, 3, 9, 2⟩) (by decide) node_5692

theorem node_6508 : Outcome ⟨6, 3, 10, 14⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 18⟩) (by decide) node_1483

theorem node_6509 : Outcome ⟨6, 4, 9, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 9, 2⟩) (by decide) node_5692

theorem node_6510 : Outcome ⟨6, 4, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 3, 9, 2⟩) (by decide) node_5692

theorem node_6511 : Outcome ⟨6, 4, 9, 20⟩ true :=
  Outcome.win (q := ⟨6, 3, 9, 2⟩) (by decide) node_5692

theorem node_6512 : Outcome ⟨6, 5, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 2⟩) (by decide) node_5648

theorem node_6513 : Outcome ⟨6, 5, 8, 8⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 2⟩) (by decide) node_5648

theorem node_6514 : Outcome ⟨6, 5, 8, 18⟩ true :=
  Outcome.win (q := ⟨5, 5, 8, 2⟩) (by decide) node_5648

theorem node_6515 : Outcome ⟨6, 6, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 6, 2⟩) (by decide) node_5703

theorem node_6516 : Outcome ⟨6, 6, 7, 10⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 14⟩) (by decide) node_2231

theorem node_6517 : Outcome ⟨6, 6, 7, 26⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 14⟩) (by decide) node_2231

theorem node_6518 : Outcome ⟨6, 7, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 6, 2⟩) (by decide) node_5703

theorem node_6519 : Outcome ⟨6, 7, 6, 10⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 14⟩) (by decide) node_2197

theorem node_6520 : Outcome ⟨6, 7, 6, 26⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 14⟩) (by decide) node_2197

theorem node_6521 : Outcome ⟨6, 8, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 8, 5, 2⟩) (by decide) node_5659

theorem node_6522 : Outcome ⟨6, 8, 5, 8⟩ true :=
  Outcome.win (q := ⟨5, 8, 5, 2⟩) (by decide) node_5659

theorem node_6523 : Outcome ⟨6, 8, 5, 18⟩ true :=
  Outcome.win (q := ⟨5, 8, 5, 2⟩) (by decide) node_5659

theorem node_6524 : Outcome ⟨6, 9, 4, 2⟩ true :=
  Outcome.win (q := ⟨6, 9, 3, 2⟩) (by decide) node_5713

theorem node_6525 : Outcome ⟨6, 9, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 9, 3, 2⟩) (by decide) node_5713

theorem node_6526 : Outcome ⟨6, 9, 4, 20⟩ true :=
  Outcome.win (q := ⟨6, 9, 3, 2⟩) (by decide) node_5713

theorem node_6527 : Outcome ⟨6, 10, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 9, 3, 2⟩) (by decide) node_5713

theorem node_6528 : Outcome ⟨6, 10, 3, 8⟩ true :=
  Outcome.win (q := ⟨6, 9, 3, 2⟩) (by decide) node_5713

theorem node_6529 : Outcome ⟨6, 10, 3, 14⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 18⟩) (by decide) node_1463

theorem node_6530 : Outcome ⟨6, 11, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil))))))

theorem node_6531 : Outcome ⟨6, 11, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil))))))))))

theorem node_6532 : Outcome ⟨6, 11, 2, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨1, 11, 2, 10⟩, ⟨0, 11, 2, 12⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 6, 2, 10⟩, ⟨6, 5, 2, 12⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_2931 (AllWinning.cons node_2417 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_3151 (AllWinning.cons node_2687 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil))))))))))))))

theorem node_6533 : Outcome ⟨6, 11, 2, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨1, 11, 2, 10⟩, ⟨0, 11, 2, 12⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 6, 2, 10⟩, ⟨6, 5, 2, 12⟩, ⟨6, 4, 2, 14⟩, ⟨6, 3, 2, 16⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_2931 (AllWinning.cons node_2417 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_3151 (AllWinning.cons node_2687 (AllWinning.cons node_2220 (AllWinning.cons node_1789 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil))))))))))))))))

theorem node_6534 : Outcome ⟨6, 11, 2, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨1, 11, 2, 10⟩, ⟨0, 11, 2, 12⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 6, 2, 10⟩, ⟨6, 5, 2, 12⟩, ⟨6, 4, 2, 14⟩, ⟨6, 3, 2, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 1, 2, 20⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_2931 (AllWinning.cons node_2417 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_3151 (AllWinning.cons node_2687 (AllWinning.cons node_2220 (AllWinning.cons node_1789 (AllWinning.cons node_1474 (AllWinning.cons node_1111 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil))))))))))))))))))

theorem node_6535 : Outcome ⟨6, 11, 2, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨1, 11, 2, 10⟩, ⟨0, 11, 2, 12⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 6, 2, 10⟩, ⟨6, 5, 2, 12⟩, ⟨6, 4, 2, 14⟩, ⟨6, 3, 2, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 1, 2, 20⟩, ⟨6, 0, 2, 22⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_2931 (AllWinning.cons node_2417 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_3151 (AllWinning.cons node_2687 (AllWinning.cons node_2220 (AllWinning.cons node_1789 (AllWinning.cons node_1474 (AllWinning.cons node_1111 (AllWinning.cons node_883 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil)))))))))))))))))))

theorem node_6536 : Outcome ⟨6, 11, 2, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨1, 11, 2, 10⟩, ⟨0, 11, 2, 12⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 6, 2, 10⟩, ⟨6, 5, 2, 12⟩, ⟨6, 4, 2, 14⟩, ⟨6, 3, 2, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 1, 2, 20⟩, ⟨6, 0, 2, 22⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_2931 (AllWinning.cons node_2417 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_3151 (AllWinning.cons node_2687 (AllWinning.cons node_2220 (AllWinning.cons node_1789 (AllWinning.cons node_1474 (AllWinning.cons node_1111 (AllWinning.cons node_883 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil)))))))))))))))))))

theorem node_6537 : Outcome ⟨6, 11, 2, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨1, 11, 2, 10⟩, ⟨0, 11, 2, 12⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 6, 2, 10⟩, ⟨6, 5, 2, 12⟩, ⟨6, 4, 2, 14⟩, ⟨6, 3, 2, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 1, 2, 20⟩, ⟨6, 0, 2, 22⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_2931 (AllWinning.cons node_2417 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_3151 (AllWinning.cons node_2687 (AllWinning.cons node_2220 (AllWinning.cons node_1789 (AllWinning.cons node_1474 (AllWinning.cons node_1111 (AllWinning.cons node_883 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil)))))))))))))))))))

theorem node_6538 : Outcome ⟨6, 11, 2, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨5, 11, 2, 2⟩, ⟨4, 11, 2, 4⟩, ⟨3, 11, 2, 6⟩, ⟨2, 11, 2, 8⟩, ⟨1, 11, 2, 10⟩, ⟨0, 11, 2, 12⟩, ⟨6, 10, 2, 2⟩, ⟨6, 9, 2, 4⟩, ⟨6, 8, 2, 6⟩, ⟨6, 7, 2, 8⟩, ⟨6, 6, 2, 10⟩, ⟨6, 5, 2, 12⟩, ⟨6, 4, 2, 14⟩, ⟨6, 3, 2, 16⟩, ⟨6, 2, 2, 18⟩, ⟨6, 1, 2, 20⟩, ⟨6, 0, 2, 22⟩, ⟨6, 11, 1, 2⟩, ⟨6, 11, 0, 4⟩]
  exact AllWinning.cons node_5671 (AllWinning.cons node_4910 (AllWinning.cons node_4141 (AllWinning.cons node_3526 (AllWinning.cons node_2931 (AllWinning.cons node_2417 (AllWinning.cons node_5718 (AllWinning.cons node_5020 (AllWinning.cons node_4317 (AllWinning.cons node_3716 (AllWinning.cons node_3151 (AllWinning.cons node_2687 (AllWinning.cons node_2220 (AllWinning.cons node_1789 (AllWinning.cons node_1474 (AllWinning.cons node_1111 (AllWinning.cons node_883 (AllWinning.cons node_5721 (AllWinning.cons node_5026 (AllWinning.nil)))))))))))))))))))

theorem node_6539 : Outcome ⟨6, 12, 1, 2⟩ true :=
  Outcome.win (q := ⟨5, 12, 1, 2⟩) (by decide) node_5673

theorem node_6540 : Outcome ⟨6, 12, 1, 4⟩ true :=
  Outcome.win (q := ⟨5, 12, 1, 2⟩) (by decide) node_5673

theorem node_6541 : Outcome ⟨6, 12, 1, 8⟩ true :=
  Outcome.win (q := ⟨5, 12, 1, 2⟩) (by decide) node_5673

theorem node_6542 : Outcome ⟨6, 12, 1, 10⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 18⟩) (by decide) node_1483

theorem node_6543 : Outcome ⟨6, 12, 1, 30⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 18⟩) (by decide) node_1483

end RQ9F1
