import Chunk09
set_option autoImplicit false
namespace RQ9F1

theorem node_2548 : Outcome ⟨3, 4, 6, 10⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 6⟩) (by decide) node_1321

theorem node_2549 : Outcome ⟨3, 4, 6, 14⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 6⟩) (by decide) node_1321

theorem node_2550 : Outcome ⟨3, 4, 6, 20⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 6⟩) (by decide) node_1321

theorem node_2551 : Outcome ⟨3, 5, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 4⟩) (by decide) node_1691

theorem node_2552 : Outcome ⟨3, 5, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 6⟩) (by decide) node_1173

theorem node_2553 : Outcome ⟨3, 5, 5, 10⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 6⟩) (by decide) node_1173

theorem node_2554 : Outcome ⟨3, 5, 5, 12⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 6⟩) (by decide) node_1173

theorem node_2555 : Outcome ⟨3, 5, 5, 20⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 6⟩) (by decide) node_1173

theorem node_2556 : Outcome ⟨3, 6, 4, 2⟩ true :=
  Outcome.win (q := ⟨2, 6, 4, 2⟩) (by decide) node_2019

theorem node_2557 : Outcome ⟨3, 6, 4, 10⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 6⟩) (by decide) node_1352

theorem node_2558 : Outcome ⟨3, 6, 4, 14⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 6⟩) (by decide) node_1352

theorem node_2559 : Outcome ⟨3, 6, 4, 20⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 6⟩) (by decide) node_1352

theorem node_2560 : Outcome ⟨3, 7, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 3, 4⟩) (by decide) node_1699

theorem node_2561 : Outcome ⟨3, 7, 3, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 14⟩) (by decide) node_409

theorem node_2562 : Outcome ⟨3, 7, 3, 24⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 14⟩) (by decide) node_409

theorem node_2563 : Outcome ⟨3, 8, 2, 2⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 2⟩) (by decide) node_2040

theorem node_2564 : Outcome ⟨3, 8, 2, 4⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 2⟩) (by decide) node_2040

theorem node_2565 : Outcome ⟨3, 8, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 2⟩) (by decide) node_2040

theorem node_2566 : Outcome ⟨3, 8, 2, 24⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 2⟩) (by decide) node_2040

theorem node_2567 : Outcome ⟨3, 8, 2, 28⟩ true :=
  Outcome.win (q := ⟨2, 8, 2, 2⟩) (by decide) node_2040

theorem node_2568 : Outcome ⟨3, 9, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 9, 1, 2⟩, ⟨1, 9, 1, 4⟩, ⟨3, 8, 1, 2⟩, ⟨3, 7, 1, 4⟩, ⟨3, 9, 0, 2⟩]
  exact AllWinning.cons node_2045 (AllWinning.cons node_1628 (AllWinning.cons node_2111 (AllWinning.cons node_1706 (AllWinning.cons node_2117 (AllWinning.nil)))))

theorem node_2569 : Outcome ⟨3, 9, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 6⟩) (by decide) node_1198

theorem node_2570 : Outcome ⟨3, 9, 1, 10⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 6⟩) (by decide) node_1198

theorem node_2571 : Outcome ⟨3, 9, 1, 20⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 6⟩) (by decide) node_1198

theorem node_2572 : Outcome ⟨3, 9, 1, 22⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 6⟩) (by decide) node_1198

theorem node_2573 : Outcome ⟨3, 10, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 10, 0, 2⟩) (by decide) node_2049

theorem node_2574 : Outcome ⟨3, 10, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 10, 0, 2⟩) (by decide) node_2049

theorem node_2575 : Outcome ⟨3, 10, 0, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 14⟩) (by decide) node_432

theorem node_2576 : Outcome ⟨3, 10, 0, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 14⟩) (by decide) node_432

theorem node_2577 : Outcome ⟨3, 10, 0, 26⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 14⟩) (by decide) node_432

theorem node_2578 : Outcome ⟨4, 0, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 0, 9, 2⟩, ⟨2, 0, 9, 4⟩, ⟨4, 0, 8, 2⟩, ⟨4, 0, 7, 4⟩]
  exact AllWinning.cons node_2054 (AllWinning.cons node_1635 (AllWinning.cons node_2122 (AllWinning.cons node_1716 (AllWinning.nil))))

theorem node_2579 : Outcome ⟨4, 0, 9, 4⟩ true :=
  Outcome.win (q := ⟨1, 0, 9, 6⟩) (by decide) node_1207

theorem node_2580 : Outcome ⟨4, 0, 9, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2581 : Outcome ⟨4, 0, 9, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2582 : Outcome ⟨4, 0, 9, 16⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2583 : Outcome ⟨4, 0, 9, 32⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2584 : Outcome ⟨4, 1, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 1, 8, 6⟩) (by decide) node_1212

theorem node_2585 : Outcome ⟨4, 1, 8, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2586 : Outcome ⟨4, 1, 8, 14⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2587 : Outcome ⟨4, 1, 8, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2588 : Outcome ⟨4, 1, 8, 32⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2589 : Outcome ⟨4, 2, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 2⟩) (by decide) node_2065

theorem node_2590 : Outcome ⟨4, 2, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2591 : Outcome ⟨4, 2, 7, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2592 : Outcome ⟨4, 2, 7, 14⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2593 : Outcome ⟨4, 2, 7, 16⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2594 : Outcome ⟨4, 2, 7, 28⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2595 : Outcome ⟨4, 3, 6, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 6, 2⟩) (by decide) node_2131

theorem node_2596 : Outcome ⟨4, 3, 6, 10⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 6⟩) (by decide) node_1221

theorem node_2597 : Outcome ⟨4, 3, 6, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 6⟩) (by decide) node_1221

theorem node_2598 : Outcome ⟨4, 3, 6, 20⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 6⟩) (by decide) node_1221

theorem node_2599 : Outcome ⟨4, 4, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 5, 2⟩, ⟨2, 4, 5, 4⟩, ⟨4, 3, 5, 2⟩, ⟨4, 2, 5, 4⟩, ⟨4, 4, 4, 2⟩, ⟨4, 4, 3, 4⟩]
  exact AllWinning.cons node_2084 (AllWinning.cons node_1650 (AllWinning.cons node_2136 (AllWinning.cons node_1725 (AllWinning.cons node_2140 (AllWinning.cons node_1735 (AllWinning.nil))))))

theorem node_2600 : Outcome ⟨4, 4, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 5, 2⟩, ⟨2, 4, 5, 4⟩, ⟨1, 4, 5, 6⟩, ⟨0, 4, 5, 8⟩, ⟨4, 3, 5, 2⟩, ⟨4, 2, 5, 4⟩, ⟨4, 1, 5, 6⟩, ⟨4, 0, 5, 8⟩, ⟨4, 4, 4, 2⟩, ⟨4, 4, 3, 4⟩, ⟨4, 4, 2, 6⟩, ⟨4, 4, 1, 8⟩]
  exact AllWinning.cons node_2084 (AllWinning.cons node_1650 (AllWinning.cons node_1237 (AllWinning.cons node_927 (AllWinning.cons node_2136 (AllWinning.cons node_1725 (AllWinning.cons node_1376 (AllWinning.cons node_1060 (AllWinning.cons node_2140 (AllWinning.cons node_1735 (AllWinning.cons node_1391 (AllWinning.cons node_1079 (AllWinning.nil))))))))))))

theorem node_2601 : Outcome ⟨4, 4, 5, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2602 : Outcome ⟨4, 4, 5, 16⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2603 : Outcome ⟨4, 5, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 4, 2⟩, ⟨2, 5, 4, 4⟩, ⟨4, 4, 4, 2⟩, ⟨4, 3, 4, 4⟩, ⟨4, 5, 3, 2⟩, ⟨4, 5, 2, 4⟩]
  exact AllWinning.cons node_2088 (AllWinning.cons node_1656 (AllWinning.cons node_2140 (AllWinning.cons node_1731 (AllWinning.cons node_2143 (AllWinning.cons node_1739 (AllWinning.nil))))))

theorem node_2604 : Outcome ⟨4, 5, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 4, 2⟩, ⟨2, 5, 4, 4⟩, ⟨1, 5, 4, 6⟩, ⟨0, 5, 4, 8⟩, ⟨4, 4, 4, 2⟩, ⟨4, 3, 4, 4⟩, ⟨4, 2, 4, 6⟩, ⟨4, 1, 4, 8⟩, ⟨4, 5, 3, 2⟩, ⟨4, 5, 2, 4⟩, ⟨4, 5, 1, 6⟩, ⟨4, 5, 0, 8⟩]
  exact AllWinning.cons node_2088 (AllWinning.cons node_1656 (AllWinning.cons node_1243 (AllWinning.cons node_930 (AllWinning.cons node_2140 (AllWinning.cons node_1731 (AllWinning.cons node_1382 (AllWinning.cons node_1065 (AllWinning.cons node_2143 (AllWinning.cons node_1739 (AllWinning.cons node_1397 (AllWinning.cons node_1083 (AllWinning.nil))))))))))))

theorem node_2605 : Outcome ⟨4, 5, 4, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2606 : Outcome ⟨4, 5, 4, 16⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2607 : Outcome ⟨4, 6, 3, 2⟩ true :=
  Outcome.win (q := ⟨4, 6, 2, 2⟩) (by decide) node_2147

theorem node_2608 : Outcome ⟨4, 6, 3, 10⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 6⟩) (by decide) node_1249

theorem node_2609 : Outcome ⟨4, 6, 3, 14⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 6⟩) (by decide) node_1249

theorem node_2610 : Outcome ⟨4, 6, 3, 20⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 6⟩) (by decide) node_1249

theorem node_2611 : Outcome ⟨4, 7, 2, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 2⟩) (by decide) node_2096

theorem node_2612 : Outcome ⟨4, 7, 2, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2613 : Outcome ⟨4, 7, 2, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2614 : Outcome ⟨4, 7, 2, 14⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2615 : Outcome ⟨4, 7, 2, 16⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2616 : Outcome ⟨4, 7, 2, 28⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2617 : Outcome ⟨4, 8, 1, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 6⟩) (by decide) node_1270

theorem node_2618 : Outcome ⟨4, 8, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2619 : Outcome ⟨4, 8, 1, 14⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2620 : Outcome ⟨4, 8, 1, 16⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2621 : Outcome ⟨4, 8, 1, 32⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2622 : Outcome ⟨4, 9, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 0, 2⟩, ⟨2, 9, 0, 4⟩, ⟨4, 8, 0, 2⟩, ⟨4, 7, 0, 4⟩]
  exact AllWinning.cons node_2117 (AllWinning.cons node_1672 (AllWinning.cons node_2158 (AllWinning.cons node_1749 (AllWinning.nil))))

theorem node_2623 : Outcome ⟨4, 9, 0, 4⟩ true :=
  Outcome.win (q := ⟨1, 9, 0, 6⟩) (by decide) node_1275

theorem node_2624 : Outcome ⟨4, 9, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2625 : Outcome ⟨4, 9, 0, 10⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2626 : Outcome ⟨4, 9, 0, 16⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2627 : Outcome ⟨4, 9, 0, 32⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2628 : Outcome ⟨5, 0, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 0, 8, 2⟩, ⟨3, 0, 8, 4⟩, ⟨5, 0, 7, 2⟩, ⟨5, 0, 6, 4⟩]
  exact AllWinning.cons node_2122 (AllWinning.cons node_1678 (AllWinning.cons node_2161 (AllWinning.cons node_1754 (AllWinning.nil))))

theorem node_2629 : Outcome ⟨5, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2630 : Outcome ⟨5, 0, 8, 6⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2631 : Outcome ⟨5, 0, 8, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2632 : Outcome ⟨5, 0, 8, 20⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2633 : Outcome ⟨5, 0, 8, 30⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2634 : Outcome ⟨5, 1, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 7, 2⟩) (by decide) node_2125

theorem node_2635 : Outcome ⟨5, 1, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 1, 7, 2⟩) (by decide) node_2125

theorem node_2636 : Outcome ⟨5, 1, 7, 12⟩ true :=
  Outcome.win (q := ⟨4, 1, 7, 2⟩) (by decide) node_2125

theorem node_2637 : Outcome ⟨5, 2, 6, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 6, 2⟩) (by decide) node_2131

theorem node_2638 : Outcome ⟨5, 2, 6, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 6, 2⟩) (by decide) node_2131

theorem node_2639 : Outcome ⟨5, 2, 6, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 6, 2⟩) (by decide) node_2131

theorem node_2640 : Outcome ⟨5, 2, 6, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 6, 2⟩) (by decide) node_2131

theorem node_2641 : Outcome ⟨5, 3, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 5, 4⟩) (by decide) node_1691

theorem node_2642 : Outcome ⟨5, 3, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2643 : Outcome ⟨5, 3, 5, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2644 : Outcome ⟨5, 3, 5, 12⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2645 : Outcome ⟨5, 3, 5, 20⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2646 : Outcome ⟨5, 4, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 4, 4, 2⟩, ⟨3, 4, 4, 4⟩, ⟨2, 4, 4, 6⟩, ⟨1, 4, 4, 8⟩, ⟨5, 3, 4, 2⟩, ⟨5, 2, 4, 4⟩, ⟨5, 1, 4, 6⟩, ⟨5, 0, 4, 8⟩, ⟨5, 4, 3, 2⟩, ⟨5, 4, 2, 4⟩, ⟨5, 4, 1, 6⟩, ⟨5, 4, 0, 8⟩]
  exact AllWinning.cons node_2140 (AllWinning.cons node_1695 (AllWinning.cons node_1295 (AllWinning.cons node_972 (AllWinning.cons node_2172 (AllWinning.cons node_1759 (AllWinning.cons node_1420 (AllWinning.cons node_1086 (AllWinning.cons node_2176 (AllWinning.cons node_1768 (AllWinning.cons node_1434 (AllWinning.cons node_1101 (AllWinning.nil))))))))))))

theorem node_2647 : Outcome ⟨5, 4, 4, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 10⟩) (by decide) node_703

theorem node_2648 : Outcome ⟨5, 4, 4, 16⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 10⟩) (by decide) node_703

theorem node_2649 : Outcome ⟨5, 5, 3, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 3, 4⟩) (by decide) node_1699

theorem node_2650 : Outcome ⟨5, 5, 3, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2651 : Outcome ⟨5, 5, 3, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2652 : Outcome ⟨5, 5, 3, 12⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2653 : Outcome ⟨5, 5, 3, 20⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2654 : Outcome ⟨5, 6, 2, 2⟩ true :=
  Outcome.win (q := ⟨4, 6, 2, 2⟩) (by decide) node_2147

theorem node_2655 : Outcome ⟨5, 6, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 6, 2, 2⟩) (by decide) node_2147

theorem node_2656 : Outcome ⟨5, 6, 2, 8⟩ true :=
  Outcome.win (q := ⟨4, 6, 2, 2⟩) (by decide) node_2147

theorem node_2657 : Outcome ⟨5, 6, 2, 12⟩ true :=
  Outcome.win (q := ⟨4, 6, 2, 2⟩) (by decide) node_2147

theorem node_2658 : Outcome ⟨5, 7, 1, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 1, 2⟩) (by decide) node_2152

theorem node_2659 : Outcome ⟨5, 7, 1, 6⟩ true :=
  Outcome.win (q := ⟨4, 7, 1, 2⟩) (by decide) node_2152

theorem node_2660 : Outcome ⟨5, 7, 1, 12⟩ true :=
  Outcome.win (q := ⟨4, 7, 1, 2⟩) (by decide) node_2152

theorem node_2661 : Outcome ⟨5, 8, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 8, 0, 2⟩, ⟨3, 8, 0, 4⟩, ⟨5, 7, 0, 2⟩, ⟨5, 6, 0, 4⟩]
  exact AllWinning.cons node_2158 (AllWinning.cons node_1710 (AllWinning.cons node_2187 (AllWinning.cons node_1776 (AllWinning.nil))))

theorem node_2662 : Outcome ⟨5, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2663 : Outcome ⟨5, 8, 0, 6⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2664 : Outcome ⟨5, 8, 0, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2665 : Outcome ⟨5, 8, 0, 20⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2666 : Outcome ⟨5, 8, 0, 30⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2667 : Outcome ⟨6, 0, 7, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 2⟩) (by decide) node_2191

theorem node_2668 : Outcome ⟨6, 0, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 2⟩) (by decide) node_2191

theorem node_2669 : Outcome ⟨6, 0, 7, 16⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 2⟩) (by decide) node_2191

theorem node_2670 : Outcome ⟨6, 1, 6, 4⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 6⟩) (by decide) node_1321

theorem node_2671 : Outcome ⟨6, 1, 6, 20⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 6⟩) (by decide) node_1321

theorem node_2672 : Outcome ⟨6, 2, 5, 2⟩ true :=
  Outcome.win (q := ⟨6, 2, 4, 2⟩) (by decide) node_2208

theorem node_2673 : Outcome ⟨6, 2, 5, 4⟩ true :=
  Outcome.win (q := ⟨6, 2, 4, 2⟩) (by decide) node_2208

theorem node_2674 : Outcome ⟨6, 2, 5, 8⟩ true :=
  Outcome.win (q := ⟨6, 2, 4, 2⟩) (by decide) node_2208

theorem node_2675 : Outcome ⟨6, 2, 5, 12⟩ true :=
  Outcome.win (q := ⟨6, 2, 4, 2⟩) (by decide) node_2208

theorem node_2676 : Outcome ⟨6, 3, 4, 2⟩ true :=
  Outcome.win (q := ⟨6, 2, 4, 2⟩) (by decide) node_2208

theorem node_2677 : Outcome ⟨6, 3, 4, 10⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 6⟩) (by decide) node_1477

theorem node_2678 : Outcome ⟨6, 3, 4, 14⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 6⟩) (by decide) node_1477

theorem node_2679 : Outcome ⟨6, 3, 4, 20⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 6⟩) (by decide) node_1477

theorem node_2680 : Outcome ⟨6, 4, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 4, 2, 2⟩) (by decide) node_2217

theorem node_2681 : Outcome ⟨6, 4, 3, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 6⟩) (by decide) node_1457

theorem node_2682 : Outcome ⟨6, 4, 3, 14⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 6⟩) (by decide) node_1457

theorem node_2683 : Outcome ⟨6, 4, 3, 20⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 6⟩) (by decide) node_1457

theorem node_2684 : Outcome ⟨6, 5, 2, 2⟩ true :=
  Outcome.win (q := ⟨6, 4, 2, 2⟩) (by decide) node_2217

theorem node_2685 : Outcome ⟨6, 5, 2, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 2, 2⟩) (by decide) node_2217

theorem node_2686 : Outcome ⟨6, 5, 2, 8⟩ true :=
  Outcome.win (q := ⟨6, 4, 2, 2⟩) (by decide) node_2217

theorem node_2687 : Outcome ⟨6, 5, 2, 12⟩ true :=
  Outcome.win (q := ⟨6, 4, 2, 2⟩) (by decide) node_2217

theorem node_2688 : Outcome ⟨6, 6, 1, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 6⟩) (by decide) node_1352

theorem node_2689 : Outcome ⟨6, 6, 1, 20⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 6⟩) (by decide) node_1352

theorem node_2690 : Outcome ⟨6, 7, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 2⟩) (by decide) node_2225

theorem node_2691 : Outcome ⟨6, 7, 0, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 2⟩) (by decide) node_2225

theorem node_2692 : Outcome ⟨6, 7, 0, 16⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 2⟩) (by decide) node_2225

theorem node_2693 : Outcome ⟨7, 0, 6, 2⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 2⟩) (by decide) node_2191

theorem node_2694 : Outcome ⟨7, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 2⟩) (by decide) node_2191

theorem node_2695 : Outcome ⟨7, 0, 6, 16⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 2⟩) (by decide) node_2191

theorem node_2696 : Outcome ⟨7, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨7, 1, 4, 2⟩) (by decide) node_2243

theorem node_2697 : Outcome ⟨7, 1, 5, 6⟩ true :=
  Outcome.win (q := ⟨7, 1, 4, 2⟩) (by decide) node_2243

theorem node_2698 : Outcome ⟨7, 1, 5, 12⟩ true :=
  Outcome.win (q := ⟨7, 1, 4, 2⟩) (by decide) node_2243

theorem node_2699 : Outcome ⟨7, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨6, 2, 4, 2⟩) (by decide) node_2208

theorem node_2700 : Outcome ⟨7, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 12⟩) (by decide) node_510

theorem node_2701 : Outcome ⟨7, 2, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 12⟩) (by decide) node_510

theorem node_2702 : Outcome ⟨7, 2, 4, 14⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 12⟩) (by decide) node_510

theorem node_2703 : Outcome ⟨7, 2, 4, 16⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 12⟩) (by decide) node_510

theorem node_2704 : Outcome ⟨7, 2, 4, 28⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 12⟩) (by decide) node_510

theorem node_2705 : Outcome ⟨7, 3, 3, 2⟩ true :=
  Outcome.win (q := ⟨5, 3, 3, 4⟩) (by decide) node_1764

theorem node_2706 : Outcome ⟨7, 3, 3, 12⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 14⟩) (by decide) node_343

theorem node_2707 : Outcome ⟨7, 3, 3, 24⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 14⟩) (by decide) node_343

theorem node_2708 : Outcome ⟨7, 4, 2, 4⟩ true :=
  Outcome.win (q := ⟨6, 4, 2, 2⟩) (by decide) node_2217

theorem node_2709 : Outcome ⟨7, 4, 2, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 12⟩) (by decide) node_531

theorem node_2710 : Outcome ⟨7, 4, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 12⟩) (by decide) node_531

theorem node_2711 : Outcome ⟨7, 4, 2, 14⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 12⟩) (by decide) node_531

theorem node_2712 : Outcome ⟨7, 4, 2, 16⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 12⟩) (by decide) node_531

theorem node_2713 : Outcome ⟨7, 4, 2, 28⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 12⟩) (by decide) node_531

theorem node_2714 : Outcome ⟨7, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨7, 4, 1, 2⟩) (by decide) node_2281

theorem node_2715 : Outcome ⟨7, 5, 1, 6⟩ true :=
  Outcome.win (q := ⟨7, 4, 1, 2⟩) (by decide) node_2281

theorem node_2716 : Outcome ⟨7, 5, 1, 12⟩ true :=
  Outcome.win (q := ⟨7, 4, 1, 2⟩) (by decide) node_2281

theorem node_2717 : Outcome ⟨7, 6, 0, 2⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 2⟩) (by decide) node_2225

theorem node_2718 : Outcome ⟨7, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 2⟩) (by decide) node_2225

theorem node_2719 : Outcome ⟨7, 6, 0, 16⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 2⟩) (by decide) node_2225

theorem node_2720 : Outcome ⟨8, 0, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 0, 5, 2⟩, ⟨6, 0, 5, 4⟩, ⟨8, 0, 4, 2⟩, ⟨8, 0, 3, 4⟩]
  exact AllWinning.cons node_2239 (AllWinning.cons node_1779 (AllWinning.cons node_2291 (AllWinning.cons node_1817 (AllWinning.nil))))

theorem node_2721 : Outcome ⟨8, 0, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2722 : Outcome ⟨8, 0, 5, 6⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2723 : Outcome ⟨8, 0, 5, 10⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2724 : Outcome ⟨8, 0, 5, 20⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2725 : Outcome ⟨8, 0, 5, 30⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 6⟩) (by decide) node_1406

theorem node_2726 : Outcome ⟨8, 1, 4, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 1, 6⟩) (by decide) node_1518

theorem node_2727 : Outcome ⟨8, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 12⟩) (by decide) node_561

theorem node_2728 : Outcome ⟨8, 1, 4, 14⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 12⟩) (by decide) node_561

theorem node_2729 : Outcome ⟨8, 1, 4, 16⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 12⟩) (by decide) node_561

theorem node_2730 : Outcome ⟨8, 1, 4, 32⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 12⟩) (by decide) node_561

theorem node_2731 : Outcome ⟨8, 2, 3, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 2⟩) (by decide) node_2249

theorem node_2732 : Outcome ⟨8, 2, 3, 4⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 2⟩) (by decide) node_2249

theorem node_2733 : Outcome ⟨8, 2, 3, 8⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 2⟩) (by decide) node_2249

theorem node_2734 : Outcome ⟨8, 2, 3, 28⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 2⟩) (by decide) node_2249

theorem node_2735 : Outcome ⟨8, 2, 3, 32⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 2⟩) (by decide) node_2249

theorem node_2736 : Outcome ⟨8, 3, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 2⟩) (by decide) node_2265

theorem node_2737 : Outcome ⟨8, 3, 2, 4⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 2⟩) (by decide) node_2265

theorem node_2738 : Outcome ⟨8, 3, 2, 8⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 2⟩) (by decide) node_2265

theorem node_2739 : Outcome ⟨8, 3, 2, 28⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 2⟩) (by decide) node_2265

theorem node_2740 : Outcome ⟨8, 3, 2, 32⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 2⟩) (by decide) node_2265

theorem node_2741 : Outcome ⟨8, 4, 1, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 1, 6⟩) (by decide) node_1518

theorem node_2742 : Outcome ⟨8, 4, 1, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 12⟩) (by decide) node_583

theorem node_2743 : Outcome ⟨8, 4, 1, 14⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 12⟩) (by decide) node_583

theorem node_2744 : Outcome ⟨8, 4, 1, 16⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 12⟩) (by decide) node_583

theorem node_2745 : Outcome ⟨8, 4, 1, 32⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 12⟩) (by decide) node_583

theorem node_2746 : Outcome ⟨8, 5, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 5, 0, 2⟩, ⟨6, 5, 0, 4⟩, ⟨8, 4, 0, 2⟩, ⟨8, 3, 0, 4⟩]
  exact AllWinning.cons node_2287 (AllWinning.cons node_1796 (AllWinning.cons node_2312 (AllWinning.cons node_1833 (AllWinning.nil))))

theorem node_2747 : Outcome ⟨8, 5, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2748 : Outcome ⟨8, 5, 0, 6⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2749 : Outcome ⟨8, 5, 0, 10⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2750 : Outcome ⟨8, 5, 0, 20⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2751 : Outcome ⟨8, 5, 0, 30⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 6⟩) (by decide) node_1440

theorem node_2752 : Outcome ⟨9, 0, 4, 4⟩ true :=
  Outcome.win (q := ⟨9, 0, 1, 6⟩) (by decide) node_1528

theorem node_2753 : Outcome ⟨9, 0, 4, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2754 : Outcome ⟨9, 0, 4, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2755 : Outcome ⟨9, 0, 4, 16⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2756 : Outcome ⟨9, 0, 4, 32⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 10⟩) (by decide) node_824

theorem node_2757 : Outcome ⟨9, 1, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 3, 2⟩, ⟨7, 1, 3, 4⟩, ⟨9, 0, 3, 2⟩, ⟨9, 1, 2, 2⟩, ⟨9, 1, 1, 4⟩]
  exact AllWinning.cons node_2295 (AllWinning.cons node_1803 (AllWinning.cons node_2316 (AllWinning.cons node_2321 (AllWinning.cons node_1843 (AllWinning.nil)))))

theorem node_2758 : Outcome ⟨9, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 6⟩) (by decide) node_1457

theorem node_2759 : Outcome ⟨9, 1, 3, 10⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 6⟩) (by decide) node_1457

theorem node_2760 : Outcome ⟨9, 1, 3, 20⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 6⟩) (by decide) node_1457

theorem node_2761 : Outcome ⟨9, 1, 3, 22⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 6⟩) (by decide) node_1457

theorem node_2762 : Outcome ⟨9, 2, 2, 4⟩ true :=
  Outcome.win (q := ⟨8, 2, 2, 2⟩) (by decide) node_2301

theorem node_2763 : Outcome ⟨9, 2, 2, 8⟩ true :=
  Outcome.win (q := ⟨8, 2, 2, 2⟩) (by decide) node_2301

theorem node_2764 : Outcome ⟨9, 2, 2, 26⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 18⟩) (by decide) node_149

theorem node_2765 : Outcome ⟨9, 3, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 3, 1, 2⟩, ⟨7, 3, 1, 4⟩, ⟨9, 2, 1, 2⟩, ⟨9, 1, 1, 4⟩, ⟨9, 3, 0, 2⟩]
  exact AllWinning.cons node_2306 (AllWinning.cons node_1809 (AllWinning.cons node_2325 (AllWinning.cons node_1843 (AllWinning.cons node_2329 (AllWinning.nil)))))

theorem node_2766 : Outcome ⟨9, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 6⟩) (by decide) node_1477

theorem node_2767 : Outcome ⟨9, 3, 1, 10⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 6⟩) (by decide) node_1477

theorem node_2768 : Outcome ⟨9, 3, 1, 20⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 6⟩) (by decide) node_1477

theorem node_2769 : Outcome ⟨9, 3, 1, 22⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 6⟩) (by decide) node_1477

theorem node_2770 : Outcome ⟨9, 4, 0, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 0, 6⟩) (by decide) node_1533

theorem node_2771 : Outcome ⟨9, 4, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2772 : Outcome ⟨9, 4, 0, 10⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2773 : Outcome ⟨9, 4, 0, 16⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2774 : Outcome ⟨9, 4, 0, 32⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 10⟩) (by decide) node_850

theorem node_2775 : Outcome ⟨10, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 2⟩) (by decide) node_2334

theorem node_2776 : Outcome ⟨10, 0, 3, 12⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 14⟩) (by decide) node_409

theorem node_2777 : Outcome ⟨10, 0, 3, 14⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 14⟩) (by decide) node_409

theorem node_2778 : Outcome ⟨10, 0, 3, 26⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 14⟩) (by decide) node_409

theorem node_2779 : Outcome ⟨10, 1, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 2⟩) (by decide) node_2334

theorem node_2780 : Outcome ⟨10, 1, 2, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2781 : Outcome ⟨10, 1, 2, 14⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2782 : Outcome ⟨10, 1, 2, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 12⟩) (by decide) node_621

theorem node_2783 : Outcome ⟨10, 2, 1, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 2⟩) (by decide) node_2342

theorem node_2784 : Outcome ⟨10, 2, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2785 : Outcome ⟨10, 2, 1, 14⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2786 : Outcome ⟨10, 2, 1, 24⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 12⟩) (by decide) node_639

theorem node_2787 : Outcome ⟨10, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 2⟩) (by decide) node_2342

theorem node_2788 : Outcome ⟨10, 3, 0, 12⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 14⟩) (by decide) node_432

theorem node_2789 : Outcome ⟨10, 3, 0, 14⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 14⟩) (by decide) node_432

theorem node_2790 : Outcome ⟨10, 3, 0, 26⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 14⟩) (by decide) node_432

theorem node_2791 : Outcome ⟨11, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 2⟩) (by decide) node_2334

theorem node_2792 : Outcome ⟨11, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 2⟩) (by decide) node_2334

theorem node_2793 : Outcome ⟨11, 0, 2, 8⟩ true :=
  Outcome.win (q := ⟨10, 0, 2, 2⟩) (by decide) node_2334

theorem node_2794 : Outcome ⟨11, 0, 2, 12⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 18⟩) (by decide) node_191

theorem node_2795 : Outcome ⟨11, 0, 2, 18⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 18⟩) (by decide) node_191

theorem node_2796 : Outcome ⟨11, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 1, 1, 2⟩, ⟨9, 1, 1, 4⟩, ⟨11, 0, 1, 2⟩, ⟨11, 1, 0, 2⟩]
  exact AllWinning.cons node_2339 (AllWinning.cons node_1843 (AllWinning.cons node_2347 (AllWinning.cons node_2352 (AllWinning.nil))))

theorem node_2797 : Outcome ⟨11, 1, 1, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 1, 6⟩) (by decide) node_1518

theorem node_2798 : Outcome ⟨11, 1, 1, 12⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 22⟩) (by decide) node_42

theorem node_2799 : Outcome ⟨11, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 2⟩) (by decide) node_2342

theorem node_2800 : Outcome ⟨11, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 2⟩) (by decide) node_2342

theorem node_2801 : Outcome ⟨11, 2, 0, 8⟩ true :=
  Outcome.win (q := ⟨10, 2, 0, 2⟩) (by decide) node_2342

theorem node_2802 : Outcome ⟨11, 2, 0, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 18⟩) (by decide) node_212

theorem node_2803 : Outcome ⟨11, 2, 0, 18⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 18⟩) (by decide) node_212

theorem node_2804 : Outcome ⟨12, 0, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 0, 1, 2⟩, ⟨10, 0, 1, 4⟩, ⟨12, 0, 0, 2⟩]
  exact AllWinning.cons node_2347 (AllWinning.cons node_1851 (AllWinning.cons node_2357 (AllWinning.nil)))

theorem node_2805 : Outcome ⟨12, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 0, 1, 6⟩) (by decide) node_1528

theorem node_2806 : Outcome ⟨12, 0, 1, 6⟩ true :=
  Outcome.win (q := ⟨9, 0, 1, 6⟩) (by decide) node_1528

theorem node_2807 : Outcome ⟨12, 0, 1, 16⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 22⟩) (by decide) node_64

theorem node_2808 : Outcome ⟨12, 0, 1, 22⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 22⟩) (by decide) node_64

theorem node_2809 : Outcome ⟨12, 1, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨11, 1, 0, 2⟩, ⟨10, 1, 0, 4⟩, ⟨12, 0, 0, 2⟩]
  exact AllWinning.cons node_2352 (AllWinning.cons node_1856 (AllWinning.cons node_2357 (AllWinning.nil)))

theorem node_2810 : Outcome ⟨12, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 0, 6⟩) (by decide) node_1533

theorem node_2811 : Outcome ⟨12, 1, 0, 6⟩ true :=
  Outcome.win (q := ⟨9, 1, 0, 6⟩) (by decide) node_1533

theorem node_2812 : Outcome ⟨12, 1, 0, 16⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 22⟩) (by decide) node_81

theorem node_2813 : Outcome ⟨12, 1, 0, 22⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 22⟩) (by decide) node_81

theorem node_2814 : Outcome ⟨13, 0, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 0, 2⟩, ⟨11, 0, 0, 4⟩]
  exact AllWinning.cons node_2357 (AllWinning.cons node_1861 (AllWinning.nil))

theorem node_2815 : Outcome ⟨13, 0, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 0, 2⟩, ⟨11, 0, 0, 4⟩, ⟨10, 0, 0, 6⟩, ⟨9, 0, 0, 8⟩]
  exact AllWinning.cons node_2357 (AllWinning.cons node_1861 (AllWinning.cons node_1538 (AllWinning.cons node_1149 (AllWinning.nil))))

theorem node_2816 : Outcome ⟨13, 0, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 0, 2⟩, ⟨11, 0, 0, 4⟩, ⟨10, 0, 0, 6⟩, ⟨9, 0, 0, 8⟩, ⟨8, 0, 0, 10⟩, ⟨7, 0, 0, 12⟩]
  exact AllWinning.cons node_2357 (AllWinning.cons node_1861 (AllWinning.cons node_1538 (AllWinning.cons node_1149 (AllWinning.cons node_905 (AllWinning.cons node_678 (AllWinning.nil))))))

theorem node_2817 : Outcome ⟨13, 0, 0, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 0, 2⟩, ⟨11, 0, 0, 4⟩, ⟨10, 0, 0, 6⟩, ⟨9, 0, 0, 8⟩, ⟨8, 0, 0, 10⟩, ⟨7, 0, 0, 12⟩, ⟨6, 0, 0, 14⟩, ⟨5, 0, 0, 16⟩]
  exact AllWinning.cons node_2357 (AllWinning.cons node_1861 (AllWinning.cons node_1538 (AllWinning.cons node_1149 (AllWinning.cons node_905 (AllWinning.cons node_678 (AllWinning.cons node_465 (AllWinning.cons node_323 (AllWinning.nil))))))))

theorem node_2818 : Outcome ⟨13, 0, 0, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 0, 2⟩, ⟨11, 0, 0, 4⟩, ⟨10, 0, 0, 6⟩, ⟨9, 0, 0, 8⟩, ⟨8, 0, 0, 10⟩, ⟨7, 0, 0, 12⟩, ⟨6, 0, 0, 14⟩, ⟨5, 0, 0, 16⟩, ⟨4, 0, 0, 18⟩, ⟨3, 0, 0, 20⟩]
  exact AllWinning.cons node_2357 (AllWinning.cons node_1861 (AllWinning.cons node_1538 (AllWinning.cons node_1149 (AllWinning.cons node_905 (AllWinning.cons node_678 (AllWinning.cons node_465 (AllWinning.cons node_323 (AllWinning.cons node_233 (AllWinning.cons node_132 (AllWinning.nil))))))))))

theorem node_2819 : Outcome ⟨13, 0, 0, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 0, 0, 2⟩, ⟨11, 0, 0, 4⟩, ⟨10, 0, 0, 6⟩, ⟨9, 0, 0, 8⟩, ⟨8, 0, 0, 10⟩, ⟨7, 0, 0, 12⟩, ⟨6, 0, 0, 14⟩, ⟨5, 0, 0, 16⟩, ⟨4, 0, 0, 18⟩, ⟨3, 0, 0, 20⟩, ⟨2, 0, 0, 22⟩, ⟨1, 0, 0, 24⟩]
  exact AllWinning.cons node_2357 (AllWinning.cons node_1861 (AllWinning.cons node_1538 (AllWinning.cons node_1149 (AllWinning.cons node_905 (AllWinning.cons node_678 (AllWinning.cons node_465 (AllWinning.cons node_323 (AllWinning.cons node_233 (AllWinning.cons node_132 (AllWinning.cons node_92 (AllWinning.cons node_26 (AllWinning.nil))))))))))))

theorem node_2820 : Outcome ⟨13, 0, 0, 26⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 26⟩) (by decide) node_12

theorem node_2821 : Outcome ⟨0, 0, 14, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 2⟩) (by decide) node_2360

theorem node_2822 : Outcome ⟨0, 0, 14, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 2⟩) (by decide) node_2360

theorem node_2823 : Outcome ⟨0, 0, 14, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 2⟩) (by decide) node_2360

theorem node_2824 : Outcome ⟨0, 0, 14, 28⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 28⟩) (by decide) node_13

theorem node_2825 : Outcome ⟨0, 1, 13, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 2⟩) (by decide) node_2360

theorem node_2826 : Outcome ⟨0, 1, 13, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 13, 2⟩) (by decide) node_2360

theorem node_2827 : Outcome ⟨0, 1, 13, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 24⟩) (by decide) node_43

theorem node_2828 : Outcome ⟨0, 2, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 4⟩) (by decide) node_1873

theorem node_2829 : Outcome ⟨0, 2, 12, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 4⟩) (by decide) node_1873

theorem node_2830 : Outcome ⟨0, 2, 12, 6⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 4⟩) (by decide) node_1873

theorem node_2831 : Outcome ⟨0, 2, 12, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 20⟩) (by decide) node_150

theorem node_2832 : Outcome ⟨0, 2, 12, 20⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 20⟩) (by decide) node_150

theorem node_2833 : Outcome ⟨0, 2, 12, 28⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 20⟩) (by decide) node_150

theorem node_2834 : Outcome ⟨0, 3, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 11, 2⟩, ⟨0, 1, 11, 4⟩, ⟨0, 3, 10, 2⟩, ⟨0, 3, 9, 4⟩]
  exact AllWinning.cons node_2372 (AllWinning.cons node_1868 (AllWinning.cons node_2376 (AllWinning.cons node_1878 (AllWinning.nil))))

theorem node_2835 : Outcome ⟨0, 3, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 11, 2⟩, ⟨0, 1, 11, 4⟩, ⟨0, 0, 11, 6⟩, ⟨0, 3, 10, 2⟩, ⟨0, 3, 9, 4⟩, ⟨0, 3, 8, 6⟩, ⟨0, 3, 7, 8⟩]
  exact AllWinning.cons node_2372 (AllWinning.cons node_1868 (AllWinning.cons node_1542 (AllWinning.cons node_2376 (AllWinning.cons node_1878 (AllWinning.cons node_1557 (AllWinning.cons node_1166 (AllWinning.nil)))))))

theorem node_2836 : Outcome ⟨0, 3, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 11, 2⟩, ⟨0, 1, 11, 4⟩, ⟨0, 0, 11, 6⟩, ⟨0, 3, 10, 2⟩, ⟨0, 3, 9, 4⟩, ⟨0, 3, 8, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 3, 6, 10⟩, ⟨0, 3, 5, 12⟩]
  exact AllWinning.cons node_2372 (AllWinning.cons node_1868 (AllWinning.cons node_1542 (AllWinning.cons node_2376 (AllWinning.cons node_1878 (AllWinning.cons node_1557 (AllWinning.cons node_1166 (AllWinning.cons node_924 (AllWinning.cons node_697 (AllWinning.nil)))))))))

theorem node_2837 : Outcome ⟨0, 3, 11, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 16⟩) (by decide) node_344

theorem node_2838 : Outcome ⟨0, 3, 11, 16⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 16⟩) (by decide) node_344

theorem node_2839 : Outcome ⟨0, 4, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 4⟩) (by decide) node_1873

theorem node_2840 : Outcome ⟨0, 4, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 10, 4⟩) (by decide) node_1873

theorem node_2841 : Outcome ⟨0, 4, 10, 12⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 12⟩) (by decide) node_704

theorem node_2842 : Outcome ⟨0, 4, 10, 14⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 12⟩) (by decide) node_704

theorem node_2843 : Outcome ⟨0, 5, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 4, 9, 2⟩) (by decide) node_2381

theorem node_2844 : Outcome ⟨0, 5, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 8⟩) (by decide) node_1174

theorem node_2845 : Outcome ⟨0, 5, 9, 18⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 8⟩) (by decide) node_1174

theorem node_2846 : Outcome ⟨0, 6, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 4⟩) (by decide) node_1890

theorem node_2847 : Outcome ⟨0, 6, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 4⟩) (by decide) node_1890

theorem node_2848 : Outcome ⟨0, 6, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 4⟩) (by decide) node_1890

theorem node_2849 : Outcome ⟨0, 7, 7, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.nil))))

theorem node_2850 : Outcome ⟨0, 7, 7, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.nil))))))))

theorem node_2851 : Outcome ⟨0, 7, 7, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.nil))))))))))))

theorem node_2852 : Outcome ⟨0, 7, 7, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2853 : Outcome ⟨0, 7, 7, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2854 : Outcome ⟨0, 7, 7, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2855 : Outcome ⟨0, 7, 7, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2856 : Outcome ⟨0, 7, 7, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2857 : Outcome ⟨0, 7, 7, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2858 : Outcome ⟨0, 7, 7, 20⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2859 : Outcome ⟨0, 7, 7, 22⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2860 : Outcome ⟨0, 7, 7, 24⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2861 : Outcome ⟨0, 7, 7, 26⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 7, 2⟩, ⟨0, 5, 7, 4⟩, ⟨0, 4, 7, 6⟩, ⟨0, 3, 7, 8⟩, ⟨0, 2, 7, 10⟩, ⟨0, 1, 7, 12⟩, ⟨0, 0, 7, 14⟩, ⟨0, 7, 6, 2⟩, ⟨0, 7, 5, 4⟩, ⟨0, 7, 4, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 7, 2, 10⟩, ⟨0, 7, 1, 12⟩, ⟨0, 7, 0, 14⟩]
  exact AllWinning.cons node_2393 (AllWinning.cons node_1886 (AllWinning.cons node_1563 (AllWinning.cons node_1166 (AllWinning.cons node_919 (AllWinning.cons node_688 (AllWinning.cons node_469 (AllWinning.cons node_2396 (AllWinning.cons node_1904 (AllWinning.cons node_1573 (AllWinning.cons node_1190 (AllWinning.cons node_940 (AllWinning.cons node_726 (AllWinning.cons node_495 (AllWinning.nil))))))))))))))

theorem node_2862 : Outcome ⟨0, 8, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 4⟩) (by decide) node_1890

theorem node_2863 : Outcome ⟨0, 8, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 4⟩) (by decide) node_1890

theorem node_2864 : Outcome ⟨0, 8, 6, 14⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 4⟩) (by decide) node_1890

theorem node_2865 : Outcome ⟨0, 9, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 5, 2⟩) (by decide) node_2399

theorem node_2866 : Outcome ⟨0, 9, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 8⟩) (by decide) node_1174

theorem node_2867 : Outcome ⟨0, 9, 5, 18⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 8⟩) (by decide) node_1174

theorem node_2868 : Outcome ⟨0, 10, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 4⟩) (by decide) node_1916

theorem node_2869 : Outcome ⟨0, 10, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 4⟩) (by decide) node_1916

theorem node_2870 : Outcome ⟨0, 10, 4, 12⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 12⟩) (by decide) node_704

theorem node_2871 : Outcome ⟨0, 10, 4, 14⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 12⟩) (by decide) node_704

theorem node_2872 : Outcome ⟨0, 11, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 3, 2⟩, ⟨0, 9, 3, 4⟩, ⟨0, 11, 2, 2⟩, ⟨0, 11, 1, 4⟩]
  exact AllWinning.cons node_2410 (AllWinning.cons node_1911 (AllWinning.cons node_2415 (AllWinning.cons node_1921 (AllWinning.nil))))

theorem node_2873 : Outcome ⟨0, 11, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 3, 2⟩, ⟨0, 9, 3, 4⟩, ⟨0, 8, 3, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 11, 2, 2⟩, ⟨0, 11, 1, 4⟩, ⟨0, 11, 0, 6⟩]
  exact AllWinning.cons node_2410 (AllWinning.cons node_1911 (AllWinning.cons node_1578 (AllWinning.cons node_1190 (AllWinning.cons node_2415 (AllWinning.cons node_1921 (AllWinning.cons node_1594 (AllWinning.nil)))))))

theorem node_2874 : Outcome ⟨0, 11, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 3, 2⟩, ⟨0, 9, 3, 4⟩, ⟨0, 8, 3, 6⟩, ⟨0, 7, 3, 8⟩, ⟨0, 6, 3, 10⟩, ⟨0, 5, 3, 12⟩, ⟨0, 11, 2, 2⟩, ⟨0, 11, 1, 4⟩, ⟨0, 11, 0, 6⟩]
  exact AllWinning.cons node_2410 (AllWinning.cons node_1911 (AllWinning.cons node_1578 (AllWinning.cons node_1190 (AllWinning.cons node_935 (AllWinning.cons node_717 (AllWinning.cons node_2415 (AllWinning.cons node_1921 (AllWinning.cons node_1594 (AllWinning.nil)))))))))

theorem node_2875 : Outcome ⟨0, 11, 3, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 16⟩) (by decide) node_344

theorem node_2876 : Outcome ⟨0, 11, 3, 16⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 16⟩) (by decide) node_344

theorem node_2877 : Outcome ⟨0, 12, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 4⟩) (by decide) node_1916

theorem node_2878 : Outcome ⟨0, 12, 2, 4⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 4⟩) (by decide) node_1916

theorem node_2879 : Outcome ⟨0, 12, 2, 6⟩ true :=
  Outcome.win (q := ⟨0, 10, 2, 4⟩) (by decide) node_1916

theorem node_2880 : Outcome ⟨0, 12, 2, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 20⟩) (by decide) node_150

theorem node_2881 : Outcome ⟨0, 12, 2, 20⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 20⟩) (by decide) node_150

theorem node_2882 : Outcome ⟨0, 12, 2, 28⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 20⟩) (by decide) node_150

theorem node_2883 : Outcome ⟨0, 13, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 1, 2⟩) (by decide) node_2419

theorem node_2884 : Outcome ⟨0, 13, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 12, 1, 2⟩) (by decide) node_2419

theorem node_2885 : Outcome ⟨0, 13, 1, 24⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 24⟩) (by decide) node_43

theorem node_2886 : Outcome ⟨0, 14, 0, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 2⟩) (by decide) node_2424

theorem node_2887 : Outcome ⟨0, 14, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 0, 2⟩) (by decide) node_2424

end RQ9F1
