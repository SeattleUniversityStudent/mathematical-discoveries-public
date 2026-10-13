import Chunk05
set_option autoImplicit false
namespace RQ9F1

theorem node_1509 : Outcome ⟨7, 3, 0, 8⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

theorem node_1510 : Outcome ⟨7, 3, 0, 18⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 8⟩) (by decide) node_429

theorem node_1511 : Outcome ⟨8, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 4⟩) (by decide) node_903

theorem node_1512 : Outcome ⟨8, 0, 2, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 4⟩) (by decide) node_903

theorem node_1513 : Outcome ⟨8, 0, 2, 12⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 12⟩) (by decide) node_188

theorem node_1514 : Outcome ⟨8, 0, 2, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 12⟩) (by decide) node_188

theorem node_1515 : Outcome ⟨8, 0, 2, 38⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 12⟩) (by decide) node_188

theorem node_1516 : Outcome ⟨8, 1, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 1, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨8, 0, 1, 2⟩, ⟨8, 1, 0, 2⟩]
  exact AllWinning.cons node_1128 (AllWinning.cons node_884 (AllWinning.cons node_1137 (AllWinning.cons node_1142 (AllWinning.nil))))

theorem node_1517 : Outcome ⟨8, 1, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 1, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨5, 1, 1, 6⟩, ⟨4, 1, 1, 8⟩, ⟨8, 0, 1, 2⟩, ⟨8, 1, 0, 2⟩]
  exact AllWinning.cons node_1128 (AllWinning.cons node_884 (AllWinning.cons node_660 (AllWinning.cons node_449 (AllWinning.cons node_1137 (AllWinning.cons node_1142 (AllWinning.nil))))))

theorem node_1518 : Outcome ⟨8, 1, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 1, 1, 2⟩, ⟨6, 1, 1, 4⟩, ⟨5, 1, 1, 6⟩, ⟨4, 1, 1, 8⟩, ⟨3, 1, 1, 10⟩, ⟨2, 1, 1, 12⟩, ⟨8, 0, 1, 2⟩, ⟨8, 1, 0, 2⟩]
  exact AllWinning.cons node_1128 (AllWinning.cons node_884 (AllWinning.cons node_660 (AllWinning.cons node_449 (AllWinning.cons node_302 (AllWinning.cons node_202 (AllWinning.cons node_1137 (AllWinning.cons node_1142 (AllWinning.nil))))))))

theorem node_1519 : Outcome ⟨8, 1, 1, 10⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 16⟩) (by decide) node_39

theorem node_1520 : Outcome ⟨8, 1, 1, 22⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 16⟩) (by decide) node_39

theorem node_1521 : Outcome ⟨8, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 4⟩) (by decide) node_903

theorem node_1522 : Outcome ⟨8, 2, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 4⟩) (by decide) node_903

theorem node_1523 : Outcome ⟨8, 2, 0, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1524 : Outcome ⟨8, 2, 0, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1525 : Outcome ⟨8, 2, 0, 38⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 12⟩) (by decide) node_209

theorem node_1526 : Outcome ⟨9, 0, 1, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 1, 2⟩, ⟨7, 0, 1, 4⟩, ⟨9, 0, 0, 2⟩]
  exact AllWinning.cons node_1137 (AllWinning.cons node_891 (AllWinning.cons node_1147 (AllWinning.nil)))

theorem node_1527 : Outcome ⟨9, 0, 1, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 1, 2⟩, ⟨7, 0, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨5, 0, 1, 8⟩, ⟨9, 0, 0, 2⟩]
  exact AllWinning.cons node_1137 (AllWinning.cons node_891 (AllWinning.cons node_668 (AllWinning.cons node_457 (AllWinning.cons node_1147 (AllWinning.nil)))))

theorem node_1528 : Outcome ⟨9, 0, 1, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 0, 1, 2⟩, ⟨7, 0, 1, 4⟩, ⟨6, 0, 1, 6⟩, ⟨5, 0, 1, 8⟩, ⟨4, 0, 1, 10⟩, ⟨3, 0, 1, 12⟩, ⟨9, 0, 0, 2⟩]
  exact AllWinning.cons node_1137 (AllWinning.cons node_891 (AllWinning.cons node_668 (AllWinning.cons node_457 (AllWinning.cons node_312 (AllWinning.cons node_224 (AllWinning.cons node_1147 (AllWinning.nil)))))))

theorem node_1529 : Outcome ⟨9, 0, 1, 10⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 16⟩) (by decide) node_61

theorem node_1530 : Outcome ⟨9, 0, 1, 16⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 16⟩) (by decide) node_61

theorem node_1531 : Outcome ⟨9, 1, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 0, 2⟩, ⟨7, 1, 0, 4⟩, ⟨9, 0, 0, 2⟩]
  exact AllWinning.cons node_1142 (AllWinning.cons node_897 (AllWinning.cons node_1147 (AllWinning.nil)))

theorem node_1532 : Outcome ⟨9, 1, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 0, 2⟩, ⟨7, 1, 0, 4⟩, ⟨6, 1, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨9, 0, 0, 2⟩]
  exact AllWinning.cons node_1142 (AllWinning.cons node_897 (AllWinning.cons node_673 (AllWinning.cons node_460 (AllWinning.cons node_1147 (AllWinning.nil)))))

theorem node_1533 : Outcome ⟨9, 1, 0, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 1, 0, 2⟩, ⟨7, 1, 0, 4⟩, ⟨6, 1, 0, 6⟩, ⟨5, 1, 0, 8⟩, ⟨4, 1, 0, 10⟩, ⟨3, 1, 0, 12⟩, ⟨9, 0, 0, 2⟩]
  exact AllWinning.cons node_1142 (AllWinning.cons node_897 (AllWinning.cons node_673 (AllWinning.cons node_460 (AllWinning.cons node_317 (AllWinning.cons node_229 (AllWinning.cons node_1147 (AllWinning.nil)))))))

theorem node_1534 : Outcome ⟨9, 1, 0, 10⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 16⟩) (by decide) node_78

theorem node_1535 : Outcome ⟨9, 1, 0, 16⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 16⟩) (by decide) node_78

theorem node_1536 : Outcome ⟨10, 0, 0, 2⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 4⟩) (by decide) node_903

theorem node_1537 : Outcome ⟨10, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 4⟩) (by decide) node_903

theorem node_1538 : Outcome ⟨10, 0, 0, 6⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 4⟩) (by decide) node_903

theorem node_1539 : Outcome ⟨10, 0, 0, 20⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 20⟩) (by decide) node_9

theorem node_1540 : Outcome ⟨0, 0, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 0, 10, 2⟩, ⟨0, 0, 9, 4⟩]
  exact AllWinning.cons node_1151 (AllWinning.cons node_908 (AllWinning.nil))

theorem node_1541 : Outcome ⟨0, 0, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 6⟩) (by decide) node_682

theorem node_1542 : Outcome ⟨0, 0, 11, 6⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 6⟩) (by decide) node_682

theorem node_1543 : Outcome ⟨0, 0, 11, 22⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 22⟩) (by decide) node_10

theorem node_1544 : Outcome ⟨0, 1, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 2⟩) (by decide) node_1155

theorem node_1545 : Outcome ⟨0, 1, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 2⟩) (by decide) node_1155

theorem node_1546 : Outcome ⟨0, 1, 10, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 2⟩) (by decide) node_1155

theorem node_1547 : Outcome ⟨0, 1, 10, 18⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 18⟩) (by decide) node_40

theorem node_1548 : Outcome ⟨0, 1, 10, 28⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 18⟩) (by decide) node_40

theorem node_1549 : Outcome ⟨0, 2, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 7, 4⟩) (by decide) node_917

theorem node_1550 : Outcome ⟨0, 2, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 2, 7, 4⟩) (by decide) node_917

theorem node_1551 : Outcome ⟨0, 2, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1552 : Outcome ⟨0, 2, 9, 12⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1553 : Outcome ⟨0, 2, 9, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1554 : Outcome ⟨0, 2, 9, 30⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1555 : Outcome ⟨0, 3, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 2, 8, 2⟩, ⟨0, 1, 8, 4⟩, ⟨0, 3, 7, 2⟩, ⟨0, 3, 6, 4⟩]
  exact AllWinning.cons node_1160 (AllWinning.cons node_912 (AllWinning.cons node_1164 (AllWinning.cons node_922 (AllWinning.nil))))

theorem node_1556 : Outcome ⟨0, 3, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 6⟩) (by decide) node_682

theorem node_1557 : Outcome ⟨0, 3, 8, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1558 : Outcome ⟨0, 3, 8, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1559 : Outcome ⟨0, 3, 8, 16⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1560 : Outcome ⟨0, 3, 8, 32⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1561 : Outcome ⟨0, 4, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 7, 4⟩) (by decide) node_917

theorem node_1562 : Outcome ⟨0, 4, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1563 : Outcome ⟨0, 4, 7, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1564 : Outcome ⟨0, 4, 7, 10⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1565 : Outcome ⟨0, 4, 7, 20⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1566 : Outcome ⟨0, 5, 6, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1567 : Outcome ⟨0, 5, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1568 : Outcome ⟨0, 5, 6, 24⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1569 : Outcome ⟨0, 6, 5, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1570 : Outcome ⟨0, 6, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1571 : Outcome ⟨0, 6, 5, 24⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1572 : Outcome ⟨0, 7, 4, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 2, 4⟩) (by decide) node_938

theorem node_1573 : Outcome ⟨0, 7, 4, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1574 : Outcome ⟨0, 7, 4, 10⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1575 : Outcome ⟨0, 7, 4, 20⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1576 : Outcome ⟨0, 8, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 7, 3, 2⟩, ⟨0, 6, 3, 4⟩, ⟨0, 8, 2, 2⟩, ⟨0, 8, 1, 4⟩]
  exact AllWinning.cons node_1188 (AllWinning.cons node_933 (AllWinning.cons node_1192 (AllWinning.cons node_943 (AllWinning.nil))))

theorem node_1577 : Outcome ⟨0, 8, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 6⟩) (by decide) node_731

theorem node_1578 : Outcome ⟨0, 8, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1579 : Outcome ⟨0, 8, 3, 10⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1580 : Outcome ⟨0, 8, 3, 16⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1581 : Outcome ⟨0, 8, 3, 32⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1582 : Outcome ⟨0, 9, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 2, 4⟩) (by decide) node_938

theorem node_1583 : Outcome ⟨0, 9, 2, 8⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1584 : Outcome ⟨0, 9, 2, 12⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1585 : Outcome ⟨0, 9, 2, 14⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1586 : Outcome ⟨0, 9, 2, 30⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1587 : Outcome ⟨0, 10, 1, 2⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 2⟩) (by decide) node_1196

theorem node_1588 : Outcome ⟨0, 10, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 2⟩) (by decide) node_1196

theorem node_1589 : Outcome ⟨0, 10, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 2⟩) (by decide) node_1196

theorem node_1590 : Outcome ⟨0, 10, 1, 18⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 18⟩) (by decide) node_40

theorem node_1591 : Outcome ⟨0, 10, 1, 28⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 18⟩) (by decide) node_40

theorem node_1592 : Outcome ⟨0, 11, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 10, 0, 2⟩, ⟨0, 9, 0, 4⟩]
  exact AllWinning.cons node_1201 (AllWinning.cons node_948 (AllWinning.nil))

theorem node_1593 : Outcome ⟨0, 11, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 6⟩) (by decide) node_731

theorem node_1594 : Outcome ⟨0, 11, 0, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 6⟩) (by decide) node_731

theorem node_1595 : Outcome ⟨0, 11, 0, 22⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 22⟩) (by decide) node_10

theorem node_1596 : Outcome ⟨1, 0, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 0, 9, 2⟩) (by decide) node_1205

theorem node_1597 : Outcome ⟨1, 0, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 0, 9, 2⟩) (by decide) node_1205

theorem node_1598 : Outcome ⟨1, 0, 10, 18⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 18⟩) (by decide) node_62

theorem node_1599 : Outcome ⟨1, 0, 10, 28⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 18⟩) (by decide) node_62

theorem node_1600 : Outcome ⟨1, 1, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 2⟩) (by decide) node_1155

theorem node_1601 : Outcome ⟨1, 1, 9, 8⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 2⟩) (by decide) node_1155

theorem node_1602 : Outcome ⟨1, 2, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 8, 2⟩) (by decide) node_1210

theorem node_1603 : Outcome ⟨1, 2, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1604 : Outcome ⟨1, 2, 8, 18⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1605 : Outcome ⟨1, 2, 8, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1606 : Outcome ⟨1, 3, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1607 : Outcome ⟨1, 3, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1608 : Outcome ⟨1, 3, 7, 16⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1609 : Outcome ⟨1, 3, 7, 24⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1610 : Outcome ⟨1, 4, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1611 : Outcome ⟨1, 4, 6, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1612 : Outcome ⟨1, 4, 6, 18⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1613 : Outcome ⟨1, 4, 6, 24⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1614 : Outcome ⟨1, 5, 5, 8⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1615 : Outcome ⟨1, 5, 5, 24⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 2⟩) (by decide) node_1171

theorem node_1616 : Outcome ⟨1, 6, 4, 2⟩ true :=
  Outcome.win (q := ⟨1, 5, 4, 2⟩) (by decide) node_1241

theorem node_1617 : Outcome ⟨1, 6, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1618 : Outcome ⟨1, 6, 4, 18⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1619 : Outcome ⟨1, 6, 4, 24⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1620 : Outcome ⟨1, 7, 3, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 2⟩) (by decide) node_1247

theorem node_1621 : Outcome ⟨1, 7, 3, 4⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 2⟩) (by decide) node_1247

theorem node_1622 : Outcome ⟨1, 7, 3, 16⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 2⟩) (by decide) node_1247

theorem node_1623 : Outcome ⟨1, 7, 3, 24⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 2⟩) (by decide) node_1247

theorem node_1624 : Outcome ⟨1, 8, 2, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 2⟩) (by decide) node_1268

theorem node_1625 : Outcome ⟨1, 8, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1626 : Outcome ⟨1, 8, 2, 18⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1627 : Outcome ⟨1, 8, 2, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1628 : Outcome ⟨1, 9, 1, 4⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 2⟩) (by decide) node_1196

theorem node_1629 : Outcome ⟨1, 9, 1, 8⟩ true :=
  Outcome.win (q := ⟨0, 9, 1, 2⟩) (by decide) node_1196

theorem node_1630 : Outcome ⟨1, 10, 0, 2⟩ true :=
  Outcome.win (q := ⟨1, 9, 0, 2⟩) (by decide) node_1273

theorem node_1631 : Outcome ⟨1, 10, 0, 8⟩ true :=
  Outcome.win (q := ⟨1, 9, 0, 2⟩) (by decide) node_1273

theorem node_1632 : Outcome ⟨1, 10, 0, 18⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 18⟩) (by decide) node_79

theorem node_1633 : Outcome ⟨1, 10, 0, 28⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 18⟩) (by decide) node_79

theorem node_1634 : Outcome ⟨2, 0, 9, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 7, 4⟩) (by decide) node_994

theorem node_1635 : Outcome ⟨2, 0, 9, 4⟩ true :=
  Outcome.win (q := ⟨2, 0, 7, 4⟩) (by decide) node_994

theorem node_1636 : Outcome ⟨2, 0, 9, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1637 : Outcome ⟨2, 0, 9, 12⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1638 : Outcome ⟨2, 0, 9, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1639 : Outcome ⟨2, 0, 9, 30⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1640 : Outcome ⟨2, 1, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 1, 8, 2⟩) (by decide) node_1210

theorem node_1641 : Outcome ⟨2, 1, 8, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1642 : Outcome ⟨2, 1, 8, 18⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1643 : Outcome ⟨2, 1, 8, 20⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1644 : Outcome ⟨2, 2, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 2, 7, 4⟩) (by decide) node_917

theorem node_1645 : Outcome ⟨2, 2, 7, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1646 : Outcome ⟨2, 3, 6, 2⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1647 : Outcome ⟨2, 3, 6, 16⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1648 : Outcome ⟨2, 3, 6, 24⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 2⟩) (by decide) node_1219

theorem node_1649 : Outcome ⟨2, 4, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 4⟩) (by decide) node_1004

theorem node_1650 : Outcome ⟨2, 4, 5, 4⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1651 : Outcome ⟨2, 4, 5, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1652 : Outcome ⟨2, 4, 5, 10⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1653 : Outcome ⟨2, 4, 5, 12⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1654 : Outcome ⟨2, 4, 5, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1655 : Outcome ⟨2, 5, 4, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 4⟩) (by decide) node_1016

theorem node_1656 : Outcome ⟨2, 5, 4, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1657 : Outcome ⟨2, 5, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1658 : Outcome ⟨2, 5, 4, 10⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1659 : Outcome ⟨2, 5, 4, 12⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1660 : Outcome ⟨2, 5, 4, 18⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1661 : Outcome ⟨2, 6, 3, 2⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 2⟩) (by decide) node_1247

theorem node_1662 : Outcome ⟨2, 6, 3, 16⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 2⟩) (by decide) node_1247

theorem node_1663 : Outcome ⟨2, 6, 3, 24⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 2⟩) (by decide) node_1247

theorem node_1664 : Outcome ⟨2, 7, 2, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 2, 4⟩) (by decide) node_938

theorem node_1665 : Outcome ⟨2, 7, 2, 12⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1666 : Outcome ⟨2, 8, 1, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 1, 2⟩) (by decide) node_1268

theorem node_1667 : Outcome ⟨2, 8, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1668 : Outcome ⟨2, 8, 1, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1669 : Outcome ⟨2, 8, 1, 20⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1670 : Outcome ⟨2, 8, 1, 36⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1671 : Outcome ⟨2, 9, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 7, 0, 4⟩) (by decide) node_1025

theorem node_1672 : Outcome ⟨2, 9, 0, 4⟩ true :=
  Outcome.win (q := ⟨2, 7, 0, 4⟩) (by decide) node_1025

theorem node_1673 : Outcome ⟨2, 9, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1674 : Outcome ⟨2, 9, 0, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1675 : Outcome ⟨2, 9, 0, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1676 : Outcome ⟨2, 9, 0, 30⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1677 : Outcome ⟨3, 0, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 0, 8, 2⟩, ⟨1, 0, 8, 4⟩, ⟨3, 0, 7, 2⟩, ⟨3, 0, 6, 4⟩]
  exact AllWinning.cons node_1278 (AllWinning.cons node_952 (AllWinning.cons node_1315 (AllWinning.cons node_1030 (AllWinning.nil))))

theorem node_1678 : Outcome ⟨3, 0, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 0, 8, 6⟩) (by decide) node_682

theorem node_1679 : Outcome ⟨3, 0, 8, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1680 : Outcome ⟨3, 0, 8, 10⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1681 : Outcome ⟨3, 0, 8, 16⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1682 : Outcome ⟨3, 0, 8, 32⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1683 : Outcome ⟨3, 1, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1684 : Outcome ⟨3, 1, 7, 4⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1685 : Outcome ⟨3, 1, 7, 16⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1686 : Outcome ⟨3, 1, 7, 24⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1687 : Outcome ⟨3, 2, 6, 2⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1688 : Outcome ⟨3, 2, 6, 16⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1689 : Outcome ⟨3, 2, 6, 24⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1690 : Outcome ⟨3, 3, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 3, 5, 2⟩, ⟨1, 3, 5, 4⟩, ⟨3, 2, 5, 2⟩, ⟨3, 1, 5, 4⟩, ⟨3, 3, 4, 2⟩, ⟨3, 3, 3, 4⟩]
  exact AllWinning.cons node_1289 (AllWinning.cons node_966 (AllWinning.cons node_1336 (AllWinning.cons node_1035 (AllWinning.cons node_1340 (AllWinning.cons node_1043 (AllWinning.nil))))))

theorem node_1691 : Outcome ⟨3, 3, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 3, 5, 2⟩, ⟨1, 3, 5, 4⟩, ⟨0, 3, 5, 6⟩, ⟨3, 2, 5, 2⟩, ⟨3, 1, 5, 4⟩, ⟨3, 0, 5, 6⟩, ⟨3, 3, 4, 2⟩, ⟨3, 3, 3, 4⟩, ⟨3, 3, 2, 6⟩, ⟨3, 3, 1, 8⟩]
  exact AllWinning.cons node_1289 (AllWinning.cons node_966 (AllWinning.cons node_696 (AllWinning.cons node_1336 (AllWinning.cons node_1035 (AllWinning.cons node_797 (AllWinning.cons node_1340 (AllWinning.cons node_1043 (AllWinning.cons node_809 (AllWinning.cons node_610 (AllWinning.nil))))))))))

theorem node_1692 : Outcome ⟨3, 3, 5, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1693 : Outcome ⟨3, 3, 5, 16⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1694 : Outcome ⟨3, 4, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 4, 4, 2⟩, ⟨1, 4, 4, 4⟩, ⟨3, 3, 4, 2⟩, ⟨3, 2, 4, 4⟩, ⟨3, 4, 3, 2⟩, ⟨3, 4, 2, 4⟩]
  exact AllWinning.cons node_1293 (AllWinning.cons node_970 (AllWinning.cons node_1340 (AllWinning.cons node_1038 (AllWinning.cons node_1343 (AllWinning.cons node_1046 (AllWinning.nil))))))

theorem node_1695 : Outcome ⟨3, 4, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1696 : Outcome ⟨3, 4, 4, 10⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1697 : Outcome ⟨3, 4, 4, 20⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 6⟩) (by decide) node_701

theorem node_1698 : Outcome ⟨3, 5, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 5, 3, 2⟩, ⟨1, 5, 3, 4⟩, ⟨3, 4, 3, 2⟩, ⟨3, 3, 3, 4⟩, ⟨3, 5, 2, 2⟩, ⟨3, 5, 1, 4⟩]
  exact AllWinning.cons node_1299 (AllWinning.cons node_976 (AllWinning.cons node_1343 (AllWinning.cons node_1043 (AllWinning.cons node_1346 (AllWinning.cons node_1051 (AllWinning.nil))))))

theorem node_1699 : Outcome ⟨3, 5, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 5, 3, 2⟩, ⟨1, 5, 3, 4⟩, ⟨0, 5, 3, 6⟩, ⟨3, 4, 3, 2⟩, ⟨3, 3, 3, 4⟩, ⟨3, 2, 3, 6⟩, ⟨3, 1, 3, 8⟩, ⟨3, 5, 2, 2⟩, ⟨3, 5, 1, 4⟩, ⟨3, 5, 0, 6⟩]
  exact AllWinning.cons node_1299 (AllWinning.cons node_976 (AllWinning.cons node_716 (AllWinning.cons node_1343 (AllWinning.cons node_1043 (AllWinning.cons node_804 (AllWinning.cons node_602 (AllWinning.cons node_1346 (AllWinning.cons node_1051 (AllWinning.cons node_817 (AllWinning.nil))))))))))

theorem node_1700 : Outcome ⟨3, 5, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1701 : Outcome ⟨3, 5, 3, 16⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1702 : Outcome ⟨3, 6, 2, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1703 : Outcome ⟨3, 6, 2, 16⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1704 : Outcome ⟨3, 6, 2, 24⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1705 : Outcome ⟨3, 7, 1, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1706 : Outcome ⟨3, 7, 1, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1707 : Outcome ⟨3, 7, 1, 16⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1708 : Outcome ⟨3, 7, 1, 24⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1709 : Outcome ⟨3, 8, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 8, 0, 2⟩, ⟨1, 8, 0, 4⟩, ⟨3, 7, 0, 2⟩, ⟨3, 6, 0, 4⟩]
  exact AllWinning.cons node_1310 (AllWinning.cons node_989 (AllWinning.cons node_1367 (AllWinning.cons node_1055 (AllWinning.nil))))

theorem node_1710 : Outcome ⟨3, 8, 0, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 0, 6⟩) (by decide) node_731

theorem node_1711 : Outcome ⟨3, 8, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1712 : Outcome ⟨3, 8, 0, 10⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1713 : Outcome ⟨3, 8, 0, 16⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1714 : Outcome ⟨3, 8, 0, 32⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1715 : Outcome ⟨4, 0, 7, 2⟩ true :=
  Outcome.win (q := ⟨2, 0, 7, 4⟩) (by decide) node_994

theorem node_1716 : Outcome ⟨4, 0, 7, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1717 : Outcome ⟨4, 0, 7, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1718 : Outcome ⟨4, 0, 7, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1719 : Outcome ⟨4, 0, 7, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1720 : Outcome ⟨4, 1, 6, 2⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 2⟩) (by decide) node_1319

theorem node_1721 : Outcome ⟨4, 1, 6, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1722 : Outcome ⟨4, 1, 6, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1723 : Outcome ⟨4, 1, 6, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1724 : Outcome ⟨4, 2, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 5, 4⟩) (by decide) node_1004

theorem node_1725 : Outcome ⟨4, 2, 5, 4⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1726 : Outcome ⟨4, 2, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1727 : Outcome ⟨4, 2, 5, 10⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1728 : Outcome ⟨4, 2, 5, 12⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1729 : Outcome ⟨4, 2, 5, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1730 : Outcome ⟨4, 3, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 3, 4, 2⟩, ⟨2, 3, 4, 4⟩, ⟨4, 2, 4, 2⟩, ⟨4, 1, 4, 4⟩, ⟨4, 3, 3, 2⟩, ⟨4, 3, 2, 4⟩]
  exact AllWinning.cons node_1340 (AllWinning.cons node_1007 (AllWinning.cons node_1380 (AllWinning.cons node_1063 (AllWinning.cons node_1386 (AllWinning.cons node_1072 (AllWinning.nil))))))

theorem node_1731 : Outcome ⟨4, 3, 4, 4⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1732 : Outcome ⟨4, 3, 4, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1733 : Outcome ⟨4, 3, 4, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1734 : Outcome ⟨4, 4, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 3, 2⟩, ⟨2, 4, 3, 4⟩, ⟨4, 3, 3, 2⟩, ⟨4, 2, 3, 4⟩, ⟨4, 4, 2, 2⟩, ⟨4, 4, 1, 4⟩]
  exact AllWinning.cons node_1343 (AllWinning.cons node_1011 (AllWinning.cons node_1386 (AllWinning.cons node_1068 (AllWinning.cons node_1389 (AllWinning.cons node_1077 (AllWinning.nil))))))

theorem node_1735 : Outcome ⟨4, 4, 3, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1736 : Outcome ⟨4, 4, 3, 10⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1737 : Outcome ⟨4, 4, 3, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1738 : Outcome ⟨4, 5, 2, 2⟩ true :=
  Outcome.win (q := ⟨2, 5, 2, 4⟩) (by decide) node_1016

theorem node_1739 : Outcome ⟨4, 5, 2, 4⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1740 : Outcome ⟨4, 5, 2, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1741 : Outcome ⟨4, 5, 2, 10⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1742 : Outcome ⟨4, 5, 2, 12⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1743 : Outcome ⟨4, 5, 2, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1744 : Outcome ⟨4, 6, 1, 2⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 2⟩) (by decide) node_1350

theorem node_1745 : Outcome ⟨4, 6, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1746 : Outcome ⟨4, 6, 1, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1747 : Outcome ⟨4, 6, 1, 24⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1748 : Outcome ⟨4, 7, 0, 2⟩ true :=
  Outcome.win (q := ⟨2, 7, 0, 4⟩) (by decide) node_1025

theorem node_1749 : Outcome ⟨4, 7, 0, 4⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1750 : Outcome ⟨4, 7, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1751 : Outcome ⟨4, 7, 0, 10⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1752 : Outcome ⟨4, 7, 0, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1753 : Outcome ⟨5, 0, 6, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 2⟩) (by decide) node_1404

theorem node_1754 : Outcome ⟨5, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 2⟩) (by decide) node_1404

theorem node_1755 : Outcome ⟨5, 0, 6, 24⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 2⟩) (by decide) node_1404

theorem node_1756 : Outcome ⟨5, 1, 5, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 5, 2⟩) (by decide) node_1374

theorem node_1757 : Outcome ⟨5, 1, 5, 24⟩ true :=
  Outcome.win (q := ⟨4, 1, 5, 2⟩) (by decide) node_1374

theorem node_1758 : Outcome ⟨5, 2, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 4⟩) (by decide) node_1093

theorem node_1759 : Outcome ⟨5, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1760 : Outcome ⟨5, 2, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1761 : Outcome ⟨5, 2, 4, 10⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1762 : Outcome ⟨5, 2, 4, 12⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1763 : Outcome ⟨5, 2, 4, 18⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 8⟩) (by decide) node_508

theorem node_1764 : Outcome ⟨5, 3, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨4, 3, 3, 2⟩, ⟨3, 3, 3, 4⟩, ⟨2, 3, 3, 6⟩, ⟨1, 3, 3, 8⟩, ⟨5, 2, 3, 2⟩, ⟨5, 1, 3, 4⟩, ⟨5, 0, 3, 6⟩, ⟨5, 3, 2, 2⟩, ⟨5, 3, 1, 4⟩, ⟨5, 3, 0, 6⟩]
  exact AllWinning.cons node_1386 (AllWinning.cons node_1043 (AllWinning.cons node_779 (AllWinning.cons node_524 (AllWinning.cons node_1424 (AllWinning.cons node_1089 (AllWinning.cons node_863 (AllWinning.cons node_1428 (AllWinning.cons node_1097 (AllWinning.cons node_877 (AllWinning.nil))))))))))

theorem node_1765 : Outcome ⟨5, 3, 3, 6⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1766 : Outcome ⟨5, 3, 3, 16⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 10⟩) (by decide) node_341

theorem node_1767 : Outcome ⟨5, 4, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 4⟩) (by decide) node_1093

theorem node_1768 : Outcome ⟨5, 4, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1769 : Outcome ⟨5, 4, 2, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1770 : Outcome ⟨5, 4, 2, 10⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1771 : Outcome ⟨5, 4, 2, 12⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1772 : Outcome ⟨5, 4, 2, 18⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 8⟩) (by decide) node_529

theorem node_1773 : Outcome ⟨5, 5, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 5, 1, 2⟩) (by decide) node_1395

theorem node_1774 : Outcome ⟨5, 5, 1, 24⟩ true :=
  Outcome.win (q := ⟨4, 5, 1, 2⟩) (by decide) node_1395

theorem node_1775 : Outcome ⟨5, 6, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 2⟩) (by decide) node_1438

theorem node_1776 : Outcome ⟨5, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 2⟩) (by decide) node_1438

theorem node_1777 : Outcome ⟨5, 6, 0, 24⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 2⟩) (by decide) node_1438

theorem node_1778 : Outcome ⟨6, 0, 5, 2⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 2⟩) (by decide) node_1404

theorem node_1779 : Outcome ⟨6, 0, 5, 4⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 2⟩) (by decide) node_1404

theorem node_1780 : Outcome ⟨6, 0, 5, 24⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 2⟩) (by decide) node_1404

theorem node_1781 : Outcome ⟨6, 1, 4, 2⟩ true :=
  Outcome.win (q := ⟨5, 1, 4, 2⟩) (by decide) node_1418

theorem node_1782 : Outcome ⟨6, 1, 4, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1783 : Outcome ⟨6, 1, 4, 18⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1784 : Outcome ⟨6, 1, 4, 24⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 8⟩) (by decide) node_559

theorem node_1785 : Outcome ⟨6, 2, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 2⟩) (by decide) node_1455

theorem node_1786 : Outcome ⟨6, 2, 3, 16⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 2⟩) (by decide) node_1455

theorem node_1787 : Outcome ⟨6, 2, 3, 24⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 2⟩) (by decide) node_1455

theorem node_1788 : Outcome ⟨6, 3, 2, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 2⟩) (by decide) node_1475

theorem node_1789 : Outcome ⟨6, 3, 2, 16⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 2⟩) (by decide) node_1475

theorem node_1790 : Outcome ⟨6, 3, 2, 24⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 2⟩) (by decide) node_1475

theorem node_1791 : Outcome ⟨6, 4, 1, 2⟩ true :=
  Outcome.win (q := ⟨5, 4, 1, 2⟩) (by decide) node_1432

theorem node_1792 : Outcome ⟨6, 4, 1, 8⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1793 : Outcome ⟨6, 4, 1, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1794 : Outcome ⟨6, 4, 1, 24⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 8⟩) (by decide) node_581

theorem node_1795 : Outcome ⟨6, 5, 0, 2⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 2⟩) (by decide) node_1438

theorem node_1796 : Outcome ⟨6, 5, 0, 4⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 2⟩) (by decide) node_1438

theorem node_1797 : Outcome ⟨6, 5, 0, 24⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 2⟩) (by decide) node_1438

theorem node_1798 : Outcome ⟨7, 0, 4, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 2, 4⟩) (by decide) node_1124

theorem node_1799 : Outcome ⟨7, 0, 4, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1800 : Outcome ⟨7, 0, 4, 10⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1801 : Outcome ⟨7, 0, 4, 20⟩ true :=
  Outcome.win (q := ⟨4, 0, 4, 6⟩) (by decide) node_822

theorem node_1802 : Outcome ⟨7, 1, 3, 2⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 2⟩) (by decide) node_1455

theorem node_1803 : Outcome ⟨7, 1, 3, 4⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 2⟩) (by decide) node_1455

theorem node_1804 : Outcome ⟨7, 1, 3, 16⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 2⟩) (by decide) node_1455

theorem node_1805 : Outcome ⟨7, 1, 3, 24⟩ true :=
  Outcome.win (q := ⟨6, 1, 3, 2⟩) (by decide) node_1455

theorem node_1806 : Outcome ⟨7, 2, 2, 2⟩ true :=
  Outcome.win (q := ⟨5, 2, 2, 4⟩) (by decide) node_1093

theorem node_1807 : Outcome ⟨7, 2, 2, 12⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 14⟩) (by decide) node_147

theorem node_1808 : Outcome ⟨7, 3, 1, 2⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 2⟩) (by decide) node_1475

theorem node_1809 : Outcome ⟨7, 3, 1, 4⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 2⟩) (by decide) node_1475

theorem node_1810 : Outcome ⟨7, 3, 1, 16⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 2⟩) (by decide) node_1475

theorem node_1811 : Outcome ⟨7, 3, 1, 24⟩ true :=
  Outcome.win (q := ⟨6, 3, 1, 2⟩) (by decide) node_1475

theorem node_1812 : Outcome ⟨7, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 0, 4⟩) (by decide) node_1133

theorem node_1813 : Outcome ⟨7, 4, 0, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1814 : Outcome ⟨7, 4, 0, 10⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1815 : Outcome ⟨7, 4, 0, 20⟩ true :=
  Outcome.win (q := ⟨4, 4, 0, 6⟩) (by decide) node_848

theorem node_1816 : Outcome ⟨8, 0, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 0, 3, 2⟩, ⟨6, 0, 3, 4⟩, ⟨8, 0, 2, 2⟩, ⟨8, 0, 1, 4⟩]
  exact AllWinning.cons node_1495 (AllWinning.cons node_1104 (AllWinning.cons node_1511 (AllWinning.cons node_1138 (AllWinning.nil))))

theorem node_1817 : Outcome ⟨8, 0, 3, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 6⟩) (by decide) node_904

theorem node_1818 : Outcome ⟨8, 0, 3, 6⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1819 : Outcome ⟨8, 0, 3, 10⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1820 : Outcome ⟨8, 0, 3, 16⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1821 : Outcome ⟨8, 0, 3, 32⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 10⟩) (by decide) node_407

theorem node_1822 : Outcome ⟨8, 1, 2, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 1, 2⟩) (by decide) node_1516

theorem node_1823 : Outcome ⟨8, 1, 2, 8⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1824 : Outcome ⟨8, 1, 2, 18⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1825 : Outcome ⟨8, 1, 2, 20⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1826 : Outcome ⟨8, 1, 2, 36⟩ true :=
  Outcome.win (q := ⟨4, 1, 2, 8⟩) (by decide) node_619

theorem node_1827 : Outcome ⟨8, 2, 1, 2⟩ true :=
  Outcome.win (q := ⟨8, 1, 1, 2⟩) (by decide) node_1516

theorem node_1828 : Outcome ⟨8, 2, 1, 8⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1829 : Outcome ⟨8, 2, 1, 18⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1830 : Outcome ⟨8, 2, 1, 20⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1831 : Outcome ⟨8, 2, 1, 36⟩ true :=
  Outcome.win (q := ⟨4, 2, 1, 8⟩) (by decide) node_637

theorem node_1832 : Outcome ⟨8, 3, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨7, 3, 0, 2⟩, ⟨6, 3, 0, 4⟩, ⟨8, 2, 0, 2⟩, ⟨8, 1, 0, 4⟩]
  exact AllWinning.cons node_1507 (AllWinning.cons node_1119 (AllWinning.cons node_1521 (AllWinning.cons node_1143 (AllWinning.nil))))

theorem node_1833 : Outcome ⟨8, 3, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 6⟩) (by decide) node_904

theorem node_1834 : Outcome ⟨8, 3, 0, 6⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1835 : Outcome ⟨8, 3, 0, 10⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1836 : Outcome ⟨8, 3, 0, 16⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1837 : Outcome ⟨8, 3, 0, 32⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 10⟩) (by decide) node_430

theorem node_1838 : Outcome ⟨9, 0, 2, 2⟩ true :=
  Outcome.win (q := ⟨7, 0, 2, 4⟩) (by decide) node_1124

theorem node_1839 : Outcome ⟨9, 0, 2, 8⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1840 : Outcome ⟨9, 0, 2, 12⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1841 : Outcome ⟨9, 0, 2, 14⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1842 : Outcome ⟨9, 0, 2, 30⟩ true :=
  Outcome.win (q := ⟨2, 0, 2, 14⟩) (by decide) node_189

theorem node_1843 : Outcome ⟨9, 1, 1, 4⟩ true :=
  Outcome.win (q := ⟨8, 1, 1, 2⟩) (by decide) node_1516

theorem node_1844 : Outcome ⟨9, 1, 1, 8⟩ true :=
  Outcome.win (q := ⟨8, 1, 1, 2⟩) (by decide) node_1516

theorem node_1845 : Outcome ⟨9, 2, 0, 2⟩ true :=
  Outcome.win (q := ⟨7, 2, 0, 4⟩) (by decide) node_1133

theorem node_1846 : Outcome ⟨9, 2, 0, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1847 : Outcome ⟨9, 2, 0, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1848 : Outcome ⟨9, 2, 0, 14⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1849 : Outcome ⟨9, 2, 0, 30⟩ true :=
  Outcome.win (q := ⟨2, 2, 0, 14⟩) (by decide) node_210

theorem node_1850 : Outcome ⟨10, 0, 1, 2⟩ true :=
  Outcome.win (q := ⟨9, 0, 1, 2⟩) (by decide) node_1526

theorem node_1851 : Outcome ⟨10, 0, 1, 4⟩ true :=
  Outcome.win (q := ⟨9, 0, 1, 2⟩) (by decide) node_1526

theorem node_1852 : Outcome ⟨10, 0, 1, 8⟩ true :=
  Outcome.win (q := ⟨9, 0, 1, 2⟩) (by decide) node_1526

theorem node_1853 : Outcome ⟨10, 0, 1, 18⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 18⟩) (by decide) node_62

theorem node_1854 : Outcome ⟨10, 0, 1, 28⟩ true :=
  Outcome.win (q := ⟨1, 0, 1, 18⟩) (by decide) node_62

theorem node_1855 : Outcome ⟨10, 1, 0, 2⟩ true :=
  Outcome.win (q := ⟨9, 1, 0, 2⟩) (by decide) node_1531

theorem node_1856 : Outcome ⟨10, 1, 0, 4⟩ true :=
  Outcome.win (q := ⟨9, 1, 0, 2⟩) (by decide) node_1531

theorem node_1857 : Outcome ⟨10, 1, 0, 8⟩ true :=
  Outcome.win (q := ⟨9, 1, 0, 2⟩) (by decide) node_1531

theorem node_1858 : Outcome ⟨10, 1, 0, 18⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 18⟩) (by decide) node_79

theorem node_1859 : Outcome ⟨10, 1, 0, 28⟩ true :=
  Outcome.win (q := ⟨1, 1, 0, 18⟩) (by decide) node_79

theorem node_1860 : Outcome ⟨11, 0, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 0, 0, 2⟩, ⟨9, 0, 0, 4⟩]
  exact AllWinning.cons node_1536 (AllWinning.cons node_1148 (AllWinning.nil))

theorem node_1861 : Outcome ⟨11, 0, 0, 4⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 6⟩) (by decide) node_904

theorem node_1862 : Outcome ⟨11, 0, 0, 6⟩ true :=
  Outcome.win (q := ⟨8, 0, 0, 6⟩) (by decide) node_904

theorem node_1863 : Outcome ⟨11, 0, 0, 22⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 22⟩) (by decide) node_10

theorem node_1864 : Outcome ⟨0, 0, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 0, 11, 2⟩) (by decide) node_1540

theorem node_1865 : Outcome ⟨0, 0, 12, 8⟩ true :=
  Outcome.win (q := ⟨0, 0, 11, 2⟩) (by decide) node_1540

theorem node_1866 : Outcome ⟨0, 0, 12, 24⟩ true :=
  Outcome.win (q := ⟨0, 0, 0, 24⟩) (by decide) node_11

theorem node_1867 : Outcome ⟨0, 1, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 4⟩) (by decide) node_1156

theorem node_1868 : Outcome ⟨0, 1, 11, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 4⟩) (by decide) node_1156

theorem node_1869 : Outcome ⟨0, 1, 11, 6⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 4⟩) (by decide) node_1156

theorem node_1870 : Outcome ⟨0, 1, 11, 14⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 20⟩) (by decide) node_41

theorem node_1871 : Outcome ⟨0, 1, 11, 20⟩ true :=
  Outcome.win (q := ⟨0, 1, 1, 20⟩) (by decide) node_41

theorem node_1872 : Outcome ⟨0, 2, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 10, 2⟩, ⟨0, 0, 10, 4⟩, ⟨0, 2, 9, 2⟩, ⟨0, 2, 8, 4⟩]
  exact AllWinning.cons node_1544 (AllWinning.cons node_1152 (AllWinning.cons node_1549 (AllWinning.cons node_1161 (AllWinning.nil))))

theorem node_1873 : Outcome ⟨0, 2, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 10, 2⟩, ⟨0, 0, 10, 4⟩, ⟨0, 2, 9, 2⟩, ⟨0, 2, 8, 4⟩, ⟨0, 2, 7, 6⟩, ⟨0, 2, 6, 8⟩]
  exact AllWinning.cons node_1544 (AllWinning.cons node_1152 (AllWinning.cons node_1549 (AllWinning.cons node_1161 (AllWinning.cons node_918 (AllWinning.cons node_692 (AllWinning.nil))))))

theorem node_1874 : Outcome ⟨0, 2, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 1, 10, 2⟩, ⟨0, 0, 10, 4⟩, ⟨0, 2, 9, 2⟩, ⟨0, 2, 8, 4⟩, ⟨0, 2, 7, 6⟩, ⟨0, 2, 6, 8⟩, ⟨0, 2, 5, 10⟩, ⟨0, 2, 4, 12⟩]
  exact AllWinning.cons node_1544 (AllWinning.cons node_1152 (AllWinning.cons node_1549 (AllWinning.cons node_1161 (AllWinning.cons node_918 (AllWinning.cons node_692 (AllWinning.cons node_477 (AllWinning.cons node_335 (AllWinning.nil))))))))

theorem node_1875 : Outcome ⟨0, 2, 10, 10⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 16⟩) (by decide) node_148

theorem node_1876 : Outcome ⟨0, 2, 10, 16⟩ true :=
  Outcome.win (q := ⟨0, 2, 2, 16⟩) (by decide) node_148

theorem node_1877 : Outcome ⟨0, 3, 9, 2⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 4⟩) (by decide) node_1156

theorem node_1878 : Outcome ⟨0, 3, 9, 4⟩ true :=
  Outcome.win (q := ⟨0, 1, 9, 4⟩) (by decide) node_1156

theorem node_1879 : Outcome ⟨0, 3, 9, 12⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 12⟩) (by decide) node_342

theorem node_1880 : Outcome ⟨0, 3, 9, 14⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 12⟩) (by decide) node_342

theorem node_1881 : Outcome ⟨0, 3, 9, 24⟩ true :=
  Outcome.win (q := ⟨0, 3, 3, 12⟩) (by decide) node_342

theorem node_1882 : Outcome ⟨0, 4, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 3, 8, 2⟩) (by decide) node_1555

theorem node_1883 : Outcome ⟨0, 4, 8, 8⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 8⟩) (by decide) node_702

theorem node_1884 : Outcome ⟨0, 4, 8, 18⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 8⟩) (by decide) node_702

theorem node_1885 : Outcome ⟨0, 5, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 4⟩) (by decide) node_1172

theorem node_1886 : Outcome ⟨0, 5, 7, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 4⟩) (by decide) node_1172

theorem node_1887 : Outcome ⟨0, 5, 7, 8⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 4⟩) (by decide) node_1172

theorem node_1888 : Outcome ⟨0, 5, 7, 22⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 4⟩) (by decide) node_1172

theorem node_1889 : Outcome ⟨0, 6, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 6, 2⟩, ⟨0, 4, 6, 4⟩, ⟨0, 6, 5, 2⟩, ⟨0, 6, 4, 4⟩]
  exact AllWinning.cons node_1566 (AllWinning.cons node_1168 (AllWinning.cons node_1569 (AllWinning.cons node_1185 (AllWinning.nil))))

theorem node_1890 : Outcome ⟨0, 6, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 6, 2⟩, ⟨0, 4, 6, 4⟩, ⟨0, 3, 6, 6⟩, ⟨0, 2, 6, 8⟩, ⟨0, 6, 5, 2⟩, ⟨0, 6, 4, 4⟩, ⟨0, 6, 3, 6⟩, ⟨0, 6, 2, 8⟩]
  exact AllWinning.cons node_1566 (AllWinning.cons node_1168 (AllWinning.cons node_923 (AllWinning.cons node_692 (AllWinning.cons node_1569 (AllWinning.cons node_1185 (AllWinning.cons node_934 (AllWinning.cons node_720 (AllWinning.nil))))))))

theorem node_1891 : Outcome ⟨0, 6, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 6, 2⟩, ⟨0, 4, 6, 4⟩, ⟨0, 3, 6, 6⟩, ⟨0, 2, 6, 8⟩, ⟨0, 1, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨0, 6, 5, 2⟩, ⟨0, 6, 4, 4⟩, ⟨0, 6, 3, 6⟩, ⟨0, 6, 2, 8⟩, ⟨0, 6, 1, 10⟩, ⟨0, 6, 0, 12⟩]
  exact AllWinning.cons node_1566 (AllWinning.cons node_1168 (AllWinning.cons node_923 (AllWinning.cons node_692 (AllWinning.cons node_473 (AllWinning.cons node_327 (AllWinning.cons node_1569 (AllWinning.cons node_1185 (AllWinning.cons node_934 (AllWinning.cons node_720 (AllWinning.cons node_490 (AllWinning.cons node_363 (AllWinning.nil))))))))))))

theorem node_1892 : Outcome ⟨0, 6, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 6, 2⟩, ⟨0, 4, 6, 4⟩, ⟨0, 3, 6, 6⟩, ⟨0, 2, 6, 8⟩, ⟨0, 1, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨0, 6, 5, 2⟩, ⟨0, 6, 4, 4⟩, ⟨0, 6, 3, 6⟩, ⟨0, 6, 2, 8⟩, ⟨0, 6, 1, 10⟩, ⟨0, 6, 0, 12⟩]
  exact AllWinning.cons node_1566 (AllWinning.cons node_1168 (AllWinning.cons node_923 (AllWinning.cons node_692 (AllWinning.cons node_473 (AllWinning.cons node_327 (AllWinning.cons node_1569 (AllWinning.cons node_1185 (AllWinning.cons node_934 (AllWinning.cons node_720 (AllWinning.cons node_490 (AllWinning.cons node_363 (AllWinning.nil))))))))))))

theorem node_1893 : Outcome ⟨0, 6, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 6, 2⟩, ⟨0, 4, 6, 4⟩, ⟨0, 3, 6, 6⟩, ⟨0, 2, 6, 8⟩, ⟨0, 1, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨0, 6, 5, 2⟩, ⟨0, 6, 4, 4⟩, ⟨0, 6, 3, 6⟩, ⟨0, 6, 2, 8⟩, ⟨0, 6, 1, 10⟩, ⟨0, 6, 0, 12⟩]
  exact AllWinning.cons node_1566 (AllWinning.cons node_1168 (AllWinning.cons node_923 (AllWinning.cons node_692 (AllWinning.cons node_473 (AllWinning.cons node_327 (AllWinning.cons node_1569 (AllWinning.cons node_1185 (AllWinning.cons node_934 (AllWinning.cons node_720 (AllWinning.cons node_490 (AllWinning.cons node_363 (AllWinning.nil))))))))))))

theorem node_1894 : Outcome ⟨0, 6, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 6, 2⟩, ⟨0, 4, 6, 4⟩, ⟨0, 3, 6, 6⟩, ⟨0, 2, 6, 8⟩, ⟨0, 1, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨0, 6, 5, 2⟩, ⟨0, 6, 4, 4⟩, ⟨0, 6, 3, 6⟩, ⟨0, 6, 2, 8⟩, ⟨0, 6, 1, 10⟩, ⟨0, 6, 0, 12⟩]
  exact AllWinning.cons node_1566 (AllWinning.cons node_1168 (AllWinning.cons node_923 (AllWinning.cons node_692 (AllWinning.cons node_473 (AllWinning.cons node_327 (AllWinning.cons node_1569 (AllWinning.cons node_1185 (AllWinning.cons node_934 (AllWinning.cons node_720 (AllWinning.cons node_490 (AllWinning.cons node_363 (AllWinning.nil))))))))))))

theorem node_1895 : Outcome ⟨0, 6, 6, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 6, 2⟩, ⟨0, 4, 6, 4⟩, ⟨0, 3, 6, 6⟩, ⟨0, 2, 6, 8⟩, ⟨0, 1, 6, 10⟩, ⟨0, 0, 6, 12⟩, ⟨0, 6, 5, 2⟩, ⟨0, 6, 4, 4⟩, ⟨0, 6, 3, 6⟩, ⟨0, 6, 2, 8⟩, ⟨0, 6, 1, 10⟩, ⟨0, 6, 0, 12⟩]
  exact AllWinning.cons node_1566 (AllWinning.cons node_1168 (AllWinning.cons node_923 (AllWinning.cons node_692 (AllWinning.cons node_473 (AllWinning.cons node_327 (AllWinning.cons node_1569 (AllWinning.cons node_1185 (AllWinning.cons node_934 (AllWinning.cons node_720 (AllWinning.cons node_490 (AllWinning.cons node_363 (AllWinning.nil))))))))))))

end RQ9F1
