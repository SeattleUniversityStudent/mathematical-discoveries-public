import Chunk104
set_option autoImplicit false
namespace RQ9F1

theorem node_22010 : Outcome ⟨9, 18, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨8, 18, 9, 2⟩, ⟨7, 18, 9, 4⟩, ⟨9, 17, 9, 2⟩, ⟨9, 16, 9, 4⟩, ⟨9, 18, 8, 2⟩, ⟨9, 18, 7, 4⟩]
  exact AllWinning.cons node_21386 (AllWinning.cons node_20636 (AllWinning.cons node_21419 (AllWinning.cons node_20718 (AllWinning.cons node_21422 (AllWinning.cons node_20724 (AllWinning.nil))))))

theorem node_22011 : Outcome ⟨9, 18, 9, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 9, 6⟩) (by decide) node_19978

theorem node_22012 : Outcome ⟨9, 19, 8, 8⟩ true :=
  Outcome.win (q := ⟨2, 19, 8, 14⟩) (by decide) node_16019

theorem node_22013 : Outcome ⟨9, 20, 7, 4⟩ true :=
  Outcome.win (q := ⟨9, 20, 5, 4⟩) (by decide) node_20727

theorem node_22014 : Outcome ⟨10, 6, 20, 10⟩ true :=
  Outcome.win (q := ⟨6, 6, 20, 8⟩) (by decide) node_18999

theorem node_22015 : Outcome ⟨10, 7, 19, 4⟩ true :=
  Outcome.win (q := ⟨6, 7, 19, 8⟩) (by decide) node_19005

theorem node_22016 : Outcome ⟨10, 7, 19, 8⟩ true :=
  Outcome.win (q := ⟨6, 7, 19, 8⟩) (by decide) node_19005

theorem node_22017 : Outcome ⟨10, 8, 18, 4⟩ true :=
  Outcome.win (q := ⟨8, 8, 18, 4⟩) (by decide) node_20647

theorem node_22018 : Outcome ⟨10, 8, 18, 8⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 14⟩) (by decide) node_16509

theorem node_22019 : Outcome ⟨10, 9, 17, 2⟩ true :=
  Outcome.win (q := ⟨10, 7, 17, 4⟩) (by decide) node_20744

theorem node_22020 : Outcome ⟨10, 9, 17, 4⟩ true :=
  Outcome.win (q := ⟨6, 9, 17, 8⟩) (by decide) node_19011

theorem node_22021 : Outcome ⟨10, 10, 16, 2⟩ true :=
  Outcome.win (q := ⟨9, 10, 16, 2⟩) (by decide) node_21399

theorem node_22022 : Outcome ⟨10, 10, 16, 4⟩ true :=
  Outcome.win (q := ⟨10, 10, 13, 6⟩) (by decide) node_20008

theorem node_22023 : Outcome ⟨10, 10, 16, 8⟩ true :=
  Outcome.win (q := ⟨10, 10, 13, 6⟩) (by decide) node_20008

theorem node_22024 : Outcome ⟨10, 11, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 11, 15, 2⟩, ⟨8, 11, 15, 4⟩, ⟨10, 10, 15, 2⟩, ⟨10, 9, 15, 4⟩, ⟨10, 11, 14, 2⟩, ⟨10, 11, 13, 4⟩]
  exact AllWinning.cons node_21403 (AllWinning.cons node_20656 (AllWinning.cons node_21432 (AllWinning.cons node_20749 (AllWinning.cons node_21435 (AllWinning.cons node_20755 (AllWinning.nil))))))

theorem node_22025 : Outcome ⟨10, 11, 15, 8⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 14⟩) (by decide) node_16521

theorem node_22026 : Outcome ⟨10, 12, 14, 2⟩ true :=
  Outcome.win (q := ⟨8, 12, 14, 4⟩) (by decide) node_20659

theorem node_22027 : Outcome ⟨10, 12, 14, 4⟩ true :=
  Outcome.win (q := ⟨8, 12, 14, 4⟩) (by decide) node_20659

theorem node_22028 : Outcome ⟨10, 12, 14, 8⟩ true :=
  Outcome.win (q := ⟨2, 12, 14, 16⟩) (by decide) node_15031

theorem node_22029 : Outcome ⟨10, 13, 13, 2⟩ true :=
  Outcome.win (q := ⟨8, 13, 13, 4⟩) (by decide) node_20662

theorem node_22030 : Outcome ⟨10, 13, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 13, 6⟩) (by decide) node_20008

theorem node_22031 : Outcome ⟨10, 14, 12, 2⟩ true :=
  Outcome.win (q := ⟨8, 14, 12, 4⟩) (by decide) node_20667

theorem node_22032 : Outcome ⟨10, 14, 12, 4⟩ true :=
  Outcome.win (q := ⟨8, 14, 12, 4⟩) (by decide) node_20667

theorem node_22033 : Outcome ⟨10, 14, 12, 8⟩ true :=
  Outcome.win (q := ⟨2, 14, 12, 16⟩) (by decide) node_15044

theorem node_22034 : Outcome ⟨10, 15, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨9, 15, 11, 2⟩, ⟨8, 15, 11, 4⟩, ⟨10, 14, 11, 2⟩, ⟨10, 13, 11, 4⟩, ⟨10, 15, 10, 2⟩, ⟨10, 15, 9, 4⟩]
  exact AllWinning.cons node_21412 (AllWinning.cons node_20669 (AllWinning.cons node_21440 (AllWinning.cons node_20758 (AllWinning.cons node_21443 (AllWinning.cons node_20762 (AllWinning.nil))))))

theorem node_22035 : Outcome ⟨10, 15, 11, 8⟩ true :=
  Outcome.win (q := ⟨10, 8, 11, 14⟩) (by decide) node_16509

theorem node_22036 : Outcome ⟨10, 16, 10, 2⟩ true :=
  Outcome.win (q := ⟨9, 16, 10, 2⟩) (by decide) node_21415

theorem node_22037 : Outcome ⟨10, 16, 10, 4⟩ true :=
  Outcome.win (q := ⟨10, 13, 10, 6⟩) (by decide) node_20016

theorem node_22038 : Outcome ⟨10, 16, 10, 8⟩ true :=
  Outcome.win (q := ⟨10, 13, 10, 6⟩) (by decide) node_20016

theorem node_22039 : Outcome ⟨10, 17, 9, 2⟩ true :=
  Outcome.win (q := ⟨10, 17, 7, 4⟩) (by decide) node_20768

theorem node_22040 : Outcome ⟨10, 17, 9, 4⟩ true :=
  Outcome.win (q := ⟨6, 17, 9, 8⟩) (by decide) node_19039

theorem node_22041 : Outcome ⟨10, 18, 8, 4⟩ true :=
  Outcome.win (q := ⟨8, 18, 8, 4⟩) (by decide) node_20676

theorem node_22042 : Outcome ⟨10, 18, 8, 8⟩ true :=
  Outcome.win (q := ⟨10, 11, 8, 14⟩) (by decide) node_16521

theorem node_22043 : Outcome ⟨10, 19, 7, 4⟩ true :=
  Outcome.win (q := ⟨6, 19, 7, 8⟩) (by decide) node_19044

theorem node_22044 : Outcome ⟨10, 19, 7, 8⟩ true :=
  Outcome.win (q := ⟨6, 19, 7, 8⟩) (by decide) node_19044

theorem node_22045 : Outcome ⟨10, 20, 6, 10⟩ true :=
  Outcome.win (q := ⟨6, 20, 6, 8⟩) (by decide) node_19049

theorem node_22046 : Outcome ⟨11, 5, 20, 4⟩ true :=
  Outcome.win (q := ⟨9, 5, 20, 4⟩) (by decide) node_20685

theorem node_22047 : Outcome ⟨11, 5, 20, 12⟩ true :=
  Outcome.win (q := ⟨9, 5, 20, 4⟩) (by decide) node_20685

theorem node_22048 : Outcome ⟨11, 6, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 6, 19, 2⟩, ⟨9, 6, 19, 4⟩, ⟨11, 5, 19, 2⟩, ⟨11, 4, 19, 4⟩, ⟨11, 6, 18, 2⟩, ⟨11, 6, 17, 4⟩]
  exact AllWinning.cons node_21426 (AllWinning.cons node_20687 (AllWinning.cons node_21454 (AllWinning.cons node_20784 (AllWinning.cons node_21457 (AllWinning.cons node_20787 (AllWinning.nil))))))

theorem node_22049 : Outcome ⟨11, 6, 19, 8⟩ true :=
  Outcome.win (q := ⟨7, 6, 19, 8⟩) (by decide) node_19058

theorem node_22050 : Outcome ⟨11, 7, 18, 4⟩ true :=
  Outcome.win (q := ⟨11, 4, 18, 6⟩) (by decide) node_20044

theorem node_22051 : Outcome ⟨11, 8, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 17, 2⟩, ⟨9, 8, 17, 4⟩, ⟨11, 7, 17, 2⟩, ⟨11, 6, 17, 4⟩, ⟨11, 8, 16, 2⟩, ⟨11, 8, 15, 4⟩]
  exact AllWinning.cons node_21428 (AllWinning.cons node_20690 (AllWinning.cons node_21458 (AllWinning.cons node_20787 (AllWinning.cons node_21459 (AllWinning.cons node_20794 (AllWinning.nil))))))

theorem node_22052 : Outcome ⟨11, 8, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 8, 17, 2⟩, ⟨9, 8, 17, 4⟩, ⟨8, 8, 17, 6⟩, ⟨7, 8, 17, 8⟩, ⟨11, 7, 17, 2⟩, ⟨11, 6, 17, 4⟩, ⟨11, 5, 17, 6⟩, ⟨11, 4, 17, 8⟩, ⟨11, 8, 16, 2⟩, ⟨11, 8, 15, 4⟩, ⟨11, 8, 14, 6⟩, ⟨11, 8, 13, 8⟩]
  exact AllWinning.cons node_21428 (AllWinning.cons node_20690 (AllWinning.cons node_19921 (AllWinning.cons node_19066 (AllWinning.cons node_21458 (AllWinning.cons node_20787 (AllWinning.cons node_20049 (AllWinning.cons node_19260 (AllWinning.cons node_21459 (AllWinning.cons node_20794 (AllWinning.cons node_20053 (AllWinning.cons node_19272 (AllWinning.nil))))))))))))

theorem node_22053 : Outcome ⟨11, 8, 17, 12⟩ true :=
  Outcome.win (q := ⟨4, 8, 17, 14⟩) (by decide) node_16087

theorem node_22054 : Outcome ⟨11, 9, 16, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 4⟩) (by decide) node_20789

theorem node_22055 : Outcome ⟨11, 9, 16, 8⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 14⟩) (by decide) node_16094

theorem node_22056 : Outcome ⟨11, 9, 16, 12⟩ true :=
  Outcome.win (q := ⟨4, 9, 16, 14⟩) (by decide) node_16094

theorem node_22057 : Outcome ⟨11, 10, 15, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 10, 15, 2⟩, ⟨9, 10, 15, 4⟩, ⟨11, 9, 15, 2⟩, ⟨11, 8, 15, 4⟩, ⟨11, 10, 14, 2⟩, ⟨11, 10, 13, 4⟩]
  exact AllWinning.cons node_21432 (AllWinning.cons node_20698 (AllWinning.cons node_21462 (AllWinning.cons node_20794 (AllWinning.cons node_21464 (AllWinning.cons node_20799 (AllWinning.nil))))))

theorem node_22058 : Outcome ⟨11, 10, 15, 4⟩ true :=
  Outcome.win (q := ⟨11, 6, 15, 8⟩) (by decide) node_19266

theorem node_22059 : Outcome ⟨11, 10, 15, 8⟩ true :=
  Outcome.win (q := ⟨11, 10, 8, 14⟩) (by decide) node_16577

theorem node_22060 : Outcome ⟨11, 11, 14, 4⟩ true :=
  Outcome.win (q := ⟨11, 11, 13, 2⟩) (by decide) node_21467

theorem node_22061 : Outcome ⟨11, 11, 14, 12⟩ true :=
  Outcome.win (q := ⟨11, 11, 13, 2⟩) (by decide) node_21467

theorem node_22062 : Outcome ⟨11, 12, 13, 2⟩ true :=
  Outcome.win (q := ⟨9, 12, 13, 4⟩) (by decide) node_20704

theorem node_22063 : Outcome ⟨11, 12, 13, 4⟩ true :=
  Outcome.win (q := ⟨9, 12, 13, 4⟩) (by decide) node_20704

theorem node_22064 : Outcome ⟨11, 12, 13, 8⟩ true :=
  Outcome.win (q := ⟨4, 12, 13, 14⟩) (by decide) node_16107

theorem node_22065 : Outcome ⟨11, 13, 12, 2⟩ true :=
  Outcome.win (q := ⟨9, 13, 12, 4⟩) (by decide) node_20707

theorem node_22066 : Outcome ⟨11, 13, 12, 4⟩ true :=
  Outcome.win (q := ⟨9, 13, 12, 4⟩) (by decide) node_20707

theorem node_22067 : Outcome ⟨11, 13, 12, 8⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 14⟩) (by decide) node_16117

theorem node_22068 : Outcome ⟨11, 13, 12, 12⟩ true :=
  Outcome.win (q := ⟨4, 13, 12, 14⟩) (by decide) node_16117

theorem node_22069 : Outcome ⟨11, 14, 11, 4⟩ true :=
  Outcome.win (q := ⟨11, 13, 11, 2⟩) (by decide) node_21473

theorem node_22070 : Outcome ⟨11, 14, 11, 12⟩ true :=
  Outcome.win (q := ⟨11, 13, 11, 2⟩) (by decide) node_21473

theorem node_22071 : Outcome ⟨11, 15, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 15, 10, 2⟩, ⟨9, 15, 10, 4⟩, ⟨11, 14, 10, 2⟩, ⟨11, 13, 10, 4⟩, ⟨11, 15, 9, 2⟩, ⟨11, 15, 8, 4⟩]
  exact AllWinning.cons node_21443 (AllWinning.cons node_20714 (AllWinning.cons node_21476 (AllWinning.cons node_20805 (AllWinning.cons node_21479 (AllWinning.cons node_20808 (AllWinning.nil))))))

theorem node_22072 : Outcome ⟨11, 15, 10, 4⟩ true :=
  Outcome.win (q := ⟨11, 15, 6, 8⟩) (by decide) node_19290

theorem node_22073 : Outcome ⟨11, 15, 10, 8⟩ true :=
  Outcome.win (q := ⟨11, 8, 10, 14⟩) (by decide) node_16569

theorem node_22074 : Outcome ⟨11, 16, 9, 4⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 4⟩) (by decide) node_20811

theorem node_22075 : Outcome ⟨11, 16, 9, 8⟩ true :=
  Outcome.win (q := ⟨4, 16, 9, 14⟩) (by decide) node_16130

theorem node_22076 : Outcome ⟨11, 17, 8, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 8, 2⟩, ⟨9, 17, 8, 4⟩, ⟨11, 16, 8, 2⟩, ⟨11, 15, 8, 4⟩, ⟨11, 17, 7, 2⟩, ⟨11, 17, 6, 4⟩]
  exact AllWinning.cons node_21448 (AllWinning.cons node_20721 (AllWinning.cons node_21481 (AllWinning.cons node_20808 (AllWinning.cons node_21484 (AllWinning.cons node_20816 (AllWinning.nil))))))

theorem node_22077 : Outcome ⟨11, 17, 8, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 17, 8, 2⟩, ⟨9, 17, 8, 4⟩, ⟨8, 17, 8, 6⟩, ⟨7, 17, 8, 8⟩, ⟨11, 16, 8, 2⟩, ⟨11, 15, 8, 4⟩, ⟨11, 14, 8, 6⟩, ⟨11, 13, 8, 8⟩, ⟨11, 17, 7, 2⟩, ⟨11, 17, 6, 4⟩, ⟨11, 17, 5, 6⟩, ⟨11, 17, 4, 8⟩]
  exact AllWinning.cons node_21448 (AllWinning.cons node_20721 (AllWinning.cons node_19941 (AllWinning.cons node_19088 (AllWinning.cons node_21481 (AllWinning.cons node_20808 (AllWinning.cons node_20067 (AllWinning.cons node_19284 (AllWinning.cons node_21484 (AllWinning.cons node_20816 (AllWinning.cons node_20072 (AllWinning.cons node_19297 (AllWinning.nil))))))))))))

theorem node_22078 : Outcome ⟨11, 17, 8, 12⟩ true :=
  Outcome.win (q := ⟨4, 17, 8, 14⟩) (by decide) node_16138

theorem node_22079 : Outcome ⟨11, 18, 7, 4⟩ true :=
  Outcome.win (q := ⟨11, 18, 4, 6⟩) (by decide) node_20075

theorem node_22080 : Outcome ⟨11, 19, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨10, 19, 6, 2⟩, ⟨9, 19, 6, 4⟩, ⟨11, 18, 6, 2⟩, ⟨11, 17, 6, 4⟩, ⟨11, 19, 5, 2⟩, ⟨11, 19, 4, 4⟩]
  exact AllWinning.cons node_21451 (AllWinning.cons node_20726 (AllWinning.cons node_21485 (AllWinning.cons node_20816 (AllWinning.cons node_21486 (AllWinning.cons node_20818 (AllWinning.nil))))))

theorem node_22081 : Outcome ⟨11, 19, 6, 8⟩ true :=
  Outcome.win (q := ⟨7, 19, 6, 8⟩) (by decide) node_19093

theorem node_22082 : Outcome ⟨11, 20, 5, 4⟩ true :=
  Outcome.win (q := ⟨9, 20, 5, 4⟩) (by decide) node_20727

theorem node_22083 : Outcome ⟨11, 20, 5, 12⟩ true :=
  Outcome.win (q := ⟨9, 20, 5, 4⟩) (by decide) node_20727

theorem node_22084 : Outcome ⟨12, 4, 20, 2⟩ true :=
  Outcome.win (q := ⟨10, 4, 20, 4⟩) (by decide) node_20729

theorem node_22085 : Outcome ⟨12, 4, 20, 8⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 14⟩) (by decide) node_16619

theorem node_22086 : Outcome ⟨12, 5, 19, 2⟩ true :=
  Outcome.win (q := ⟨10, 5, 19, 4⟩) (by decide) node_20732

theorem node_22087 : Outcome ⟨12, 5, 19, 4⟩ true :=
  Outcome.win (q := ⟨12, 1, 19, 8⟩) (by decide) node_19308

theorem node_22088 : Outcome ⟨12, 5, 19, 6⟩ true :=
  Outcome.win (q := ⟨12, 1, 19, 8⟩) (by decide) node_19308

theorem node_22089 : Outcome ⟨12, 5, 19, 14⟩ true :=
  Outcome.win (q := ⟨12, 1, 19, 8⟩) (by decide) node_19308

theorem node_22090 : Outcome ⟨12, 6, 18, 4⟩ true :=
  Outcome.win (q := ⟨10, 6, 18, 4⟩) (by decide) node_20738

theorem node_22091 : Outcome ⟨12, 6, 18, 8⟩ true :=
  Outcome.win (q := ⟨10, 6, 18, 4⟩) (by decide) node_20738

theorem node_22092 : Outcome ⟨12, 7, 17, 4⟩ true :=
  Outcome.win (q := ⟨10, 7, 17, 4⟩) (by decide) node_20744

theorem node_22093 : Outcome ⟨12, 7, 17, 12⟩ true :=
  Outcome.win (q := ⟨10, 7, 17, 4⟩) (by decide) node_20744

theorem node_22094 : Outcome ⟨12, 8, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 4⟩) (by decide) node_20831

theorem node_22095 : Outcome ⟨12, 8, 16, 4⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 4⟩) (by decide) node_20831

theorem node_22096 : Outcome ⟨12, 8, 16, 8⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 4⟩) (by decide) node_20831

theorem node_22097 : Outcome ⟨12, 8, 16, 14⟩ true :=
  Outcome.win (q := ⟨3, 8, 16, 18⟩) (by decide) node_14116

theorem node_22098 : Outcome ⟨12, 9, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 4⟩) (by decide) node_20837

theorem node_22099 : Outcome ⟨12, 9, 15, 4⟩ true :=
  Outcome.win (q := ⟨9, 9, 15, 6⟩) (by decide) node_19957

theorem node_22100 : Outcome ⟨12, 9, 15, 14⟩ true :=
  Outcome.win (q := ⟨12, 9, 3, 24⟩) (by decide) node_11763

theorem node_22101 : Outcome ⟨12, 10, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 14, 4⟩) (by decide) node_20841

theorem node_22102 : Outcome ⟨12, 10, 14, 4⟩ true :=
  Outcome.win (q := ⟨12, 8, 14, 4⟩) (by decide) node_20841

theorem node_22103 : Outcome ⟨12, 10, 14, 8⟩ true :=
  Outcome.win (q := ⟨12, 2, 14, 16⟩) (by decide) node_15570

theorem node_22104 : Outcome ⟨12, 11, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 9, 13, 4⟩) (by decide) node_20844

theorem node_22105 : Outcome ⟨12, 11, 13, 8⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 14⟩) (by decide) node_16619

theorem node_22106 : Outcome ⟨12, 11, 13, 12⟩ true :=
  Outcome.win (q := ⟨12, 4, 13, 14⟩) (by decide) node_16619

theorem node_22107 : Outcome ⟨12, 12, 12, 4⟩ true :=
  Outcome.win (q := ⟨11, 12, 12, 2⟩) (by decide) node_21470

theorem node_22108 : Outcome ⟨12, 12, 12, 8⟩ true :=
  Outcome.win (q := ⟨11, 12, 12, 2⟩) (by decide) node_21470

theorem node_22109 : Outcome ⟨12, 12, 12, 14⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 24⟩) (by decide) node_11007

theorem node_22110 : Outcome ⟨12, 13, 11, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 9, 4⟩) (by decide) node_20853

theorem node_22111 : Outcome ⟨12, 13, 11, 8⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 14⟩) (by decide) node_16645

theorem node_22112 : Outcome ⟨12, 13, 11, 12⟩ true :=
  Outcome.win (q := ⟨12, 13, 4, 14⟩) (by decide) node_16645

theorem node_22113 : Outcome ⟨12, 14, 10, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 8, 4⟩) (by decide) node_20857

theorem node_22114 : Outcome ⟨12, 14, 10, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 8, 4⟩) (by decide) node_20857

theorem node_22115 : Outcome ⟨12, 14, 10, 8⟩ true :=
  Outcome.win (q := ⟨12, 14, 2, 16⟩) (by decide) node_15604

theorem node_22116 : Outcome ⟨12, 15, 9, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 9, 4⟩) (by decide) node_20853

theorem node_22117 : Outcome ⟨12, 15, 9, 4⟩ true :=
  Outcome.win (q := ⟨9, 15, 9, 6⟩) (by decide) node_19978

theorem node_22118 : Outcome ⟨12, 15, 9, 14⟩ true :=
  Outcome.win (q := ⟨12, 3, 9, 24⟩) (by decide) node_11733

theorem node_22119 : Outcome ⟨12, 16, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 8, 4⟩) (by decide) node_20857

theorem node_22120 : Outcome ⟨12, 16, 8, 4⟩ true :=
  Outcome.win (q := ⟨12, 14, 8, 4⟩) (by decide) node_20857

theorem node_22121 : Outcome ⟨12, 16, 8, 8⟩ true :=
  Outcome.win (q := ⟨12, 14, 8, 4⟩) (by decide) node_20857

theorem node_22122 : Outcome ⟨12, 16, 8, 14⟩ true :=
  Outcome.win (q := ⟨3, 16, 8, 18⟩) (by decide) node_14149

theorem node_22123 : Outcome ⟨12, 17, 7, 4⟩ true :=
  Outcome.win (q := ⟨10, 17, 7, 4⟩) (by decide) node_20768

theorem node_22124 : Outcome ⟨12, 17, 7, 12⟩ true :=
  Outcome.win (q := ⟨10, 17, 7, 4⟩) (by decide) node_20768

theorem node_22125 : Outcome ⟨12, 18, 6, 4⟩ true :=
  Outcome.win (q := ⟨10, 18, 6, 4⟩) (by decide) node_20771

theorem node_22126 : Outcome ⟨12, 18, 6, 8⟩ true :=
  Outcome.win (q := ⟨10, 18, 6, 4⟩) (by decide) node_20771

theorem node_22127 : Outcome ⟨12, 19, 5, 2⟩ true :=
  Outcome.win (q := ⟨10, 19, 5, 4⟩) (by decide) node_20775

theorem node_22128 : Outcome ⟨12, 19, 5, 4⟩ true :=
  Outcome.win (q := ⟨12, 19, 1, 8⟩) (by decide) node_19349

theorem node_22129 : Outcome ⟨12, 19, 5, 14⟩ true :=
  Outcome.win (q := ⟨12, 19, 1, 8⟩) (by decide) node_19349

theorem node_22130 : Outcome ⟨12, 20, 4, 2⟩ true :=
  Outcome.win (q := ⟨10, 20, 4, 4⟩) (by decide) node_20780

theorem node_22131 : Outcome ⟨13, 3, 20, 2⟩ true :=
  Outcome.win (q := ⟨12, 3, 20, 2⟩) (by decide) node_21490

theorem node_22132 : Outcome ⟨13, 4, 19, 2⟩ true :=
  Outcome.win (q := ⟨13, 2, 19, 4⟩) (by decide) node_20880

theorem node_22133 : Outcome ⟨13, 4, 19, 8⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 14⟩) (by decide) node_16678

theorem node_22134 : Outcome ⟨13, 5, 18, 2⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 2⟩) (by decide) node_21495

theorem node_22135 : Outcome ⟨13, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨12, 5, 18, 2⟩) (by decide) node_21495

theorem node_22136 : Outcome ⟨13, 6, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 6, 17, 2⟩, ⟨11, 6, 17, 4⟩, ⟨13, 5, 17, 2⟩, ⟨13, 4, 17, 4⟩, ⟨13, 6, 16, 2⟩, ⟨13, 6, 15, 4⟩]
  exact AllWinning.cons node_21500 (AllWinning.cons node_20787 (AllWinning.cons node_21542 (AllWinning.cons node_20886 (AllWinning.cons node_21545 (AllWinning.cons node_20889 (AllWinning.nil))))))

theorem node_22137 : Outcome ⟨13, 6, 17, 6⟩ true :=
  Outcome.win (q := ⟨13, 1, 17, 10⟩) (by decide) node_18484

theorem node_22138 : Outcome ⟨13, 6, 17, 12⟩ true :=
  Outcome.win (q := ⟨13, 1, 17, 10⟩) (by decide) node_18484

theorem node_22139 : Outcome ⟨13, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 4⟩) (by decide) node_20789

theorem node_22140 : Outcome ⟨13, 7, 16, 4⟩ true :=
  Outcome.win (q := ⟨11, 7, 16, 4⟩) (by decide) node_20789

theorem node_22141 : Outcome ⟨13, 7, 16, 8⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 14⟩) (by decide) node_16692

theorem node_22142 : Outcome ⟨13, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨13, 8, 13, 4⟩) (by decide) node_20894

theorem node_22143 : Outcome ⟨13, 8, 15, 8⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 16⟩) (by decide) node_15169

theorem node_22144 : Outcome ⟨13, 8, 15, 12⟩ true :=
  Outcome.win (q := ⟨5, 8, 15, 16⟩) (by decide) node_15169

theorem node_22145 : Outcome ⟨13, 9, 14, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 12, 4⟩) (by decide) node_20899

theorem node_22146 : Outcome ⟨13, 9, 14, 12⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 14⟩) (by decide) node_16703

theorem node_22147 : Outcome ⟨13, 10, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 8, 13, 4⟩) (by decide) node_20894

theorem node_22148 : Outcome ⟨13, 10, 13, 6⟩ true :=
  Outcome.win (q := ⟨10, 10, 13, 6⟩) (by decide) node_20008

theorem node_22149 : Outcome ⟨13, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 12, 4⟩) (by decide) node_20899

theorem node_22150 : Outcome ⟨13, 11, 12, 4⟩ true :=
  Outcome.win (q := ⟨13, 9, 12, 4⟩) (by decide) node_20899

theorem node_22151 : Outcome ⟨13, 11, 12, 8⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 14⟩) (by decide) node_16678

theorem node_22152 : Outcome ⟨13, 11, 12, 12⟩ true :=
  Outcome.win (q := ⟨13, 4, 12, 14⟩) (by decide) node_16678

theorem node_22153 : Outcome ⟨13, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨13, 12, 9, 4⟩) (by decide) node_20907

theorem node_22154 : Outcome ⟨13, 12, 11, 4⟩ true :=
  Outcome.win (q := ⟨13, 12, 9, 4⟩) (by decide) node_20907

theorem node_22155 : Outcome ⟨13, 12, 11, 8⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 14⟩) (by decide) node_16714

theorem node_22156 : Outcome ⟨13, 12, 11, 12⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 14⟩) (by decide) node_16714

theorem node_22157 : Outcome ⟨13, 13, 10, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 8, 4⟩) (by decide) node_20910

theorem node_22158 : Outcome ⟨13, 13, 10, 6⟩ true :=
  Outcome.win (q := ⟨10, 13, 10, 6⟩) (by decide) node_20016

theorem node_22159 : Outcome ⟨13, 14, 9, 2⟩ true :=
  Outcome.win (q := ⟨13, 12, 9, 4⟩) (by decide) node_20907

theorem node_22160 : Outcome ⟨13, 14, 9, 12⟩ true :=
  Outcome.win (q := ⟨13, 7, 9, 14⟩) (by decide) node_16692

theorem node_22161 : Outcome ⟨13, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 8, 4⟩) (by decide) node_20910

theorem node_22162 : Outcome ⟨13, 15, 8, 8⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 16⟩) (by decide) node_15200

theorem node_22163 : Outcome ⟨13, 15, 8, 12⟩ true :=
  Outcome.win (q := ⟨5, 15, 8, 16⟩) (by decide) node_15200

theorem node_22164 : Outcome ⟨13, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 4⟩) (by decide) node_20811

theorem node_22165 : Outcome ⟨13, 16, 7, 4⟩ true :=
  Outcome.win (q := ⟨11, 16, 7, 4⟩) (by decide) node_20811

theorem node_22166 : Outcome ⟨13, 16, 7, 8⟩ true :=
  Outcome.win (q := ⟨13, 9, 7, 14⟩) (by decide) node_16703

theorem node_22167 : Outcome ⟨13, 17, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨12, 17, 6, 2⟩, ⟨11, 17, 6, 4⟩, ⟨13, 16, 6, 2⟩, ⟨13, 15, 6, 4⟩, ⟨13, 17, 5, 2⟩, ⟨13, 17, 4, 4⟩]
  exact AllWinning.cons node_21523 (AllWinning.cons node_20816 (AllWinning.cons node_21568 (AllWinning.cons node_20916 (AllWinning.cons node_21571 (AllWinning.cons node_20921 (AllWinning.nil))))))

theorem node_22168 : Outcome ⟨13, 17, 6, 6⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 10⟩) (by decide) node_18539

theorem node_22169 : Outcome ⟨13, 17, 6, 12⟩ true :=
  Outcome.win (q := ⟨13, 17, 1, 10⟩) (by decide) node_18539

theorem node_22170 : Outcome ⟨13, 18, 5, 2⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 2⟩) (by decide) node_21526

theorem node_22171 : Outcome ⟨13, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨12, 18, 5, 2⟩) (by decide) node_21526

theorem node_22172 : Outcome ⟨13, 19, 4, 2⟩ true :=
  Outcome.win (q := ⟨13, 19, 2, 4⟩) (by decide) node_20926

theorem node_22173 : Outcome ⟨13, 19, 4, 8⟩ true :=
  Outcome.win (q := ⟨13, 12, 4, 14⟩) (by decide) node_16714

theorem node_22174 : Outcome ⟨13, 20, 3, 2⟩ true :=
  Outcome.win (q := ⟨12, 20, 3, 2⟩) (by decide) node_21533

theorem node_22175 : Outcome ⟨14, 2, 20, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 2, 20, 2⟩, ⟨12, 2, 20, 4⟩, ⟨11, 2, 20, 6⟩, ⟨10, 2, 20, 8⟩, ⟨14, 1, 20, 2⟩, ⟨14, 0, 20, 4⟩, ⟨14, 2, 19, 2⟩, ⟨14, 2, 18, 4⟩, ⟨14, 2, 17, 6⟩, ⟨14, 2, 16, 8⟩]
  exact AllWinning.cons node_21535 (AllWinning.cons node_20823 (AllWinning.cons node_20036 (AllWinning.cons node_19202 (AllWinning.cons node_21581 (AllWinning.cons node_20931 (AllWinning.cons node_21582 (AllWinning.cons node_20934 (AllWinning.cons node_20190 (AllWinning.cons node_19414 (AllWinning.nil))))))))))

theorem node_22176 : Outcome ⟨14, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 4⟩) (by decide) node_20936

theorem node_22177 : Outcome ⟨14, 3, 19, 4⟩ true :=
  Outcome.win (q := ⟨11, 3, 19, 6⟩) (by decide) node_20039

theorem node_22178 : Outcome ⟨14, 4, 18, 2⟩ true :=
  Outcome.win (q := ⟨14, 4, 16, 4⟩) (by decide) node_20943

theorem node_22179 : Outcome ⟨14, 4, 18, 16⟩ true :=
  Outcome.win (q := ⟨11, 4, 18, 6⟩) (by decide) node_20044

theorem node_22180 : Outcome ⟨14, 5, 17, 6⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 4⟩) (by decide) node_20936

theorem node_22181 : Outcome ⟨14, 5, 17, 12⟩ true :=
  Outcome.win (q := ⟨14, 3, 17, 4⟩) (by decide) node_20936

theorem node_22182 : Outcome ⟨14, 6, 16, 2⟩ true :=
  Outcome.win (q := ⟨12, 6, 16, 4⟩) (by decide) node_20831

theorem node_22183 : Outcome ⟨14, 6, 16, 6⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 6⟩) (by decide) node_20201

theorem node_22184 : Outcome ⟨14, 6, 16, 8⟩ true :=
  Outcome.win (q := ⟨14, 6, 13, 6⟩) (by decide) node_20201

theorem node_22185 : Outcome ⟨14, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 4⟩) (by decide) node_20837

theorem node_22186 : Outcome ⟨14, 7, 15, 12⟩ true :=
  Outcome.win (q := ⟨12, 7, 15, 4⟩) (by decide) node_20837

theorem node_22187 : Outcome ⟨14, 8, 14, 2⟩ true :=
  Outcome.win (q := ⟨12, 8, 14, 4⟩) (by decide) node_20841

theorem node_22188 : Outcome ⟨14, 8, 14, 12⟩ true :=
  Outcome.win (q := ⟨14, 0, 14, 16⟩) (by decide) node_15669

theorem node_22189 : Outcome ⟨14, 9, 13, 2⟩ true :=
  Outcome.win (q := ⟨12, 9, 13, 4⟩) (by decide) node_20844

theorem node_22190 : Outcome ⟨14, 9, 13, 12⟩ true :=
  Outcome.win (q := ⟨7, 9, 13, 14⟩) (by decide) node_16288

theorem node_22191 : Outcome ⟨14, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨14, 8, 12, 4⟩) (by decide) node_20952

theorem node_22192 : Outcome ⟨14, 10, 12, 4⟩ true :=
  Outcome.win (q := ⟨14, 8, 12, 4⟩) (by decide) node_20952

theorem node_22193 : Outcome ⟨14, 10, 12, 8⟩ true :=
  Outcome.win (q := ⟨14, 2, 12, 16⟩) (by decide) node_15680

theorem node_22194 : Outcome ⟨14, 10, 12, 16⟩ true :=
  Outcome.win (q := ⟨14, 10, 1, 22⟩) (by decide) node_12818

theorem node_22195 : Outcome ⟨14, 11, 11, 12⟩ true :=
  Outcome.win (q := ⟨13, 11, 11, 2⟩) (by decide) node_21557

theorem node_22196 : Outcome ⟨14, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨14, 12, 8, 4⟩) (by decide) node_20961

theorem node_22197 : Outcome ⟨14, 12, 10, 4⟩ true :=
  Outcome.win (q := ⟨14, 12, 8, 4⟩) (by decide) node_20961

theorem node_22198 : Outcome ⟨14, 12, 10, 8⟩ true :=
  Outcome.win (q := ⟨14, 12, 2, 16⟩) (by decide) node_15717

theorem node_22199 : Outcome ⟨14, 12, 10, 16⟩ true :=
  Outcome.win (q := ⟨14, 1, 10, 22⟩) (by decide) node_12786

theorem node_22200 : Outcome ⟨14, 13, 9, 2⟩ true :=
  Outcome.win (q := ⟨12, 13, 9, 4⟩) (by decide) node_20853

theorem node_22201 : Outcome ⟨14, 13, 9, 12⟩ true :=
  Outcome.win (q := ⟨7, 13, 9, 14⟩) (by decide) node_16304

theorem node_22202 : Outcome ⟨14, 14, 8, 2⟩ true :=
  Outcome.win (q := ⟨12, 14, 8, 4⟩) (by decide) node_20857

theorem node_22203 : Outcome ⟨14, 14, 8, 12⟩ true :=
  Outcome.win (q := ⟨14, 14, 0, 16⟩) (by decide) node_15729

theorem node_22204 : Outcome ⟨14, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 4⟩) (by decide) node_20860

theorem node_22205 : Outcome ⟨14, 15, 7, 12⟩ true :=
  Outcome.win (q := ⟨12, 15, 7, 4⟩) (by decide) node_20860

theorem node_22206 : Outcome ⟨14, 16, 6, 2⟩ true :=
  Outcome.win (q := ⟨12, 16, 6, 4⟩) (by decide) node_20865

theorem node_22207 : Outcome ⟨14, 16, 6, 6⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 6⟩) (by decide) node_20221

theorem node_22208 : Outcome ⟨14, 16, 6, 8⟩ true :=
  Outcome.win (q := ⟨14, 13, 6, 6⟩) (by decide) node_20221

theorem node_22209 : Outcome ⟨14, 17, 5, 6⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 4⟩) (by decide) node_20973

theorem node_22210 : Outcome ⟨14, 17, 5, 12⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 4⟩) (by decide) node_20973

theorem node_22211 : Outcome ⟨14, 18, 4, 2⟩ true :=
  Outcome.win (q := ⟨14, 16, 4, 4⟩) (by decide) node_20969

theorem node_22212 : Outcome ⟨14, 18, 4, 16⟩ true :=
  Outcome.win (q := ⟨11, 18, 4, 6⟩) (by decide) node_20075

theorem node_22213 : Outcome ⟨14, 19, 3, 2⟩ true :=
  Outcome.win (q := ⟨14, 17, 3, 4⟩) (by decide) node_20973

theorem node_22214 : Outcome ⟨14, 19, 3, 4⟩ true :=
  Outcome.win (q := ⟨11, 19, 3, 6⟩) (by decide) node_20080

theorem node_22215 : Outcome ⟨14, 20, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨13, 20, 2, 2⟩, ⟨12, 20, 2, 4⟩, ⟨11, 20, 2, 6⟩, ⟨10, 20, 2, 8⟩, ⟨14, 19, 2, 2⟩, ⟨14, 18, 2, 4⟩, ⟨14, 17, 2, 6⟩, ⟨14, 16, 2, 8⟩, ⟨14, 20, 1, 2⟩, ⟨14, 20, 0, 4⟩]
  exact AllWinning.cons node_21579 (AllWinning.cons node_20877 (AllWinning.cons node_20083 (AllWinning.cons node_19251 (AllWinning.cons node_21615 (AllWinning.cons node_20979 (AllWinning.cons node_20234 (AllWinning.cons node_19450 (AllWinning.cons node_21618 (AllWinning.cons node_20982 (AllWinning.nil))))))))))

theorem node_22216 : Outcome ⟨15, 1, 20, 10⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 8⟩) (by decide) node_19460

theorem node_22217 : Outcome ⟨15, 2, 19, 4⟩ true :=
  Outcome.win (q := ⟨13, 2, 19, 4⟩) (by decide) node_20880

theorem node_22218 : Outcome ⟨15, 2, 19, 6⟩ true :=
  Outcome.win (q := ⟨13, 2, 19, 4⟩) (by decide) node_20880

theorem node_22219 : Outcome ⟨15, 3, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.nil))))))

theorem node_22220 : Outcome ⟨15, 3, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨12, 3, 18, 6⟩, ⟨11, 3, 18, 8⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 0, 18, 6⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩, ⟨15, 3, 15, 6⟩, ⟨15, 3, 14, 8⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_20090 (AllWinning.cons node_19257 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_20243 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.cons node_20250 (AllWinning.cons node_19473 (AllWinning.nil)))))))))))

theorem node_22221 : Outcome ⟨15, 3, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨12, 3, 18, 6⟩, ⟨11, 3, 18, 8⟩, ⟨10, 3, 18, 10⟩, ⟨9, 3, 18, 12⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 0, 18, 6⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩, ⟨15, 3, 15, 6⟩, ⟨15, 3, 14, 8⟩, ⟨15, 3, 13, 10⟩, ⟨15, 3, 12, 12⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_20090 (AllWinning.cons node_19257 (AllWinning.cons node_18307 (AllWinning.cons node_17360 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_20243 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.cons node_20250 (AllWinning.cons node_19473 (AllWinning.cons node_18609 (AllWinning.cons node_17704 (AllWinning.nil)))))))))))))))

theorem node_22222 : Outcome ⟨15, 3, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨12, 3, 18, 6⟩, ⟨11, 3, 18, 8⟩, ⟨10, 3, 18, 10⟩, ⟨9, 3, 18, 12⟩, ⟨8, 3, 18, 14⟩, ⟨7, 3, 18, 16⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 0, 18, 6⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩, ⟨15, 3, 15, 6⟩, ⟨15, 3, 14, 8⟩, ⟨15, 3, 13, 10⟩, ⟨15, 3, 12, 12⟩, ⟨15, 3, 11, 14⟩, ⟨15, 3, 10, 16⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_20090 (AllWinning.cons node_19257 (AllWinning.cons node_18307 (AllWinning.cons node_17360 (AllWinning.cons node_16339 (AllWinning.cons node_15276 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_20243 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.cons node_20250 (AllWinning.cons node_19473 (AllWinning.cons node_18609 (AllWinning.cons node_17704 (AllWinning.cons node_16789 (AllWinning.cons node_15741 (AllWinning.nil)))))))))))))))))))

theorem node_22223 : Outcome ⟨15, 3, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨12, 3, 18, 6⟩, ⟨11, 3, 18, 8⟩, ⟨10, 3, 18, 10⟩, ⟨9, 3, 18, 12⟩, ⟨8, 3, 18, 14⟩, ⟨7, 3, 18, 16⟩, ⟨6, 3, 18, 18⟩, ⟨5, 3, 18, 20⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 0, 18, 6⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩, ⟨15, 3, 15, 6⟩, ⟨15, 3, 14, 8⟩, ⟨15, 3, 13, 10⟩, ⟨15, 3, 12, 12⟩, ⟨15, 3, 11, 14⟩, ⟨15, 3, 10, 16⟩, ⟨15, 3, 9, 18⟩, ⟨15, 3, 8, 20⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_20090 (AllWinning.cons node_19257 (AllWinning.cons node_18307 (AllWinning.cons node_17360 (AllWinning.cons node_16339 (AllWinning.cons node_15276 (AllWinning.cons node_14270 (AllWinning.cons node_13252 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_20243 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.cons node_20250 (AllWinning.cons node_19473 (AllWinning.cons node_18609 (AllWinning.cons node_17704 (AllWinning.cons node_16789 (AllWinning.cons node_15741 (AllWinning.cons node_14761 (AllWinning.cons node_13814 (AllWinning.nil)))))))))))))))))))))))

theorem node_22224 : Outcome ⟨15, 3, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨12, 3, 18, 6⟩, ⟨11, 3, 18, 8⟩, ⟨10, 3, 18, 10⟩, ⟨9, 3, 18, 12⟩, ⟨8, 3, 18, 14⟩, ⟨7, 3, 18, 16⟩, ⟨6, 3, 18, 18⟩, ⟨5, 3, 18, 20⟩, ⟨4, 3, 18, 22⟩, ⟨3, 3, 18, 24⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 0, 18, 6⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩, ⟨15, 3, 15, 6⟩, ⟨15, 3, 14, 8⟩, ⟨15, 3, 13, 10⟩, ⟨15, 3, 12, 12⟩, ⟨15, 3, 11, 14⟩, ⟨15, 3, 10, 16⟩, ⟨15, 3, 9, 18⟩, ⟨15, 3, 8, 20⟩, ⟨15, 3, 7, 22⟩, ⟨15, 3, 6, 24⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_20090 (AllWinning.cons node_19257 (AllWinning.cons node_18307 (AllWinning.cons node_17360 (AllWinning.cons node_16339 (AllWinning.cons node_15276 (AllWinning.cons node_14270 (AllWinning.cons node_13252 (AllWinning.cons node_12230 (AllWinning.cons node_11156 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_20243 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.cons node_20250 (AllWinning.cons node_19473 (AllWinning.cons node_18609 (AllWinning.cons node_17704 (AllWinning.cons node_16789 (AllWinning.cons node_15741 (AllWinning.cons node_14761 (AllWinning.cons node_13814 (AllWinning.cons node_12839 (AllWinning.cons node_11848 (AllWinning.nil)))))))))))))))))))))))))))

theorem node_22225 : Outcome ⟨15, 3, 18, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨12, 3, 18, 6⟩, ⟨11, 3, 18, 8⟩, ⟨10, 3, 18, 10⟩, ⟨9, 3, 18, 12⟩, ⟨8, 3, 18, 14⟩, ⟨7, 3, 18, 16⟩, ⟨6, 3, 18, 18⟩, ⟨5, 3, 18, 20⟩, ⟨4, 3, 18, 22⟩, ⟨3, 3, 18, 24⟩, ⟨2, 3, 18, 26⟩, ⟨1, 3, 18, 28⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 0, 18, 6⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩, ⟨15, 3, 15, 6⟩, ⟨15, 3, 14, 8⟩, ⟨15, 3, 13, 10⟩, ⟨15, 3, 12, 12⟩, ⟨15, 3, 11, 14⟩, ⟨15, 3, 10, 16⟩, ⟨15, 3, 9, 18⟩, ⟨15, 3, 8, 20⟩, ⟨15, 3, 7, 22⟩, ⟨15, 3, 6, 24⟩, ⟨15, 3, 5, 26⟩, ⟨15, 3, 4, 28⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_20090 (AllWinning.cons node_19257 (AllWinning.cons node_18307 (AllWinning.cons node_17360 (AllWinning.cons node_16339 (AllWinning.cons node_15276 (AllWinning.cons node_14270 (AllWinning.cons node_13252 (AllWinning.cons node_12230 (AllWinning.cons node_11156 (AllWinning.cons node_10029 (AllWinning.cons node_8987 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_20243 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.cons node_20250 (AllWinning.cons node_19473 (AllWinning.cons node_18609 (AllWinning.cons node_17704 (AllWinning.cons node_16789 (AllWinning.cons node_15741 (AllWinning.cons node_14761 (AllWinning.cons node_13814 (AllWinning.cons node_12839 (AllWinning.cons node_11848 (AllWinning.cons node_10850 (AllWinning.cons node_9782 (AllWinning.nil)))))))))))))))))))))))))))))))

theorem node_22226 : Outcome ⟨15, 3, 18, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 3, 18, 2⟩, ⟨13, 3, 18, 4⟩, ⟨12, 3, 18, 6⟩, ⟨11, 3, 18, 8⟩, ⟨10, 3, 18, 10⟩, ⟨9, 3, 18, 12⟩, ⟨8, 3, 18, 14⟩, ⟨7, 3, 18, 16⟩, ⟨6, 3, 18, 18⟩, ⟨5, 3, 18, 20⟩, ⟨4, 3, 18, 22⟩, ⟨3, 3, 18, 24⟩, ⟨2, 3, 18, 26⟩, ⟨1, 3, 18, 28⟩, ⟨0, 3, 18, 30⟩, ⟨15, 2, 18, 2⟩, ⟨15, 1, 18, 4⟩, ⟨15, 0, 18, 6⟩, ⟨15, 3, 17, 2⟩, ⟨15, 3, 16, 4⟩, ⟨15, 3, 15, 6⟩, ⟨15, 3, 14, 8⟩, ⟨15, 3, 13, 10⟩, ⟨15, 3, 12, 12⟩, ⟨15, 3, 11, 14⟩, ⟨15, 3, 10, 16⟩, ⟨15, 3, 9, 18⟩, ⟨15, 3, 8, 20⟩, ⟨15, 3, 7, 22⟩, ⟨15, 3, 6, 24⟩, ⟨15, 3, 5, 26⟩, ⟨15, 3, 4, 28⟩, ⟨15, 3, 3, 30⟩, ⟨15, 3, 2, 32⟩]
  exact AllWinning.cons node_21585 (AllWinning.cons node_20883 (AllWinning.cons node_20090 (AllWinning.cons node_19257 (AllWinning.cons node_18307 (AllWinning.cons node_17360 (AllWinning.cons node_16339 (AllWinning.cons node_15276 (AllWinning.cons node_14270 (AllWinning.cons node_13252 (AllWinning.cons node_12230 (AllWinning.cons node_11156 (AllWinning.cons node_10029 (AllWinning.cons node_8987 (AllWinning.cons node_7915 (AllWinning.cons node_21623 (AllWinning.cons node_20985 (AllWinning.cons node_20243 (AllWinning.cons node_21624 (AllWinning.cons node_20989 (AllWinning.cons node_20250 (AllWinning.cons node_19473 (AllWinning.cons node_18609 (AllWinning.cons node_17704 (AllWinning.cons node_16789 (AllWinning.cons node_15741 (AllWinning.cons node_14761 (AllWinning.cons node_13814 (AllWinning.cons node_12839 (AllWinning.cons node_11848 (AllWinning.cons node_10850 (AllWinning.cons node_9782 (AllWinning.cons node_8836 (AllWinning.cons node_7844 (AllWinning.nil))))))))))))))))))))))))))))))))))

theorem node_22227 : Outcome ⟨15, 4, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 17, 2⟩, ⟨13, 4, 17, 4⟩, ⟨15, 3, 17, 2⟩, ⟨15, 2, 17, 4⟩, ⟨15, 4, 16, 2⟩, ⟨15, 4, 15, 4⟩]
  exact AllWinning.cons node_21586 (AllWinning.cons node_20886 (AllWinning.cons node_21624 (AllWinning.cons node_20987 (AllWinning.cons node_21625 (AllWinning.cons node_20991 (AllWinning.nil))))))

theorem node_22228 : Outcome ⟨15, 4, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 17, 2⟩, ⟨13, 4, 17, 4⟩, ⟨12, 4, 17, 6⟩, ⟨11, 4, 17, 8⟩, ⟨15, 3, 17, 2⟩, ⟨15, 2, 17, 4⟩, ⟨15, 1, 17, 6⟩, ⟨15, 0, 17, 8⟩, ⟨15, 4, 16, 2⟩, ⟨15, 4, 15, 4⟩, ⟨15, 4, 14, 6⟩, ⟨15, 4, 13, 8⟩]
  exact AllWinning.cons node_21586 (AllWinning.cons node_20886 (AllWinning.cons node_20092 (AllWinning.cons node_19260 (AllWinning.cons node_21624 (AllWinning.cons node_20987 (AllWinning.cons node_20245 (AllWinning.cons node_19456 (AllWinning.cons node_21625 (AllWinning.cons node_20991 (AllWinning.cons node_20253 (AllWinning.cons node_19477 (AllWinning.nil))))))))))))

theorem node_22229 : Outcome ⟨15, 4, 17, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 4, 17, 2⟩, ⟨13, 4, 17, 4⟩, ⟨12, 4, 17, 6⟩, ⟨11, 4, 17, 8⟩, ⟨10, 4, 17, 10⟩, ⟨9, 4, 17, 12⟩, ⟨15, 3, 17, 2⟩, ⟨15, 2, 17, 4⟩, ⟨15, 1, 17, 6⟩, ⟨15, 0, 17, 8⟩, ⟨15, 4, 16, 2⟩, ⟨15, 4, 15, 4⟩, ⟨15, 4, 14, 6⟩, ⟨15, 4, 13, 8⟩, ⟨15, 4, 12, 10⟩, ⟨15, 4, 11, 12⟩]
  exact AllWinning.cons node_21586 (AllWinning.cons node_20886 (AllWinning.cons node_20092 (AllWinning.cons node_19260 (AllWinning.cons node_18309 (AllWinning.cons node_17362 (AllWinning.cons node_21624 (AllWinning.cons node_20987 (AllWinning.cons node_20245 (AllWinning.cons node_19456 (AllWinning.cons node_21625 (AllWinning.cons node_20991 (AllWinning.cons node_20253 (AllWinning.cons node_19477 (AllWinning.cons node_18613 (AllWinning.cons node_17708 (AllWinning.nil))))))))))))))))

theorem node_22230 : Outcome ⟨15, 5, 16, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 15, 2⟩) (by decide) node_21628

theorem node_22231 : Outcome ⟨15, 5, 16, 6⟩ true :=
  Outcome.win (q := ⟨15, 1, 16, 8⟩) (by decide) node_19460

theorem node_22232 : Outcome ⟨15, 5, 16, 14⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 16⟩) (by decide) node_15750

theorem node_22233 : Outcome ⟨15, 6, 15, 2⟩ true :=
  Outcome.win (q := ⟨15, 5, 15, 2⟩) (by decide) node_21628

theorem node_22234 : Outcome ⟨15, 6, 15, 8⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 12⟩) (by decide) node_17694

theorem node_22235 : Outcome ⟨15, 6, 15, 10⟩ true :=
  Outcome.win (q := ⟨15, 0, 15, 12⟩) (by decide) node_17694

theorem node_22236 : Outcome ⟨15, 7, 14, 2⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 4⟩) (by decide) node_21001

theorem node_22237 : Outcome ⟨15, 7, 14, 12⟩ true :=
  Outcome.win (q := ⟨15, 7, 12, 4⟩) (by decide) node_21001

theorem node_22238 : Outcome ⟨15, 8, 13, 2⟩ true :=
  Outcome.win (q := ⟨13, 8, 13, 4⟩) (by decide) node_20894

theorem node_22239 : Outcome ⟨15, 8, 13, 8⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 16⟩) (by decide) node_15767

theorem node_22240 : Outcome ⟨15, 8, 13, 12⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 16⟩) (by decide) node_15767

theorem node_22241 : Outcome ⟨15, 9, 12, 2⟩ true :=
  Outcome.win (q := ⟨13, 9, 12, 4⟩) (by decide) node_20899

theorem node_22242 : Outcome ⟨15, 9, 12, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 9, 6⟩) (by decide) node_20265

theorem node_22243 : Outcome ⟨15, 9, 12, 14⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 24⟩) (by decide) node_11182

theorem node_22244 : Outcome ⟨15, 10, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 10, 11, 2⟩, ⟨13, 10, 11, 4⟩, ⟨15, 9, 11, 2⟩, ⟨15, 8, 11, 4⟩, ⟨15, 10, 10, 2⟩, ⟨15, 10, 9, 4⟩]
  exact AllWinning.cons node_21597 (AllWinning.cons node_20903 (AllWinning.cons node_21640 (AllWinning.cons node_21007 (AllWinning.cons node_21642 (AllWinning.cons node_21014 (AllWinning.nil))))))

theorem node_22245 : Outcome ⟨15, 10, 11, 4⟩ true :=
  Outcome.win (q := ⟨15, 6, 11, 8⟩) (by decide) node_19484

theorem node_22246 : Outcome ⟨15, 10, 11, 8⟩ true :=
  Outcome.win (q := ⟨8, 10, 11, 14⟩) (by decide) node_16363

theorem node_22247 : Outcome ⟨15, 11, 10, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 11, 10, 2⟩, ⟨13, 11, 10, 4⟩, ⟨15, 10, 10, 2⟩, ⟨15, 9, 10, 4⟩, ⟨15, 11, 9, 2⟩, ⟨15, 11, 8, 4⟩]
  exact AllWinning.cons node_21600 (AllWinning.cons node_20905 (AllWinning.cons node_21642 (AllWinning.cons node_21010 (AllWinning.cons node_21645 (AllWinning.cons node_21017 (AllWinning.nil))))))

theorem node_22248 : Outcome ⟨15, 11, 10, 4⟩ true :=
  Outcome.win (q := ⟨15, 11, 6, 8⟩) (by decide) node_19499

theorem node_22249 : Outcome ⟨15, 11, 10, 8⟩ true :=
  Outcome.win (q := ⟨8, 11, 10, 14⟩) (by decide) node_16369

theorem node_22250 : Outcome ⟨15, 12, 9, 2⟩ true :=
  Outcome.win (q := ⟨13, 12, 9, 4⟩) (by decide) node_20907

theorem node_22251 : Outcome ⟨15, 12, 9, 4⟩ true :=
  Outcome.win (q := ⟨15, 9, 9, 6⟩) (by decide) node_20265

theorem node_22252 : Outcome ⟨15, 12, 9, 14⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 24⟩) (by decide) node_11203

theorem node_22253 : Outcome ⟨15, 13, 8, 2⟩ true :=
  Outcome.win (q := ⟨13, 13, 8, 4⟩) (by decide) node_20910

theorem node_22254 : Outcome ⟨15, 13, 8, 8⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 16⟩) (by decide) node_15750

theorem node_22255 : Outcome ⟨15, 13, 8, 12⟩ true :=
  Outcome.win (q := ⟨15, 5, 8, 16⟩) (by decide) node_15750

theorem node_22256 : Outcome ⟨15, 14, 7, 2⟩ true :=
  Outcome.win (q := ⟨15, 12, 7, 4⟩) (by decide) node_21020

theorem node_22257 : Outcome ⟨15, 14, 7, 12⟩ true :=
  Outcome.win (q := ⟨15, 12, 7, 4⟩) (by decide) node_21020

theorem node_22258 : Outcome ⟨15, 15, 6, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 5, 2⟩) (by decide) node_21655

theorem node_22259 : Outcome ⟨15, 15, 6, 8⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 12⟩) (by decide) node_17746

theorem node_22260 : Outcome ⟨15, 15, 6, 10⟩ true :=
  Outcome.win (q := ⟨15, 15, 0, 12⟩) (by decide) node_17746

theorem node_22261 : Outcome ⟨15, 16, 5, 2⟩ true :=
  Outcome.win (q := ⟨15, 15, 5, 2⟩) (by decide) node_21655

theorem node_22262 : Outcome ⟨15, 16, 5, 14⟩ true :=
  Outcome.win (q := ⟨15, 8, 5, 16⟩) (by decide) node_15767

theorem node_22263 : Outcome ⟨15, 17, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 17, 4, 2⟩, ⟨13, 17, 4, 4⟩, ⟨15, 16, 4, 2⟩, ⟨15, 15, 4, 4⟩, ⟨15, 17, 3, 2⟩, ⟨15, 17, 2, 4⟩]
  exact AllWinning.cons node_21612 (AllWinning.cons node_20921 (AllWinning.cons node_21658 (AllWinning.cons node_21033 (AllWinning.cons node_21661 (AllWinning.cons node_21037 (AllWinning.nil))))))

theorem node_22264 : Outcome ⟨15, 17, 4, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 17, 4, 2⟩, ⟨13, 17, 4, 4⟩, ⟨12, 17, 4, 6⟩, ⟨11, 17, 4, 8⟩, ⟨15, 16, 4, 2⟩, ⟨15, 15, 4, 4⟩, ⟨15, 14, 4, 6⟩, ⟨15, 13, 4, 8⟩, ⟨15, 17, 3, 2⟩, ⟨15, 17, 2, 4⟩, ⟨15, 17, 1, 6⟩, ⟨15, 17, 0, 8⟩]
  exact AllWinning.cons node_21612 (AllWinning.cons node_20921 (AllWinning.cons node_20118 (AllWinning.cons node_19297 (AllWinning.cons node_21658 (AllWinning.cons node_21033 (AllWinning.cons node_20276 (AllWinning.cons node_19506 (AllWinning.cons node_21661 (AllWinning.cons node_21037 (AllWinning.cons node_20285 (AllWinning.cons node_19527 (AllWinning.nil))))))))))))

theorem node_22265 : Outcome ⟨15, 17, 4, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 17, 4, 2⟩, ⟨13, 17, 4, 4⟩, ⟨12, 17, 4, 6⟩, ⟨11, 17, 4, 8⟩, ⟨10, 17, 4, 10⟩, ⟨9, 17, 4, 12⟩, ⟨15, 16, 4, 2⟩, ⟨15, 15, 4, 4⟩, ⟨15, 14, 4, 6⟩, ⟨15, 13, 4, 8⟩, ⟨15, 12, 4, 10⟩, ⟨15, 11, 4, 12⟩, ⟨15, 17, 3, 2⟩, ⟨15, 17, 2, 4⟩, ⟨15, 17, 1, 6⟩, ⟨15, 17, 0, 8⟩]
  exact AllWinning.cons node_21612 (AllWinning.cons node_20921 (AllWinning.cons node_20118 (AllWinning.cons node_19297 (AllWinning.cons node_18352 (AllWinning.cons node_17394 (AllWinning.cons node_21658 (AllWinning.cons node_21033 (AllWinning.cons node_20276 (AllWinning.cons node_19506 (AllWinning.cons node_18640 (AllWinning.cons node_17730 (AllWinning.cons node_21661 (AllWinning.cons node_21037 (AllWinning.cons node_20285 (AllWinning.cons node_19527 (AllWinning.nil))))))))))))))))

theorem node_22266 : Outcome ⟨15, 18, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 3, 2⟩, ⟨13, 18, 3, 4⟩, ⟨15, 17, 3, 2⟩, ⟨15, 16, 3, 4⟩, ⟨15, 18, 2, 2⟩, ⟨15, 18, 1, 4⟩]
  exact AllWinning.cons node_21614 (AllWinning.cons node_20923 (AllWinning.cons node_21661 (AllWinning.cons node_21035 (AllWinning.cons node_21662 (AllWinning.cons node_21039 (AllWinning.nil))))))

theorem node_22267 : Outcome ⟨15, 18, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 3, 2⟩, ⟨13, 18, 3, 4⟩, ⟨12, 18, 3, 6⟩, ⟨11, 18, 3, 8⟩, ⟨15, 17, 3, 2⟩, ⟨15, 16, 3, 4⟩, ⟨15, 15, 3, 6⟩, ⟨15, 14, 3, 8⟩, ⟨15, 18, 2, 2⟩, ⟨15, 18, 1, 4⟩, ⟨15, 18, 0, 6⟩]
  exact AllWinning.cons node_21614 (AllWinning.cons node_20923 (AllWinning.cons node_20120 (AllWinning.cons node_19299 (AllWinning.cons node_21661 (AllWinning.cons node_21035 (AllWinning.cons node_20280 (AllWinning.cons node_19510 (AllWinning.cons node_21662 (AllWinning.cons node_21039 (AllWinning.cons node_20287 (AllWinning.nil)))))))))))

theorem node_22268 : Outcome ⟨15, 18, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 3, 2⟩, ⟨13, 18, 3, 4⟩, ⟨12, 18, 3, 6⟩, ⟨11, 18, 3, 8⟩, ⟨10, 18, 3, 10⟩, ⟨9, 18, 3, 12⟩, ⟨15, 17, 3, 2⟩, ⟨15, 16, 3, 4⟩, ⟨15, 15, 3, 6⟩, ⟨15, 14, 3, 8⟩, ⟨15, 13, 3, 10⟩, ⟨15, 12, 3, 12⟩, ⟨15, 18, 2, 2⟩, ⟨15, 18, 1, 4⟩, ⟨15, 18, 0, 6⟩]
  exact AllWinning.cons node_21614 (AllWinning.cons node_20923 (AllWinning.cons node_20120 (AllWinning.cons node_19299 (AllWinning.cons node_18357 (AllWinning.cons node_17396 (AllWinning.cons node_21661 (AllWinning.cons node_21035 (AllWinning.cons node_20280 (AllWinning.cons node_19510 (AllWinning.cons node_18643 (AllWinning.cons node_17734 (AllWinning.cons node_21662 (AllWinning.cons node_21039 (AllWinning.cons node_20287 (AllWinning.nil)))))))))))))))

theorem node_22269 : Outcome ⟨15, 18, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 3, 2⟩, ⟨13, 18, 3, 4⟩, ⟨12, 18, 3, 6⟩, ⟨11, 18, 3, 8⟩, ⟨10, 18, 3, 10⟩, ⟨9, 18, 3, 12⟩, ⟨8, 18, 3, 14⟩, ⟨7, 18, 3, 16⟩, ⟨15, 17, 3, 2⟩, ⟨15, 16, 3, 4⟩, ⟨15, 15, 3, 6⟩, ⟨15, 14, 3, 8⟩, ⟨15, 13, 3, 10⟩, ⟨15, 12, 3, 12⟩, ⟨15, 11, 3, 14⟩, ⟨15, 10, 3, 16⟩, ⟨15, 18, 2, 2⟩, ⟨15, 18, 1, 4⟩, ⟨15, 18, 0, 6⟩]
  exact AllWinning.cons node_21614 (AllWinning.cons node_20923 (AllWinning.cons node_20120 (AllWinning.cons node_19299 (AllWinning.cons node_18357 (AllWinning.cons node_17396 (AllWinning.cons node_16391 (AllWinning.cons node_15316 (AllWinning.cons node_21661 (AllWinning.cons node_21035 (AllWinning.cons node_20280 (AllWinning.cons node_19510 (AllWinning.cons node_18643 (AllWinning.cons node_17734 (AllWinning.cons node_16808 (AllWinning.cons node_15776 (AllWinning.cons node_21662 (AllWinning.cons node_21039 (AllWinning.cons node_20287 (AllWinning.nil)))))))))))))))))))

theorem node_22270 : Outcome ⟨15, 18, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 3, 2⟩, ⟨13, 18, 3, 4⟩, ⟨12, 18, 3, 6⟩, ⟨11, 18, 3, 8⟩, ⟨10, 18, 3, 10⟩, ⟨9, 18, 3, 12⟩, ⟨8, 18, 3, 14⟩, ⟨7, 18, 3, 16⟩, ⟨6, 18, 3, 18⟩, ⟨5, 18, 3, 20⟩, ⟨15, 17, 3, 2⟩, ⟨15, 16, 3, 4⟩, ⟨15, 15, 3, 6⟩, ⟨15, 14, 3, 8⟩, ⟨15, 13, 3, 10⟩, ⟨15, 12, 3, 12⟩, ⟨15, 11, 3, 14⟩, ⟨15, 10, 3, 16⟩, ⟨15, 9, 3, 18⟩, ⟨15, 8, 3, 20⟩, ⟨15, 18, 2, 2⟩, ⟨15, 18, 1, 4⟩, ⟨15, 18, 0, 6⟩]
  exact AllWinning.cons node_21614 (AllWinning.cons node_20923 (AllWinning.cons node_20120 (AllWinning.cons node_19299 (AllWinning.cons node_18357 (AllWinning.cons node_17396 (AllWinning.cons node_16391 (AllWinning.cons node_15316 (AllWinning.cons node_14316 (AllWinning.cons node_13290 (AllWinning.cons node_21661 (AllWinning.cons node_21035 (AllWinning.cons node_20280 (AllWinning.cons node_19510 (AllWinning.cons node_18643 (AllWinning.cons node_17734 (AllWinning.cons node_16808 (AllWinning.cons node_15776 (AllWinning.cons node_14777 (AllWinning.cons node_13826 (AllWinning.cons node_21662 (AllWinning.cons node_21039 (AllWinning.cons node_20287 (AllWinning.nil)))))))))))))))))))))))

theorem node_22271 : Outcome ⟨15, 18, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 18, 3, 2⟩, ⟨13, 18, 3, 4⟩, ⟨12, 18, 3, 6⟩, ⟨11, 18, 3, 8⟩, ⟨10, 18, 3, 10⟩, ⟨9, 18, 3, 12⟩, ⟨8, 18, 3, 14⟩, ⟨7, 18, 3, 16⟩, ⟨6, 18, 3, 18⟩, ⟨5, 18, 3, 20⟩, ⟨4, 18, 3, 22⟩, ⟨3, 18, 3, 24⟩, ⟨15, 17, 3, 2⟩, ⟨15, 16, 3, 4⟩, ⟨15, 15, 3, 6⟩, ⟨15, 14, 3, 8⟩, ⟨15, 13, 3, 10⟩, ⟨15, 12, 3, 12⟩, ⟨15, 11, 3, 14⟩, ⟨15, 10, 3, 16⟩, ⟨15, 9, 3, 18⟩, ⟨15, 8, 3, 20⟩, ⟨15, 7, 3, 22⟩, ⟨15, 6, 3, 24⟩, ⟨15, 18, 2, 2⟩, ⟨15, 18, 1, 4⟩, ⟨15, 18, 0, 6⟩]
  exact AllWinning.cons node_21614 (AllWinning.cons node_20923 (AllWinning.cons node_20120 (AllWinning.cons node_19299 (AllWinning.cons node_18357 (AllWinning.cons node_17396 (AllWinning.cons node_16391 (AllWinning.cons node_15316 (AllWinning.cons node_14316 (AllWinning.cons node_13290 (AllWinning.cons node_12272 (AllWinning.cons node_11221 (AllWinning.cons node_21661 (AllWinning.cons node_21035 (AllWinning.cons node_20280 (AllWinning.cons node_19510 (AllWinning.cons node_18643 (AllWinning.cons node_17734 (AllWinning.cons node_16808 (AllWinning.cons node_15776 (AllWinning.cons node_14777 (AllWinning.cons node_13826 (AllWinning.cons node_12854 (AllWinning.cons node_11857 (AllWinning.cons node_21662 (AllWinning.cons node_21039 (AllWinning.cons node_20287 (AllWinning.nil)))))))))))))))))))))))))))

end RQ9F1
