import Chunk55
set_option autoImplicit false
namespace RQ9F1

theorem node_13051 : Outcome ⟨1, 12, 13, 6⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 10⟩) (by decide) node_8030

theorem node_13052 : Outcome ⟨1, 12, 13, 10⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 10⟩) (by decide) node_8030

theorem node_13053 : Outcome ⟨1, 12, 13, 12⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 10⟩) (by decide) node_8030

theorem node_13054 : Outcome ⟨1, 13, 12, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 12, 2⟩, ⟨1, 12, 12, 2⟩, ⟨1, 11, 12, 4⟩, ⟨1, 13, 11, 2⟩, ⟨1, 13, 10, 4⟩]
  exact AllWinning.cons node_11985 (AllWinning.cons node_12045 (AllWinning.cons node_11058 (AllWinning.cons node_12049 (AllWinning.cons node_11066 (AllWinning.nil)))))

theorem node_13055 : Outcome ⟨1, 13, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 6⟩) (by decide) node_9986

theorem node_13056 : Outcome ⟨1, 13, 12, 6⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 10⟩) (by decide) node_8009

theorem node_13057 : Outcome ⟨1, 13, 12, 10⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 10⟩) (by decide) node_8009

theorem node_13058 : Outcome ⟨1, 13, 12, 12⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 10⟩) (by decide) node_8009

theorem node_13059 : Outcome ⟨1, 14, 11, 2⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 2⟩) (by decide) node_12052

theorem node_13060 : Outcome ⟨1, 14, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 2⟩) (by decide) node_12052

theorem node_13061 : Outcome ⟨1, 15, 10, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 10, 2⟩) (by decide) node_11989

theorem node_13062 : Outcome ⟨1, 15, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 15, 10, 2⟩) (by decide) node_11989

theorem node_13063 : Outcome ⟨1, 15, 10, 12⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 12⟩) (by decide) node_7092

theorem node_13064 : Outcome ⟨1, 16, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 9, 2⟩, ⟨1, 15, 9, 2⟩, ⟨1, 14, 9, 4⟩, ⟨1, 16, 8, 2⟩, ⟨1, 16, 7, 4⟩]
  exact AllWinning.cons node_11993 (AllWinning.cons node_12062 (AllWinning.cons node_11069 (AllWinning.cons node_12066 (AllWinning.cons node_11076 (AllWinning.nil)))))

theorem node_13065 : Outcome ⟨1, 16, 9, 6⟩ true :=
  Outcome.win (q := ⟨1, 13, 9, 6⟩) (by decide) node_9986

theorem node_13066 : Outcome ⟨1, 16, 9, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 22⟩) (by decide) node_3422

theorem node_13067 : Outcome ⟨1, 17, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 7, 2⟩) (by decide) node_12070

theorem node_13068 : Outcome ⟨1, 17, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 7, 2⟩) (by decide) node_12070

theorem node_13069 : Outcome ⟨1, 17, 8, 6⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 12⟩) (by decide) node_7103

theorem node_13070 : Outcome ⟨1, 17, 8, 10⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 12⟩) (by decide) node_7103

theorem node_13071 : Outcome ⟨1, 18, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 7, 2⟩) (by decide) node_12070

theorem node_13072 : Outcome ⟨1, 18, 7, 24⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 14⟩) (by decide) node_6168

theorem node_13073 : Outcome ⟨1, 19, 6, 6⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 6⟩) (by decide) node_9999

theorem node_13074 : Outcome ⟨1, 19, 6, 12⟩ true :=
  Outcome.win (q := ⟨1, 16, 6, 6⟩) (by decide) node_9999

theorem node_13075 : Outcome ⟨1, 19, 6, 24⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 32⟩) (by decide) node_1234

theorem node_13076 : Outcome ⟨1, 20, 5, 6⟩ true :=
  Outcome.win (q := ⟨1, 20, 4, 2⟩) (by decide) node_12080

theorem node_13077 : Outcome ⟨2, 4, 20, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 14, 12⟩) (by decide) node_7134

theorem node_13078 : Outcome ⟨2, 5, 19, 2⟩ true :=
  Outcome.win (q := ⟨2, 4, 19, 2⟩) (by decide) node_12088

theorem node_13079 : Outcome ⟨2, 5, 19, 6⟩ true :=
  Outcome.win (q := ⟨2, 4, 19, 2⟩) (by decide) node_12088

theorem node_13080 : Outcome ⟨2, 5, 19, 16⟩ true :=
  Outcome.win (q := ⟨2, 5, 10, 18⟩) (by decide) node_4751

theorem node_13081 : Outcome ⟨2, 6, 18, 2⟩ true :=
  Outcome.win (q := ⟨2, 6, 17, 2⟩) (by decide) node_12096

theorem node_13082 : Outcome ⟨2, 6, 18, 16⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 14⟩) (by decide) node_6223

theorem node_13083 : Outcome ⟨2, 6, 18, 20⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 14⟩) (by decide) node_6223

theorem node_13084 : Outcome ⟨2, 7, 17, 2⟩ true :=
  Outcome.win (q := ⟨1, 7, 17, 2⟩) (by decide) node_12020

theorem node_13085 : Outcome ⟨2, 7, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 12⟩) (by decide) node_7120

theorem node_13086 : Outcome ⟨2, 7, 17, 8⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 12⟩) (by decide) node_7120

theorem node_13087 : Outcome ⟨2, 8, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 16, 4⟩) (by decide) node_10989

theorem node_13088 : Outcome ⟨2, 8, 16, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 16, 4⟩) (by decide) node_10989

theorem node_13089 : Outcome ⟨2, 8, 16, 6⟩ true :=
  Outcome.win (q := ⟨0, 8, 16, 4⟩) (by decide) node_10989

theorem node_13090 : Outcome ⟨2, 8, 16, 20⟩ true :=
  Outcome.win (q := ⟨0, 8, 16, 4⟩) (by decide) node_10989

theorem node_13091 : Outcome ⟨2, 9, 15, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 15, 2⟩, ⟨0, 9, 15, 4⟩, ⟨2, 8, 15, 2⟩, ⟨2, 7, 15, 4⟩, ⟨2, 6, 15, 6⟩, ⟨2, 5, 15, 8⟩, ⟨2, 9, 14, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 9, 12, 6⟩, ⟨2, 9, 11, 8⟩]
  exact AllWinning.cons node_12028 (AllWinning.cons node_10993 (AllWinning.cons node_12106 (AllWinning.cons node_11107 (AllWinning.cons node_10039 (AllWinning.cons node_9067 (AllWinning.cons node_12109 (AllWinning.cons node_11112 (AllWinning.cons node_10047 (AllWinning.cons node_9081 (AllWinning.nil))))))))))

theorem node_13092 : Outcome ⟨2, 9, 15, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 15, 2⟩, ⟨0, 9, 15, 4⟩, ⟨2, 8, 15, 2⟩, ⟨2, 7, 15, 4⟩, ⟨2, 6, 15, 6⟩, ⟨2, 5, 15, 8⟩, ⟨2, 4, 15, 10⟩, ⟨2, 3, 15, 12⟩, ⟨2, 9, 14, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 9, 12, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 9, 10, 10⟩, ⟨2, 9, 9, 12⟩]
  exact AllWinning.cons node_12028 (AllWinning.cons node_10993 (AllWinning.cons node_12106 (AllWinning.cons node_11107 (AllWinning.cons node_10039 (AllWinning.cons node_9067 (AllWinning.cons node_8083 (AllWinning.cons node_7128 (AllWinning.cons node_12109 (AllWinning.cons node_11112 (AllWinning.cons node_10047 (AllWinning.cons node_9081 (AllWinning.cons node_8104 (AllWinning.cons node_7157 (AllWinning.nil))))))))))))))

theorem node_13093 : Outcome ⟨2, 9, 15, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 15, 2⟩, ⟨0, 9, 15, 4⟩, ⟨2, 8, 15, 2⟩, ⟨2, 7, 15, 4⟩, ⟨2, 6, 15, 6⟩, ⟨2, 5, 15, 8⟩, ⟨2, 4, 15, 10⟩, ⟨2, 3, 15, 12⟩, ⟨2, 2, 15, 14⟩, ⟨2, 1, 15, 16⟩, ⟨2, 9, 14, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 9, 12, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 9, 10, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 9, 8, 14⟩, ⟨2, 9, 7, 16⟩]
  exact AllWinning.cons node_12028 (AllWinning.cons node_10993 (AllWinning.cons node_12106 (AllWinning.cons node_11107 (AllWinning.cons node_10039 (AllWinning.cons node_9067 (AllWinning.cons node_8083 (AllWinning.cons node_7128 (AllWinning.cons node_6205 (AllWinning.cons node_5462 (AllWinning.cons node_12109 (AllWinning.cons node_11112 (AllWinning.cons node_10047 (AllWinning.cons node_9081 (AllWinning.cons node_8104 (AllWinning.cons node_7157 (AllWinning.cons node_6235 (AllWinning.cons node_5491 (AllWinning.nil))))))))))))))))))

theorem node_13094 : Outcome ⟨2, 9, 15, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 15, 2⟩, ⟨0, 9, 15, 4⟩, ⟨2, 8, 15, 2⟩, ⟨2, 7, 15, 4⟩, ⟨2, 6, 15, 6⟩, ⟨2, 5, 15, 8⟩, ⟨2, 4, 15, 10⟩, ⟨2, 3, 15, 12⟩, ⟨2, 2, 15, 14⟩, ⟨2, 1, 15, 16⟩, ⟨2, 0, 15, 18⟩, ⟨2, 9, 14, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 9, 12, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 9, 10, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 9, 8, 14⟩, ⟨2, 9, 7, 16⟩, ⟨2, 9, 6, 18⟩, ⟨2, 9, 5, 20⟩]
  exact AllWinning.cons node_12028 (AllWinning.cons node_10993 (AllWinning.cons node_12106 (AllWinning.cons node_11107 (AllWinning.cons node_10039 (AllWinning.cons node_9067 (AllWinning.cons node_8083 (AllWinning.cons node_7128 (AllWinning.cons node_6205 (AllWinning.cons node_5462 (AllWinning.cons node_4725 (AllWinning.cons node_12109 (AllWinning.cons node_11112 (AllWinning.cons node_10047 (AllWinning.cons node_9081 (AllWinning.cons node_8104 (AllWinning.cons node_7157 (AllWinning.cons node_6235 (AllWinning.cons node_5491 (AllWinning.cons node_4771 (AllWinning.cons node_4082 (AllWinning.nil)))))))))))))))))))))

theorem node_13095 : Outcome ⟨2, 9, 15, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 15, 2⟩, ⟨0, 9, 15, 4⟩, ⟨2, 8, 15, 2⟩, ⟨2, 7, 15, 4⟩, ⟨2, 6, 15, 6⟩, ⟨2, 5, 15, 8⟩, ⟨2, 4, 15, 10⟩, ⟨2, 3, 15, 12⟩, ⟨2, 2, 15, 14⟩, ⟨2, 1, 15, 16⟩, ⟨2, 0, 15, 18⟩, ⟨2, 9, 14, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 9, 12, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 9, 10, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 9, 8, 14⟩, ⟨2, 9, 7, 16⟩, ⟨2, 9, 6, 18⟩, ⟨2, 9, 5, 20⟩, ⟨2, 9, 4, 22⟩, ⟨2, 9, 3, 24⟩]
  exact AllWinning.cons node_12028 (AllWinning.cons node_10993 (AllWinning.cons node_12106 (AllWinning.cons node_11107 (AllWinning.cons node_10039 (AllWinning.cons node_9067 (AllWinning.cons node_8083 (AllWinning.cons node_7128 (AllWinning.cons node_6205 (AllWinning.cons node_5462 (AllWinning.cons node_4725 (AllWinning.cons node_12109 (AllWinning.cons node_11112 (AllWinning.cons node_10047 (AllWinning.cons node_9081 (AllWinning.cons node_8104 (AllWinning.cons node_7157 (AllWinning.cons node_6235 (AllWinning.cons node_5491 (AllWinning.cons node_4771 (AllWinning.cons node_4082 (AllWinning.cons node_3519 (AllWinning.cons node_2979 (AllWinning.nil)))))))))))))))))))))))

theorem node_13096 : Outcome ⟨2, 9, 15, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 15, 2⟩, ⟨0, 9, 15, 4⟩, ⟨2, 8, 15, 2⟩, ⟨2, 7, 15, 4⟩, ⟨2, 6, 15, 6⟩, ⟨2, 5, 15, 8⟩, ⟨2, 4, 15, 10⟩, ⟨2, 3, 15, 12⟩, ⟨2, 2, 15, 14⟩, ⟨2, 1, 15, 16⟩, ⟨2, 0, 15, 18⟩, ⟨2, 9, 14, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 9, 12, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 9, 10, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 9, 8, 14⟩, ⟨2, 9, 7, 16⟩, ⟨2, 9, 6, 18⟩, ⟨2, 9, 5, 20⟩, ⟨2, 9, 4, 22⟩, ⟨2, 9, 3, 24⟩, ⟨2, 9, 2, 26⟩, ⟨2, 9, 1, 28⟩]
  exact AllWinning.cons node_12028 (AllWinning.cons node_10993 (AllWinning.cons node_12106 (AllWinning.cons node_11107 (AllWinning.cons node_10039 (AllWinning.cons node_9067 (AllWinning.cons node_8083 (AllWinning.cons node_7128 (AllWinning.cons node_6205 (AllWinning.cons node_5462 (AllWinning.cons node_4725 (AllWinning.cons node_12109 (AllWinning.cons node_11112 (AllWinning.cons node_10047 (AllWinning.cons node_9081 (AllWinning.cons node_8104 (AllWinning.cons node_7157 (AllWinning.cons node_6235 (AllWinning.cons node_5491 (AllWinning.cons node_4771 (AllWinning.cons node_4082 (AllWinning.cons node_3519 (AllWinning.cons node_2979 (AllWinning.cons node_2520 (AllWinning.cons node_2048 (AllWinning.nil)))))))))))))))))))))))))

theorem node_13097 : Outcome ⟨2, 9, 15, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 9, 15, 2⟩, ⟨0, 9, 15, 4⟩, ⟨2, 8, 15, 2⟩, ⟨2, 7, 15, 4⟩, ⟨2, 6, 15, 6⟩, ⟨2, 5, 15, 8⟩, ⟨2, 4, 15, 10⟩, ⟨2, 3, 15, 12⟩, ⟨2, 2, 15, 14⟩, ⟨2, 1, 15, 16⟩, ⟨2, 0, 15, 18⟩, ⟨2, 9, 14, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 9, 12, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 9, 10, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 9, 8, 14⟩, ⟨2, 9, 7, 16⟩, ⟨2, 9, 6, 18⟩, ⟨2, 9, 5, 20⟩, ⟨2, 9, 4, 22⟩, ⟨2, 9, 3, 24⟩, ⟨2, 9, 2, 26⟩, ⟨2, 9, 1, 28⟩, ⟨2, 9, 0, 30⟩]
  exact AllWinning.cons node_12028 (AllWinning.cons node_10993 (AllWinning.cons node_12106 (AllWinning.cons node_11107 (AllWinning.cons node_10039 (AllWinning.cons node_9067 (AllWinning.cons node_8083 (AllWinning.cons node_7128 (AllWinning.cons node_6205 (AllWinning.cons node_5462 (AllWinning.cons node_4725 (AllWinning.cons node_12109 (AllWinning.cons node_11112 (AllWinning.cons node_10047 (AllWinning.cons node_9081 (AllWinning.cons node_8104 (AllWinning.cons node_7157 (AllWinning.cons node_6235 (AllWinning.cons node_5491 (AllWinning.cons node_4771 (AllWinning.cons node_4082 (AllWinning.cons node_3519 (AllWinning.cons node_2979 (AllWinning.cons node_2520 (AllWinning.cons node_2048 (AllWinning.cons node_1676 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13098 : Outcome ⟨2, 10, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 10, 14, 2⟩) (by decide) node_12032

theorem node_13099 : Outcome ⟨2, 11, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 11, 13, 2⟩, ⟨0, 11, 13, 4⟩, ⟨2, 10, 13, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 11, 12, 2⟩, ⟨2, 11, 11, 4⟩]
  exact AllWinning.cons node_12042 (AllWinning.cons node_10997 (AllWinning.cons node_12111 (AllWinning.cons node_11112 (AllWinning.cons node_12113 (AllWinning.cons node_11118 (AllWinning.nil))))))

theorem node_13100 : Outcome ⟨2, 11, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 11, 13, 2⟩, ⟨0, 11, 13, 4⟩, ⟨2, 10, 13, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 8, 13, 6⟩, ⟨2, 7, 13, 8⟩, ⟨2, 11, 12, 2⟩, ⟨2, 11, 11, 4⟩, ⟨2, 11, 10, 6⟩, ⟨2, 11, 9, 8⟩]
  exact AllWinning.cons node_12042 (AllWinning.cons node_10997 (AllWinning.cons node_12111 (AllWinning.cons node_11112 (AllWinning.cons node_10044 (AllWinning.cons node_9074 (AllWinning.cons node_12113 (AllWinning.cons node_11118 (AllWinning.cons node_10057 (AllWinning.cons node_9088 (AllWinning.nil))))))))))

theorem node_13101 : Outcome ⟨2, 11, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 11, 13, 2⟩, ⟨0, 11, 13, 4⟩, ⟨2, 10, 13, 2⟩, ⟨2, 9, 13, 4⟩, ⟨2, 8, 13, 6⟩, ⟨2, 7, 13, 8⟩, ⟨2, 6, 13, 10⟩, ⟨2, 5, 13, 12⟩, ⟨2, 11, 12, 2⟩, ⟨2, 11, 11, 4⟩, ⟨2, 11, 10, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 11, 8, 10⟩, ⟨2, 11, 7, 12⟩]
  exact AllWinning.cons node_12042 (AllWinning.cons node_10997 (AllWinning.cons node_12111 (AllWinning.cons node_11112 (AllWinning.cons node_10044 (AllWinning.cons node_9074 (AllWinning.cons node_8087 (AllWinning.cons node_7139 (AllWinning.cons node_12113 (AllWinning.cons node_11118 (AllWinning.cons node_10057 (AllWinning.cons node_9088 (AllWinning.cons node_8112 (AllWinning.cons node_7164 (AllWinning.nil))))))))))))))

theorem node_13102 : Outcome ⟨2, 11, 13, 8⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 14⟩) (by decide) node_6247

theorem node_13103 : Outcome ⟨2, 12, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 4⟩) (by decide) node_11000

theorem node_13104 : Outcome ⟨2, 12, 12, 4⟩ true :=
  Outcome.win (q := ⟨0, 12, 12, 4⟩) (by decide) node_11000

theorem node_13105 : Outcome ⟨2, 13, 11, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 11, 2⟩, ⟨0, 13, 11, 4⟩, ⟨2, 12, 11, 2⟩, ⟨2, 11, 11, 4⟩, ⟨2, 13, 10, 2⟩, ⟨2, 13, 9, 4⟩]
  exact AllWinning.cons node_12049 (AllWinning.cons node_11008 (AllWinning.cons node_12117 (AllWinning.cons node_11118 (AllWinning.cons node_12121 (AllWinning.cons node_11125 (AllWinning.nil))))))

theorem node_13106 : Outcome ⟨2, 13, 11, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 11, 2⟩, ⟨0, 13, 11, 4⟩, ⟨2, 12, 11, 2⟩, ⟨2, 11, 11, 4⟩, ⟨2, 10, 11, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 13, 10, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 13, 8, 6⟩, ⟨2, 13, 7, 8⟩]
  exact AllWinning.cons node_12049 (AllWinning.cons node_11008 (AllWinning.cons node_12117 (AllWinning.cons node_11118 (AllWinning.cons node_10051 (AllWinning.cons node_9081 (AllWinning.cons node_12121 (AllWinning.cons node_11125 (AllWinning.cons node_10064 (AllWinning.cons node_9094 (AllWinning.nil))))))))))

theorem node_13107 : Outcome ⟨2, 13, 11, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 13, 11, 2⟩, ⟨0, 13, 11, 4⟩, ⟨2, 12, 11, 2⟩, ⟨2, 11, 11, 4⟩, ⟨2, 10, 11, 6⟩, ⟨2, 9, 11, 8⟩, ⟨2, 8, 11, 10⟩, ⟨2, 7, 11, 12⟩, ⟨2, 13, 10, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 13, 8, 6⟩, ⟨2, 13, 7, 8⟩, ⟨2, 13, 6, 10⟩, ⟨2, 13, 5, 12⟩]
  exact AllWinning.cons node_12049 (AllWinning.cons node_11008 (AllWinning.cons node_12117 (AllWinning.cons node_11118 (AllWinning.cons node_10051 (AllWinning.cons node_9081 (AllWinning.cons node_8098 (AllWinning.cons node_7146 (AllWinning.cons node_12121 (AllWinning.cons node_11125 (AllWinning.cons node_10064 (AllWinning.cons node_9094 (AllWinning.cons node_8124 (AllWinning.cons node_7174 (AllWinning.nil))))))))))))))

theorem node_13108 : Outcome ⟨2, 13, 11, 8⟩ true :=
  Outcome.win (q := ⟨2, 6, 11, 14⟩) (by decide) node_6223

theorem node_13109 : Outcome ⟨2, 14, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 14, 10, 2⟩) (by decide) node_12052

theorem node_13110 : Outcome ⟨2, 15, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 9, 2⟩, ⟨0, 15, 9, 4⟩, ⟨2, 14, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 12, 9, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 15, 8, 2⟩, ⟨2, 15, 7, 4⟩, ⟨2, 15, 6, 6⟩, ⟨2, 15, 5, 8⟩]
  exact AllWinning.cons node_12062 (AllWinning.cons node_11013 (AllWinning.cons node_12123 (AllWinning.cons node_11125 (AllWinning.cons node_10062 (AllWinning.cons node_9088 (AllWinning.cons node_12125 (AllWinning.cons node_11130 (AllWinning.cons node_10070 (AllWinning.cons node_9103 (AllWinning.nil))))))))))

theorem node_13111 : Outcome ⟨2, 15, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 9, 2⟩, ⟨0, 15, 9, 4⟩, ⟨2, 14, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 12, 9, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 10, 9, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 15, 8, 2⟩, ⟨2, 15, 7, 4⟩, ⟨2, 15, 6, 6⟩, ⟨2, 15, 5, 8⟩, ⟨2, 15, 4, 10⟩, ⟨2, 15, 3, 12⟩]
  exact AllWinning.cons node_12062 (AllWinning.cons node_11013 (AllWinning.cons node_12123 (AllWinning.cons node_11125 (AllWinning.cons node_10062 (AllWinning.cons node_9088 (AllWinning.cons node_8109 (AllWinning.cons node_7157 (AllWinning.cons node_12125 (AllWinning.cons node_11130 (AllWinning.cons node_10070 (AllWinning.cons node_9103 (AllWinning.cons node_8130 (AllWinning.cons node_7185 (AllWinning.nil))))))))))))))

theorem node_13112 : Outcome ⟨2, 15, 9, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 9, 2⟩, ⟨0, 15, 9, 4⟩, ⟨2, 14, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 12, 9, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 10, 9, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 8, 9, 14⟩, ⟨2, 7, 9, 16⟩, ⟨2, 15, 8, 2⟩, ⟨2, 15, 7, 4⟩, ⟨2, 15, 6, 6⟩, ⟨2, 15, 5, 8⟩, ⟨2, 15, 4, 10⟩, ⟨2, 15, 3, 12⟩, ⟨2, 15, 2, 14⟩, ⟨2, 15, 1, 16⟩]
  exact AllWinning.cons node_12062 (AllWinning.cons node_11013 (AllWinning.cons node_12123 (AllWinning.cons node_11125 (AllWinning.cons node_10062 (AllWinning.cons node_9088 (AllWinning.cons node_8109 (AllWinning.cons node_7157 (AllWinning.cons node_6232 (AllWinning.cons node_5482 (AllWinning.cons node_12125 (AllWinning.cons node_11130 (AllWinning.cons node_10070 (AllWinning.cons node_9103 (AllWinning.cons node_8130 (AllWinning.cons node_7185 (AllWinning.cons node_6264 (AllWinning.cons node_5512 (AllWinning.nil))))))))))))))))))

theorem node_13113 : Outcome ⟨2, 15, 9, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 9, 2⟩, ⟨0, 15, 9, 4⟩, ⟨2, 14, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 12, 9, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 10, 9, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 8, 9, 14⟩, ⟨2, 7, 9, 16⟩, ⟨2, 6, 9, 18⟩, ⟨2, 5, 9, 20⟩, ⟨2, 15, 8, 2⟩, ⟨2, 15, 7, 4⟩, ⟨2, 15, 6, 6⟩, ⟨2, 15, 5, 8⟩, ⟨2, 15, 4, 10⟩, ⟨2, 15, 3, 12⟩, ⟨2, 15, 2, 14⟩, ⟨2, 15, 1, 16⟩, ⟨2, 15, 0, 18⟩]
  exact AllWinning.cons node_12062 (AllWinning.cons node_11013 (AllWinning.cons node_12123 (AllWinning.cons node_11125 (AllWinning.cons node_10062 (AllWinning.cons node_9088 (AllWinning.cons node_8109 (AllWinning.cons node_7157 (AllWinning.cons node_6232 (AllWinning.cons node_5482 (AllWinning.cons node_4758 (AllWinning.cons node_4067 (AllWinning.cons node_12125 (AllWinning.cons node_11130 (AllWinning.cons node_10070 (AllWinning.cons node_9103 (AllWinning.cons node_8130 (AllWinning.cons node_7185 (AllWinning.cons node_6264 (AllWinning.cons node_5512 (AllWinning.cons node_4808 (AllWinning.nil)))))))))))))))))))))

theorem node_13114 : Outcome ⟨2, 15, 9, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 9, 2⟩, ⟨0, 15, 9, 4⟩, ⟨2, 14, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 12, 9, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 10, 9, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 8, 9, 14⟩, ⟨2, 7, 9, 16⟩, ⟨2, 6, 9, 18⟩, ⟨2, 5, 9, 20⟩, ⟨2, 4, 9, 22⟩, ⟨2, 3, 9, 24⟩, ⟨2, 15, 8, 2⟩, ⟨2, 15, 7, 4⟩, ⟨2, 15, 6, 6⟩, ⟨2, 15, 5, 8⟩, ⟨2, 15, 4, 10⟩, ⟨2, 15, 3, 12⟩, ⟨2, 15, 2, 14⟩, ⟨2, 15, 1, 16⟩, ⟨2, 15, 0, 18⟩]
  exact AllWinning.cons node_12062 (AllWinning.cons node_11013 (AllWinning.cons node_12123 (AllWinning.cons node_11125 (AllWinning.cons node_10062 (AllWinning.cons node_9088 (AllWinning.cons node_8109 (AllWinning.cons node_7157 (AllWinning.cons node_6232 (AllWinning.cons node_5482 (AllWinning.cons node_4758 (AllWinning.cons node_4067 (AllWinning.cons node_3497 (AllWinning.cons node_2953 (AllWinning.cons node_12125 (AllWinning.cons node_11130 (AllWinning.cons node_10070 (AllWinning.cons node_9103 (AllWinning.cons node_8130 (AllWinning.cons node_7185 (AllWinning.cons node_6264 (AllWinning.cons node_5512 (AllWinning.cons node_4808 (AllWinning.nil)))))))))))))))))))))))

theorem node_13115 : Outcome ⟨2, 15, 9, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 9, 2⟩, ⟨0, 15, 9, 4⟩, ⟨2, 14, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 12, 9, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 10, 9, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 8, 9, 14⟩, ⟨2, 7, 9, 16⟩, ⟨2, 6, 9, 18⟩, ⟨2, 5, 9, 20⟩, ⟨2, 4, 9, 22⟩, ⟨2, 3, 9, 24⟩, ⟨2, 2, 9, 26⟩, ⟨2, 1, 9, 28⟩, ⟨2, 15, 8, 2⟩, ⟨2, 15, 7, 4⟩, ⟨2, 15, 6, 6⟩, ⟨2, 15, 5, 8⟩, ⟨2, 15, 4, 10⟩, ⟨2, 15, 3, 12⟩, ⟨2, 15, 2, 14⟩, ⟨2, 15, 1, 16⟩, ⟨2, 15, 0, 18⟩]
  exact AllWinning.cons node_12062 (AllWinning.cons node_11013 (AllWinning.cons node_12123 (AllWinning.cons node_11125 (AllWinning.cons node_10062 (AllWinning.cons node_9088 (AllWinning.cons node_8109 (AllWinning.cons node_7157 (AllWinning.cons node_6232 (AllWinning.cons node_5482 (AllWinning.cons node_4758 (AllWinning.cons node_4067 (AllWinning.cons node_3497 (AllWinning.cons node_2953 (AllWinning.cons node_2490 (AllWinning.cons node_1990 (AllWinning.cons node_12125 (AllWinning.cons node_11130 (AllWinning.cons node_10070 (AllWinning.cons node_9103 (AllWinning.cons node_8130 (AllWinning.cons node_7185 (AllWinning.cons node_6264 (AllWinning.cons node_5512 (AllWinning.cons node_4808 (AllWinning.nil)))))))))))))))))))))))))

theorem node_13116 : Outcome ⟨2, 15, 9, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨1, 15, 9, 2⟩, ⟨0, 15, 9, 4⟩, ⟨2, 14, 9, 2⟩, ⟨2, 13, 9, 4⟩, ⟨2, 12, 9, 6⟩, ⟨2, 11, 9, 8⟩, ⟨2, 10, 9, 10⟩, ⟨2, 9, 9, 12⟩, ⟨2, 8, 9, 14⟩, ⟨2, 7, 9, 16⟩, ⟨2, 6, 9, 18⟩, ⟨2, 5, 9, 20⟩, ⟨2, 4, 9, 22⟩, ⟨2, 3, 9, 24⟩, ⟨2, 2, 9, 26⟩, ⟨2, 1, 9, 28⟩, ⟨2, 0, 9, 30⟩, ⟨2, 15, 8, 2⟩, ⟨2, 15, 7, 4⟩, ⟨2, 15, 6, 6⟩, ⟨2, 15, 5, 8⟩, ⟨2, 15, 4, 10⟩, ⟨2, 15, 3, 12⟩, ⟨2, 15, 2, 14⟩, ⟨2, 15, 1, 16⟩, ⟨2, 15, 0, 18⟩]
  exact AllWinning.cons node_12062 (AllWinning.cons node_11013 (AllWinning.cons node_12123 (AllWinning.cons node_11125 (AllWinning.cons node_10062 (AllWinning.cons node_9088 (AllWinning.cons node_8109 (AllWinning.cons node_7157 (AllWinning.cons node_6232 (AllWinning.cons node_5482 (AllWinning.cons node_4758 (AllWinning.cons node_4067 (AllWinning.cons node_3497 (AllWinning.cons node_2953 (AllWinning.cons node_2490 (AllWinning.cons node_1990 (AllWinning.cons node_1639 (AllWinning.cons node_12125 (AllWinning.cons node_11130 (AllWinning.cons node_10070 (AllWinning.cons node_9103 (AllWinning.cons node_8130 (AllWinning.cons node_7185 (AllWinning.cons node_6264 (AllWinning.cons node_5512 (AllWinning.cons node_4808 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13117 : Outcome ⟨2, 16, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 16, 8, 4⟩) (by decide) node_11016

theorem node_13118 : Outcome ⟨2, 16, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 8, 4⟩) (by decide) node_11016

theorem node_13119 : Outcome ⟨2, 16, 8, 6⟩ true :=
  Outcome.win (q := ⟨0, 16, 8, 4⟩) (by decide) node_11016

theorem node_13120 : Outcome ⟨2, 16, 8, 20⟩ true :=
  Outcome.win (q := ⟨0, 16, 8, 4⟩) (by decide) node_11016

theorem node_13121 : Outcome ⟨2, 17, 7, 2⟩ true :=
  Outcome.win (q := ⟨1, 17, 7, 2⟩) (by decide) node_12070

theorem node_13122 : Outcome ⟨2, 17, 7, 6⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 12⟩) (by decide) node_7193

theorem node_13123 : Outcome ⟨2, 17, 7, 8⟩ true :=
  Outcome.win (q := ⟨2, 17, 1, 12⟩) (by decide) node_7193

theorem node_13124 : Outcome ⟨2, 18, 6, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 6, 2⟩) (by decide) node_12133

theorem node_13125 : Outcome ⟨2, 18, 6, 16⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 14⟩) (by decide) node_6247

theorem node_13126 : Outcome ⟨2, 18, 6, 20⟩ true :=
  Outcome.win (q := ⟨2, 11, 6, 14⟩) (by decide) node_6247

theorem node_13127 : Outcome ⟨2, 19, 5, 2⟩ true :=
  Outcome.win (q := ⟨2, 19, 4, 2⟩) (by decide) node_12142

theorem node_13128 : Outcome ⟨2, 19, 5, 6⟩ true :=
  Outcome.win (q := ⟨2, 19, 4, 2⟩) (by decide) node_12142

theorem node_13129 : Outcome ⟨2, 19, 5, 16⟩ true :=
  Outcome.win (q := ⟨2, 10, 5, 18⟩) (by decide) node_4780

theorem node_13130 : Outcome ⟨2, 20, 4, 6⟩ true :=
  Outcome.win (q := ⟨2, 14, 4, 12⟩) (by decide) node_7180

theorem node_13131 : Outcome ⟨3, 4, 19, 2⟩ true :=
  Outcome.win (q := ⟨2, 4, 19, 2⟩) (by decide) node_12088

theorem node_13132 : Outcome ⟨3, 4, 19, 14⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 6⟩) (by decide) node_10091

theorem node_13133 : Outcome ⟨3, 4, 19, 22⟩ true :=
  Outcome.win (q := ⟨3, 1, 19, 6⟩) (by decide) node_10091

theorem node_13134 : Outcome ⟨3, 5, 18, 2⟩ true :=
  Outcome.win (q := ⟨3, 3, 18, 4⟩) (by decide) node_11155

theorem node_13135 : Outcome ⟨3, 5, 18, 4⟩ true :=
  Outcome.win (q := ⟨0, 5, 18, 6⟩) (by decide) node_9877

theorem node_13136 : Outcome ⟨3, 5, 18, 18⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 14⟩) (by decide) node_6305

theorem node_13137 : Outcome ⟨3, 5, 18, 20⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 14⟩) (by decide) node_6305

theorem node_13138 : Outcome ⟨3, 6, 17, 6⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13139 : Outcome ⟨3, 6, 17, 12⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13140 : Outcome ⟨3, 6, 17, 16⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 32⟩) (by decide) node_1365

theorem node_13141 : Outcome ⟨3, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨3, 5, 16, 4⟩) (by decide) node_11162

theorem node_13142 : Outcome ⟨3, 7, 16, 6⟩ true :=
  Outcome.win (q := ⟨3, 5, 16, 4⟩) (by decide) node_11162

theorem node_13143 : Outcome ⟨3, 7, 16, 16⟩ true :=
  Outcome.win (q := ⟨3, 7, 2, 28⟩) (by decide) node_2109

theorem node_13144 : Outcome ⟨3, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 2⟩) (by decide) node_12168

theorem node_13145 : Outcome ⟨3, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 2⟩) (by decide) node_12168

theorem node_13146 : Outcome ⟨3, 8, 15, 8⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 2⟩) (by decide) node_12168

theorem node_13147 : Outcome ⟨3, 8, 15, 20⟩ true :=
  Outcome.win (q := ⟨3, 7, 15, 2⟩) (by decide) node_12168

theorem node_13148 : Outcome ⟨3, 9, 14, 4⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13149 : Outcome ⟨3, 9, 14, 6⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13150 : Outcome ⟨3, 9, 14, 16⟩ true :=
  Outcome.win (q := ⟨3, 6, 14, 6⟩) (by decide) node_10111

theorem node_13151 : Outcome ⟨3, 10, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.nil)))))))))))

theorem node_13152 : Outcome ⟨3, 10, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 5, 13, 10⟩, ⟨3, 4, 13, 12⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩, ⟨3, 10, 8, 10⟩, ⟨3, 10, 7, 12⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_8167 (AllWinning.cons node_7215 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.cons node_8187 (AllWinning.cons node_7242 (AllWinning.nil)))))))))))))))

theorem node_13153 : Outcome ⟨3, 10, 13, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 5, 13, 10⟩, ⟨3, 4, 13, 12⟩, ⟨3, 3, 13, 14⟩, ⟨3, 2, 13, 16⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩, ⟨3, 10, 8, 10⟩, ⟨3, 10, 7, 12⟩, ⟨3, 10, 6, 14⟩, ⟨3, 10, 5, 16⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_8167 (AllWinning.cons node_7215 (AllWinning.cons node_6294 (AllWinning.cons node_5530 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.cons node_8187 (AllWinning.cons node_7242 (AllWinning.cons node_6329 (AllWinning.cons node_5559 (AllWinning.nil)))))))))))))))))))

theorem node_13154 : Outcome ⟨3, 10, 13, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 5, 13, 10⟩, ⟨3, 4, 13, 12⟩, ⟨3, 3, 13, 14⟩, ⟨3, 2, 13, 16⟩, ⟨3, 1, 13, 18⟩, ⟨3, 0, 13, 20⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩, ⟨3, 10, 8, 10⟩, ⟨3, 10, 7, 12⟩, ⟨3, 10, 6, 14⟩, ⟨3, 10, 5, 16⟩, ⟨3, 10, 4, 18⟩, ⟨3, 10, 3, 20⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_8167 (AllWinning.cons node_7215 (AllWinning.cons node_6294 (AllWinning.cons node_5530 (AllWinning.cons node_4818 (AllWinning.cons node_4100 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.cons node_8187 (AllWinning.cons node_7242 (AllWinning.cons node_6329 (AllWinning.cons node_5559 (AllWinning.cons node_4855 (AllWinning.cons node_4139 (AllWinning.nil)))))))))))))))))))))))

theorem node_13155 : Outcome ⟨3, 10, 13, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 5, 13, 10⟩, ⟨3, 4, 13, 12⟩, ⟨3, 3, 13, 14⟩, ⟨3, 2, 13, 16⟩, ⟨3, 1, 13, 18⟩, ⟨3, 0, 13, 20⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩, ⟨3, 10, 8, 10⟩, ⟨3, 10, 7, 12⟩, ⟨3, 10, 6, 14⟩, ⟨3, 10, 5, 16⟩, ⟨3, 10, 4, 18⟩, ⟨3, 10, 3, 20⟩, ⟨3, 10, 2, 22⟩, ⟨3, 10, 1, 24⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_8167 (AllWinning.cons node_7215 (AllWinning.cons node_6294 (AllWinning.cons node_5530 (AllWinning.cons node_4818 (AllWinning.cons node_4100 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.cons node_8187 (AllWinning.cons node_7242 (AllWinning.cons node_6329 (AllWinning.cons node_5559 (AllWinning.cons node_4855 (AllWinning.cons node_4139 (AllWinning.cons node_3576 (AllWinning.cons node_3039 (AllWinning.nil)))))))))))))))))))))))))

theorem node_13156 : Outcome ⟨3, 10, 13, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 5, 13, 10⟩, ⟨3, 4, 13, 12⟩, ⟨3, 3, 13, 14⟩, ⟨3, 2, 13, 16⟩, ⟨3, 1, 13, 18⟩, ⟨3, 0, 13, 20⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩, ⟨3, 10, 8, 10⟩, ⟨3, 10, 7, 12⟩, ⟨3, 10, 6, 14⟩, ⟨3, 10, 5, 16⟩, ⟨3, 10, 4, 18⟩, ⟨3, 10, 3, 20⟩, ⟨3, 10, 2, 22⟩, ⟨3, 10, 1, 24⟩, ⟨3, 10, 0, 26⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_8167 (AllWinning.cons node_7215 (AllWinning.cons node_6294 (AllWinning.cons node_5530 (AllWinning.cons node_4818 (AllWinning.cons node_4100 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.cons node_8187 (AllWinning.cons node_7242 (AllWinning.cons node_6329 (AllWinning.cons node_5559 (AllWinning.cons node_4855 (AllWinning.cons node_4139 (AllWinning.cons node_3576 (AllWinning.cons node_3039 (AllWinning.cons node_2577 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13157 : Outcome ⟨3, 10, 13, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 5, 13, 10⟩, ⟨3, 4, 13, 12⟩, ⟨3, 3, 13, 14⟩, ⟨3, 2, 13, 16⟩, ⟨3, 1, 13, 18⟩, ⟨3, 0, 13, 20⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩, ⟨3, 10, 8, 10⟩, ⟨3, 10, 7, 12⟩, ⟨3, 10, 6, 14⟩, ⟨3, 10, 5, 16⟩, ⟨3, 10, 4, 18⟩, ⟨3, 10, 3, 20⟩, ⟨3, 10, 2, 22⟩, ⟨3, 10, 1, 24⟩, ⟨3, 10, 0, 26⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_8167 (AllWinning.cons node_7215 (AllWinning.cons node_6294 (AllWinning.cons node_5530 (AllWinning.cons node_4818 (AllWinning.cons node_4100 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.cons node_8187 (AllWinning.cons node_7242 (AllWinning.cons node_6329 (AllWinning.cons node_5559 (AllWinning.cons node_4855 (AllWinning.cons node_4139 (AllWinning.cons node_3576 (AllWinning.cons node_3039 (AllWinning.cons node_2577 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13158 : Outcome ⟨3, 10, 13, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 10, 13, 2⟩, ⟨1, 10, 13, 4⟩, ⟨0, 10, 13, 6⟩, ⟨3, 9, 13, 2⟩, ⟨3, 8, 13, 4⟩, ⟨3, 7, 13, 6⟩, ⟨3, 6, 13, 8⟩, ⟨3, 5, 13, 10⟩, ⟨3, 4, 13, 12⟩, ⟨3, 3, 13, 14⟩, ⟨3, 2, 13, 16⟩, ⟨3, 1, 13, 18⟩, ⟨3, 0, 13, 20⟩, ⟨3, 10, 12, 2⟩, ⟨3, 10, 11, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 10, 9, 8⟩, ⟨3, 10, 8, 10⟩, ⟨3, 10, 7, 12⟩, ⟨3, 10, 6, 14⟩, ⟨3, 10, 5, 16⟩, ⟨3, 10, 4, 18⟩, ⟨3, 10, 3, 20⟩, ⟨3, 10, 2, 22⟩, ⟨3, 10, 1, 24⟩, ⟨3, 10, 0, 26⟩]
  exact AllWinning.cons node_12111 (AllWinning.cons node_11055 (AllWinning.cons node_9899 (AllWinning.cons node_12179 (AllWinning.cons node_11170 (AllWinning.cons node_10117 (AllWinning.cons node_9144 (AllWinning.cons node_8167 (AllWinning.cons node_7215 (AllWinning.cons node_6294 (AllWinning.cons node_5530 (AllWinning.cons node_4818 (AllWinning.cons node_4100 (AllWinning.cons node_12181 (AllWinning.cons node_11184 (AllWinning.cons node_10127 (AllWinning.cons node_9163 (AllWinning.cons node_8187 (AllWinning.cons node_7242 (AllWinning.cons node_6329 (AllWinning.cons node_5559 (AllWinning.cons node_4855 (AllWinning.cons node_4139 (AllWinning.cons node_3576 (AllWinning.cons node_3039 (AllWinning.cons node_2577 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13159 : Outcome ⟨3, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 4⟩) (by decide) node_11173

theorem node_13160 : Outcome ⟨3, 11, 12, 4⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 4⟩) (by decide) node_11173

theorem node_13161 : Outcome ⟨3, 11, 12, 6⟩ true :=
  Outcome.win (q := ⟨3, 9, 12, 4⟩) (by decide) node_11173

theorem node_13162 : Outcome ⟨3, 11, 12, 8⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 14⟩) (by decide) node_6336

theorem node_13163 : Outcome ⟨3, 11, 12, 14⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 14⟩) (by decide) node_6336

theorem node_13164 : Outcome ⟨3, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 4⟩) (by decide) node_11194

theorem node_13165 : Outcome ⟨3, 12, 11, 4⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 4⟩) (by decide) node_11194

theorem node_13166 : Outcome ⟨3, 12, 11, 6⟩ true :=
  Outcome.win (q := ⟨3, 12, 9, 4⟩) (by decide) node_11194

theorem node_13167 : Outcome ⟨3, 12, 11, 8⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 14⟩) (by decide) node_6305

theorem node_13168 : Outcome ⟨3, 12, 11, 14⟩ true :=
  Outcome.win (q := ⟨3, 5, 11, 14⟩) (by decide) node_6305

theorem node_13169 : Outcome ⟨3, 13, 10, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.nil)))))))))))

theorem node_13170 : Outcome ⟨3, 13, 10, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 8, 10, 10⟩, ⟨3, 7, 10, 12⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩, ⟨3, 13, 5, 10⟩, ⟨3, 13, 4, 12⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_8178 (AllWinning.cons node_7227 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.cons node_8200 (AllWinning.cons node_7250 (AllWinning.nil)))))))))))))))

theorem node_13171 : Outcome ⟨3, 13, 10, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 8, 10, 10⟩, ⟨3, 7, 10, 12⟩, ⟨3, 6, 10, 14⟩, ⟨3, 5, 10, 16⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩, ⟨3, 13, 5, 10⟩, ⟨3, 13, 4, 12⟩, ⟨3, 13, 3, 14⟩, ⟨3, 13, 2, 16⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_8178 (AllWinning.cons node_7227 (AllWinning.cons node_6312 (AllWinning.cons node_5536 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.cons node_8200 (AllWinning.cons node_7250 (AllWinning.cons node_6351 (AllWinning.cons node_5566 (AllWinning.nil)))))))))))))))))))

theorem node_13172 : Outcome ⟨3, 13, 10, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 8, 10, 10⟩, ⟨3, 7, 10, 12⟩, ⟨3, 6, 10, 14⟩, ⟨3, 5, 10, 16⟩, ⟨3, 4, 10, 18⟩, ⟨3, 3, 10, 20⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩, ⟨3, 13, 5, 10⟩, ⟨3, 13, 4, 12⟩, ⟨3, 13, 3, 14⟩, ⟨3, 13, 2, 16⟩, ⟨3, 13, 1, 18⟩, ⟨3, 13, 0, 20⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_8178 (AllWinning.cons node_7227 (AllWinning.cons node_6312 (AllWinning.cons node_5536 (AllWinning.cons node_4829 (AllWinning.cons node_4111 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.cons node_8200 (AllWinning.cons node_7250 (AllWinning.cons node_6351 (AllWinning.cons node_5566 (AllWinning.cons node_4867 (AllWinning.cons node_4149 (AllWinning.nil)))))))))))))))))))))))

theorem node_13173 : Outcome ⟨3, 13, 10, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 8, 10, 10⟩, ⟨3, 7, 10, 12⟩, ⟨3, 6, 10, 14⟩, ⟨3, 5, 10, 16⟩, ⟨3, 4, 10, 18⟩, ⟨3, 3, 10, 20⟩, ⟨3, 2, 10, 22⟩, ⟨3, 1, 10, 24⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩, ⟨3, 13, 5, 10⟩, ⟨3, 13, 4, 12⟩, ⟨3, 13, 3, 14⟩, ⟨3, 13, 2, 16⟩, ⟨3, 13, 1, 18⟩, ⟨3, 13, 0, 20⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_8178 (AllWinning.cons node_7227 (AllWinning.cons node_6312 (AllWinning.cons node_5536 (AllWinning.cons node_4829 (AllWinning.cons node_4111 (AllWinning.cons node_3546 (AllWinning.cons node_3000 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.cons node_8200 (AllWinning.cons node_7250 (AllWinning.cons node_6351 (AllWinning.cons node_5566 (AllWinning.cons node_4867 (AllWinning.cons node_4149 (AllWinning.nil)))))))))))))))))))))))))

theorem node_13174 : Outcome ⟨3, 13, 10, 14⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 8, 10, 10⟩, ⟨3, 7, 10, 12⟩, ⟨3, 6, 10, 14⟩, ⟨3, 5, 10, 16⟩, ⟨3, 4, 10, 18⟩, ⟨3, 3, 10, 20⟩, ⟨3, 2, 10, 22⟩, ⟨3, 1, 10, 24⟩, ⟨3, 0, 10, 26⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩, ⟨3, 13, 5, 10⟩, ⟨3, 13, 4, 12⟩, ⟨3, 13, 3, 14⟩, ⟨3, 13, 2, 16⟩, ⟨3, 13, 1, 18⟩, ⟨3, 13, 0, 20⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_8178 (AllWinning.cons node_7227 (AllWinning.cons node_6312 (AllWinning.cons node_5536 (AllWinning.cons node_4829 (AllWinning.cons node_4111 (AllWinning.cons node_3546 (AllWinning.cons node_3000 (AllWinning.cons node_2533 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.cons node_8200 (AllWinning.cons node_7250 (AllWinning.cons node_6351 (AllWinning.cons node_5566 (AllWinning.cons node_4867 (AllWinning.cons node_4149 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13175 : Outcome ⟨3, 13, 10, 16⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 8, 10, 10⟩, ⟨3, 7, 10, 12⟩, ⟨3, 6, 10, 14⟩, ⟨3, 5, 10, 16⟩, ⟨3, 4, 10, 18⟩, ⟨3, 3, 10, 20⟩, ⟨3, 2, 10, 22⟩, ⟨3, 1, 10, 24⟩, ⟨3, 0, 10, 26⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩, ⟨3, 13, 5, 10⟩, ⟨3, 13, 4, 12⟩, ⟨3, 13, 3, 14⟩, ⟨3, 13, 2, 16⟩, ⟨3, 13, 1, 18⟩, ⟨3, 13, 0, 20⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_8178 (AllWinning.cons node_7227 (AllWinning.cons node_6312 (AllWinning.cons node_5536 (AllWinning.cons node_4829 (AllWinning.cons node_4111 (AllWinning.cons node_3546 (AllWinning.cons node_3000 (AllWinning.cons node_2533 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.cons node_8200 (AllWinning.cons node_7250 (AllWinning.cons node_6351 (AllWinning.cons node_5566 (AllWinning.cons node_4867 (AllWinning.cons node_4149 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13176 : Outcome ⟨3, 13, 10, 18⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨2, 13, 10, 2⟩, ⟨1, 13, 10, 4⟩, ⟨0, 13, 10, 6⟩, ⟨3, 12, 10, 2⟩, ⟨3, 11, 10, 4⟩, ⟨3, 10, 10, 6⟩, ⟨3, 9, 10, 8⟩, ⟨3, 8, 10, 10⟩, ⟨3, 7, 10, 12⟩, ⟨3, 6, 10, 14⟩, ⟨3, 5, 10, 16⟩, ⟨3, 4, 10, 18⟩, ⟨3, 3, 10, 20⟩, ⟨3, 2, 10, 22⟩, ⟨3, 1, 10, 24⟩, ⟨3, 0, 10, 26⟩, ⟨3, 13, 9, 2⟩, ⟨3, 13, 8, 4⟩, ⟨3, 13, 7, 6⟩, ⟨3, 13, 6, 8⟩, ⟨3, 13, 5, 10⟩, ⟨3, 13, 4, 12⟩, ⟨3, 13, 3, 14⟩, ⟨3, 13, 2, 16⟩, ⟨3, 13, 1, 18⟩, ⟨3, 13, 0, 20⟩]
  exact AllWinning.cons node_12121 (AllWinning.cons node_11066 (AllWinning.cons node_9905 (AllWinning.cons node_12188 (AllWinning.cons node_11189 (AllWinning.cons node_10127 (AllWinning.cons node_9159 (AllWinning.cons node_8178 (AllWinning.cons node_7227 (AllWinning.cons node_6312 (AllWinning.cons node_5536 (AllWinning.cons node_4829 (AllWinning.cons node_4111 (AllWinning.cons node_3546 (AllWinning.cons node_3000 (AllWinning.cons node_2533 (AllWinning.cons node_12190 (AllWinning.cons node_11204 (AllWinning.cons node_10138 (AllWinning.cons node_9175 (AllWinning.cons node_8200 (AllWinning.cons node_7250 (AllWinning.cons node_6351 (AllWinning.cons node_5566 (AllWinning.cons node_4867 (AllWinning.cons node_4149 (AllWinning.nil))))))))))))))))))))))))))

theorem node_13177 : Outcome ⟨3, 14, 9, 4⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13178 : Outcome ⟨3, 14, 9, 6⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13179 : Outcome ⟨3, 14, 9, 16⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13180 : Outcome ⟨3, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 2⟩) (by decide) node_12195

theorem node_13181 : Outcome ⟨3, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 2⟩) (by decide) node_12195

theorem node_13182 : Outcome ⟨3, 15, 8, 8⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 2⟩) (by decide) node_12195

theorem node_13183 : Outcome ⟨3, 15, 8, 20⟩ true :=
  Outcome.win (q := ⟨3, 15, 7, 2⟩) (by decide) node_12195

theorem node_13184 : Outcome ⟨3, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 5, 4⟩) (by decide) node_11213

theorem node_13185 : Outcome ⟨3, 16, 7, 6⟩ true :=
  Outcome.win (q := ⟨3, 16, 5, 4⟩) (by decide) node_11213

theorem node_13186 : Outcome ⟨3, 16, 7, 16⟩ true :=
  Outcome.win (q := ⟨3, 2, 7, 28⟩) (by decide) node_2078

theorem node_13187 : Outcome ⟨3, 17, 6, 2⟩ true :=
  Outcome.win (q := ⟨2, 17, 6, 2⟩) (by decide) node_12133

theorem node_13188 : Outcome ⟨3, 17, 6, 6⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13189 : Outcome ⟨3, 17, 6, 12⟩ true :=
  Outcome.win (q := ⟨3, 14, 6, 6⟩) (by decide) node_10142

theorem node_13190 : Outcome ⟨3, 17, 6, 16⟩ true :=
  Outcome.win (q := ⟨3, 1, 6, 32⟩) (by decide) node_1334

theorem node_13191 : Outcome ⟨3, 18, 5, 2⟩ true :=
  Outcome.win (q := ⟨3, 16, 5, 4⟩) (by decide) node_11213

theorem node_13192 : Outcome ⟨3, 18, 5, 4⟩ true :=
  Outcome.win (q := ⟨0, 18, 5, 6⟩) (by decide) node_9923

theorem node_13193 : Outcome ⟨3, 18, 5, 18⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 14⟩) (by decide) node_6336

theorem node_13194 : Outcome ⟨3, 18, 5, 20⟩ true :=
  Outcome.win (q := ⟨3, 11, 5, 14⟩) (by decide) node_6336

theorem node_13195 : Outcome ⟨3, 19, 4, 2⟩ true :=
  Outcome.win (q := ⟨2, 19, 4, 2⟩) (by decide) node_12142

theorem node_13196 : Outcome ⟨3, 19, 4, 14⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 6⟩) (by decide) node_10162

theorem node_13197 : Outcome ⟨3, 19, 4, 22⟩ true :=
  Outcome.win (q := ⟨3, 19, 1, 6⟩) (by decide) node_10162

theorem node_13198 : Outcome ⟨4, 2, 20, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 12⟩) (by decide) node_7282

theorem node_13199 : Outcome ⟨4, 3, 19, 2⟩ true :=
  Outcome.win (q := ⟨4, 2, 19, 2⟩) (by decide) node_12223

theorem node_13200 : Outcome ⟨4, 3, 19, 14⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 6⟩) (by decide) node_9936

theorem node_13201 : Outcome ⟨4, 3, 19, 22⟩ true :=
  Outcome.win (q := ⟨1, 3, 19, 6⟩) (by decide) node_9936

theorem node_13202 : Outcome ⟨4, 4, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 18, 2⟩, ⟨2, 4, 18, 4⟩, ⟨4, 3, 18, 2⟩, ⟨4, 2, 18, 4⟩, ⟨4, 4, 17, 2⟩, ⟨4, 4, 16, 4⟩]
  exact AllWinning.cons node_12158 (AllWinning.cons node_11094 (AllWinning.cons node_12227 (AllWinning.cons node_11232 (AllWinning.cons node_12231 (AllWinning.cons node_11241 (AllWinning.nil))))))

theorem node_13203 : Outcome ⟨4, 4, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 4, 18, 2⟩, ⟨2, 4, 18, 4⟩, ⟨1, 4, 18, 6⟩, ⟨0, 4, 18, 8⟩, ⟨4, 3, 18, 2⟩, ⟨4, 2, 18, 4⟩, ⟨4, 1, 18, 6⟩, ⟨4, 0, 18, 8⟩, ⟨4, 4, 17, 2⟩, ⟨4, 4, 16, 4⟩, ⟨4, 4, 15, 6⟩, ⟨4, 4, 14, 8⟩]
  exact AllWinning.cons node_12158 (AllWinning.cons node_11094 (AllWinning.cons node_9943 (AllWinning.cons node_8912 (AllWinning.cons node_12227 (AllWinning.cons node_11232 (AllWinning.cons node_10172 (AllWinning.cons node_9197 (AllWinning.cons node_12231 (AllWinning.cons node_11241 (AllWinning.cons node_10185 (AllWinning.cons node_9213 (AllWinning.nil))))))))))))

theorem node_13204 : Outcome ⟨4, 4, 18, 14⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 10⟩) (by decide) node_8237

theorem node_13205 : Outcome ⟨4, 5, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 17, 2⟩, ⟨2, 5, 17, 4⟩, ⟨4, 4, 17, 2⟩, ⟨4, 3, 17, 4⟩, ⟨4, 5, 16, 2⟩, ⟨4, 5, 15, 4⟩]
  exact AllWinning.cons node_12161 (AllWinning.cons node_11099 (AllWinning.cons node_12231 (AllWinning.cons node_11237 (AllWinning.cons node_12233 (AllWinning.cons node_11244 (AllWinning.nil))))))

theorem node_13206 : Outcome ⟨4, 5, 17, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 5, 17, 2⟩, ⟨2, 5, 17, 4⟩, ⟨1, 5, 17, 6⟩, ⟨0, 5, 17, 8⟩, ⟨4, 4, 17, 2⟩, ⟨4, 3, 17, 4⟩, ⟨4, 2, 17, 6⟩, ⟨4, 1, 17, 8⟩, ⟨4, 5, 16, 2⟩, ⟨4, 5, 15, 4⟩, ⟨4, 5, 14, 6⟩, ⟨4, 5, 13, 8⟩]
  exact AllWinning.cons node_12161 (AllWinning.cons node_11099 (AllWinning.cons node_9948 (AllWinning.cons node_8916 (AllWinning.cons node_12231 (AllWinning.cons node_11237 (AllWinning.cons node_10177 (AllWinning.cons node_9202 (AllWinning.cons node_12233 (AllWinning.cons node_11244 (AllWinning.cons node_10187 (AllWinning.cons node_9216 (AllWinning.nil))))))))))))

theorem node_13207 : Outcome ⟨4, 5, 17, 6⟩ true :=
  Outcome.win (q := ⟨4, 0, 17, 10⟩) (by decide) node_8223

theorem node_13208 : Outcome ⟨4, 6, 16, 2⟩ true :=
  Outcome.win (q := ⟨4, 6, 15, 2⟩) (by decide) node_12236

theorem node_13209 : Outcome ⟨4, 6, 16, 6⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 12⟩) (by decide) node_7298

theorem node_13210 : Outcome ⟨4, 6, 16, 16⟩ true :=
  Outcome.win (q := ⟨4, 6, 10, 12⟩) (by decide) node_7298

theorem node_13211 : Outcome ⟨4, 7, 15, 16⟩ true :=
  Outcome.win (q := ⟨4, 7, 5, 20⟩) (by decide) node_4196

theorem node_13212 : Outcome ⟨4, 8, 14, 4⟩ true :=
  Outcome.win (q := ⟨4, 7, 14, 2⟩) (by decide) node_12239

theorem node_13213 : Outcome ⟨4, 8, 14, 6⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 12⟩) (by decide) node_7282

theorem node_13214 : Outcome ⟨4, 8, 14, 22⟩ true :=
  Outcome.win (q := ⟨4, 2, 14, 12⟩) (by decide) node_7282

theorem node_13215 : Outcome ⟨4, 9, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨3, 9, 13, 2⟩, ⟨2, 9, 13, 4⟩, ⟨4, 8, 13, 2⟩, ⟨4, 7, 13, 4⟩, ⟨4, 9, 12, 2⟩, ⟨4, 9, 11, 4⟩]
  exact AllWinning.cons node_12179 (AllWinning.cons node_11112 (AllWinning.cons node_12242 (AllWinning.cons node_11251 (AllWinning.cons node_12244 (AllWinning.cons node_11257 (AllWinning.nil))))))

theorem node_13216 : Outcome ⟨4, 9, 13, 6⟩ true :=
  Outcome.win (q := ⟨4, 4, 13, 10⟩) (by decide) node_8237

theorem node_13217 : Outcome ⟨4, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 2⟩) (by decide) node_12246

theorem node_13218 : Outcome ⟨4, 10, 12, 4⟩ true :=
  Outcome.win (q := ⟨4, 10, 11, 2⟩) (by decide) node_12246

end RQ9F1
