import Chunk41
set_option autoImplicit false
namespace RQ9F1

theorem node_9787 : Outcome ⟨15, 5, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 5, 2, 2⟩, ⟨13, 5, 2, 4⟩, ⟨12, 5, 2, 6⟩, ⟨11, 5, 2, 8⟩, ⟨15, 4, 2, 2⟩, ⟨15, 3, 2, 4⟩, ⟨15, 2, 2, 6⟩, ⟨15, 1, 2, 8⟩, ⟨15, 5, 1, 2⟩, ⟨15, 5, 0, 4⟩]
  exact AllWinning.cons node_8813 (AllWinning.cons node_7776 (AllWinning.cons node_6829 (AllWinning.cons node_5922 (AllWinning.cons node_8837 (AllWinning.cons node_7841 (AllWinning.cons node_6898 (AllWinning.cons node_6002 (AllWinning.cons node_8840 (AllWinning.cons node_7852 (AllWinning.nil))))))))))

theorem node_9788 : Outcome ⟨15, 5, 2, 8⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 10⟩) (by decide) node_5175

theorem node_9789 : Outcome ⟨15, 5, 2, 12⟩ true :=
  Outcome.win (q := ⟨10, 5, 2, 10⟩) (by decide) node_5175

theorem node_9790 : Outcome ⟨15, 6, 1, 2⟩ true :=
  Outcome.win (q := ⟨13, 6, 1, 4⟩) (by decide) node_7780

theorem node_9791 : Outcome ⟨15, 6, 1, 6⟩ true :=
  Outcome.win (q := ⟨13, 6, 1, 4⟩) (by decide) node_7780

theorem node_9792 : Outcome ⟨15, 6, 1, 10⟩ true :=
  Outcome.win (q := ⟨13, 6, 1, 4⟩) (by decide) node_7780

theorem node_9793 : Outcome ⟨15, 6, 1, 20⟩ true :=
  Outcome.win (q := ⟨3, 6, 1, 24⟩) (by decide) node_1361

theorem node_9794 : Outcome ⟨15, 7, 0, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 7, 0, 2⟩, ⟨13, 7, 0, 4⟩, ⟨15, 6, 0, 2⟩, ⟨15, 5, 0, 4⟩]
  exact AllWinning.cons node_8818 (AllWinning.cons node_7785 (AllWinning.cons node_8845 (AllWinning.cons node_7852 (AllWinning.nil))))

theorem node_9795 : Outcome ⟨15, 7, 0, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨14, 7, 0, 2⟩, ⟨13, 7, 0, 4⟩, ⟨12, 7, 0, 6⟩, ⟨11, 7, 0, 8⟩, ⟨15, 6, 0, 2⟩, ⟨15, 5, 0, 4⟩, ⟨15, 4, 0, 6⟩, ⟨15, 3, 0, 8⟩]
  exact AllWinning.cons node_8818 (AllWinning.cons node_7785 (AllWinning.cons node_6837 (AllWinning.cons node_5927 (AllWinning.cons node_8845 (AllWinning.cons node_7852 (AllWinning.cons node_6906 (AllWinning.cons node_6010 (AllWinning.nil))))))))

theorem node_9796 : Outcome ⟨15, 7, 0, 6⟩ true :=
  Outcome.win (q := ⟨15, 2, 0, 10⟩) (by decide) node_5295

theorem node_9797 : Outcome ⟨15, 7, 0, 16⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 16⟩) (by decide) node_3205

theorem node_9798 : Outcome ⟨15, 7, 0, 24⟩ true :=
  Outcome.win (q := ⟨7, 7, 0, 16⟩) (by decide) node_3205

theorem node_9799 : Outcome ⟨16, 0, 6, 2⟩ true :=
  Outcome.win (q := ⟨14, 0, 6, 4⟩) (by decide) node_7789

theorem node_9800 : Outcome ⟨16, 0, 6, 4⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 6⟩) (by decide) node_6910

theorem node_9801 : Outcome ⟨16, 0, 6, 6⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 6⟩) (by decide) node_6910

theorem node_9802 : Outcome ⟨16, 0, 6, 20⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 20⟩) (by decide) node_2200

theorem node_9803 : Outcome ⟨16, 0, 6, 24⟩ true :=
  Outcome.win (q := ⟨6, 0, 6, 20⟩) (by decide) node_2200

theorem node_9804 : Outcome ⟨16, 1, 5, 2⟩ true :=
  Outcome.win (q := ⟨14, 1, 5, 4⟩) (by decide) node_7794

theorem node_9805 : Outcome ⟨16, 1, 5, 4⟩ true :=
  Outcome.win (q := ⟨14, 1, 5, 4⟩) (by decide) node_7794

theorem node_9806 : Outcome ⟨16, 1, 5, 20⟩ true :=
  Outcome.win (q := ⟨9, 1, 5, 14⟩) (by decide) node_3801

theorem node_9807 : Outcome ⟨16, 2, 4, 4⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 4⟩) (by decide) node_7798

theorem node_9808 : Outcome ⟨16, 2, 4, 6⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 4⟩) (by decide) node_7798

theorem node_9809 : Outcome ⟨16, 2, 4, 12⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 4⟩) (by decide) node_7798

theorem node_9810 : Outcome ⟨16, 2, 4, 14⟩ true :=
  Outcome.win (q := ⟨14, 2, 4, 4⟩) (by decide) node_7798

theorem node_9811 : Outcome ⟨16, 2, 4, 28⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 30⟩) (by decide) node_518

theorem node_9812 : Outcome ⟨16, 3, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨15, 3, 3, 2⟩, ⟨14, 3, 3, 4⟩, ⟨16, 2, 3, 2⟩, ⟨16, 1, 3, 4⟩, ⟨16, 3, 2, 2⟩, ⟨16, 3, 1, 4⟩]
  exact AllWinning.cons node_8834 (AllWinning.cons node_7805 (AllWinning.cons node_8855 (AllWinning.cons node_7860 (AllWinning.cons node_8860 (AllWinning.cons node_7869 (AllWinning.nil))))))

theorem node_9813 : Outcome ⟨16, 3, 3, 4⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 6⟩) (by decide) node_6853

theorem node_9814 : Outcome ⟨16, 3, 3, 10⟩ true :=
  Outcome.win (q := ⟨13, 3, 3, 6⟩) (by decide) node_6853

theorem node_9815 : Outcome ⟨16, 4, 2, 4⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 4⟩) (by decide) node_7809

theorem node_9816 : Outcome ⟨16, 4, 2, 12⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 4⟩) (by decide) node_7809

theorem node_9817 : Outcome ⟨16, 4, 2, 14⟩ true :=
  Outcome.win (q := ⟨14, 4, 2, 4⟩) (by decide) node_7809

theorem node_9818 : Outcome ⟨16, 4, 2, 28⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 30⟩) (by decide) node_539

theorem node_9819 : Outcome ⟨16, 5, 1, 2⟩ true :=
  Outcome.win (q := ⟨14, 5, 1, 4⟩) (by decide) node_7817

theorem node_9820 : Outcome ⟨16, 5, 1, 4⟩ true :=
  Outcome.win (q := ⟨14, 5, 1, 4⟩) (by decide) node_7817

theorem node_9821 : Outcome ⟨16, 5, 1, 20⟩ true :=
  Outcome.win (q := ⟨9, 5, 1, 14⟩) (by decide) node_3829

theorem node_9822 : Outcome ⟨16, 6, 0, 2⟩ true :=
  Outcome.win (q := ⟨14, 6, 0, 4⟩) (by decide) node_7821

theorem node_9823 : Outcome ⟨16, 6, 0, 4⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 6⟩) (by decide) node_6926

theorem node_9824 : Outcome ⟨16, 6, 0, 6⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 6⟩) (by decide) node_6926

theorem node_9825 : Outcome ⟨16, 6, 0, 20⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 20⟩) (by decide) node_2234

theorem node_9826 : Outcome ⟨16, 6, 0, 24⟩ true :=
  Outcome.win (q := ⟨6, 6, 0, 20⟩) (by decide) node_2234

theorem node_9827 : Outcome ⟨17, 0, 5, 2⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 2⟩) (by decide) node_8871

theorem node_9828 : Outcome ⟨17, 0, 5, 8⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 2⟩) (by decide) node_8871

theorem node_9829 : Outcome ⟨17, 0, 5, 14⟩ true :=
  Outcome.win (q := ⟨5, 0, 5, 24⟩) (by decide) node_1415

theorem node_9830 : Outcome ⟨17, 1, 4, 2⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9831 : Outcome ⟨17, 1, 4, 4⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9832 : Outcome ⟨17, 1, 4, 6⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9833 : Outcome ⟨17, 1, 4, 8⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9834 : Outcome ⟨17, 1, 4, 14⟩ true :=
  Outcome.win (q := ⟨15, 1, 4, 4⟩) (by decide) node_7831

theorem node_9835 : Outcome ⟨17, 1, 4, 18⟩ true :=
  Outcome.win (q := ⟨2, 1, 4, 30⟩) (by decide) node_569

theorem node_9836 : Outcome ⟨17, 2, 3, 4⟩ true :=
  Outcome.win (q := ⟨17, 2, 1, 4⟩) (by decide) node_7887

theorem node_9837 : Outcome ⟨17, 2, 3, 6⟩ true :=
  Outcome.win (q := ⟨17, 2, 1, 4⟩) (by decide) node_7887

theorem node_9838 : Outcome ⟨17, 2, 3, 16⟩ true :=
  Outcome.win (q := ⟨7, 2, 3, 20⟩) (by decide) node_2258

theorem node_9839 : Outcome ⟨17, 3, 2, 4⟩ true :=
  Outcome.win (q := ⟨17, 1, 2, 4⟩) (by decide) node_7880

theorem node_9840 : Outcome ⟨17, 3, 2, 6⟩ true :=
  Outcome.win (q := ⟨17, 1, 2, 4⟩) (by decide) node_7880

theorem node_9841 : Outcome ⟨17, 3, 2, 16⟩ true :=
  Outcome.win (q := ⟨7, 3, 2, 20⟩) (by decide) node_2274

theorem node_9842 : Outcome ⟨17, 4, 1, 2⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9843 : Outcome ⟨17, 4, 1, 4⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9844 : Outcome ⟨17, 4, 1, 6⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9845 : Outcome ⟨17, 4, 1, 8⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9846 : Outcome ⟨17, 4, 1, 14⟩ true :=
  Outcome.win (q := ⟨15, 4, 1, 4⟩) (by decide) node_7846

theorem node_9847 : Outcome ⟨17, 4, 1, 18⟩ true :=
  Outcome.win (q := ⟨2, 4, 1, 30⟩) (by decide) node_591

theorem node_9848 : Outcome ⟨17, 5, 0, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 2⟩) (by decide) node_8886

theorem node_9849 : Outcome ⟨17, 5, 0, 8⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 2⟩) (by decide) node_8886

theorem node_9850 : Outcome ⟨17, 5, 0, 14⟩ true :=
  Outcome.win (q := ⟨5, 5, 0, 24⟩) (by decide) node_1449

theorem node_9851 : Outcome ⟨18, 0, 4, 2⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 2⟩) (by decide) node_8871

theorem node_9852 : Outcome ⟨18, 0, 4, 8⟩ true :=
  Outcome.win (q := ⟨17, 0, 4, 2⟩) (by decide) node_8871

theorem node_9853 : Outcome ⟨18, 1, 3, 2⟩ true :=
  Outcome.win (q := ⟨18, 1, 1, 4⟩) (by decide) node_7898

theorem node_9854 : Outcome ⟨18, 2, 2, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 2, 2, 2⟩, ⟨16, 2, 2, 4⟩, ⟨18, 1, 2, 2⟩, ⟨18, 0, 2, 4⟩, ⟨18, 2, 1, 2⟩, ⟨18, 2, 0, 4⟩]
  exact AllWinning.cons node_8880 (AllWinning.cons node_7866 (AllWinning.cons node_8893 (AllWinning.cons node_7894 (AllWinning.cons node_8896 (AllWinning.cons node_7899 (AllWinning.nil))))))

theorem node_9855 : Outcome ⟨18, 2, 2, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨17, 2, 2, 2⟩, ⟨16, 2, 2, 4⟩, ⟨15, 2, 2, 6⟩, ⟨14, 2, 2, 8⟩, ⟨18, 1, 2, 2⟩, ⟨18, 0, 2, 4⟩, ⟨18, 2, 1, 2⟩, ⟨18, 2, 0, 4⟩]
  exact AllWinning.cons node_8880 (AllWinning.cons node_7866 (AllWinning.cons node_6898 (AllWinning.cons node_5987 (AllWinning.cons node_8893 (AllWinning.cons node_7894 (AllWinning.cons node_8896 (AllWinning.cons node_7899 (AllWinning.nil))))))))

theorem node_9856 : Outcome ⟨18, 2, 2, 10⟩ true :=
  Outcome.win (q := ⟨13, 2, 2, 10⟩) (by decide) node_5251

theorem node_9857 : Outcome ⟨18, 3, 1, 2⟩ true :=
  Outcome.win (q := ⟨18, 1, 1, 4⟩) (by decide) node_7898

theorem node_9858 : Outcome ⟨18, 4, 0, 2⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 2⟩) (by decide) node_8886

theorem node_9859 : Outcome ⟨18, 4, 0, 8⟩ true :=
  Outcome.win (q := ⟨17, 4, 0, 2⟩) (by decide) node_8886

theorem node_9860 : Outcome ⟨19, 0, 3, 2⟩ true :=
  Outcome.win (q := ⟨19, 0, 1, 4⟩) (by decide) node_7902

theorem node_9861 : Outcome ⟨19, 0, 3, 6⟩ true :=
  Outcome.win (q := ⟨16, 0, 3, 6⟩) (by decide) node_6910

theorem node_9862 : Outcome ⟨19, 0, 3, 32⟩ true :=
  Outcome.win (q := ⟨3, 0, 3, 32⟩) (by decide) node_417

theorem node_9863 : Outcome ⟨19, 1, 2, 2⟩ true :=
  Outcome.win (q := ⟨17, 1, 2, 4⟩) (by decide) node_7880

theorem node_9864 : Outcome ⟨19, 1, 2, 14⟩ true :=
  Outcome.win (q := ⟨17, 1, 2, 4⟩) (by decide) node_7880

theorem node_9865 : Outcome ⟨19, 2, 1, 2⟩ true :=
  Outcome.win (q := ⟨17, 2, 1, 4⟩) (by decide) node_7887

theorem node_9866 : Outcome ⟨19, 2, 1, 6⟩ true :=
  Outcome.win (q := ⟨17, 2, 1, 4⟩) (by decide) node_7887

theorem node_9867 : Outcome ⟨19, 2, 1, 14⟩ true :=
  Outcome.win (q := ⟨17, 2, 1, 4⟩) (by decide) node_7887

theorem node_9868 : Outcome ⟨19, 3, 0, 2⟩ true :=
  Outcome.win (q := ⟨19, 1, 0, 4⟩) (by decide) node_7905

theorem node_9869 : Outcome ⟨19, 3, 0, 6⟩ true :=
  Outcome.win (q := ⟨16, 3, 0, 6⟩) (by decide) node_6926

theorem node_9870 : Outcome ⟨19, 3, 0, 32⟩ true :=
  Outcome.win (q := ⟨3, 3, 0, 32⟩) (by decide) node_440

theorem node_9871 : Outcome ⟨0, 3, 20, 4⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 8⟩) (by decide) node_6045

theorem node_9872 : Outcome ⟨0, 3, 20, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 8⟩) (by decide) node_6045

theorem node_9873 : Outcome ⟨0, 4, 19, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 4⟩) (by decide) node_7917

theorem node_9874 : Outcome ⟨0, 4, 19, 28⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 30⟩) (by decide) node_713

theorem node_9875 : Outcome ⟨0, 5, 18, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 18, 2⟩, ⟨0, 3, 18, 4⟩, ⟨0, 5, 17, 2⟩, ⟨0, 5, 16, 4⟩]
  exact AllWinning.cons node_8911 (AllWinning.cons node_7913 (AllWinning.cons node_8915 (AllWinning.cons node_7922 (AllWinning.nil))))

theorem node_9876 : Outcome ⟨0, 5, 18, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 18, 2⟩, ⟨0, 3, 18, 4⟩, ⟨0, 2, 18, 6⟩, ⟨0, 1, 18, 8⟩, ⟨0, 5, 17, 2⟩, ⟨0, 5, 16, 4⟩, ⟨0, 5, 15, 6⟩, ⟨0, 5, 14, 8⟩]
  exact AllWinning.cons node_8911 (AllWinning.cons node_7913 (AllWinning.cons node_6952 (AllWinning.cons node_6038 (AllWinning.cons node_8915 (AllWinning.cons node_7922 (AllWinning.cons node_6962 (AllWinning.cons node_6055 (AllWinning.nil))))))))

theorem node_9877 : Outcome ⟨0, 5, 18, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 18, 2⟩, ⟨0, 3, 18, 4⟩, ⟨0, 2, 18, 6⟩, ⟨0, 1, 18, 8⟩, ⟨0, 0, 18, 10⟩, ⟨0, 5, 17, 2⟩, ⟨0, 5, 16, 4⟩, ⟨0, 5, 15, 6⟩, ⟨0, 5, 14, 8⟩, ⟨0, 5, 13, 10⟩, ⟨0, 5, 12, 12⟩]
  exact AllWinning.cons node_8911 (AllWinning.cons node_7913 (AllWinning.cons node_6952 (AllWinning.cons node_6038 (AllWinning.cons node_5312 (AllWinning.cons node_8915 (AllWinning.cons node_7922 (AllWinning.cons node_6962 (AllWinning.cons node_6055 (AllWinning.cons node_5331 (AllWinning.cons node_4594 (AllWinning.nil)))))))))))

theorem node_9878 : Outcome ⟨0, 5, 18, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 18, 2⟩, ⟨0, 3, 18, 4⟩, ⟨0, 2, 18, 6⟩, ⟨0, 1, 18, 8⟩, ⟨0, 0, 18, 10⟩, ⟨0, 5, 17, 2⟩, ⟨0, 5, 16, 4⟩, ⟨0, 5, 15, 6⟩, ⟨0, 5, 14, 8⟩, ⟨0, 5, 13, 10⟩, ⟨0, 5, 12, 12⟩, ⟨0, 5, 11, 14⟩, ⟨0, 5, 10, 16⟩]
  exact AllWinning.cons node_8911 (AllWinning.cons node_7913 (AllWinning.cons node_6952 (AllWinning.cons node_6038 (AllWinning.cons node_5312 (AllWinning.cons node_8915 (AllWinning.cons node_7922 (AllWinning.cons node_6962 (AllWinning.cons node_6055 (AllWinning.cons node_5331 (AllWinning.cons node_4594 (AllWinning.cons node_3951 (AllWinning.cons node_3343 (AllWinning.nil)))))))))))))

theorem node_9879 : Outcome ⟨0, 5, 18, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 18, 2⟩, ⟨0, 3, 18, 4⟩, ⟨0, 2, 18, 6⟩, ⟨0, 1, 18, 8⟩, ⟨0, 0, 18, 10⟩, ⟨0, 5, 17, 2⟩, ⟨0, 5, 16, 4⟩, ⟨0, 5, 15, 6⟩, ⟨0, 5, 14, 8⟩, ⟨0, 5, 13, 10⟩, ⟨0, 5, 12, 12⟩, ⟨0, 5, 11, 14⟩, ⟨0, 5, 10, 16⟩, ⟨0, 5, 9, 18⟩, ⟨0, 5, 8, 20⟩]
  exact AllWinning.cons node_8911 (AllWinning.cons node_7913 (AllWinning.cons node_6952 (AllWinning.cons node_6038 (AllWinning.cons node_5312 (AllWinning.cons node_8915 (AllWinning.cons node_7922 (AllWinning.cons node_6962 (AllWinning.cons node_6055 (AllWinning.cons node_5331 (AllWinning.cons node_4594 (AllWinning.cons node_3951 (AllWinning.cons node_3343 (AllWinning.cons node_2845 (AllWinning.cons node_2391 (AllWinning.nil)))))))))))))))

theorem node_9880 : Outcome ⟨0, 5, 18, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 4, 18, 2⟩, ⟨0, 3, 18, 4⟩, ⟨0, 2, 18, 6⟩, ⟨0, 1, 18, 8⟩, ⟨0, 0, 18, 10⟩, ⟨0, 5, 17, 2⟩, ⟨0, 5, 16, 4⟩, ⟨0, 5, 15, 6⟩, ⟨0, 5, 14, 8⟩, ⟨0, 5, 13, 10⟩, ⟨0, 5, 12, 12⟩, ⟨0, 5, 11, 14⟩, ⟨0, 5, 10, 16⟩, ⟨0, 5, 9, 18⟩, ⟨0, 5, 8, 20⟩, ⟨0, 5, 7, 22⟩, ⟨0, 5, 6, 24⟩]
  exact AllWinning.cons node_8911 (AllWinning.cons node_7913 (AllWinning.cons node_6952 (AllWinning.cons node_6038 (AllWinning.cons node_5312 (AllWinning.cons node_8915 (AllWinning.cons node_7922 (AllWinning.cons node_6962 (AllWinning.cons node_6055 (AllWinning.cons node_5331 (AllWinning.cons node_4594 (AllWinning.cons node_3951 (AllWinning.cons node_3343 (AllWinning.cons node_2845 (AllWinning.cons node_2391 (AllWinning.cons node_1888 (AllWinning.cons node_1568 (AllWinning.nil)))))))))))))))))

theorem node_9881 : Outcome ⟨0, 5, 18, 24⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 26⟩) (by decide) node_1183

theorem node_9882 : Outcome ⟨0, 5, 18, 26⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 26⟩) (by decide) node_1183

theorem node_9883 : Outcome ⟨0, 6, 17, 4⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 4⟩) (by decide) node_7917

theorem node_9884 : Outcome ⟨0, 6, 17, 6⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 4⟩) (by decide) node_7917

theorem node_9885 : Outcome ⟨0, 6, 17, 18⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 22⟩) (by decide) node_1899

theorem node_9886 : Outcome ⟨0, 7, 16, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 15, 2⟩) (by decide) node_8923

theorem node_9887 : Outcome ⟨0, 7, 16, 8⟩ true :=
  Outcome.win (q := ⟨0, 3, 16, 8⟩) (by decide) node_6045

theorem node_9888 : Outcome ⟨0, 7, 16, 18⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 18⟩) (by decide) node_2857

theorem node_9889 : Outcome ⟨0, 7, 16, 22⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 18⟩) (by decide) node_2857

theorem node_9890 : Outcome ⟨0, 8, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 8, 13, 4⟩) (by decide) node_7935

theorem node_9891 : Outcome ⟨0, 8, 15, 4⟩ true :=
  Outcome.win (q := ⟨0, 8, 13, 4⟩) (by decide) node_7935

theorem node_9892 : Outcome ⟨0, 8, 15, 10⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 14⟩) (by decide) node_3964

theorem node_9893 : Outcome ⟨0, 8, 15, 14⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 14⟩) (by decide) node_3964

theorem node_9894 : Outcome ⟨0, 9, 14, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 14, 2⟩, ⟨0, 7, 14, 4⟩, ⟨0, 9, 13, 2⟩, ⟨0, 9, 12, 4⟩]
  exact AllWinning.cons node_8929 (AllWinning.cons node_7930 (AllWinning.cons node_8932 (AllWinning.cons node_7938 (AllWinning.nil))))

theorem node_9895 : Outcome ⟨0, 9, 14, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 8, 14, 2⟩, ⟨0, 7, 14, 4⟩, ⟨0, 6, 14, 6⟩, ⟨0, 5, 14, 8⟩, ⟨0, 9, 13, 2⟩, ⟨0, 9, 12, 4⟩, ⟨0, 9, 11, 6⟩, ⟨0, 9, 10, 8⟩]
  exact AllWinning.cons node_8929 (AllWinning.cons node_7930 (AllWinning.cons node_6967 (AllWinning.cons node_6055 (AllWinning.cons node_8932 (AllWinning.cons node_7938 (AllWinning.cons node_6979 (AllWinning.cons node_6074 (AllWinning.nil))))))))

theorem node_9896 : Outcome ⟨0, 9, 14, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 10⟩) (by decide) node_5348

theorem node_9897 : Outcome ⟨0, 9, 14, 10⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 10⟩) (by decide) node_5348

theorem node_9898 : Outcome ⟨0, 10, 13, 4⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 6⟩) (by decide) node_6982

theorem node_9899 : Outcome ⟨0, 10, 13, 6⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 6⟩) (by decide) node_6982

theorem node_9900 : Outcome ⟨0, 11, 12, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 2⟩) (by decide) node_8938

theorem node_9901 : Outcome ⟨0, 11, 12, 8⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 2⟩) (by decide) node_8938

theorem node_9902 : Outcome ⟨0, 12, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 2⟩) (by decide) node_8938

theorem node_9903 : Outcome ⟨0, 12, 11, 8⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 2⟩) (by decide) node_8938

theorem node_9904 : Outcome ⟨0, 13, 10, 4⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 6⟩) (by decide) node_6982

theorem node_9905 : Outcome ⟨0, 13, 10, 6⟩ true :=
  Outcome.win (q := ⟨0, 10, 10, 6⟩) (by decide) node_6982

theorem node_9906 : Outcome ⟨0, 14, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 9, 2⟩, ⟨0, 12, 9, 4⟩, ⟨0, 14, 8, 2⟩, ⟨0, 14, 7, 4⟩]
  exact AllWinning.cons node_8950 (AllWinning.cons node_7947 (AllWinning.cons node_8953 (AllWinning.cons node_7953 (AllWinning.nil))))

theorem node_9907 : Outcome ⟨0, 14, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 9, 2⟩, ⟨0, 12, 9, 4⟩, ⟨0, 11, 9, 6⟩, ⟨0, 10, 9, 8⟩, ⟨0, 14, 8, 2⟩, ⟨0, 14, 7, 4⟩, ⟨0, 14, 6, 6⟩, ⟨0, 14, 5, 8⟩]
  exact AllWinning.cons node_8950 (AllWinning.cons node_7947 (AllWinning.cons node_6993 (AllWinning.cons node_6077 (AllWinning.cons node_8953 (AllWinning.cons node_7953 (AllWinning.cons node_7003 (AllWinning.cons node_6094 (AllWinning.nil))))))))

theorem node_9908 : Outcome ⟨0, 14, 9, 6⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 10⟩) (by decide) node_5348

theorem node_9909 : Outcome ⟨0, 14, 9, 10⟩ true :=
  Outcome.win (q := ⟨0, 9, 9, 10⟩) (by decide) node_5348

theorem node_9910 : Outcome ⟨0, 15, 8, 2⟩ true :=
  Outcome.win (q := ⟨0, 13, 8, 4⟩) (by decide) node_7949

theorem node_9911 : Outcome ⟨0, 15, 8, 4⟩ true :=
  Outcome.win (q := ⟨0, 13, 8, 4⟩) (by decide) node_7949

theorem node_9912 : Outcome ⟨0, 15, 8, 10⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 14⟩) (by decide) node_3964

theorem node_9913 : Outcome ⟨0, 15, 8, 14⟩ true :=
  Outcome.win (q := ⟨0, 8, 8, 14⟩) (by decide) node_3964

theorem node_9914 : Outcome ⟨0, 16, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 7, 2⟩) (by decide) node_8956

theorem node_9915 : Outcome ⟨0, 16, 7, 8⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 8⟩) (by decide) node_6103

theorem node_9916 : Outcome ⟨0, 16, 7, 18⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 18⟩) (by decide) node_2857

theorem node_9917 : Outcome ⟨0, 16, 7, 22⟩ true :=
  Outcome.win (q := ⟨0, 7, 7, 18⟩) (by decide) node_2857

theorem node_9918 : Outcome ⟨0, 17, 6, 4⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 4⟩) (by decide) node_7965

theorem node_9919 : Outcome ⟨0, 17, 6, 6⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 4⟩) (by decide) node_7965

theorem node_9920 : Outcome ⟨0, 17, 6, 18⟩ true :=
  Outcome.win (q := ⟨0, 6, 6, 22⟩) (by decide) node_1899

theorem node_9921 : Outcome ⟨0, 18, 5, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 5, 2⟩, ⟨0, 16, 5, 4⟩, ⟨0, 18, 4, 2⟩, ⟨0, 18, 3, 4⟩]
  exact AllWinning.cons node_8967 (AllWinning.cons node_7961 (AllWinning.cons node_8970 (AllWinning.cons node_7970 (AllWinning.nil))))

theorem node_9922 : Outcome ⟨0, 18, 5, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 5, 2⟩, ⟨0, 16, 5, 4⟩, ⟨0, 15, 5, 6⟩, ⟨0, 14, 5, 8⟩, ⟨0, 18, 4, 2⟩, ⟨0, 18, 3, 4⟩, ⟨0, 18, 2, 6⟩, ⟨0, 18, 1, 8⟩]
  exact AllWinning.cons node_8967 (AllWinning.cons node_7961 (AllWinning.cons node_7008 (AllWinning.cons node_6094 (AllWinning.cons node_8970 (AllWinning.cons node_7970 (AllWinning.cons node_7018 (AllWinning.cons node_6112 (AllWinning.nil))))))))

theorem node_9923 : Outcome ⟨0, 18, 5, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 5, 2⟩, ⟨0, 16, 5, 4⟩, ⟨0, 15, 5, 6⟩, ⟨0, 14, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨0, 12, 5, 12⟩, ⟨0, 18, 4, 2⟩, ⟨0, 18, 3, 4⟩, ⟨0, 18, 2, 6⟩, ⟨0, 18, 1, 8⟩, ⟨0, 18, 0, 10⟩]
  exact AllWinning.cons node_8967 (AllWinning.cons node_7961 (AllWinning.cons node_7008 (AllWinning.cons node_6094 (AllWinning.cons node_5369 (AllWinning.cons node_4623 (AllWinning.cons node_8970 (AllWinning.cons node_7970 (AllWinning.cons node_7018 (AllWinning.cons node_6112 (AllWinning.cons node_5388 (AllWinning.nil)))))))))))

theorem node_9924 : Outcome ⟨0, 18, 5, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 5, 2⟩, ⟨0, 16, 5, 4⟩, ⟨0, 15, 5, 6⟩, ⟨0, 14, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨0, 12, 5, 12⟩, ⟨0, 11, 5, 14⟩, ⟨0, 10, 5, 16⟩, ⟨0, 18, 4, 2⟩, ⟨0, 18, 3, 4⟩, ⟨0, 18, 2, 6⟩, ⟨0, 18, 1, 8⟩, ⟨0, 18, 0, 10⟩]
  exact AllWinning.cons node_8967 (AllWinning.cons node_7961 (AllWinning.cons node_7008 (AllWinning.cons node_6094 (AllWinning.cons node_5369 (AllWinning.cons node_4623 (AllWinning.cons node_3981 (AllWinning.cons node_3362 (AllWinning.cons node_8970 (AllWinning.cons node_7970 (AllWinning.cons node_7018 (AllWinning.cons node_6112 (AllWinning.cons node_5388 (AllWinning.nil)))))))))))))

theorem node_9925 : Outcome ⟨0, 18, 5, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 5, 2⟩, ⟨0, 16, 5, 4⟩, ⟨0, 15, 5, 6⟩, ⟨0, 14, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨0, 12, 5, 12⟩, ⟨0, 11, 5, 14⟩, ⟨0, 10, 5, 16⟩, ⟨0, 9, 5, 18⟩, ⟨0, 8, 5, 20⟩, ⟨0, 18, 4, 2⟩, ⟨0, 18, 3, 4⟩, ⟨0, 18, 2, 6⟩, ⟨0, 18, 1, 8⟩, ⟨0, 18, 0, 10⟩]
  exact AllWinning.cons node_8967 (AllWinning.cons node_7961 (AllWinning.cons node_7008 (AllWinning.cons node_6094 (AllWinning.cons node_5369 (AllWinning.cons node_4623 (AllWinning.cons node_3981 (AllWinning.cons node_3362 (AllWinning.cons node_2867 (AllWinning.cons node_2403 (AllWinning.cons node_8970 (AllWinning.cons node_7970 (AllWinning.cons node_7018 (AllWinning.cons node_6112 (AllWinning.cons node_5388 (AllWinning.nil)))))))))))))))

theorem node_9926 : Outcome ⟨0, 18, 5, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 17, 5, 2⟩, ⟨0, 16, 5, 4⟩, ⟨0, 15, 5, 6⟩, ⟨0, 14, 5, 8⟩, ⟨0, 13, 5, 10⟩, ⟨0, 12, 5, 12⟩, ⟨0, 11, 5, 14⟩, ⟨0, 10, 5, 16⟩, ⟨0, 9, 5, 18⟩, ⟨0, 8, 5, 20⟩, ⟨0, 7, 5, 22⟩, ⟨0, 6, 5, 24⟩, ⟨0, 18, 4, 2⟩, ⟨0, 18, 3, 4⟩, ⟨0, 18, 2, 6⟩, ⟨0, 18, 1, 8⟩, ⟨0, 18, 0, 10⟩]
  exact AllWinning.cons node_8967 (AllWinning.cons node_7961 (AllWinning.cons node_7008 (AllWinning.cons node_6094 (AllWinning.cons node_5369 (AllWinning.cons node_4623 (AllWinning.cons node_3981 (AllWinning.cons node_3362 (AllWinning.cons node_2867 (AllWinning.cons node_2403 (AllWinning.cons node_1906 (AllWinning.cons node_1571 (AllWinning.cons node_8970 (AllWinning.cons node_7970 (AllWinning.cons node_7018 (AllWinning.cons node_6112 (AllWinning.cons node_5388 (AllWinning.nil)))))))))))))))))

theorem node_9927 : Outcome ⟨0, 18, 5, 24⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 26⟩) (by decide) node_1183

theorem node_9928 : Outcome ⟨0, 18, 5, 26⟩ true :=
  Outcome.win (q := ⟨0, 5, 5, 26⟩) (by decide) node_1183

theorem node_9929 : Outcome ⟨0, 19, 4, 4⟩ true :=
  Outcome.win (q := ⟨0, 17, 4, 4⟩) (by decide) node_7965

theorem node_9930 : Outcome ⟨0, 19, 4, 28⟩ true :=
  Outcome.win (q := ⟨0, 4, 4, 30⟩) (by decide) node_713

theorem node_9931 : Outcome ⟨0, 20, 3, 4⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 8⟩) (by decide) node_6103

theorem node_9932 : Outcome ⟨0, 20, 3, 8⟩ true :=
  Outcome.win (q := ⟨0, 16, 3, 8⟩) (by decide) node_6103

theorem node_9933 : Outcome ⟨1, 2, 20, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 6⟩) (by decide) node_7035

theorem node_9934 : Outcome ⟨1, 3, 19, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 19, 2⟩, ⟨1, 2, 19, 2⟩, ⟨1, 1, 19, 4⟩, ⟨1, 3, 18, 2⟩, ⟨1, 3, 17, 4⟩]
  exact AllWinning.cons node_8908 (AllWinning.cons node_8981 (AllWinning.cons node_7981 (AllWinning.cons node_8985 (AllWinning.cons node_7985 (AllWinning.nil)))))

theorem node_9935 : Outcome ⟨1, 3, 19, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 19, 2⟩, ⟨1, 2, 19, 2⟩, ⟨1, 1, 19, 4⟩, ⟨1, 0, 19, 6⟩, ⟨1, 3, 18, 2⟩, ⟨1, 3, 17, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 3, 15, 8⟩]
  exact AllWinning.cons node_8908 (AllWinning.cons node_8981 (AllWinning.cons node_7981 (AllWinning.cons node_7029 (AllWinning.cons node_8985 (AllWinning.cons node_7985 (AllWinning.cons node_7041 (AllWinning.cons node_6124 (AllWinning.nil))))))))

theorem node_9936 : Outcome ⟨1, 3, 19, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 19, 2⟩, ⟨1, 2, 19, 2⟩, ⟨1, 1, 19, 4⟩, ⟨1, 0, 19, 6⟩, ⟨1, 3, 18, 2⟩, ⟨1, 3, 17, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 3, 15, 8⟩, ⟨1, 3, 14, 10⟩, ⟨1, 3, 13, 12⟩]
  exact AllWinning.cons node_8908 (AllWinning.cons node_8981 (AllWinning.cons node_7981 (AllWinning.cons node_7029 (AllWinning.cons node_8985 (AllWinning.cons node_7985 (AllWinning.cons node_7041 (AllWinning.cons node_6124 (AllWinning.cons node_5402 (AllWinning.cons node_4663 (AllWinning.nil))))))))))

theorem node_9937 : Outcome ⟨1, 3, 19, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 19, 2⟩, ⟨1, 2, 19, 2⟩, ⟨1, 1, 19, 4⟩, ⟨1, 0, 19, 6⟩, ⟨1, 3, 18, 2⟩, ⟨1, 3, 17, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 3, 15, 8⟩, ⟨1, 3, 14, 10⟩, ⟨1, 3, 13, 12⟩, ⟨1, 3, 12, 14⟩, ⟨1, 3, 11, 16⟩]
  exact AllWinning.cons node_8908 (AllWinning.cons node_8981 (AllWinning.cons node_7981 (AllWinning.cons node_7029 (AllWinning.cons node_8985 (AllWinning.cons node_7985 (AllWinning.cons node_7041 (AllWinning.cons node_6124 (AllWinning.cons node_5402 (AllWinning.cons node_4663 (AllWinning.cons node_4011 (AllWinning.cons node_3406 (AllWinning.nil))))))))))))

theorem node_9938 : Outcome ⟨1, 3, 19, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 19, 2⟩, ⟨1, 2, 19, 2⟩, ⟨1, 1, 19, 4⟩, ⟨1, 0, 19, 6⟩, ⟨1, 3, 18, 2⟩, ⟨1, 3, 17, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 3, 15, 8⟩, ⟨1, 3, 14, 10⟩, ⟨1, 3, 13, 12⟩, ⟨1, 3, 12, 14⟩, ⟨1, 3, 11, 16⟩, ⟨1, 3, 10, 18⟩, ⟨1, 3, 9, 20⟩]
  exact AllWinning.cons node_8908 (AllWinning.cons node_8981 (AllWinning.cons node_7981 (AllWinning.cons node_7029 (AllWinning.cons node_8985 (AllWinning.cons node_7985 (AllWinning.cons node_7041 (AllWinning.cons node_6124 (AllWinning.cons node_5402 (AllWinning.cons node_4663 (AllWinning.cons node_4011 (AllWinning.cons node_3406 (AllWinning.cons node_2900 (AllWinning.cons node_2445 (AllWinning.nil))))))))))))))

theorem node_9939 : Outcome ⟨1, 3, 19, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 3, 19, 2⟩, ⟨1, 2, 19, 2⟩, ⟨1, 1, 19, 4⟩, ⟨1, 0, 19, 6⟩, ⟨1, 3, 18, 2⟩, ⟨1, 3, 17, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 3, 15, 8⟩, ⟨1, 3, 14, 10⟩, ⟨1, 3, 13, 12⟩, ⟨1, 3, 12, 14⟩, ⟨1, 3, 11, 16⟩, ⟨1, 3, 10, 18⟩, ⟨1, 3, 9, 20⟩, ⟨1, 3, 8, 22⟩, ⟨1, 3, 7, 24⟩]
  exact AllWinning.cons node_8908 (AllWinning.cons node_8981 (AllWinning.cons node_7981 (AllWinning.cons node_7029 (AllWinning.cons node_8985 (AllWinning.cons node_7985 (AllWinning.cons node_7041 (AllWinning.cons node_6124 (AllWinning.cons node_5402 (AllWinning.cons node_4663 (AllWinning.cons node_4011 (AllWinning.cons node_3406 (AllWinning.cons node_2900 (AllWinning.cons node_2445 (AllWinning.cons node_1944 (AllWinning.cons node_1609 (AllWinning.nil))))))))))))))))

theorem node_9940 : Outcome ⟨1, 3, 19, 18⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 26⟩) (by decide) node_1231

theorem node_9941 : Outcome ⟨1, 3, 19, 20⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 26⟩) (by decide) node_1231

theorem node_9942 : Outcome ⟨1, 4, 18, 4⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 6⟩) (by decide) node_7047

theorem node_9943 : Outcome ⟨1, 4, 18, 6⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 6⟩) (by decide) node_7047

theorem node_9944 : Outcome ⟨1, 4, 18, 8⟩ true :=
  Outcome.win (q := ⟨1, 4, 15, 6⟩) (by decide) node_7047

theorem node_9945 : Outcome ⟨1, 4, 18, 20⟩ true :=
  Outcome.win (q := ⟨1, 4, 2, 32⟩) (by decide) node_540

theorem node_9946 : Outcome ⟨1, 5, 17, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 5, 17, 2⟩, ⟨1, 4, 17, 2⟩, ⟨1, 3, 17, 4⟩, ⟨1, 5, 16, 2⟩, ⟨1, 5, 15, 4⟩]
  exact AllWinning.cons node_8915 (AllWinning.cons node_8988 (AllWinning.cons node_7985 (AllWinning.cons node_8994 (AllWinning.cons node_7994 (AllWinning.nil)))))

theorem node_9947 : Outcome ⟨1, 5, 17, 4⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 6⟩) (by decide) node_7035

theorem node_9948 : Outcome ⟨1, 5, 17, 6⟩ true :=
  Outcome.win (q := ⟨1, 2, 17, 6⟩) (by decide) node_7035

theorem node_9949 : Outcome ⟨1, 5, 17, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 16⟩) (by decide) node_3419

theorem node_9950 : Outcome ⟨1, 5, 17, 16⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 16⟩) (by decide) node_3419

theorem node_9951 : Outcome ⟨1, 6, 16, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 16, 2⟩, ⟨1, 5, 16, 2⟩, ⟨1, 4, 16, 4⟩, ⟨1, 6, 15, 2⟩, ⟨1, 6, 14, 4⟩]
  exact AllWinning.cons node_8918 (AllWinning.cons node_8994 (AllWinning.cons node_7989 (AllWinning.cons node_8997 (AllWinning.cons node_7998 (AllWinning.nil)))))

theorem node_9952 : Outcome ⟨1, 6, 16, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 16, 2⟩, ⟨1, 5, 16, 2⟩, ⟨1, 4, 16, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 2, 16, 8⟩, ⟨1, 6, 15, 2⟩, ⟨1, 6, 14, 4⟩, ⟨1, 6, 13, 6⟩, ⟨1, 6, 12, 8⟩]
  exact AllWinning.cons node_8918 (AllWinning.cons node_8994 (AllWinning.cons node_7989 (AllWinning.cons node_7041 (AllWinning.cons node_6120 (AllWinning.cons node_8997 (AllWinning.cons node_7998 (AllWinning.cons node_7057 (AllWinning.cons node_6135 (AllWinning.nil)))))))))

theorem node_9953 : Outcome ⟨1, 6, 16, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 16, 2⟩, ⟨1, 5, 16, 2⟩, ⟨1, 4, 16, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 2, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨1, 0, 16, 12⟩, ⟨1, 6, 15, 2⟩, ⟨1, 6, 14, 4⟩, ⟨1, 6, 13, 6⟩, ⟨1, 6, 12, 8⟩, ⟨1, 6, 11, 10⟩, ⟨1, 6, 10, 12⟩]
  exact AllWinning.cons node_8918 (AllWinning.cons node_8994 (AllWinning.cons node_7989 (AllWinning.cons node_7041 (AllWinning.cons node_6120 (AllWinning.cons node_5394 (AllWinning.cons node_4651 (AllWinning.cons node_8997 (AllWinning.cons node_7998 (AllWinning.cons node_7057 (AllWinning.cons node_6135 (AllWinning.cons node_5414 (AllWinning.cons node_4675 (AllWinning.nil)))))))))))))

theorem node_9954 : Outcome ⟨1, 6, 16, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 16, 2⟩, ⟨1, 5, 16, 2⟩, ⟨1, 4, 16, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 2, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨1, 0, 16, 12⟩, ⟨1, 6, 15, 2⟩, ⟨1, 6, 14, 4⟩, ⟨1, 6, 13, 6⟩, ⟨1, 6, 12, 8⟩, ⟨1, 6, 11, 10⟩, ⟨1, 6, 10, 12⟩, ⟨1, 6, 9, 14⟩, ⟨1, 6, 8, 16⟩]
  exact AllWinning.cons node_8918 (AllWinning.cons node_8994 (AllWinning.cons node_7989 (AllWinning.cons node_7041 (AllWinning.cons node_6120 (AllWinning.cons node_5394 (AllWinning.cons node_4651 (AllWinning.cons node_8997 (AllWinning.cons node_7998 (AllWinning.cons node_7057 (AllWinning.cons node_6135 (AllWinning.cons node_5414 (AllWinning.cons node_4675 (AllWinning.cons node_4021 (AllWinning.cons node_3429 (AllWinning.nil)))))))))))))))

theorem node_9955 : Outcome ⟨1, 6, 16, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 16, 2⟩, ⟨1, 5, 16, 2⟩, ⟨1, 4, 16, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 2, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨1, 0, 16, 12⟩, ⟨1, 6, 15, 2⟩, ⟨1, 6, 14, 4⟩, ⟨1, 6, 13, 6⟩, ⟨1, 6, 12, 8⟩, ⟨1, 6, 11, 10⟩, ⟨1, 6, 10, 12⟩, ⟨1, 6, 9, 14⟩, ⟨1, 6, 8, 16⟩, ⟨1, 6, 7, 18⟩, ⟨1, 6, 6, 20⟩]
  exact AllWinning.cons node_8918 (AllWinning.cons node_8994 (AllWinning.cons node_7989 (AllWinning.cons node_7041 (AllWinning.cons node_6120 (AllWinning.cons node_5394 (AllWinning.cons node_4651 (AllWinning.cons node_8997 (AllWinning.cons node_7998 (AllWinning.cons node_7057 (AllWinning.cons node_6135 (AllWinning.cons node_5414 (AllWinning.cons node_4675 (AllWinning.cons node_4021 (AllWinning.cons node_3429 (AllWinning.cons node_2913 (AllWinning.cons node_2455 (AllWinning.nil)))))))))))))))))

theorem node_9956 : Outcome ⟨1, 6, 16, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 6, 16, 2⟩, ⟨1, 5, 16, 2⟩, ⟨1, 4, 16, 4⟩, ⟨1, 3, 16, 6⟩, ⟨1, 2, 16, 8⟩, ⟨1, 1, 16, 10⟩, ⟨1, 0, 16, 12⟩, ⟨1, 6, 15, 2⟩, ⟨1, 6, 14, 4⟩, ⟨1, 6, 13, 6⟩, ⟨1, 6, 12, 8⟩, ⟨1, 6, 11, 10⟩, ⟨1, 6, 10, 12⟩, ⟨1, 6, 9, 14⟩, ⟨1, 6, 8, 16⟩, ⟨1, 6, 7, 18⟩, ⟨1, 6, 6, 20⟩, ⟨1, 6, 5, 22⟩, ⟨1, 6, 4, 24⟩]
  exact AllWinning.cons node_8918 (AllWinning.cons node_8994 (AllWinning.cons node_7989 (AllWinning.cons node_7041 (AllWinning.cons node_6120 (AllWinning.cons node_5394 (AllWinning.cons node_4651 (AllWinning.cons node_8997 (AllWinning.cons node_7998 (AllWinning.cons node_7057 (AllWinning.cons node_6135 (AllWinning.cons node_5414 (AllWinning.cons node_4675 (AllWinning.cons node_4021 (AllWinning.cons node_3429 (AllWinning.cons node_2913 (AllWinning.cons node_2455 (AllWinning.cons node_1957 (AllWinning.cons node_1619 (AllWinning.nil)))))))))))))))))))

theorem node_9957 : Outcome ⟨1, 6, 16, 18⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 26⟩) (by decide) node_1259

theorem node_9958 : Outcome ⟨1, 6, 16, 22⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 26⟩) (by decide) node_1259

theorem node_9959 : Outcome ⟨1, 7, 15, 2⟩ true :=
  Outcome.win (q := ⟨0, 7, 15, 2⟩) (by decide) node_8923

theorem node_9960 : Outcome ⟨1, 7, 15, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 8⟩) (by decide) node_6140

theorem node_9961 : Outcome ⟨1, 7, 15, 8⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 8⟩) (by decide) node_6140

theorem node_9962 : Outcome ⟨1, 7, 15, 18⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 8⟩) (by decide) node_6140

theorem node_9963 : Outcome ⟨1, 7, 15, 22⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 8⟩) (by decide) node_6140

theorem node_9964 : Outcome ⟨1, 8, 14, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 4⟩) (by decide) node_8006

theorem node_9965 : Outcome ⟨1, 8, 14, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 4⟩) (by decide) node_8006

theorem node_9966 : Outcome ⟨1, 8, 14, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 4⟩) (by decide) node_8006

theorem node_9967 : Outcome ⟨1, 9, 13, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 13, 2⟩, ⟨1, 8, 13, 2⟩, ⟨1, 7, 13, 4⟩, ⟨1, 9, 12, 2⟩, ⟨1, 9, 11, 4⟩]
  exact AllWinning.cons node_8932 (AllWinning.cons node_9003 (AllWinning.cons node_8001 (AllWinning.cons node_9006 (AllWinning.cons node_8018 (AllWinning.nil)))))

theorem node_9968 : Outcome ⟨1, 9, 13, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 13, 2⟩, ⟨1, 8, 13, 2⟩, ⟨1, 7, 13, 4⟩, ⟨1, 6, 13, 6⟩, ⟨1, 5, 13, 8⟩, ⟨1, 9, 12, 2⟩, ⟨1, 9, 11, 4⟩, ⟨1, 9, 10, 6⟩, ⟨1, 9, 9, 8⟩]
  exact AllWinning.cons node_8932 (AllWinning.cons node_9003 (AllWinning.cons node_8001 (AllWinning.cons node_7057 (AllWinning.cons node_6131 (AllWinning.cons node_9006 (AllWinning.cons node_8018 (AllWinning.cons node_7068 (AllWinning.cons node_6156 (AllWinning.nil)))))))))

theorem node_9969 : Outcome ⟨1, 9, 13, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 9, 13, 2⟩, ⟨1, 8, 13, 2⟩, ⟨1, 7, 13, 4⟩, ⟨1, 6, 13, 6⟩, ⟨1, 5, 13, 8⟩, ⟨1, 4, 13, 10⟩, ⟨1, 3, 13, 12⟩, ⟨1, 9, 12, 2⟩, ⟨1, 9, 11, 4⟩, ⟨1, 9, 10, 6⟩, ⟨1, 9, 9, 8⟩, ⟨1, 9, 8, 10⟩, ⟨1, 9, 7, 12⟩]
  exact AllWinning.cons node_8932 (AllWinning.cons node_9003 (AllWinning.cons node_8001 (AllWinning.cons node_7057 (AllWinning.cons node_6131 (AllWinning.cons node_5406 (AllWinning.cons node_4663 (AllWinning.cons node_9006 (AllWinning.cons node_8018 (AllWinning.cons node_7068 (AllWinning.cons node_6156 (AllWinning.cons node_5425 (AllWinning.cons node_4688 (AllWinning.nil)))))))))))))

theorem node_9970 : Outcome ⟨1, 9, 13, 12⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 16⟩) (by decide) node_3443

theorem node_9971 : Outcome ⟨1, 9, 13, 16⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 16⟩) (by decide) node_3443

theorem node_9972 : Outcome ⟨1, 10, 12, 2⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 4⟩) (by decide) node_8006

theorem node_9973 : Outcome ⟨1, 10, 12, 4⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 4⟩) (by decide) node_8006

theorem node_9974 : Outcome ⟨1, 10, 12, 8⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 4⟩) (by decide) node_8006

theorem node_9975 : Outcome ⟨1, 10, 12, 18⟩ true :=
  Outcome.win (q := ⟨1, 8, 12, 4⟩) (by decide) node_8006

theorem node_9976 : Outcome ⟨1, 11, 11, 2⟩ true :=
  Outcome.win (q := ⟨0, 11, 11, 2⟩) (by decide) node_8938

theorem node_9977 : Outcome ⟨1, 11, 11, 4⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 8⟩) (by decide) node_6140

theorem node_9978 : Outcome ⟨1, 11, 11, 8⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 8⟩) (by decide) node_6140

theorem node_9979 : Outcome ⟨1, 11, 11, 16⟩ true :=
  Outcome.win (q := ⟨1, 7, 11, 8⟩) (by decide) node_6140

theorem node_9980 : Outcome ⟨1, 12, 10, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 4⟩) (by decide) node_8027

theorem node_9981 : Outcome ⟨1, 12, 10, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 4⟩) (by decide) node_8027

theorem node_9982 : Outcome ⟨1, 12, 10, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 4⟩) (by decide) node_8027

theorem node_9983 : Outcome ⟨1, 12, 10, 18⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 4⟩) (by decide) node_8027

theorem node_9984 : Outcome ⟨1, 13, 9, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 9, 2⟩, ⟨1, 12, 9, 2⟩, ⟨1, 11, 9, 4⟩, ⟨1, 13, 8, 2⟩, ⟨1, 13, 7, 4⟩]
  exact AllWinning.cons node_8950 (AllWinning.cons node_9017 (AllWinning.cons node_8024 (AllWinning.cons node_9020 (AllWinning.cons node_8038 (AllWinning.nil)))))

theorem node_9985 : Outcome ⟨1, 13, 9, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 9, 2⟩, ⟨1, 12, 9, 2⟩, ⟨1, 11, 9, 4⟩, ⟨1, 10, 9, 6⟩, ⟨1, 9, 9, 8⟩, ⟨1, 13, 8, 2⟩, ⟨1, 13, 7, 4⟩, ⟨1, 13, 6, 6⟩, ⟨1, 13, 5, 8⟩]
  exact AllWinning.cons node_8950 (AllWinning.cons node_9017 (AllWinning.cons node_8024 (AllWinning.cons node_7072 (AllWinning.cons node_6156 (AllWinning.cons node_9020 (AllWinning.cons node_8038 (AllWinning.cons node_7081 (AllWinning.cons node_6179 (AllWinning.nil)))))))))

theorem node_9986 : Outcome ⟨1, 13, 9, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 13, 9, 2⟩, ⟨1, 12, 9, 2⟩, ⟨1, 11, 9, 4⟩, ⟨1, 10, 9, 6⟩, ⟨1, 9, 9, 8⟩, ⟨1, 8, 9, 10⟩, ⟨1, 7, 9, 12⟩, ⟨1, 13, 8, 2⟩, ⟨1, 13, 7, 4⟩, ⟨1, 13, 6, 6⟩, ⟨1, 13, 5, 8⟩, ⟨1, 13, 4, 10⟩, ⟨1, 13, 3, 12⟩]
  exact AllWinning.cons node_8950 (AllWinning.cons node_9017 (AllWinning.cons node_8024 (AllWinning.cons node_7072 (AllWinning.cons node_6156 (AllWinning.cons node_5421 (AllWinning.cons node_4680 (AllWinning.cons node_9020 (AllWinning.cons node_8038 (AllWinning.cons node_7081 (AllWinning.cons node_6179 (AllWinning.cons node_5438 (AllWinning.cons node_4704 (AllWinning.nil)))))))))))))

theorem node_9987 : Outcome ⟨1, 13, 9, 12⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 16⟩) (by decide) node_3419

theorem node_9988 : Outcome ⟨1, 13, 9, 16⟩ true :=
  Outcome.win (q := ⟨1, 5, 9, 16⟩) (by decide) node_3419

theorem node_9989 : Outcome ⟨1, 14, 8, 2⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 4⟩) (by decide) node_8027

theorem node_9990 : Outcome ⟨1, 14, 8, 4⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 4⟩) (by decide) node_8027

theorem node_9991 : Outcome ⟨1, 14, 8, 8⟩ true :=
  Outcome.win (q := ⟨1, 12, 8, 4⟩) (by decide) node_8027

theorem node_9992 : Outcome ⟨1, 15, 7, 2⟩ true :=
  Outcome.win (q := ⟨0, 15, 7, 2⟩) (by decide) node_8956

theorem node_9993 : Outcome ⟨1, 15, 7, 4⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 8⟩) (by decide) node_6165

theorem node_9994 : Outcome ⟨1, 15, 7, 8⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 8⟩) (by decide) node_6165

theorem node_9995 : Outcome ⟨1, 15, 7, 18⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 8⟩) (by decide) node_6165

theorem node_9996 : Outcome ⟨1, 15, 7, 22⟩ true :=
  Outcome.win (q := ⟨1, 11, 7, 8⟩) (by decide) node_6165

theorem node_9997 : Outcome ⟨1, 16, 6, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 6, 2⟩, ⟨1, 15, 6, 2⟩, ⟨1, 14, 6, 4⟩, ⟨1, 16, 5, 2⟩, ⟨1, 16, 4, 4⟩]
  exact AllWinning.cons node_8962 (AllWinning.cons node_9024 (AllWinning.cons node_8042 (AllWinning.cons node_9029 (AllWinning.cons node_8049 (AllWinning.nil)))))

theorem node_9998 : Outcome ⟨1, 16, 6, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 6, 2⟩, ⟨1, 15, 6, 2⟩, ⟨1, 14, 6, 4⟩, ⟨1, 13, 6, 6⟩, ⟨1, 12, 6, 8⟩, ⟨1, 16, 5, 2⟩, ⟨1, 16, 4, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 16, 2, 8⟩]
  exact AllWinning.cons node_8962 (AllWinning.cons node_9024 (AllWinning.cons node_8042 (AllWinning.cons node_7081 (AllWinning.cons node_6176 (AllWinning.cons node_9029 (AllWinning.cons node_8049 (AllWinning.cons node_7095 (AllWinning.cons node_6189 (AllWinning.nil)))))))))

theorem node_9999 : Outcome ⟨1, 16, 6, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 6, 2⟩, ⟨1, 15, 6, 2⟩, ⟨1, 14, 6, 4⟩, ⟨1, 13, 6, 6⟩, ⟨1, 12, 6, 8⟩, ⟨1, 11, 6, 10⟩, ⟨1, 10, 6, 12⟩, ⟨1, 16, 5, 2⟩, ⟨1, 16, 4, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 16, 2, 8⟩, ⟨1, 16, 1, 10⟩, ⟨1, 16, 0, 12⟩]
  exact AllWinning.cons node_8962 (AllWinning.cons node_9024 (AllWinning.cons node_8042 (AllWinning.cons node_7081 (AllWinning.cons node_6176 (AllWinning.cons node_5431 (AllWinning.cons node_4691 (AllWinning.cons node_9029 (AllWinning.cons node_8049 (AllWinning.cons node_7095 (AllWinning.cons node_6189 (AllWinning.cons node_5451 (AllWinning.cons node_4717 (AllWinning.nil)))))))))))))

theorem node_10000 : Outcome ⟨1, 16, 6, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 6, 2⟩, ⟨1, 15, 6, 2⟩, ⟨1, 14, 6, 4⟩, ⟨1, 13, 6, 6⟩, ⟨1, 12, 6, 8⟩, ⟨1, 11, 6, 10⟩, ⟨1, 10, 6, 12⟩, ⟨1, 9, 6, 14⟩, ⟨1, 8, 6, 16⟩, ⟨1, 16, 5, 2⟩, ⟨1, 16, 4, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 16, 2, 8⟩, ⟨1, 16, 1, 10⟩, ⟨1, 16, 0, 12⟩]
  exact AllWinning.cons node_8962 (AllWinning.cons node_9024 (AllWinning.cons node_8042 (AllWinning.cons node_7081 (AllWinning.cons node_6176 (AllWinning.cons node_5431 (AllWinning.cons node_4691 (AllWinning.cons node_4032 (AllWinning.cons node_3435 (AllWinning.cons node_9029 (AllWinning.cons node_8049 (AllWinning.cons node_7095 (AllWinning.cons node_6189 (AllWinning.cons node_5451 (AllWinning.cons node_4717 (AllWinning.nil)))))))))))))))

theorem node_10001 : Outcome ⟨1, 16, 6, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 6, 2⟩, ⟨1, 15, 6, 2⟩, ⟨1, 14, 6, 4⟩, ⟨1, 13, 6, 6⟩, ⟨1, 12, 6, 8⟩, ⟨1, 11, 6, 10⟩, ⟨1, 10, 6, 12⟩, ⟨1, 9, 6, 14⟩, ⟨1, 8, 6, 16⟩, ⟨1, 7, 6, 18⟩, ⟨1, 6, 6, 20⟩, ⟨1, 16, 5, 2⟩, ⟨1, 16, 4, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 16, 2, 8⟩, ⟨1, 16, 1, 10⟩, ⟨1, 16, 0, 12⟩]
  exact AllWinning.cons node_8962 (AllWinning.cons node_9024 (AllWinning.cons node_8042 (AllWinning.cons node_7081 (AllWinning.cons node_6176 (AllWinning.cons node_5431 (AllWinning.cons node_4691 (AllWinning.cons node_4032 (AllWinning.cons node_3435 (AllWinning.cons node_2917 (AllWinning.cons node_2455 (AllWinning.cons node_9029 (AllWinning.cons node_8049 (AllWinning.cons node_7095 (AllWinning.cons node_6189 (AllWinning.cons node_5451 (AllWinning.cons node_4717 (AllWinning.nil)))))))))))))))))

theorem node_10002 : Outcome ⟨1, 16, 6, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 16, 6, 2⟩, ⟨1, 15, 6, 2⟩, ⟨1, 14, 6, 4⟩, ⟨1, 13, 6, 6⟩, ⟨1, 12, 6, 8⟩, ⟨1, 11, 6, 10⟩, ⟨1, 10, 6, 12⟩, ⟨1, 9, 6, 14⟩, ⟨1, 8, 6, 16⟩, ⟨1, 7, 6, 18⟩, ⟨1, 6, 6, 20⟩, ⟨1, 5, 6, 22⟩, ⟨1, 4, 6, 24⟩, ⟨1, 16, 5, 2⟩, ⟨1, 16, 4, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 16, 2, 8⟩, ⟨1, 16, 1, 10⟩, ⟨1, 16, 0, 12⟩]
  exact AllWinning.cons node_8962 (AllWinning.cons node_9024 (AllWinning.cons node_8042 (AllWinning.cons node_7081 (AllWinning.cons node_6176 (AllWinning.cons node_5431 (AllWinning.cons node_4691 (AllWinning.cons node_4032 (AllWinning.cons node_3435 (AllWinning.cons node_2917 (AllWinning.cons node_2455 (AllWinning.cons node_1954 (AllWinning.cons node_1613 (AllWinning.cons node_9029 (AllWinning.cons node_8049 (AllWinning.cons node_7095 (AllWinning.cons node_6189 (AllWinning.cons node_5451 (AllWinning.cons node_4717 (AllWinning.nil)))))))))))))))))))

theorem node_10003 : Outcome ⟨1, 16, 6, 18⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 26⟩) (by decide) node_1231

theorem node_10004 : Outcome ⟨1, 16, 6, 22⟩ true :=
  Outcome.win (q := ⟨1, 3, 6, 26⟩) (by decide) node_1231

theorem node_10005 : Outcome ⟨1, 17, 5, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 6⟩) (by decide) node_7101

theorem node_10006 : Outcome ⟨1, 17, 5, 6⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 6⟩) (by decide) node_7101

theorem node_10007 : Outcome ⟨1, 17, 5, 12⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 16⟩) (by decide) node_3443

theorem node_10008 : Outcome ⟨1, 17, 5, 16⟩ true :=
  Outcome.win (q := ⟨1, 9, 5, 16⟩) (by decide) node_3443

theorem node_10009 : Outcome ⟨1, 18, 4, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 18, 4, 2⟩, ⟨1, 17, 4, 2⟩, ⟨1, 16, 4, 4⟩, ⟨1, 18, 3, 2⟩, ⟨1, 18, 2, 4⟩]
  exact AllWinning.cons node_8970 (AllWinning.cons node_9032 (AllWinning.cons node_8049 (AllWinning.cons node_9038 (AllWinning.cons node_8058 (AllWinning.nil)))))

theorem node_10010 : Outcome ⟨1, 18, 4, 4⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 6⟩) (by decide) node_7089

theorem node_10011 : Outcome ⟨1, 18, 4, 6⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 6⟩) (by decide) node_7089

theorem node_10012 : Outcome ⟨1, 18, 4, 8⟩ true :=
  Outcome.win (q := ⟨1, 15, 4, 6⟩) (by decide) node_7089

theorem node_10013 : Outcome ⟨1, 18, 4, 20⟩ true :=
  Outcome.win (q := ⟨1, 2, 4, 32⟩) (by decide) node_519

theorem node_10014 : Outcome ⟨1, 19, 3, 2⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 3, 2⟩, ⟨1, 18, 3, 2⟩, ⟨1, 17, 3, 4⟩, ⟨1, 19, 2, 2⟩, ⟨1, 19, 1, 4⟩]
  exact AllWinning.cons node_8974 (AllWinning.cons node_9038 (AllWinning.cons node_8053 (AllWinning.cons node_9041 (AllWinning.cons node_8061 (AllWinning.nil)))))

theorem node_10015 : Outcome ⟨1, 19, 3, 4⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 3, 2⟩, ⟨1, 18, 3, 2⟩, ⟨1, 17, 3, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 15, 3, 8⟩, ⟨1, 19, 2, 2⟩, ⟨1, 19, 1, 4⟩, ⟨1, 19, 0, 6⟩]
  exact AllWinning.cons node_8974 (AllWinning.cons node_9038 (AllWinning.cons node_8053 (AllWinning.cons node_7095 (AllWinning.cons node_6185 (AllWinning.cons node_9041 (AllWinning.cons node_8061 (AllWinning.cons node_7110 (AllWinning.nil))))))))

theorem node_10016 : Outcome ⟨1, 19, 3, 6⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 3, 2⟩, ⟨1, 18, 3, 2⟩, ⟨1, 17, 3, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 15, 3, 8⟩, ⟨1, 14, 3, 10⟩, ⟨1, 13, 3, 12⟩, ⟨1, 19, 2, 2⟩, ⟨1, 19, 1, 4⟩, ⟨1, 19, 0, 6⟩]
  exact AllWinning.cons node_8974 (AllWinning.cons node_9038 (AllWinning.cons node_8053 (AllWinning.cons node_7095 (AllWinning.cons node_6185 (AllWinning.cons node_5443 (AllWinning.cons node_4704 (AllWinning.cons node_9041 (AllWinning.cons node_8061 (AllWinning.cons node_7110 (AllWinning.nil))))))))))

theorem node_10017 : Outcome ⟨1, 19, 3, 8⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 3, 2⟩, ⟨1, 18, 3, 2⟩, ⟨1, 17, 3, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 15, 3, 8⟩, ⟨1, 14, 3, 10⟩, ⟨1, 13, 3, 12⟩, ⟨1, 12, 3, 14⟩, ⟨1, 11, 3, 16⟩, ⟨1, 19, 2, 2⟩, ⟨1, 19, 1, 4⟩, ⟨1, 19, 0, 6⟩]
  exact AllWinning.cons node_8974 (AllWinning.cons node_9038 (AllWinning.cons node_8053 (AllWinning.cons node_7095 (AllWinning.cons node_6185 (AllWinning.cons node_5443 (AllWinning.cons node_4704 (AllWinning.cons node_4042 (AllWinning.cons node_3457 (AllWinning.cons node_9041 (AllWinning.cons node_8061 (AllWinning.cons node_7110 (AllWinning.nil))))))))))))

theorem node_10018 : Outcome ⟨1, 19, 3, 10⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 3, 2⟩, ⟨1, 18, 3, 2⟩, ⟨1, 17, 3, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 15, 3, 8⟩, ⟨1, 14, 3, 10⟩, ⟨1, 13, 3, 12⟩, ⟨1, 12, 3, 14⟩, ⟨1, 11, 3, 16⟩, ⟨1, 10, 3, 18⟩, ⟨1, 9, 3, 20⟩, ⟨1, 19, 2, 2⟩, ⟨1, 19, 1, 4⟩, ⟨1, 19, 0, 6⟩]
  exact AllWinning.cons node_8974 (AllWinning.cons node_9038 (AllWinning.cons node_8053 (AllWinning.cons node_7095 (AllWinning.cons node_6185 (AllWinning.cons node_5443 (AllWinning.cons node_4704 (AllWinning.cons node_4042 (AllWinning.cons node_3457 (AllWinning.cons node_2927 (AllWinning.cons node_2467 (AllWinning.cons node_9041 (AllWinning.cons node_8061 (AllWinning.cons node_7110 (AllWinning.nil))))))))))))))

theorem node_10019 : Outcome ⟨1, 19, 3, 12⟩ false := by
  apply Outcome.lose
  change AllWinning [⟨0, 19, 3, 2⟩, ⟨1, 18, 3, 2⟩, ⟨1, 17, 3, 4⟩, ⟨1, 16, 3, 6⟩, ⟨1, 15, 3, 8⟩, ⟨1, 14, 3, 10⟩, ⟨1, 13, 3, 12⟩, ⟨1, 12, 3, 14⟩, ⟨1, 11, 3, 16⟩, ⟨1, 10, 3, 18⟩, ⟨1, 9, 3, 20⟩, ⟨1, 8, 3, 22⟩, ⟨1, 7, 3, 24⟩, ⟨1, 19, 2, 2⟩, ⟨1, 19, 1, 4⟩, ⟨1, 19, 0, 6⟩]
  exact AllWinning.cons node_8974 (AllWinning.cons node_9038 (AllWinning.cons node_8053 (AllWinning.cons node_7095 (AllWinning.cons node_6185 (AllWinning.cons node_5443 (AllWinning.cons node_4704 (AllWinning.cons node_4042 (AllWinning.cons node_3457 (AllWinning.cons node_2927 (AllWinning.cons node_2467 (AllWinning.cons node_1968 (AllWinning.cons node_1623 (AllWinning.cons node_9041 (AllWinning.cons node_8061 (AllWinning.cons node_7110 (AllWinning.nil))))))))))))))))

theorem node_10020 : Outcome ⟨1, 19, 3, 18⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 26⟩) (by decide) node_1259

theorem node_10021 : Outcome ⟨1, 19, 3, 20⟩ true :=
  Outcome.win (q := ⟨1, 6, 3, 26⟩) (by decide) node_1259

theorem node_10022 : Outcome ⟨1, 20, 2, 4⟩ true :=
  Outcome.win (q := ⟨1, 17, 2, 6⟩) (by decide) node_7101

theorem node_10023 : Outcome ⟨2, 1, 20, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 6⟩) (by decide) node_7118

theorem node_10024 : Outcome ⟨2, 2, 19, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 18, 2⟩) (by decide) node_9052

theorem node_10025 : Outcome ⟨2, 2, 19, 12⟩ true :=
  Outcome.win (q := ⟨2, 2, 13, 12⟩) (by decide) node_4735

theorem node_10026 : Outcome ⟨2, 3, 18, 2⟩ true :=
  Outcome.win (q := ⟨2, 2, 18, 2⟩) (by decide) node_9052

theorem node_10027 : Outcome ⟨2, 3, 18, 4⟩ true :=
  Outcome.win (q := ⟨2, 2, 18, 2⟩) (by decide) node_9052

theorem node_10028 : Outcome ⟨2, 3, 18, 8⟩ true :=
  Outcome.win (q := ⟨2, 2, 18, 2⟩) (by decide) node_9052

theorem node_10029 : Outcome ⟨2, 3, 18, 26⟩ true :=
  Outcome.win (q := ⟨2, 3, 7, 22⟩) (by decide) node_2004

theorem node_10030 : Outcome ⟨2, 4, 17, 2⟩ true :=
  Outcome.win (q := ⟨0, 4, 17, 4⟩) (by decide) node_7917

theorem node_10031 : Outcome ⟨2, 4, 17, 4⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 6⟩) (by decide) node_7118

theorem node_10032 : Outcome ⟨2, 4, 17, 6⟩ true :=
  Outcome.win (q := ⟨2, 1, 17, 6⟩) (by decide) node_7118

end RQ9F1
