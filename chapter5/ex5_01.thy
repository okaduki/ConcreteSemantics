theory ex5_01 imports Main begin
lemma
assumes
 T: "\<forall>x y. T x y \<or> T y x" and
 A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y" and
 TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
proof -
 from T have "T x y \<or> T y x" by auto
 then show ?thesis
 proof
  assume "T x y" then show ?thesis by simp
 next
  assume "T y x"
  hence "A y x" using TA by auto
  hence "x = y" using A assms(4) by auto
  thus ?thesis using T by auto
 qed
qed

end