theory ex4_03 imports Main "~~/src/HOL/IMP/Star" begin

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

theorem[simp]: "star' r x y \<Longrightarrow> star r x y"
apply(induction rule: star'.induct)
apply auto
by (meson star_step1 star_trans)

lemma lem1: "\<lbrakk> star' r y z; r x y \<rbrakk> \<Longrightarrow> star' r x z"
apply(induction rule: "star'.induct")
apply(meson refl' step')
apply(auto simp add: step')
done

theorem "star r x y \<Longrightarrow> star' r x y"
apply(induction rule: star.induct)
apply(auto simp add: refl')
apply(simp add: lem1)
done

end