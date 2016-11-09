theory ex5_05 imports Main "~~/src/HOL/IMP/Star" begin
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
irefl: "iter r 0 x x" |
istep: "iter r n xa y \<Longrightarrow> r x xa \<Longrightarrow> iter r (n+1) x y"

theorem "iter r n x y \<Longrightarrow> star r x y"
proof(induction rule: iter.induct)
  fix x
  show "star r x x" by simp
next
  fix n xa y x
  assume "star r xa y" "r x xa"
  thus "star r x y" by (simp add: star.step)
qed

end