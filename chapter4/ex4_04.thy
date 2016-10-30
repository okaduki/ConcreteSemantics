theory ex4_04 imports Main "~~/src/HOL/IMP/Star" begin

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
irefl: "iter r 0 x x" |
istep: "iter r n xa y \<Longrightarrow> r x xa \<Longrightarrow> iter r (n+1) x y"

theorem "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
apply(induction rule: star.induct)
apply (meson irefl)
by (meson istep)

end