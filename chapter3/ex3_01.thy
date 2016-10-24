theory ex3_01 imports Main "~~/src/IMP/AExp" begin

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N _) = True" |
"optimal (V _) = True" |
"optimal (Plus (N _) (N _)) = False" |
"optimal (Plus l r) = (optimal l \<and> optimal r)"

theorem "optimal (asimp_const a)"
apply(induction a)
apply auto
apply (simp split: aexp.split)
apply auto
done

end