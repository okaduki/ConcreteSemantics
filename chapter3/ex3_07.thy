theory ex3_07 imports Main "~~/src/HOL/IMP/AExp" "~~/src/HOL/IMP/BExp" begin

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a1 a2 = Not (Less a2 a1)"

theorem "bval (Eq a1 a2) s = (aval a1 s = aval a2 s)"
apply auto
done

theorem "bval (Le a1 a2) s = (aval a1 s \<le> aval a2 s)"
apply auto
done

end