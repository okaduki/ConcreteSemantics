theory ex3_03 imports Main "~~/src/HOL/IMP/AExp" begin

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V v) = (if x = v then a else (V v))" |
"subst x a (Plus l r) = Plus (subst x a l) (subst x a r)"

value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))"

theorem "aval (subst x a e) s = aval e (s(x := aval a s))"
by (induction e, auto)

theorem "aval a_1 s = aval a_2 s \<Longrightarrow> aval (subst x a_1 e) s = aval (subst x a_2 e) s"
by (induction e, auto)

end