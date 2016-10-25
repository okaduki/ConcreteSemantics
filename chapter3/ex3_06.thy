theory ex3_06 imports Main "~~/src/HOL/IMP/AExp" begin

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> val" where
"lval (Nl n) s = n" |
"lval (Vl x) s = s x" |
"lval (Plusl l r) s = lval l s + lval r s" |
"lval (LET x a b) s = lval b (s(x := lval a s))"

(** let x = (let y = 1 in y+y) in 1+x == 3 **)
value "lval (LET ''x'' (LET ''y'' (Nl 1) (Plusl (Vl ''y'') (Vl ''y''))) (Plusl (Nl 1) (Vl ''x''))) <>"

(** see ex3.3 **)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V v) = (if x = v then a else (V v))" |
"subst x a (Plus l r) = Plus (subst x a l) (subst x a r)"

theorem[simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
by (induction e, auto)

theorem[simp]: "aval a_1 s = aval a_2 s \<Longrightarrow> aval (subst x a_1 e) s = aval (subst x a_2 e) s"
by (induction e, auto)

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = N n" |
"inline (Vl x) = V x" |
"inline (Plusl l r) = Plus (inline l) (inline r)" |
"inline (LET x a b) = subst x (inline a) (inline b)"

(** let x = (let y = 1 in y+y) in 1+x **)
value "inline (LET ''x'' (LET ''y'' (Nl 1) (Plusl (Vl ''y'') (Vl ''y''))) (Plusl (Nl 1) (Vl ''x'')))"

theorem "aval (inline e) s = lval e s"
apply(induction e arbitrary: s)
apply auto
done

end
