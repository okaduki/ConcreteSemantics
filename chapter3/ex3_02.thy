theory ex3_02 imports Main "~~/src/IMP/AExp" begin

(*
 full_asymp (Plus a b) returns (Plus x c) where c is summed up value.
 This is ugly but I do not have a better idea :-(
*)
fun full_asymp :: "aexp \<Rightarrow> aexp" where
"full_asymp (N n) = N n" |
"full_asymp (V v) = V v" |
"full_asymp (Plus a b) =
 (case (full_asymp a, full_asymp b) of
  (Plus ll (N m), Plus rl (N n)) \<Rightarrow> Plus (Plus ll rl) (N (m+n)) |
  (Plus ll (N m), N n)           \<Rightarrow> Plus ll (N (m+n)) |
  (Plus ll (N m), r)             \<Rightarrow> Plus (Plus ll r) (N m) |
  (Plus ll lr   , Plus rl (N n)) \<Rightarrow> Plus (Plus (Plus ll lr) rl) (N n) |
  (Plus ll lr   , N n) \<Rightarrow> Plus (Plus ll lr) (N n) |
  (N m, N n) \<Rightarrow> N (m+n) |
  (N m, Plus l (N n)) \<Rightarrow> Plus l (N (m+n)) |
  (N m, r) \<Rightarrow> Plus r (N m) |
  (l, Plus rl rr) \<Rightarrow> Plus (Plus l rl) rr |
  (l, r) \<Rightarrow> Plus l r
 )"

(** 1+(x+2) **)
value "full_asymp (Plus (N 1) (Plus (V x) (N 2)))"
(** (y+(1+z))+(2+(x+4)) **)
value "full_asymp (Plus (Plus (V y) (Plus (N 1) (V z))) (Plus (N 2) (Plus (V x) (N 4))))"

theorem "aval (full_asymp a) s = aval a s"
apply(induction a arbitrary: s rule: full_asymp.induct)
apply (auto split: aexp.split)
apply(auto simp add: algebra_simps)
done

end
