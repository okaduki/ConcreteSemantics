theory ex4_06 imports Main "~~/src/HOL/IMP/AExp" begin

inductive aval_rel :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
const_rel: "aval_rel (N n) _ n" |
var_rel: "v = s x \<Longrightarrow> aval_rel (V x) s v" |
pl_rel: "\<lbrakk> aval_rel a1 s v1; aval_rel a2 s v2; v = v1+v2 \<rbrakk> \<Longrightarrow> aval_rel (Plus a1 a2) s v"


theorem rel2val: "aval_rel a s v \<Longrightarrow> aval a s = v"
by (induction rule: "aval_rel.induct", auto)

theorem val2rel: "aval a s = v \<Longrightarrow> aval_rel a s v"
apply(induction arbitrary: s v rule: aexp.induct)
apply(simp add: const_rel)
apply(simp add: var_rel)
apply(rule pl_rel)
apply auto
done

theorem "aval_rel a s v \<longleftrightarrow> aval a s = v"
using rel2val val2rel by blast

end