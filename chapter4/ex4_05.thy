theory ex4_05 imports Main "~~/src/HOL/IMP/Star" begin

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
s1: "S []"  |
s2: "S w \<Longrightarrow> S (a # w @ [b])" |
s3: "\<lbrakk> S w1; S w2 \<rbrakk> \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
t1: "T []"  |
t2: "\<lbrakk> T x; T y \<rbrakk> \<Longrightarrow> T (x @ a # y @ [b])"
  
lemma lem1:"T w \<Longrightarrow> T (a # w @ [b])"
using t1 t2 by force

lemma t2':"\<lbrakk> T w2; T w1 \<rbrakk> \<Longrightarrow> T (a # w1 @ b # w2)"
apply(induction rule: T.induct)
apply(auto simp add: t1 t2)
using t1 t2 apply force
using t2 by fastforce

lemma lem2: "\<lbrakk> T w3; T w1; T w2 \<rbrakk> \<Longrightarrow> T (w1 @ a # w2 @ b # w3)"
apply(induction rule: T.induct)
apply(auto simp add: t2)
using t2 by fastforce

lemma[simp]: "\<lbrakk> T w1; T w2 \<rbrakk> \<Longrightarrow> T (w1 @ w2)"
apply(induction rule: T.induct)
apply(auto simp add: lem2)
done

theorem s2t: "S w \<Longrightarrow> T w"
apply(induction rule: S.induct)
apply(auto simp add: t1 lem1)
done

theorem t2s: "T w \<Longrightarrow> S w"
apply(induction rule: T.induct)
apply(auto simp add: s1 s2 s3)
done

end