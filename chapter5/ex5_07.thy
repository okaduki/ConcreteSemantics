theory ex5_07 imports Main "~~/src/HOL/IMP/Star" begin

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
s1: "S []"  |
s2: "S w \<Longrightarrow> S (a # w @ [b])" |
s3: "\<lbrakk> S w1; S w2 \<rbrakk> \<Longrightarrow> S (w1 @ w2)"

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
"balanced 0 w = (S w)" |
"balanced (Suc n) w = balanced n (a # w)"

lemma r: "balanced n w \<Longrightarrow> S (replicate n a @ w)"
proof(induction n arbitrary: w)
  fix w
  let "?case" = "S (replicate 0 a @ w)"
  assume "balanced 0 w"
  then show ?case by auto
next
  fix n w
  let "?case" = "S (replicate (Suc n) a @ w)"
  assume
    IH : "\<And>w. balanced n w \<Longrightarrow> S (replicate n a @ w)" and
    prems : "balanced (Suc n) w"
  thus ?case
    by (metis append_Cons balanced.simps(2) replicate_Suc replicate_app_Cons_same)
qed

lemma l: "S (replicate n a @ w) \<Longrightarrow> balanced n w"
proof(induction n arbitrary: w)
  case 0
    fix w
    assume prems : "S (replicate 0 a @ w)"
    thus "balanced 0 w" by auto
next
  case Suc
    fix n w
    from Suc.IH Suc.prems show ?case by (simp add: replicate_app_Cons_same)
qed

theorem "balanced n w \<longleftrightarrow> S (replicate n a @ w)"
using r l by auto

end