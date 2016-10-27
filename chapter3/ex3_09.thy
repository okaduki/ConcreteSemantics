theory ex3_09 imports Main "~~/src/HOL/IMP/AExp" "~~/src/HOL/IMP/BExp" begin

datatype pbexp = VAR vname | NOT pbexp | OR pbexp pbexp | AND pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x) s = s x" |
"pbval (NOT x) s = (\<not> pbval x s)" |
"pbval (OR x y) s = (pbval x s \<and> pbval y s)" |
"pbval (AND x y) s = (pbval x s \<or> pbval y s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (VAR x) = True" |
"is_nnf (NOT (VAR _)) = True" |
"is_nnf (NOT _) = False" |
"is_nnf (OR x y) = (is_nnf x \<and> is_nnf y)" |
"is_nnf (AND x y) = (is_nnf x \<and> is_nnf y)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (VAR x) = VAR x" |
"nnf (OR x y) = OR (nnf x) (nnf y)" |
"nnf (AND x y) = AND (nnf x) (nnf y)" |
"nnf (NOT (VAR x)) = NOT (VAR x)" |
"nnf (NOT (NOT x)) = nnf x" |
"nnf (NOT (AND x y)) = OR (nnf (NOT x)) (nnf (NOT y))" |
"nnf (NOT (OR x y)) = AND (nnf (NOT x)) (nnf (NOT y))"

theorem[simp]: "pbval (nnf b) s = pbval b s"
apply(induction b rule: "nnf.induct")
apply auto
done

theorem[simp]: "is_nnf (nnf b)"
apply(induction b rule: "nnf.induct")
apply auto
done

fun is_dnf_sub :: "pbexp \<Rightarrow> bool" where
"is_dnf_sub (VAR x) = True" |
"is_dnf_sub (NOT x) = is_dnf_sub x" |
"is_dnf_sub (OR x y) = False" |
"is_dnf_sub (AND x y) = (is_dnf_sub x \<and> is_dnf_sub y)"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf (VAR x) = True" |
"is_dnf (NOT (VAR x)) = True" |
"is_dnf (NOT _) = False" |
"is_dnf (OR x y) = (is_nnf (OR x y) \<and> is_dnf x \<and> is_dnf y)" |
"is_dnf (AND x y) = (is_nnf (AND x y) \<and> is_dnf_sub x \<and> is_dnf_sub y)"

(* calculate dnf of (x\<and>y) where x,y is dnf *)
fun dnf_dist :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dnf_dist (OR x1 x2) y = (OR (dnf_dist x1 y) (dnf_dist x2 y))" |
"dnf_dist x (OR y1 y2) = (OR (dnf_dist x y1) (dnf_dist x y2))" |
"dnf_dist x y = (AND x y)"

fun dnf_of_nnf :: "pbexp \<Rightarrow> pbexp" where
"dnf_of_nnf (VAR x) = VAR x" |
"dnf_of_nnf (NOT x) = NOT x" |
"dnf_of_nnf (OR x y) = OR (dnf_of_nnf x) (dnf_of_nnf y)" |
"dnf_of_nnf (AND x y) = dnf_dist (dnf_of_nnf x) (dnf_of_nnf y)"

lemma[simp]: "pbval (dnf_dist x y) s = pbval (AND x y) s"
apply(induction x y arbitrary: s rule: "dnf_dist.induct")
apply auto
done

theorem[simp]: "pbval (dnf_of_nnf b) s = pbval b s"
apply(induction b arbitrary: s rule: "dnf_of_nnf.induct")
apply auto
done


lemma[simp]: "is_dnf x \<Longrightarrow> is_nnf x"
apply(induction x)
apply auto
using is_dnf.elims(2) by fastforce

lemma[simp]: "\<lbrakk> is_dnf x; is_dnf y \<rbrakk> \<Longrightarrow> is_dnf (dnf_dist x y)"
apply(induction x y rule: "dnf_dist.induct")
apply auto
apply (metis is_dnf.simps(3) is_dnf.simps(4) is_dnf.simps(5) is_dnf_sub.elims(3))+
done

theorem[simp]: "is_nnf b \<Longrightarrow> is_dnf (dnf_of_nnf b)"
apply(induction b rule: "dnf_of_nnf.induct")
apply auto
using is_nnf.elims(2) by fastforce

end