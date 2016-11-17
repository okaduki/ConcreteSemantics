theory ex7_02 imports Main "~~/src/HOL/IMP/Big_Step"
begin

fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True" |
"skip (v ::= x) = False" |
"skip (c1;;c2) = (skip c1 & skip c2)" |
"skip (IF b THEN c1 ELSE c2) = (skip c1 & skip c2)" |
"skip (WHILE b DO c) = False" (* If we try to check more strictly, we also need to consider termination *)


lemma skip_has_no_action: "\<lbrakk> skip c; (c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> s = t"
apply (induction arbitrary: s t rule: "skip.induct")
apply auto
done

theorem "skip c \<Longrightarrow> c \<sim> SKIP"
apply (induction c rule: "skip.induct")
apply auto
apply blast+
done

end
