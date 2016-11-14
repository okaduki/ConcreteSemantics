theory ex7_01 imports Main "~~/src/HOL/IMP/Big_Step"
begin

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (v ::= x) = {v}" |
"assigned (c1;;c2) = assigned c1 \<union> assigned c2" |
"assigned (IF b THEN c1 ELSE c2) = assigned c1 \<union> assigned c2" |
"assigned (WHILE b DO c) = assigned c"

theorem "\<lbrakk> (c,s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"
by(induction arbitrary: rule: big_step_induct, auto)

end
