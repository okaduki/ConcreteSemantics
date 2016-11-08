theory ex4_07 imports Main "~~/src/HOL/IMP/ASM" begin

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
 "ok n [] n" |
 "ok (n+1) cs n' \<Longrightarrow> ok n (LOADI _ # cs) n'" |
 "ok (n+1) cs n' \<Longrightarrow> ok n (LOAD _ # cs) n'" |
 "\<lbrakk> n \<ge> 2; ok (n-1) cs n' \<rbrakk> \<Longrightarrow> ok n (ADD # cs) n'"

declare ok.intros[simp,intro]

theorem "\<lbrakk> ok n is n'; length stk = n \<rbrakk> \<Longrightarrow> length (exec is s stk) = n'"
by (induction arbitrary: stk rule: ok.induct, auto)


lemma length_of_compiled: "length (exec (comp a) s stk) = length stk + 1"
by(induction a arbitrary: s stk, auto)

lemma append_coms: "\<lbrakk> ok n1 is1 n2; ok n2 is2 n3 \<rbrakk> \<Longrightarrow> ok n1 (is1@is2) n3"
by(induction rule: ok.induct, auto)

theorem "ok n (comp a) (n+1)"
apply(induction a arbitrary: n rule: comp.induct)
apply auto 
by (metis One_nat_def Suc_eq_plus1 add_Suc_right add_diff_cancel_right' add_leD2 append_coms comp.simps(3) numeral_2_eq_2 ok.intros(1) ok.intros(4) order_refl)

end