theory ex3_12 imports Main "~~/src/HOL/IMP/AExp" begin

type_synonym reg = nat
datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg
type_synonym reg_st = "reg \<Rightarrow> int"

fun exec1 :: "instr0 \<Rightarrow> state \<Rightarrow> reg_st \<Rightarrow> reg_st" where
"exec1 (LDI0 n) _ f =  f(0 := n)" |
"exec1 (LD0 x) s f = f(0 := s x)" |
"exec1 (MV0 r) _ f = f(r := f 0)" |
"exec1 (ADD0 r) _ f = f(0 := f r + f 0)"

fun exec :: "instr0 list \<Rightarrow> state \<Rightarrow> reg_st \<Rightarrow> reg_st" where
"exec [] _ f = f" |
"exec (i#is) s f = exec is s (exec1 i s f)"

lemma exec_append[simp]:
  "exec (is1@is2) s f = exec is2 s (exec is1 s f)"
apply(induction is1 arbitrary: s f)
apply (auto)
done

(* "comp a r" uses temporary register r' where r' > r *)
fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp (N n) r = [LDI0 n]" |
"comp (V x) r = [LD0 x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) r = comp e\<^sub>1 r @ [MV0 (r+1)] @ comp e\<^sub>2 (r+1) @ [ADD0 (r+1)]"

lemma[simp]: "\<lbrakk> r' \<noteq> 0; r' \<le> r \<rbrakk> \<Longrightarrow> exec (comp a r) s rs r' = rs r'"
apply(induction a arbitrary: rs r)
apply auto
done

theorem exec_comp: "exec (comp a r) s rs 0 = aval a s"
apply(induction a arbitrary: s rs r)
apply (auto)
done

end