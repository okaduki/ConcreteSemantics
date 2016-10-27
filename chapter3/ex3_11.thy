theory ex3_11 imports Main "~~/src/HOL/IMP/AExp" begin

type_synonym reg = nat
datatype instr = LDI int reg | LD vname reg | ADD reg reg
type_synonym reg_st = "reg \<Rightarrow> int"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> reg_st \<Rightarrow> reg_st" where
"exec1 (LDI n r) _ f =  f(r := n)" |
"exec1 (LD x r) s f = f(r := s x)" |
"exec1 (ADD r1 r2) _ f = f(r1 := f r1 + f r2)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> reg_st \<Rightarrow> reg_st" where
"exec [] _ f = f" |
"exec (i#is) s f = exec is s (exec1 i s f)"

lemma exec_append[simp]:
  "exec (is1@is2) s f = exec is2 s (exec is1 s f)"
apply(induction is1 arbitrary: s f)
apply (auto)
done

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
"comp (N n) r = [LDI n r]" |
"comp (V x) r = [LD x r]" |
"comp (Plus e\<^sub>1 e\<^sub>2) r = comp e\<^sub>1 r @ comp e\<^sub>2 (r+1) @ [ADD r (r+1)]"

lemma[simp]: "r' < r \<Longrightarrow> exec (comp a r) s rs r' = rs r'"
apply(induction a arbitrary: rs r)
apply auto
done

theorem exec_comp: "exec (comp a r) s rs r = aval a s"
apply(induction a arbitrary: s rs r)
apply (auto)
done

end