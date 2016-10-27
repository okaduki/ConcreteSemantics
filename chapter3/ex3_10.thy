theory ex3_10 imports Main "~~/src/HOL/IMP/AExp" begin

datatype instr = LOADI val | LOAD vname | ADD
type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk  =  Some (n # stk)" |
"exec1 (LOAD x) s stk  =  Some (s(x) # stk)" |
"exec1  ADD s [] =  None" |
"exec1  ADD s [x] =  None" |
"exec1  ADD s (x#y#stk) =  Some ((x+y) # stk)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = (case exec1 i s stk of
 None \<Rightarrow> None |
 Some stk2 \<Rightarrow> exec is s stk2
)"

lemma exec_append[simp]:
  "exec is1 s stk = Some stk2 \<Longrightarrow> exec (is1@is2) s stk = exec is2 s stk2"
apply(induction is1 arbitrary: stk)
apply (auto)
by (metis option.case_eq_if option.distinct(1))

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x) = [LOAD x]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
apply(induction a arbitrary: stk)
apply (auto)
done

end
