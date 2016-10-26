theory ex3_08 imports Main "~~/src/HOL/IMP/AExp" "~~/src/HOL/IMP/BExp" begin

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 b) _ = b" |
"ifval (If b e1 e2) s = (if (ifval b s) then ifval e1 s else ifval e2 s)" |
"ifval (Less2 a1 a2) s = (aval a1 s < aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc b) = Bc2 b" |
"b2ifexp (Not b) = If (b2ifexp b) (Bc2 False) (Bc2 True)" |
"b2ifexp (And b1 b2) = If (b2ifexp b1) (If (b2ifexp b2) (Bc2 True) (Bc2 False)) (Bc2 False)" |
"b2ifexp (Less a1 a2) = Less2 a1 a2"

fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 b) = Bc b" |
"if2bexp (If b e1 e2) = (Not (And (Not (And (if2bexp b) (if2bexp e1))) (Not (And (Not (if2bexp b)) (if2bexp e2)))))" |
"if2bexp (Less2 a1 a2) = Less a1 a2"

theorem "bval e s = ifval (b2ifexp e) s"
apply(induction e)
apply auto
done

theorem "ifval e s = bval (if2bexp e) s"
apply(induction e)
apply auto
done

end