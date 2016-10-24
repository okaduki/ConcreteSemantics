theory ex2_11 imports Main begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var v = v" |
  "eval (Const i) _ = i" |
  "eval (Add e1 e2) v = eval e1 v + eval e2 v" |
  "eval (Mult e1 e2) v = eval e1 v * eval e2 v"

fun evalp_sub :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "evalp_sub [] _ _ = 0" |
  "evalp_sub (p#ps) x ith = p * (x ^ ith) + evalp_sub ps x (Suc ith)"
fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp xs v = evalp_sub xs v 0"

value "evalp [4,2,-1,3] 2"

fun add_p :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "add_p [] ys = ys" |
  "add_p xs [] = xs" |
  "add_p (x#xs) (y#ys) = (x+y)#(add_p xs ys)"
fun mult_p :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mult_p [] ys = []" |
  "mult_p xs [] = []" |
  "mult_p (x#xs) ys = add_p (map (\<lambda>a. a*x) ys) (mult_p xs (0#ys))"
fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0,1]" |
  "coeffs (Const i) = [i]" |
  "coeffs (Add e1 e2) = add_p (coeffs e1) (coeffs e2)" |
  "coeffs (Mult e1 e2) = mult_p (coeffs e1) (coeffs e2)"

value "evalp (coeffs (Mult Var Var)) (-2)"
value "eval (Mult Var Var) (-2)"

(*----------------------*)

lemma add_poly: "evalp_sub (add_p p1 p2) x px = evalp_sub p1 x px + evalp_sub p2 x px"
apply (induct p1 p2 arbitrary: px rule: "add_p.induct")
apply (auto simp add: algebra_simps)
done

lemma mult_const: "evalp_sub (map (\<lambda>a. a * const) ps) x px = const * (evalp_sub ps x px)"
apply (induct ps arbitrary: const x px)
apply (auto simp add: algebra_simps)
done

lemma unfold_poly: "evalp_sub ps x (Suc px) = x * (evalp_sub ps x px)"
apply (induct ps arbitrary: px)
apply (auto simp add: algebra_simps)
done

lemma mult_poly: "evalp_sub (mult_p p1 p2) x 0 = evalp_sub p1 x 0 * evalp_sub p2 x 0"
apply (induct p1 p2 rule: mult_p.induct)
apply (auto simp add: add_poly mult_const)
apply (simp add: algebra_simps)
apply (simp add: unfold_poly)
done


theorem th_2_11: "evalp (coeffs e) x = eval e x"
apply(induct e)
apply (auto simp add: add_poly mult_poly)
done

end