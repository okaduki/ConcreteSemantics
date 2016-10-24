theory ex2_03 imports Main begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count y Nil = 0" |
"count y (x#xs) = (if x = y then 1+(count y xs) else count y xs)"

(* I cannot understand why the value is not 1*)
value "count 1 (1#2#3#[])"

theorem "count x xs \<le> length xs"
apply(induction xs)
apply auto
done

end