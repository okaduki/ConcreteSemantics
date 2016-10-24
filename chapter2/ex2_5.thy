theory ex2_5 imports Main begin

fun sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = Suc n + sum n"

theorem "sum n = n * (n+1) div 2"
apply(induction n)
apply auto
done

end