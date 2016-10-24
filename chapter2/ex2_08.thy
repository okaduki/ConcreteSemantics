theory ex2_8 imports Main begin

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse _ [] = []" |
"intersperse _ [x] = [x]" |
"intersperse c (x#xs) = x # c # intersperse c xs"

value "intersperse 0 [1,2,3]"

theorem "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs rule: intersperse.induct)
apply auto
done

end