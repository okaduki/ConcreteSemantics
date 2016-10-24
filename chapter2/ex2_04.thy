theory ex2_4 imports Main begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] y = [y]" |
"snoc (x#xs) y = x # snoc xs y"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x#xs) = snoc (reverse xs) x"

lemma rev_snoc[simp]: "reverse (snoc xs x) = x # (reverse xs)"
apply(induction xs)
apply auto
done

theorem "reverse (reverse xs) = xs"
apply(induction xs)
apply auto
done

end