theory ex4_02 imports Main begin

inductive palindrome :: "'a list \<Rightarrow> bool" where
"palindrome []" |
"palindrome [x]" |
"palindrome xs \<Longrightarrow> palindrome (a#xs@[a])"

theorem "palindrome xs \<Longrightarrow> rev xs = xs"
apply(induction xs rule: "palindrome.induct")
apply auto
done

end