theory ex2_09 imports Main begin

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

(** see section 2.2.2 **)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma add_r[simp]: "add m (Suc n) = Suc (add m n)"
apply(induction m)
apply auto
done

theorem "itadd m n = add m n"
apply(induction m arbitrary: n)
apply auto
done

end