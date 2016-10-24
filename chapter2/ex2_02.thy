theory ex2_02 imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m))"

theorem add_assoc: "add (add m n) p = add m (add n p)"
apply(induction m)
apply auto
done

lemma add_zero[simp]: "add m 0 = m"
apply(induction m)
apply auto
done

lemma add_suc[simp]: "add m (Suc n) = Suc(add m n)"
apply(induction m)
apply auto
done

theorem add_comm: "add m n = add n m"
apply(induction m)
apply auto
done

theorem add_double: "double m = add m m"
apply (induction m)
apply auto
done

end