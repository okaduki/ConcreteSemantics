theory ex5_03 imports Main begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0 : "ev 0" |
evSS: "ev n \<Longrightarrow> ev (n+2)"

lemma
  assumes a: "ev(Suc(Suc n))"
  shows "ev n"
proof -
  from assms show ?thesis
    proof cases
      case evSS then show ?thesis by simp
    qed
qed

end