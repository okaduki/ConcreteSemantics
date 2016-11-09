theory ex5_04 imports Main begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0 : "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "\<not> ev (Suc (Suc (Suc 0)))" (is "\<not> ?e3")
proof
  assume ?e3 thus False
    proof cases
      assume "ev (Suc 0)" thus False
      proof cases qed
    qed
qed
end