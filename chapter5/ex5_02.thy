theory ex5_02 imports Main begin

lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof(cases "even (length xs)")
  assume "even (length xs)"
  let ?n = "length xs"
  let ?n2 = "?n div 2"
  let ?ys = "take ?n2 xs"
  let ?zs = "drop ?n2 xs"
  have "xs = ?ys @ ?zs" by auto
  moreover have "length ?ys = length ?zs"
    proof -
      have "2 * (length xs div 2) = length xs"
        by (meson \<open>even (length xs)\<close> even_two_times_div_two)
      then show ?thesis
        by (metis (no_types) add_diff_cancel_right' append_eq_conv_conj length_append length_drop length_take mult_2)
    qed
  then show ?thesis using calculation by blast 
next
  assume "odd (length xs)"
  let ?n = "length xs"
  let ?n2 = "?n - ?n div 2"
  let ?ys = "take ?n2 xs"
  let ?zs = "drop ?n2 xs"
  have "xs = ?ys @ ?zs" by auto
  moreover have "length ?ys = length ?zs + 1"
    proof -
      have "2 * (length xs div 2) + 1 = length xs"
        using \<open>odd (length xs)\<close> odd_two_times_div_two_succ by blast
      then show ?thesis
        by simp
    qed 
  then show ?thesis using calculation by blast
qed

end