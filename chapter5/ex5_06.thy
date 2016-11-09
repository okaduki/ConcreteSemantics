theory ex5_06 imports Main "~~/src/HOL/IMP/Star" begin

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x#xs) = insert x (elems xs)"

theorem "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof -
  assume "x \<in> elems xs" thus "\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof(induction arbitrary: x rule: elems.induct)
    fix x
    show "x \<in> elems [] \<Longrightarrow> \<exists>ys zs. [] = ys @ x # zs \<and> x \<notin> elems ys" by simp
  next
    fix x xs xa
    assume a1: "(\<And>a. a \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ a # zs \<and> a \<notin> elems ys)" and
           a2: "xa \<in> elems (x # xs)"
    thus "\<exists>ys zs. x # xs = ys @ xa # zs \<and> xa \<notin> elems ys"
    proof(cases "x = xa")
      assume "x = xa"
      hence "x # xs = [] @ xa # xs \<and> xa \<notin> elems []" by auto
      thus "\<exists>ys zs. x # xs = ys @ xa # zs \<and> xa \<notin> elems ys" by blast
    next
      assume "x \<noteq> xa"
      moreover obtain yss zss where "xs = yss @ xa # zss \<and> xa \<notin> elems yss"
        using calculation a1 a2 by fastforce 
      hence "x # xs = (x#yss) @ xa # zss \<and> xa \<notin> elems (x#yss)"
        using calculation by auto 
      thus "\<exists>ys zs. x # xs = ys @ xa # zs \<and> xa \<notin> elems ys" by blast
    qed
  qed
qed

end
