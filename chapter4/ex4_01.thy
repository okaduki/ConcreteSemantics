theory ex4_01 imports Main begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l x r) = set l \<union> {x} \<union> set r"

value "set (Node (Node Tip 1 Tip) 2 (Node Tip 1 Tip))"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l x r) = ((\<forall>lv \<in> (set l). (lv < x)) \<and> (\<forall>rv \<in> (set r). (rv > x)))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l v r) = (
 if x < v then Node (ins x l) v r
 else if x > v then Node l v (ins x r)
 else Node l v r
)"

theorem[simp]: "set (ins x t) = {x} \<union> set t"
apply (induction t)
apply auto
done

theorem "ord t \<Longrightarrow> ord (ins i t)"
apply(induction t)
apply auto
done

end