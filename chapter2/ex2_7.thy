theory ex2_7 imports Main begin

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip v) = Tip v" |
"mirror (Node l v r) = Node (mirror r) v (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list"  where
"pre_order (Tip v) = [v]" |
"pre_order (Node l v r) = v # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip v) = [v]" |
"post_order (Node l v r) = (post_order l) @ (post_order r) @ [v]"

value "pre_order (Node (Tip 2) 1 (Node (Tip 4) 3 (Tip 5)))"
value "post_order (Node (Tip 2) 1 (Node (Tip 4) 3 (Tip 5)))"

theorem "pre_order (mirror t) = rev (post_order t)"
apply(induction t)
apply auto
done

end