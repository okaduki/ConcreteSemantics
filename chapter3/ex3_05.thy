theory ex3_05 imports Main begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp2 = N int | V vname | Incr vname | Plus aexp2 aexp2

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state" where
"aval2 (N n) s = (n, s)" |
"aval2 (V x) s = (s x, s)" |
"aval2 (Incr x) s = (s x, s(x := 1 + s x))" |
"aval2 (Plus a\<^sub>1 a\<^sub>2) s = (
 let (v1,s1) = aval2 a\<^sub>1 s;
     (v2,s2) = aval2 a\<^sub>2 s1
 in (v1+v2,s2))"

value "let (v,t) = (aval2 (Plus (Incr ''x'') (Plus (V ''x'') (V ''y''))) <>) in (v, map t [''x'', ''y''])"

datatype aexp2' = N' int | V' vname | Incr' vname | Plus' aexp2' aexp2' | Div aexp2' aexp2'

fun aval2' :: "aexp2' \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2' (N' n) s = Some (n, s)" |
"aval2' (V' x) s = Some (s x, s)" |
"aval2' (Incr' x) s = Some (s x, s(x := 1 + s x))" |
"aval2' (Plus' l r) s = (
 case (aval2' l s) of
  None \<Rightarrow> None |
  Some (v1,s1) \<Rightarrow> (
   case (aval2' r s1) of
    None \<Rightarrow> None |
    Some (v2,s2) \<Rightarrow> Some (v1 + v2, s2)
   )
 )" |
"aval2' (Div l r) s = (
 case (aval2' l s) of
  None \<Rightarrow> None |
  Some (v1,s1) \<Rightarrow> (
   case (aval2' r s1) of
    None \<Rightarrow> None |
    Some (v2,s2) \<Rightarrow> if v2 = 0 then None else Some (v1 div v2, s2)
   )
 )"

value "aval2' (Div (N' 10) (V' x)) <>"
value "aval2' (Div (N' 10) (V' x)) <x := 3>"
value "aval2' (Plus' (Incr' ''x'') (Div (N' 10) (V' ''x''))) <>"

end
