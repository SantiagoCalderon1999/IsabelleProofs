theory Introduction
  imports Main
begin

(*Terms*)
term "True"
term "False"
term "0::nat"
term "0::int"

(*Functions*)
term "(+)::nat \<Rightarrow> nat \<Rightarrow> nat "
term "x::(nat * int) \<Rightarrow> int"
term "fst::(nat * int \<Rightarrow> nat)"
term "snd::(nat * int \<Rightarrow> int)"

term "[]"
term "[a::nat, b, c]"
term "append::nat list \<Rightarrow> nat list \<Rightarrow> nat list"
term "append [a,b] [c]"
term "hd [a,b]"
term "tl [a,b]"

term "{}"
term "{a::nat}"
term "union"
term "s \<union> t"
term "union s t"
term "inter"
term "s \<inter> t"

term "0::nat" 
term "Suc 0"
term "Suc (Suc 0)"

term "[]"
term "Cons a []"
term "a # []"
term "a # b # c # []"

(*Logical properties*)
term "a = b"
term "a \<noteq> b"
term "a \<and> b"
term "a \<or> b"
term "a \<longrightarrow> b" (*HOL implication*)
term "a = b \<longrightarrow> [a] = [b]"

(*Theorem statements*)
lemma "A \<Longrightarrow> B \<Longrightarrow> C"
  sorry

lemma "X \<longrightarrow> Y \<Longrightarrow> X \<Longrightarrow> Y"(*Modus ponens*)
  sorry



end