theory Addition
  imports Main
begin
text \<open>Recursive definition of addition\<close>

fun Sum::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"Sum 0 m = m"
| "Sum (Suc n) m = Suc (Sum n m)"

value "Sum 3 9"

text \<open>Addition basic theorem\<close>
lemma "Sum n 0 = n"
proof(induction n)
  case 0
  have 1: "Sum 0 0 = 0"
    using  Sum.simps(1)
    .

  show ?case
    using 1
    .
next
  case (Suc n)
  have 1: "Sum (Suc n) 0 = Suc(Sum n 0)"
    using Sum.simps(2)
    .

  also have 2: "... = Suc n"
    using Suc.IH
    ..

  finally show ?case
    .
qed

end