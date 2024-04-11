theory Addition
  imports Main
begin
text \<open>Recursive definition of addition\<close>

fun Sum::"nat \<Rightarrow> nat \<Rightarrow> nat" where
"Sum 0 m = m"
| "Sum (Suc n) m = Suc (Sum n m)"

value "Sum 3 9"

text \<open>Addition basic lemma part 1, proof by induction\<close>
lemma addition_1: "Sum n 0 = n"
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


text \<open>Addition basic lemma part 2, proof by induction\<close>
lemma "Sum n (Suc m) = Suc (Sum n m)"
proof(induction n)
  case 0
  have 1: "Sum 0 (Suc m) = Suc m"
    using  Sum.simps(1)
    .

  also have 2: "... = Suc (Sum 0 m)"
    using Sum.simps(1)[symmetric]
    ..

  finally show ?case
    .

next
  case (Suc n)
  have 1: "Sum (Suc n) (Suc m) = Suc (Sum n (Suc m))"
    using Sum.simps(2)
    .

  also have 2: "... = Suc (Suc (Sum n m))"
    using Suc.IH
    ..

  also have 3: "... = Suc (Sum (Suc n) m)"
    using Sum.simps(2)[symmetric]
    ..

  finally show ?case
    .
qed

end