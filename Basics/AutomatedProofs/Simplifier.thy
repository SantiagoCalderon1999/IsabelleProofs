theory simplifier
  imports Main
begin

lemma "(5:: nat) = 2+ 3"
  by simp


(*By removing the theorem, you get bad results*)
lemma "length (xs @ ys @ zs) = length xs + length ys + length zs"
  apply(simp del: length_append)
  sorry

fun max_list:: "nat list \<Rightarrow> nat" where
  "max_list [] = 0"
| "max_list (x#xs) = (if (x \<ge> max_list xs) then x else (max_list xs))"

fun list_set::"'a list \<Rightarrow> 'a set" where
  "list_set [] = {}"
| "list_set(x#xs) = insert x (list_set xs)"

lemma "x \<in> list_set xs \<Longrightarrow> x \<le> max_list xs"
proof(induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  show ?case
  proof(cases "x = a")
    case True
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using Cons.IH Cons(2)
      by simp
  qed
qed

end