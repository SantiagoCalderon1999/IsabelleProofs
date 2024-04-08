theory auto
  imports Main
begin

lemma "(5:: nat) = 2+ 3"
  by simp

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
    by auto
next
  case (Cons a xs)
  then show ?case
    by auto
qed

lemma "x \<in> list_set xs \<Longrightarrow> x \<le> max_list xs"
  apply(induction xs)
  apply auto
  .



end