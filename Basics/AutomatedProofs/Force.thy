theory force
  imports Main
begin

fun max_list:: "nat list \<Rightarrow> nat" where
  "max_list [] = 0"
| "max_list (x#xs) = (if (x \<ge> max_list xs) then x else (max_list xs))"

fun list_set::"'a list \<Rightarrow> 'a set" where
  "list_set [] = {}"
| "list_set(x#xs) = insert x (list_set xs)"


lemma "x \<in> list_set xs \<Longrightarrow> x \<le> max_list xs"
  apply(induction xs)
  apply force
  apply force
  .

lemma "x \<in> list_set xs \<Longrightarrow> x \<le> max_list xs"
  apply(induction xs)
  apply fastforce
  apply fastforce
  .

end