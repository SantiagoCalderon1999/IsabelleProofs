theory list_recursion
  imports Main
begin

fun sum::"nat list \<Rightarrow> nat" where
  "sum [] = 0"
|  "sum (x # xs) = x + sum xs"

thm sum.simps

value "sum [1, 2, 3]"

fun append::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "append [] ys = ys"
| "append (x#xs) ys = x # (append xs ys)"

thm append.simps

value "append ([]::nat list) []"
value "append ([1,2]::nat list) [3,4]"

fun max_list:: "nat list \<Rightarrow> nat" where
  "max_list [] = 0"
| "max_list (x#xs) = (if (x \<ge> max_list xs) then x else (max_list xs))"

fun max_list2:: "nat list \<Rightarrow> nat" where
  "max_list2 [] = 0"
| "max_list2 (x#xs) = max x (max_list2 xs)"

fun max_list3:: "nat list \<Rightarrow> nat" where
  "max_list3 [] = 0"
| "max_list3 (x#xs) = (let M = max_list3 xs in (if x \<ge> M then x else M))"

value "max_list [1,2,3,3,4]"
value "max_list2 [1,2,3,3,4]"
value "max_list3 [1,2,3,3,4]"

thm max_list.simps

find_theorems "?f ?x ?y \<ge> ?x"

end