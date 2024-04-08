theory ListSum
  imports Main
begin

fun sum:: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum ( x # xs ) = x + sum xs"

fun fold::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold f [] acc = acc"
| "fold f (x#xs) acc = fold f xs (f x acc)"

fun sum_var::"nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_var a b = a + b"

fun sum':: "nat list \<Rightarrow> nat" where
  "sum' [] = 0"
| "sum' (x#xs)  = fold sum_var xs x"

value "sum' [1, 2, 10]"

lemma "sum xs = sum' xs"
proof (induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  then show ?case
    by auto

qed
end