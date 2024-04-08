theory Successor
  imports Main
begin

thm add_Suc_right

lemma "(n::nat) + m = m + n"
proof(induction n)
  case 0

  have "0 + m = m"
    apply(subst add_0_left)
    ..

  also have "... = m + 0"
    apply(subst add_0_right)
    ..

  finally show ?case 
    .

next
  case (Suc n)

  have "Suc n + m = Suc (n + m)"
    apply(subst add_Suc)
    ..

  also have "... = Suc(m + n)"
    apply(subst Suc.IH)
    ..

  also have "... = m + Suc n"
    apply(subst add_Suc_right[symmetric])
    ..

  finally show ?case
    .
qed
end