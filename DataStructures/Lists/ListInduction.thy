theory ListInduction
  imports Main
begin

thm append.simps

(*Proving association in append*)

lemma "(xs @ ys) @ zs = xs @ (ys @ zs)"
proof(induction xs)
  case Nil
  have "([] @ ys) @ zs = ys @ zs"
    apply(subst append.simps)
    ..

  also have "... = [] @ (ys @ zs)"
    apply(subst append.simps)
    ..

  finally show ?case 
    .

next
  case (Cons a xs)
  have "((a # xs) @ ys) @ zs = (a#(xs@ys))@zs"
    apply(subst append.simps)
    ..

  also have "... = a#((xs@ys)@zs)"
    apply(subst append.simps)
    ..

  also have "... = a#(xs@(ys@zs))"
    apply(subst Cons.IH)
    ..

  also have "... = (a#xs)@ys@zs"
    apply(subst append.simps)
    ..

  finally show ?case
    .
qed

end