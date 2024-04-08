theory Case
  imports Main
begin

lemma lemma4: "a \<le> b \<Longrightarrow> Suc a \<le> Suc b"
  sorry

lemma lemma1: "a \<ge> b \<Longrightarrow> (Suc a) - b = Suc(a - b)"
  sorry

lemma "(x::nat) - y \<le> x"
proof(induction x)
  case 0

  have "0 -y = 0"
    using zero_diff
    .

  also have "... \<le> 0"
    using order.refl
    .

  finally show ?case
    .
next
  case (Suc x)
  show ?case
  proof(cases "x \<ge> y")
    case True
    have 1: "(Suc x) - y = Suc (x - y)"
      using Suc_diff_le[OF True]
      .

    have 2: "Suc x - y \<le> Suc x - y"
      using order.refl
      .

    then have 3: "Suc x - y \<le> Suc (x - y)"
      using 2
      apply(subst 1[symmetric])
      .

    also have "... \<le> Suc x"
      using lemma4[OF Suc.IH]
      .

    finally show ?thesis
      .

  next
    case False

    have 1: "x < y"
      using not_le_imp_less[OF False]
      .

    have 2: "Suc x \<le> y"
      using Suc_leI[OF 1]
      .

    have 3: "Suc x - y = 0"
      using diff_is_0_eq'[OF 2]
      .

    have 4: "0 \<le> Suc x"
      using zero_le
      .

    show ?thesis
      using 4
      apply(subst 3)
      .
  qed
qed

end