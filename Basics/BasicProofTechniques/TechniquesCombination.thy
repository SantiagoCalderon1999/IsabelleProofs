theory TechniquesCombination
imports Main
begin

lemma impI: assumes "P"
  shows "Q \<Longrightarrow> P"
  sorry

lemma lem2: assumes "(Q \<Longrightarrow> R)"
  assumes "(Q \<Longrightarrow> \<not>R)"
  shows "\<not>Q"
  sorry

lemma lem3:
  assumes "(Q \<Longrightarrow> \<not>R)"
  shows "\<not>Q"
  sorry

thm impI

lemma assumes assum1:  "P \<Longrightarrow> Q"
  assumes assum2: "Q \<Longrightarrow> R"
  shows "\<not> R \<Longrightarrow> \<not>P"

proof-
  assume 1: "\<not>R"
  have 2: "Q \<Longrightarrow> R"
    using assum2
    .

  find_theorems "?P \<Longrightarrow> (?Q \<Longrightarrow> ?P)"

  have 3: "Q \<Longrightarrow> \<not>R"
    using impI[OF 1]
    .

(*Forward reasoning*)
  have 4: "\<not>Q"
    using lem2[where ?Q = Q and ?R = R, OF 2 3]
    .
(*Backwards reasoning*)
  have 5: "\<not>Q"
  thm lem3
    apply(rule lem3)
  using 3
  .

  have 6: "P \<Longrightarrow> \<not>Q"
    using impI[where ?P = "\<not>Q" and ?Q = P, OF 4]
    .

  have 7: "\<not>P"
    using lem3[where ?R = Q and ?Q = P, OF 5]
    .

  show "\<not>P"
    using 7
    .
qed

lemma assumes assum1: "b = a"
  assumes assum2: "a \<and> c"
  shows "b \<and> c"

proof-
  have "b\<and>c"
    apply(subst assum1)
    using assum2
    .