theory FW
  imports Main
begin

lemma implication_introduction:
  "X \<Longrightarrow> (Y \<longrightarrow> X)"
  sorry

thm implication_introduction

lemma negation_introduction:
"X \<longrightarrow> Y \<Longrightarrow> X\<longrightarrow>\<not>Y \<Longrightarrow> \<not> X"
  sorry

thm negation_introduction

lemma assumes
    assum1: "P\<longrightarrow>Q"
    and assum2: " Q \<longrightarrow> R"
    and assum3: " \<not> R"
  shows " \<not> P"

proof-
  have 1:  "\<not> R"
    using assum3
    .

  have 2: "Q \<longrightarrow> R"
    using assum2
    .

  have 3: "Q \<longrightarrow> \<not> R"
    using implication_introduction[OF 1]
    .

  have 4: "\<not> Q"
    using negation_introduction[OF 2 3]
    .

  have 5: "P \<longrightarrow> \<not>Q"
    using implication_introduction[OF 4]
    .

  show ?thesis
    using negation_introduction[OF assum1 5]
    .

qed
end