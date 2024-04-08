theory BW
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

  have 3: "Q \<longrightarrow> \<not>R"
    apply(rule implication_introduction[OF assum3])
    .

  have 4: "\<not> Q"
    apply(rule negation_introduction[OF assum2 3])
    .

  have 5: "P \<longrightarrow> \<not>Q"
    apply(rule implication_introduction[OF 4])
    .

  show "\<not> P"
    apply(rule negation_introduction[OF assum1 5])
    .
    
qed
end