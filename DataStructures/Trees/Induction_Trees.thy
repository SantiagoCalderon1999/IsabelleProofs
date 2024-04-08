theory Induction_Trees
  imports Main
begin

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"
definition tree_eg where "tree_eg \<equiv> Node (Node Leaf 1 (Node Leaf 2 Leaf)) (4::nat) (Node
Leaf 3 Leaf)"

fun tree_set::"'a tree \<Rightarrow> 'a set" where
  "tree_set Leaf = {}"
  | "tree_set (Node l a r) = insert a ((tree_set l) \<union> (tree_set r))"
value "tree_set tree_eg"

fun inorder::"'a tree \<Rightarrow> 'a list" where
  "inorder Leaf = []"
  | "inorder (Node l a r) = (inorder l) @ [a] @ (inorder r)"
value "inorder tree_eg"

term set
thm set_simps

lemma "set (inorder t) = tree_set t"
proof(induction t)
  case Leaf
  then show ?case
    by auto
next
  case (Node t1 x2 t2)
  thm Node.IH

  then show ?case
    by auto
qed


end