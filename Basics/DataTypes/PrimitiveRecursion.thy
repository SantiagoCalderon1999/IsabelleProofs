theory PrimitiveRecursion
  imports Main
begin

datatype Nat = Zero | Succ Nat
term "Zero"
term "Succ (Succ Zero)"

datatype 'a List = Nill | Conss 'a "'a List"
term "Nill"
term "Conss (2::nat) (Conss 3 Nill)"

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

datatype 'a tree' = 
  Leaf' 'a 
  | Node' "'a tree'" "'a tree'"

term "Node'(Node'(Leaf'(2::nat)) (Leaf' 1)) (Leaf' 3)"
end