theory Datatypes
  imports Main
begin

datatype Nat =  Zero | Succ  Nat

term "Zero" (*0*)
term "Succ (Succ Zero)"(*2*)

datatype 'a List = Nill |  Conss 'a "'a List"

term "Nill"
term "Conss (2::nat) (Conss 3 Nill)"

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

term "Leaf"
term "Node (Node Leaf 2 Leaf)  (1::nat) (Node Leaf 3 Leaf)"

datatype 'a tree' = Leaf' 'a | Node' "'a tree'" "'a tree'"

term "Node' (Node' (Leaf' (2::nat)) (Leaf' 1)) (Leaf' 3)"

end