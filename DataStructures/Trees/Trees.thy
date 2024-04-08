theory Trees
  imports Main
begin

section \<open>0. Definition of \<open>tree\<close>, \<open>tree_set\<close>, \<open>bst\<close> \<close>
text \<open>These are a set of functions defined in the lecture.\<close>

datatype 'a tree = 
  Leaf | 
  Node "'a tree" 'a "'a tree" 

fun tree_set where  
"tree_set Leaf = {}"
| "tree_set (Node l a r) = insert a (tree_set l) \<union> (tree_set r)"

fun bst where
"bst Leaf = True"
| "bst (Node l a r) = ((\<forall>x\<in>tree_set l. x < a) \<and> bst l \<and> (\<forall>x\<in>tree_set r. a < x) \<and> bst r)"

section \<open>1. Define a function \<open>mirror_tree\<close> which mirrors a given tree\<close>
text \<open>
This function is recursively defined, ensuring that the left node is exchanged with the right node
 while preserving the tree's original value. In the case of a \<open>Leaf\<close>, it is evident that mirroring
 it results in the same \<open>Leaf\<close>.\<close>

fun mirror_tree::"nat tree \<Rightarrow> nat tree" where
  "mirror_tree Leaf = Leaf"
  | "mirror_tree (Node l a r) = Node (mirror_tree r) a (mirror_tree l)"

text \<open>These are some test cases your function should pass:\<close>

value  "mirror_tree Leaf = Leaf"
value  "mirror_tree (Node Leaf 1 Leaf) = (Node Leaf 1 Leaf)"
value  "mirror_tree (Node (Node Leaf 0 Leaf) 1 Leaf) = (Node Leaf 1 (Node Leaf 0 Leaf)) \<or> 
        mirror_tree (Node (Node Leaf 0 Leaf) 1 Leaf) = (Node (Node Leaf 1 Leaf) 0 Leaf) "

section \<open>2. Show the following property of \<open>mirror_tree\<close> \<close>
text \<open>This property intuitively demonstrates that a tree, when mirrored twice, yields the same tree as the original. 
The proof involves induction, coupled with the relevant definition of \<open>mirror_tree\<close>.\<close>

lemma "mirror_tree (mirror_tree t) = t"
proof(induction t)
  case Leaf
  have 1: "mirror_tree(mirror_tree Leaf) = mirror_tree Leaf"
    apply(subst mirror_tree.simps(1))
    ..

  also have 2: "... = Leaf"
    apply(subst mirror_tree.simps(1))
    ..

  finally show ?case 
    .
next
  case (Node tl a tr)
  have 1: "mirror_tree(mirror_tree(Node tl a tr)) = mirror_tree((Node (mirror_tree tr) a (mirror_tree tl)))"
    apply(subst mirror_tree.simps(2))
    ..

  also have 2: " ... = Node (mirror_tree (mirror_tree tl)) a (mirror_tree (mirror_tree tr))"
    apply(subst mirror_tree.simps(2))
    ..
  
  also have 3: "... = Node tl a (mirror_tree (mirror_tree tr))"
    apply(subst Node.IH(1))
    ..

  also have 4: "... = Node tl a tr"
    apply(subst Node.IH(2))
    ..

  finally show ?case
    .
qed

section \<open>3. Define a function \<open>scale_tree\<close>, s.t. this function multiplies all elements of a tree by a 
given constant.\<close>
text \<open>The \<open>scale_tree\<close> function is recursively defined, considering that the scaling of a tree involves 
multiplying its own value by the scaling factor and then recursively scaling its child nodes. 
In the case of a \<open>Leaf\<close>, the result is the \<open>Leaf\<close> itself.\<close>

fun scale_tree :: "nat \<Rightarrow> nat tree \<Rightarrow> nat tree" where
  "scale_tree x Leaf = Leaf"
  | "scale_tree x (Node l a r) = Node (scale_tree x l) (a*x) (scale_tree x r)"

text \<open>These are some test cases your function should pass:\<close>

value "scale_tree 1 (Node (Node Leaf 2 Leaf) 1 Leaf) = (Node (Node Leaf 2 Leaf) 1 Leaf)"
value "scale_tree 3 (Node (Node Leaf 2 Leaf) 1 Leaf) = (Node (Node Leaf 6 Leaf) 3 Leaf)"

section \<open>4. Show the following identity relating \<open>scale_tree\<close> and \<open>mirror_tree\<close>.\<close>
text \<open>The lemma's core idea is that the operations of \<open>scale_tree\<close> and \<open>mirror_tree\<close> can be interchanged 
without altering the result. To substantiate this claim, induction is employed, along with reference to 
the definitions of \<open>scale_tree\<close> and \<open>mirror_tree\<close>.\<close>

lemma "mirror_tree (scale_tree c t) = scale_tree c (mirror_tree t)"
proof(induction t)
  case Leaf
  have 1: "mirror_tree (scale_tree c Leaf) = mirror_tree Leaf"
    apply(subst scale_tree.simps(1))
    ..

  then have 2: "... = Leaf"
    apply(subst mirror_tree.simps(1))
    ..

  have 3: "scale_tree c (mirror_tree Leaf) = scale_tree c Leaf"
    apply(subst mirror_tree.simps(1))
    ..

  then have 4: "... = Leaf"
    apply(subst scale_tree.simps(1))
    ..

  have 5: "mirror_tree (scale_tree c Leaf) = Leaf"
    apply (rule trans [OF 1 2])
    .

  have 6: "scale_tree c (mirror_tree Leaf) = Leaf"
    apply (rule trans [OF 3 4])
    .

  show ?case
    using 5 6
    ..
next
  case (Node tl a tr)
  have 1: "mirror_tree (scale_tree c (Node tl a tr)) = mirror_tree (Node (scale_tree c tl) (a*c) (scale_tree c tr))"
    apply(subst scale_tree.simps(2))
    ..

  also have 2: "... = Node (mirror_tree(scale_tree c tr)) (a*c) (mirror_tree(scale_tree c tl))"
    apply(subst mirror_tree.simps(2))
    ..

  also have 3: "... = Node (scale_tree c (mirror_tree tr)) (a*c) (mirror_tree(scale_tree c tl))"
    apply(subst Node.IH(2))
    ..

  also have 4: "... = Node (scale_tree c (mirror_tree tr)) (a*c) (scale_tree c (mirror_tree tl))"
    apply(subst Node.IH(1))
    ..

  also have 5: "... = scale_tree c (Node (mirror_tree tr) (a) (mirror_tree tl))"
    apply(subst scale_tree.simps(2)[symmetric])
    ..

  also have 6: "... = scale_tree c (mirror_tree (Node tl a tr))"
    apply(subst mirror_tree.simps(2)[symmetric])
    ..

  finally show ?case
    .
qed

section \<open>5. Define a new function \<open>add_tree\<close> that adds the elements in the tree\<close>

text \<open>The proposed \<open>add_tree\<close> function is grounded in the principle that the sum of elements
within a \<open>Leaf\<close> is \<open>0\<close>. For trees with shapes other than \<open>Leaf\<close>, their addition is determined
by the sum of their own value and the two values resulting from the addition of the trees comprising them.\<close>

fun add_tree:: "nat tree \<Rightarrow> nat" where
"add_tree Leaf = 0"
| "add_tree (Node l a r) = a + add_tree l + add_tree r"

text \<open>These are some test cases your function should pass:\<close>

value "add_tree (Node (Node Leaf 3 Leaf) 2 (Node Leaf 1 Leaf)) = 6"
value "add_tree (Node (Node Leaf 0 Leaf) 1 (Node Leaf 2 Leaf)) = 3"

section \<open>6. Show the following identity relating \<open>add_tree\<close> and \<open>mirror_tree\<close>.\<close>

text \<open>This lemma is based on the observation that the addition of elements in a tree remains 
unaffected by its mirroring. Consequently, the proof is structured as an induction, initially
leveraging the definition of \<open>mirror_tree\<close> and subsequently rearranging the elements of the equation
to demonstrate the equivalence of both sides.\<close>

lemma "add_tree (mirror_tree t) = add_tree t"
proof(induction t)
  case Leaf
  show ?case
    apply(subst mirror_tree.simps(1))
    ..
next
  case (Node tl a tr)
  have 1: "add_tree (mirror_tree(Node tl a tr)) = add_tree (Node (mirror_tree tr) a (mirror_tree tl))"
    apply(subst mirror_tree.simps(2))
    ..

  also have 2: "... = a + add_tree(mirror_tree tr) + add_tree( mirror_tree tl)"
    apply(subst add_tree.simps(2))
    ..

  also have 3: "... = a + add_tree tr + add_tree( mirror_tree tl)"
    apply(subst Node.IH(2))
    ..

  also have 4: "... = a + add_tree tr + add_tree tl"
    apply(subst Node.IH(1))
    ..

  find_theorems "?x + ?y + ?z = ?x + ?z + ?y"

  also have 5: "... = a + add_tree tl + add_tree tr"
    apply(subst  Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(23))
    ..

  also have 6: "... = add_tree(Node tl a tr)"
    apply(subst add_tree.simps(2)[symmetric])
    ..

  finally show ?case
    .
qed

section \<open>7. Show the identity of \<open>add_tree\<close> and \<open>scale_tree\<close>.\<close>

text \<open>This proof strategically employs Forward Reasoning, Backward Reasoning, and Substitution
to prove the lemma. The overarching approach involves transforming the definition of \<open>scale_tree\<close>
into a multiplication, followed by leveraging associative and distributive properties to demonstrate 
the equivalence of both sides of the equation.\<close>

lemma "add_tree (scale_tree (a + b) t) = a * (add_tree t) + b * (add_tree t)"
proof(induction t)
  case Leaf
  have 1: "add_tree (scale_tree (a + b) Leaf) = add_tree Leaf"
    apply(subst scale_tree.simps(1))
    ..

  also have 2: "... = 0"
    apply(subst add_tree.simps(1))
    ..

  have 3: "a * (add_tree Leaf) + b * (add_tree Leaf) = a * 0 + b * 0"
    apply(subst add_tree.simps(1))
    apply(subst add_tree.simps(1))
    ..

  also have 4: "... = 0"
    apply(subst Rings.mult_zero_class.mult_zero_right)
    apply(subst Rings.mult_zero_class.mult_zero_right)
    apply(subst Groups.add_0)
    ..

  find_theorems "0 + ?b"

  have 5: "add_tree (scale_tree (a + b) Leaf) = 0"
    apply (rule trans [OF 1 2])
    .

  have 6: " a * (add_tree Leaf) + b * (add_tree Leaf) = 0"
    apply (rule trans [OF 3 4])
    .

  show ?case
    using 5 6
    ..
next
  case (Node tl x tr)

  have 1: "add_tree (scale_tree (a + b) (Node tl x tr)) = add_tree ((Node (scale_tree (a+b) tl) (x*(a+b)) (scale_tree (a+b) tr)))"
    apply(subst scale_tree.simps(2))
    ..

  also have 2: "... = (x*(a+b)) + add_tree(scale_tree (a+b) tl) + add_tree(scale_tree (a+b) tr)"
    apply(subst add_tree.simps(2))
    ..

  also have 3: "... = (x*(a+b)) + (a*add_tree tl + b* add_tree tl) + (a*add_tree tr + b* add_tree tr) "
    apply(subst Node.IH(1))
    apply(subst Node.IH(2))
    ..

  find_theorems "?a * (?b + ?c)"

  also have 5: "... = x*a + x*b + (a*add_tree tl + b* add_tree tl) + (a*add_tree tr + b* add_tree tr)"
    apply(subst distrib_left)
    ..

  also have 7: "... = a*x + a*add_tree tl+ a*add_tree tr + b*x + b* add_tree tl + b* add_tree tr"
    by auto

  also have 8: "... = b*x + b*add_tree tl + b* add_tree tr + a * (x + add_tree tl + add_tree tr)"
    apply(subst distrib_left[symmetric])
    apply(subst distrib_left[symmetric])
    by auto

  also have 9: "... = a * (x + add_tree tl + add_tree tr) + b*(x + add_tree tl + add_tree tr)"
    apply(subst distrib_left[symmetric])
    apply(subst distrib_left[symmetric])
    using  Groups.ab_semigroup_add_class.add.commute
    .

  also have 9: "... = a * (add_tree(Node tl x tr)) + b * (add_tree(Node tl x tr))"
    apply(subst add_tree.simps(2)[symmetric])
    apply(subst add_tree.simps(2)[symmetric])
    ..

  finally show ?case
    .
 qed

section \<open>8. Guess the only two possible shapes of a binary search tree
whose elements add up to \<open>0\<close> \<close>

text \<open>These two values can be readily discerned through visual inspection. It is evident that a \<open>Leaf\<close>
fulfills the specified condition, establishing itself as the first shape. Furthermore, 
only trees with 0's as their associated values can yield an \<open>add_tree\<close> value of 0, given our focus on
natural numbers. Moreover, the additional constraint of the tree being a binary search tree narrows 
the possibilities, leading to the inevitable conclusion that the second shape must be a \<open>Node Leaf 0 Leaf\<close>.\<close>

definition shape1 :: "nat tree" where "shape1 =  Leaf"
definition shape2 :: "nat tree" where "shape2 = Node Leaf 0 Leaf"

section \<open>9. Show that the shapes you guessed are correct.\<close>

text \<open>This proof builds upon the earlier definitions of \<open>shape1\<close> and \<open>shape2\<close>.
The underlying strategy involves employing induction to establish that the condition is met by the \<open>Leaf\<close>
in the base case and that in the recursive step, \<open>Node Leaf 0 Leaf\<close> emerges as an inevitable solution.\<close>

lemma or_condition: "P \<or> Q \<Longrightarrow> \<not>P \<Longrightarrow> Q"
proof -
  assume 1: "P \<or> Q"
  assume 2: "\<not>P"
  show "Q"
    using 1 2 by auto
qed

lemma shows "\<lbrakk>bst t; add_tree t = 0\<rbrakk> \<Longrightarrow> t = shape1 \<or> t = shape2"
proof(induction t)
  case Leaf
  show ?case
    apply(rule disjI1)
    apply(subst shape1_def)
    apply(rule HOL.refl)
    .
next
  case (Node tl a tr)
  have 1: "add_tree(Node tl a tr) = a + add_tree tl + add_tree tr"
    apply(subst add_tree.simps(2))
    ..

  have 3: "add_tree(Node tl a tr) = 0 \<Longrightarrow> add_tree tr = 0"
    by auto
  
  have 4: "add_tree(Node tl a tr) = 0 \<Longrightarrow> add_tree tl = 0"
    by auto

  have 5: "add_tree(Node tl a tr) = 0 \<Longrightarrow> a = 0"
    by auto

  have 6: "bst(Node tl a tr) \<Longrightarrow> bst tl"
    by auto

  have 7: "bst(Node tl a tr) \<Longrightarrow> bst tr"
    by auto

  have 10: "tl = shape1 \<or> tl = shape2"
    apply(rule Node.IH(1))
    apply(rule 6 [OF Node.prems(1)])
    apply(rule 4 [OF Node.prems(2)])
    .

  have 11: "tr = shape1 \<or> tr = shape2"
    apply(rule Node.IH(2))
    apply(rule 7 [OF Node.prems(1)])
    apply(rule 3 [OF Node.prems(2)])
    .

  have 12: "a = 0"
    apply(rule 5)
    apply(rule Node.prems(2))
    .

  have 8: "bst(Node tl a tr) \<Longrightarrow> (\<forall>x\<in>tree_set tl. x < a)"
    by auto

  have 9: "bst(Node tl a tr) \<Longrightarrow> (\<forall>x\<in>tree_set tr. x > a)"
    by auto
  
  have 13: "(\<forall>x\<in>tree_set tr. x > a)"
    apply(rule 9)
    apply(rule Node.prems(1))
    .

  have 15: "(\<forall>x\<in>tree_set tl. x < a)"
    apply(rule 8)
    apply(rule Node.prems(1))
    .

  have 17: "tl = shape1"
  proof (rule ccontr)
    assume assumption: "\<not> (tl = shape1)"
    thm "assumption"
    have c_1: "tl = shape2"
      using or_condition[OF 10 assumption]
      .

    have c_2: "tree_set tl = {0}"
      apply(subst c_1)
      apply(subst shape2_def)
      apply(subst tree_set.simps(2))
      by auto

    then show False
      using 12 15 by auto    
  qed

  have 18: "tr = shape1"
  proof (rule ccontr)
    assume assumption: "\<not> (tr = shape1)"
    thm "assumption"
    have c_1: "tr = shape2"
      using or_condition[OF 11 assumption]
      .

    have c_2: "tree_set tr = {0}"
      apply(subst c_1)
      apply(subst shape2_def)
      apply(subst tree_set.simps(2))
      by auto

    then show False
      using 12 13 by auto
  qed

  have 19: "Node tl a tr = shape2"
    apply(subst 18)
    apply(subst 17)
    apply(subst 12)
    apply(subst shape1_def)
    apply(subst shape1_def)
    apply(subst shape2_def)
    ..

  show ?case  
    apply(rule disjI2)
    using 19
    .
qed
end