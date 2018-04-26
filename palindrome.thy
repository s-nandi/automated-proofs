theory palindrome
  imports Main
begin

datatype 'a palindrome = Nil | Merge "'a palindrome" "'a palindrome"

fun left :: "'a palindrome ⇒ 'a palindrome" where
  "left Nil = Nil" |
  "left (Merge l r) = l"

fun right :: "'a palindrome ⇒ 'a palindrome" where
  "right Nil = Nil" |
  "right (Merge l r) = r"

fun reversed :: "'a palindrome ⇒ 'a palindrome" where
  "reversed Nil = Nil" |
  "reversed (Merge l r) = Merge (reversed r) (reversed l)"

fun connect :: "'a palindrome ⇒ 'a palindrome ⇒ 'a palindrome"  where
 "connect Nil nw = Nil" |
 "connect (Merge l r) m = Merge (Merge l m) (Merge (reversed m) (reversed l))"

lemma double_reverse: "reversed (reversed a) = a"
  apply (induct_tac a)
  apply (auto)
  done

lemma reversed_commutativity: 
  assumes "reversed a = b"
  shows "reversed b = a"

proof (cases "a")
  case (Merge l r)
  then have  "b = Merge (reversed r) (reversed l)" using assms by simp
  then have "reversed b = Merge (reversed (reversed l)) (reversed (reversed r))" by auto
  then have "reversed b = Merge l r" using double_reverse by auto
  thus ?thesis using Merge by auto
next 
  case Nil
  then have "reversed a = Nil" by auto
  then have "b = Nil" using assms by auto
  then have "reversed b = Nil" by auto
  thus ?thesis using local.Nil by simp
qed

theorem palindrome_is_symmetric:
  fixes a b
  assumes "p = connect a b"
  shows "reversed (right p) = left p"

proof (cases "a")
  case (Merge l r)
    from assms have "p = connect a b" by auto
    then have "p = Merge (Merge l b) (Merge (reversed b) (reversed l))" by (simp add: Merge)
    also have "reversed (Merge l b) = Merge (reversed b) (reversed l)" by auto
    then have "reversed (left p) = right p" by (simp add: calculation)
    then have "reversed (right p) = left p" using reversed_commutativity by auto
    thus ?thesis by auto
  next
    case Nil
    then have "p = Nil" using assms by auto
    then have "left p = Nil" and "right p = Nil" and "reversed (right p) = Nil" by auto
    thus ?thesis by auto
 qed

end
    
  
