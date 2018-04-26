theory sumOfFirstN
  imports Main
begin

theorem sum_of_first_n:
  shows "(∑i::nat = 0..n. i) = (n * (n + 1)) div 2" (is "?P n")
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  thus ?case by simp
qed

end
