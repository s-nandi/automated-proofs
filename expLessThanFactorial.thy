theory expLessThanFactorial
  imports Main Complex_Main "HOL-Computational_Algebra.Computational_Algebra" Factorial
begin

fun fac :: "nat ⇒ nat"
  where "fac 0 = 1"
  |"fac i = i * (fac (i - 1))"

theorem exp_less_than_factorial[consumes 1]:
  fixes n::nat
  assumes "n ≥ 4"
  shows "n ≥ 4 ⟶ (2 ^ n ≤ fac n)" (is "?P n")
proof (induction n)
  show "?P 0" by auto
next
  fix n::nat
  assume IH:"?P n"
  show InductiveResult: "?P (Suc n)"
  proof cases
    assume greaterThanFour: "n ≥ 4"
    have baseCase: "(2 ^ n ≤ fac n)" using IH greaterThanFour by auto
    then have nextStep: "2 ^ (Suc n) ≤ fac (Suc n)"
    proof-
        have "2 * 2 ^ n <= 2 * fac n" using baseCase by auto
        also have "2 * fac n ≤ (n + 1) * fac n" using greaterThanFour by auto
        also have "2 * 2 ^ n = 2 ^ (n + 1)" by auto
        also have "(n + 1) * fac n = fac (n + 1)" by auto
        finally show ?thesis by auto
      qed
    thus ?thesis by auto
  next
    assume lessThanFour: "¬n≥4"
    show ?thesis 
    proof cases
        assume "n < 3"
        then have "Suc n < 4" by simp
        thus ?thesis using assms by auto
      next
        assume "¬n < 3"
        then have nIsThree: "n = 3" using lessThanFour by auto
        also have s1:"(16::nat) ≤ (24::nat)" by auto
        also have s2:"2^(Suc n) = (16::nat)" using nIsThree by auto
        also have s3:"fac (Suc n) = fac (4::nat)" using nIsThree by auto
        also have s4:"fac (4::nat) = (24::nat)"
          by (metis One_nat_def Suc_eq_plus1 add_2_eq_Suc' add_diff_cancel_right' distrib_left distrib_right fac.simps(1) fac.simps(2) mult_2 nat_1_add_1 numeral_2_eq_2 numeral_3_eq_3 numeral_Bit0 numeral_eq_Suc one_add_one)
        have "2 ^ (Suc n) ≤ fac (Suc n)" using s1 s2 s3 s4 by linarith
        thus ?thesis by auto
    qed
  qed
qed

end
