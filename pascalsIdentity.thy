theory pascalsIdentity
  imports Main "HOL-Number_Theory.Number_Theory" 
begin

fun comb :: "nat ⇒ nat ⇒ real" where
  "comb n k = (if n < k then 0 else fact n / (fact k * fact (n - k)))"

theorem pascals_identity:
  fixes n k :: nat
  assumes "n > 0 ∧ k > 0"
  shows "comb n k = comb (n - 1) (k - 1) + comb (n - 1) k" 
proof cases
  {
    assume nLessThank: "n < k"
    then have lessThanRule: "n - 1 < k - 1" using assms by linarith
    thus ?thesis by auto
  }
next
  {
  assume nNotLessk:"¬ n < k"
  hence "n ≥ k" by auto
  show ?thesis  
  proof cases
    {
      assume nEqualk: "n = k"
      thus ?thesis using assms by auto
    }
  next
    {
      assume "¬ n = k"
      hence nGreaterk: "n > k" using nNotLessk by auto

      have "comb n k = fact n / (fact k * fact (n - k))"
        by (simp add: nNotLessk)

      also have "fact n / (fact k * fact (n - k)) = fact(n - 1) * n  / (fact k * fact (n - k))"
        by (simp add: assms fact_reduce semiring_normalization_rules(7))

      also have "fact(n - 1) * n  / (fact k * fact (n - k)) = 
                 fact(n - 1) * ((n - k) / (fact k * fact (n - k)) + k / (fact k * fact (n - k)))"
        by (metis (no_types, hide_lams) ‹k ≤ n› add_divide_distrib le_add_diff_inverse2 of_nat_add of_nat_fact of_nat_mult times_divide_eq_right)

      also have "fact(n - 1) * ((n - k) / (fact k * fact (n - k)) + k / (fact k * fact (n - k))) =
                    fact (n - 1) * (1 / (fact k * fact (n - k - 1)) + 1 / (fact (k - 1) * fact (n - k)))"
      proof -
        have part1: " (n - k) / (fact k * fact (n - k)) = (n - k) / fact (n - k) / fact k" by auto
        have part2: "(n - k) / fact(n - k) = 1 / fact(n - k - 1)"
          by (metis ‹k ≤ n› ‹n ≠ k› diff_is_0_eq divide_divide_eq_left divide_self_if fact_reduce le_antisym nGreaterk of_nat_eq_0_iff zero_less_diff)
        have part3: "k / (fact k * fact (n - k)) =  1 / (fact (k - 1) * fact (n - k))"
          by (metis (no_types, lifting) assms divide_divide_eq_left divide_self_if fact_reduce neq0_conv of_nat_eq_0_iff)
        show ?thesis using part1 part2 part3 by auto
      qed
      
      also have "fact (n - 1) * (1 / (fact k * fact (n - k - 1)) + 1 / (fact (k - 1) * fact (n - k))) = 
                       fact (n - 1) * 1 / (fact k * fact (n - k - 1)) + fact (n - 1) * 1 / (fact (k - 1) * fact (n - k))"
      proof -
        show ?thesis sorry
      qed

      also have "fact (n - 1) * 1 / (fact k * fact (n - k - 1)) + fact (n - 1) * 1 / (fact (k - 1) * fact (n - k)) =
                fact (n - 1) / (fact k * fact (n - k - 1)) + fact (n - 1) / (fact (k - 1) * fact (n - k))"
        by auto

      also have "fact (n - 1) / (fact k * fact (n - k - 1)) + fact (n - 1) / (fact (k - 1) * fact (n - k)) =
                 comb (n - 1) (k - 1) + comb (n - 1) k"
        using ‹n ≠ k› assms nNotLessk by auto

      finally show ?thesis by auto
    }
qed
}
end
