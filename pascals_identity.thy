theory pascalsIdentity
  imports Main "HOL-Number_Theory.Number_Theory" Factorial Rat
begin

fun comb :: "nat ⇒ nat ⇒ real" where
  "comb n k = (if n < k then 0 else fact n / (fact k * fact (n - k)))"

lemma firstHalf:
  fixes n k :: nat
  assumes "n > k"
  shows "(n - k) / (fact k * fact (n - k)) = (1 / (fact k * fact (n - k - 1)))"
proof -
  have "(n - k) / (fact k * fact (n - k)) = (n - k) / fact(n - k) / fact k" by auto
  also have "(n - k) dvd fact(n - k)"
    by (simp add: Suc_leI assms dvd_fact)
  hence "(n - k) / fact(n - k) = 1 / fact(n - k - 1)"
    by (metis assms diff_is_0_eq divide_divide_eq_left divide_self_if fact_reduce not_less of_nat_eq_0_iff zero_less_diff)
  finally show ?thesis by auto
qed

lemma matchingSides: 
  fixes n k :: nat  
  assumes "n > 0 ∧ n > k ∧ k > 0"
  shows "fact (n - 1) * (1 / (fact k * fact (n - k - 1)) + 1 / (fact (k - 1) * fact (n - k))) =
                     fact (n - 1) * 1 / (fact k * fact (n - k - 1)) + fact (n - 1) * 1 / (fact (k - 1) * fact (n - k))"
  sorry

theorem pascals_identity:
  fixes n k :: nat
  assumes "n > 0 ∧ k > 0"
  shows "comb n k = comb (n - 1) (k - 1) + comb (n - 1) k" 
proof cases
  {
    assume asm: "n < k"
    then have expr1: "n - 1 < k - 1" and expr2: "n - 1 < k" 
       apply (simp add: Suc_leI assms diff_less_mono) 
      by (simp add: ‹n < k› less_imp_diff_less)  
    hence step1: "comb n k = 0" using asm by auto 
    have step2: "comb (n - 1) (k - 1) = 0" using expr1 by auto
    have step3: "comb (n - 1) k = 0" using expr2 by auto
    show ?thesis using step1 step2 step3 by auto
  }
next
  {
  assume asm1: "¬ n < k"
  hence "n ≥ k" by auto
  show ?thesis  
  proof cases
    {
      assume equality: "n = k"
      have step1: "comb n k = 1"
        using equality by auto
      also have step2: "comb (n - 1) (k - 1) = 1"
      proof -
        have "n - 1 = k - 1" using equality by auto
        thus ?thesis by auto
      qed
      also have step3: "comb (n - 1) k = 0"
      proof -
        have "n - 1 < k"
          by (simp add: assms local.equality)
        thus ?thesis by auto
      qed
      thus ?thesis using step1 step2 step3 by auto
    }
  next
    {
      assume "¬ n = k"
      hence asm2: "n > k" using asm1 by auto
  
      hence "k * fact (n - 1) / (fact k * fact (n - k)) + (n - k) * fact (n - 1) / (fact k * fact (n - k)) = 
                 (k * fact (n - 1)) / (fact k * fact (n - k)) + ((n - k) * fact (n - 1)) / (fact k * fact (n - k))" by auto
      have One: "comb n k = fact n / (fact k * fact (n - k))"
        by (simp add: asm1)
      hence two: "fact n / (fact k * fact (n - k)) = fact(n - 1) * n  / (fact k * fact (n - k))"
        by (simp add: assms fact_reduce semiring_normalization_rules(7))
      hence three: "fact(n - 1) * n  / (fact k * fact (n - k)) = fact(n - 1) * ((n - k) / (fact k * fact (n - k)) + k / (fact k * fact (n - k)))"
        by (metis (no_types, hide_lams) ‹k ≤ n› add_divide_distrib le_add_diff_inverse2 of_nat_add of_nat_fact of_nat_mult times_divide_eq_right)
      
      hence four: "fact(n - 1) * ((n - k) / (fact k * fact (n - k)) + k / (fact k * fact (n - k))) =
                    fact (n - 1) * (1 / (fact k * fact (n - k - 1)) + 1 / (fact (k - 1) * fact (n - k)))"
        by (metis ‹k ≤ n› asm2 assms diff_diff_cancel diff_less firstHalf mult.commute)
  
      have five : "comb (n - 1) (k - 1) + comb (n - 1) k =
                   fact (n - 1) / (fact (k - 1) * fact (n - k)) + fact (n - 1) / (fact k * fact (n - k - 1))"
        using Suc_leI Suc_pred' ‹k ≤ n› ‹n ≠ k› add_diff_cancel_left add_less_cancel_left asm1 assms cancel_ab_semigroup_add_class.diff_right_commute comb.elims le_antisym by force
  
      hence six: " fact (n - 1) / (fact (k - 1) * fact (n - k)) + fact (n - 1) / (fact k * fact (n - k - 1)) =
                    fact (n - 1) * 1 / (fact (k - 1) * fact (n - k)) + fact (n - 1) * 1 / (fact k * fact (n - k - 1))" by auto
  
      hence consolidatedLhs: "comb n k = fact (n - 1) * (1 / (fact k * fact (n - k - 1)) + 1 / (fact (k - 1) * fact (n - k)))" 
        using One two three four by auto
  
      hence consolidatedRhs: "comb (n - 1) (k - 1) + comb (n - 1) k = 
                              fact (n - 1) * 1 / (fact k * fact (n - k - 1)) + fact (n - 1) * 1 / (fact (k - 1) * fact (n - k))"
        using five six by auto
  
      hence joining: " fact (n - 1) * (1 / (fact k * fact (n - k - 1)) + 1 / (fact (k - 1) * fact (n - k))) = 
                       fact (n - 1) * 1 / (fact k * fact (n - k - 1)) + fact (n - 1) * 1 / (fact (k - 1) * fact (n - k))"
        using asm2 assms matchingSides by blast
  
      thus ?thesis using consolidatedLhs consolidatedRhs joining by auto
    }
qed
}
end
