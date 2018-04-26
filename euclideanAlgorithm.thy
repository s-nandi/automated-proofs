theory euclideanAlgorithm
  imports Complex_Main "HOL-Number_Theory.Number_Theory" GCD
begin

lemma gcd_mod:
  fixes a b :: nat
  shows "gcd a b = gcd b (a mod b)"
  by (metis gcd_red_nat)

lemma gcd_0:
  fixes a b :: nat
  shows "b = 0 ⟶ gcd a b = a" by auto

fun euclidean_algorithm :: "nat ⇒ nat ⇒ int * int" where
  "euclidean_algorithm x 0 = (x, 0)" |
  "euclidean_algorithm x y = euclidean_algorithm y (x mod y)"

lemma b_equal_at_0: 
  fixes a b :: nat
  assumes "b = 0"
  shows "fst(euclidean_algorithm a b) = gcd a b"
proof -
    have "fst(euclidean_algorithm a b) = a" using assms by auto
    also have "gcd a b = a" using assms gcd_0 by auto         
    thus "fst(euclidean_algorithm a b) = gcd a b"  by (simp add: calculation)
  qed

lemma a_equal_at_0: 
  fixes a b :: nat
  assumes "a = 0"
  shows "fst(euclidean_algorithm a b) = gcd a b"
proof -
    have "euclidean_algorithm a b = euclidean_algorithm b 0"
      by (metis assms euclidean_algorithm.elims mod_0)
    also have "gcd a b = gcd b 0" using assms gcd_mod by auto         
    thus "fst(euclidean_algorithm a b) = gcd a b"  by (simp add: calculation)
qed

theorem division_theorem: 
  fixes a b :: nat
  assumes "(b ≠ 0)"
  shows "∃ (q :: nat) (r :: nat) . (a = q * b + r) ∧ (r < b)"
proof -
  have "a = nat(a div b) * b + a mod b" by auto
  thus ?thesis
    using assms mod_less_divisor by blast
qed

theorem euclidean_algorithm_validity:
  fixes a b :: nat
  assumes "a ≥ b ∧ a ≠ 0 ∧ b ≠ 0"
  shows "fst(euclidean_algorithm a b) = gcd a b"
proof (induct "a + b" arbitrary: a b rule: less_induct)
  fix a b :: nat
  case less
  then have IH: "∀ aa bb. aa + bb < a + b ⟶ fst(euclidean_algorithm aa bb) = gcd aa bb" by simp
  thus ?case
  proof cases 
    assume nonZeros: "b ≠ 0 ∧ a ≠ 0"
    show ?thesis
    proof cases
      assume asm: "a ≥ b"
      have gcdRule: "gcd a b = gcd b (a mod b)" using gcd_mod by auto
      have euclidRule: "euclidean_algorithm a b = euclidean_algorithm b (a mod b)"
        by (metis euclidean_algorithm.elims mod_0 mod_by_0)
      have step1: "a ≥ b" using asm by auto
      have step2: "a mod b < b"
        using nonZeros by auto
      have lessThan: "b + (a mod b) < a + b" using step1 step2 by linarith
      thus ?thesis
        using IH euclidRule gcd_red_nat by auto
    next
      assume asm: "¬ a ≥ b"
      hence "a < b" by auto
      have gcdRule: "gcd b a = gcd a (b mod a)" using gcd_mod by auto
      have euclidRule: "euclidean_algorithm b a = euclidean_algorithm a (b mod a)"
        by (metis euclidean_algorithm.elims mod_0 mod_by_0)
      have step1: "b > a" using asm by auto
      have step2: "b mod a < a"
        using nonZeros by auto
      have lessThan: "a + (b mod a) < a + b" using step1 step2 by linarith
      thus ?thesis
        by (metis Divides.mod_less IH euclidRule euclidean_algorithm.elims gcd.commute gcdRule nonZeros step1)
    qed
  next
    assume "¬ (b ≠ 0 ∧ a ≠ 0)"
    hence "b = 0 ∨ a = 0" by auto
    thus ?thesis using a_equal_at_0 b_equal_at_0 by auto
  qed
qed

end
