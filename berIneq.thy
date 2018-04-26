theory berIneq
  imports Complex_Main
begin 

theorem BernoulliInequality:
  fixes x :: real
  fixes n:: nat
  assumes "x \<ge> -1"
  shows "(1 + x) ^ n\<ge> 1 + n*x" (is "?P n")
proof (induction n)
  show "?P 0" by auto
next
  fix n :: nat
  assume IH : "?P n"
  show "?P (Suc n)"
  proof -
    from assms have "1+x \<ge> 0" by auto
    then have start :"(1+x)*(1+x) ^ n \<ge> (1+x)*(1+n*x)" 
      proof cases
        assume "1+x = 0"
        thus ?thesis using IH  by auto
      next
        assume "\<not>(1+x=0)"
        thus ?thesis using IH assms by auto
      qed
      have "(1+x)*(1+n*x) = (1+n*x + x + n*(x ^ 2))" by algebra
      then have helper: "(1+x) ^ (1+n) \<ge> (1+n*x + x + n*(x ^ 2))" using start by auto
      have "n*(x ^ 2) \<ge> 0" by auto
      then have helper2 : "(1+n*x + x + n*(x ^ 2)) \<ge> (1+n*x + x)" by auto
      then have "(1+x) ^ (1+n) \<ge> (1+n*x + x)" using helper by linarith
      thus ?thesis
        by (smt \<open>(1 + x) * (1 + real n * x) = 1 + real n * x + x + real n * x\<^sup>2\<close> \<open>0 \<le> real n * x\<^sup>2\<close> of_nat_Suc power_Suc semiring_normalization_rules(2) start)
    qed
  qed
end
      
    
  