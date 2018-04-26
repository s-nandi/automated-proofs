theory sqrt2Irrational
  imports Complex_Main "HOL-Number_Theory.Number_Theory"
begin

theorem sqrt_2_irrational:
  shows "(sqrt (real 2)) ∉ ℚ"
proof
  {
    assume "sqrt (real 2) ∈ ℚ"
    then obtain m n :: nat 
      where nIsNotZero: "n ≠ 0" 
        and rationalDefinition: "¦sqrt (real 2)¦ = real m / real n"
        and gcdIsOne: "gcd m n = (1::nat)" by (rule Rats_abs_nat_div_natE)
  
    hence contradiction: "2 * n^2 = m^2"
    proof -
      {
        from nIsNotZero and rationalDefinition have "sqrt (2) * (n) = (m)" by simp
        then have "(m^2) = (sqrt (2))^2 * (n^2)" by (metis of_nat_power power_mult_distrib)
        also have "(sqrt 2)^2 = 2" by simp
        finally show ?thesis by arith
      }
    qed
  
    hence showDivisibility: "2 dvd n ∧ 2 dvd m"
    proof -
      {
        from contradiction have "2 dvd m^2" by arith
        then have mdiv: "2 dvd m" by simp
        then obtain k where "m = 2 * k" ..

        also with contradiction have "2 * n^2 = 2^2 * k^2" by (auto)
        then have "n^2 = 2 * k^2" by simp
        then have "2 dvd n^2" by arith
        then have ndiv: "2 dvd n" by simp

        show ?thesis by (simp add: mdiv ndiv)
      }
    qed

    have gcdEven: "2 dvd (gcd n m)" by (simp add: showDivisibility)    
    have gcdOdd: "¬(2 dvd (gcd n m))" by (simp add: gcd.commute gcdIsOne)
    show False using gcdEven gcdOdd by auto
  }
qed

end
