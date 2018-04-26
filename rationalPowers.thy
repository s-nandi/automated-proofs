theory rationalPowers
  imports Complex_Main sqrt2Irrational
begin 

theorem ratPow:
  shows "\<exists>a b. (a\<notin>\<rat> \<and> b\<notin>\<rat>) \<longrightarrow> a powr b \<in> \<rat>"
proof cases
  assume inRat: "sqrt (real 2) powr sqrt (real 2) \<in> \<rat>"
  show ?thesis using inRat sqrt_2_irrational Rats_1 by blast 
next
  assume notRat: "\<not>(sqrt (real 2) powr sqrt (real 2) \<in> \<rat>)"
  show ?thesis using notRat sqrt_2_irrational Rats_1 by blast 
qed
end

