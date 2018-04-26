theory notDivision
  imports Complex_Main
begin

theorem notDiv: 
  fixes n a b :: int
  shows "\<not>(n dvd a*b) \<longrightarrow> \<not>(n dvd a) \<and> \<not>(n dvd b)"

proof -
  have contrapositive: " n dvd a \<or> n dvd b \<longrightarrow> n dvd a*b" by auto
  thus ?thesis using contrapositive by auto
qed
end
  
