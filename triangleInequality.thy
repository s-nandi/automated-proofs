theory triangleInequality
  imports Complex_Main
begin

theorem triangle_inequality:
  fixes x y :: real
  shows "abs x + abs y ≥ abs(x + y)"
proof cases
  {
    assume xGreater: "x ≥ 0"
    show ?thesis proof cases
      {
        assume yGreater: "y ≥ 0"
        show ?thesis by simp
      next      
        assume yLess: "¬(y ≥ 0)"
        show ?thesis by simp
      }
    qed

  next
    assume xLess: "¬(x ≥ 0)"
    show ?thesis proof cases
      {
        assume yGreater: "y ≥ 0"
        show ?thesis by simp
      next
        assume yLess: "¬(y ≥ 0)"
        show ?thesis by simp
      }
    qed
  }
qed

end




