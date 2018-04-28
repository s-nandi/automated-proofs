theory neighborRelation
  imports Main
begin

text {* Idea of edge list representation taken from Nishihara and Minamide's paper:
      https://www.isa-afp.org/browser_info/current/AFP/Depth-First-Search/document.pdf *}

typedecl node 
type_synonym graph = "(node * node) list"

definition isReachable :: "[graph, node, node] ⇒ bool"
  where "isReachable g a b = (if a = b ∨ ((a, b) ∈ set g ∧ (b, a) ∈ set g) then True else False)"

theorem neighbor_reflexive:
  fixes a :: node
  fixes g :: graph
  shows "isReachable g a a" 
  by (metis isReachable_def)

theorem neighbor_symmetric:
  fixes a b :: node
  fixes g :: graph
  assumes "isReachable g a b"
  shows "isReachable g b a"
    by (metis assms isReachable_def)

theorem neighbor_not_transitive:
  shows "∃ (g :: graph) (a :: node) (b :: node) (c :: node). a ≠ b ∧ b ≠ c ∧ a ≠ c ⟶ isReachable g a b ∧ isReachable g b c ∧ ¬isReachable g a c"
proof -
  fix a b c :: node
  obtain g :: graph where G: "g = (a, b) # (b, a) # (b, c) # (c, b) # []" by auto
  show ?thesis 
  proof cases
    assume unique: "a ≠ b ∧ b ≠ c ∧ a ≠ c"

    have "(a, b) ∈ set g" and baInG: "(b, a) ∈ set g" using G by auto
    hence ab: "isReachable g a b" using isReachable_def by metis

    have "(b, c) ∈ set g" and cbInG: "(c, b) ∈ set g" using G by auto
    hence bc: "isReachable g b c" using isReachable_def by metis

    have ac: "¬ isReachable g a c" 
    proof-
      from G have "g = (a, b) # (b, a) # (b, c) # (c, b) # []" by auto
      then have "set g = {(a, b), (b, a), (b, c), (c, b)}" by auto
      then have "(a, c) ∉ set g" using unique by auto
      thus ?thesis using isReachable_def unique by auto
    qed

    show ?thesis using ab bc ac by auto
  next
    assume "~ (a ≠ b ∧ b ≠ c ∧ a ≠ c)"
    show ?thesis by auto
  qed
qed

end
