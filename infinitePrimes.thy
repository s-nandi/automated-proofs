theory infinitePrimes
  imports Main "HOL-Number_Theory.Number_Theory"
begin

definition primeNat :: "nat => bool"
  where "primeNat p = (1 < p ∧ (∀m. m dvd p ⟶ m = 1 ∨ m = p))"

theorem infinite_primes: "~ finite {p::nat. primeNat p}"
proof cases
  assume finitePrimes: "finite {p::nat. p ≥ 2 ∧ primeNat p}"

  then have biggerThanPrimes:"∃ bigger. (ALL x: {(p::nat). primeNat p}. x <= bigger)"
    by (metis (no_types, lifting) Collect_cong primeNat_def prime_ge_2_nat prime_nat_iff primes_infinite)

  then obtain bigger :: nat where "ALL (x :: nat). primeNat x ⟶ x ≤ bigger"
    using finite_nat_set_iff_bounded_le primes_infinite by blast

  have False
    by (metis (no_types, lifting) Collect_cong finitePrimes primeNat_def prime_ge_2_nat prime_nat_iff primes_infinite)
  thus ?thesis by auto
next
  assume "¬finite {p::nat. p ≥ 2 ∧ primeNat p}"
  thus ?thesis by auto
qed

end
