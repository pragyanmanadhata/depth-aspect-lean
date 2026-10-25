import DepthAspect.SignedAuxiliary
import DepthAspect.DyadicRamanujan

/-!
# The literal prime-index hyperbolic trace

The two divisors of a prime are evaluated in the general signed trace.
The even-depth second difference is the actual additive-character sum of
(79), and at odd depth the two equal pairs cancel.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- A dyadic gcd stops changing as soon as the larger power does not divide
its second argument. No factorization or positivity of that argument is needed. -/
theorem gcd_two_pow_stable (a z : ℕ) (hz : ¬ 2 ^ (a + 1) ∣ z) :
    Nat.gcd (2 ^ (a + 1)) z = Nat.gcd (2 ^ a) z := by
  obtain ⟨b, hb, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (Nat.gcd_dvd_left (2 ^ (a + 1)) z)
  have hba : b ≤ a := by
    by_contra h
    have he : b = a + 1 := by omega
    apply hz
    simpa only [hg, he] using Nat.gcd_dvd_right (2 ^ (a + 1)) z
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · rw [hg]
      exact pow_dvd_pow 2 hba
    · exact Nat.gcd_dvd_right _ _
  · exact Nat.gcd_dvd_gcd_of_dvd_left z (pow_dvd_pow 2 (by omega))

/-- Equation (79) with q=2^(a+2), including every divisibility case. -/
theorem hyperbolic_gcd_ramanujan (a z : ℕ) :
    -(Nat.gcd (2 ^ (a + 2)) z : ℂ) +
      2 * (Nat.gcd (2 ^ (a + 1)) z : ℂ) - (Nat.gcd (2 ^ a) z : ℂ) =
      -DyadicRamanujan.ramanujanTwoPow (a + 1) (z : ℤ) / 2 := by
  rw [DyadicRamanujan.ramanujanTwoPow_formula]
  have hcast (b : ℕ) : (2 : ℤ) ^ b ∣ (z : ℤ) ↔ (2 : ℕ) ^ b ∣ z := by
    exact_mod_cast (Iff.rfl : (2 : ℕ) ^ b ∣ z ↔ (2 : ℕ) ^ b ∣ z)
  simp only [hcast, show a + 1 + 1 = a + 2 by omega]
  by_cases hbig : 2 ^ (a + 2) ∣ z
  · have hhalf : 2 ^ (a + 1) ∣ z := dvd_trans (pow_dvd_pow 2 (by omega)) hbig
    have hsmall : 2 ^ a ∣ z := dvd_trans (pow_dvd_pow 2 (by omega)) hbig
    rw [if_pos hbig, if_pos hhalf, Nat.gcd_eq_left_iff_dvd.mpr hbig,
      Nat.gcd_eq_left_iff_dvd.mpr hhalf, Nat.gcd_eq_left_iff_dvd.mpr hsmall]
    push_cast
    simp only [pow_add, pow_one, pow_two]
    ring
  · have hstable := gcd_two_pow_stable (a + 1) z (by simpa using hbig)
    rw [show a + 1 + 1 = a + 2 by omega] at hstable
    rw [if_neg hbig, hstable]
    by_cases hhalf : 2 ^ (a + 1) ∣ z
    · have hsmall : 2 ^ a ∣ z := dvd_trans (pow_dvd_pow 2 (by omega)) hhalf
      rw [if_pos hhalf, Nat.gcd_eq_left_iff_dvd.mpr hhalf,
        Nat.gcd_eq_left_iff_dvd.mpr hsmall]
      push_cast
      rw [pow_succ]
      ring
    · rw [if_neg hhalf, gcd_two_pow_stable a z hhalf]
      ring

/-- The two literal divisors of a prime give the same hyperbolic summand. -/
theorem hyperbolic_prime (r h P : ℕ) (hP : P.Prime) :
    (∑ d ∈ P.divisors,
      ((min d (P / d) : ℕ) : ℝ) ^ (r + 1) *
        (Nat.gcd (squarePart (2 ^ h)) (d + P / d) : ℝ)) =
      2 * (Nat.gcd (2 ^ (h / 2)) (P + 1) : ℝ) := by
  rw [hP.divisors]
  simp only [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hP.ne_one.symm : 1 ∉ ({P} : Finset ℕ)),
    Finset.sum_singleton, Nat.div_one, Nat.div_self hP.pos,
    min_eq_left hP.one_le, min_eq_right hP.one_le, Nat.cast_one, one_pow,
    one_mul, squarePart_two_pow]
  rw [Nat.add_comm 1 P]
  ring

/-- The actual hyperbolic contribution of the four-level signed formula at
even depth, evaluated as the Ramanujan sum in (79). -/
theorem hyperbolic_prime_even_sieve (r a P : ℕ) (hP : P.Prime) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (-(((∑ d ∈ P.divisors,
        ((min d (P / d) : ℕ) : ℝ) ^ (r + 1) *
          (Nat.gcd (squarePart (2 ^ (2 * a + 4 - j))) (d + P / d) : ℝ)) : ℝ) : ℂ) / 2)) =
      -DyadicRamanujan.ramanujanTwoPow (a + 1) ((P + 1 : ℕ) : ℤ) / 2 := by
  simp only [hyperbolic_prime r _ P hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Dyadic.alpha, Nat.sub_zero,
    show (2 * a + 4) / 2 = a + 2 by omega,
    show (2 * a + 4 - 1) / 2 = a + 1 by omega,
    show (2 * a + 4 - 2) / 2 = a + 1 by omega,
    show (2 * a + 4 - 3) / 2 = a by omega]
  convert hyperbolic_gcd_ramanujan a (P + 1) using 1 <;> push_cast <;> ring

/-- At odd depth the actual four hyperbolic terms cancel in equal pairs. -/
theorem hyperbolic_prime_odd_sieve (r a P : ℕ) (hP : P.Prime) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (-(((∑ d ∈ P.divisors,
        ((min d (P / d) : ℕ) : ℝ) ^ (r + 1) *
          (Nat.gcd (squarePart (2 ^ (2 * a + 5 - j))) (d + P / d) : ℝ)) : ℝ) : ℂ) / 2)) = 0 := by
  simp only [hyperbolic_prime r _ P hP]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Dyadic.alpha, Nat.sub_zero,
    show (2 * a + 5) / 2 = a + 2 by omega,
    show (2 * a + 5 - 1) / 2 = a + 2 by omega,
    show (2 * a + 5 - 2) / 2 = a + 1 by omega,
    show (2 * a + 5 - 3) / 2 = a + 1 by omega]
  push_cast
  ring

end DepthAspect.SignedSieve
