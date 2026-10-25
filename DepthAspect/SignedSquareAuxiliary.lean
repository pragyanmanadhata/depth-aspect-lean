import DepthAspect.SignedAuxiliary
import DepthAspect.SignedStratumReindex

/-!
# The literal auxiliary terms at odd prime-square index

The hyperbolic gcds and weight-two term are evaluated before cancellation.
The elliptic zero-discriminant terms vanish after the actual stratum sieve.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- An integer congruent to two modulo four has dyadic gcd exactly two. -/
theorem gcd_two_pow_mod_four_two (a x : ℕ) (ha : 1 ≤ a) (hx : x % 4 = 2) :
    Nat.gcd (2 ^ a) x = 2 := by
  have he : x = 2 * (x / 2) := by omega
  have ho : Odd (x / 2) := Nat.odd_iff.mpr (by omega)
  conv_lhs => rw [he]
  exact gcd_two_pow_twice_odd a (x / 2) ha ho

theorem odd_square_add_one_mod_four (p : ℕ) (hp : Odd p) : (p ^ 2 + 1) % 4 = 2 := by
  have hpmod : p % 4 = 1 ∨ p % 4 = 3 := by
    have := Nat.odd_iff.mp hp
    omega
  rw [Nat.add_mod, Nat.pow_mod]
  rcases hpmod with h | h <;> norm_num [h]

/-- The three actual divisors of p² give a depth-independent hyperbolic sum. -/
theorem hyperbolic_prime_square (r h p : ℕ) (hh : 2 ≤ h)
    (hp : p.Prime) (hodd : Odd p) :
    (∑ d ∈ (p ^ 2).divisors,
      ((min d (p ^ 2 / d) : ℕ) : ℝ) ^ (r + 1) *
        (Nat.gcd (squarePart (2 ^ h)) (d + p ^ 2 / d) : ℝ)) =
      2 * (2 + (p : ℝ) ^ (r + 1)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp2 : 1 ≤ p ^ 2 := one_le_pow₀ hp.one_le
  have hquot : p ^ 2 / p = p := by rw [pow_two, Nat.mul_div_left _ hp.pos]
  have hg₁ := gcd_two_pow_mod_four_two (h / 2) (p ^ 2 + 1) (by omega)
    (odd_square_add_one_mod_four p hodd)
  have hg₂ := gcd_two_pow_twice_odd (h / 2) p (by omega) hodd
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Function.Embedding.coeFn_mk, pow_zero, pow_one,
    Nat.div_one, Nat.div_self (pow_pos hp.pos 2), hquot, min_self,
    min_eq_left hp2, min_eq_right hp2, Nat.cast_one, one_pow, one_mul,
    squarePart_two_pow, Nat.add_zero, zero_add]
  rw [show 1 + p ^ 2 = p ^ 2 + 1 by omega, hg₁,
    show p + p = 2 * p by omega, hg₂]
  push_cast
  ring

/-- Literal cancellation of every hyperbolic contribution at m=p². -/
theorem hyperbolic_prime_square_sieve (r n p : ℕ) (hn : 5 ≤ n)
    (hp : p.Prime) (hodd : Odd p) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (((∑ d ∈ (p ^ 2).divisors,
        ((min d (p ^ 2 / d) : ℕ) : ℝ) ^ (r + 1) *
          (Nat.gcd (squarePart (2 ^ (n - j))) (d + p ^ 2 / d) : ℝ)) : ℝ) : ℂ)) = 0 := by
  have heq : (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (((∑ d ∈ (p ^ 2).divisors,
        ((min d (p ^ 2 / d) : ℕ) : ℝ) ^ (r + 1) *
          (Nat.gcd (squarePart (2 ^ (n - j))) (d + p ^ 2 / d) : ℝ)) : ℝ) : ℂ)) =
      ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
        ((2 * (2 + (p : ℝ) ^ (r + 1)) : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj4 : j < 4 := Finset.mem_range.mp hj
    rw [hyperbolic_prime_square r (n - j) p (by omega) hp hodd]
  rw [heq]
  have h := alpha_affine_sieve n (by omega) (0 : ℂ)
    ((2 * (2 + (p : ℝ) ^ (r + 1)) : ℝ) : ℂ)
  simpa only [zero_mul, zero_add] using h

/-- No surviving divisor v divisible by eight can give a zero discriminant
at an odd square index. Thus H(0) is removed only after the exact sieve. -/
theorem surviving_square_discriminant_ne_zero (a p : ℕ) (ha : 3 ≤ a)
    (hodd : Odd p) (u : ℤ) :
    (((2 ^ a : ℕ) : ℤ) * u) ^ 2 - 4 * ((2 ^ a : ℕ) : ℤ) * (p : ℤ) ^ 2 ≠ 0 := by
  intro hz
  have hv : (((2 ^ a : ℕ) : ℤ)) ≠ 0 := by positivity
  have he : ((2 ^ a : ℕ) : ℤ) * u ^ 2 = 4 * (p : ℤ) ^ 2 := by
    apply mul_left_cancel₀ hv
    nlinarith [hz]
  have h8v : (8 : ℤ) ∣ ((2 ^ a : ℕ) : ℤ) := by
    have h8n : (2 : ℕ) ^ 3 ∣ 2 ^ a :=
      (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mpr ha
    norm_num only [show (2 : ℕ) ^ 3 = 8 by norm_num] at h8n
    exact_mod_cast h8n
  have h8 : (8 : ℤ) ∣ 4 * (p : ℤ) ^ 2 := by
    rw [← he]
    exact dvd_mul_of_dvd_left h8v _
  have h2 : (2 : ℤ) ∣ (p : ℤ) ^ 2 := by
    have h := h8
    change (4 : ℤ) * 2 ∣ 4 * (p : ℤ) ^ 2 at h
    exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp h
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hodd
  exact (Int.not_even_iff_odd.mpr (show Odd ((p : ℤ) ^ 2) from hpOdd.pow)) (even_iff_two_dvd.mpr h2)

/-- Every actual surviving prime-square argument is strictly negative,
so the class-number bound applies to it without an H(0) convention. -/
theorem surviving_square_discriminant_neg (n b p : ℕ) (hn : 7 ≤ n) (hb : b ≤ 4)
    (hp : 0 < p) (hodd : Odd p) (u : ℤ)
    (hu : u ∈ quotientTraces (2 ^ (n - b)) (p ^ 2)) :
    (((2 ^ (n - b) : ℕ) : ℤ) * u) ^ 2 -
      4 * ((2 ^ (n - b) : ℕ) : ℤ) * (p : ℤ) ^ 2 < 0 := by
  have hbnd := (mem_quotientTraces (2 ^ (n - b)) (p ^ 2)
    (by positivity) (by positivity) u).mp hu
  push_cast at hbnd
  have hv : (0 : ℤ) ≤ 2 ^ (n - b) := by positivity
  have hnonpos : (((2 ^ (n - b) : ℕ) : ℤ) * u) ^ 2 -
      4 * ((2 ^ (n - b) : ℕ) : ℤ) * (p : ℤ) ^ 2 ≤ 0 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hbnd hv]
  exact lt_of_le_of_ne hnonpos (surviving_square_discriminant_ne_zero (n - b) p
    (by omega) hodd u)

end DepthAspect.SignedSieve
