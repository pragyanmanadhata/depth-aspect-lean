import DepthAspect.SignedSieve
import DepthAspect.OldformTrace

/-!
# Literal auxiliary terms of the signed dyadic sieve

The weight-two correction is killed by the actual four-level coefficient
sum. At index one, the hyperbolic term is the same at all four levels.
These statements concern the literal divisor sums in the cited formula.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- The four-level sieve kills every affine function of the exponent. -/
theorem alpha_affine_sieve (n : ℕ) (hn : 3 ≤ n) (c d : ℂ) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (c * ((n - j : ℕ) : ℂ) + d)) = 0 := by
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  norm_num [Finset.sum_range_succ, Dyadic.alpha, Nat.cast_sub h1,
    Nat.cast_sub h2, Nat.cast_sub hn]
  ring

/-- The two adjacent zero-trace divisors telescope to a second difference
with step two under the four-level sieve. -/
theorem alpha_adjacent_sieve (n : ℕ) (G : ℕ → ℂ) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (G (n - j) + G (n - j - 1))) =
      G n - 2 * G (n - 2) + G (n - 4) := by
  norm_num [Finset.sum_range_succ, Dyadic.alpha, Nat.sub_sub]
  ring

/-- Combine all terms of the index-one sieve in one finite-sum identity. -/
theorem alpha_auxiliary_window_sieve (n : ℕ) (hn : 3 ≤ n) (K s w : ℂ) (G : ℕ → ℂ) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (-(K + s * (G (n - j) + G (n - j - 1))) / 2 - 1 +
        w * (((n - j : ℕ) : ℂ) + 1))) =
      -s / 2 * (G n - 2 * G (n - 2) + G (n - 4)) := by
  have hsum : (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (-(K + s * (G (n - j) + G (n - j - 1))) / 2 - 1 +
        w * (((n - j : ℕ) : ℂ) + 1))) =
      -(∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) * K) / 2 -
        s / 2 * (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
          (G (n - j) + G (n - j - 1))) -
        (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) * 1) +
        w * (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
          (((n - j : ℕ) : ℂ) + 1)) := by
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hc := alpha_affine_sieve n hn (0 : ℂ) K
  have h1 := alpha_affine_sieve n hn (0 : ℂ) 1
  have hw := alpha_affine_sieve n hn (1 : ℂ) 1
  simp only [zero_mul, zero_add] at hc h1
  simp only [one_mul] at hw
  rw [hsum, hc, h1, hw, alpha_adjacent_sieve]
  ring

/-- The literal divisor-count weight-two correction vanishes in the sieve. -/
theorem weight_two_sieve (n m : ℕ) (hn : 3 ≤ n) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (((2 ^ (n - j)).divisors.card : ℂ) *
        ((∑ d ∈ m.divisors, d : ℕ) : ℂ))) = 0 := by
  simp only [OldformTrace.two_pow_divisors_card, Nat.cast_add, Nat.cast_one]
  have h := alpha_affine_sieve n hn
    ((∑ d ∈ m.divisors, d : ℕ) : ℂ) ((∑ d ∈ m.divisors, d : ℕ) : ℂ)
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Coprimality gives the actual dyadic gcd when the second argument has
valuation one. -/
theorem gcd_two_pow_twice_odd (a u : ℕ) (ha : 1 ≤ a) (hu : Odd u) :
    Nat.gcd (2 ^ a) (2 * u) = 2 := by
  have hp : 2 ^ a = 2 * 2 ^ (a - 1) := by
    calc
      2 ^ a = 2 ^ ((a - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ac_rfl
  rw [hp, Nat.gcd_mul_left]
  have hc : Nat.Coprime (2 ^ (a - 1)) u := hu.coprime_two_left.pow_left _
  rw [hc.gcd_eq_one, mul_one]

/-- The hyperbolic divisor sum in (66) equals 2 at index one and depth≥2,
so its contribution after multiplication by −1/2 is exactly −1. -/
theorem hyperbolic_index_one (r h : ℕ) (hh : 2 ≤ h) :
    (∑ d ∈ (1 : ℕ).divisors,
      ((min d (1 / d) : ℕ) : ℝ) ^ (r + 1) *
        (Nat.gcd (squarePart (2 ^ h)) (d + 1 / d) : ℝ)) = 2 := by
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_one, min_self,
    Nat.cast_one, one_pow, one_mul, squarePart_two_pow]
  have hg := gcd_two_pow_twice_odd (h / 2) 1 (by omega) (by decide)
  norm_num only [mul_one] at hg
  exact_mod_cast hg

/-- The actual hyperbolic index-one term cancels at all four levels n≥5. -/
theorem hyperbolic_index_one_sieve (r n : ℕ) (hn : 5 ≤ n) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (((∑ d ∈ (1 : ℕ).divisors,
        ((min d (1 / d) : ℕ) : ℝ) ^ (r + 1) *
          (Nat.gcd (squarePart (2 ^ (n - j))) (d + 1 / d) : ℝ)) : ℝ) : ℂ)) = 0 := by
  have hs : (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (((∑ d ∈ (1 : ℕ).divisors,
        ((min d (1 / d) : ℕ) : ℝ) ^ (r + 1) *
          (Nat.gcd (squarePart (2 ^ (n - j))) (d + 1 / d) : ℝ)) : ℝ) : ℂ)) =
      ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) * (2 : ℂ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hyperbolic_index_one r (n - j) (by have := Finset.mem_range.mp hj; omega)]
    norm_num
  rw [hs]
  norm_num [Finset.sum_range_succ, Dyadic.alpha]


/-- The literal elliptic part before its coefficient and content reindexing. -/
noncomputable def ellipticSieve (r n m : ℕ) (H : ℤ → ℝ) : ℂ :=
  ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
    ∑ v ∈ (2 ^ (n - j)).divisors,
      ∑ t ∈ admissibleTraces (2 ^ (n - j)) v m,
        tracePolynomial (((t : ℝ) / Real.sqrt v : ℝ) : ℂ) (m : ℂ) r *
          (H (t ^ 2 - 4 * v * m) : ℂ)

/-- The literal hyperbolic contribution, including its factor −1/2. -/
noncomputable def hyperbolicSieve (r n m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
    (-(((∑ d ∈ m.divisors,
      ((min d (m / d) : ℕ) : ℝ) ^ (r + 1) *
        (Nat.gcd (squarePart (2 ^ (n - j))) (d + m / d) : ℝ)) : ℝ) : ℂ) / 2)

/-- The complete general signed expression after proving the actual
weight-two cancellation. This identity applies to every positive or zero
index; no elliptic or hyperbolic term has yet been discarded. -/
theorem newSignedExpression_elliptic_hyperbolic (r n m : ℕ) (hn : 3 ≤ n)
    (H : ℤ → ℝ) :
    newSignedExpression r (2 ^ n) m H =
      -ellipticSieve r n m H / 2 + hyperbolicSieve r n m := by
  rw [newSignedExpression_two_pow r n m hn]
  have hW := weight_two_sieve n m hn
  unfold fullSignedExpression ellipticSieve hyperbolicSieve
  push_cast at hW ⊢
  by_cases hr : r = 0
  · simp only [hr, if_true]
    simp only [mul_add, mul_sub, mul_div, mul_neg,
      Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.sum_div]
    rw [hW]
    ring
  · simp only [hr, if_false, add_zero]
    simp only [mul_sub, mul_div, mul_neg, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.sum_div]
    ring

end DepthAspect.SignedSieve
