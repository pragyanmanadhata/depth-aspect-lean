import DepthAspect.SignedPrimeAuxiliary
import DepthAspect.PrimePowerApplications
import DepthAspect.MartinDimension

/-! The literal hyperbolic contribution in (114). The finite divisor sum
is evaluated internally at primes, bounded at the four dyadic levels,
and then summed with the already proved Chebyshev partial summation. -/
namespace DepthAspect.SignedSieve
open scoped BigOperators
open PrimePowerApplications

/-- The square part at every lower level is at most the square root of N. -/
theorem lower_squarePart_bound (n j : ℕ) :
    ((2 ^ ((n - j) / 2) : ℕ) : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ n) := by
  push_cast
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem alpha_norm_le_one (j : ℕ) (hj : j ∈ Finset.range 4) :
    ‖(Dyadic.alpha j : ℂ)‖ ≤ 1 := by
  have hj' := Finset.mem_range.mp hj
  interval_cases j <;> norm_num [Dyadic.alpha]

/-- A direct bound on the literal four-level hyperbolic term. The odd-depth
exact cancellation is proved separately; this uniform bound suffices for
(114) at both parities. -/
theorem hyperbolicSieve_prime_bound (r n p : ℕ) (hp : p.Prime) :
    ‖hyperbolicSieve r n p‖ ≤ 4 * Real.sqrt ((2 : ℝ) ^ n) := by
  unfold hyperbolicSieve
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range 4, Real.sqrt ((2 : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [hyperbolic_prime r (n - j) p hp]
      have he : -(((2 * (Nat.gcd (2 ^ ((n - j) / 2)) (p + 1) : ℝ) : ℝ) : ℂ)) / 2 =
          -(Nat.gcd (2 ^ ((n - j) / 2)) (p + 1) : ℂ) := by push_cast; ring
      rw [he, norm_mul, norm_neg, Complex.norm_natCast]
      calc
        _ ≤ 1 * (Nat.gcd (2 ^ ((n - j) / 2)) (p + 1) : ℝ) :=
          mul_le_mul_of_nonneg_right (alpha_norm_le_one j hj) (Nat.cast_nonneg _)
        _ ≤ ((2 ^ ((n - j) / 2) : ℕ) : ℝ) := by
          rw [one_mul]
          exact_mod_cast Nat.le_of_dvd (by positivity : 0 < 2 ^ ((n - j) / 2))
            (Nat.gcd_dvd_left (2 ^ ((n - j) / 2)) (p + 1))
        _ ≤ _ := lower_squarePart_bound n j
    _ = _ := by simp

/-- Actual spectral normalization of the hyperbolic summand. A unit root
sign can be multiplied back in without changing its norm. -/
noncomputable def normalizedHyperbolic (r n : ℕ) (d : ℝ) (p : ℕ) : ℂ :=
  hyperbolicSieve r n p / ((d * (p : ℝ) ^ (((r : ℝ) + 1) / 2) : ℝ) : ℂ)

/-- The pointwise bound needed in (114), with the literal dimension
normalization and an explicit constant independent of depth. -/
theorem normalizedHyperbolic_prime_bound (r n p : ℕ) (hp : p.Prime) (d : ℝ)
    (hd : ((r : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d) :
    ‖normalizedHyperbolic r n d p‖ ≤
      (256 / ((r : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) *
        (p : ℝ) ^ (-((r : ℝ) + 1) / 2) := by
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hr : 0 < (r : ℝ) + 1 := by positivity
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs := Real.sqrt_pos.mpr hN
  have hfrac : 4 * Real.sqrt ((2 : ℝ) ^ n) / d ≤
      256 / ((r : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n) := by
    rw [div_div]
    apply (div_le_div_iff₀ hd0 (mul_pos hr hs)).mpr
    calc
      _ = 4 * ((r : ℝ) + 1) * (2 : ℝ) ^ n := by
        rw [show 4 * Real.sqrt ((2 : ℝ) ^ n) *
            (((r : ℝ) + 1) * Real.sqrt ((2 : ℝ) ^ n)) =
          4 * ((r : ℝ) + 1) * (Real.sqrt ((2 : ℝ) ^ n)) ^ 2 by ring,
          Real.sq_sqrt hN.le]
      _ ≤ 256 * d := by linarith
  unfold normalizedHyperbolic
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ = (‖hyperbolicSieve r n p‖ / d) / (p : ℝ) ^ (((r : ℝ) + 1) / 2) := by rw [div_mul_eq_div_div]
    _ ≤ (4 * Real.sqrt ((2 : ℝ) ^ n) / d) / (p : ℝ) ^ (((r : ℝ) + 1) / 2) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (hyperbolicSieve_prime_bound r n p hp) hd0.le) (by positivity)
    _ ≤ (256 / ((r : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n)) /
        (p : ℝ) ^ (((r : ℝ) + 1) / 2) :=
      div_le_div_of_nonneg_right hfrac (by positivity)
    _ = _ := by
      rw [show -((r : ℝ) + 1) / 2 = -(((r : ℝ) + 1) / 2) by ring,
        Real.rpow_neg hp0.le, Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow]
      ring

/-- Equation (114) for the literal hyperbolic trace, with an arbitrary
finite prime cutoff and its actual compact-test weights. -/
theorem normalizedHyperbolic_prime_sum_bound (r n signExponent : ℕ)
    {X L H s d : ℝ} (hX : 1 ≤ X) (hL : 1 ≤ L) (hH : 0 ≤ H) (hs : 0 ≤ s)
    (hlog : Real.log X ≤ s * L)
    (hd : ((r : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (S : Finset ℕ) (hS : S ⊆ Nat.primesLE ⌊X⌋₊) (w : ℕ → ℂ)
    (hw : ∀ p ∈ S, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum S (-(1 / 2 : ℝ))
      (fun p => (-1 : ℂ) ^ signExponent * normalizedHyperbolic r n d p) w ≤
      2 * (256 / ((r : ℝ) + 1)) * H * Real.log 4 * (1 + s) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  apply cusp_prime_sum_bound hX (by positivity) hL
    (show 2 ≤ (r : ℝ) + 2 by have := Nat.cast_nonneg (α := ℝ) r; linarith)
    (by positivity) hH hs hlog S hS _ w _ hw
  intro p hp
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have he : -((r : ℝ) + 2 - 1) / 2 = -((r : ℝ) + 1) / 2 := by ring
  rw [he]
  exact normalizedHyperbolic_prime_bound r n p (Nat.mem_primesLE.mp (hS hp)).2 d hd

/-- The actual (114) bound from the general dimension formula, with the
internal dimension estimate discharged. -/
theorem normalizedHyperbolic_sum_from_general_dimension (r n signExponent : ℕ)
    (hn : 8 ≤ n) (d : ℕ → ℝ)
    (hd : MartinDimension.SatisfiesMartinFormula (r + 2) d)
    {X L H s : ℝ} (hX : 1 ≤ X) (hL : 1 ≤ L) (hH : 0 ≤ H) (hs : 0 ≤ s)
    (hlog : Real.log X ≤ s * L)
    (S : Finset ℕ) (hS : S ⊆ Nat.primesLE ⌊X⌋₊) (w : ℕ → ℂ)
    (hw : ∀ p ∈ S, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum S (-(1 / 2 : ℝ))
      (fun p => (-1 : ℂ) ^ signExponent * normalizedHyperbolic r n (d (2 ^ n)) p) w ≤
      2 * (256 / ((r : ℝ) + 1)) * H * Real.log 4 * (1 + s) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) :=
  normalizedHyperbolic_prime_sum_bound r n signExponent hX hL hH hs hlog
    (MartinDimension.polynomial_degree_dimension_lower r n hn d hd) S hS w hw

end DepthAspect.SignedSieve
