import DepthAspect.ArithmeticWeightSummability
import DepthAspect.ArithmeticSummatoryLimit
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.LinearCombination

/-! The actual Dirichlet-series and Euler-product identity (122). -/
namespace DepthAspect.ArithmeticWeights

open scoped BigOperators LSeries.notation

noncomputable def H (ℓ : ℕ) (z : ℂ) : ℂ := LSeries (fun n => (h ℓ n : ℂ)) z

/-- Hℓ(0) is the actual coefficient sum appearing in the summatory formula. -/
theorem H_zero (ℓ : ℕ) : H ℓ 0 = (R ℓ : ℂ) := by
  unfold H LSeries R
  simp only [LSeries.term_def₀ (f := fun n => (h ℓ n : ℂ)) (by simp), neg_zero,
    Complex.cpow_zero, mul_one, Complex.ofReal_tsum]

/-- Absolute convergence of the actual h-series on Re z > -1/2. -/
theorem h_LSeries_summable (ℓ : ℕ) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    LSeriesSummable (fun n => (h ℓ n : ℂ)) z := by
  let σ := max 0 (-z.re)
  have hσ0 : 0 ≤ σ := le_max_left _ _
  have hσ1 : σ < 1 / 2 := max_lt (by norm_num) (by linarith)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := weightedAbs ℓ σ) _ (weightedAbs_summable ℓ hσ0 hσ1)
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn, Complex.norm_real, Real.norm_eq_abs]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right 0 (-z.re))
    rw [Real.rpow_neg (Nat.cast_nonneg n)] at hp
    exact (by simpa only [weightedAbs, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hp (abs_nonneg (h ℓ n)))

/-- The reciprocal sequence shifts the usual zeta Dirichlet series by one. -/
theorem reciprocal_term (z : ℂ) (n : ℕ) :
    LSeries.term (fun m => (reciprocal m : ℂ)) z n = LSeries.term 1 (1 + z) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Pi.one_apply, reciprocal_apply, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [Complex.cpow_add 1 z (by exact_mod_cast hn), Complex.cpow_one, one_div,
      mul_inv_rev, div_eq_mul_inv]
    ring

theorem reciprocal_LSeries_summable {z : ℂ} (hz : 0 < z.re) :
    LSeriesSummable (fun n => (reciprocal n : ℂ)) z := by
  have hs := LSeriesSummable_one_iff.mpr (show 1 < (1 + z).re by simpa using hz)
  exact hs.congr (fun n => (reciprocal_term z n).symm)

theorem reciprocal_LSeries {z : ℂ} (hz : 0 < z.re) :
    LSeries (fun n => (reciprocal n : ℂ)) z = riemannZeta (1 + z) := by
  simp_rw [LSeries, reciprocal_term]
  exact LSeries_one_eq_riemannZeta (by simpa using hz)

/-- The literal finite convolution is preserved by the real-to-complex cast. -/
theorem complex_coefficient_convolution (ℓ : ℕ) :
    (fun n => (h ℓ n : ℂ)) ⍟ (fun n => (reciprocal n : ℂ)) =
      (fun n => (c ℓ n : ℂ)) := by
  funext n
  rw [LSeries.convolution_def, c_divisor_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
    reciprocal_apply, Complex.ofReal_inv, div_eq_mul_inv]

/-- The first identity in (122), for the actual cℓ and hℓ coefficient sequences. -/
theorem dirichlet_series_factorization (ℓ : ℕ) {z : ℂ} (hz : 0 < z.re) :
    LSeries (fun n => (c ℓ n : ℂ)) z = riemannZeta (1 + z) * H ℓ z := by
  rw [← complex_coefficient_convolution, LSeries_convolution'
    (h_LSeries_summable ℓ (by linarith)) (reciprocal_LSeries_summable hz),
    reciprocal_LSeries hz, H, mul_comm]

/-- The h-series is multiplicative after its actual complex Dirichlet weight. -/
theorem h_term_mul (ℓ : ℕ) (z : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    LSeries.term (fun a => (h ℓ a : ℂ)) z (m * n) =
      LSeries.term (fun a => (h ℓ a : ℂ)) z m *
        LSeries.term (fun a => (h ℓ a : ℂ)) z n := by
  simp only [LSeries.term_def₀ (f := fun n => (h ℓ n : ℂ)) (by simp),
    (h_isMultiplicative ℓ).2 hmn, Complex.ofReal_mul, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

noncomputable def Hlocal (ℓ p : ℕ) (z : ℂ) : ℂ :=
  (1 + ((p : ℂ) * (excludedFactor ℓ p : ℂ)) * (p : ℂ) ^ (-z)) *
    (1 - (p : ℂ) ^ (-1 - z))

/-- Only the first three actual prime-power coefficients survive. Their
sum is exactly the pair of Euler factors displayed in (122). -/
theorem h_local_sum (ℓ : ℕ) {p : ℕ} (hp : p.Prime) (z : ℂ) :
    (∑' j : ℕ, LSeries.term (fun n => (h ℓ n : ℂ)) z (p ^ j)) = Hlocal ℓ p z := by
  have ht : (∑' j : ℕ, LSeries.term (fun n => (h ℓ n : ℂ)) z (p ^ j)) =
      ∑ j ∈ Finset.range 3, LSeries.term (fun n => (h ℓ n : ℂ)) z (p ^ j) := by
    apply tsum_eq_sum
    intro j hj
    rw [LSeries.term_def₀ (f := fun n => (h ℓ n : ℂ)) (by simp),
      h_prime_power_zero ℓ hp (by simpa only [Finset.mem_range, not_lt] using hj)]
    simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsquare : ((p ^ 2 : ℕ) : ℂ) ^ (-z) = ((p : ℂ) ^ (-z)) ^ 2 := by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  have hshift : (p : ℂ) ^ (-1 - z) = (p : ℂ)⁻¹ * (p : ℂ) ^ (-z) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hp0, Complex.cpow_neg_one]
  rw [ht]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    LSeries.term_def₀ (f := fun n => (h ℓ n : ℂ)) (by simp), pow_zero, pow_one, h_one,
    h_prime ℓ hp, h_prime_square ℓ hp, Complex.ofReal_one, Nat.cast_one,
    Complex.one_cpow, mul_one, hsquare]
  unfold Hlocal
  rw [hshift]
  push_cast
  have hc : (p : ℂ) * (p : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hp0
  linear_combination (excludedFactor ℓ p : ℂ) * ((p : ℂ) ^ (-z)) ^ 2 * hc

/-- The actual Euler product for Hℓ on the entire half-plane of absolute
convergence asserted in Lemma 6.2. -/
theorem H_euler_product (ℓ : ℕ) {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    HasProd (fun p : Nat.Primes => Hlocal ℓ p z) (H ℓ z) := by
  have ht := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term (fun n => (h ℓ n : ℂ)) z)
    (by simp [LSeries.term_of_ne_zero]) (h_term_mul ℓ z)
    (h_LSeries_summable ℓ hz).norm (by simp)
  simpa only [h_local_sum ℓ (Subtype.property _) z, H, LSeries] using ht

/-- The omitted prime contributes exactly the single first factor. -/
theorem Hlocal_omitted (ℓ : ℕ) (z : ℂ) : Hlocal ℓ ℓ z = 1 - (ℓ : ℂ) ^ (-1 - z) := by
  simp [Hlocal, excludedFactor]

/-- At every other prime the product is literally the factor in (122). -/
theorem Hlocal_other (ℓ p : ℕ) (hp : p ≠ ℓ) (z : ℂ) :
    Hlocal ℓ p z = (1 + ((p : ℂ) / (denominator p : ℂ)) * (p : ℂ) ^ (-z)) *
      (1 - (p : ℂ) ^ (-1 - z)) := by
  simp [Hlocal, excludedFactor, hp, div_eq_mul_inv]

end DepthAspect.ArithmeticWeights
