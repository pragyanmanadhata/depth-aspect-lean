import DepthAspect.MurmurationIntegralSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! The actual limiting constant in (129), by dominated convergence of
the integrated Bessel series. -/
open MeasureTheory Filter Set
open scoped BigOperators
namespace DepthAspect.MurmurationIntegralLimit
open BesselFirstKind BesselBounds MurmurationIntegralSeries

noncomputable def limitValue (ℓ : ℕ) : ℝ :=
  (1 + (ℓ : ℝ)⁻¹) * (Real.pi ^ 2 / 6)

/-- The positive-integer inverse-square sum has its usual exact value. -/
theorem inverse_squares_tsum :
    (∑' ν : ℕ+, ((ν : ℝ) ^ 2)⁻¹) = Real.pi ^ 2 / 6 := by
  rw [tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) (by simp)]
  simpa only [one_div] using hasSum_zeta_two.tsum_eq

theorem inverse_squares_summable :
    Summable (fun ν : ℕ+ => ((ν : ℝ) ^ 2)⁻¹) := by
  have h : Summable (fun ν : ℕ+ => (1 : ℝ) / (ν : ℝ) ^ 2) :=
    hasSum_zeta_two.summable.comp_injective Subtype.val_injective
  simpa only [one_div] using h

noncomputable def integratedTerm (a ℓ : ℕ) (Z : ℝ) (ν : ℕ+) : ℝ :=
  ((ν : ℝ) ^ 2)⁻¹ * (I a (4 * Real.pi * ν * Real.sqrt Z) -
    ((ℓ : ℝ) ^ 2)⁻¹ * I a (4 * Real.pi * ℓ * ν * Real.sqrt Z))

/-- The odd-order antiderivative is uniformly bounded on the positive
half-line, so the integrated series has an inverse-square majorant. -/
theorem integratedTerm_bound (a : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {K : ℝ} (hK : 0 ≤ K) (hI : ∀ T : ℝ, 0 ≤ T → |I a T| ≤ K)
    {Z : ℝ} (hZ : 0 ≤ Z) (ν : ℕ+) :
    ‖integratedTerm a ℓ Z ν‖ ≤
      (K * (1 + ((ℓ : ℝ) ^ 2)⁻¹)) * ((ν : ℝ) ^ 2)⁻¹ := by
  have h1 := hI (4 * Real.pi * ν * Real.sqrt Z) (by positivity)
  have h2 := hI (4 * Real.pi * ℓ * ν * Real.sqrt Z) (by positivity)
  have hmul : |((ℓ : ℝ) ^ 2)⁻¹ * I a (4 * Real.pi * ℓ * ν * Real.sqrt Z)| ≤
      ((ℓ : ℝ) ^ 2)⁻¹ * K := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((ℓ : ℝ) ^ 2)⁻¹)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [integratedTerm, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((ν : ℝ) ^ 2)⁻¹)]
  calc
    _ ≤ ((ν : ℝ) ^ 2)⁻¹ * (K + ((ℓ : ℝ) ^ 2)⁻¹ * K) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 hmul)) (by positivity)
    _ = _ := by ring

theorem integratedTerm_summable (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) {Z : ℝ} (hZ : 0 ≤ Z) :
    Summable (integratedTerm a ℓ Z) := by
  obtain ⟨K, hK, hI, _⟩ := odd_integral_bounds hDLMF a
  exact (inverse_squares_summable.mul_left (K * (1 + ((ℓ : ℝ) ^ 2)⁻¹))).of_norm_bounded
    (integratedTerm_bound a hℓ hK.le hI hZ)

/-- The exact constant is the cancellation of two integrated zero limits. -/
theorem limiting_constant_algebra {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (1 / (1 - (ℓ : ℝ)⁻¹)) *
      ((1 - ((ℓ : ℝ) ^ 2)⁻¹) * (Real.pi ^ 2 / 6)) = limitValue ℓ := by
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 1 - (ℓ : ℝ)⁻¹ ≠ 0 := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  have hfactor : 1 - ((ℓ : ℝ) ^ 2)⁻¹ =
      (1 - (ℓ : ℝ)⁻¹) * (1 + (ℓ : ℝ)⁻¹) := by
    rw [← inv_pow]
    ring
  rw [hfactor]
  unfold limitValue
  generalize hden : 1 - (ℓ : ℝ)⁻¹ = z at hz ⊢
  field_simp [hz]
  <;> ring

/-- The limit in (129) is a proved limit of the actual integral G. No
infinite-interval integral of a Bessel function is used. -/
theorem G_tendsto (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    Tendsto (G a ℓ) atTop (nhds (limitValue ℓ)) := by
  obtain ⟨K, hK, hI, _⟩ := odd_integral_bounds hDLMF a
  have hterm (ν : ℕ+) : Tendsto (fun Z : ℝ => integratedTerm a ℓ Z ν) atTop
      (nhds (((ν : ℝ) ^ 2)⁻¹ * (1 - ((ℓ : ℝ) ^ 2)⁻¹))) := by
    have h1 : Tendsto (fun Z : ℝ => I a (4 * Real.pi * ν * Real.sqrt Z)) atTop (nhds 1) :=
      (odd_integral_tendsto_one hDLMF a).comp
        (Tendsto.const_mul_atTop (by positivity) Real.tendsto_sqrt_atTop)
    have h2 : Tendsto (fun Z : ℝ => I a (4 * Real.pi * ℓ * ν * Real.sqrt Z)) atTop (nhds 1) :=
      (odd_integral_tendsto_one hDLMF a).comp
        (Tendsto.const_mul_atTop (by positivity) Real.tendsto_sqrt_atTop)
    simpa only [integratedTerm, mul_one] using
      (h1.sub (h2.const_mul (((ℓ : ℝ) ^ 2)⁻¹))).const_mul (((ν : ℝ) ^ 2)⁻¹)
  have hsum := tendsto_tsum_of_dominated_convergence
    (inverse_squares_summable.mul_left (K * (1 + ((ℓ : ℝ) ^ 2)⁻¹))) hterm
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with Z hZ ν
      exact integratedTerm_bound a (by omega : 0 < ℓ) hK.le hI hZ ν)
  have hvalue : (∑' ν : ℕ+, ((ν : ℝ) ^ 2)⁻¹ * (1 - ((ℓ : ℝ) ^ 2)⁻¹)) =
      (1 - ((ℓ : ℝ) ^ 2)⁻¹) * (Real.pi ^ 2 / 6) := by
    rw [tsum_mul_right, inverse_squares_tsum]
    ring
  rw [hvalue] at hsum
  have h := hsum.const_mul (1 / (1 - (ℓ : ℝ)⁻¹))
  rw [limiting_constant_algebra hℓ] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with Z hZ
  exact (G_eq_series hDLMF a hℓ hZ).symm

/-- The real constant agrees with the paper's zeta notation. -/
theorem limitValue_eq_zeta (ℓ : ℕ) :
    (limitValue ℓ : ℂ) = (1 + (ℓ : ℂ)⁻¹) * riemannZeta 2 := by
  rw [riemannZeta_two]
  unfold limitValue
  push_cast
  ring

end DepthAspect.MurmurationIntegralLimit
