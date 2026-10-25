import DepthAspect.MurmurationIntegralSeries
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Integrability at the origin and the small-Z bound in (129). -/
open MeasureTheory Set
open scoped BigOperators
namespace DepthAspect.MurmurationIntegralSmall
open BesselFirstKind MurmurationBesselSeries MurmurationPointwiseBounds MurmurationIntegralSeries

theorem term_measurable (hDLMF : DLMFIdentities) (a ℓ : ℕ) (ν : ℕ+) :
    Measurable (term a ℓ ν) := by
  have hJ := (hDLMF.continuous (2 * a + 1)).measurable
  unfold term
  fun_prop

/-- The actual density integrand is measurable on every positive interval,
using the now proved Bessel expansion. -/
theorem log_density_aestronglyMeasurable (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {Z : ℝ} (hZ : 0 ≤ Z) :
    AEStronglyMeasurable (fun y => g a ℓ y / y) (volume.restrict (uIoc 0 Z)) := by
  have hm : Measurable (fun y : ℝ => ∑' ν : ℕ+, term a ℓ ν y) :=
    Measurable.tsum (fun ν => term_measurable hDLMF a ℓ ν)
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  rw [uIoc_of_le hZ] at hy
  exact (term_hasSum hDLMF a hℓ hy.1).tsum_eq

/-- The original logarithmic density integrand is genuinely integrable
at zero; this is not inferred merely from a formal integral identity. -/
theorem log_density_intervalIntegrable (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {Z : ℝ} (hZ : 0 ≤ Z) :
    IntervalIntegrable (fun y => g a ℓ y / y) volume 0 Z := by
  obtain ⟨C, hC, hb⟩ := g_quarter_bound hDLMF a hℓ
  have hi : IntervalIntegrable (fun y : ℝ => C * y ^ (-(3 / 4 : ℝ))) volume 0 Z :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))).const_mul C
  apply hi.mono_fun' (log_density_aestronglyMeasurable hDLMF a hℓ hZ)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  rw [uIoc_of_le hZ] at hy
  have hy0 := hy.1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0]
  calc
    _ ≤ (C * y ^ (1 / 4 : ℝ)) / y := div_le_div_of_nonneg_right (hb y hy0) hy0.le
    _ = C * y ^ (-(3 / 4 : ℝ)) := by
      have he : y ^ (1 / 4 : ℝ) / y = y ^ (-(3 / 4 : ℝ)) := by
        nth_rw 2 [← Real.rpow_one y]
        rw [← Real.rpow_sub hy0]
        norm_num
      rw [mul_div_assoc, he]

/-- The remaining small-Z estimate in (129). -/
theorem G_small_bound (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, ∀ Z : ℝ, 0 < Z → Z ≤ 1 → |G a ℓ Z| ≤ C * Real.sqrt Z := by
  obtain ⟨K, hK, hb⟩ := g_small_bound a hℓ
  refine ⟨2 * K, by positivity, ?_⟩
  intro Z hZ hZ1
  have hi : IntervalIntegrable (fun y : ℝ => K * y ^ (-(1 / 2 : ℝ))) volume 0 Z :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul K
  have hbound : ∀ᵐ y : ℝ, y ∈ Ioc 0 Z →
      ‖g a ℓ y / y‖ ≤ K * y ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [] with y hy
    have hy0 := hy.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hy0]
    calc
      _ ≤ (K * Real.sqrt y) / y :=
        div_le_div_of_nonneg_right (hb y hy0 (hy.2.trans hZ1)) hy0.le
      _ = K * y ^ (-(1 / 2 : ℝ)) := by
        have he : Real.sqrt y / y = y ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow]
          nth_rw 2 [← Real.rpow_one y]
          rw [← Real.rpow_sub hy0]
          norm_num
        rw [mul_div_assoc, he]
  have hn := intervalIntegral.norm_integral_le_of_norm_le hZ.le hbound hi
  have he : (∫ y : ℝ in (0)..Z, K * y ^ (-(1 / 2 : ℝ))) = 2 * K * Real.sqrt Z := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
    norm_num [← Real.sqrt_eq_rpow]
    ring
  simpa only [G, Real.norm_eq_abs, he] using hn

end DepthAspect.MurmurationIntegralSmall
