import DepthAspect.MurmurationPointwiseBounds
import DepthAspect.BesselSqrtIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! The actual integral-series identity in (129). Every series/integral
interchange is controlled by a ν^{-3/2} y^{-3/4} majorant at the origin. -/
open MeasureTheory Set
open scoped BigOperators
namespace DepthAspect.MurmurationIntegralSeries
open BesselFirstKind BesselSqrtIntegral MurmurationBesselSeries
open MurmurationPointwiseBounds

noncomputable def I (a : ℕ) (T : ℝ) : ℝ := ∫ t : ℝ in (0)..T, J (2 * a + 1) t
noncomputable def G (a ℓ : ℕ) (Z : ℝ) : ℝ := ∫ y : ℝ in (0)..Z, g a ℓ y / y

noncomputable def term (a ℓ : ℕ) (ν : ℕ+) (y : ℝ) : ℝ :=
  (2 * Real.pi / (1 - (ℓ : ℝ)⁻¹)) *
    ((J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / Real.sqrt y) / (ν : ℝ) -
      (J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / Real.sqrt y) /
        ((ℓ : ℝ) * ν))

theorem term_intervalIntegrable (hDLMF : DLMFIdentities) (a ℓ : ℕ)
    (ν : ℕ+) {Z : ℝ} (hZ : 0 ≤ Z) : IntervalIntegrable (term a ℓ ν) volume 0 Z := by
  have h1 := (intervalIntegrable_bessel_sqrt hDLMF (by omega : 0 < 2 * a + 1)
    (4 * Real.pi * ν) hZ).div_const (ν : ℝ)
  have h2 := (intervalIntegrable_bessel_sqrt hDLMF (by omega : 0 < 2 * a + 1)
    (4 * Real.pi * ℓ * ν) hZ).div_const ((ℓ : ℝ) * ν)
  exact (h1.sub h2).const_mul _

/-- Computing the individual integral retains both powers of ℓ. -/
theorem integral_term (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (ν : ℕ+) {Z : ℝ} (hZ : 0 ≤ Z) :
    (∫ y : ℝ in (0)..Z, term a ℓ ν y) =
      (1 / (1 - (ℓ : ℝ)⁻¹)) * ((ν : ℝ) ^ 2)⁻¹ *
        (I a (4 * Real.pi * ν * Real.sqrt Z) -
          ((ℓ : ℝ) ^ 2)⁻¹ * I a (4 * Real.pi * ℓ * ν * Real.sqrt Z)) := by
  have hν : (0 : ℝ) < ν := by exact_mod_cast ν.pos
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 1 - (ℓ : ℝ)⁻¹ ≠ 0 := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  have hi1 := intervalIntegrable_bessel_sqrt hDLMF (by omega : 0 < 2 * a + 1)
    (4 * Real.pi * ν) hZ
  have hi2 := intervalIntegrable_bessel_sqrt hDLMF (by omega : 0 < 2 * a + 1)
    (4 * Real.pi * ℓ * ν) hZ
  unfold term
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hi1.div_const _) (hi2.div_const _),
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    integral_bessel_sqrt hDLMF (by omega : 0 < 2 * a + 1) (by positivity) hZ,
    integral_bessel_sqrt hDLMF (by omega : 0 < 2 * a + 1) (by positivity) hZ]
  change _ = (1 / (1 - (ℓ : ℝ)⁻¹)) * ((ν : ℝ) ^ 2)⁻¹ *
    ((∫ t : ℝ in (0)..(4 * Real.pi * ν * Real.sqrt Z), J (2 * a + 1) t) -
      ((ℓ : ℝ) ^ 2)⁻¹ * ∫ t : ℝ in (0)..(4 * Real.pi * ℓ * ν * Real.sqrt Z), J (2 * a + 1) t)
  generalize hfirst : (∫ t : ℝ in (0)..(4 * Real.pi * ν * Real.sqrt Z),
    J (2 * a + 1) t) = U
  generalize hsecond : (∫ t : ℝ in (0)..(4 * Real.pi * ℓ * ν * Real.sqrt Z),
    J (2 * a + 1) t) = V
  generalize hden : 1 - (ℓ : ℝ)⁻¹ = z at hz ⊢
  field_simp [hz, Real.pi_ne_zero, ne_of_gt hν, ne_of_gt (lt_trans zero_lt_one hℓR)]
  <;> ring

/-- The sum of the actual integrands is g(y)/y for y>0. -/
theorem term_hasSum (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) {y : ℝ} (hy : 0 < y) :
    HasSum (fun ν : ℕ+ => term a ℓ ν y) (g a ℓ y / y) := by
  have hs := (g_bessel_series_summable hDLMF a (by omega : 0 < ℓ) hy).hasSum
  have hsum := (hs.mul_left (2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹))).div_const y
  rw [← g_eq_bessel hDLMF a hℓ hy] at hsum
  apply hsum.congr_fun
  intro ν
  symm
  unfold term
  have hsqrt : Real.sqrt y ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hy)
  have hsquare : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy.le
  have hscalar : Real.sqrt y / y = (Real.sqrt y)⁻¹ := by
    apply (div_eq_iff (ne_of_gt hy)).mpr
    calc
      Real.sqrt y = (Real.sqrt y)⁻¹ * (Real.sqrt y) ^ 2 := by field_simp [hsqrt] <;> ring
      _ = (Real.sqrt y)⁻¹ * y := by rw [hsquare]
  calc
    _ = (2 * Real.pi / (1 - (ℓ : ℝ)⁻¹)) * (Real.sqrt y / y) *
        (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
          J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)) := by ring
    _ = _ := by rw [hscalar]; ring

/-- The quantitative majorant is integrable even at y=0. -/
theorem term_bound (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {K : ℝ} (hK : 0 < K)
    (hb : ∀ t : ℝ, 0 < t → |J (2 * a + 1) t| ≤ K * t ^ (-(1 / 2 : ℝ)))
    (ν : ℕ+) {y : ℝ} (hy : 0 < y) :
    ‖term a ℓ ν y‖ ≤ (4 * Real.pi * K / (1 - (ℓ : ℝ)⁻¹)) *
      (ν : ℝ) ^ (-(3 / 2 : ℝ)) * y ^ (-(3 / 4 : ℝ)) := by
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hbound := bessel_difference_bound a hℓ hK hb hy ν
  have he : term a ℓ ν y = (2 * Real.pi / (1 - (ℓ : ℝ)⁻¹)) *
      (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
        J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)) /
          Real.sqrt y := by unfold term; ring
  rw [he, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi / (1 - (ℓ : ℝ)⁻¹))]
  calc
    _ ≤ (2 * Real.pi / (1 - (ℓ : ℝ)⁻¹)) *
        (2 * K * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) * (ν : ℝ) ^ (-(3 / 2 : ℝ))) /
          Real.sqrt y :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (by positivity)) hs.le
    _ = _ := by
      have hp : (Real.sqrt y) ^ (-(1 / 2 : ℝ)) / Real.sqrt y =
          y ^ (-(3 / 4 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy.le, ← Real.rpow_sub hy]
        norm_num
      calc
        _ = (4 * Real.pi * K / (1 - (ℓ : ℝ)⁻¹)) * (ν : ℝ) ^ (-(3 / 2 : ℝ)) *
            ((Real.sqrt y) ^ (-(1 / 2 : ℝ)) / Real.sqrt y) := by ring
        _ = _ := by rw [hp]

/-- The first identity in (129), including a proof of the required
termwise integration at the singular endpoint. -/
theorem G_eq_series (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) {Z : ℝ} (hZ : 0 ≤ Z) :
    G a ℓ Z = (1 / (1 - (ℓ : ℝ)⁻¹)) *
      ∑' ν : ℕ+, ((ν : ℝ) ^ 2)⁻¹ *
        (I a (4 * Real.pi * ν * Real.sqrt Z) -
          ((ℓ : ℝ) ^ 2)⁻¹ * I a (4 * Real.pi * ℓ * ν * Real.sqrt Z)) := by
  obtain ⟨K, hK, hb⟩ := J_global_half_bound hDLMF (2 * a + 1)
  let C : ℝ := 4 * Real.pi * K / (1 - (ℓ : ℝ)⁻¹)
  let bound : ℕ+ → ℝ → ℝ := fun ν y =>
    C * (ν : ℝ) ^ (-(3 / 2 : ℝ)) * y ^ (-(3 / 4 : ℝ))
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := term a ℓ) (f := fun y => g a ℓ y / y)
    (μ := volume) (a := 0) (b := Z) bound
    (fun ν => (term_intervalIntegrable hDLMF a ℓ ν hZ).aestronglyMeasurable_restrict_uIoc)
    (by
      intro ν
      filter_upwards [] with y hy
      rw [uIoc_of_le hZ] at hy
      exact term_bound a hℓ hK hb ν hy.1)
    (by
      filter_upwards [] with y _
      exact (pnat_three_halves_summable.mul_left C).mul_right _)
    (by
      simp only [bound, tsum_mul_right, tsum_mul_left]
      exact (intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))).const_mul _)
    (by
      filter_upwards [] with y hy
      rw [uIoc_of_le hZ] at hy
      exact term_hasSum hDLMF a hℓ hy.1)
  unfold G
  rw [← hdom.tsum_eq]
  simp_rw [integral_term hDLMF a hℓ _ hZ, mul_assoc]
  exact tsum_mul_left

end DepthAspect.MurmurationIntegralSeries
