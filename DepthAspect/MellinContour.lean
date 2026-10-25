import DepthAspect.ContourShift
import DepthAspect.GammaStrip
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.GCongr

/-!
# The actual Gamma/L-function contour in the exponential smoothing argument

The general entire function `L` has the explicit strip growth hypothesis used
in the contour argument. For the paper's imprimitive function this hypothesis
is supplied by the proved finite Euler-factor estimate and the primitive GRH
bound, not by an assumed smoothing estimate. Every contour, numerator, Gamma
factor, and remainder integral below is defined literally.
-/

open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace DepthAspect.MellinContour

open ContourShift

noncomputable def kernel (L : ℂ → ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  Complex.Gamma w * L (1 + w) * (x : ℂ) ^ w

noncomputable def numerator (L : ℂ → ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  Complex.Gamma (1 + w) * L (1 + w) * (x : ℂ) ^ w

noncomputable def lineIntegral (L : ℂ → ℂ) (x σ : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, kernel L x (point σ t)

noncomputable def gammaMoment (σ η : ℝ) : ℝ :=
  ∫ t : ℝ, ‖Complex.Gamma (point σ t)‖ * (2 + |t|) ^ η

theorem gammaMoment_nonneg (σ η : ℝ) : 0 ≤ gammaMoment σ η := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

@[simp] theorem numerator_zero (L : ℂ → ℂ) (x : ℝ) : numerator L x 0 = L 1 := by
  simp [numerator, Complex.Gamma_one]

theorem quotient_numerator {L : ℂ → ℂ} {x : ℝ} {w : ℂ} (hw : w ≠ 0) :
    quotient (numerator L x) w = kernel L x w := by
  unfold quotient numerator kernel
  rw [add_comm (1 : ℂ) w, Complex.Gamma_add_one _ hw]
  field_simp [hw] <;> ring

theorem numerator_differentiableOn {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (numerator L x) {w : ℂ | -1 < w.re} := by
  intro w hw
  change -1 < w.re at hw
  have hg : DifferentiableAt ℂ Complex.Gamma (1 + w) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  exact ((hg.comp w (by fun_prop)).mul ((hL (1 + w)).comp w (by fun_prop)) |>.mul
    (differentiableAt_id.const_cpow (Or.inl hxC))).differentiableWithinAt

theorem Gamma_line_continuous {σ : ℝ} (hσ : -1 < σ) (hσ0 : σ ≠ 0) :
    Continuous (fun t : ℝ => Complex.Gamma (point σ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp (by unfold point; fun_prop)
  intro m hm
  have hre : σ = -(m : ℝ) := by simpa using congrArg Complex.re hm
  by_cases hm0 : m = 0
  · exact hσ0 (by simpa only [hm0, Nat.cast_zero, neg_zero] using hre)
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
    linarith

theorem kernel_line_continuous {L : ℂ → ℂ} (hL : Continuous L)
    {x σ : ℝ} (hx : 0 < x) (hσ : -1 < σ) (hσ0 : σ ≠ 0) :
    Continuous (fun t : ℝ => kernel L x (point σ t)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpoint : Continuous (fun t : ℝ => point σ t) := by unfold point; fun_prop
  unfold kernel
  apply ((Gamma_line_continuous hσ hσ0).mul (hL.comp (by unfold point; fun_prop))).mul
  exact hpoint.const_cpow (Or.inl hxC)

/-- The pointwise majorant retains the exact `x^σ` power. -/
theorem norm_kernel_le {L : ℂ → ℂ} {x σ t C η : ℝ} (hx : 0 < x)
    (hC : 0 ≤ C)
    (hL : ‖L (1 + point σ t)‖ ≤ C * (2 + |t|) ^ η) :
    ‖kernel L x (point σ t)‖ ≤
      (C * x ^ σ) * (‖Complex.Gamma (point σ t)‖ * (2 + |t|) ^ η) := by
  unfold kernel
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, point_re]
  calc
    _ ≤ (‖Complex.Gamma (point σ t)‖ * (C * (2 + |t|) ^ η)) * x ^ σ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (norm_nonneg _))
        (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

/-- Absolute integrability on a contour follows from the actual Gamma
moment. The polynomial growth bound is the only property of `L` used here. -/
theorem kernel_integrable {L : ℂ → ℂ} (hLcont : Continuous L)
    {x σ C η : ℝ} (hx : 0 < x) (hσ : -1 < σ) (hσ0 : σ ≠ 0) (hC : 0 ≤ C)
    (hL : ∀ t : ℝ, ‖L (1 + point σ t)‖ ≤ C * (2 + |t|) ^ η)
    (hΓ : Integrable (fun t : ℝ => ‖Complex.Gamma (point σ t)‖ * (2 + |t|) ^ η)) :
    Integrable (fun t : ℝ => kernel L x (point σ t)) := by
  apply (hΓ.const_mul (C * x ^ σ)).mono'
    (kernel_line_continuous hLcont hx hσ hσ0).aestronglyMeasurable
  filter_upwards with t
  exact norm_kernel_le hx hC (hL t)

/-- The quantitative horizontal-edge bound used to discharge the contour
lemma's decay hypothesis. No asymptotic Gamma estimate is a premise. -/
theorem kernel_horizontal_bound {L : ℂ → ℂ} {x σ t C η : ℝ}
    (hx : 1 ≤ x) (hσ : σ ∈ Icc (-(1 / 2)) 1) (ht : 1 ≤ |t|)
    (hC : 0 ≤ C) (hη : η ≤ 1)
    (hL : ‖L (1 + point σ t)‖ ≤ C * (2 + |t|) ^ η) :
    ‖kernel L x (point σ t)‖ ≤ 72 * C * x * (|t|⁻¹) ^ 3 := by
  have hx0 : 0 < x := by linarith
  have ht0 : 0 < |t| := by linarith
  have hpow : x ^ σ ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hσ.2
  have hweight : (2 + |t|) ^ η ≤ 3 * |t| := by
    calc
      _ ≤ (2 + |t|) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hη
      _ ≤ _ := by rw [Real.rpow_one]; linarith
  have hΓ := GammaStrip.norm_Gamma_strip_le hσ ht0
  have hk := norm_kernel_le hx0 hC hL
  calc
    _ ≤ (C * x ^ σ) * (‖Complex.Gamma (point σ t)‖ * (2 + |t|) ^ η) := hk
    _ ≤ (C * x) * ((24 / |t| ^ 4) * (3 * |t|)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hpow hC
      · exact mul_le_mul hΓ hweight (Real.rpow_nonneg (by positivity) _) (by positivity)
      · exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      · exact mul_nonneg hC hx0.le
    _ = _ := by field_simp [ht0.ne'] <;> ring

/-- Shifting the actual Gamma/L contour from 1 to `σ` picks up exactly
`L(1)`. The strip growth condition is the cited primitive bound after the
internal Euler correction; it is not a contour-shift identity. -/
theorem line_shift {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    {x σ C η : ℝ} (hx : 1 ≤ x)
    (hσ : σ ∈ Icc (-(1 / 2)) (-(1 / 4))) (hC : 0 ≤ C) (hη : η ≤ 1)
    (hgrowth : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖L s‖ ≤ C * (2 + |s.im|) ^ η) :
    lineIntegral L x 1 = L 1 + lineIntegral L x σ := by
  have hx0 : 0 < x := by linarith
  have hσ0 : σ < 0 := by linarith [hσ.2]
  have hσm : -1 < σ := by linarith [hσ.1]
  have hLσ (t : ℝ) : ‖L (1 + point σ t)‖ ≤ C * (2 + |t|) ^ η := by
    simpa only [Complex.add_re, Complex.one_re, point_re, Complex.add_im,
      Complex.one_im, point_im, zero_add] using
      hgrowth (1 + point σ t) (by simp; linarith [hσ.1]) (by simp; linarith [hσ.2])
  have hLone (t : ℝ) : ‖L (1 + point 1 t)‖ ≤ C * (2 + |t|) ^ η := by
    simpa only [Complex.add_re, Complex.one_re, point_re, Complex.add_im,
      Complex.one_im, point_im, zero_add] using
      hgrowth (1 + point 1 t) (by norm_num) (by norm_num)
  have hQa := kernel_integrable hL.continuous hx0 hσm hσ0.ne hC hLσ
    (GammaStrip.Gamma_shifted_weight_integrable hσ hη)
  have hQb := kernel_integrable hL.continuous hx0 (by norm_num : (-1 : ℝ) < 1)
    one_ne_zero hC hLone (GammaStrip.Gamma_one_weight_integrable hη)
  let R : ℝ → ℝ := fun T => 72 * C * x * (T⁻¹) ^ 3
  have hR : Tendsto R atTop (𝓝 0) := by
    simpa [R] using (tendsto_inv_atTop_zero.pow 3).const_mul (72 * C * x)
  have hquot (a t : ℝ) (ha : a ≠ 0) :
      quotient (numerator L x) (point a t) = kernel L x (point a t) :=
    quotient_numerator (point_ne_zero_of_re ha)
  have hshift := ContourShift.vertical_shift (numerator L x)
    (numerator_differentiableOn hL hx0) hσm hσ0 (by norm_num : (0 : ℝ) < 1)
    (by simpa only [hquot σ _ hσ0.ne] using hQa)
    (by simpa only [hquot 1 _ one_ne_zero] using hQb) R hR (by
      intro a ha t ht
      have ht0 : t ≠ 0 := abs_pos.mp (by linarith : 0 < |t|)
      rw [quotient_numerator (point_ne_zero_of_im ht0)]
      apply kernel_horizontal_bound hx ⟨hσ.1.trans ha.1, ha.2⟩ ht hC hη
      simpa only [Complex.add_re, Complex.one_re, point_re, Complex.add_im,
        Complex.one_im, point_im, zero_add] using
        hgrowth (1 + point a t) (by simp; linarith [hσ.1, ha.1]) (by simp; linarith [ha.2]))
  simp only [hquot σ _ hσ0.ne, hquot 1 _ one_ne_zero, numerator_zero] at hshift
  unfold lineIntegral
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  field_simp [hπ]
  linear_combination hshift

/-- A finite, literal Gamma moment supplies the constant in the remainder
estimate. Its finiteness was established before the shift. -/
theorem lineIntegral_bound {L : ℂ → ℂ} (hL : Continuous L)
    {x σ C η : ℝ} (hx : 0 < x)
    (hσ : σ ∈ Icc (-(1 / 2)) (-(1 / 4))) (hC : 0 ≤ C) (hη : η ≤ 1)
    (hgrowth : ∀ t : ℝ, ‖L (1 + point σ t)‖ ≤ C * (2 + |t|) ^ η) :
    ‖lineIntegral L x σ‖ ≤
      ((2 * Real.pi)⁻¹ * gammaMoment σ η) * C * x ^ σ := by
  have hΓ := GammaStrip.Gamma_shifted_weight_integrable hσ hη
  have hK := kernel_integrable hL hx (by linarith [hσ.1]) (by linarith [hσ.2]) hC hgrowth hΓ
  have hnorm : ‖∫ t : ℝ, kernel L x (point σ t)‖ ≤
      (C * x ^ σ) * gammaMoment σ η := by
    calc
      _ ≤ ∫ t : ℝ, ‖kernel L x (point σ t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (C * x ^ σ) *
          (‖Complex.Gamma (point σ t)‖ * (2 + |t|) ^ η) :=
        integral_mono hK.norm (hΓ.const_mul _) (fun t => norm_kernel_le hx hC (hgrowth t))
      _ = _ := by rw [integral_const_mul]; rfl
  unfold lineIntegral
  rw [norm_mul, norm_inv, Complex.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ((C * x ^ σ) * gammaMoment σ η) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-- The analytic remainder in (102), prior to identifying the initial line
with the exponentially smoothed Dirichlet series. -/
theorem smoothing_remainder_bound {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    {x C η : ℝ} (hx : 1 ≤ x) (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖L s‖ ≤ C * (2 + |s.im|) ^ η) :
    ‖lineIntegral L x 1 - L 1‖ ≤
      ((2 * Real.pi)⁻¹ * gammaMoment (-1 / 2 + η) η) * C * x ^ (-1 / 2 + η) := by
  have hσ : -1 / 2 + η ∈ Icc (-(1 / 2)) (-(1 / 4)) := by constructor <;> linarith
  rw [line_shift hL hx hσ hC (by linarith) hgrowth, add_sub_cancel_left]
  apply lineIntegral_bound hL.continuous (by linarith) hσ hC (by linarith)
  intro t
  simpa only [Complex.add_re, Complex.one_re, point_re, Complex.add_im,
    Complex.one_im, point_im, zero_add] using
    hgrowth (1 + point (-1 / 2 + η) t) (by simp; linarith) (by simp; linarith)

end DepthAspect.MellinContour
