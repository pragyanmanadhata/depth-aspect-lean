import DepthAspect.PoleIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr

/-!
# A vertical contour shift with an actual simple-pole residue

The proof applies Cauchy–Goursat to `dslope F 0` on finite rectangles. The
simple pole is integrated only over finite symmetric intervals, and its
limits are supplied by `PoleIntegral`. In particular no whole-line Bochner
integral of `1 / (σ + it)` is used.

The decay and integrability hypotheses below are general analytic inputs to
this contour lemma. In the Mellin application they must be proved for the
actual Gamma/L-function product; this module alone does not claim (102).
-/

open Filter MeasureTheory Set
open scoped Topology ComplexOrder
namespace DepthAspect.ContourShift

noncomputable def point (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
noncomputable def quotient (F : ℂ → ℂ) (z : ℂ) : ℂ := F z / z
noncomputable def horizontal (g : ℂ → ℂ) (a b t : ℝ) : ℂ :=
  ∫ σ : ℝ in a..b, g (point σ t)
noncomputable def vertical (g : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  ∫ t : ℝ in -T..T, g (point σ t)

@[simp] theorem point_re (σ t : ℝ) : (point σ t).re = σ := by simp [point]
@[simp] theorem point_im (σ t : ℝ) : (point σ t).im = t := by simp [point]

theorem point_ne_zero_of_re {σ t : ℝ} (hσ : σ ≠ 0) : point σ t ≠ 0 := by
  intro h
  exact hσ (by simpa using congrArg Complex.re h)

theorem point_ne_zero_of_im {σ t : ℝ} (ht : t ≠ 0) : point σ t ≠ 0 := by
  intro h
  exact ht (by simpa using congrArg Complex.im h)

theorem dslope_eq_quotient_sub {F : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) :
    dslope F 0 z = quotient F z - F 0 * z⁻¹ := by
  rw [dslope_of_ne _ hz]
  simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul, quotient, div_eq_mul_inv]
  ring

/-- The removable singularity is obtained from differentiability of the
numerator on an open half-plane. -/
theorem differentiableOn_dslope_halfPlane (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | -1 < z.re}) :
    DifferentiableOn ℂ (dslope F 0) {z : ℂ | -1 < z.re} := by
  apply (Complex.differentiableOn_dslope ?_).mpr hF
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)

/-- Cauchy–Goursat with the two vertical edges solved for explicitly. -/
theorem finite_rectangle (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | -1 < z.re})
    {a b T : ℝ} (ha : -1 < a) (hab : a ≤ b) :
    vertical (dslope F 0) b T - vertical (dslope F 0) a T =
      Complex.I * (horizontal (dslope F 0) a b (-T) -
        horizontal (dslope F 0) a b T) := by
  have hd := differentiableOn_dslope_halfPlane F hF
  have hrect : DifferentiableOn ℂ (dslope F 0)
      (Set.uIcc a b ×ℂ Set.uIcc (-T) T) := by
    apply hd.mono
    intro z hz
    have hzre : z.re ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using (Complex.mem_reProdIm.mp hz).1
    exact ha.trans_le hzre.1
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dslope F 0) (point a (-T)) (point b T) (by simpa only [point_re, point_im] using hrect)
  simp only [point_re, point_im, smul_eq_mul] at h
  change horizontal (dslope F 0) a b (-T) - horizontal (dslope F 0) a b T +
    Complex.I * vertical (dslope F 0) b T - Complex.I * vertical (dslope F 0) a T = 0 at h
  have hi : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination -Complex.I * h +
    (vertical (dslope F 0) b T - vertical (dslope F 0) a T) * hi

/-- On either horizontal edge, the removed pole contributes at most
`‖F 0‖ / |t|`; the remaining term is the literal quotient. -/
theorem norm_dslope_point_le {F : ℂ → ℂ} {σ t R : ℝ}
    (ht : 0 < |t|) (hQ : ‖quotient F (point σ t)‖ ≤ R) :
    ‖dslope F 0 (point σ t)‖ ≤ R + ‖F 0‖ / |t| := by
  have hz : point σ t ≠ 0 := point_ne_zero_of_im (abs_pos.mp ht)
  have him : |t| ≤ ‖point σ t‖ := by
    simpa using Complex.abs_im_le_norm (point σ t)
  rw [dslope_eq_quotient_sub hz]
  calc
    _ ≤ ‖quotient F (point σ t)‖ + ‖F 0 * (point σ t)⁻¹‖ := norm_sub_le _ _
    _ ≤ R + ‖F 0‖ / |t| := by
      apply add_le_add hQ
      rw [norm_mul, norm_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ ht him) (norm_nonneg _)

/-- Uniform quotient decay implies that both actual horizontal integrals
of the removable quotient tend to zero. -/
theorem horizontal_tendsto_zero (F : ℂ → ℂ) {a b : ℝ}
    (hab : a ≤ b) (R : ℝ → ℝ) (hR : Tendsto R atTop (𝓝 0))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖quotient F (point σ t)‖ ≤ R |t|) :
    Tendsto (fun T : ℝ => horizontal (dslope F 0) a b T) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => horizontal (dslope F 0) a b (-T)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun T : ℝ => (R T + ‖F 0‖ / T) * |b - a|) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero, zero_mul] using
      (hR.add (tendsto_inv_atTop_zero.const_mul ‖F 0‖)).mul_const |b - a|
  constructor
  · apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc a b := by
      exact ⟨(uIoc_of_le hab ▸ hσ).1.le, (uIoc_of_le hab ▸ hσ).2⟩
    simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using
      norm_dslope_point_le (F := F) (σ := σ) (t := T)
        (by simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using (show 0 < T by linarith))
        (hbound σ hσ' T (by simpa only [abs_of_nonneg (by linarith : 0 ≤ T)] using hT))
  · apply squeeze_zero_norm' _ hmajor
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    have hσ' : σ ∈ Icc a b := by
      exact ⟨(uIoc_of_le hab ▸ hσ).1.le, (uIoc_of_le hab ▸ hσ).2⟩
    simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] using
      norm_dslope_point_le (F := F) (σ := σ) (t := -T)
        (by simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] using
          (show 0 < T by linarith))
        (hbound σ hσ' (-T)
          (by simpa only [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T)] using hT))

/-- Finite splitting on a vertical edge. Its two terms have distinct
limiting interpretations: an ordinary integral and a symmetric pole limit. -/
theorem vertical_dslope_eq (F : ℂ → ℂ) {σ : ℝ} (hσ : σ ≠ 0)
    (hQ : Integrable (fun t : ℝ => quotient F (point σ t))) (T : ℝ) :
    vertical (dslope F 0) σ T = vertical (quotient F) σ T -
      F 0 * (∫ t : ℝ in -T..T, (point σ t)⁻¹) := by
  have hpoint : (fun t : ℝ => dslope F 0 (point σ t)) =
      (fun t : ℝ => quotient F (point σ t) - F 0 * (point σ t)⁻¹) := by
    funext t
    exact dslope_eq_quotient_sub (point_ne_zero_of_re hσ)
  have hpole : IntervalIntegrable (fun t : ℝ => F 0 * (point σ t)⁻¹)
      volume (-T) T := by
    simpa only [point] using
      (((PoleIntegral.vertical_reciprocal_continuous hσ).const_mul (F 0)).intervalIntegrable (-T) T)
  unfold vertical
  rw [hpoint, intervalIntegral.integral_sub hQ.intervalIntegrable hpole,
    intervalIntegral.integral_const_mul]

/-- A genuine contour-shift formula. The residue is proved from finite
rectangles and the two symmetric pole limits, rather than supplied as an
identity. The quotient itself must be integrable on both vertical lines. -/
theorem vertical_shift (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | -1 < z.re})
    {a b : ℝ} (ha : -1 < a) (ha0 : a < 0) (hb0 : 0 < b)
    (hQa : Integrable (fun t : ℝ => quotient F (point a t)))
    (hQb : Integrable (fun t : ℝ => quotient F (point b t)))
    (R : ℝ → ℝ) (hR : Tendsto R atTop (𝓝 0))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ, 1 ≤ |t| →
      ‖quotient F (point σ t)‖ ≤ R |t|) :
    (∫ t : ℝ, quotient F (point b t)) - (∫ t : ℝ, quotient F (point a t)) =
      (2 * Real.pi : ℝ) * F 0 := by
  have hab : a ≤ b := ha0.le.trans hb0.le
  have hVb := (intervalIntegral_tendsto_integral hQb
    tendsto_neg_atTop_atBot tendsto_id).sub
    ((PoleIntegral.symmetric_limit_pos hb0).const_mul (F 0))
  have hVa := (intervalIntegral_tendsto_integral hQa
    tendsto_neg_atTop_atBot tendsto_id).sub
    ((PoleIntegral.symmetric_limit_neg ha0).const_mul (F 0))
  have hVb' : Tendsto (fun T : ℝ => vertical (dslope F 0) b T) atTop
      (𝓝 ((∫ t : ℝ, quotient F (point b t)) - F 0 * (Real.pi : ℂ))) := by
    simp_rw [vertical_dslope_eq F hb0.ne' hQb]
    simpa only [vertical, point, id_eq] using hVb
  have hVa' : Tendsto (fun T : ℝ => vertical (dslope F 0) a T) atTop
      (𝓝 ((∫ t : ℝ, quotient F (point a t)) - F 0 * (-(Real.pi : ℂ)))) := by
    simp_rw [vertical_dslope_eq F ha0.ne hQa]
    simpa only [vertical, point, id_eq] using hVa
  obtain ⟨hHplus, hHminus⟩ := horizontal_tendsto_zero F hab R hR hbound
  have hzero := (hHminus.sub hHplus).const_mul Complex.I
  have hzero' : Tendsto (fun T : ℝ => vertical (dslope F 0) b T -
      vertical (dslope F 0) a T) atTop (𝓝 0) := by
    simpa only [finite_rectangle F hF ha hab, sub_zero, mul_zero] using hzero
  have heq := tendsto_nhds_unique (hVb'.sub hVa') hzero'
  push_cast
  linear_combination heq

end DepthAspect.ContourShift
