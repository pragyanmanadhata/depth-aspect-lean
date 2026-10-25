import DepthAspect.ArchimedeanBound
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# The actual archimedean local factor

Its logarithmic derivative and the passage to the real part in (56) are
proved here. The test may be complex-valued; only its evenness is needed.
-/
open MeasureTheory ComplexConjugate
namespace DepthAspect.GammaLocal
open DigammaBound ArchimedeanBound

noncomputable def gammaFactor (k : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-z * (Real.log (2 * Real.pi) : ℂ)) *
    Complex.Gamma (z + ((k - 1) / 2 : ℝ))

private theorem gamma_arg_not_neg_nat {k : ℝ} (hk : 1 ≤ k) {z : ℂ}
    (hz : 0 < z.re) : ∀ m : ℕ, z + ((k - 1) / 2 : ℝ) ≠ -(m : ℂ) := by
  intro m hm
  have he := congrArg Complex.re hm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at he
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  linarith

/-- The archimedean factor is pole-free in the strip used for the local shift. -/
theorem gammaFactor_differentiableAt {k : ℝ} (hk : 1 ≤ k) {z : ℂ}
    (hz : 0 < z.re) : DifferentiableAt ℂ (gammaFactor k) z := by
  unfold gammaFactor
  apply DifferentiableAt.mul (by fun_prop)
  exact (Complex.differentiableAt_Gamma _ (gamma_arg_not_neg_nat hk hz)).comp z
    (by fun_prop)

theorem gammaFactor_ne_zero {k : ℝ} (hk : 1 ≤ k) {z : ℂ}
    (hz : 0 < z.re) : gammaFactor k z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero (gamma_arg_not_neg_nat hk hz))

/-- Differentiating the actual Gamma factor gives its constant and digamma
pieces with the normalization used in the paper. -/
theorem gammaFactor_logDeriv {k : ℝ} (hk : 1 ≤ k) {z : ℂ} (hz : 0 < z.re) :
    deriv (gammaFactor k) z / gammaFactor k z =
      -(Real.log (2 * Real.pi) : ℂ) + Complex.digamma (z + ((k - 1) / 2 : ℝ)) := by
  have he := ((((hasDerivAt_id z).neg).mul_const (Real.log (2 * Real.pi) : ℂ)).cexp)
  have hg := (Complex.differentiableAt_Gamma _ (gamma_arg_not_neg_nat hk hz)).hasDerivAt.comp z
    ((hasDerivAt_id z).add_const (((k - 1) / 2 : ℝ) : ℂ))
  have hd := he.mul hg
  have hderiv : deriv (gammaFactor k) z =
      Complex.exp (-z * (Real.log (2 * Real.pi) : ℂ)) *
        (-(Real.log (2 * Real.pi) : ℂ) * Complex.Gamma (z + ((k - 1) / 2 : ℝ)) +
          deriv Complex.Gamma (z + ((k - 1) / 2 : ℝ))) := by
    have hd' : HasDerivAt (gammaFactor k)
        (Complex.exp (-z * (Real.log (2 * Real.pi) : ℂ)) *
          (-(Real.log (2 * Real.pi) : ℂ) * Complex.Gamma (z + ((k - 1) / 2 : ℝ)) +
            deriv Complex.Gamma (z + ((k - 1) / 2 : ℝ)))) z := by
      apply hd.congr_deriv
      dsimp only [Pi.neg_apply, id_eq, Function.comp_apply]
      ring
    exact hd'.deriv
  rw [hderiv, gammaFactor, Complex.digamma_def, logDeriv_apply]
  rw [mul_div_mul_left _ _ (Complex.exp_ne_zero _), add_div,
    mul_div_cancel_right₀ _ (Complex.Gamma_ne_zero (gamma_arg_not_neg_nat hk hz))]

/-- On the central line the Gamma argument is precisely k/2+it. -/
theorem gammaFactor_logDeriv_critical {k : ℝ} (hk : 1 ≤ k) (t : ℝ) :
    deriv (gammaFactor k) ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) /
      gammaFactor k ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
    -(Real.log (2 * Real.pi) : ℂ) + Complex.digamma ((k / 2 : ℝ) + (t : ℂ) * Complex.I) := by
  rw [gammaFactor_logDeriv hk (by norm_num [Complex.mul_re])]
  congr 2
  push_cast
  ring

/-- The cited series identity implies conjugation symmetry for the actual
digamma, without assuming a new analytic symmetry as an extra input. -/
theorem digamma_conj (hDLMF : DLMFSeriesIdentity) {z : ℂ} (hz : 1 ≤ z.re) :
    Complex.digamma (conj z) = conj (Complex.digamma z) := by
  rw [hDLMF z hz, hDLMF (conj z) (by simpa using hz)]
  unfold seriesDigamma
  rw [map_add, map_neg, Complex.conj_ofReal, Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro n
  simp [seriesTerm]

/-- Reflection symmetry of the kernel and evenness of a complex test justify
taking the real part of the kernel inside the integral. -/
theorem even_integral_eq_re (G φ : ℝ → ℂ)
    (hG : ∀ x, G (-x) = conj (G x)) (hφ : Function.Even φ)
    (hI : Integrable (fun x => G x * φ x)) :
    (∫ x, G x * φ x) = ∫ x, (G x).re • φ x := by
  have hr : (∫ x, G (-x) * φ (-x)) = ∫ x, G x * φ x :=
    integral_neg_eq_self (fun x : ℝ => G x * φ x) volume
  have he : (fun x => G x * φ x + G (-x) * φ (-x)) =
      (fun x => (2 : ℂ) * ((G x).re • φ x)) := by
    funext x
    rw [hG x, hφ x, ← add_mul, Complex.add_conj]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.real_smul]
    ring
  have hi := integral_add hI hI.comp_neg
  rw [he, integral_const_mul, hr] at hi
  linear_combination -hi / 2

/-- The digamma kernel has exactly the symmetry needed above. -/
theorem digamma_kernel_reflection (hDLMF : DLMFSeriesIdentity) {a : ℝ} (ha : 1 ≤ a)
    (c x : ℝ) :
    Complex.digamma ((a : ℂ) + ((c * (-x) : ℝ) : ℂ) * Complex.I) =
      conj (Complex.digamma ((a : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I)) := by
  rw [← digamma_conj hDLMF (by simpa using ha)]
  congr 1
  simp


/-- The full complex digamma kernel is integrable against the paper's tests. -/
theorem digamma_kernel_integrable (hDLMF : DLMFSeriesIdentity) {a : ℝ} (ha : 1 ≤ a)
    (c : ℝ) (φ : ℝ → ℂ) (hφ : Integrable φ)
    (hxφ : Integrable (fun x : ℝ => x • φ x)) :
    Integrable (fun x => Complex.digamma ((a : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I) * φ x) := by
  have hc : Continuous (fun x : ℝ =>
      Complex.digamma ((a : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I)) :=
    (digamma_vertical_lipschitz hDLMF a ha).continuous.comp
      (continuous_const.mul continuous_id)
  apply ((hφ.norm.const_mul ‖Complex.digamma (a : ℂ)‖).add
    (hxφ.norm.const_mul (2 * |c|))).mono'
    (hc.aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  filter_upwards [] with x
  have hd := digamma_vertical_bound_of_dlmf hDLMF a (c * x) ha
  have hn := norm_le_norm_sub_add
    (Complex.digamma ((a : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I))
    (Complex.digamma (a : ℂ))
  have hnorm : ‖Complex.digamma ((a : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I)‖ ≤
      ‖Complex.digamma (a : ℂ)‖ + 2 * |c| * |x| := by
    rw [abs_mul] at hd
    linarith
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [norm_mul, norm_smul, Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hnorm (norm_nonneg (φ x))]

/-- The real-part step is valid for arbitrary even complex-valued tests. -/
theorem digamma_even_integral (hDLMF : DLMFSeriesIdentity)
    (a : ℕ) (ha : 1 ≤ a) (c : ℝ) (φ : ℝ → ℂ) (heven : Function.Even φ)
    (hφ : Integrable φ) (hxφ : Integrable (fun x : ℝ => x • φ x)) :
    (∫ x, Complex.digamma ((a : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I) * φ x) =
      ∫ x, gammaIntegrand a c φ x := by
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  simpa only [gammaIntegrand, Complex.ofReal_natCast] using
    (even_integral_eq_re
      (fun x : ℝ => Complex.digamma (((a : ℝ) : ℂ) + ((c * x : ℝ) : ℂ) * Complex.I))
      φ (fun x => digamma_kernel_reflection hDLMF haR c x) heven
      (digamma_kernel_integrable hDLMF haR c φ hφ hxφ))

end DepthAspect.GammaLocal
