import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Compact Fourier support and the entire extension

The Fourier–Laplace integral is an actual complex-valued integral. This file
establishes the extension and estimates used in Lemma 4.5, without any
assumption about the zeros of modular L-functions.
-/

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

namespace DepthAspect.EntireExtension

noncomputable def twoPiI : ℂ := (2 * Real.pi : ℝ) * Complex.I

noncomputable def kernel (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (twoPiI * z * (t : ℂ))

noncomputable def extension (s : ℝ) (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in -s..s, h t * kernel z t

theorem kernel_continuous : Continuous (fun p : ℂ × ℝ => kernel p.1 p.2) := by
  unfold kernel
  fun_prop

theorem kernel_hasDerivAt_complex (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w : ℂ => kernel w t)
      ((twoPiI * (t : ℂ)) * kernel z t) z := by
  unfold kernel
  simpa only [id_eq, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id z).const_mul twoPiI).mul_const (t : ℂ)).cexp

theorem kernel_hasDerivAt_real (z : ℂ) (t : ℝ) :
    HasDerivAt (kernel z) ((twoPiI * z) * kernel z t) t := by
  unfold kernel
  simpa only [id_eq, Complex.ofReal_one, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id t).ofReal_comp).const_mul (twoPiI * z)).cexp

/-- Differentiation under the integral is justified by a continuous derivative
on a compact product neighborhood, giving a uniform integrable majorant. -/
theorem extension_hasDerivAt {s : ℝ} (hs : 0 ≤ s) {h : ℝ → ℂ}
    (hh : Continuous h) (z : ℂ) :
    HasDerivAt (extension s h)
      (∫ t in -s..s, h t * ((twoPiI * (t : ℂ)) * kernel z t)) z := by
  let F' : ℂ × ℝ → ℂ := fun p => h p.2 * ((twoPiI * (p.2 : ℂ)) * kernel p.1 p.2)
  have hc : Continuous F' := by
    dsimp [F']
    exact (hh.comp continuous_snd).mul
      ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).mul kernel_continuous)
  have hcompact : IsCompact (closedBall z 1 ×ˢ Icc (-s) s) :=
    (isCompact_closedBall z 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hc.norm.continuousOn
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun t : ℝ => h t * kernel w t)
        (volume.restrict (uIoc (-s) s)) := by
    apply Eventually.of_forall
    intro w
    exact (hh.mul (kernel_continuous.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  have hint : IntervalIntegrable (fun t => h t * kernel z t) volume (-s) s :=
    (hh.mul (kernel_continuous.comp (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  have hderivmeas : AEStronglyMeasurable (fun t => F' (z, t))
      (volume.restrict (uIoc (-s) s)) :=
    (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume, t ∈ uIoc (-s) s →
      ∀ w ∈ ball z 1, ‖F' (w, t)‖ ≤ C := by
    apply Eventually.of_forall
    intro t ht w hw
    have ht' : t ∈ Icc (-s) s := by
      rw [uIoc_of_le (by linarith)] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact hC (mem_image_of_mem _ ⟨mem_closedBall.mpr (mem_ball.mp hw).le, ht'⟩)
  have hdiff : ∀ᵐ t ∂volume, t ∈ uIoc (-s) s → ∀ w ∈ ball z 1,
      HasDerivAt (fun v : ℂ => h t * kernel v t) (F' (w, t)) w := by
    apply Eventually.of_forall
    intro t _ w _
    exact (kernel_hasDerivAt_complex w t).const_mul (h t)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z (by norm_num : (0 : ℝ) < 1)) hmeas hint hderivmeas hbound
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (-s) s) hdiff).2

/-- The integral in (53) is entire for every continuous integrand on its
compact frequency interval. -/
theorem extension_entire {s : ℝ} (hs : 0 ≤ s) {h : ℝ → ℂ} (hh : Continuous h) :
    Differentiable ℂ (extension s h) :=
  fun z => (extension_hasDerivAt hs hh z).differentiableAt

theorem norm_kernel (z : ℂ) (t : ℝ) :
    ‖kernel z t‖ = Real.exp (-2 * Real.pi * t * z.im) := by
  rw [kernel, Complex.norm_exp]
  congr 1
  simp [twoPiI, Complex.mul_re, Complex.mul_im]
  ring

theorem norm_kernel_le {s t : ℝ} (ht : |t| ≤ s) (z : ℂ) :
    ‖kernel z t‖ ≤ Real.exp (2 * Real.pi * s * |z.im|) := by
  rw [norm_kernel]
  apply Real.exp_le_exp.mpr
  have hm : -(t * z.im) ≤ s * |z.im| := calc
    -(t * z.im) ≤ |t * z.im| := neg_le_abs _
    _ = |t| * |z.im| := abs_mul _ _
    _ ≤ s * |z.im| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  nlinarith [Real.pi_pos]

/-- The direct exponential-type estimate, with the actual L¹ integral. -/
theorem norm_extension_le {s : ℝ} (hs : 0 ≤ s) {h : ℝ → ℂ}
    (hh : Continuous h) (z : ℂ) :
    ‖extension s h z‖ ≤ (∫ t in -s..s, ‖h t‖) *
      Real.exp (2 * Real.pi * s * |z.im|) := by
  unfold extension
  calc
    ‖∫ t in -s..s, h t * kernel z t‖ ≤
        ∫ t in -s..s, ‖h t‖ * Real.exp (2 * Real.pi * s * |z.im|) := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      · apply Eventually.of_forall
        intro t ht
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_kernel_le (abs_le.mpr ⟨ht.1.le, ht.2⟩) z) (norm_nonneg _)
      · exact hh.norm.intervalIntegrable _ _ |>.mul_const _
    _ = _ := intervalIntegral.integral_mul_const _ _

/-- A continuous function supported in a closed interval vanishes at its
endpoints as well. This justifies all boundary terms in repeated integration. -/
theorem endpoints_zero {s : ℝ} {h : ℝ → ℂ} (hh : Continuous h)
    (hsupp : Function.support h ⊆ Icc (-s) s) : h (-s) = 0 ∧ h s = 0 := by
  have hi : Function.support h ⊆ Ioo (-s) s := by
    simpa only [interior_Icc] using hh.isOpen_support.subset_interior_iff.mpr hsupp
  constructor
  · by_contra hn
    have hx := hi hn
    exact (lt_irrefl (-s)) hx.1
  · by_contra hn
    have hx := hi hn
    exact (lt_irrefl s) hx.2

theorem iteratedDeriv_support {s : ℝ} {h : ℝ → ℂ}
    (hsupp : Function.support h ⊆ Icc (-s) s) (J : ℕ) :
    tsupport (iteratedDeriv J h) ⊆ Icc (-s) s := by
  induction J with
  | zero => simpa only [iteratedDeriv_zero, tsupport] using closure_minimal hsupp isClosed_Icc
  | succ J ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- One integration by parts, including the vanishing boundary terms. -/
theorem extension_deriv {s : ℝ} {h : ℝ → ℂ} (hh : Differentiable ℝ h)
    (hd : Continuous (deriv h)) (hsupp : Function.support h ⊆ Icc (-s) s) (z : ℂ) :
    extension s (deriv h) z = -(twoPiI * z) * extension s h z := by
  have hk : Continuous (kernel z) := kernel_continuous.comp (continuous_const.prodMk continuous_id)
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := -s) (b := s)
    hh.continuous.continuousOn hk.continuousOn
    (fun t _ => (hh t).hasDerivAt) (fun t _ => kernel_hasDerivAt_real z t)
    (hd.intervalIntegrable _ _)
    ((continuous_const.mul hk).intervalIntegrable _ _)
  obtain ⟨ha, hb⟩ := endpoints_zero hh.continuous hsupp
  rw [ha, hb] at hp
  simp only [zero_mul, sub_self, zero_sub] at hp
  have hi : (∫ t in -s..s, h t * ((twoPiI * z) * kernel z t)) =
      (twoPiI * z) * extension s h z := by
    unfold extension
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hi] at hp
  change (twoPiI * z) * extension s h z = -extension s (deriv h) z at hp
  linear_combination hp

/-- Repeated integration by parts is an exact identity, not an assumed decay
estimate. Every derivative has the same compact support. -/
theorem extension_iteratedDeriv {s : ℝ} {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Icc (-s) s) (J : ℕ) (z : ℂ) :
    extension s (iteratedDeriv J h) z = (-(twoPiI * z)) ^ J * extension s h z := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [iteratedDeriv_succ, extension_deriv
      (hh.differentiable_iteratedDeriv J (ENat.natCast_lt_of_coe_top_le_withTop le_rfl J))
      (by simpa only [← iteratedDeriv_succ] using hh.continuous_iteratedDeriv (J + 1) (ENat.natCast_le_of_coe_top_le_withTop le_rfl (J + 1)))
      ((subset_tsupport (iteratedDeriv J h)).trans (iteratedDeriv_support hsupp J)), ih, pow_succ]
    ring

end DepthAspect.EntireExtension
