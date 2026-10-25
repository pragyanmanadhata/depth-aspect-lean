import DepthAspect.PrimitiveBound
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Complex test functions and a bounded real primitive

This extends the integration-by-parts step in (115) to complex absolutely
continuous test functions, retaining the sharp total-variation bound. The
complex fundamental theorem is derived from its two real components. No
pointwise differentiability hypothesis is substituted for absolute continuity.

The construction and boundedness of the specific arithmetic primitive remain
separate obligations; they are not asserted in this file.
-/

open MeasureTheory Set
open scoped Topology NNReal

namespace DepthAspect

/-- Lipschitz postcomposition preserves absolute continuity. -/
theorem absolutelyContinuous_comp_lipschitz
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : ℝ → E} {g : E → F} {a b : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzWith K g) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero (fun t => ?_) (fun t => ?_)
    (by simpa only [mul_zero] using Filter.Tendsto.const_mul (K : ℝ) hf)
  · exact Finset.sum_nonneg fun _ _ => dist_nonneg
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun _ _ => hg.dist_le_mul _ _

theorem complex_ac_re {h : ℝ → ℂ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b) :
    AbsolutelyContinuousOnInterval (fun x => (h x).re) a b :=
  absolutelyContinuous_comp_lipschitz hh (RCLike.lipschitzWith_re (K := ℂ))

theorem complex_ac_im {h : ℝ → ℂ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b) :
    AbsolutelyContinuousOnInterval (fun x => (h x).im) a b :=
  absolutelyContinuous_comp_lipschitz hh (RCLike.lipschitzWith_im (K := ℂ))

/-- Reconstruction of a complex derivative from the real derivatives. -/
noncomputable def componentDeriv (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((deriv (fun t => (h t).re) x : ℝ) : ℂ) +
    ((deriv (fun t => (h t).im) x : ℝ) : ℂ) * Complex.I

theorem complex_ac_ae_hasDerivAt {h : ℝ → ℂ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b) :
    ∀ᵐ x ∂volume, x ∈ uIcc a b → HasDerivAt h (componentDeriv h x) x := by
  filter_upwards [(complex_ac_re hh).ae_differentiableAt,
    (complex_ac_im hh).ae_differentiableAt] with x hr hi hx
  have hd := ((hr hx).hasDerivAt.ofReal_comp).fun_add
    (((hi hx).hasDerivAt.ofReal_comp).mul_const Complex.I)
  simpa only [componentDeriv, Pi.add_apply, Complex.re_add_im] using hd

theorem complex_ac_ae_deriv {h : ℝ → ℂ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b) :
    ∀ᵐ x ∂volume, x ∈ uIcc a b → deriv h x = componentDeriv h x := by
  filter_upwards [complex_ac_ae_hasDerivAt hh] with x hx hxab
  exact (hx hxab).deriv

private theorem intervalIntegrable_complex_ofReal {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume a b :=
  ⟨Complex.ofRealCLM.integrable_comp hf.1, Complex.ofRealCLM.integrable_comp hf.2⟩

theorem complex_ac_intervalIntegrable_componentDeriv {h : ℝ → ℂ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b) :
    IntervalIntegrable (componentDeriv h) volume a b := by
  exact (intervalIntegrable_complex_ofReal (complex_ac_re hh).intervalIntegrable_deriv).add
    ((intervalIntegrable_complex_ofReal (complex_ac_im hh).intervalIntegrable_deriv).mul_const
      Complex.I)

theorem complex_ac_intervalIntegrable_deriv {h : ℝ → ℂ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b) :
    IntervalIntegrable (deriv h) volume a b := by
  apply (complex_ac_intervalIntegrable_componentDeriv hh).congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [complex_ac_ae_deriv hh] with x hx hxab
  exact (hx (uIoc_subset_uIcc hxab)).symm

/-- The fundamental theorem for a complex absolutely continuous function,
proved using the real fundamental theorem twice. -/
theorem complex_ac_integral_deriv_eq_sub {h : ℝ → ℂ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b) :
    (∫ x in a..b, deriv h x) = h b - h a := by
  have heq : (∫ x in a..b, deriv h x) = ∫ x in a..b, componentDeriv h x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [complex_ac_ae_deriv hh] with x hx hxab
    exact hx (uIoc_subset_uIcc hxab)
  rw [heq]
  unfold componentDeriv
  rw [intervalIntegral.integral_add
    (intervalIntegrable_complex_ofReal (complex_ac_re hh).intervalIntegrable_deriv)
    ((intervalIntegrable_complex_ofReal (complex_ac_im hh).intervalIntegrable_deriv).mul_const
      Complex.I)]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, (complex_ac_re hh).integral_deriv_eq_sub,
    (complex_ac_im hh).integral_deriv_eq_sub]
  apply Complex.ext <;> simp

/-- Integration by parts for a real AC multiplier and a complex AC test. -/
theorem complex_ac_integral_smul_deriv {h : ℝ → ℂ} {P : ℝ → ℝ} {a b : ℝ}
    (hh : AbsolutelyContinuousOnInterval h a b)
    (hP : AbsolutelyContinuousOnInterval P a b) :
    (∫ x in a..b, deriv P x • h x) =
      P b • h b - P a • h a - ∫ x in a..b, P x • deriv h x := by
  have hs : (∫ x in a..b, deriv P x • h x + P x • deriv h x) =
      P b • h b - P a • h a := by
    rw [← complex_ac_integral_deriv_eq_sub (hP.fun_smul hh)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hP.ae_differentiableAt, complex_ac_ae_hasDerivAt hh] with x hp hx hxab
    have hmem := uIoc_subset_uIcc hxab
    have hd := (hp hmem).hasDerivAt.fun_smul (hx hmem)
    rw [(hx hmem).deriv]
    simpa only [Pi.smul_apply, add_comm] using hd.deriv.symm
  rw [intervalIntegral.integral_add
    (hP.intervalIntegrable_deriv.smul_continuousOn hh.continuousOn)
    ((complex_ac_intervalIntegrable_deriv hh).continuousOn_smul hP.continuousOn)] at hs
  exact eq_sub_of_add_eq hs

/-- The sharp total-variation bound for a complex AC test vanishing at both
endpoints and a bounded real AC primitive. -/
theorem bounded_primitive_pairing_complex {a b C : ℝ} {h : ℝ → ℂ} {P : ℝ → ℝ}
    (hab : a ≤ b) (hh : AbsolutelyContinuousOnInterval h a b)
    (hP : AbsolutelyContinuousOnInterval P a b)
    (ha : h a = 0) (hb : h b = 0)
    (hbound : ∀ x ∈ Icc a b, |P x| ≤ C) :
    ‖∫ x in a..b, deriv P x • h x‖ ≤ C * ∫ x in a..b, ‖deriv h x‖ := by
  have hparts := complex_ac_integral_smul_deriv hh hP
  rw [ha, hb] at hparts
  simp only [smul_zero, sub_self, zero_sub] at hparts
  rw [hparts, norm_neg]
  have hi : IntervalIntegrable (fun x => C * ‖deriv h x‖) volume a b :=
    (complex_ac_intervalIntegrable_deriv hh).norm.const_mul C
  calc
    ‖∫ x in a..b, P x • deriv h x‖ ≤ ∫ x in a..b, C * ‖deriv h x‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab _ hi
      exact Filter.Eventually.of_forall fun x hx => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbound x ⟨hx.1.le, hx.2⟩) (norm_nonneg _)
    _ = C * ∫ x in a..b, ‖deriv h x‖ := intervalIntegral.integral_const_mul _ _

/-- A density specified a.e. as the primitive's derivative gives the same
bound, including at exceptional points of piecewise defined densities. -/
theorem bounded_primitive_pairing_complex_of_ae {a b C : ℝ}
    {h : ℝ → ℂ} {P e : ℝ → ℝ}
    (hab : a ≤ b) (hh : AbsolutelyContinuousOnInterval h a b)
    (hP : AbsolutelyContinuousOnInterval P a b)
    (ha : h a = 0) (hb : h b = 0)
    (hbound : ∀ x ∈ Icc a b, |P x| ≤ C)
    (he : ∀ᵐ x ∂volume, x ∈ uIoc a b → e x = deriv P x) :
    ‖∫ x in a..b, e x • h x‖ ≤ C * ∫ x in a..b, ‖deriv h x‖ := by
  have hi : (∫ x in a..b, e x • h x) = ∫ x in a..b, deriv P x • h x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [he] with x hx hxab
    rw [hx hxab]
  rw [hi]
  exact bounded_primitive_pairing_complex hab hh hP ha hb hbound

end DepthAspect
