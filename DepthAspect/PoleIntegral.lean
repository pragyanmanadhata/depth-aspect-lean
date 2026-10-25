import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Group.Ext

/-!
# Symmetric vertical integrals of the simple pole

The function 1/(σ+it) is not absolutely integrable on the whole line.
Everything here is a finite interval integral or its symmetric limit; no
unordered Bochner integral is substituted for this principal value.
-/

open Filter MeasureTheory
open scoped Topology
namespace DepthAspect.PoleIntegral

theorem reciprocal_vertical_eq (σ t : ℝ) :
    ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹ =
      (σ / (σ ^ 2 + t ^ 2) : ℝ) - (t / (σ ^ 2 + t ^ 2) : ℝ) * Complex.I := by
  apply Complex.ext <;>
    simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, one_mul,
      add_zero, zero_add, sub_zero, zero_sub, pow_two, div_eq_mul_inv] <;> ring

noncomputable def primitive (σ t : ℝ) : ℂ :=
  (Real.arctan (t / σ) : ℂ) - (Complex.I / 2) * (Real.log (σ ^ 2 + t ^ 2) : ℂ)

theorem primitive_hasDerivAt {σ : ℝ} (hσ : σ ≠ 0) (t : ℝ) :
    HasDerivAt (primitive σ) (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) t := by
  have hd : σ ^ 2 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hda : 1 + (t / σ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hA : HasDerivAt (fun u : ℝ => Real.arctan (u / σ))
      (σ / (σ ^ 2 + t ^ 2)) t := by
    have hraw : HasDerivAt (fun u : ℝ => Real.arctan (u / σ))
        ((1 / (1 + (t / σ) ^ 2)) * (1 / σ)) t := by
      simpa only [id_eq] using ((hasDerivAt_id t).div_const σ).arctan
    have heq : (1 / (1 + (t / σ) ^ 2)) * (1 / σ) = σ / (σ ^ 2 + t ^ 2) := by
      field_simp [hσ, hd, hda] <;> ring
    rwa [heq] at hraw
  have hL : HasDerivAt (fun u : ℝ => Real.log (σ ^ 2 + u ^ 2))
      (2 * t / (σ ^ 2 + t ^ 2)) t := by
    simpa using (((hasDerivAt_id t).pow 2).const_add (σ ^ 2)).log hd
  have h := hA.ofReal_comp.sub (hL.ofReal_comp.const_mul (Complex.I / 2))
  convert h using 1 <;> first
    | exact AddCommGroup.ext rfl
    | rfl
    | (rw [reciprocal_vertical_eq]; push_cast; ring)

theorem vertical_reciprocal_continuous {σ : ℝ} (hσ : σ ≠ 0) :
    Continuous (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  intro t ht
  apply hσ
  have h := congrArg Complex.re ht
  simpa using h

/-- Exact finite-interval formula, valid with either sign of σ. -/
theorem integral_vertical_reciprocal {σ : ℝ} (hσ : σ ≠ 0) (T : ℝ) :
    (∫ t : ℝ in -T..T, ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) =
      2 * (Real.arctan (T / σ) : ℂ) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_hasDerivAt hσ t)
    ((vertical_reciprocal_continuous hσ).intervalIntegrable (-T) T)]
  simp only [primitive, neg_div, Real.arctan_neg, neg_sq, Complex.ofReal_neg]
  ring

/-- The right-hand vertical simple-pole integral tends to π. -/
theorem symmetric_limit_pos {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T,
      ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) atTop (𝓝 (Real.pi : ℂ)) := by
  have hdiv : Tendsto (fun T : ℝ => T / σ) atTop atTop :=
    tendsto_id.atTop_div_const hσ
  have ha := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hdiv
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ha
  have h := hc.const_mul (2 : ℂ)
  simpa only [Function.comp_def, integral_vertical_reciprocal hσ.ne', Complex.ofReal_div,
    Complex.ofReal_ofNat, mul_div_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using h

/-- The left-hand vertical simple-pole integral tends to -π. -/
theorem symmetric_limit_neg {σ : ℝ} (hσ : σ < 0) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in -T..T,
      ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) atTop (𝓝 (-(Real.pi : ℂ))) := by
  have hdiv : Tendsto (fun T : ℝ => T / σ) atTop atBot :=
    tendsto_id.atTop_div_const_of_neg hσ
  have ha := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp hdiv
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp ha
  have h := hc.const_mul (2 : ℂ)
  simpa only [Function.comp_def, integral_vertical_reciprocal hσ.ne, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat, mul_neg,
    mul_div_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using h

end DepthAspect.PoleIntegral
