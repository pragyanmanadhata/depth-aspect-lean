import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Linarith

/-!
# Pairing a bounded primitive with a test function

The analytic integration-by-parts step in (115), on an interval containing
the test's support. Absolute continuity accommodates the step at v = 1;
continuous differentiability of the primitive is not required.

Constructing the paper's specific primitive and proving its bound (Proposition
5.7) remain separate obligations. This theorem does not assume them globally.
-/

open MeasureTheory Set

namespace DepthAspect

/-- A bounded absolutely continuous primitive gives a uniform bound in terms
of the total variation of a test vanishing at both endpoints. -/
theorem bounded_primitive_pairing {a b C : ℝ} {h P : ℝ → ℝ}
    (hab : a ≤ b)
    (hh : AbsolutelyContinuousOnInterval h a b)
    (hP : AbsolutelyContinuousOnInterval P a b)
    (ha : h a = 0) (hb : h b = 0)
    (hbound : ∀ x ∈ Icc a b, |P x| ≤ C) :
    |∫ x in a..b, h x * deriv P x| ≤ C * ∫ x in a..b, |deriv h x| := by
  have hparts := hh.integral_mul_deriv_eq_deriv_mul hP
  rw [ha, hb] at hparts
  simp only [zero_mul, sub_self, zero_sub] at hparts
  rw [hparts, abs_neg]
  have hi : IntervalIntegrable (fun x => C * |deriv h x|) volume a b := by
    simpa only [Real.norm_eq_abs] using hh.intervalIntegrable_deriv.norm.const_mul C
  calc
    |∫ x in a..b, deriv h x * P x| = ‖∫ x in a..b, deriv h x * P x‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in a..b, C * |deriv h x| := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab _ hi
      exact Filter.Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        have hbx := hbound x ⟨hx.1.le, hx.2⟩
        nlinarith [abs_nonneg (deriv h x)]
    _ = C * ∫ x in a..b, |deriv h x| := intervalIntegral.integral_const_mul _ _

/-- A version for an a.e. specified density, which ignores exceptional
derivative points such as the jump in the comparison step function. -/
theorem bounded_primitive_pairing_of_ae {a b C : ℝ} {h P e : ℝ → ℝ}
    (hab : a ≤ b)
    (hh : AbsolutelyContinuousOnInterval h a b)
    (hP : AbsolutelyContinuousOnInterval P a b)
    (ha : h a = 0) (hb : h b = 0)
    (hbound : ∀ x ∈ Icc a b, |P x| ≤ C)
    (he : ∀ᵐ x ∂volume, x ∈ uIoc a b → e x = deriv P x) :
    |∫ x in a..b, h x * e x| ≤ C * ∫ x in a..b, |deriv h x| := by
  have hi : (∫ x in a..b, h x * e x) = ∫ x in a..b, h x * deriv P x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [he] with x hx hxab
    rw [hx hxab]
  rw [hi]
  exact bounded_primitive_pairing hab hh hP ha hb hbound

end DepthAspect
