import DepthAspect.TracePolynomial
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Identifying the trace polynomial with the generating function

This supplies the formal-power-series meaning of equation (1): the coefficients
of `(1 - t X + m X²)⁻¹` are exactly the recurrence-defined `tracePolynomial`.
No convergence or choice of complex roots is required for this identity.
-/

namespace DepthAspect

open PowerSeries

noncomputable def traceSeries (t m : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (tracePolynomial t m)

theorem traceSeries_mul_denominator (t m : ℂ) :
    traceSeries t m * (1 - C t * X + C m * X ^ 2) = 1 := by
  have heq : traceSeries t m * (1 - C t * X + C m * X ^ 2) =
      traceSeries t m - (traceSeries t m * C t) * X +
        ((traceSeries t m * C m) * X) * X := by ring
  rw [heq]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [traceSeries, tracePolynomial]
  | succ n =>
    cases n with
    | zero => simp [traceSeries, tracePolynomial]
    | succ n =>
      simp only [map_add, map_sub, coeff_succ_mul_X, coeff_mul_C,
        traceSeries, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false]
      rw [tracePolynomial]
      ring

theorem traceSeries_eq_inverse (t m : ℂ) :
    traceSeries t m = (1 - C t * X + C m * X ^ 2)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).mpr
  exact traceSeries_mul_denominator t m

/-- The definition in equation (1), with its coefficient extraction made explicit. -/
theorem tracePolynomial_eq_coefficient (t m : ℂ) (n : ℕ) :
    tracePolynomial t m n =
      PowerSeries.coeff n ((1 - C t * X + C m * X ^ 2)⁻¹) := by
  rw [← traceSeries_eq_inverse]
  simp [traceSeries]

end DepthAspect
