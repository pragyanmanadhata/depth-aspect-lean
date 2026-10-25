import DepthAspect.TraceTrigonometry
import DepthAspect.SignedTraceInterface
import Mathlib.Tactic.FieldSimp

/-!
# Exact normalization of a signed elliptic prime term

The trace polynomial is the actual coefficient polynomial, and its
trigonometric identity is proved in `TraceTrigonometry`. This module cancels
the square-root class factor and the individual eigenvalue normalization;
the resulting cosine/L-value expression is a conclusion.
-/
namespace DepthAspect.SignedSieve

theorem sign_product (r : ℕ) :
    (-1 : ℝ) ^ (r + 1) * (-1 : ℝ) ^ r = -1 := by
  have hs : ((-1 : ℝ) ^ r) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm r 2, pow_mul]
    norm_num
  rw [pow_succ]
  nlinarith

/-- The numerical cancellation behind (75) and (76), before choosing the
depth-dependent finite coefficient or the fundamental discriminant. -/
theorem normalizedClassTerm (r : ℕ) (t v m : ℝ)
    (hv : 0 < v) (hm : 0 < m) (ht : t ^ 2 < 4 * v * m) (L : ℂ) :
    (-1 : ℂ) ^ (r + 1) *
      tracePolynomial ((t / Real.sqrt v : ℝ) : ℂ) (m : ℂ) (2 * r) *
      ((Real.sqrt (4 * v * m - t ^ 2) / Real.pi : ℝ) : ℂ) * L /
      ((m ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
    -((2 * Real.sqrt v / Real.pi *
      Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin (t / (2 * Real.sqrt (v * m)))) : ℝ) : ℂ) * L := by
  have hp : m ^ ((r : ℝ) + 1 / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hm _)
  have hs : Real.sqrt (4 * v * m - t ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  let c : ℝ := Real.cos ((2 * (r : ℝ) + 1) *
    Real.arcsin (t / (2 * Real.sqrt (v * m))))
  have hn : (-1 : ℝ) ^ (r + 1) *
      (2 * (-1 : ℝ) ^ r * m ^ ((r : ℝ) + 1 / 2) * Real.sqrt v * c /
        Real.sqrt (4 * v * m - t ^ 2)) *
      (Real.sqrt (4 * v * m - t ^ 2) / Real.pi) /
      m ^ ((r : ℝ) + 1 / 2) = -(2 * Real.sqrt v / Real.pi * c) := by
    calc
      _ = ((-1 : ℝ) ^ (r + 1) * (-1 : ℝ) ^ r) *
          (2 * Real.sqrt v / Real.pi * c) := by
        field_simp [hp, hs, Real.pi_ne_zero] <;> ring
      _ = _ := by rw [sign_product]; ring
  rw [TraceTrigonometry.tracePolynomial_signed_formula r t v m hv hm ht]
  change (-1 : ℂ) ^ (r + 1) *
      ((2 * (-1 : ℝ) ^ r * m ^ ((r : ℝ) + 1 / 2) * Real.sqrt v * c /
        Real.sqrt (4 * v * m - t ^ 2) : ℝ) : ℂ) *
      ((Real.sqrt (4 * v * m - t ^ 2) / Real.pi : ℝ) : ℂ) * L /
      ((m ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
    -((2 * Real.sqrt v / Real.pi * c : ℝ) : ℂ) * L
  calc
    _ = (((-1 : ℝ) ^ (r + 1) *
        (2 * (-1 : ℝ) ^ r * m ^ ((r : ℝ) + 1 / 2) * Real.sqrt v * c /
          Real.sqrt (4 * v * m - t ^ 2)) *
        (Real.sqrt (4 * v * m - t ^ 2) / Real.pi) /
        m ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * L := by
      push_cast
      ring
    _ = _ := by rw [hn]; push_cast; ring

end DepthAspect.SignedSieve
