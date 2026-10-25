import DepthAspect.Dimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quantitative root-sign projection

These bounds justify removal of the denominator in (119), including for
complex test functions. They are reductions from explicit unsigned, signed,
and imbalance estimates, not proofs of the estimates themselves.
-/

namespace DepthAspect

theorem normalization_error (z A : ℂ) (δ : ℝ) (hδ : |δ| ≤ (1 / 2 : ℝ)) :
    ‖z / ((1 + δ : ℝ) : ℂ) - A‖ ≤ 2 * ‖z - A‖ + 2 * |δ| * ‖A‖ := by
  obtain ⟨hl, hu⟩ := abs_le.mp hδ
  have hp : 0 < 1 + δ := by linarith
  have hn : ((1 + δ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  have heq : z / ((1 + δ : ℝ) : ℂ) - A =
      (z - A) / ((1 + δ : ℝ) : ℂ) +
      ((((1 + δ)⁻¹ - 1 : ℝ) : ℂ) * A) := by
    push_cast
    field_simp
    ring
  have hfirst : ‖(z - A) / ((1 + δ : ℝ) : ℂ)‖ ≤ 2 * ‖z - A‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    apply (div_le_iff₀ hp).2
    nlinarith [norm_nonneg (z - A)]
  have hsecond : ‖(((1 + δ)⁻¹ - 1 : ℝ) : ℂ) * A‖ ≤ 2 * |δ| * ‖A‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (inverse_one_add_error δ hδ) (norm_nonneg A)
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Quantitative plus-family reduction, with no reality assumption on the
zero sums or test function. -/
theorem plus_density_error (U S A B : ℂ) (δ eu es : ℝ)
    (hδ : |δ| ≤ (1 / 2 : ℝ))
    (hU : ‖U - A‖ ≤ eu) (hS : ‖S - B‖ ≤ es) :
    ‖(U + S) / ((1 + δ : ℝ) : ℂ) - (A + B)‖ ≤
      2 * (eu + es) + 2 * |δ| * (‖A‖ + ‖B‖) := by
  have hdiff : ‖U + S - (A + B)‖ ≤ eu + es := by
    have heq : U + S - (A + B) = (U - A) + (S - B) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hU hS)
  have hmain := norm_add_le A B
  have hnorm := normalization_error (U + S) (A + B) δ hδ
  have hprod := mul_le_mul_of_nonneg_left hmain (show 0 ≤ 2 * |δ| by positivity)
  nlinarith

/-- Quantitative minus-family reduction. -/
theorem minus_density_error (U S A B : ℂ) (δ eu es : ℝ)
    (hδ : |δ| ≤ (1 / 2 : ℝ))
    (hU : ‖U - A‖ ≤ eu) (hS : ‖S - B‖ ≤ es) :
    ‖(U - S) / ((1 - δ : ℝ) : ℂ) - (A - B)‖ ≤
      2 * (eu + es) + 2 * |δ| * (‖A‖ + ‖B‖) := by
  have hS' : ‖-S - -B‖ ≤ es := by
    rw [show -S - -B = -(S - B) by ring, norm_neg]
    exact hS
  have h := plus_density_error U (-S) A (-B) (-δ) eu es (by simpa using hδ) hU hS'
  simpa only [sub_eq_add_neg, abs_neg, norm_neg] using h

/-- The SO(even) main term after Fourier inversion and splitting the integral
into |ξ|≤1 and |ξ|>1. The analytic integral identities are explicit premises. -/
theorem even_density_main_term (h0 phi0 inside outside : ℂ)
    (hinversion : phi0 = inside + outside) :
    (h0 + phi0 / 2) + (-outside / 2) = h0 + inside / 2 := by
  rw [hinversion]
  ring

/-- The corresponding SO(odd) main term, including the central delta mass. -/
theorem odd_density_main_term (h0 phi0 inside outside : ℂ)
    (hinversion : phi0 = inside + outside) :
    (h0 + phi0 / 2) - (-outside / 2) = h0 - inside / 2 + phi0 := by
  rw [hinversion]
  ring

end DepthAspect
