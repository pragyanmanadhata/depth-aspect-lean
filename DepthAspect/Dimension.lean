import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact dimension and sign-balance arithmetic

The inputs in this file are the explicit dimension and signed-count formulas
cited in the paper. Those modular-form formulas are not proved here.
For even depth `n=2a`, put `q=2^a` and `N=q²`; for odd depth `n=2a+1`,
put `q=2^a` and `N=2q²`. Thus `n≥8` gives `q≥16` in the even case,
and `n≥7` gives `q≥8` in the odd case.
-/

namespace DepthAspect

noncomputable section

/-- Lemma 2.5, even-depth dimension after writing `N=q²`. -/
def evenDimension (k q : ℝ) : ℝ := (k - 1) * q ^ 2 / 32 - q / 8

/-- Lemma 2.5, odd-depth dimension after writing `N=2q²`. -/
def oddDimension (k q : ℝ) : ℝ := (k - 1) * q ^ 2 / 16

/-- Signed-count magnitude in the even-depth formula. -/
def evenImbalance (q : ℝ) : ℝ := q / 8

/-- Signed-count magnitude in the odd-depth formula. -/
def oddImbalance (q : ℝ) : ℝ := q / 4

/-- The dimension bounds in (15), even depth. -/
theorem even_dimension_bounds (k q : ℝ) (hk : 2 ≤ k) (hq : 16 ≤ q) :
    (k - 1) * q ^ 2 / 64 ≤ evenDimension k q ∧
      evenDimension k q ≤ (k - 1) * q ^ 2 / 32 := by
  unfold evenDimension
  have hq0 : 0 ≤ q := by linarith
  have hprod : q ^ 2 ≤ (k - 1) * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ k - 2 by linarith) (sq_nonneg q)]
  have hq_sq : 16 * q ≤ q ^ 2 := by
    nlinarith [mul_nonneg hq0 (show 0 ≤ q - 16 by linarith)]
  constructor <;> nlinarith

/-- The lower bound is positive, so the even-depth family is nonempty
whenever the supplied count is its dimension. -/
theorem even_dimension_pos (k q : ℝ) (hk : 2 ≤ k) (hq : 16 ≤ q) :
    0 < evenDimension k q := by
  have hb := (even_dimension_bounds k q hk hq).1
  have hk0 : 0 < k - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have hprod : 0 < (k - 1) * q ^ 2 := by positivity
  linarith

/-- The same dimension bounds, odd depth. -/
theorem odd_dimension_bounds (k q : ℝ) (hk : 2 ≤ k) (hq : 0 < q) :
    (k - 1) * (2 * q ^ 2) / 64 ≤ oddDimension k q ∧
      oddDimension k q = (k - 1) * (2 * q ^ 2) / 32 := by
  unfold oddDimension
  have hk0 : 0 < k - 1 := by linarith
  have hprod : 0 ≤ (k - 1) * q ^ 2 := by positivity
  constructor
  · nlinarith
  · ring

/-- Positive dimension in odd depth. -/
theorem odd_dimension_pos (k q : ℝ) (hk : 2 ≤ k) (hq : 0 < q) :
    0 < oddDimension k q := by
  unfold oddDimension
  have hk0 : 0 < k - 1 := by linarith
  positivity

/-- Exact formulas, rather than only the coarser asymptotic bound, show
that the signed-count magnitude is at most half the dimension. -/
theorem even_imbalance_le_half (k q : ℝ) (hk : 2 ≤ k) (hq : 16 ≤ q) :
    evenImbalance q ≤ evenDimension k q / 2 := by
  unfold evenImbalance evenDimension
  have hprod : q ^ 2 ≤ (k - 1) * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ k - 2 by linarith) (sq_nonneg q)]
  have hq_sq : 16 * q ≤ q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q - 16 by linarith)]
  nlinarith

/-- Includes the boundary `k=2, n=7`, where `q=8` and the ratio is `1/2`. -/
theorem odd_imbalance_le_half (k q : ℝ) (hk : 2 ≤ k) (hq : 8 ≤ q) :
    oddImbalance q ≤ oddDimension k q / 2 := by
  unfold oddImbalance oddDimension
  have hprod : q ^ 2 ≤ (k - 1) * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ k - 2 by linarith) (sq_nonneg q)]
  have hq_sq : 8 * q ≤ q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) (show 0 ≤ q - 8 by linarith)]
  nlinarith

/-- Both projected dimensions are positive under an imbalance bound. -/
theorem both_sign_dimensions_positive (d R : ℝ) (hd : 0 < d) (hR : |R| ≤ d / 2) :
    0 < (d + R) / 2 ∧ 0 < (d - R) / 2 := by
  rcases abs_le.mp hR with ⟨hl, hu⟩
  constructor <;> linarith

/-- The relative imbalance bound needed to remove the denominators in (119). -/
theorem relative_imbalance_le_half (d R : ℝ) (hd : 0 < d) (hR : |R| ≤ d / 2) :
    |R / d| ≤ (1 / 2 : ℝ) := by
  rw [abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  linarith

/-- Exact even-depth formulas imply that both root-sign classes have positive size. -/
theorem even_sign_dimensions_positive (k q R : ℝ) (hk : 2 ≤ k) (hq : 16 ≤ q)
    (hR : |R| = evenImbalance q) :
    0 < (evenDimension k q + R) / 2 ∧ 0 < (evenDimension k q - R) / 2 := by
  apply both_sign_dimensions_positive _ _ (even_dimension_pos k q hk hq)
  rw [hR]
  exact even_imbalance_le_half k q hk hq

/-- Exact odd-depth formulas give nonemptiness already at depth seven. -/
theorem odd_sign_dimensions_positive (k q R : ℝ) (hk : 2 ≤ k) (hq : 8 ≤ q)
    (hR : |R| = oddImbalance q) :
    0 < (oddDimension k q + R) / 2 ∧ 0 < (oddDimension k q - R) / 2 := by
  apply both_sign_dimensions_positive _ _ (odd_dimension_pos k q hk (by linarith))
  rw [hR]
  exact odd_imbalance_le_half k q hk hq

/-- The exceptional smallest parameters are safe: the two projected
sizes are `3` and `1` (their assignment to signs depends on the sign of `R`). -/
theorem odd_depth_seven_weight_two :
    oddDimension 2 8 = 4 ∧ oddImbalance 8 = 2 ∧
      (oddDimension 2 8 + oddImbalance 8) / 2 = 3 ∧
      (oddDimension 2 8 - oddImbalance 8) / 2 = 1 := by
  norm_num [oddDimension, oddImbalance]

/-- Scalar normalization equals one in odd depth. -/
theorem odd_scalar_coefficient (k q : ℝ) (hk : 2 ≤ k) (hq : 0 < q) :
    (k - 1) * (2 * q ^ 2) / (32 * oddDimension k q) = 1 := by
  have hk0 : k - 1 ≠ 0 := by linarith
  have hq0 : q ≠ 0 := ne_of_gt hq
  unfold oddDimension
  field_simp
  ring

/-- Bounds for the scalar normalization at even depth, from the exact dimension. -/
theorem even_scalar_coefficient_bounds (k q : ℝ) (hk : 2 ≤ k) (hq : 16 ≤ q) :
    1 ≤ (k - 1) * q ^ 2 / (32 * evenDimension k q) ∧
      (k - 1) * q ^ 2 / (32 * evenDimension k q) ≤ 2 := by
  have hd := even_dimension_pos k q hk hq
  have hb := even_dimension_bounds k q hk hq
  have hden : 0 < 32 * evenDimension k q := by positivity
  constructor
  · apply (le_div_iff₀ hden).2
    linarith [hb.2]
  · apply (div_le_iff₀ hden).2
    linarith [hb.1]

/-- The explicit `O(N⁻¹/²)` estimate in (15), with `q=√N`. -/
theorem even_scalar_coefficient_error (k q : ℝ) (hk : 2 ≤ k) (hq : 16 ≤ q) :
    |(k - 1) * q ^ 2 / (32 * evenDimension k q) - 1| ≤
      8 / ((k - 1) * q) := by
  have hd := even_dimension_pos k q hk hq
  have hq0 : 0 < q := by linarith
  have hk0 : 0 < k - 1 := by linarith
  have hden : 0 < (k - 1) * q := mul_pos hk0 hq0
  have hc := (even_scalar_coefficient_bounds k q hk hq).1
  rw [abs_of_nonneg (by linarith : 0 ≤ (k - 1) * q ^ 2 / (32 * evenDimension k q) - 1)]
  have heq : (k - 1) * q ^ 2 / (32 * evenDimension k q) - 1 =
      q / (8 * evenDimension k q) := by
    field_simp [ne_of_gt hd]
    unfold evenDimension
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity : 0 < 8 * evenDimension k q) hden).2
  have hb := (even_dimension_bounds k q hk hq).1
  nlinarith

/-- Denominator perturbation used after (119). Its hypothesis also proves
that the denominator is positive and therefore nonzero. -/
theorem inverse_one_add_error (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    |(1 + x)⁻¹ - 1| ≤ 2 * |x| := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  have hpos : 0 < 1 + x := by linarith
  have heq : (1 + x)⁻¹ - 1 = -x / (1 + x) := by
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hpos]
  apply (div_le_iff₀ hpos).2
  nlinarith [mul_nonneg (abs_nonneg x) (show 0 ≤ x + 1 / 2 by linarith)]

/-- The negative sign obeys the identical perturbation bound. -/
theorem inverse_one_sub_error (x : ℝ) (hx : |x| ≤ (1 / 2 : ℝ)) :
    |(1 - x)⁻¹ - 1| ≤ 2 * |x| := by
  simpa only [sub_eq_add_neg, abs_neg] using inverse_one_add_error (-x) (by simpa using hx)

end

end DepthAspect
