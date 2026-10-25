import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The balancing step in the prime-averaging proof

These are elementary real inequalities. The analytic smoothing estimate (103)
is an explicit premise when it is used. This module does not assert that the
Dirichlet-L-function discrepancy satisfies that premise.
-/
namespace DepthAspect.Smoothing

/-- The value of `A / sqrt x + C * sqrt x` at the balancing choice `x=A/C`. -/
theorem balance_identity (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    A / Real.sqrt (A / C) + C * Real.sqrt (A / C) =
      2 * Real.sqrt (A * C) := by
  rw [Real.sqrt_div hA.le, Real.sqrt_mul hA.le]
  have ha : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hA)
  have hc : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC)
  have ha2 := Real.sq_sqrt hA.le
  have hc2 := Real.sq_sqrt hC.le
  field_simp
  rw [ha2, hc2]
  ring

/-- The smoothing parameter used in the nontrivial branch of Theorem 5.5. -/
noncomputable def balancedParameter (M V B : ℝ) : ℝ := M * Real.sqrt B / (M + V)

/-- The paper's choice is allowed: it lies between 1 and `sqrt B`. -/
theorem balancedParameter_mem (M V B : ℝ)
    (hM : 0 < M) (hV : 0 ≤ V) (_hB : 1 ≤ B)
    (hsmall : M + V ≤ M * Real.sqrt B) :
    1 ≤ balancedParameter M V B ∧ balancedParameter M V B ≤ Real.sqrt B := by
  have hMV : 0 < M + V := by linarith
  have hsB : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  constructor
  · rw [balancedParameter, le_div_iff₀ hMV]
    simpa using hsmall
  · rw [balancedParameter, div_le_iff₀ hMV]
    nlinarith

/-- The product of a scale and its square root yields the three-quarter
power after taking one further square root. -/
theorem sqrt_scale (B : ℝ) (hB : 0 < B) :
    Real.sqrt (B * Real.sqrt B) = B ^ (3 / 4 : ℝ) := by
  have h : B * Real.sqrt B = B ^ (3 / 2 : ℝ) := by
    calc
      _ = B ^ (1 : ℝ) * B ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hB]; norm_num
  rw [h, Real.sqrt_eq_rpow, ← Real.rpow_mul hB.le]
  norm_num

/-- Exact balance of the two leading terms in (103). This establishes the
three-quarter exponent before the arbitrarily small exponent losses. -/
theorem balanced_error (M V B E : ℝ)
    (hM : 0 < M) (hV : 0 ≤ V) (hB : 0 < B)
    (hE : E ≤ M * B / Real.sqrt (balancedParameter M V B) +
      (M + V) * Real.sqrt B * Real.sqrt (balancedParameter M V B)) :
    E ≤ 2 * Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ) := by
  have hMV : 0 < M + V := by linarith
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hsB2 := Real.sq_sqrt hB.le
  have hx : balancedParameter M V B = (M * B) / ((M + V) * Real.sqrt B) := by
    unfold balancedParameter
    field_simp
    exact hsB2
  have hb := balance_identity (M * B) ((M + V) * Real.sqrt B)
    (mul_pos hM hB) (mul_pos hMV hsB)
  rw [← hx] at hb
  have hp : (M * B) * ((M + V) * Real.sqrt B) =
      (M * (M + V)) * (B * Real.sqrt B) := by ring
  rw [hp, Real.sqrt_mul (mul_nonneg hM.le hMV.le), sqrt_scale B hB] at hb
  calc
    E ≤ _ := hE
    _ = _ := by rw [hb]; ring

/-- The complementary large-variation branch of Theorem 5.5: the trivial
estimate is already no larger than the desired geometric-mean scale. -/
theorem large_variation_error (M V B E : ℝ)
    (hM : 0 < M) (hV : 0 ≤ V) (hB : 0 < B)
    (hlarge : M * Real.sqrt B ≤ M + V) (hE : E ≤ M * B) :
    E ≤ Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ) := by
  have hMV : 0 ≤ M + V := by linarith
  have hAC : M * B ≤ (M + V) * Real.sqrt B := by
    calc
      M * B = (M * Real.sqrt B) * Real.sqrt B := by
        rw [mul_assoc, Real.mul_self_sqrt hB.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right hlarge (Real.sqrt_nonneg _)
  have hsq : (M * B) ^ 2 ≤ (M * B) * ((M + V) * Real.sqrt B) := by
    calc
      _ = (M * B) * (M * B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAC (mul_nonneg hM.le hB.le)
  have hg := Real.le_sqrt_of_sq_le hsq
  have hp : (M * B) * ((M + V) * Real.sqrt B) =
      (M * (M + V)) * (B * Real.sqrt B) := by ring
  rw [hp, Real.sqrt_mul (mul_nonneg hM.le hMV), sqrt_scale B hB] at hg
  exact hE.trans hg

/-- Optimization of a supplied smoothing bound and a supplied trivial bound.
The conclusion has exactly the three-quarter exponent of (104). A common
constant or a previously absorbed factor `B^ε` may be included in `C`.

The hypotheses explicitly expose the two analytic estimates; this theorem
proves their optimization, not those analytic estimates themselves. -/
theorem optimize_smoothing (M V B C E : ℝ)
    (hM : 0 < M) (hV : 0 ≤ V) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (htrivial : E ≤ C * M * B)
    (hsmooth : ∀ x : ℝ, 1 ≤ x → x ≤ Real.sqrt B →
      E ≤ C * (M * B / Real.sqrt x + (M + V) * Real.sqrt B * Real.sqrt x)) :
    E ≤ 2 * C * Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ) := by
  have hBpos : 0 < B := by linarith
  by_cases hsmall : M + V ≤ M * Real.sqrt B
  · have hm := balancedParameter_mem M V B hM hV hB hsmall
    have h := hsmooth (balancedParameter M V B) hm.1 hm.2
    have hb := balanced_error M V B
      (M * B / Real.sqrt (balancedParameter M V B) +
        (M + V) * Real.sqrt B * Real.sqrt (balancedParameter M V B))
      hM hV hBpos (le_refl _)
    calc
      E ≤ _ := h
      _ ≤ C * (2 * Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hb hC
      _ = _ := by ring
  · have hlarge : M * Real.sqrt B ≤ M + V := le_of_lt (lt_of_not_ge hsmall)
    have hb := large_variation_error M V B (M * B) hM hV hBpos hlarge (le_refl _)
    have hscale : 0 ≤ Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ) := by positivity
    calc
      E ≤ C * (M * B) := by simpa [mul_assoc] using htrivial
      _ ≤ C * (Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hb hC
      _ ≤ 2 * C * Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ) := by
        nlinarith [mul_nonneg hC hscale]

end DepthAspect.Smoothing
