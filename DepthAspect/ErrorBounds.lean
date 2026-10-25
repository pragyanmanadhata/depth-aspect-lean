import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorbing the power savings into the logarithmic error

This supplies the last step of (42) and (118) as an explicit inequality, rather
than an informal appeal to domination of logarithms by powers. The preceding
analytic error estimates are not proved or postulated in this file.
-/

namespace DepthAspect

/-- A uniform elementary estimate for every negative power, valid for x > 1. -/
theorem negative_power_mul_log_le {x a : ℝ} (hx : 1 < x) (ha : a < 0) :
    x ^ a * Real.log x ≤ 1 / (-a) := by
  have hx0 : 0 < x := by linarith
  have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le a
  have hlog := Real.log_le_rpow_div hx0.le (neg_pos.mpr ha)
  have heq : x ^ a * x ^ (-a) = 1 := by
    rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
  calc
    x ^ a * Real.log x ≤ x ^ a * (x ^ (-a) / (-a)) :=
      mul_le_mul_of_nonneg_left hlog hp
    _ = 1 / (-a) := by rw [← mul_div_assoc, heq]

/-- Here c = k² and x = N in the paper. The constant is explicit. -/
theorem negative_power_le_inverse_conductor_log {x c a : ℝ}
    (hx : 1 < x) (hc : 1 ≤ c) (ha : a < 0) :
    x ^ a ≤ (Real.log c + 1 / (-a)) / Real.log (c * x) := by
  have hx0 : 0 < x := by linarith
  have hc0 : 0 < c := by linarith
  have hcx : 1 < c * x := by nlinarith
  have hlog : 0 < Real.log (c * x) := Real.log_pos hcx
  have hpow : x ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le ha.le
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  apply (le_div_iff₀ hlog).2
  rw [Real.log_mul (ne_of_gt hc0) (ne_of_gt hx0), mul_add]
  have h₁ := mul_le_mul_of_nonneg_right hpow hlc
  have h₂ := negative_power_mul_log_le hx ha
  linarith

/-- Any finite collection of negative powers is absorbed into 1/log(c*x).
The finite-point majorant `hE` is an explicit hypothesis, not an axiom or a
claim that the paper's analytic work has already been formalized. -/
theorem absorb_power_errors {ι : Type*} (I : Finset ι) (a : ι → ℝ)
    {x c C E : ℝ} (hx : 1 < x) (hc : 1 ≤ c) (hC : 0 ≤ C)
    (ha : ∀ i ∈ I, a i < 0)
    (hE : E ≤ C * (1 / Real.log (c * x) + ∑ i ∈ I, x ^ a i)) :
    E ≤ C * (1 + ∑ i ∈ I, (Real.log c + 1 / (-a i))) /
      Real.log (c * x) := by
  have hp : (∑ i ∈ I, x ^ a i) ≤
      ∑ i ∈ I, (Real.log c + 1 / (-a i)) / Real.log (c * x) := by
    exact Finset.sum_le_sum fun i hi =>
      negative_power_le_inverse_conductor_log hx hc (ha i hi)
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hp
  calc
    E ≤ C * (1 / Real.log (c * x) + ∑ i ∈ I, x ^ a i) := hE
    _ ≤ C * (1 / Real.log (c * x) +
        (∑ i ∈ I, (Real.log c + 1 / (-a i))) / Real.log (c * x)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hp' : (∑ i ∈ I, x ^ a i) ≤
          (∑ i ∈ I, (Real.log c + 1 / (-a i))) / Real.log (c * x) := by
        simpa only [div_eq_mul_inv] using hp
      linarith
    _ = C * (1 + ∑ i ∈ I, (Real.log c + 1 / (-a i))) /
        Real.log (c * x) := by ring

/-- The dyadic conductor actually goes to infinity. -/
theorem dyadic_level_tendsto :
    Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

end DepthAspect
