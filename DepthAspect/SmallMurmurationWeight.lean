import DepthAspect.MurmurationPrimitive
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! The actual small-v contribution in (113), including the early-level
case in which the support cutoff is below two. -/
open MeasureTheory Set
open scoped SchwartzMap
namespace DepthAspect.SmallMurmurationWeight
open MurmurationArithmetic MurmurationPrimitive

/-- Testing the actual square-root bound near zero against a bounded
complex function preserves the integrable square-root majorant. -/
theorem small_weighted_integral (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ V H : ℝ, 0 < V → V ≤ 1 → 0 ≤ H →
      ∀ w : ℝ → ℂ, (∀ v ∈ Ioc 0 V, ‖w v‖ ≤ H) →
      ‖∫ v in (0)..V, (M a ℓ v / v) • w v‖ ≤ C * H * Real.sqrt V := by
  obtain ⟨C, hC, hb⟩ := M_small_bound a hℓ
  refine ⟨2 * C, by positivity, ?_⟩
  intro V H hV hV1 hH w hw
  have hi : IntervalIntegrable (fun v : ℝ => (C * H) * v ^ (-(1 / 2 : ℝ))) volume 0 V :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hV.le
    (f := fun v => (M a ℓ v / v) • w v)
    (g := fun v : ℝ => (C * H) * v ^ (-(1 / 2 : ℝ))) (by
      filter_upwards [] with v hv
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hv.1]
      calc
        _ ≤ ((C * Real.sqrt v) / v) * H :=
          mul_le_mul (div_le_div_of_nonneg_right (hb v hv.1 (hv.2.trans hV1)) hv.1.le)
            (hw v hv) (norm_nonneg _)
            (div_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg v)) hv.1.le)
        _ = _ := by
          rw [Real.sqrt_eq_rpow, mul_div_assoc]
          nth_rw 2 [← Real.rpow_one v]
          rw [← Real.rpow_sub hv.1]
          norm_num
          ring) hi
  have he : (∫ v in (0)..V, (C * H) * v ^ (-(1 / 2 : ℝ))) =
      (2 * C) * H * Real.sqrt V := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
    norm_num [← Real.sqrt_eq_rpow]
    ring
  simpa only [he] using hnorm

/-- The same integrable majorant applies on any subinterval near zero.
This includes a final dyadic interval whose prime endpoint is below three. -/
theorem small_weighted_interval (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ A B H : ℝ, 0 ≤ A → A ≤ B → 0 < B → B ≤ 1 → 0 ≤ H →
      ∀ w : ℝ → ℂ, (∀ v ∈ Ioc A B, ‖w v‖ ≤ H) →
      ‖∫ v in A..B, (M a ℓ v / v) • w v‖ ≤ C * H * Real.sqrt B := by
  obtain ⟨C, hC, hb⟩ := M_small_bound a hℓ
  refine ⟨2 * C, by positivity, ?_⟩
  intro A B H hA hAB hB hB1 hH w hw
  have hi : IntervalIntegrable (fun v : ℝ => (C * H) * v ^ (-(1 / 2 : ℝ))) volume A B :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hAB
    (f := fun v => (M a ℓ v / v) • w v)
    (g := fun v : ℝ => (C * H) * v ^ (-(1 / 2 : ℝ))) (by
      filter_upwards [] with v hv
      have hv0 : 0 < v := hA.trans_lt hv.1
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hv0]
      calc
        _ ≤ ((C * Real.sqrt v) / v) * H :=
          mul_le_mul (div_le_div_of_nonneg_right (hb v hv0 (hv.2.trans hB1)) hv0.le)
            (hw v hv) (norm_nonneg _) (by positivity)
        _ = _ := by
          rw [Real.sqrt_eq_rpow, mul_div_assoc]
          nth_rw 2 [← Real.rpow_one v]
          rw [← Real.rpow_sub hv0]
          norm_num
          ring) hi
  apply hnorm.trans
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num [← Real.sqrt_eq_rpow]
  nlinarith [Real.sqrt_nonneg A, mul_nonneg (mul_nonneg hC.le hH) (Real.sqrt_nonneg A)]

/-- The logarithmically rescaled Schwartz test requires no extra uniform
boundedness assumption. -/
theorem schwartz_small_weighted_integral (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ V N L : ℝ, 0 < V → V ≤ 1 → ∀ h : 𝓢(ℝ, ℂ),
      ‖∫ v in (0)..V, (M a ℓ v / v) • h (Real.log (N * v) / L)‖ ≤
        C * ‖h.toBoundedContinuousFunction‖ * Real.sqrt V := by
  obtain ⟨C, hC, hb⟩ := small_weighted_integral a hℓ
  refine ⟨C, hC, ?_⟩
  intro V N L hV hV1 h
  exact hb V _ hV hV1 (norm_nonneg _) _
    (fun v _ => h.toBoundedContinuousFunction.norm_coe_le_norm _)

end DepthAspect.SmallMurmurationWeight
