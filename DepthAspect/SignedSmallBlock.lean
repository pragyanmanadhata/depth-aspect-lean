import DepthAspect.SmallMurmurationWeight
import DepthAspect.UnsignedDensity

/-!
# The last dyadic block below three

The character-average theorems require an upper endpoint at least three.
An interval with 2 ≤ A ≤ B < 3 contains no odd prime, and its main integral
is bounded directly by the proved small-argument bound for M.
-/
namespace DepthAspect.SignedSmallBlock
open MeasureTheory Set MurmurationArithmetic
open scoped BigOperators FourierTransform SchwartzMap

theorem prime_interval_empty (L s : ℝ) {A B : ℝ} (hA : 2 ≤ A) (hB : B < 3) :
    (UnsignedDensity.primeBases L s).filter
      (fun p : ℕ => A < (p : ℝ) ∧ (p : ℝ) ≤ B) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpbase, hpA, hpB⟩ := Finset.mem_filter.mp hp
  have hc := (Finset.mem_filter.mp hpbase).2
  have hp3 : 3 ≤ p := by have := hc.1.two_le; omega
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  linarith

/-- The missing tiny final block has the same N^(-1/2) majorant as the
first component of (112), with a fixed test-dependent constant. -/
theorem main_integral_small_block (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ A B N L : ℝ, 2 ≤ A → A ≤ B → B < 3 → 3 ≤ N →
      ∀ h : 𝓢(ℝ, ℂ),
      ‖∫ v in (A / N)..(B / N), (M a ℓ v / v) • h (Real.log (N * v) / L)‖ ≤
        (C * Real.sqrt 3 * ‖h.toBoundedContinuousFunction‖) *
          N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := SmallMurmurationWeight.small_weighted_interval a hℓ
  refine ⟨C, hC, ?_⟩
  intro A B N L hA hAB hB hN h
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have ht := hb (A / N) (B / N) ‖h.toBoundedContinuousFunction‖
    (div_nonneg (by linarith) hN0.le)
    (div_le_div_of_nonneg_right hAB hN0.le) (div_pos hB0 hN0)
    ((div_le_one hN0).mpr (by linarith)) (norm_nonneg _)
    (fun v => h (Real.log (N * v) / L))
    (fun v _ => h.toBoundedContinuousFunction.norm_coe_le_norm _)
  apply ht.trans
  have hs : Real.sqrt (B / N) ≤ Real.sqrt (3 / N) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hB.le hN0.le)
  calc
    _ ≤ C * ‖h.toBoundedContinuousFunction‖ * Real.sqrt (3 / N) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow]
      ring

end DepthAspect.SignedSmallBlock
