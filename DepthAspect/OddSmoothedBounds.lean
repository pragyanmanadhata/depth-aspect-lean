import DepthAspect.OddDepthCoefficientAverages
import DepthAspect.GlobalSmoothedBounds
import DepthAspect.OddEulerAtOne

/-! Convergence, smoothing tails, and the exact main coefficient for (105).
These concern the actual odd averaged sequence, not an unspecified majorant. -/
noncomputable section
open scoped BigOperators
namespace DepthAspect.OddSmoothedBounds
open OddDepthCoefficientAverages OddDepthResidueCoefficient GlobalSmoothedBounds

theorem norm_coefficient_le (t : ℤ) (m : ℕ) :
    ‖OddAverageEuler.coefficient t m‖ ≤ 1 := by
  by_cases hm : m = 0
  · simp [hm]
  letI : NeZero m := ⟨hm⟩
  rw [← principal_mean t]
  exact LocalCoefficientNorm.norm_principal_le_one _ (norm_residueFunction_le m t)

theorem summable_at_one (t : ℤ) :
    Summable (fun n : ℕ => OddAverageEuler.coefficient t (n + 1) /
      ((n + 1 : ℕ) : ℂ)) := by
  apply Summable.of_norm
  simpa only [norm_div, Complex.norm_natCast] using (absolute_coefficients t).1

theorem valueAtOne_bound (t : ℤ) :
    ‖valueAtOne t‖ ≤ CoefficientTail.tailConstant / (1 - Real.exp (-1)) := by
  apply (norm_tsum_le_tsum_norm (summable_at_one t).norm).trans
  simpa only [norm_div, Complex.norm_natCast] using (absolute_coefficients t).2

theorem valueAtOne_eq_LSeries (t : ℤ) :
    valueAtOne t = LSeries (OddAverageEuler.coefficient t) 1 := by
  have hs : Summable (LSeries.term (OddAverageEuler.coefficient t) 1) :=
    (OddAverageEuler.summable_norm_terms t (s := 1) (by norm_num)).of_norm
  rw [LSeries, hs.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add, LSeries.term_of_ne_zero (Nat.succ_ne_zero _),
    Complex.cpow_one]
  rfl

/-- The literal G_t in (84), including t=0. -/
theorem valueAtOne_eq_primeWeight (t : ℤ) :
    valueAtOne t = ((Real.pi : ℂ) ^ 2 / 8) *
      (ArithmeticWeights.integerPrimeWeight 2 t : ℂ) := by
  rw [valueAtOne_eq_LSeries, OddEulerAtOne.odd_series_at_one]

theorem average_smoothed_summable (t : ℤ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n => (FiniteSmoothedAssembly.weight x n : ℂ) *
      OddAverageEuler.coefficient t (n + 1)) :=
  smoothed_summable _ (norm_coefficient_le t) hx

theorem average_smoothed_tail (t : ℤ) {x : ℝ} (hx : 0 < x) :
    ‖FiniteSmoothedAssembly.smoothed x (OddAverageEuler.coefficient t) - valueAtOne t‖ ≤
      CoefficientTail.tailConstant / Real.sqrt x := by
  have hs := average_smoothed_summable t hx
  have hu := summable_at_one t
  have htail := coefficient_tail t hx
  unfold FiniteSmoothedAssembly.smoothed valueAtOne
  rw [← hs.tsum_sub hu]
  calc
    _ ≤ ∑' n : ℕ, ‖(FiniteSmoothedAssembly.weight x n : ℂ) *
        OddAverageEuler.coefficient t (n + 1) -
        OddAverageEuler.coefficient t (n + 1) / ((n + 1 : ℕ) : ℂ)‖ :=
      norm_tsum_le_tsum_norm (hs.sub hu).norm
    _ = ∑' n : ℕ, ‖OddAverageEuler.coefficient t (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
        (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x)) := by
      apply tsum_congr
      intro n
      have he : Real.exp (-((n + 1 : ℕ) : ℝ) / x) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hx.le)
      have heq : (FiniteSmoothedAssembly.weight x n : ℂ) *
          OddAverageEuler.coefficient t (n + 1) -
          OddAverageEuler.coefficient t (n + 1) / ((n + 1 : ℕ) : ℂ) =
        -(OddAverageEuler.coefficient t (n + 1) / ((n + 1 : ℕ) : ℂ)) *
          ((1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x) : ℝ) : ℂ) := by
        unfold FiniteSmoothedAssembly.weight
        push_cast
        ring
      rw [heq, norm_mul, norm_neg, norm_div, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    _ ≤ _ := htail.2

end DepthAspect.OddSmoothedBounds
