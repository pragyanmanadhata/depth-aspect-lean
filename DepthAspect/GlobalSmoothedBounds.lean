import DepthAspect.GlobalCoefficientTail
import DepthAspect.FiniteSmoothedAssembly
import DepthAspect.MellinSmoothing

/-! Absolute convergence and tail of the literal smoothed average. -/
noncomputable section
open scoped BigOperators
namespace DepthAspect.GlobalSmoothedBounds
open GlobalResidueMean GlobalResidueCoefficient GlobalCoefficientTail

 theorem norm_twisted_le (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8)
    (x : (ZMod (modulus m))ˣ) : ‖twistedFunction m t χ x‖ ≤ 1 := by
  have hminus : ‖χ (-1)‖ = 1 := by simpa using χ.unit_norm_eq_one (-1 : (ZMod 8)ˣ)
  rw [twistedFunction, norm_mul, norm_mul, hminus,
    DirichletCharacter.unit_norm_eq_one, one_mul, one_mul]
  exact LocalCoefficientNorm.norm_coefficientFunction_le m t x

 theorem norm_sequence_le (t : ℤ) (χ : DirichletCharacter ℂ 8) (m : ℕ) :
    ‖sequence t χ m‖ ≤ 1 := by
  by_cases hm : m = 0
  · simp [GlobalResidueMean.sequence, hm]
  letI : NeZero m := ⟨hm⟩
  rw [GlobalResidueMean.sequence_eq, GlobalResidueMean.average]
  exact LocalCoefficientNorm.norm_principal_le_one _ (norm_twisted_le m t χ)

 theorem weight_mul_eq_smoothedTerm (a : ℕ → ℂ) (x : ℝ) (n : ℕ) :
    (FiniteSmoothedAssembly.weight x n : ℂ) * a (n + 1) =
      MellinSmoothing.smoothedTerm a x n := by
  unfold FiniteSmoothedAssembly.weight MellinSmoothing.smoothedTerm
  push_cast
  ring

 theorem smoothed_summable (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n => (FiniteSmoothedAssembly.weight x n : ℂ) * a (n + 1)) := by
  simp_rw [weight_mul_eq_smoothedTerm]
  exact (MellinSmoothing.smoothed_hasSum_initialIntegral a ha hx).summable

 theorem average_smoothed_summable (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n => (FiniteSmoothedAssembly.weight x n : ℂ) * sequence t χ (n + 1)) :=
  smoothed_summable _ (norm_sequence_le t χ) hx

/-- The exact norm estimate needed for the third term of (103). -/
theorem average_smoothed_tail (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {x : ℝ} (hx : 0 < x) :
    ‖FiniteSmoothedAssembly.smoothed x (sequence t χ) - valueAtOne t χ‖ ≤
      CoefficientTail.tailConstant / Real.sqrt x := by
  have hs := average_smoothed_summable t χ hx
  have hu := summable_at_one t χ
  have htail := exponential_tail t χ hx
  unfold FiniteSmoothedAssembly.smoothed valueAtOne
  rw [← hs.tsum_sub hu]
  calc
    _ ≤ ∑' n : ℕ, ‖(FiniteSmoothedAssembly.weight x n : ℂ) * sequence t χ (n + 1) -
        sequence t χ (n + 1) / ((n + 1 : ℕ) : ℂ)‖ :=
      norm_tsum_le_tsum_norm (hs.sub hu).norm
    _ = ∑' n : ℕ, ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
        (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x)) := by
      apply tsum_congr
      intro n
      have he : Real.exp (-((n + 1 : ℕ) : ℝ) / x) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hx.le)
      have heq : (FiniteSmoothedAssembly.weight x n : ℂ) * sequence t χ (n + 1) -
          sequence t χ (n + 1) / ((n + 1 : ℕ) : ℂ) =
        -(sequence t χ (n + 1) / ((n + 1 : ℕ) : ℂ)) *
          ((1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x) : ℝ) : ℂ) := by
        unfold FiniteSmoothedAssembly.weight
        push_cast
        ring
      rw [heq, norm_mul, norm_neg, norm_div, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    _ ≤ _ := htail.2

end DepthAspect.GlobalSmoothedBounds
