import DepthAspect.GlobalResidueMean
import DepthAspect.CoefficientTail

/-!
# Absolute convergence and the actual coefficient tail (85)

The input sequence is the literal normalized residue average from (81).
Its squarefree majorant is proved by local arithmetic and CRT, so no bound on
an unspecified sequence remains in these statements.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.GlobalCoefficientTail
open GlobalResidueMean

/-- The absolutely convergent value of the actual averaged Dirichlet series
at one. This differs from the conditionally convergent ψ_D series at one. -/
def valueAtOne (t : ℤ) (χ : DirichletCharacter ℂ 8) : ℂ :=
  ∑' n : ℕ, sequence t χ (n + 1) / ((n + 1 : ℕ) : ℂ)

 theorem absolute_summability (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    Summable (fun n : ℕ => ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ)) :=
  (CoefficientTail.absolute_series_summable_and_bound (sequence t χ)
    (sequence_majorant t χ)).1

 theorem summable_at_one (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    Summable (fun n : ℕ => sequence t χ (n + 1) / ((n + 1 : ℕ) : ℂ)) := by
  apply Summable.of_norm
  simpa only [norm_div, Complex.norm_natCast] using absolute_summability t χ

/-- The exact uniformly bounded absolute coefficient sum in (85). -/
theorem absolute_sum_bound (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    (∑' n : ℕ, ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ)) ≤
      CoefficientTail.tailConstant / (1 - Real.exp (-1)) :=
  (CoefficientTail.absolute_series_summable_and_bound (sequence t χ)
    (sequence_majorant t χ)).2

 theorem valueAtOne_bound (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    ‖valueAtOne t χ‖ ≤ CoefficientTail.tailConstant / (1 - Real.exp (-1)) := by
  apply (norm_tsum_le_tsum_norm (summable_at_one t χ).norm).trans
  simpa only [norm_div, Complex.norm_natCast] using absolute_sum_bound t χ

/-- Both convergence and the quantitative literal exponential-tail estimate. -/
theorem exponential_tail (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))) ∧
    (∑' n : ℕ, ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))) ≤
        CoefficientTail.tailConstant / Real.sqrt x :=
  CoefficientTail.tail_summable_and_bound (sequence t χ) (sequence_majorant t χ) hx

end DepthAspect.GlobalCoefficientTail
