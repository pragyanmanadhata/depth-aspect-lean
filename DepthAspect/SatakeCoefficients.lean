import DepthAspect.TracePolynomial
import Mathlib.Tactic.FieldSimp

/-!
# The actual local Euler coefficients in the explicit formula

The two reciprocal Euler roots are explicit complex numbers. Their unit norms
and product one are the Deligne/normalization input (55). The coefficient
identities and all bounds below are proved from those inputs.
-/

open scoped BigOperators
namespace DepthAspect.SatakeCoefficients

/-- The coefficient a_f(p^j) of the logarithmic Euler-factor derivative. -/
def powerCoefficient (α β : ℂ) (j : ℕ) : ℂ := α ^ j + β ^ j

@[simp] theorem powerCoefficient_one (α β : ℂ) :
    powerCoefficient α β 1 = α + β := by simp [powerCoefficient]

/-- The square coefficient is λ_f(p²)−1 when the product of roots is one.
`tracePolynomial` is already proved to be the reciprocal Euler-series coefficient. -/
theorem powerCoefficient_two (α β : ℂ) (hp : α * β = 1) :
    powerCoefficient α β 2 = tracePolynomial (α + β) 1 2 - 1 := by
  unfold powerCoefficient
  calc
    α ^ 2 + β ^ 2 = (α + β) ^ 2 - 2 * (α * β) := by ring
    _ = (α + β) ^ 2 - 2 := by rw [hp]; ring
    _ = _ := by simp [tracePolynomial]; ring

/-- The uniform bound |a_f(p^j)|≤2, for every nonnegative integer j. -/
theorem norm_powerCoefficient_le_two (α β : ℂ)
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (j : ℕ) :
    ‖powerCoefficient α β j‖ ≤ 2 := by
  calc
    _ ≤ ‖α ^ j‖ + ‖β ^ j‖ := norm_add_le _ _
    _ = 2 := by rw [norm_pow, norm_pow, hα, hβ]; norm_num

/-- Taking a finite natural average, with real weights of magnitude at most
one, preserves the prime-power bound. This includes both signs ε_f=±1. -/
theorem norm_weighted_average_le_two {ι : Type*} (S : Finset ι)
    (α β : ι → ℂ) (w : ι → ℝ) (j : ℕ)
    (hα : ∀ f ∈ S, ‖α f‖ = 1) (hβ : ∀ f ∈ S, ‖β f‖ = 1)
    (hw : ∀ f ∈ S, |w f| ≤ 1) :
    ‖(∑ f ∈ S, (w f : ℂ) * powerCoefficient (α f) (β f) j) / (S.card : ℂ)‖ ≤ 2 := by
  by_cases hc : S.card = 0
  · simp [hc]
  have hcpos : (0 : ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hs : ‖∑ f ∈ S, (w f : ℂ) * powerCoefficient (α f) (β f) j‖ ≤
      (S.card : ℝ) * 2 := by
    calc
      _ ≤ ∑ f ∈ S, ‖(w f : ℂ) * powerCoefficient (α f) (β f) j‖ := norm_sum_le _ _
      _ ≤ ∑ _f ∈ S, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro f hf
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simpa only [one_mul] using mul_le_mul (hw f hf)
          (norm_powerCoefficient_le_two (α f) (β f) (hα f hf) (hβ f hf) j)
          (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ = _ := by simp
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ hcpos).mpr (by simpa only [mul_comm] using hs)

end DepthAspect.SatakeCoefficients
