import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Actual prime-power removal for the Dirichlet GRH estimate

The weighted difference between the von-Mangoldt sum and the logarithmic
prime sum is bounded by Mathlib's proved Chebyshev ψ−θ estimate. No separate
prime-power counting premise is introduced.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.PrimePowerRemoval
open Finset ArithmeticFunction

/-- The actual cumulative von-Mangoldt sum with arbitrary complex weights. -/
def vonMangoldtSum (w : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊u⌋₊, w n * (vonMangoldt n : ℂ)

/-- The actual logarithmic prime sum with the same weights. -/
def primeSum (w : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊u⌋₊, if n.Prime then w n * (Real.log n : ℂ) else 0

theorem difference_eq (w : ℕ → ℂ) (u : ℝ) :
    vonMangoldtSum w u - primeSum w u =
      ∑ n ∈ Icc 0 ⌊u⌋₊, if ¬n.Prime then w n * (vonMangoldt n : ℂ) else 0 := by
  rw [vonMangoldtSum, primeSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp [hp]

theorem nonprime_sum_eq (u : ℝ) :
    (∑ n ∈ Icc 0 ⌊u⌋₊, if ¬n.Prime then vonMangoldt n else 0) =
      Chebyshev.psi u - Chebyshev.theta u := by
  rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc,
    Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp [hp]

/-- Removing all higher prime powers costs at most 2√u logu for every bounded
complex coefficient sequence. -/
theorem norm_difference_le (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1)
    {u : ℝ} (hu : 1 ≤ u) :
    ‖vonMangoldtSum w u - primeSum w u‖ ≤ 2 * Real.sqrt u * Real.log u := by
  rw [difference_eq]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊u⌋₊,
        ‖if ¬n.Prime then w n * (vonMangoldt n : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 0 ⌊u⌋₊, if ¬n.Prime then vonMangoldt n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · simp [hp]
      · simp only [hp, not_false_eq_true, ↓reduceIte]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (vonMangoldt_nonneg (n := n))]
        exact mul_le_of_le_one_left (vonMangoldt_nonneg (n := n)) (hw n)
    _ = Chebyshev.psi u - Chebyshev.theta u := nonprime_sum_eq u
    _ ≤ _ := Chebyshev.psi_sub_theta_le hu

/-- The character version used in passing from the cited primitive GRH bound
to (92). The norm hypothesis is discharged by the actual character theorem. -/
theorem character_norm_difference_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {u : ℝ} (hu : 1 ≤ u) :
    ‖vonMangoldtSum (fun n => χ (n : ZMod q)) u -
      primeSum (fun n => χ (n : ZMod q)) u‖ ≤ 2 * Real.sqrt u * Real.log u :=
  norm_difference_le _ (fun n => χ.norm_le_one _) hu

end DepthAspect.PrimePowerRemoval
