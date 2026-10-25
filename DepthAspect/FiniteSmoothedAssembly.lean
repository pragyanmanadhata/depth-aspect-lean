import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact finite-prime/exponential-series discrepancy decomposition

This is finite-sum and absolutely-convergent-series algebra, before the
arithmetic estimates are inserted. The three terms are the L-value smoothing
error, the coefficient-wise prime discrepancy, and the averaged coefficient
tail. None is silently identified with zero, and each convergence premise is
visible for the later arithmetic instantiation to discharge.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.FiniteSmoothedAssembly

/-- The literal positive exponential smoothing weight at the positive index n+1. -/
def weight (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((n + 1 : ℕ) : ℝ) / x) / ((n + 1 : ℕ) : ℝ)

 theorem weight_nonneg (x : ℝ) (n : ℕ) : 0 ≤ weight x n := by
  unfold weight
  positivity

variable {ι : Type*} (S : Finset ι) (w L : ι → ℂ) (a : ι → ℕ → ℂ)
variable (b : ℕ → ℂ) (I : ℂ) (x : ℝ)

def smoothed (c : ℕ → ℂ) : ℂ := ∑' n : ℕ, (weight x n : ℂ) * c (n + 1)
def value : ℂ := ∑' n : ℕ, b (n + 1) / ((n + 1 : ℕ) : ℂ)
def coefficientError (n : ℕ) : ℂ :=
  (∑ p ∈ S, w p * a p (n + 1)) - b (n + 1) * I

theorem coefficientError_summable
    (ha : ∀ p ∈ S, Summable (fun n => (weight x n : ℂ) * a p (n + 1)))
    (hb : Summable (fun n => (weight x n : ℂ) * b (n + 1))) :
    Summable (fun n => (weight x n : ℂ) * coefficientError S w a b I n) := by
  have hs := (summable_sum (s := S) (fun p hp => (ha p hp).mul_left (w p))).sub
    (hb.mul_right I)
  apply hs.congr
  intro n
  unfold coefficientError
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    ring
  · ring

/-- Exact decomposition used in (103), with literal infinite series and
finite prime weights. Convergence is required explicitly before exchanging. -/
theorem discrepancy_identity
    (ha : ∀ p ∈ S, Summable (fun n => (weight x n : ℂ) * a p (n + 1)))
    (hb : Summable (fun n => (weight x n : ℂ) * b (n + 1))) :
    (∑ p ∈ S, w p * L p) - value b * I =
      (∑ p ∈ S, w p * (L p - smoothed x (a p))) +
      (∑' n : ℕ, (weight x n : ℂ) * coefficientError S w a b I n) +
      (smoothed x b - value b) * I := by
  have hexchange : (∑' n : ℕ, (weight x n : ℂ) * coefficientError S w a b I n) =
      (∑ p ∈ S, w p * smoothed x (a p)) - smoothed x b * I := by
    have hs := summable_sum (s := S) (fun p hp => (ha p hp).mul_left (w p))
    have heq : (fun n : ℕ => (weight x n : ℂ) * coefficientError S w a b I n) =
        (fun n => (∑ p ∈ S, w p * ((weight x n : ℂ) * a p (n + 1))) -
          ((weight x n : ℂ) * b (n + 1)) * I) := by
      funext n
      unfold coefficientError
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        ring
      · ring
    rw [heq, hs.tsum_sub (hb.mul_right I), Summable.tsum_finsetSum,
      tsum_mul_right]
    · simp only [tsum_mul_left, smoothed]
    · intro p hp
      exact (ha p hp).mul_left (w p)
  rw [hexchange]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- Quantitative triangle inequality after the exact decomposition. The
supplied functions U and R are estimates to be proved from (102) and (98),
not assumptions attached to a claimed final prime-average theorem. -/
theorem discrepancy_norm_le
    (ha : ∀ p ∈ S, Summable (fun n => (weight x n : ℂ) * a p (n + 1)))
    (hb : Summable (fun n => (weight x n : ℂ) * b (n + 1)))
    (U : ι → ℝ) (hU : ∀ p ∈ S, ‖L p - smoothed x (a p)‖ ≤ U p)
    (R : ℕ → ℝ) (hR : ∀ n, ‖coefficientError S w a b I n‖ ≤ R n)
    (hRs : Summable (fun n => weight x n * R n)) :
    ‖(∑ p ∈ S, w p * L p) - value b * I‖ ≤
      (∑ p ∈ S, ‖w p‖ * U p) + (∑' n, weight x n * R n) +
        ‖smoothed x b - value b‖ * ‖I‖ := by
  rw [discrepancy_identity S w L a b I x ha hb]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hU p hp) (norm_nonneg _)
    · apply tsum_of_norm_bounded hRs.hasSum
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_nonneg x n)]
      exact mul_le_mul_of_nonneg_left (hR n) (weight_nonneg x n)
  · exact le_of_eq (norm_mul _ _)

end DepthAspect.FiniteSmoothedAssembly
