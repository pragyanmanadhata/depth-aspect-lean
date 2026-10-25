import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The trace polynomial

The recurrence here is the coefficient recurrence for (1 - t*z + m*z²)⁻¹
in equation (1). We prove its root expansion and the norm bound used in
(29) and (73), including the repeated-root endpoints.
-/

open scoped BigOperators

namespace DepthAspect

def tracePolynomial (t m : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => t
  | n + 2 => t * tracePolynomial t m (n + 1) - m * tracePolynomial t m n

def rootSum (α β : ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), α ^ i * β ^ (n - i)

theorem rootSum_succ (α β : ℂ) (n : ℕ) :
    rootSum α β (n + 1) = α * rootSum α β n + β ^ (n + 1) := by
  unfold rootSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rootSum_recurrence (α β : ℂ) (n : ℕ) :
    rootSum α β (n + 2) =
      (α + β) * rootSum α β (n + 1) - α * β * rootSum α β n := by
  rw [rootSum_succ α β (n + 1), rootSum_succ α β n]
  rw [show n + 1 + 1 = n + 2 by omega, pow_succ β (n + 1)]
  ring

theorem tracePolynomial_eq_rootSum (α β : ℂ) (n : ℕ) :
    tracePolynomial (α + β) (α * β) n = rootSum α β n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [tracePolynomial, rootSum]
  | one => simp [tracePolynomial, rootSum, Finset.sum_range_succ, add_comm]
  | more n ih₀ ih₁ =>
    rw [tracePolynomial, ih₀, ih₁, rootSum_recurrence]

theorem norm_rootSum_le (α β : ℂ) (r : ℝ) (n : ℕ)
    (hα : ‖α‖ = r) (hβ : ‖β‖ = r) :
    ‖rootSum α β n‖ ≤ (n + 1) * r ^ n := by
  unfold rootSum
  calc
    ‖∑ i ∈ Finset.range (n + 1), α ^ i * β ^ (n - i)‖ ≤
        ∑ i ∈ Finset.range (n + 1), ‖α ^ i * β ^ (n - i)‖ := norm_sum_le _ _
    _ = ∑ _i ∈ Finset.range (n + 1), r ^ n := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [norm_mul, norm_pow, norm_pow, hα, hβ, ← pow_add,
        Nat.add_sub_of_le hi']
    _ = (n + 1) * r ^ n := by simp

/-- The polynomial bound from a pair of equal-modulus roots. -/
theorem norm_tracePolynomial_le_of_roots (t m α β : ℂ) (r : ℝ) (n : ℕ)
    (hs : α + β = t) (hp : α * β = m) (hα : ‖α‖ = r) (hβ : ‖β‖ = r) :
    ‖tracePolynomial t m n‖ ≤ (n + 1) * r ^ n := by
  rw [← hs, ← hp, tracePolynomial_eq_rootSum]
  exact norm_rootSum_le α β r n hα hβ

/-- An explicit pair of conjugate roots for t² ≤ 4m. -/
theorem conjugate_roots (t m : ℝ) (h : t ^ 2 ≤ 4 * m) :
    let α : ℂ := ⟨t / 2, Real.sqrt (m - (t / 2) ^ 2)⟩
    let β : ℂ := ⟨t / 2, -Real.sqrt (m - (t / 2) ^ 2)⟩
    α + β = (t : ℂ) ∧ α * β = (m : ℂ) ∧
      ‖α‖ = Real.sqrt m ∧ ‖β‖ = Real.sqrt m := by
  dsimp only
  have hd : 0 ≤ m - (t / 2) ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Complex.ext <;> simp
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re]
      nlinarith
    · simp; ring
  · rw [Complex.norm_def, Complex.normSq_mk]
    congr 1
    nlinarith
  · rw [Complex.norm_def, Complex.normSq_mk]
    congr 1
    nlinarith

/-- Equations (29) and (73), expressed using integral powers of √m.
Taking n = k-2 yields (k-1)*(√m)^(k-2). -/
theorem norm_tracePolynomial_le (t m : ℝ) (n : ℕ) (h : t ^ 2 ≤ 4 * m) :
    ‖tracePolynomial (t : ℂ) (m : ℂ) n‖ ≤ (n + 1) * (Real.sqrt m) ^ n := by
  obtain ⟨hs, hp, hα, hβ⟩ := conjugate_roots t m h
  exact norm_tracePolynomial_le_of_roots _ _ _ _ _ n hs hp hα hβ

/-- The repeated-root formula, including both signs at t² = 4m. -/
theorem tracePolynomial_double_root (α : ℂ) (n : ℕ) :
    tracePolynomial (2 * α) (α ^ 2) n = (n + 1) * α ^ n := by
  have h : (2 * α) = α + α := by ring
  rw [h, pow_two, tracePolynomial_eq_rootSum]
  unfold rootSum
  calc
    (∑ i ∈ Finset.range (n + 1), α ^ i * α ^ (n - i)) =
        ∑ _i ∈ Finset.range (n + 1), α ^ n := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [← pow_add, Nat.add_sub_of_le hi']
    _ = (n + 1) * α ^ n := by simp

end DepthAspect
