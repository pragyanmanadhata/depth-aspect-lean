import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Bessel functions with a precise cited-input boundary

The function itself is the defining power series DLMF 10.2.2 at natural
orders. Its convergence and the small-argument estimate are proved here.
The separate cited identities are general statements about this function,
not the paper's kernel transform or murmuration conclusions.

Sources: https://dlmf.nist.gov/10.2.E2, https://dlmf.nist.gov/10.9.E2,
https://dlmf.nist.gov/10.6.E1, https://dlmf.nist.gov/10.17.E3,
https://dlmf.nist.gov/10.22.E9.
-/
open scoped BigOperators
open MeasureTheory Filter Asymptotics
namespace DepthAspect.BesselFirstKind

noncomputable def seriesTerm (m : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  (-1) ^ n * (t / 2) ^ (2 * n + m) /
    ((n.factorial : ℝ) * ((n + m).factorial : ℝ))

noncomputable def J (m : ℕ) (t : ℝ) : ℝ := ∑' n, seriesTerm m t n

theorem norm_seriesTerm_le (m : ℕ) (t : ℝ) (n : ℕ) :
    ‖seriesTerm m t n‖ ≤ |t / 2| ^ m * ((|t / 2| ^ 2) ^ n / (n.factorial : ℝ)) := by
  have hf : (1 : ℝ) ≤ (n + m).factorial := by exact_mod_cast Nat.factorial_pos (n + m)
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hd : (n.factorial : ℝ) ≤ (n.factorial : ℝ) * ((n + m).factorial : ℝ) := by
    nlinarith
  have hnorm : ‖seriesTerm m t n‖ =
      |t / 2| ^ (2 * n + m) / ((n.factorial : ℝ) * ((n + m).factorial : ℝ)) := by
    norm_num [seriesTerm, norm_div, norm_mul, norm_pow, Real.norm_eq_abs, abs_div]
  rw [hnorm]
  calc
    _ ≤ |t / 2| ^ (2 * n + m) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hn hd
    _ = _ := by rw [pow_add, pow_mul] <;> ring

/-- Absolute convergence of the defining Bessel series at every real point. -/
theorem seriesTerm_norm_summable (m : ℕ) (t : ℝ) :
    Summable (fun n => ‖seriesTerm m t n‖) := by
  apply ((Real.summable_pow_div_factorial (|t / 2| ^ 2)).mul_left (|t / 2| ^ m)).of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · exact norm_seriesTerm_le m t

theorem seriesTerm_summable (m : ℕ) (t : ℝ) : Summable (seriesTerm m t) :=
  (seriesTerm_norm_summable m t).of_norm

theorem seriesTerm_neg (m n : ℕ) (t : ℝ) :
    seriesTerm m (-t) n = (-1 : ℝ) ^ m * seriesTerm m t n := by
  have he : (-t) / 2 = (-1 : ℝ) * (t / 2) := by ring
  have hpar : (-1 : ℝ) ^ (2 * n + m) = (-1 : ℝ) ^ m := by
    rw [pow_add, pow_mul]
    norm_num
  unfold seriesTerm
  rw [he, mul_pow, hpar]
  ring

/-- Natural-order parity follows from the defining series. -/
theorem J_neg (m : ℕ) (t : ℝ) : J m (-t) = (-1 : ℝ) ^ m * J m t := by
  unfold J
  simp_rw [seriesTerm_neg]
  exact tsum_mul_left

theorem J_zero_of_pos {m : ℕ} (hm : 0 < m) : J m 0 = 0 := by
  unfold J
  calc
    _ = ∑' n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      have hn : 2 * n + m ≠ 0 := by omega
      simp [seriesTerm, zero_pow hn]
    _ = 0 := tsum_zero

/-- The value at order zero and argument zero is fixed by the defining series. -/
theorem J_zero_zero : J 0 0 = 1 := by
  unfold J
  rw [tsum_eq_single 0]
  · norm_num [seriesTerm]
  · intro n hn
    have he : 2 * n + 0 ≠ 0 := by omega
    simp [seriesTerm, hn, zero_pow he]

theorem J_at_zero (m : ℕ) : J m 0 = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simpa using J_zero_zero
  · rw [if_neg hm]
    exact J_zero_of_pos (Nat.pos_of_ne_zero hm)

set_option maxHeartbeats 800000 in
/-- An explicit small-argument estimate, derived from the power series. -/
theorem small_argument_bound (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |J m t| ≤ Real.exp 1 * t ^ m := by
  have hbase : 0 ≤ t / 2 := by positivity
  have hbase1 : t / 2 ≤ 1 := by linarith
  have hterm (n : ℕ) : ‖seriesTerm m t n‖ ≤ t ^ m * (1 ^ n / (n.factorial : ℝ)) := by
    apply (norm_seriesTerm_le m t n).trans
    rw [abs_of_nonneg hbase]
    apply mul_le_mul
    · exact pow_le_pow_left₀ hbase (by linarith) _
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (sq_nonneg _) (by nlinarith) _
    · positivity
    · positivity
  have hs := (Real.summable_pow_div_factorial 1).mul_left (t ^ m)
  have hexp : (∑' n : ℕ, (1 : ℝ) ^ n / n.factorial) = Real.exp 1 := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)).tsum_eq
  calc
    |J m t| ≤ ∑' n, ‖seriesTerm m t n‖ := norm_tsum_le_tsum_norm (seriesTerm_norm_summable m t)
    _ ≤ ∑' n, t ^ m * (1 ^ n / (n.factorial : ℝ)) :=
      Summable.tsum_le_tsum hterm (seriesTerm_norm_summable m t) hs
    _ = Real.exp 1 * t ^ m := by rw [tsum_mul_left, hexp]; ring

/-- The genuinely external Bessel identities cited by the paper. The first
asymptotic term is the leading-order specialization of DLMF 10.17.3; all
estimates for the paper's arithmetic kernel remain internal obligations. -/
structure DLMFIdentities : Prop where
  continuous : ∀ m, Continuous (J m)
  integral : ∀ m t, J m t = (1 / Real.pi) *
    ∫ θ : ℝ in (0)..Real.pi, Real.cos (t * Real.sin θ - (m : ℝ) * θ)
  cosine_integral : ∀ (m : ℕ) (t : ℝ),
    (∫ θ : ℝ in (0)..Real.pi,
      Complex.exp (Complex.I * (t * Real.cos θ : ℝ)) * (Real.cos ((m : ℝ) * θ) : ℂ)) =
      (Real.pi : ℂ) * Complex.I ^ m * (J m t : ℂ)
  recurrence : ∀ m t, t ≠ 0 →
    J m t + J (m + 2) t = (2 * (m + 1 : ℝ) / t) * J (m + 1) t
  asymptotic : ∀ m,
    (fun t => J m t - Real.sqrt (2 / (Real.pi * t)) *
      Real.cos (t - ((2 * m + 1 : ℝ) * Real.pi / 4)))
      =O[atTop] (fun t : ℝ => t ^ (-(3 / 2 : ℝ)))
  odd_integral : ∀ n T, 0 ≤ T →
    (∫ t : ℝ in (0)..T, J (2 * n + 1) t) =
      1 - J 0 T - 2 * ∑ j ∈ Finset.Icc 1 n, J (2 * j) T

end DepthAspect.BesselFirstKind
