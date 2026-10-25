import DepthAspect.DigammaBound
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The numerical smoothing tail in (88)

The literal series is bounded by a cutoff at ceil(sqrt(T)) and an explicit
telescoping majorant for its inverse-square tail. No integral-comparison or
smoothing estimate is an input.
-/
open scoped BigOperators
namespace DepthAspect.SmoothingKernel

noncomputable def term (T : ℝ) (n : ℕ) : ℝ :=
  DigammaBound.inverseSquare n * min 1 (((n : ℝ) + 1) ^ 2 / T)

 theorem term_nonneg {T : ℝ} (hT : 0 < T) (n : ℕ) : 0 ≤ term T n := by
  unfold term DigammaBound.inverseSquare
  positivity

 theorem term_le_inverseSquare {T : ℝ} (hT : 0 < T) (n : ℕ) :
    term T n ≤ DigammaBound.inverseSquare n := by
  unfold term
  simpa using mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) (((n : ℝ) + 1) ^ 2 / T))
    (by unfold DigammaBound.inverseSquare; positivity)

 theorem term_le_reciprocal {T : ℝ} (hT : 0 < T) (n : ℕ) : term T n ≤ 1 / T := by
  calc
    _ ≤ DigammaBound.inverseSquare n * (((n : ℝ) + 1) ^ 2 / T) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _)
        (by unfold DigammaBound.inverseSquare; positivity)
    _ = _ := by
      unfold DigammaBound.inverseSquare
      field_simp

 theorem term_summable {T : ℝ} (hT : 0 < T) : Summable (term T) :=
  Summable.of_nonneg_of_le (term_nonneg hT) (term_le_inverseSquare hT)
    DigammaBound.inverseSquare_summable

 theorem inverseSquare_tail_partial {N : ℕ} (hN : 0 < N) (K : ℕ) :
    (∑ n ∈ Finset.range K, DigammaBound.inverseSquare (n + N)) ≤
      1 / (N : ℝ) - 1 / ((N : ℝ) + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h := DigammaBound.inverse_square_le_telescoping
      (x := (N : ℝ) + K) (by exact_mod_cast Nat.add_pos_left hN K)
    simp only [DigammaBound.inverseSquare, Nat.cast_add, Nat.cast_one] at *
    have hsum := add_le_add ih h
    simp only [add_comm (K : ℝ) (N : ℝ), add_assoc] at hsum ⊢
    linarith

 theorem inverseSquare_tail {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, DigammaBound.inverseSquare (n + N)) ≤ 1 / (N : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    unfold DigammaBound.inverseSquare
    positivity
  · intro K
    have h := inverseSquare_tail_partial hN K
    have hpos : 0 ≤ 1 / ((N : ℝ) + K) := by positivity
    linarith

 theorem term_cutoff_bound {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, term T n) ≤ (N : ℝ) / T + 1 / (N : ℝ) := by
  rw [← (term_summable hT).sum_add_tsum_nat_add N]
  apply add_le_add
  · calc
      _ ≤ ∑ n ∈ Finset.range N, 1 / T :=
        Finset.sum_le_sum fun n _ => term_le_reciprocal hT n
      _ = _ := by simp [div_eq_mul_inv]
  · apply le_trans _ (inverseSquare_tail hN)
    exact Summable.tsum_le_tsum (fun n => term_le_inverseSquare hT (n + N))
      ((term_summable hT).comp_injective (by intro a b h; exact Nat.add_right_cancel h))
      (DigammaBound.inverseSquare_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h))

/-- Equation (88), for its literal positive-integer series. -/
theorem tsum_term_le {T : ℝ} (hT : 0 < T) :
    (∑' n : ℕ, term T n) ≤ 4 / Real.sqrt T := by
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hs2 : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hT.le
  by_cases hT1 : 1 ≤ T
  · let N : ℕ := ⌈Real.sqrt T⌉₊
    have hs1 : 1 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by simpa using hT1)
    have hNs : Real.sqrt T ≤ (N : ℝ) := Nat.le_ceil _
    have hNhi : (N : ℝ) < Real.sqrt T + 1 := Nat.ceil_lt_add_one hs0.le
    have hN : 0 < N := by exact_mod_cast (lt_of_lt_of_le hs0 hNs)
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hhead : (N : ℝ) / T ≤ 2 / Real.sqrt T := by
      apply (div_le_div_iff₀ hT hs0).mpr
      have hmul := mul_le_mul_of_nonneg_right hNhi.le hs0.le
      nlinarith
    have htail : 1 / (N : ℝ) ≤ 1 / Real.sqrt T :=
      one_div_le_one_div_of_le hs0 hNs
    apply (term_cutoff_bound hT hN).trans
    calc
      _ ≤ 2 / Real.sqrt T + 1 / Real.sqrt T := add_le_add hhead htail
      _ = 3 / Real.sqrt T := by ring
      _ ≤ 4 / Real.sqrt T := div_le_div_of_nonneg_right (by norm_num) hs0.le
  · have hs1 : Real.sqrt T ≤ 1 := (Real.sqrt_le_one).mpr (le_of_not_ge hT1)
    have htwo : (∑' n : ℕ, term T n) ≤ 2 := by
      apply le_trans _ DigammaBound.inverseSquare_tsum_le_two
      exact Summable.tsum_le_tsum (term_le_inverseSquare hT) (term_summable hT)
        DigammaBound.inverseSquare_summable
    apply htwo.trans
    apply (le_div_iff₀ hs0).mpr
    nlinarith

/-- The elementary exponential cutoff inequality used immediately after (88). -/
theorem one_sub_exp_neg_le_min {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ 1 - Real.exp (-y) ∧ 1 - Real.exp (-y) ≤ min 1 y := by
  constructor
  · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)
    linarith
  · apply le_min
    · linarith [Real.exp_pos (-y)]
    · linarith [Real.one_sub_le_exp_neg y]

end DepthAspect.SmoothingKernel
