import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ordered Dirichlet series at one

The value at one is a limit of natural partial sums. It is deliberately not
the unordered `tsum`, which is unsuitable for conditionally convergent complex
Dirichlet series. The complete-period condition removes the lower endpoint
in finite Abel summation and gives the constant 2 in the logarithmic bound.
-/

open Filter
open scoped BigOperators Topology
namespace DepthAspect.OrderedDirichlet

def partialSum (a : ℕ → ℂ) (n : ℕ) : ℂ := ∑ i ∈ Finset.range n, a (i + 1)

noncomputable def partialL (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range n, a (i + 1) / ((i : ℂ) + 1)

@[simp] theorem partialSum_succ (a : ℕ → ℂ) (n : ℕ) :
    partialSum a (n + 1) = partialSum a n + a (n + 1) := by
  simp [partialSum, Finset.sum_range_succ]

@[simp] theorem partialL_succ (a : ℕ → ℂ) (n : ℕ) :
    partialL a (n + 1) = partialL a n + a (n + 1) / ((n : ℂ) + 1) := by
  simp [partialL, Finset.sum_range_succ]

/-- Bounded partial sums give convergence in the correct, ordered sense. -/
theorem ordered_limit_exists (a : ℕ → ℂ) {B : ℝ}
    (hB : ∀ n, ‖partialSum a n‖ ≤ B) :
    ∃ L : ℂ, Tendsto (partialL a) atTop (𝓝 L) := by
  have ha : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hc := ha.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    tendsto_one_div_add_atTop_nhds_zero_nat hB
  have he : (fun n => ∑ i ∈ Finset.range n,
      (1 / ((i : ℝ) + 1)) • a (i + 1)) = partialL a := by
    funext n
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  rw [he] at hc
  exact cauchySeq_tendsto_of_complete hc

/-- The finite summation-by-parts identity with arbitrary natural endpoints. -/
theorem partialL_sub_eq (a : ℕ → ℂ) {q n : ℕ} (hqn : q ≤ n) :
    partialL a n - partialL a q =
      partialSum a n / (n : ℂ) - partialSum a q / (q : ℂ) +
        ∑ i ∈ Finset.Ico q n,
          partialSum a i * ((i : ℂ)⁻¹ - ((i : ℂ) + 1)⁻¹) := by
  induction n, hqn using Nat.le_induction with
  | base => simp
  | succ n hqn ih =>
    rw [partialL_succ, partialSum_succ, Finset.sum_Ico_succ_top hqn]
    push_cast
    linear_combination ih

private theorem inverse_difference_nonneg {q i : ℕ} (hq : 0 < q) (hqi : q ≤ i) :
    0 ≤ (i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹ := by
  have hi : (0 : ℝ) < i := by exact_mod_cast hq.trans_le hqi
  exact sub_nonneg.mpr (inv_anti₀ hi (by linarith))

private theorem sum_inverse_difference {q n : ℕ} (hqn : q ≤ n) :
    (∑ i ∈ Finset.Ico q n, ((i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹)) =
      (q : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  induction n, hqn using Nat.le_induction with
  | base => simp
  | succ n hqn ih =>
    rw [Finset.sum_Ico_succ_top hqn, ih]
    push_cast
    ring

/-- A complete zero-sum period makes the weighted tail have norm at most one. -/
theorem norm_tail_le_one (a : ℕ → ℂ) {q n : ℕ} (hq : 0 < q) (hqn : q ≤ n)
    (hzero : partialSum a q = 0) (hB : ∀ j, ‖partialSum a j‖ ≤ q) :
    ‖partialL a n - partialL a q‖ ≤ 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hq.trans_le hqn
  rw [partialL_sub_eq a hqn, hzero, zero_div, sub_zero]
  calc
    _ ≤ ‖partialSum a n / (n : ℂ)‖ +
        ∑ i ∈ Finset.Ico q n,
          ‖partialSum a i * ((i : ℂ)⁻¹ - ((i : ℂ) + 1)⁻¹)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ (q : ℝ) / n + ∑ i ∈ Finset.Ico q n,
        (q : ℝ) * ((i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹) := by
      apply add_le_add
      · rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_right (hB n) hnR.le
      · apply Finset.sum_le_sum
        intro i hi
        have hd := inverse_difference_nonneg hq (Finset.mem_Ico.mp hi).1
        have he : ((i : ℂ)⁻¹ - ((i : ℂ) + 1)⁻¹) =
            (((i : ℝ)⁻¹ - ((i : ℝ) + 1)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_right (hB i) hd
    _ = 1 := by
      rw [← Finset.mul_sum, sum_inverse_difference hqn]
      field_simp [ne_of_gt hqR, ne_of_gt hnR]
      <;> ring

/-- The initial block is bounded by the actual harmonic number. -/
theorem norm_partialL_le_harmonic (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (q : ℕ) :
    ‖partialL a q‖ ≤ (harmonic q : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range q, ‖a (i + 1) / ((i : ℂ) + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range q, ((i : ℝ) + 1)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have he : ‖(i : ℂ) + 1‖ = (i : ℝ) + 1 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hi]
      rw [norm_div, he, ← one_div]
      exact div_le_div_of_nonneg_right (ha (i + 1)) hi.le
    _ = (harmonic q : ℝ) := by
      simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
        Nat.cast_one]

/-- Equation (8)'s logarithmic estimate for any bounded, zero-mean periodic
coefficient sequence, including the imprimitive sequence after period reduction. -/
theorem norm_ordered_limit_le (a : ℕ → ℂ) {q : ℕ} (hq : 0 < q)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hzero : partialSum a q = 0)
    (hB : ∀ n, ‖partialSum a n‖ ≤ q) {L : ℂ}
    (hL : Tendsto (partialL a) atTop (𝓝 L)) :
    ‖L‖ ≤ 2 + Real.log q := by
  apply le_of_tendsto hL.norm
  filter_upwards [eventually_ge_atTop q] with n hn
  calc
    ‖partialL a n‖ ≤ ‖partialL a q‖ + ‖partialL a n - partialL a q‖ := by
      calc
        _ = ‖partialL a q + (partialL a n - partialL a q)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ (harmonic q : ℝ) + 1 := add_le_add
      (norm_partialL_le_harmonic a ha q) (norm_tail_le_one a hq hn hzero hB)
    _ ≤ _ := by linarith [harmonic_le_one_add_log q]

/-- A logarithmic bound gives the required arbitrarily small power loss.
The constant is slightly larger than the draft's but remains uniform. -/
theorem norm_ordered_limit_rpow {D δ : ℝ} (hD : 1 ≤ D) (hδ : 0 < δ) {L : ℂ}
    (hL : ‖L‖ ≤ 2 + Real.log D) : ‖L‖ ≤ (2 + δ⁻¹) * D ^ δ := by
  have hpow : 1 ≤ D ^ δ := Real.one_le_rpow hD hδ.le
  have hlog := Real.log_le_rpow_div (zero_le_one.trans hD) hδ
  calc
    ‖L‖ ≤ 2 + Real.log D := hL
    _ ≤ 2 * D ^ δ + D ^ δ / δ := by linarith
    _ = _ := by ring

/-- The cited class-number identity transfers the proved L-value estimate to
the class-number growth bound. The identity itself contains no size estimate. -/
theorem class_number_bound_of_formula {D δ H : ℝ} (hD : 1 ≤ D) (hδ : 0 < δ)
    {L : ℂ} (hL : ‖L‖ ≤ 2 + Real.log D)
    (hH : H = Real.sqrt D / Real.pi * L.re) :
    H ≤ ((2 + δ⁻¹) / Real.pi) * D ^ (1 / 2 + δ) := by
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  calc
    H = Real.sqrt D / Real.pi * L.re := hH
    _ ≤ Real.sqrt D / Real.pi * ((2 + δ⁻¹) * D ^ δ) :=
      mul_le_mul_of_nonneg_left
        ((Complex.re_le_norm L).trans (norm_ordered_limit_rpow hD hδ hL)) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hD0, ← Real.sqrt_eq_rpow]
      ring

theorem class_number_constant_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < (2 + δ⁻¹) / Real.pi := by positivity

end DepthAspect.OrderedDirichlet
