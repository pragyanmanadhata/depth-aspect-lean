import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The harmonic-sum remainder in equation (124)

The Euler constant is mathlib's actual limit. The estimate is proved from
the increasing and decreasing sequences bounding that limit, including
real, nonintegral endpoints.
-/
open scoped BigOperators
namespace DepthAspect.HarmonicRemainder

/-- Adjacent logarithms differ by at most the reciprocal of the lower endpoint. -/
theorem log_gap_le {x : ℝ} (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  rw [← Real.log_div (by positivity) (ne_of_gt hx)]
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  calc
    _ ≤ (x + 1) / x - 1 := h
    _ = _ := by field_simp; ring

/-- Equation (124) with the explicit absolute constant 2. -/
theorem harmonic_floor_remainder {T : ℝ} (hT : 1 ≤ T) :
    |(harmonic ⌊T⌋₊ : ℝ) - Real.log T - Real.eulerMascheroniConstant| ≤ 2 / T := by
  let n : ℕ := ⌊T⌋₊
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa only [Nat.cast_one] using hT)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn1)
  have hnT : (n : ℝ) ≤ T := Nat.floor_le hT0.le
  have hTn : T < (n : ℝ) + 1 := Nat.lt_floor_add_one T
  have hloglo : Real.log (n : ℝ) ≤ Real.log T := Real.log_le_log hnR hnT
  have hloghi : Real.log T ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hT0 hTn.le
  have hγlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have hγhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq', ne_of_gt (show 0 < n from hn1),
    if_false, Nat.cast_add, Nat.cast_one] at hγlo hγhi
  have hgap := log_gap_le hnR
  have habs : |(harmonic n : ℝ) - Real.log T - Real.eulerMascheroniConstant| ≤
      1 / (n : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith
  apply habs.trans
  apply (div_le_div_iff₀ hnR hT0).mpr
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  nlinarith

/-- The real-endpoint harmonic sum is expressed as a literal finite sum. -/
theorem harmonic_floor_as_sum (T : ℝ) :
    (harmonic ⌊T⌋₊ : ℝ) = ∑ i ∈ Finset.range ⌊T⌋₊, 1 / ((i : ℝ) + 1) := by
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add,
    Nat.cast_one, one_div]

/-- The summation form used after the divisor reindexing in Lemma 6.3. -/
theorem sum_reciprocal_floor_remainder {T : ℝ} (hT : 1 ≤ T) :
    |(∑ i ∈ Finset.range ⌊T⌋₊, 1 / ((i : ℝ) + 1)) - Real.log T -
      Real.eulerMascheroniConstant| ≤ 2 / T := by
  rw [← harmonic_floor_as_sum]
  exact harmonic_floor_remainder hT

end DepthAspect.HarmonicRemainder
