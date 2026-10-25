import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact dyadic cusp totient sums

This proves equation (30) for actual Euler totients, and bounds any restricted
nonnegative cusp sum dominated by it. Identification of the specific trace
formula cusp term with such a restricted sum remains separate.
-/
open scoped BigOperators
namespace DepthAspect.CuspBounds

/-- The unrestricted sum in (30). -/
def cuspSum (h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (h + 1), Nat.totient (2 ^ min j (h - j))

/-- The sum of dyadic totients through exponent a is exactly `2^a`. -/
theorem sum_dyadic_totients (a : ℕ) :
    ∑ j ∈ Finset.range (a + 1), Nat.totient (2 ^ j) = 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow_succ Nat.prime_two]
    simp [pow_succ]
    omega

/-- Symmetry splits an odd-length exponent interval into equal halves. -/
theorem symmetric_sum_odd (f : ℕ → ℕ) (a : ℕ) :
    (∑ j ∈ Finset.range (2 * a + 1 + 1), f (min j (2 * a + 1 - j))) =
      2 * ∑ j ∈ Finset.range (a + 1), f j := by
  rw [show 2 * a + 1 + 1 = (a + 1) + (a + 1) by omega, Finset.sum_range_add]
  have hleft : (∑ j ∈ Finset.range (a + 1), f (min j (2 * a + 1 - j))) =
      ∑ j ∈ Finset.range (a + 1), f j := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply min_eq_left
    have hj' := Finset.mem_range.mp hj
    omega
  have hright : (∑ j ∈ Finset.range (a + 1),
      f (min (a + 1 + j) (2 * a + 1 - (a + 1 + j)))) =
      ∑ j ∈ Finset.range (a + 1), f j := by
    rw [← Finset.sum_range_reflect f (a + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have hj' := Finset.mem_range.mp hj
    omega
  rw [hleft, hright]
  omega

/-- At even depth the two halves differ by their central term. -/
theorem symmetric_sum_even (f : ℕ → ℕ) (a : ℕ) :
    (∑ j ∈ Finset.range (2 * a + 1), f (min j (2 * a - j))) =
      (∑ j ∈ Finset.range a, f j) + ∑ j ∈ Finset.range (a + 1), f j := by
  rw [show 2 * a + 1 = a + (a + 1) by omega, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply min_eq_left
    have hj' := Finset.mem_range.mp hj
    omega
  · rw [← Finset.sum_range_reflect f (a + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    have hj' := Finset.mem_range.mp hj
    omega

/-- Exact odd-depth formula in (30). -/
theorem cuspSum_odd (a : ℕ) : cuspSum (2 * a + 1) = 2 ^ (a + 1) := by
  unfold cuspSum
  rw [symmetric_sum_odd (fun j => Nat.totient (2 ^ j)) a,
    sum_dyadic_totients, pow_succ]
  omega

/-- Exact even-depth formula in (30), excluding depth zero. -/
theorem cuspSum_even (a : ℕ) (ha : 1 ≤ a) :
    cuspSum (2 * a) = 3 * 2 ^ (a - 1) := by
  unfold cuspSum
  rw [symmetric_sum_even (fun j => Nat.totient (2 ^ j)) a, sum_dyadic_totients]
  have hsum : (∑ j ∈ Finset.range a, Nat.totient (2 ^ j)) = 2 ^ (a - 1) := by
    have h := sum_dyadic_totients (a - 1)
    rwa [show a - 1 + 1 = a by omega] at h
  have hp := pow_succ (2 : ℕ) (a - 1)
  rw [show a - 1 + 1 = a by omega] at hp
  rw [hsum, hp]
  omega

@[simp] theorem cuspSum_zero : cuspSum 0 = 1 := by norm_num [cuspSum]

/-- A stronger integer floor-exponent bound, also valid at depth zero. -/
theorem cuspSum_bound (h : ℕ) : cuspSum h ≤ 2 * 2 ^ (h / 2) := by
  rcases Nat.even_or_odd h with he | ho
  · obtain ⟨a, ha⟩ := he
    have hh : h = 2 * a := by omega
    rw [hh]
    by_cases haz : a = 0
    · simp [haz]
    · rw [cuspSum_even a (by omega)]
      have hp := pow_succ (2 : ℕ) (a - 1)
      rw [show a - 1 + 1 = a by omega] at hp
      rw [show 2 * a / 2 = a by omega, hp]
      omega
  · obtain ⟨a, ha⟩ := ho
    have hh : h = 2 * a + 1 := by omega
    rw [hh, cuspSum_odd, show (2 * a + 1) / 2 = a by omega, pow_succ]
    omega

/-- The square root dominates the power with the floored half exponent. -/
theorem floor_power_le_sqrt (h : ℕ) :
    (2 : ℝ) ^ (h / 2) ≤ Real.sqrt ((2 : ℝ) ^ h) := by
  apply Real.le_sqrt_of_sq_le
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by norm_num)
  exact Nat.div_mul_le_self h 2

/-- The uniform real-valued cusp bound in (30). -/
theorem cuspSum_bound_real (h : ℕ) :
    (cuspSum h : ℝ) ≤ 2 * Real.sqrt ((2 : ℝ) ^ h) := by
  have hb : (cuspSum h : ℝ) ≤ 2 * (2 : ℝ) ^ (h / 2) := by
    exact_mod_cast cuspSum_bound h
  exact hb.trans (mul_le_mul_of_nonneg_left (floor_power_le_sqrt h) (by norm_num))

/-- Restricting the actual totient sum by any congruence predicate. -/
def restrictedCuspSum (h : ℕ) (P : ℕ → Prop) [DecidablePred P] : ℕ :=
  ∑ j ∈ (Finset.range (h + 1)).filter P, Nat.totient (2 ^ min j (h - j))

theorem restrictedCuspSum_le (h : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    restrictedCuspSum h P ≤ cuspSum h := by
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Any nonnegative cusp count below the totient sum obeys a uniform
second-difference bound; positivity gives the sharper constant 4. -/
theorem cusp_second_difference_bound (Φ : ℕ → ℝ)
    (hΦ : ∀ h, 0 ≤ Φ h ∧ Φ h ≤ cuspSum h) (n : ℕ) :
    |Φ n - 2 * Φ (n - 1) + Φ (n - 2)| ≤ 4 * Real.sqrt ((2 : ℝ) ^ n) := by
  have h0 := (hΦ n).2.trans (cuspSum_bound_real n)
  have h1 := (hΦ (n - 1)).2.trans (cuspSum_bound_real (n - 1))
  have h2 := (hΦ (n - 2)).2.trans (cuspSum_bound_real (n - 2))
  have hp1 : Real.sqrt ((2 : ℝ) ^ (n - 1)) ≤ Real.sqrt ((2 : ℝ) ^ n) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (by omega))
  have hp2 : Real.sqrt ((2 : ℝ) ^ (n - 2)) ≤ Real.sqrt ((2 : ℝ) ^ n) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (by omega))
  have hn0 := (hΦ n).1
  have hn1 := (hΦ (n - 1)).1
  have hn2 := (hΦ (n - 2)).1
  rw [abs_le]
  constructor <;> linarith

/-- The stated constant 6 in the paragraph following (30). -/
theorem cusp_second_difference_bound_six (Φ : ℕ → ℝ)
    (hΦ : ∀ h, 0 ≤ Φ h ∧ Φ h ≤ cuspSum h) (n : ℕ) :
    |Φ n - 2 * Φ (n - 1) + Φ (n - 2)| ≤ 6 * Real.sqrt ((2 : ℝ) ^ n) := by
  have h := cusp_second_difference_bound Φ hΦ n
  nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ n)]

end DepthAspect.CuspBounds
