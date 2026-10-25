import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Restoring the omitted primes in exponential smoothing

This proves (99) from the literal prime-factor sum. The logarithmic series is
bounded by an actual logarithm power series and a geometric series, so no
smoothed-sum estimate is supplied as a premise.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.OmittedPrimeCost

/-- The primes omitted at coefficient m are exactly the prime divisors of 2m. -/
def primeCost (m : ℕ) : ℝ := ∑ p ∈ (2 * m).primeFactors, Real.log p

theorem primeCost_nonneg (m : ℕ) : 0 ≤ primeCost m := by
  apply Finset.sum_nonneg
  intro p hp
  exact Real.log_nonneg (by exact_mod_cast
    (Nat.prime_of_mem_primeFactors hp).one_lt.le)

theorem primeCost_le_log {m : ℕ} (hm : 0 < m) : primeCost m ≤ Real.log (2 * m) := by
  have hprod : 0 < ∏ p ∈ (2 * m).primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hle : ∏ p ∈ (2 * m).primeFactors, p ≤ 2 * m :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd _)
  rw [primeCost, ← Real.log_prod (fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero), ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hprod) (by exact_mod_cast hle)

def ratio (x : ℝ) : ℝ := Real.exp (-1 / x)

theorem ratio_pos (x : ℝ) : 0 < ratio x := Real.exp_pos _

theorem ratio_lt_one {x : ℝ} (hx : 0 < x) : ratio x < 1 := by
  rw [ratio, Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos (by norm_num) hx

/-- Both auxiliary series bounds follow from the elementary inequality exp y≥1+y. -/
theorem ratio_bound {x : ℝ} (hx : 0 < x) : ratio x ≤ x * (1 - ratio x) := by
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 / x))
    (ratio_pos x).le
  have hexp : ratio x * Real.exp (1 / x) = 1 := by
    rw [ratio, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [hexp] at he
  have hmul := mul_le_mul_of_nonneg_left he hx.le
  have hcancel : x * (ratio x * (1 / x + 1)) = ratio x + x * ratio x := by
    field_simp [hx.ne']
  rw [hcancel] at hmul
  nlinarith

theorem geometric_bound {x : ℝ} (hx : 0 < x) : ratio x / (1 - ratio x) ≤ x := by
  exact (div_le_iff₀ (sub_pos.mpr (ratio_lt_one hx))).mpr (by
    simpa only [mul_comm] using ratio_bound hx)

theorem logarithmic_bound {x : ℝ} (hx : 1 ≤ x) :
    -Real.log (1 - ratio x) ≤ Real.log (2 * x) := by
  have hx0 : 0 < x := by linarith
  have hr := ratio_bound hx0
  have hpos : 0 < 1 - ratio x := sub_pos.mpr (ratio_lt_one hx0)
  have hlower : (x + 1)⁻¹ ≤ 1 - ratio x := by
    apply (inv_le_iff_one_le_mul₀' (by linarith : 0 < x + 1)).mpr
    nlinarith
  have hlog := Real.log_le_log (inv_pos.mpr (by linarith : 0 < x + 1)) hlower
  rw [Real.log_inv] at hlog
  exact (by linarith : -Real.log (1 - ratio x) ≤ Real.log (x + 1)).trans
    (Real.log_le_log (by linarith) (by linarith))

theorem log_weight_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.log (2 * ((n : ℝ) + 1)) ≤ Real.log (2 * x) + ((n : ℝ) + 1) / x := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn hx)
  have hid : Real.log (2 * ((n : ℝ) + 1)) =
      Real.log (2 * x) + Real.log (((n : ℝ) + 1) / x) := by
    rw [← Real.log_mul (by positivity : 2 * x ≠ 0) (ne_of_gt (div_pos hn hx))]
    congr 1
    field_simp
  rw [hid]
  linarith

def logarithmicTerm (x : ℝ) (n : ℕ) : ℝ :=
  ratio x ^ (n + 1) / ((n : ℝ) + 1) * Real.log (2 * ((n : ℝ) + 1))

def majorant (x : ℝ) (n : ℕ) : ℝ :=
  Real.log (2 * x) * (ratio x ^ (n + 1) / ((n : ℝ) + 1)) +
    x⁻¹ * ratio x ^ (n + 1)

theorem logarithmicTerm_nonneg {x : ℝ} (n : ℕ) : 0 ≤ logarithmicTerm x n := by
  unfold logarithmicTerm
  exact mul_nonneg (by have := ratio_pos x; positivity) (Real.log_nonneg (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; nlinarith))

theorem logarithmicTerm_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    logarithmicTerm x n ≤ majorant x n := by
  have h := mul_le_mul_of_nonneg_left (log_weight_le hx n)
    (by have := ratio_pos x; positivity : 0 ≤ ratio x ^ (n + 1) / ((n : ℝ) + 1))
  calc
    logarithmicTerm x n ≤ ratio x ^ (n + 1) / ((n : ℝ) + 1) *
        (Real.log (2 * x) + ((n : ℝ) + 1) / x) := h
    _ = majorant x n := by
      unfold majorant
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hx.ne', hn] <;> ring

theorem majorant_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (majorant x)
      (Real.log (2 * x) * (-Real.log (1 - ratio x)) +
        x⁻¹ * (ratio x / (1 - ratio x))) := by
  have hr : |ratio x| < 1 := by rw [abs_of_pos (ratio_pos x)]; exact ratio_lt_one hx
  have hh := (Real.hasSum_pow_div_log_of_abs_lt_one hr).mul_left (Real.log (2 * x))
  have hg := (hasSum_geometric_of_abs_lt_one hr).mul_left (ratio x)
  have hg' : HasSum (fun n : ℕ => ratio x ^ (n + 1)) (ratio x / (1 - ratio x)) := by
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using hg
  exact hh.add (hg'.mul_left x⁻¹)

/-- The analytic series estimate behind the omitted-prime cost. -/
theorem logarithmicSeries_bound {x : ℝ} (hx : 1 ≤ x) :
    Summable (logarithmicTerm x) ∧
      (∑' n, logarithmicTerm x n) ≤ Real.log (2 * x) ^ 2 + 1 := by
  have hx0 : 0 < x := by linarith
  have hm := majorant_hasSum hx0
  have hs : Summable (logarithmicTerm x) :=
    Summable.of_nonneg_of_le (logarithmicTerm_nonneg) (logarithmicTerm_le hx0) hm.summable
  refine ⟨hs, (hs.tsum_le_tsum (logarithmicTerm_le hx0) hm.summable).trans ?_⟩
  rw [hm.tsum_eq]
  have hlog : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have h1 := mul_le_mul_of_nonneg_left (logarithmic_bound hx) hlog
  have h2 := mul_le_mul_of_nonneg_left (geometric_bound hx0) (inv_nonneg.mpr hx0.le)
  have hxx : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
  rw [hxx] at h2
  nlinarith

/-- Literal exponential smoothing agrees with the geometric parameter above. -/
theorem exp_term_eq (x : ℝ) (n : ℕ) :
    Real.exp (-((n : ℝ) + 1) / x) = ratio x ^ (n + 1) := by
  rw [ratio, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Equation (99), before absorbing the harmless constant into log²(2x). -/
theorem omitted_prime_cost {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun n : ℕ => Real.exp (-((n : ℝ) + 1) / x) /
      ((n : ℝ) + 1) * primeCost (n + 1)) ∧
    (∑' n : ℕ, Real.exp (-((n : ℝ) + 1) / x) /
      ((n : ℝ) + 1) * primeCost (n + 1)) ≤ Real.log (2 * x) ^ 2 + 1 := by
  have hmajor (n : ℕ) : Real.exp (-((n : ℝ) + 1) / x) /
      ((n : ℝ) + 1) * primeCost (n + 1) ≤ logarithmicTerm x n := by
    rw [exp_term_eq, logarithmicTerm]
    apply mul_le_mul_of_nonneg_left
    · simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using primeCost_le_log (Nat.succ_pos n)
    · have := ratio_pos x
      positivity
  have hs : Summable (fun n : ℕ => Real.exp (-((n : ℝ) + 1) / x) /
      ((n : ℝ) + 1) * primeCost (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (primeCost_nonneg _))
      hmajor (logarithmicSeries_bound hx).1
  exact ⟨hs, (hs.tsum_le_tsum hmajor (logarithmicSeries_bound hx).1).trans
    (logarithmicSeries_bound hx).2⟩

/-- One explicit absolute constant suffices for the printed log-squared form. -/
def absoluteConstant : ℝ := 1 + 1 / Real.log 2 ^ 2

theorem log_squared_absorption {x : ℝ} (hx : 1 ≤ x) :
    Real.log (2 * x) ^ 2 + 1 ≤ absoluteConstant * Real.log (2 * x) ^ 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 * x) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hs : Real.log 2 ^ 2 ≤ Real.log (2 * x) ^ 2 := by nlinarith
  have hratio : 1 ≤ Real.log (2 * x) ^ 2 / Real.log 2 ^ 2 :=
    (one_le_div (sq_pos_of_pos h2)).mpr hs
  calc
    _ ≤ Real.log (2 * x) ^ 2 + Real.log (2 * x) ^ 2 / Real.log 2 ^ 2 :=
      add_le_add (le_refl _) hratio
    _ = _ := by unfold absoluteConstant; ring

/-- Equation (99) with a literal finite prime-divisor sum and an absolute
constant, uniformly for every smoothing length x≥1 and bound M≥0. -/
theorem omitted_prime_cost_bound {x M : ℝ} (hx : 1 ≤ x) (hM : 0 ≤ M) :
    (∑' n : ℕ, M * (Real.exp (-((n : ℝ) + 1) / x) /
      ((n : ℝ) + 1) * primeCost (n + 1))) ≤
        absoluteConstant * M * Real.log (2 * x) ^ 2 := by
  rw [tsum_mul_left]
  have h := mul_le_mul_of_nonneg_left
    ((omitted_prime_cost hx).2.trans (log_squared_absorption hx)) hM
  simpa only [mul_left_comm, mul_assoc] using h

end DepthAspect.OmittedPrimeCost
