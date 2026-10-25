import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Chebyshev partial summation for the prime weights in Section 4

Chebyshev's estimate is supplied by mathlib with the proved constant `log 4`.
The Abel-summation identity, derivative estimates, integrability, and power
integrals are all proved here for the actual finite prime sums.
-/
namespace DepthAspect.ChebyshevWeights

open Finset MeasureTheory
open scoped BigOperators

/-- The logarithmic coefficient at primes, zero elsewhere. -/
noncomputable def primeLog (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

@[simp] theorem primeLog_zero : primeLog 0 = 0 := by simp [primeLog]
@[simp] theorem primeLog_one : primeLog 1 = 0 := by simp [primeLog]

theorem primeLog_nonneg (n : ℕ) : 0 ≤ primeLog n := by
  unfold primeLog
  split_ifs with hn
  · exact Real.log_nonneg (by exact_mod_cast hn.one_le)
  · rfl

/-- The actual weighted finite prime sum. -/
noncomputable def primePowerSum (Z a : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊Z⌋₊, (p : ℝ) ^ a * Real.log p

theorem sum_primeLog (Z : ℝ) :
    (∑ n ∈ Icc 0 ⌊Z⌋₊, primeLog n) = Chebyshev.theta Z := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp only [primeLog, Finset.sum_filter]

theorem primePowerSum_eq_sum (Z a : ℝ) :
    primePowerSum Z a = ∑ n ∈ Icc 0 ⌊Z⌋₊, (n : ℝ) ^ a * primeLog n := by
  unfold primePowerSum
  rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [primeLog, hp]

theorem primePowerSum_nonneg (Z a : ℝ) : 0 ≤ primePowerSum Z a := by
  rw [primePowerSum_eq_sum]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (Real.rpow_nonneg (by positivity) a) (primeLog_nonneg n)

theorem primePowerSum_mono_exponent (Z : ℝ) {a b : ℝ} (hab : a ≤ b) :
    primePowerSum Z a ≤ primePowerSum Z b := by
  unfold primePowerSum
  apply Finset.sum_le_sum
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpprime.one_le) hab)
    (Real.log_nonneg (by exact_mod_cast hpprime.one_le))

/-- Any chosen prime subset has no greater nonnegative power-weighted sum.
In particular, deleting the prime two gives the odd-prime sums in the paper. -/
theorem primePowerSum_subset (Z a : ℝ) (M : Finset ℕ)
    (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) :
    (∑ p ∈ M, (p : ℝ) ^ a * Real.log p) ≤ primePowerSum Z a := by
  unfold primePowerSum
  apply Finset.sum_le_sum_of_subset_of_nonneg hM
  intro p hp hnot
  exact mul_nonneg (Real.rpow_nonneg (by positivity) a) (Real.log_natCast_nonneg p)

/-- The first estimate in (50), proved directly from Chebyshev's theorem. -/
theorem primePowerSum_nonnegative_exponent {Z a : ℝ} (hZ : 1 ≤ Z) (ha : 0 ≤ a) :
    primePowerSum Z a ≤ Real.log 4 * Z ^ (1 + a) := by
  have hZ0 : 0 < Z := by linarith
  have hs : primePowerSum Z a ≤ Z ^ a * Chebyshev.theta Z := by
    rw [Chebyshev.theta_eq_sum_primesLE, Finset.mul_sum]
    unfold primePowerSum
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpZ, hpprime⟩ := Nat.mem_primesLE.mp hp
    have hpZ' : (p : ℝ) ≤ Z :=
      (by exact_mod_cast hpZ : (p : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hpZ' ha)
      (Real.log_nonneg (by exact_mod_cast hpprime.one_le))
  calc
    _ ≤ Z ^ a * Chebyshev.theta Z := hs
    _ ≤ Z ^ a * (Real.log 4 * Z) := mul_le_mul_of_nonneg_left
      (Chebyshev.theta_le_log4_mul_x hZ0.le) (Real.rpow_nonneg hZ0.le a)
    _ = Real.log 4 * Z ^ (1 + a) := by
      rw [Real.rpow_add hZ0, Real.rpow_one]
      ring

/-- Every real power is integrable on intervals bounded away from zero. -/
theorem rpow_integrableOn (Z a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ a) (Set.Icc 2 Z) := by
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  exact (continuousAt_id.rpow_const (Or.inl hx0)).continuousWithinAt

/-- The step-function Chebyshev weight times any real power is integrable. -/
theorem theta_rpow_integrableOn (Z a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ a * Chebyshev.theta x) (Set.Icc 2 Z) := by
  have h := integrableOn_mul_sum_Icc primeLog (m := 0) (by norm_num : (0 : ℝ) ≤ 2)
    (rpow_integrableOn Z a)
  simpa only [sum_primeLog] using h

/-- Abel summation specialized to the actual prime-log coefficient sequence. -/
theorem primePowerSum_abel {Z : ℝ} (hZ : 2 ≤ Z) (a : ℝ) :
    primePowerSum Z a = Z ^ a * Chebyshev.theta Z -
      a * ∫ x in (2 : ℝ)..Z, x ^ (a - 1) * Chebyshev.theta x := by
  have hd : ∀ x ∈ Set.Icc (2 : ℝ) Z,
      DifferentiableAt ℝ (fun x : ℝ => x ^ a) x := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1] : x ≠ 0))).differentiableAt
  have hi : IntegrableOn (deriv (fun x : ℝ => x ^ a)) (Set.Icc 2 Z) := by
    rw [Real.deriv_rpow_const']
    exact (rpow_integrableOn Z (a - 1)).const_mul a
  have hs := sum_mul_eq_sub_integral_mul₁ primeLog primeLog_zero primeLog_one Z hd hi
  rw [← primePowerSum_eq_sum] at hs
  simp_rw [sum_primeLog, Real.deriv_rpow_const] at hs
  rw [← intervalIntegral.integral_of_le hZ] at hs
  simpa only [mul_assoc, intervalIntegral.integral_const_mul] using hs

/-- Chebyshev controls the complete partial-summation integral, for every power. -/
theorem theta_power_integral_bound {Z : ℝ} (hZ : 2 ≤ Z) (a : ℝ) :
    (∫ x in (2 : ℝ)..Z, x ^ a * Chebyshev.theta x) ≤
      Real.log 4 * ∫ x in (2 : ℝ)..Z, x ^ (a + 1) := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ a * Chebyshev.theta x) volume 2 Z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hZ).mpr (theta_rpow_integrableOn Z a)
  have hj : IntervalIntegrable (fun x : ℝ => Real.log 4 * x ^ (a + 1)) volume 2 Z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hZ).mpr
      ((rpow_integrableOn Z (a + 1)).const_mul (Real.log 4))
  have hm := intervalIntegral.integral_mono_on hZ hi hj (fun x hx => by
    have hx0 : 0 < x := by linarith [hx.1]
    calc
      x ^ a * Chebyshev.theta x ≤ x ^ a * (Real.log 4 * x) :=
        mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hx0.le)
          (Real.rpow_nonneg hx0.le a)
      _ = Real.log 4 * x ^ (a + 1) := by
        rw [Real.rpow_add hx0, Real.rpow_one]
        ring)
  simpa only [intervalIntegral.integral_const_mul] using hm

theorem theta_power_integral_nonneg {Z : ℝ} (hZ : 2 ≤ Z) (a : ℝ) :
    0 ≤ ∫ x in (2 : ℝ)..Z, x ^ a * Chebyshev.theta x := by
  apply intervalIntegral.integral_nonneg hZ
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg (by linarith [hx.1]) a) (Chebyshev.theta_nonneg x)

/-- The second estimate in (50), with concrete `CCh=log 4`.
The proof establishes the actual partial-summation and power-integral bounds. -/
theorem primePowerSum_negative_exponent {Z α : ℝ}
    (hZ : 2 ≤ Z) (hα : 0 < α) (hα1 : α < 1) :
    primePowerSum Z (α - 1) ≤ Real.log 4 * (1 + 1 / α) * Z ^ α := by
  have hZ0 : 0 < Z := by linarith
  have hC : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  let I := ∫ x in (2 : ℝ)..Z, x ^ (α - 1 - 1) * Chebyshev.theta x
  have hI0 : 0 ≤ I := theta_power_integral_nonneg hZ _
  have hI : I ≤ Real.log 4 * (Z ^ α / α) := by
    have h := theta_power_integral_bound hZ (α - 1 - 1)
    have he : α - 1 - 1 + 1 = α - 1 := by ring
    rw [he, integral_rpow (Or.inl (by linarith : -1 < α - 1)),
      show α - 1 + 1 = α by ring] at h
    apply h.trans
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by norm_num) α)) hα.le) hC
  have hmain : Z ^ (α - 1) * Chebyshev.theta Z ≤ Real.log 4 * Z ^ α := by
    calc
      _ ≤ Z ^ (α - 1) * (Real.log 4 * Z) := mul_le_mul_of_nonneg_left
        (Chebyshev.theta_le_log4_mul_x hZ0.le) (Real.rpow_nonneg hZ0.le _)
      _ = Real.log 4 * (Z ^ (α - 1) * Z) := by ring
      _ = _ := by
        have hp : Z ^ (α - 1) * Z = Z ^ α := by
          calc
            _ = Z ^ (α - 1) * Z ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = Z ^ ((α - 1) + 1) := (Real.rpow_add hZ0 _ _).symm
            _ = _ := by congr 1; ring
        rw [hp]
  have hab := primePowerSum_abel hZ (α - 1)
  change primePowerSum Z (α - 1) = Z ^ (α - 1) * Chebyshev.theta Z - (α - 1) * I at hab
  have hcoef : -(α - 1) * I ≤ I := by nlinarith
  have htotal : primePowerSum Z (α - 1) ≤
      Real.log 4 * Z ^ α + Real.log 4 * (Z ^ α / α) := by linarith
  convert htotal using 1 <;> ring

/-- No prime contributes below two. -/
theorem primePowerSum_eq_zero_of_lt_two {Z : ℝ} (hZ : Z < 2) (a : ℝ) :
    primePowerSum Z a = 0 := by
  unfold primePowerSum
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpZ, hpprime⟩ := Nat.mem_primesLE.mp hp
  have hf : ⌊Z⌋₊ < 2 := (Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr hZ
  have hp2 := hpprime.two_le
  omega

/-- The second estimate (50) for every endpoint `Z≥1`. -/
theorem primePowerSum_negative_exponent_all {Z α : ℝ}
    (hZ : 1 ≤ Z) (hα : 0 < α) (hα1 : α < 1) :
    primePowerSum Z (α - 1) ≤ Real.log 4 * (1 + 1 / α) * Z ^ α := by
  by_cases hZ2 : 2 ≤ Z
  · exact primePowerSum_negative_exponent hZ2 hα hα1
  · rw [primePowerSum_eq_zero_of_lt_two (lt_of_not_ge hZ2)]
    have hC : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity

/-- The logarithmic prime-weight bound needed for the cusp contributions. -/
theorem primePowerSum_harmonic {Z : ℝ} (hZ : 1 ≤ Z) :
    primePowerSum Z (-1) ≤ Real.log 4 * (1 + Real.log Z) := by
  have hC : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hZ0 : 0 < Z := by linarith
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ
  by_cases hZ2 : 2 ≤ Z
  · let I := ∫ x in (2 : ℝ)..Z, x ^ (-2 : ℝ) * Chebyshev.theta x
    have hI : I ≤ Real.log 4 * Real.log Z := by
      have hi := theta_power_integral_bound hZ2 (-2)
      norm_num only [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one] at hi
      rw [integral_inv_of_pos (by norm_num) hZ0,
        Real.log_div hZ0.ne' (by norm_num)] at hi
      exact hi.trans (mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))) hC)
    have hmain : Z ^ (-1 : ℝ) * Chebyshev.theta Z ≤ Real.log 4 := by
      calc
        _ ≤ Z ^ (-1 : ℝ) * (Real.log 4 * Z) := mul_le_mul_of_nonneg_left
          (Chebyshev.theta_le_log4_mul_x hZ0.le) (Real.rpow_nonneg hZ0.le _)
        _ = _ := by rw [Real.rpow_neg_one]; field_simp
    have hab := primePowerSum_abel hZ2 (-1)
    have he : (-1 : ℝ) - 1 = -2 := by norm_num
    rw [he] at hab
    change primePowerSum Z (-1) = Z ^ (-1 : ℝ) * Chebyshev.theta Z - (-1) * I at hab
    nlinarith
  · rw [primePowerSum_eq_zero_of_lt_two (lt_of_not_ge hZ2)]
    positivity

/-- A uniform square-denominator prime-weight bound for the scalar term. -/
theorem primePowerSum_square_denominator {Z : ℝ} (hZ : 1 ≤ Z) :
    primePowerSum Z (-2) ≤ 2 * Real.log 4 := by
  have hC : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hZ0 : 0 < Z := by linarith
  by_cases hZ2 : 2 ≤ Z
  · let I := ∫ x in (2 : ℝ)..Z, x ^ (-3 : ℝ) * Chebyshev.theta x
    have hI : I ≤ Real.log 4 / 2 := by
      have hi := theta_power_integral_bound hZ2 (-3)
      have hz : (0 : ℝ) ∉ Set.uIcc 2 Z := by rw [Set.uIcc_of_le hZ2]; norm_num
      rw [show (-3 : ℝ) + 1 = -2 by norm_num,
        integral_rpow (Or.inr ⟨by norm_num, hz⟩),
        show (-2 : ℝ) + 1 = -1 by norm_num] at hi
      simp only [Real.rpow_neg_one] at hi
      have hinv : 0 ≤ Z⁻¹ := inv_nonneg.mpr hZ0.le
      have hfrac : (Z⁻¹ - (2 : ℝ)⁻¹) / (-1) ≤ 1 / 2 := by norm_num; linarith
      exact hi.trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hfrac hC)
    have hmain : Z ^ (-2 : ℝ) * Chebyshev.theta Z ≤ Real.log 4 := by
      calc
        _ ≤ Z ^ (-2 : ℝ) * (Real.log 4 * Z) := mul_le_mul_of_nonneg_left
          (Chebyshev.theta_le_log4_mul_x hZ0.le) (Real.rpow_nonneg hZ0.le _)
        _ = Real.log 4 * Z ^ (-1 : ℝ) := by
          have hp : Z ^ (-2 : ℝ) * Z = Z ^ (-1 : ℝ) := by
            calc
              _ = Z ^ (-2 : ℝ) * Z ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = Z ^ ((-2 : ℝ) + 1) := (Real.rpow_add hZ0 _ _).symm
              _ = _ := by norm_num
          calc
            _ = Real.log 4 * (Z ^ (-2 : ℝ) * Z) := by ring
            _ = _ := by rw [hp]
        _ ≤ Real.log 4 * 1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hZ (by norm_num)) hC
        _ = _ := mul_one _
    have hab := primePowerSum_abel hZ2 (-2)
    rw [show (-2 : ℝ) - 1 = -3 by norm_num] at hab
    change primePowerSum Z (-2) = Z ^ (-2 : ℝ) * Chebyshev.theta Z - (-2) * I at hab
    nlinarith
  · rw [primePowerSum_eq_zero_of_lt_two (lt_of_not_ge hZ2)]
    positivity

end DepthAspect.ChebyshevWeights
