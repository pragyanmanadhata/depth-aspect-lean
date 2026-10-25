import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

open scoped BigOperators

/-!
# Exact dyadic calculations in Sections 5 and 6

This module proves finite algebra used by the paper. It does not assume a trace
formula or an analytic estimate. It also does not assert that the entire paper
has been formalized.
-/
namespace DepthAspect.Dyadic

/-- The four coefficients of the signed newspace sieve, (66). -/
def alpha (j : ℕ) : ℤ :=
  match j with
  | 0 => 1
  | 1 => -1
  | 2 => -1
  | 3 => 1
  | _ => 0

/-- The coefficient of the stratum `v = N / 2^b`, after putting `t = v*u`.
`oddU` records whether `u` is odd. The two restrictions in the summand are
exactly `j ≤ b` and the squarefree-gcd restriction `oddU ∨ b-j ≤ 1`. -/
def stratumCoefficient (b : ℕ) (oddU : Bool) : ℤ :=
  ∑ j ∈ Finset.range 4,
    if j ≤ b ∧ (oddU = true ∨ b ≤ j + 1) then alpha j else 0

 theorem alpha_sum : (∑ j ∈ Finset.range 4, alpha j) = 0 := by
  norm_num [alpha, Finset.sum_range_succ]

 theorem alpha_first_moment : (∑ j ∈ Finset.range 4, (j : ℤ) * alpha j) = 0 := by
  norm_num [alpha, Finset.sum_range_succ]

/-- The odd-`u` rows of table (72), including the assertion that all unlisted
strata vanish. -/
 theorem stratum_odd (b : ℕ) :
    stratumCoefficient b true =
      if b = 0 then 1 else if b = 2 then -1 else 0 := by
  by_cases h : b < 5
  · interval_cases b <;> norm_num [stratumCoefficient, alpha, Finset.sum_range_succ]
  · have h0 : b ≠ 0 := by omega
    have h2 : b ≠ 2 := by omega
    have h1 : 1 ≤ b := by omega
    have h3 : 3 ≤ b := by omega
    simp [stratumCoefficient, alpha, Finset.sum_range_succ, h0, h2, h1,
      show 2 ≤ b by omega, h3]

/-- The even-`u` rows of table (72), including all vanishing strata. -/
 theorem stratum_even (b : ℕ) :
    stratumCoefficient b false =
      if b = 0 then 1 else if b = 2 then -2 else if b = 4 then 1 else 0 := by
  by_cases h : b < 5
  · interval_cases b <;> norm_num [stratumCoefficient, alpha, Finset.sum_range_succ]
  · have h0 : b ≠ 0 := by omega
    have h2 : b ≠ 2 := by omega
    have h4 : b ≠ 4 := by omega
    simp [stratumCoefficient, alpha, Finset.sum_range_succ, h0, h2, h4,
      show ¬ b ≤ 1 by omega, show ¬ b ≤ 2 by omega,
      show ¬ b ≤ 3 by omega, show ¬ b ≤ 4 by omega]

/-- The factor `T_e` in the elementary local class-number identity (77).
The parameter `a` is the Kronecker symbol at 2. -/
def classNumberFactor (a : ℚ) (e : ℕ) : ℚ :=
  1 + (2 - a) * (2 ^ e - 1)

 theorem classNumberFactor_zero (a : ℚ) : classNumberFactor a 0 = 1 := by
  simp [classNumberFactor]

 theorem classNumberFactor_difference (a : ℚ) (e : ℕ) :
    classNumberFactor a (e + 1) - classNumberFactor a e = (2 - a) * 2 ^ e := by
  simp only [classNumberFactor, pow_succ]
  ring

/-- The geometric difference relation underlying (77), with no positivity or
Kronecker-symbol assumptions needed for the algebra. -/
 theorem classNumberFactor_scaled_difference (a : ℚ) (e j : ℕ) :
    classNumberFactor a (e + j + 1) - classNumberFactor a (e + j) =
      2 ^ j * (classNumberFactor a (e + 1) - classNumberFactor a e) := by
  rw [classNumberFactor_difference, classNumberFactor_difference, pow_add]
  ring

/-- Multiplying the previous relation by the primitive odd-part class number
recovers the class-number difference relation used in the trace sieve. -/
 theorem classNumber_scaled_difference (a base : ℚ) (e j : ℕ) :
    classNumberFactor a (e + j + 1) * base - classNumberFactor a (e + j) * base =
      2 ^ j * (classNumberFactor a (e + 1) * base - classNumberFactor a e * base) := by
  calc
    _ = (classNumberFactor a (e + j + 1) - classNumberFactor a (e + j)) * base := by ring
    _ = _ := by
      rw [classNumberFactor_scaled_difference]
      ring

/-- The algebraic reduction of the even-depth elliptic trace in (78).
`full` and `half` will be divisibility indicators. The identity is valid for
arbitrary rational values of those indicators. -/
 theorem even_elliptic_reduction (a base full half : ℚ) (e j : ℕ) :
    half * ((classNumberFactor a (e + j + 1) - classNumberFactor a (e + j)) * base) -
    full * ((classNumberFactor a (e + (j + 1) + 1) - classNumberFactor a (e + (j + 1))) * base) =
      -(1 / 2 : ℚ) * (2 ^ (j + 2) * full - 2 ^ (j + 1) * half) *
        ((classNumberFactor a (e + 1) - classNumberFactor a e) * base) := by
  rw [classNumberFactor_scaled_difference, classNumberFactor_scaled_difference]
  simp only [pow_succ]
  ring

/-- The same calculation with the odd-depth Ramanujan normalization, (80). -/
 theorem odd_elliptic_reduction (a base full half : ℚ) (e j : ℕ) :
    half * ((classNumberFactor a (e + j + 1) - classNumberFactor a (e + j)) * base) -
    full * ((classNumberFactor a (e + (j + 1) + 1) - classNumberFactor a (e + (j + 1))) * base) =
      -(1 / 4 : ℚ) * (2 ^ (j + 3) * full - 2 ^ (j + 2) * half) *
        ((classNumberFactor a (e + 1) - classNumberFactor a e) * base) := by
  rw [classNumberFactor_scaled_difference, classNumberFactor_scaled_difference]
  simp only [pow_succ]
  ring

/-- At valuation three, the local symbol at 2 is zero and the square-factor
exponent is zero. This produces the final doubling in (80). -/
 theorem odd_depth_classNumber_ratio (base : ℚ) :
    classNumberFactor 0 1 * base - classNumberFactor 0 0 * base = 2 * base := by
  norm_num [classNumberFactor]
  ring

/-- The four rational functions asserted for the local factors in (89). -/
def Etrivial (z : ℚ) : ℚ := (2 + z - 2 * z ^ 2) / (2 * (1 - z ^ 2))
def EminusFour (z : ℚ) : ℚ := z / (2 * (1 - z ^ 2))
def Eeight (z : ℚ) : ℚ := z ^ 2 / (2 * (1 - z ^ 2))
def EminusEight (z : ℚ) : ℚ := z ^ 2 / (2 * (1 - z ^ 2))

 theorem Etrivial_half : Etrivial (1 / 2) = 4 / 3 := by norm_num [Etrivial]
 theorem EminusFour_half : EminusFour (1 / 2) = 1 / 3 := by norm_num [EminusFour]
 theorem Eeight_half : Eeight (1 / 2) = 1 / 6 := by norm_num [Eeight]
 theorem EminusEight_half : EminusEight (1 / 2) = 1 / 6 := by norm_num [EminusEight]

/-- The local weighted mean in (90). This is the numerical identity after
factorization of the odd Euler product; that factorization is not assumed here. -/
 theorem weighted_local_mean :
    (13 / 32 : ℚ) * Etrivial (1 / 2) -
    (3 / 32 : ℚ) * EminusFour (1 / 2) -
    (1 / 32 : ℚ) * Eeight (1 / 2) -
    (1 / 32 : ℚ) * EminusEight (1 / 2) = 1 / 2 := by
  norm_num [Etrivial, EminusFour, Eeight, EminusEight]

/-- The character expansion of the prime weight, evaluated on the residue
classes 1, 3, 5, and 7 modulo 8. -/
def characterWeight (a b c : ℚ) : ℚ := (13 - 3 * a - b - c) / 32

 theorem weight_residue_one : characterWeight (-1) 1 (-1) = 1 / 2 := by
  norm_num [characterWeight]
 theorem weight_residue_three : characterWeight 1 (-1) (-1) = 3 / 8 := by
  norm_num [characterWeight]
 theorem weight_residue_five : characterWeight (-1) (-1) 1 = 1 / 2 := by
  norm_num [characterWeight]
 theorem weight_residue_seven : characterWeight 1 1 1 = 1 / 4 := by
  norm_num [characterWeight]

/-- A normalization identity for the even-depth sign trace in (70). -/
 theorem even_depth_normalization (a : ℕ) :
    (2 : ℚ) ^ (a + 3) / 8 = 2 ^ a := by
  rw [pow_add]
  norm_num

end DepthAspect.Dyadic
