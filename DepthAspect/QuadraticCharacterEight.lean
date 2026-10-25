import DepthAspect.QuadraticCharacterValues
import DepthAspect.QuadraticCharacterIntegrals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# The actual ordered L-value of the negative-eight character

The proof integrates a finite geometric polynomial and bounds its remainder
by 2/(4n+1). Thus no interchange of a conditionally convergent series is
assumed, and the endpoint x=1 is included in the error bound.
-/
namespace DepthAspect.QuadraticCharacterValues
open scoped BigOperators Topology
open Filter OrderedDirichlet ImprimitiveCharacter ClassNumberGrowth MeasureTheory

noncomputable def eightIntegrand (x : ℝ) : ℝ := (1 + x ^ 2) / (1 + x ^ 4)
noncomputable def eightPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  (1 + x ^ 2) * ∑ j ∈ Finset.range n, (-x ^ 4) ^ j
noncomputable def eightPartial (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j *
    (1 / (4 * (j : ℝ) + 1) + 1 / (4 * (j : ℝ) + 3))

@[fun_prop] theorem eightIntegrand_continuous : Continuous eightIntegrand := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  positivity

@[fun_prop] theorem eightPolynomial_continuous (n : ℕ) : Continuous (eightPolynomial n) := by
  unfold eightPolynomial
  fun_prop

theorem eightPolynomial_integral (n : ℕ) :
    (∫ x in (0 : ℝ)..1, eightPolynomial n x) = eightPartial n := by
  have heq (x : ℝ) : eightPolynomial n x =
      ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * (x ^ (4 * j) + x ^ (4 * j + 2)) := by
    unfold eightPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_pow, ← pow_mul, pow_add]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum
    (fun j hj => (by fun_prop : Continuous (fun x : ℝ =>
      (-1 : ℝ) ^ j * (x ^ (4 * j) + x ^ (4 * j + 2)))).intervalIntegrable _ _)]
  unfold eightPartial
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), integral_pow, integral_pow]
  simp only [one_pow, zero_pow (by omega : 4 * j + 1 ≠ 0),
    zero_pow (by omega : 4 * j + 2 + 1 ≠ 0), sub_zero]
  push_cast
  ring

theorem eightPolynomial_remainder (n : ℕ) (x : ℝ) :
    eightPolynomial n x - eightIntegrand x =
      -eightIntegrand x * (-x ^ 4) ^ n := by
  have hg := geom_sum_mul_neg (-x ^ 4) n
  have hg' : (∑ j ∈ Finset.range n, (-x ^ 4) ^ j) * (1 + x ^ 4) =
      1 - (-x ^ 4) ^ n := by simpa only [sub_neg_eq_add] using hg
  unfold eightPolynomial eightIntegrand
  have hd : 1 + x ^ 4 ≠ 0 := by positivity
  calc
    _ = ((1 + x ^ 2) / (1 + x ^ 4)) *
        ((∑ j ∈ Finset.range n, (-x ^ 4) ^ j) * (1 + x ^ 4) - 1) := by
      field_simp [hd] <;> ring
    _ = _ := by rw [hg']; ring

theorem eightPolynomial_remainder_bound (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |eightPolynomial n x - eightIntegrand x| ≤ 2 * x ^ (4 * n) := by
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith [hx.1, hx.2, mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hg0 : 0 ≤ eightIntegrand x := by unfold eightIntegrand; positivity
  have hg2 : eightIntegrand x ≤ 2 := by
    unfold eightIntegrand
    apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 4)).mpr
    nlinarith [pow_nonneg hx.1 4]
  rw [eightPolynomial_remainder, abs_mul, abs_neg, abs_of_nonneg hg0,
    abs_pow, abs_neg, abs_of_nonneg (pow_nonneg hx.1 4), ← pow_mul]
  exact mul_le_mul_of_nonneg_right hg2 (pow_nonneg hx.1 _)

/-- Finite, quantitative justification of the integral/series passage in (69). -/
theorem eightPartial_error (n : ℕ) :
    |eightPartial n - Real.pi / (2 * Real.sqrt 2)| ≤ 2 / (4 * (n : ℝ) + 1) := by
  have hi : (∫ x in (0 : ℝ)..1, eightIntegrand x) = Real.pi / (2 * Real.sqrt 2) :=
    QuadraticCharacterIntegrals.mod_eight_integral
  rw [← eightPolynomial_integral, ← hi,
    ← intervalIntegral.integral_sub ((eightPolynomial_continuous n).intervalIntegrable _ _)
      (eightIntegrand_continuous.intervalIntegrable _ _)]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, |eightPolynomial n x - eightIntegrand x| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ x in (0 : ℝ)..1, 2 * x ^ (4 * n) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop) (eightPolynomial_remainder_bound n)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [one_pow, zero_pow (by omega : 4 * n + 1 ≠ 0), sub_zero]
      push_cast
      ring

/-- The real finite block sums converge to the evaluated quartic integral. -/
theorem eightPartial_tendsto :
    Tendsto eightPartial atTop (𝓝 (Real.pi / (2 * Real.sqrt 2))) := by
  have hden : Tendsto (fun n : ℕ => 4 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hzero : Tendsto (fun n : ℕ => 2 / (4 * (n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hden).const_mul 2
  have hdiff : Tendsto (fun n => eightPartial n - Real.pi / (2 * Real.sqrt 2))
      atTop (𝓝 0) := squeeze_zero_norm (fun n => by
    simpa only [Real.norm_eq_abs] using eightPartial_error n) hzero
  exact tendsto_sub_nhds_zero_iff.mp hdiff

@[simp] theorem chiMinusEight_even (n : ℕ) : chiMinusEight (2 * n : ℕ) = 0 := by
  change ((ZMod.χ₈' (2 * n : ℕ) : ℤ) : ℂ) = 0
  rw [ZMod.χ₈'_nat_eq_if_mod_eight]
  simp

@[simp] theorem chiMinusEight_four_add_one (n : ℕ) :
    chiMinusEight (4 * n + 1 : ℕ) = (-1 : ℂ) ^ n := by
  change ((ZMod.χ₈' (4 * n + 1 : ℕ) : ℤ) : ℂ) = _
  rw [ZMod.χ₈'_nat_eq_if_mod_eight]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨a, rfl⟩ := he
    rw [show a + a = 2 * a by omega]
    simp [show (4 * (2 * a) + 1) % 2 = 1 by omega,
      show (4 * (2 * a) + 1) % 8 = 1 by omega, pow_mul]
  · obtain ⟨a, rfl⟩ := ho
    simp [show (4 * (2 * a + 1) + 1) % 2 = 1 by omega,
      show (4 * (2 * a + 1) + 1) % 8 = 5 by omega, pow_add, pow_mul]

@[simp] theorem chiMinusEight_four_add_three (n : ℕ) :
    chiMinusEight (4 * n + 3 : ℕ) = (-1 : ℂ) ^ n := by
  change ((ZMod.χ₈' (4 * n + 3 : ℕ) : ℤ) : ℂ) = _
  rw [ZMod.χ₈'_nat_eq_if_mod_eight]
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨a, rfl⟩ := he
    rw [show a + a = 2 * a by omega]
    simp [show (4 * (2 * a) + 3) % 2 = 1 by omega,
      show (4 * (2 * a) + 3) % 8 = 3 by omega, pow_mul]
  · obtain ⟨a, rfl⟩ := ho
    simp [show (4 * (2 * a + 1) + 3) % 2 = 1 by omega,
      show (4 * (2 * a + 1) + 3) % 8 = 7 by omega, pow_add, pow_mul]

theorem partialL_chiMinusEight_four (n : ℕ) :
    partialL (fun j : ℕ => chiMinusEight (j : ZMod 8)) (4 * n) = (eightPartial n : ℂ) := by
  induction n with
  | zero => simp [partialL, eightPartial]
  | succ n ih =>
    rw [show 4 * (n + 1) = (4 * n + 1 + 1 + 1) + 1 by omega,
      partialL_succ, partialL_succ, partialL_succ, partialL_succ, ih]
    rw [show 4 * n + 1 + 1 + 1 + 1 = 2 * (2 * n + 2) by omega,
      chiMinusEight_even,
      show 4 * n + 1 + 1 + 1 = 4 * n + 3 by omega, chiMinusEight_four_add_three,
      show 4 * n + 1 + 1 = 2 * (2 * n + 1) by omega, chiMinusEight_even,
      chiMinusEight_four_add_one]
    unfold eightPartial
    rw [Finset.sum_range_succ]
    push_cast
    ring

/-- The primitive negative-eight ordered L-value in equation (69). -/
theorem chiMinusEight_LAtOne :
    imprimitiveLAtOne chiMinusEight chiMinusEight_odd (by decide) 1 (by decide) =
      ((Real.pi / (2 * Real.sqrt 2) : ℝ) : ℂ) := by
  have hfour : Tendsto (fun n : ℕ => 4 * n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn => by omega⟩
  have hL := (imprimitiveLAtOne_limit chiMinusEight chiMinusEight_odd
    (by decide) 1 (by decide)).comp hfour
  have hπ := (Complex.continuous_ofReal.tendsto (Real.pi / (2 * Real.sqrt 2))).comp
    eightPartial_tendsto
  have hpsi : psiNat chiMinusEight 1 = (fun j : ℕ => chiMinusEight (j : ZMod 8)) :=
    funext (psiNat_conductor_one chiMinusEight)
  change Tendsto (fun n => partialL (psiNat chiMinusEight 1) (4 * n)) atTop _ at hL
  simp only [hpsi, partialL_chiMinusEight_four] at hL
  have hvalue := tendsto_nhds_unique hL hπ
  simpa using hvalue

end DepthAspect.QuadraticCharacterValues
