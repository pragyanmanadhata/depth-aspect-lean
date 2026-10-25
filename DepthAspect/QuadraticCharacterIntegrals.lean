import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The two elementary integrals in (69)

The quartic integral is evaluated using an antiderivative with no endpoint
singularity. The later character-series bridge must identify these actual
integrals with the actual ordered L-values; that identification is not a
premise or a conclusion of this module.
-/
namespace DepthAspect.QuadraticCharacterIntegrals
open Real

theorem mod_four_integral :
    (∫ x : ℝ in (0 : ℝ)..1, 1 / (1 + x ^ 2)) = Real.pi / 4 := by
  rw [integral_one_div_one_add_sq, arctan_one, arctan_zero, sub_zero]

noncomputable def quarticPrimitive (x : ℝ) : ℝ :=
  (Real.arctan (Real.sqrt 2 * x + 1) + Real.arctan (Real.sqrt 2 * x - 1)) /
    Real.sqrt 2

theorem quarticPrimitive_derivative (x : ℝ) :
    HasDerivAt quarticPrimitive ((1 + x ^ 2) / (1 + x ^ 4)) x := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ha := (((hasDerivAt_id x).const_mul (Real.sqrt 2)).add_const 1).arctan
  have hb := (((hasDerivAt_id x).const_mul (Real.sqrt 2)).sub_const 1).arctan
  have hdplus : 0 < 1 + (Real.sqrt 2 * x + 1) ^ 2 := by positivity
  have hdminus : 0 < 1 + (Real.sqrt 2 * x - 1) ^ 2 := by positivity
  have hdquartic : 0 < 1 + x ^ 4 := by positivity
  have hsum : (1 + (Real.sqrt 2 * x + 1) ^ 2) +
      (1 + (Real.sqrt 2 * x - 1) ^ 2) = 4 * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt 2 * x),
      show (Real.sqrt 2 * x) ^ 2 = 2 * x ^ 2 by rw [mul_pow, hsq]]
  have hproduct : (1 + (Real.sqrt 2 * x + 1) ^ 2) *
      (1 + (Real.sqrt 2 * x - 1) ^ 2) = 4 * (1 + x ^ 4) := by
    calc
      _ = (Real.sqrt 2 * x) ^ 4 + 4 := by ring
      _ = _ := by rw [mul_pow, show (Real.sqrt 2) ^ 4 = 4 by
        calc
          (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
          _ = 4 := by rw [hsq]; norm_num]; ring
  have he : 1 / (1 + (Real.sqrt 2 * x + 1) ^ 2) +
      1 / (1 + (Real.sqrt 2 * x - 1) ^ 2) = (1 + x ^ 2) / (1 + x ^ 4) := by
    rw [div_add_div _ _ hdplus.ne' hdminus.ne']
    simp only [one_mul, mul_one]
    rw [add_comm (1 + (Real.sqrt 2 * x - 1) ^ 2) (1 + (Real.sqrt 2 * x + 1) ^ 2),
      hsum, hproduct]
    field_simp [hdquartic.ne'] <;> ring
  have hderiv : ((1 / (1 + (Real.sqrt 2 * x + 1) ^ 2) * Real.sqrt 2) +
      (1 / (1 + (Real.sqrt 2 * x - 1) ^ 2) * Real.sqrt 2)) / Real.sqrt 2 =
      (1 + x ^ 2) / (1 + x ^ 4) := by
    rw [← add_mul, mul_div_cancel_right₀ _ hp.ne']
    exact he
  have h := (ha.add hb).div_const (Real.sqrt 2)
  simp only [mul_one, id_eq] at h
  rw [hderiv] at h
  exact h

@[simp] theorem quarticPrimitive_zero : quarticPrimitive 0 = 0 := by
  simp [quarticPrimitive, Real.arctan_neg]

theorem quarticPrimitive_one : quarticPrimitive 1 = Real.pi / (2 * Real.sqrt 2) := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 + 1 := by positivity
  have hinv : (Real.sqrt 2 + 1)⁻¹ = Real.sqrt 2 - 1 := by
    apply inv_eq_of_mul_eq_one_left
    nlinarith
  have hangle := Real.arctan_inv_of_pos hp
  rw [hinv] at hangle
  simp only [quarticPrimitive, mul_one]
  rw [hangle]
  ring

theorem mod_eight_integral :
    (∫ x : ℝ in (0 : ℝ)..1, (1 + x ^ 2) / (1 + x ^ 4)) =
      Real.pi / (2 * Real.sqrt 2) := by
  have hc : Continuous (fun x : ℝ => (1 + x ^ 2) / (1 + x ^ 4)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => quarticPrimitive_derivative x) (hc.intervalIntegrable 0 1),
    quarticPrimitive_one, quarticPrimitive_zero, sub_zero]

end DepthAspect.QuadraticCharacterIntegrals
