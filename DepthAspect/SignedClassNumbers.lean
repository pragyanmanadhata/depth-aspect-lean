import DepthAspect.DyadicClassScaling
import DepthAspect.QuadraticCharacterEight

/-!
# The class numbers and sign trace at dyadic index one

The two base ordered L-values and the conductor-two identity are proved in
the imported modules. Only the general class-number identity is supplied to
identify the actual analytic expressions with H. The elementary sign trace
combination is then evaluated exactly, including both parity classes.
-/
namespace DepthAspect.SignedClassNumbers
open QuadraticCharacterValues DyadicClassScaling

@[simp] theorem chiMinusFour_two : chiMinusFour (2 : ZMod 4) = 0 := by
  simpa using chiMinusFour_even 1

@[simp] theorem chiMinusEight_two : chiMinusEight (2 : ZMod 8) = 0 := by
  simpa using chiMinusEight_even 1

theorem classValue_minus_four_one :
    classValue chiMinusFour chiMinusFour_odd (by decide) 1 (by decide) = 1 / 2 := by
  unfold classValue
  rw [chiMinusFour_LAtOne, Complex.ofReal_re]
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [hs4]
  field_simp [Real.pi_ne_zero] <;> ring

theorem classValue_minus_eight_one :
    classValue chiMinusEight chiMinusEight_odd (by decide) 1 (by decide) = 1 := by
  unfold classValue
  rw [chiMinusEight_LAtOne, Complex.ofReal_re]
  norm_num
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num), hs4]
  rw [hs]
  field_simp [Real.pi_ne_zero, ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))] <;> ring

theorem classValue_minus_four_two_pow (e : ℕ) :
    classValue chiMinusFour chiMinusFour_odd (by decide) (2 ^ e) (by positivity) =
      (2 : ℝ) ^ e - 1 / 2 := by
  have h := classValue_two_part chiMinusFour chiMinusFour_odd (by decide) e 1
    (by decide) (by decide) 0 (by simp)
  simp only [mul_one, classValue_minus_four_one, localClassFactor, sub_zero] at h
  rw [h]
  ring

theorem classValue_minus_eight_two_pow (e : ℕ) :
    classValue chiMinusEight chiMinusEight_odd (by decide) (2 ^ e) (by positivity) =
      (2 : ℝ) ^ (e + 1) - 1 := by
  have h := classValue_two_part chiMinusEight chiMinusEight_odd (by decide) e 1
    (by decide) (by decide) 0 (by simp)
  simp only [mul_one, classValue_minus_eight_one, localClassFactor, sub_zero] at h
  rw [h, pow_succ]
  ring

/-- The first actual class-number evaluation in (70). -/
theorem hurwitz_even_power (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-4 * (f : ℤ) ^ 2) = classValue chiMinusFour chiMinusFour_odd (by decide) f hf)
    (e : ℕ) : H (-(2 : ℤ) ^ (2 * e + 2)) = (2 : ℝ) ^ e - 1 / 2 := by
  have he : -(2 : ℤ) ^ (2 * e + 2) = -4 * ((2 ^ e : ℕ) : ℤ) ^ 2 := by
    push_cast
    rw [pow_add, mul_comm 2 e, pow_mul]
    ring
  rw [he, hformula _ (by positivity), classValue_minus_four_two_pow]

/-- The second actual class-number evaluation in (70). -/
theorem hurwitz_odd_power (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-8 * (f : ℤ) ^ 2) = classValue chiMinusEight chiMinusEight_odd (by decide) f hf)
    (e : ℕ) : H (-(2 : ℤ) ^ (2 * e + 3)) = (2 : ℝ) ^ (e + 1) - 1 := by
  have he : -(2 : ℤ) ^ (2 * e + 3) = -8 * ((2 ^ e : ℕ) : ℤ) ^ 2 := by
    push_cast
    rw [pow_add, mul_comm 2 e, pow_mul]
    ring
  rw [he, hformula _ (by positivity), classValue_minus_eight_two_pow]

/-- The exact combination obtained from the signed sieve at index one. -/
noncomputable def indexOneClassTrace (H : ℤ → ℝ) (n : ℕ) : ℝ :=
  (H (-(2 : ℤ) ^ (n + 2)) - 2 * H (-(2 : ℤ) ^ n) +
    H (-(2 : ℤ) ^ (n - 2))) / 2

theorem indexOneClassTrace_even (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-4 * (f : ℤ) ^ 2) = classValue chiMinusFour chiMinusFour_odd (by decide) f hf)
    (a : ℕ) (ha : 3 ≤ a) :
    indexOneClassTrace H (2 * a) = (2 : ℝ) ^ (a - 3) := by
  unfold indexOneClassTrace
  rw [hurwitz_even_power H hformula a,
    show 2 * a = 2 * (a - 1) + 2 by omega,
    hurwitz_even_power H hformula (a - 1)]
  have he : (2 * (a - 1) + 2) - 2 = 2 * (a - 2) + 2 := by omega
  rw [he, hurwitz_even_power H hformula (a - 2)]
  have ha0 : (2 : ℝ) ^ a = 8 * 2 ^ (a - 3) := by
    conv_lhs => rw [show a = (a - 3) + 3 by omega, pow_add]
    ring
  have ha1 : (2 : ℝ) ^ (a - 1) = 4 * 2 ^ (a - 3) := by
    conv_lhs => rw [show a - 1 = (a - 3) + 2 by omega, pow_add]
    ring
  have ha2 : (2 : ℝ) ^ (a - 2) = 2 * 2 ^ (a - 3) := by
    conv_lhs => rw [show a - 2 = (a - 3) + 1 by omega, pow_add]
    ring
  rw [ha0, ha1, ha2]
  ring

theorem indexOneClassTrace_odd (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-8 * (f : ℤ) ^ 2) = classValue chiMinusEight chiMinusEight_odd (by decide) f hf)
    (a : ℕ) (ha : 2 ≤ a) :
    indexOneClassTrace H (2 * a + 1) = (2 : ℝ) ^ (a - 2) := by
  unfold indexOneClassTrace
  rw [show 2 * a + 1 + 2 = 2 * a + 3 by omega,
    hurwitz_odd_power H hformula a,
    show 2 * a + 1 = 2 * (a - 1) + 3 by omega,
    hurwitz_odd_power H hformula (a - 1)]
  have he : (2 * (a - 1) + 3) - 2 = 2 * (a - 2) + 3 := by omega
  rw [he, hurwitz_odd_power H hformula (a - 2)]
  have ha0 : (2 : ℝ) ^ (a + 1) = 8 * 2 ^ (a - 2) := by
    conv_lhs => rw [show a + 1 = (a - 2) + 3 by omega, pow_add]
    ring
  have ha1 : (2 : ℝ) ^ (a - 1 + 1) = 4 * 2 ^ (a - 2) := by
    conv_lhs => rw [show a - 1 + 1 = (a - 2) + 2 by omega, pow_add]
    ring
  have ha2 : (2 : ℝ) ^ (a - 2 + 1) = 2 * 2 ^ (a - 2) := by
    rw [pow_add]
    ring
  rw [ha0, ha1, ha2]
  ring

end DepthAspect.SignedClassNumbers
