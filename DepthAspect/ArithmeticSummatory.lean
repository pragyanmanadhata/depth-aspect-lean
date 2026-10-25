import DepthAspect.ArithmeticWeightSummability
import DepthAspect.HarmonicRemainder
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The literal divisor reindexing and harmonic substitution in (124). -/
namespace DepthAspect.ArithmeticWeights

open ArithmeticFunction
open scoped BigOperators

noncomputable def partialC (ℓ : ℕ) (X : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊X⌋₊, c ℓ d

/-- The inner finite reciprocal sum is the actual rational harmonic number,
coerced to the reals. -/
theorem reciprocal_sum_Ioc (N : ℕ) :
    (∑ b ∈ Finset.Ioc 0 N, reciprocal b) = (harmonic N : ℝ) := by
  have hset : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext b
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset, harmonic_eq_sum_Icc]
  simp only [reciprocal_apply, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Equation (124)'s exact finite reindexing, including nonintegral endpoints.
The convolution identity itself was proved from the actual Möbius transform. -/
theorem partialC_eq_harmonic_sum (ℓ : ℕ) (X : ℝ) :
    partialC ℓ X = ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊,
      h ℓ a * (harmonic ⌊X / (a : ℝ)⌋₊ : ℝ) := by
  unfold partialC
  rw [← h_convolution_reciprocal ℓ, sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [reciprocal_sum_Ioc, Nat.floor_div_natCast]

/-- Substituting the proved harmonic estimate gives the finite remainder
before any extension to infinite coefficient sums. -/
theorem partialC_harmonic_error (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |partialC ℓ X - ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊,
      h ℓ a * (Real.log (X / a) + Real.eulerMascheroniConstant)| ≤
      (2 / X) * ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊, |h ℓ a| * a := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  rw [partialC_eq_harmonic_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  have ha' := Finset.mem_Ioc.mp ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha'.1
  have haX : (a : ℝ) ≤ X := (by exact_mod_cast ha'.2 : (a : ℝ) ≤ ⌊X⌋₊).trans
    (Nat.floor_le hX0.le)
  have hT : 1 ≤ X / (a : ℝ) := (le_div_iff₀ ha0).mpr (by simpa using haX)
  have he := HarmonicRemainder.harmonic_floor_remainder hT
  calc
    |h ℓ a * (harmonic ⌊X / (a : ℝ)⌋₊ : ℝ) -
        h ℓ a * (Real.log (X / a) + Real.eulerMascheroniConstant)| =
      |h ℓ a| * |(harmonic ⌊X / (a : ℝ)⌋₊ : ℝ) -
        Real.log (X / a) - Real.eulerMascheroniConstant| := by
      rw [← mul_sub, abs_mul, sub_add_eq_sub_sub]
    _ ≤ |h ℓ a| * (2 / (X / a)) := mul_le_mul_of_nonneg_left he (abs_nonneg _)
    _ = (2 / X) * (|h ℓ a| * a) := by field_simp

/-- A concrete finite-moment bound, used for the harmonic remainder in (123). -/
theorem finite_first_moment (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    (∑ a ∈ Finset.Ioc 0 ⌊X⌋₊, |h ℓ a| * a) ≤
      X ^ (5 / 8 : ℝ) * ∑' a : ℕ, |h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊,
        X ^ (5 / 8 : ℝ) * (|h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' := Finset.mem_Ioc.mp ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha'.1
      have haX : (a : ℝ) ≤ X :=
        (by exact_mod_cast ha'.2 : (a : ℝ) ≤ ⌊X⌋₊).trans (Nat.floor_le hX0.le)
      have hp := Real.rpow_le_rpow ha0.le haX (by norm_num : (0 : ℝ) ≤ 5 / 8)
      have hid : (a : ℝ) = (a : ℝ) ^ (3 / 8 : ℝ) * (a : ℝ) ^ (5 / 8 : ℝ) := by
        rw [← Real.rpow_add ha0]
        norm_num
      calc
        |h ℓ a| * (a : ℝ) =
            (|h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ)) * (a : ℝ) ^ (5 / 8 : ℝ) := by
          rw [mul_assoc, ← hid]
        _ ≤ X ^ (5 / 8 : ℝ) * (|h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ)) := by
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp
            (mul_nonneg (abs_nonneg (h ℓ a)) (Real.rpow_nonneg ha0.le (3 / 8 : ℝ)))
    _ = X ^ (5 / 8 : ℝ) *
        ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊, |h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((coefficient_three_eighth_moment ℓ).sum_le_tsum _ (fun a _ => by positivity))
      (by positivity)

/-- The finite harmonic substitution actually has a slightly stronger
`X^(-3/8)` remainder than needed for (123). -/
theorem partialC_harmonic_moment_error (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |partialC ℓ X - ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊,
      h ℓ a * (Real.log (X / a) + Real.eulerMascheroniConstant)| ≤
      2 * (∑' a : ℕ, |h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ)) * X ^ (-3 / 8 : ℝ) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  calc
    _ ≤ (2 / X) * ∑ a ∈ Finset.Ioc 0 ⌊X⌋₊, |h ℓ a| * a :=
      partialC_harmonic_error ℓ hX
    _ ≤ (2 / X) * (X ^ (5 / 8 : ℝ) *
        ∑' a : ℕ, |h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_first_moment ℓ hX) (by positivity)
    _ = _ := by
      rw [show (-3 / 8 : ℝ) = 5 / 8 - 1 by norm_num, Real.rpow_sub hX0, Real.rpow_one]
      ring

end DepthAspect.ArithmeticWeights
