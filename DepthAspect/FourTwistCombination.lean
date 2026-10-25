import DepthAspect.FourDyadicTwists
import DepthAspect.DyadicWeightedMean
import DepthAspect.SignedPrimeClassWeights
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The actual four-twist combination used in the even-depth prime sum

The coefficient table is exactly the weight w(P) of (75)/(90). The finite
combination of (104) has total coefficient norm 9/16, and its main term is
proved from the actual dyadic averaged L-values. The individual (104)
discrepancies remain explicit intermediate inputs in this module.
-/
noncomputable section
namespace DepthAspect.FourTwistCombination
open MeasureTheory FourDyadicTwists GlobalCoefficientTail QuadraticDiscriminantL
open scoped BigOperators

/-- The four coefficients in the first line of (90). -/
def coefficient : Fin 4 → ℂ := ![13 / 32, -3 / 32, -1 / 32, -1 / 32]

theorem coefficient_norm_sum : (∑ i : Fin 4, ‖coefficient i‖) = 9 / 16 := by
  norm_num [coefficient, Fin.sum_univ_succ, norm_div]

private theorem twistValue_neg_one (i : Fin 4) :
    DyadicLocalMeans.twistValue i (-(1 : ZMod 8)) =
      (![1, -1, 1, -1] : Fin 4 → ℤ) i := by
  fin_cases i <;> decide

private theorem twistValue_neg_three (i : Fin 4) :
    DyadicLocalMeans.twistValue i (-(3 : ZMod 8)) =
      (![1, 1, -1, -1] : Fin 4 → ℤ) i := by
  fin_cases i <;> decide

private theorem twistValue_neg_five (i : Fin 4) :
    DyadicLocalMeans.twistValue i (-(5 : ZMod 8)) =
      (![1, -1, -1, 1] : Fin 4 → ℤ) i := by
  fin_cases i <;> decide

private theorem twistValue_neg_seven (i : Fin 4) :
    DyadicLocalMeans.twistValue i (-(7 : ZMod 8)) =
      (![1, 1, 1, 1] : Fin 4 → ℤ) i := by
  fin_cases i <;> decide

/-- The literal residue-table weight is the sum of the four actual
Dirichlet characters, evaluated at -P as in (104). -/
theorem primeWeight_character_expansion {P : ℕ} (hP : Odd P) :
    (primeWeight (P : ℤ) : ℂ) =
      ∑ i : Fin 4, coefficient i * character i (-(P : ZMod 8)) := by
  have hc2 : P.Coprime 2 := Nat.coprime_two_right.mpr hP
  have hc8 : P.Coprime 8 := by
    simpa using (Nat.coprime_pow_right_iff (by decide : 0 < 3) P 2).mpr hc2
  let u : (ZMod 8)ˣ := ZMod.unitOfCoprime P hc8
  have hu : (u : ZMod 8) = (P : ZMod 8) := ZMod.coe_unitOfCoprime P hc8
  have hχ (i : Fin 4) : character i (-(P : ZMod 8)) =
      (DyadicLocalMeans.twistValue i (-(P : ZMod 8)) : ℂ) := by
    simpa only [Units.val_neg, hu] using character_apply_unit i (-u)
  simp_rw [hχ]
  have hmod : P % 8 = 1 ∨ P % 8 = 3 ∨ P % 8 = 5 ∨ P % 8 = 7 := by
    have ho := Nat.odd_iff.mp hP
    omega
  rcases hmod with hmod | hmod | hmod | hmod
  all_goals
    have hcast : (P : ZMod 8) = ((P % 8 : ℕ) : ZMod 8) := by simp
    rw [hmod] at hcast
    have h4 : (P : ℤ) % 4 = ((P % 8) % 4 : ℕ) := by
      norm_cast
      omega
    have h8 : (P : ℤ) % 8 = (P % 8 : ℕ) := by norm_cast
    rw [hmod] at h4 h8
    norm_num [primeWeight, h4, h8, hcast, coefficient, Fin.sum_univ_succ,
      twistValue_neg_one, twistValue_neg_three, twistValue_neg_five, twistValue_neg_seven]

/-- The second line of (90), in finite-sum notation for the same table. -/
theorem weighted_mean_sum {t : ℤ} (ht : 8 ∣ t) :
    (∑ i : Fin 4, coefficient i * valueAtOne t (character i)) =
      (1 / 2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 8 *
        (ArithmeticWeights.integerPrimeWeight 2 t : ℂ)) := by
  have hm := DyadicWeightedMean.weighted_mean ht
  simpa [coefficient, Fin.sum_univ_succ, sub_eq_add_neg, neg_div, neg_mul, add_assoc] using hm

/-- A finite weighted prime discrepancy with the actual character and
actual averaged coefficient. The set T may already include any interval
and primality restrictions used by the caller. -/
def twistDiscrepancy (T : Finset ℕ) (t : ℤ) (A B : ℝ)
    (Φ : ℝ → ℂ) (V : ℕ → ℂ) (i : Fin 4) : ℂ :=
  (∑ P ∈ T, (Real.log (P : ℝ) : ℂ) *
    (character i (-(P : ZMod 8)) * V P * Φ P)) -
    valueAtOne t (character i) * (∫ u in A..B, Φ u)

/-- Exact finite linearity combines the true table and the true main
coefficient. No bound or integral interchange is assumed here. -/
theorem weighted_discrepancy_identity (T : Finset ℕ) (t : ℤ)
    (hT : ∀ P ∈ T, Odd P) (ht : 8 ∣ t) (A B : ℝ)
    (Φ : ℝ → ℂ) (V : ℕ → ℂ) :
    (∑ P ∈ T, (Real.log (P : ℝ) : ℂ) * ((primeWeight (P : ℤ) : ℂ) * V P * Φ P)) -
      ((1 / 2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 8 *
        (ArithmeticWeights.integerPrimeWeight 2 t : ℂ))) * (∫ u in A..B, Φ u) =
      ∑ i : Fin 4, coefficient i * twistDiscrepancy T t A B Φ V i := by
  rw [← weighted_mean_sum ht, Finset.sum_mul]
  have hsum :
      (∑ P ∈ T, (Real.log (P : ℝ) : ℂ) * ((primeWeight (P : ℤ) : ℂ) * V P * Φ P)) =
      ∑ i : Fin 4, coefficient i *
        ∑ P ∈ T, (Real.log (P : ℝ) : ℂ) *
          (character i (-(P : ZMod 8)) * V P * Φ P) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro P hP
    rw [primeWeight_character_expansion (hT P hP)]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold twistDiscrepancy
  ring

/-- Applying the four instances of (104) costs precisely 9/16. This is
the finite weighted consequence used before summing over trace indices. -/
theorem weighted_discrepancy_bound (T : Finset ℕ) (t : ℤ)
    (hT : ∀ P ∈ T, Odd P) (ht : 8 ∣ t) (A B : ℝ)
    (Φ : ℝ → ℂ) (V : ℕ → ℂ) (E : ℝ)
    (hE : ∀ i : Fin 4, ‖twistDiscrepancy T t A B Φ V i‖ ≤ E) :
    ‖(∑ P ∈ T, (Real.log (P : ℝ) : ℂ) * ((primeWeight (P : ℤ) : ℂ) * V P * Φ P)) -
      ((1 / 2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 8 *
        (ArithmeticWeights.integerPrimeWeight 2 t : ℂ))) * (∫ u in A..B, Φ u)‖ ≤
      (9 / 16 : ℝ) * E := by
  rw [weighted_discrepancy_identity T t hT ht A B Φ V]
  calc
    _ ≤ ∑ i : Fin 4, ‖coefficient i * twistDiscrepancy T t A B Φ V i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 4, ‖coefficient i‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hE i) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, coefficient_norm_sum]

/-- The even-depth trace normalization doubles w(P), so its averaged
coefficient is G_t and its discrepancy coefficient is exactly 9/8. -/
theorem doubled_weighted_discrepancy_bound (T : Finset ℕ) (t : ℤ)
    (hT : ∀ P ∈ T, Odd P) (ht : 8 ∣ t) (A B : ℝ)
    (Φ : ℝ → ℂ) (V : ℕ → ℂ) (E : ℝ)
    (hE : ∀ i : Fin 4, ‖twistDiscrepancy T t A B Φ V i‖ ≤ E) :
    ‖(∑ P ∈ T, (Real.log (P : ℝ) : ℂ) *
        ((2 : ℂ) * (primeWeight (P : ℤ) : ℂ) * V P * Φ P)) -
      ((Real.pi : ℂ) ^ 2 / 8 * (ArithmeticWeights.integerPrimeWeight 2 t : ℂ)) *
        (∫ u in A..B, Φ u)‖ ≤ (9 / 8 : ℝ) * E := by
  have hb := weighted_discrepancy_bound T t hT ht A B Φ V E hE
  have hid :
      (∑ P ∈ T, (Real.log (P : ℝ) : ℂ) *
        ((2 : ℂ) * (primeWeight (P : ℤ) : ℂ) * V P * Φ P)) -
        ((Real.pi : ℂ) ^ 2 / 8 * (ArithmeticWeights.integerPrimeWeight 2 t : ℂ)) *
          (∫ u in A..B, Φ u) =
      (2 : ℂ) * ((∑ P ∈ T, (Real.log (P : ℝ) : ℂ) *
        ((primeWeight (P : ℤ) : ℂ) * V P * Φ P)) -
        ((1 / 2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 8 *
          (ArithmeticWeights.integerPrimeWeight 2 t : ℂ))) * (∫ u in A..B, Φ u)) := by
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro P hP
      ring
    · ring
  rw [hid, norm_mul]
  norm_num only [Complex.norm_ofNat]
  nlinarith [hb]

end DepthAspect.FourTwistCombination
