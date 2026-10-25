import DepthAspect.PrimeAverageSmoothing
import DepthAspect.ClassNumberGrowth

/-! The actual trivial prime-average bound used in the large-variation branch. -/
noncomputable section
open scoped BigOperators
namespace DepthAspect.PrimeAverageTrivial
open QuadraticClassFormula QuadraticDiscriminantL PrimeAverageSmoothing
open GlobalCoefficientTail

 theorem LAtOne_power_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (D : ℤ) (hD : IsNegativeDiscriminant D) {δ : ℝ} (hδ : 0 < δ) :
    ‖LAtOne G D‖ ≤ (2 + δ⁻¹) * (D.natAbs : ℝ) ^ δ := by
  rw [LAtOne, dif_pos hD]
  have h := ClassNumberGrowth.imprimitiveLAtOne_power_bound
    (character G D hD) (character_odd G D hD) (modulus_pos D hD)
    (datum D hD).conductor (datum D hD).conductor_pos hδ
  rw [NegativeDiscriminantSmoothing.conductor_size D hD] at h
  exact h

 theorem averaged_absolute_constant_nonneg :
    0 ≤ CoefficientTail.tailConstant / (1 - Real.exp (-1)) := by
  exact (norm_nonneg (valueAtOne 0 1)).trans (valueAtOne_bound 0 1)

/-- A uniform numerical constant, independent of the discriminant and test. -/
def constant (δ : ℝ) : ℝ :=
  (2 + δ⁻¹) * 4 ^ δ * Real.log 4 +
    CoefficientTail.tailConstant / (1 - Real.exp (-1))

 theorem constant_nonneg {δ : ℝ} (hδ : 0 < δ) : 0 ≤ constant δ := by
  unfold constant
  have := averaged_absolute_constant_nonneg
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

/-- The actual discrepancy is Oδ(M B^(1+δ)) before any prime cancellation.
The ordered-series bound, finite prime sum, and average tail are all derived. -/
theorem trivial_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (t : ℤ) (χ : DirichletCharacter ℂ 8) {A B M δ : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 1 ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) (hM0 : 0 ≤ M) (hδ : 0 < δ)
    (Φ : ℝ → ℂ) (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    ‖primeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u‖ ≤
      constant δ * M * B ^ (1 + δ) := by
  have hB0 : 0 < B := by linarith
  have hL (p : ℕ) (hp : p ∈ primeSet A B) :
      ‖LAtOne G (t ^ 2 - 4 * (p : ℤ))‖ ≤ (2 + δ⁻¹) * (4 * B) ^ δ := by
    apply (LAtOne_power_bound G _ (primeSet_discriminant hA ht hp) hδ).trans
    gcongr
    exact discriminant_abs_le hA ht hp
  have hsum : ‖primeLsum G t χ A B Φ‖ ≤
      (2 + δ⁻¹) * 4 ^ δ * Real.log 4 * M * B ^ (1 + δ) := by
    unfold primeLsum
    calc
      _ ≤ ∑ p ∈ primeSet A B, ‖primeWeight χ Φ p * LAtOne G (t ^ 2 - 4 * (p : ℤ))‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ primeSet A B, (M * Real.log p) * ((2 + δ⁻¹) * (4 * B) ^ δ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
          exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
        rw [norm_mul]
        exact mul_le_mul (norm_primeWeight_le hA χ Φ hM hp) (hL p hp)
          (norm_nonneg _) (by positivity)
      _ = (M * ∑ p ∈ primeSet A B, Real.log p) * ((2 + δ⁻¹) * (4 * B) ^ δ) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (M * (Real.log 4 * B)) * ((2 + δ⁻¹) * (4 * B) ^ δ) := by
        gcongr
        exact prime_log_sum_le hB0.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) hB0.le, Real.rpow_add hB0, Real.rpow_one]
        ring
  have hI := integral_norm_le hA hAB hM0 Φ hM
  have hb := valueAtOne_bound t χ
  have hmain : ‖valueAtOne t χ * ∫ u in A..B, Φ u‖ ≤
      (CoefficientTail.tailConstant / (1 - Real.exp (-1))) * M * B ^ (1 + δ) := by
    rw [norm_mul]
    apply (mul_le_mul hb hI (norm_nonneg _) averaged_absolute_constant_nonneg).trans
    have hpow : B ≤ B ^ (1 + δ) := by
      conv_lhs => rw [← Real.rpow_one B]
      exact Real.rpow_le_rpow_of_exponent_le hB (by linarith)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow
      (mul_nonneg averaged_absolute_constant_nonneg hM0)
  apply (norm_sub_le _ _).trans
  unfold constant
  nlinarith

end DepthAspect.PrimeAverageTrivial
