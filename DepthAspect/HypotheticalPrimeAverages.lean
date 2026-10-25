import DepthAspect.SignedDensityTheorem

/-!
# The precise hypothetical strengthening in the final support discussion

This is a conditional interface, not an asserted estimate. Its two fields
are the literal arithmetic prime-average assertions (104) and (105), with
exponent 1/2+ε. Constants precede all discriminants, class data, intervals,
and test functions. No density or spectral-trace bound is assumed.
-/
namespace DepthAspect.HypotheticalSignedDensity
open MeasureTheory Set SignedDensity SignedSieve QuadraticClassFormula
open QuadraticDiscriminantL GlobalCoefficientTail
open FourDyadicTwists FourTwistCombination
open scoped BigOperators SchwartzMap FourierTransform

structure StrengthenedPrimeAverages : Prop where
  even : ∀ ε : ℝ, 0 < ε →
      ∃ Cε : ℝ, 0 < Cε ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
        (t : ℤ) (χ : DirichletCharacter ℂ 8) (A B M : ℝ) (Φ : ℝ → ℂ),
        0 ≤ A → A ≤ B → 3 ≤ B → (t : ℝ) ^ 2 ≤ 4 * A → 0 ≤ M →
        ContinuousOn Φ (Set.Icc A B) →
        (∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u) →
        IntegrableOn (deriv Φ) (Set.Icc A B) →
        (∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) →
        ‖PrimeAverageSmoothing.primeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u‖ ≤
          Cε * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
            B ^ (1 / 2 + ε)
  odd : ∀ ε : ℝ, 0 < ε →
      ∃ Cε : ℝ, 0 < Cε ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
        (t : ℤ) (A B M : ℝ) (Φ : ℝ → ℂ),
        8 ∣ t → 2 ≤ A → A ≤ B → 3 ≤ B → (t : ℝ) ^ 2 ≤ 8 * A → 0 ≤ M →
        ContinuousOn Φ (Set.Icc A B) →
        (∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u) →
        IntegrableOn (deriv Φ) (Set.Icc A B) →
        (∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) →
        ‖(∑ p ∈ PrimeAverageSmoothing.primeSet A B, (Real.log (p : ℝ) : ℂ) *
            (QuadraticDiscriminantL.LAtOne G (t ^ 2 - 8 * (p : ℤ)) * Φ p)) -
          (((Real.pi : ℂ) ^ 2 / 8) * (ArithmeticWeights.integerPrimeWeight 2 t : ℂ)) *
            (∫ u in A..B, Φ u)‖ ≤
          Cε * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
            B ^ (1 / 2 + ε)

theorem even_weighted_prime_average_bound
    (improved : StrengthenedPrimeAverages)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (t : ℤ) (A B M : ℝ) (Φ : ℝ → ℂ),
      8 ∣ t → 0 ≤ A → A ≤ B → 3 ≤ B → (t : ℝ) ^ 2 ≤ 4 * A → 0 ≤ M →
      ContinuousOn Φ (Set.Icc A B) →
      (∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u) →
      IntegrableOn (deriv Φ) (Set.Icc A B) →
      (∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) →
      ‖(∑ P ∈ PrimeAverageSmoothing.primeSet A B,
          (Real.log (P : ℝ) : ℂ) *
            ((2 : ℂ) * (primeWeight (P : ℤ) : ℂ) *
              LAtOne G (t ^ 2 - 4 * (P : ℤ)) * Φ P)) -
        ((Real.pi : ℂ) ^ 2 / 8 * (ArithmeticWeights.integerPrimeWeight 2 t : ℂ)) *
          (∫ u in A..B, Φ u)‖ ≤
        C * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
          B ^ (1 / 2 + ε) := by
  obtain ⟨Cε, hCε, hbound⟩ := improved.even ε hε
  refine ⟨(9 / 8) * Cε, by positivity, ?_⟩
  intro H G t A B M Φ ht hA hAB hB htA hM hΦ hdΦ hI hMbound
  have hT : ∀ P ∈ PrimeAverageSmoothing.primeSet A B, Odd P := by
    intro P hP
    obtain ⟨_, hprime, htwo⟩ := Finset.mem_filter.mp hP
    exact hprime.odd_of_ne_two htwo
  have he : ∀ i : Fin 4,
      ‖twistDiscrepancy (PrimeAverageSmoothing.primeSet A B) t A B Φ
        (fun P => LAtOne G (t ^ 2 - 4 * (P : ℤ))) i‖ ≤
        Cε * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
          B ^ (1 / 2 + ε) := by
    intro i
    rw [EvenPrimeAverage.twistDiscrepancy_eq_primeLsum]
    exact hbound G t (character i) A B M Φ hA hAB hB htA hM hΦ hdΦ hI hMbound
  have hb := doubled_weighted_discrepancy_bound (PrimeAverageSmoothing.primeSet A B)
    t hT ht A B Φ (fun P => LAtOne G (t ^ 2 - 4 * (P : ℤ))) _ he
  exact hb.trans_eq (by ring)

end DepthAspect.HypotheticalSignedDensity
