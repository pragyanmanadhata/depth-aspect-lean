import DepthAspect.TheoremFiveFive
import DepthAspect.FourTwistCombination

/-!
# The actual weighted even-depth prime-average estimate

The four instances of Theorem 5.5 are combined with the actual table w(P).
The doubled weight is the one appearing after the common trace scale is
factored out, so the main coefficient is exactly G_t, not G_t/2.
-/
noncomputable section
namespace DepthAspect.EvenPrimeAverage
open MeasureTheory DirichletRH GRHConsequences QuadraticClassFormula
open QuadraticDiscriminantL FourDyadicTwists FourTwistCombination GlobalCoefficientTail
open scoped BigOperators

/-- The canonical finite character discrepancy is exactly the actual
prime L-value sum of Theorem 5.5, with only factors commuted. -/
theorem twistDiscrepancy_eq_primeLsum {H : ℤ → ℝ} (G : GeneralFormula H)
    (t : ℤ) (A B : ℝ) (Φ : ℝ → ℂ) (i : Fin 4) :
    twistDiscrepancy (PrimeAverageSmoothing.primeSet A B) t A B Φ
      (fun P => LAtOne G (t ^ 2 - 4 * (P : ℤ))) i =
      PrimeAverageSmoothing.primeLsum G t (character i) A B Φ -
        valueAtOne t (character i) * (∫ u in A..B, Φ u) := by
  unfold twistDiscrepancy PrimeAverageSmoothing.primeLsum
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  unfold PrimeAverageSmoothing.primeWeight
  simp only [Int.cast_neg, Int.cast_natCast]
  ring

/-- The actual doubled residue weight, with a constant uniform before
all discriminants, interval endpoints, class-formula data and tests. -/
theorem even_weighted_prime_average_bound
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
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
          B ^ (3 / 4 + ε) := by
  obtain ⟨Cε, hCε, hbound⟩ := TheoremFiveFive.prime_average_bound hRH cited hε
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
          B ^ (3 / 4 + ε) := by
    intro i
    rw [twistDiscrepancy_eq_primeLsum]
    exact hbound G t (character i) A B M Φ hA hAB hB htA hM hΦ hdΦ hI hMbound
  have hb := doubled_weighted_discrepancy_bound (PrimeAverageSmoothing.primeSet A B)
    t hT ht A B Φ (fun P => LAtOne G (t ^ 2 - 4 * (P : ℤ))) _ he
  exact hb.trans_eq (by ring)

end DepthAspect.EvenPrimeAverage
