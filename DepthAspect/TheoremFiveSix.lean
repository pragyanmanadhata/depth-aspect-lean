import DepthAspect.OddPrimeAverageTrivial
import DepthAspect.SmoothingLossAbsorption
import DepthAspect.GRHConsequences

/-!
# The actual uniform prime-average theorem (105)

The input is the zero-location primitive Dirichlet RH predicate, together with
its two cited general analytic implications. The uniform constant is chosen
before the quadratic-character/class-formula data, discriminant,
interval, and test weight. Every local arithmetic, Fourier, smoothing, omitted
prime, and optimization estimate is supplied by the preceding proofs.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DepthAspect.TheoremFiveSix
open DirichletRH GRHConsequences QuadraticClassFormula
open OddPrimeAverageSmoothing OddDepthCoefficientAverages SmoothingLossAbsorption
open PrimeAverageSmoothing (smoothingConstant_nonneg)

/-- Theorem 5.6 for the actual odd-prime sum and odd averaged coefficient,
with the slightly weaker endpoint differentiability hypothesis
actually needed by Abel summation. A supplied uniform bound M may replace the
maximum; taking M=max|Φ| gives the paper's exact statement. -/
theorem prime_average_bound (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (t : ℤ) (A B M : ℝ) (Φ : ℝ → ℂ),
      8 ∣ t → 2 ≤ A → A ≤ B → 3 ≤ B → (t : ℝ) ^ 2 ≤ 8 * A → 0 ≤ M →
      ContinuousOn Φ (Set.Icc A B) →
      (∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u) →
      IntegrableOn (deriv Φ) (Set.Icc A B) →
      (∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) →
      ‖primeLsum G t A B Φ - valueAtOne t * ∫ u in A..B, Φ u‖ ≤
        Cε * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
          B ^ (3 / 4 + ε) := by
  let η : ℝ := min (ε / 4) (1 / 8)
  let δ : ℝ := η / 2
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 / 4 := (min_le_right _ _).trans (by norm_num)
  have hηε : 2 * η ≤ ε := by have := min_le_left (ε / 4) (1 / 8 : ℝ); dsimp [η]; linarith
  have hδ0 : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 / 4 := by dsimp [δ]; linarith
  have hδε : 3 * δ ≤ ε := by dsimp [δ]; linarith
  obtain ⟨C₁, hC₁, hprime⟩ := cited.vonMangoldt hRH
  obtain ⟨C₂, hC₂, hstrip⟩ := cited.strip hRH η hη0
  let a : ℝ := NegativeDiscriminantSmoothing.constant η C₂ * 8 ^ η * Real.log 4
  let b : ℝ := CoefficientErrorMajorant.constant δ C₁ * ((4 / δ ^ 2) * 2 ^ δ *
    (1 + Real.Gamma (1 / 2 + δ + δ)))
  let d : ℝ := max 0 CoefficientTail.tailConstant
  let K : ℝ := 1 + OddPrimeAverageTrivial.constant η + a + b + logarithmConstant η + d
  have ha : 0 ≤ a := by
    have := smoothingConstant_nonneg (η := η) hC₂.le
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    have := CoefficientErrorMajorant.constant_nonneg hδ0 hC₁.le
    have := Real.Gamma_pos_of_pos (by linarith : 0 < 1 / 2 + δ + δ)
    dsimp [b]
    positivity
  have hd : 0 ≤ d := le_max_left _ _
  have hlog : 0 ≤ logarithmConstant η := by unfold logarithmConstant; positivity
  have htrivK := OddPrimeAverageTrivial.constant_nonneg hη0
  have hK : 0 < K := by dsimp [K]; linarith
  have haK : a + b + logarithmConstant η + d ≤ K := by dsimp [K]; linarith
  have htK : OddPrimeAverageTrivial.constant η ≤ K := by dsimp [K]; linarith
  refine ⟨2 * K, by positivity, ?_⟩
  intro H G t A B M Φ ht8 hA2 hAB hB ht hM hΦ hdΦ hI hMbound
  have hA : 0 ≤ A := by linarith
  let V : ℝ := ∫ u in A..B, ‖deriv Φ u‖
  let E : ℝ := ‖primeLsum G t A B Φ - valueAtOne t * ∫ u in A..B, Φ u‖
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hBp : 0 < B ^ ε := Real.rpow_pos_of_pos hB0 ε
  have htrivial : E ≤ (K * B ^ ε) * M * B := by
    have h := OddPrimeAverageTrivial.trivial_bound G t hA hAB hB1 ht hM hη0 Φ hMbound
    apply h.trans
    rw [Real.rpow_add hB0, Real.rpow_one]
    calc
      _ = OddPrimeAverageTrivial.constant η * B ^ η * M * B := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul htK
            (Real.rpow_le_rpow_of_exponent_le hB1 (by linarith : η ≤ ε))
            (by positivity) hK.le) hM) hB0.le
  by_cases hMzero : M = 0
  · subst M
    simpa [E] using htrivial
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
  have hsmooth : ∀ x : ℝ, 1 ≤ x → x ≤ Real.sqrt B →
      E ≤ (K * B ^ ε) * leading M V B x := by
    intro x hx hxB
    have hx0 : 0 < x := by linarith
    have hraw := raw_smoothing_bound G t ht8 hA hAB (by linarith) ht hM hx
      hη0 hη1 hδ0 hδ1 hC₁.le hC₂.le hprime hstrip Φ hΦ hdΦ hI hMbound
    have htail : CoefficientTail.tailConstant / Real.sqrt x * (M * B) ≤
        d / Real.sqrt x * (M * B) := by
      gcongr
      exact le_max_right _ _
    have hloss := raw_le_leading hM hV hB1 hx hxB hη0 hδ0.le hηε hδε ha hb hd
    have hraw' : E ≤ a * M * B ^ (1 + η) * x ^ (-1 / 2 + η) +
      b * (M + V) * Real.sqrt B * B ^ δ * x ^ (1 / 2 + δ + δ) +
      M * (Real.log (2 * x) ^ 2 + 1) + d / Real.sqrt x * (M * B) := by
      dsimp [a, b, E, V]
      linarith
    apply (hraw'.trans hloss).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right haK hBp.le) (leading_nonneg hM hV hB0.le)
  have hopt := Smoothing.optimize_smoothing M V B (K * B ^ ε) E hMpos hV hB1
    (mul_nonneg hK.le hBp.le) htrivial hsmooth
  have heq : 2 * (K * B ^ ε) * Real.sqrt (M * (M + V)) * B ^ (3 / 4 : ℝ) =
      (2 * K) * Real.sqrt M * Real.sqrt (M + V) * B ^ (3 / 4 + ε) := by
    rw [Real.sqrt_mul hM, Real.rpow_add hB0]
    ring
  rw [heq] at hopt
  exact hopt

/-- Equation (105) with the actual Euler-product constant G_t written out.
This is also the interface used in the odd-depth trace-index application. -/
theorem odd_weighted_prime_average_bound (hRH : PrimitiveDirichletRH)
    (cited : CitedGeneralTheorems) {ε : ℝ} (hε : 0 < ε) :
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
          B ^ (3 / 4 + ε) := by
  obtain ⟨C, hC, hb⟩ := prime_average_bound hRH cited hε
  refine ⟨C, hC, ?_⟩
  intro H G t A B M Φ ht8 hA hAB hB ht hM hΦ hdΦ hI hMbound
  have h := hb G t A B M Φ ht8 hA hAB hB ht hM hΦ hdΦ hI hMbound
  have he : primeLsum G t A B Φ =
      ∑ p ∈ PrimeAverageSmoothing.primeSet A B, (Real.log (p : ℝ) : ℂ) *
        (QuadraticDiscriminantL.LAtOne G (t ^ 2 - 8 * (p : ℤ)) * Φ p) := by
    unfold primeLsum
    apply Finset.sum_congr rfl
    intro p hp
    unfold primeWeight
    ring
  rw [he, OddSmoothedBounds.valueAtOne_eq_primeWeight] at h
  exact h

end DepthAspect.TheoremFiveSix
