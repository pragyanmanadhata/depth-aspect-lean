import DepthAspect.CoefficientErrorMajorant
import DepthAspect.GRHConsequences

/-! The literal coprime-restricted prime sum and bound printed in (98). -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace DepthAspect.RestrictedPrimeAverage
open QuadraticClassFormula QuadraticDiscriminantL GlobalResidueCoefficient GlobalResidueMean
open CharacterPrimeAverages CoefficientPrimeAverages NegativeResidueBridge
open FiniteCharacterFourier CoefficientErrorMajorant PrimitiveGRHTransport

/-- The actual restricted coefficient sum, before restoration of the bad primes. -/
def restrictedPsi {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) (m : ℕ) (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
    if p.Prime ∧ p.Coprime (2 * m) then
      Φ p * χ (-(p : ℤ)) * psi G (t ^ 2 - 4 * (p : ℤ)) m * (Real.log p : ℂ)
    else 0

 theorem prime_coprime_iff {p m : ℕ} (hp : p.Prime) :
    p.Coprime (2 * m) ↔ p ≠ 2 ∧ ¬p ∣ m := by
  rw [hp.coprime_iff_not_dvd, hp.dvd_mul, Nat.dvd_prime Nat.prime_two]
  simp [hp.ne_one]

/-- The zero extension used by Fourier expansion is exactly the literal
coprime-prime restriction, not a differently defined prime sequence. -/
theorem residueWeighted_eq_restrictedPsi {H : ℤ → ℝ} (G : GeneralFormula H)
    {m : ℕ} [NeZero m] (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {A B : ℝ} (hA : 0 ≤ A) (ht : (t : ℝ) ^ 2 ≤ 4 * A) (Φ : ℝ → ℂ) :
    residueWeighted (twistedFunction m t χ) A B Φ = restrictedPsi G t χ m A B Φ := by
  unfold residueWeighted restrictedPsi
  apply Finset.sum_congr rfl
  intro p hpI
  by_cases hp : p.Prime
  · by_cases hc : p.Coprime (2 * m)
    · obtain ⟨hp2, hpm⟩ := (prime_coprime_iff hp).mp hc
      rw [if_pos hp, if_pos ⟨hp, hc⟩,
        extend_twisted_good_prime G hp hp2 hpm t χ (discriminant_negative hA ht hpI)]
      ring
    · have hbad : p = 2 ∨ p ∣ m := by
        by_cases hp2 : p = 2
        · exact Or.inl hp2
        · exact Or.inr (by by_contra hpm; exact hc ((prime_coprime_iff hp).mpr ⟨hp2, hpm⟩))
      simp [hp, hc, extend_bad_prime hp hbad t χ]
  · simp [hp]

/-- Exact equation (98) up to its uniform numerical constant. Its beta is
the actual finite character-coefficient norm, with the exact modulus q_m. -/
theorem restricted_coefficient_error_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    {m : ℕ} [NeZero m] (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {A B M C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 2 ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hGRH : PrimitiveVonMangoldtEstimate C)
    (Φ : ℝ → ℂ) (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ x ∈ Set.Ioo A B, DifferentiableAt ℝ Φ x)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ x ∈ Set.Icc A B, ‖Φ x‖ ≤ M) :
    ‖restrictedPsi G t χ m A B Φ - average m t χ * ∫ u in A..B, Φ u‖ ≤
      (2 * envelopeConstant C) * (M + ∫ u in A..B, ‖deriv Φ u‖) *
        beta (twistedFunction m t χ) * Real.sqrt B * Real.log (2 * B * m) ^ 2 := by
  have hC' : 0 ≤ C + 3 / Real.log 4 := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have h := residueWeighted_error_GRH (q := modulus m) hA hAB hB hC'
    (all_characters_estimate (q := modulus m) hC hGRH) (twistedFunction m t χ) Φ hΦ hdΦ hI hM
  rw [residueWeighted_eq_restrictedPsi G t χ hA ht Φ] at h
  have hV : 0 ≤ ∫ u in A..B, ‖deriv Φ u‖ :=
    intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have henv := envelope_le (NeZero.pos m) hB hC
  have hβ := beta_nonneg (twistedFunction m t χ)
  have hK := envelopeConstant_nonneg hC
  calc
    _ ≤ (2 * M + ∫ u in A..B, ‖deriv Φ u‖) * beta (twistedFunction m t χ) *
        envelope (C + 3 / Real.log 4) B (modulus m) := h
    _ ≤ (2 * (M + ∫ u in A..B, ‖deriv Φ u‖)) * beta (twistedFunction m t χ) *
        (envelopeConstant C * Real.sqrt B * Real.log (2 * B * m) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by linarith) hβ
      · exact henv
      · unfold envelope
        positivity
      · positivity
    _ = _ := by ring

/-- The constant in (98) is fixed before all coefficient indices, trace
parameters, characters, intervals and weights. The supplied estimates are
obtained from the actual RH predicate through the cited general theorem. -/
theorem uniform_restricted_bound (hRH : DirichletRH.PrimitiveDirichletRH)
    (cited : GRHConsequences.CitedGeneralTheorems) :
    ∃ K : ℝ, 0 < K ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (m : ℕ) [NeZero m] (t : ℤ) (χ : DirichletCharacter ℂ 8) (A B M : ℝ) (Φ : ℝ → ℂ),
      0 ≤ A → A ≤ B → 2 ≤ B → (t : ℝ) ^ 2 ≤ 4 * A → 0 ≤ M →
      ContinuousOn Φ (Set.Icc A B) →
      (∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u) →
      IntegrableOn (deriv Φ) (Set.Icc A B) →
      (∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) →
      ‖restrictedPsi G t χ m A B Φ - average m t χ * ∫ u in A..B, Φ u‖ ≤
        K * (M + ∫ u in A..B, ‖deriv Φ u‖) * beta (twistedFunction m t χ) *
          Real.sqrt B * Real.log (2 * B * m) ^ 2 := by
  obtain ⟨C, hC, hprime⟩ := cited.vonMangoldt hRH
  have hK := envelopeConstant_nonneg hC.le
  refine ⟨1 + 2 * envelopeConstant C, by positivity, ?_⟩
  intro H G m hm t χ A B M Φ hA hAB hB ht hM hΦ hdΦ hI hMb
  have h := restricted_coefficient_error_bound G (m := m) t χ hA hAB hB ht hM hC.le hprime
    Φ hΦ hdΦ hI hMb
  have hV : 0 ≤ ∫ u in A..B, ‖deriv Φ u‖ :=
    intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have hβ := beta_nonneg (twistedFunction m t χ)
  apply h.trans
  gcongr
  linarith

end DepthAspect.RestrictedPrimeAverage
