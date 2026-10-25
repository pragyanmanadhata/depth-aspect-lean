import DepthAspect.NegativeResidueBridge
import DepthAspect.PrimitiveGRHTransport
import DepthAspect.OmittedPrimeCost
import DepthAspect.GlobalFourierBound

/-!
# The actual coefficient-wise prime discrepancy used in (103)

The sum below contains the literal negative-discriminant ψ, with the odd-prime
restriction in the paper. Its residue-class expansion is used only at unit
primes. Restoring the omitted primes is proved from the actual prime divisors
of 2m, rather than supplied as a bound. The Fourier norm and local mean are
also the previously constructed functions.
-/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace DepthAspect.CoefficientPrimeAverages
open QuadraticClassFormula QuadraticDiscriminantL GlobalResidueCoefficient
open GlobalResidueMean CharacterPrimeAverages NegativeResidueBridge

/-- The coefficient-m prime sum before exponential smoothing. -/
def weightedPsi {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) (m : ℕ) (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
    if p.Prime ∧ p ≠ 2 then
      Φ p * χ (-(p : ℤ)) * psi G (t ^ 2 - 4 * (p : ℤ)) m * (Real.log p : ℂ)
    else 0

 theorem norm_psi_le {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ) (m : ℕ) :
    ‖psi G D m‖ ≤ 1 := by
  unfold psi
  split_ifs
  · exact ImprimitiveCharacter.psiNat_norm_le_one _ _ _
  · norm_num

 theorem prime_mem_interval {A B : ℝ} (hA : 0 ≤ A) {p : ℕ}
    (hp : p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊) : (p : ℝ) ∈ Set.Ioc A B := by
  obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hp
  have ha' : A < p := (Nat.floor_lt hA).mp ha
  have hb' : (p : ℝ) ≤ B := (Nat.le_floor_iff' (by omega : p ≠ 0)).mp hb
  exact ⟨ha', hb'⟩

 theorem discriminant_negative {t : ℤ} {A B : ℝ} (hA : 0 ≤ A)
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) {p : ℕ}
    (hp : p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊) :
    IsNegativeDiscriminant (t ^ 2 - 4 * (p : ℤ)) := by
  have hlt : (t : ℝ) ^ 2 < 4 * p := by
    have := (prime_mem_interval hA hp).1
    nlinarith
  exact elliptic_isNegativeDiscriminant t p (by exact_mod_cast hlt)

 theorem extend_bad_prime {m p : ℕ} [NeZero m] (hp : p.Prime)
    (hbad : p = 2 ∨ p ∣ m) (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    CharacterPrimeAverages.extend (twistedFunction m t χ) (p : ZMod (modulus m)) = 0 := by
  have hn : ¬ IsUnit (p : ZMod (modulus m)) := by
    rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd]
    exact not_not.mpr ((prime_dvd_modulus_iff m hp).mpr hbad)
  simp only [CharacterPrimeAverages.extend, dif_neg hn]

/-- Exact restoration of all removed unit-prime restrictions costs the
literal prime-factor sum in (99), with no arithmetic cancellation assumed. -/
theorem restored_difference_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    {m : ℕ} [NeZero m] (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {A B M : ℝ} (hA : 0 ≤ A) (ht : (t : ℝ) ^ 2 ≤ 4 * A)
    (hM0 : 0 ≤ M) (Φ : ℝ → ℂ)
    (hM : ∀ x ∈ Set.Icc A B, ‖Φ x‖ ≤ M) :
    ‖weightedPsi G t χ m A B Φ - residueWeighted (twistedFunction m t χ) A B Φ‖ ≤
      M * OmittedPrimeCost.primeCost m := by
  rw [weightedPsi, residueWeighted, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
      ‖(if p.Prime ∧ p ≠ 2 then
        Φ p * χ (-(p : ℤ)) * psi G (t ^ 2 - 4 * (p : ℤ)) m * (Real.log p : ℂ)
        else 0) -
      (if p.Prime then Φ p * CharacterPrimeAverages.extend (twistedFunction m t χ)
        (p : ZMod (modulus m)) * (Real.log p : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
        if p.Prime ∧ p ∣ 2 * m then M * Real.log p else 0 := by
      apply Finset.sum_le_sum
      intro p hpS
      by_cases hp : p.Prime
      · by_cases hp2 : p = 2
        · subst p
          have htwo : ¬ ((2 : ℕ).Prime ∧ (2 : ℕ) ≠ 2) := fun h => h.2 rfl
          have hbad : (2 : ℕ).Prime ∧ 2 ∣ 2 * m := ⟨Nat.prime_two, ⟨m, rfl⟩⟩
          rw [if_neg htwo, if_pos hp,
            extend_bad_prime (m := m) Nat.prime_two (Or.inl rfl) t χ,
            mul_zero, zero_mul, sub_zero, norm_zero, if_pos hbad]
          exact mul_nonneg hM0 (Real.log_nonneg (by norm_num))
        · have hprime : p.Prime ∧ p ≠ 2 := ⟨hp, hp2⟩
          by_cases hpm : p ∣ m
          · have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
            have hbad : p.Prime ∧ p ∣ 2 * m := ⟨hp, dvd_mul_of_dvd_right hpm 2⟩
            rw [if_pos hprime, if_pos hp,
              extend_bad_prime (m := m) hp (Or.inr hpm) t χ,
              mul_zero, zero_mul, sub_zero, if_pos hbad, norm_mul, norm_mul, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
            have hΦp := hM p (Set.Ioc_subset_Icc_self (prime_mem_interval hA hpS))
            have hχ := χ.norm_le_one (-(p : ℤ))
            have hψ := norm_psi_le G (t ^ 2 - 4 * p) m
            calc
              _ ≤ M * 1 * 1 * Real.log p := by gcongr
              _ = _ := by ring
          · have hgood := extend_twisted_good_prime G hp hp2 hpm t χ
              (discriminant_negative hA ht hpS)
            have hnot : ¬p ∣ 2 * m := by
              rw [hp.dvd_mul, Nat.dvd_prime Nat.prime_two]
              simp [hp.ne_one, hp2, hpm]
            have hbad : ¬ (p.Prime ∧ p ∣ 2 * m) := fun h => hnot h.2
            rw [if_pos hprime, if_pos hp, if_neg hbad, hgood]
            ring_nf <;> norm_num
      · simp [hp]
    _ = M * ∑ p ∈ (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun p => p.Prime ∧ p ∣ 2 * m),
        Real.log p := by rw [Finset.sum_filter, Finset.mul_sum]; congr 1; funext p; split_ifs <;> simp
    _ ≤ M * OmittedPrimeCost.primeCost m := by
      apply mul_le_mul_of_nonneg_left _ hM0
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨_, hprime, hdvd⟩ := Finset.mem_filter.mp hp
        exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, mul_ne_zero (by norm_num) (NeZero.ne m)⟩
      · intro p hp _
        exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)

/-- The literal coefficient-wise version of (98), now including the omitted
primes. Its only analytic input is the cited primitive character estimate. -/
theorem coefficient_error_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    {m : ℕ} [NeZero m] (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {A B M C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 2 ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hGRH : PrimitiveGRHTransport.PrimitiveVonMangoldtEstimate C)
    (Φ : ℝ → ℂ) (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ x ∈ Set.Ioo A B, DifferentiableAt ℝ Φ x)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ x ∈ Set.Icc A B, ‖Φ x‖ ≤ M) :
    ‖weightedPsi G t χ m A B Φ - average m t χ * ∫ u in A..B, Φ u‖ ≤
      (2 * M + ∫ u in A..B, ‖deriv Φ u‖) * GlobalFourierBound.localProduct m *
        envelope (C + 3 / Real.log 4) B (modulus m) + M * OmittedPrimeCost.primeCost m := by
  have hg := PrimitiveGRHTransport.all_characters_estimate (q := modulus m) hC hGRH
  have hC' : 0 ≤ C + 3 / Real.log 4 := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have hmain := residueWeighted_error_GRH (q := modulus m) hA hAB hB hC' hg
    (twistedFunction m t χ) Φ hΦ hdΦ hI hM
  have hβ := beta_twistedFunction (NeZero.ne m) t χ
  have hV : 0 ≤ ∫ u in A..B, ‖deriv Φ u‖ :=
    intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have hE : 0 ≤ envelope (C + 3 / Real.log 4) B (modulus m) := by
    unfold envelope
    positivity
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hβ (by linarith : 0 ≤ 2 * M + ∫ u in A..B, ‖deriv Φ u‖)) hE
  have hrestore := restored_difference_bound G (m := m) t χ hA ht hM0 Φ hM
  calc
    _ ≤ ‖weightedPsi G t χ m A B Φ - residueWeighted (twistedFunction m t χ) A B Φ‖ +
        ‖residueWeighted (twistedFunction m t χ) A B Φ -
          average m t χ * ∫ u in A..B, Φ u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      unfold GlobalResidueMean.average at *
      linarith

end DepthAspect.CoefficientPrimeAverages
