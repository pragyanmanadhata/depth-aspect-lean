import DepthAspect.CoefficientPrimeAverages

/-! General finite-prime restoration algebra used for the odd-depth variant. -/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace DepthAspect.ResiduePrimeRestoration
open GlobalResidueCoefficient CharacterPrimeAverages CoefficientPrimeAverages

/-- An arbitrary scalar coefficient evaluated at the actual odd primes. -/
def weightedOdd (c : ℕ → ℂ) (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
    if p.Prime ∧ p ≠ 2 then Φ p * c p * (Real.log p : ℂ) else 0

 theorem extend_nonunit {m p : ℕ} [NeZero m] (hp : p.Prime)
    (hbad : p = 2 ∨ p ∣ m) (g : (ZMod (modulus m))ˣ → ℂ) :
    CharacterPrimeAverages.extend g (p : ZMod (modulus m)) = 0 := by
  have hn : ¬ IsUnit (p : ZMod (modulus m)) := by
    rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd]
    exact not_not.mpr ((NegativeResidueBridge.prime_dvd_modulus_iff m hp).mpr hbad)
  simp only [CharacterPrimeAverages.extend, dif_neg hn]

/-- Pure restoration algebra. Its coefficient identities and unit bound are
explicit premises, instantiated by the actual discriminant formulas below. -/
theorem restoration_bound {m : ℕ} [NeZero m]
    (g : (ZMod (modulus m))ˣ → ℂ) (c : ℕ → ℂ) {A B M : ℝ}
    (hA : 0 ≤ A) (hM0 : 0 ≤ M) (Φ : ℝ → ℂ)
    (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M)
    (hc : ∀ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, p.Prime → p ≠ 2 → ‖c p‖ ≤ 1)
    (hgood : ∀ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, p.Prime → p ≠ 2 → ¬p ∣ m →
      CharacterPrimeAverages.extend g (p : ZMod (modulus m)) = c p) :
    ‖weightedOdd c A B Φ - residueWeighted g A B Φ‖ ≤ M * OmittedPrimeCost.primeCost m := by
  rw [weightedOdd, residueWeighted, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
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
            extend_nonunit (m := m) Nat.prime_two (Or.inl rfl) g,
            mul_zero, zero_mul, sub_zero, norm_zero, if_pos hbad]
          exact mul_nonneg hM0 (Real.log_nonneg (by norm_num))
        · have hprime : p.Prime ∧ p ≠ 2 := ⟨hp, hp2⟩
          by_cases hpm : p ∣ m
          · have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
            have hbad : p.Prime ∧ p ∣ 2 * m := ⟨hp, dvd_mul_of_dvd_right hpm 2⟩
            rw [if_pos hprime, if_pos hp, extend_nonunit (m := m) hp (Or.inr hpm) g,
              mul_zero, zero_mul, sub_zero, if_pos hbad, norm_mul, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
            calc
              _ ≤ M * 1 * Real.log p := by
                gcongr
                · exact hM p (Set.Ioc_subset_Icc_self (prime_mem_interval hA hpS))
                · exact hc p hpS hp hp2
              _ = _ := by ring
          · have hnot : ¬ p ∣ 2 * m := by
              rw [hp.dvd_mul, Nat.dvd_prime Nat.prime_two]
              simp [hp.ne_one, hp2, hpm]
            have hbad : ¬ (p.Prime ∧ p ∣ 2 * m) := fun h => hnot h.2
            rw [if_pos hprime, if_pos hp, if_neg hbad, hgood p hpS hp hp2 hpm,
              sub_self, norm_zero]
      · simp [hp]
    _ = M * ∑ p ∈ (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun p => p.Prime ∧ p ∣ 2 * m),
        Real.log p := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hM0
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨_, hprime, hdvd⟩ := Finset.mem_filter.mp hp
        exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd, mul_ne_zero (by norm_num) (NeZero.ne m)⟩
      · intro p hp _
        exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)

/-- General Fourier/Abel consequence before a particular arithmetic function
is substituted. This is not itself a theorem about an unspecified L-value. -/
theorem coefficient_bound {m : ℕ} [NeZero m]
    (g : (ZMod (modulus m))ˣ → ℂ) (c : ℕ → ℂ) {A B M C : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 2 ≤ B) (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hGRH : PrimitiveGRHTransport.PrimitiveVonMangoldtEstimate C)
    (Φ : ℝ → ℂ) (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M)
    (hc : ∀ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, p.Prime → p ≠ 2 → ‖c p‖ ≤ 1)
    (hgood : ∀ p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, p.Prime → p ≠ 2 → ¬p ∣ m →
      CharacterPrimeAverages.extend g (p : ZMod (modulus m)) = c p) :
    ‖weightedOdd c A B Φ - FiniteCharacterFourier.coefficient g 1 * ∫ u in A..B, Φ u‖ ≤
      (2 * M + ∫ u in A..B, ‖deriv Φ u‖) * FiniteCharacterFourier.beta g *
        envelope (C + 3 / Real.log 4) B (modulus m) + M * OmittedPrimeCost.primeCost m := by
  have hC' : 0 ≤ C + 3 / Real.log 4 := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  have hmain := residueWeighted_error_GRH (q := modulus m) hA hAB hB hC'
    (PrimitiveGRHTransport.all_characters_estimate (q := modulus m) hC hGRH) g Φ hΦ hdΦ hI hM
  have hrestore := restoration_bound (m := m) g c hA hM0 Φ hM hc hgood
  exact (norm_sub_le_norm_sub_add_norm_sub (weightedOdd c A B Φ)
    (residueWeighted g A B Φ)
    (FiniteCharacterFourier.coefficient g 1 * ∫ u in A..B, Φ u)).trans (by linarith)

end DepthAspect.ResiduePrimeRestoration
