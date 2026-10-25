import DepthAspect.TheoremFiveFive

/-!
# An all-prime strengthening of (104)

Section 1.3 of the paper defines P to be an odd prime, so (104) itself has
no prime-two contribution. This optional strengthening admits all primes and
uses the primitive trivial twist, which takes value one at two. The single
additional term is bounded internally. This is not a correction to the paper;
no new analytic estimate is assumed, and the constant remains uniform in t.
-/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace DepthAspect.TheoremFiveFiveAllPrimes
open DirichletRH GRHConsequences QuadraticClassFormula QuadraticDiscriminantL
open PrimeAverageSmoothing GlobalCoefficientTail CoefficientPrimeAverages

/-- The primitive trivial twist is one at every integer. The three nontrivial
quadratic twists retain their ordinary zero value at the prime two. -/
def primitiveTwist (χ : DirichletCharacter ℂ 8) (p : ℕ) : ℂ :=
  if χ = 1 then 1 else χ (-(p : ℤ))

theorem primitiveTwist_eq_on_odd_prime (χ : DirichletCharacter ℂ 8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    primitiveTwist χ p = χ (-(p : ℤ)) := by
  by_cases hχ : χ = 1
  · subst χ
    have hc : p.Coprime 8 := hp.coprime_iff_not_dvd.mpr (by
      intro h
      have hpdiv : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by norm_num; exact h)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpdiv))
    have hu : IsUnit (p : ZMod 8) := by
      simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime p hc).isUnit
    have hun : IsUnit ((-(p : ℤ)) : ZMod 8) := by
      simpa only [Int.cast_neg, Int.cast_natCast] using hu.neg
    rw [primitiveTwist, if_pos rfl, MulChar.one_apply hun]
  · simp only [primitiveTwist, if_neg hχ]

theorem norm_primitiveTwist_two_le (χ : DirichletCharacter ℂ 8) :
    ‖primitiveTwist χ 2‖ ≤ 1 := by
  unfold primitiveTwist
  split_ifs
  · norm_num
  · exact χ.norm_le_one _

def allPrimeLsum {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ p ∈ (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime,
    Φ p * primitiveTwist χ p * LAtOne G (t ^ 2 - 4 * (p : ℤ)) * (Real.log p : ℂ)

private theorem sum_difference_at_two (s : Finset ℕ) (f g : ℕ → ℂ)
    (heq : ∀ p ∈ s, p ≠ 2 → f p = g p) (hg : g 2 = 0) :
    (∑ p ∈ s, f p) - ∑ p ∈ s, g p = if 2 ∈ s then f 2 else 0 := by
  rw [← Finset.sum_sub_distrib]
  by_cases h2 : 2 ∈ s
  · rw [if_pos h2, Finset.sum_eq_single_of_mem 2 h2
      (fun p hp hp2 => by rw [heq p hp hp2, sub_self]), hg, sub_zero]
  · rw [if_neg h2]
    apply Finset.sum_eq_zero
    intro p hp
    rw [heq p hp (fun he => h2 (he ▸ hp)), sub_self]

/-- The convention change adds exactly the two-term when that prime lies in
the interval, and adds nothing for each nonprincipal twist. -/
theorem allPrimeLsum_sub_modEight {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) (A B : ℝ) (Φ : ℝ → ℂ) :
    allPrimeLsum G t χ A B Φ - primeLsum G t χ A B Φ =
      if 2 ∈ (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime then
        Φ 2 * primitiveTwist χ 2 * LAtOne G (t ^ 2 - 8) * (Real.log 2 : ℂ)
      else 0 := by
  rw [primeLsum_eq_all_primes, allPrimeLsum]
  apply sum_difference_at_two
  · intro p hp hp2
    rw [primitiveTwist_eq_on_odd_prime χ (Finset.mem_filter.mp hp).2 hp2]
  · rw [show χ (-((2 : ℕ) : ℤ)) = 0 from character_neg_two χ]
    simp only [mul_zero, zero_mul]

/-- If two is counted then 0<|t²−8|≤8, so the proved δ=1 L-value estimate
bounds it by 24. This avoids assuming any special quadratic L-value. -/
theorem allPrimeLsum_difference_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (t : ℤ) (χ : DirichletCharacter ℂ 8) {A B M : ℝ}
    (hA : 0 ≤ A) (ht : (t : ℝ) ^ 2 ≤ 4 * A) (hM : 0 ≤ M)
    (Φ : ℝ → ℂ) (hΦ : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    ‖allPrimeLsum G t χ A B Φ - primeLsum G t χ A B Φ‖ ≤
      (24 * Real.log 2) * M := by
  rw [allPrimeLsum_sub_modEight]
  split_ifs with h2
  · have h2I := (Finset.mem_filter.mp h2).1
    have hD : IsNegativeDiscriminant (t ^ 2 - 8) := by
      simpa only [Nat.cast_ofNat, show (4 : ℤ) * (2 : ℤ) = 8 by norm_num] using
        discriminant_negative hA ht h2I
    have habs : ((t ^ 2 - 8).natAbs : ℝ) ≤ 8 := by
      have hi : ((t ^ 2 - 8).natAbs : ℤ) = -(t ^ 2 - 8) := by
        rw [Int.natCast_natAbs, abs_of_neg hD.1]
      have hr : ((t ^ 2 - 8).natAbs : ℝ) = -((t ^ 2 - 8 : ℤ) : ℝ) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using
          congrArg (fun z : ℤ => (z : ℝ)) hi
      rw [hr]
      push_cast
      nlinarith [sq_nonneg (t : ℝ)]
    have hL : ‖LAtOne G (t ^ 2 - 8)‖ ≤ 24 := by
      have h := PrimeAverageTrivial.LAtOne_power_bound G _ hD (δ := 1) (by norm_num)
      norm_num only [inv_one, Real.rpow_one] at h
      nlinarith
    have hPhi : ‖Φ 2‖ ≤ M := hΦ 2
      ⟨(prime_mem_interval hA h2I).1.le, (prime_mem_interval hA h2I).2⟩
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    calc
      _ ≤ M * 1 * 24 * Real.log 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul
            (mul_le_mul hPhi (norm_primitiveTwist_two_le χ) (norm_nonneg _) hM)
            hL (norm_nonneg _) (by positivity)) hlog
      _ = _ := by ring
  · simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hM

/-- A stronger standalone variant of (104) allowing every prime and the
primitive trivial twist. The added prime two changes only the uniform constant;
the original paper already restricts P to odd primes. -/
theorem prime_average_bound (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (t : ℤ) (χ : DirichletCharacter ℂ 8) (A B M : ℝ) (Φ : ℝ → ℂ),
      0 ≤ A → A ≤ B → 3 ≤ B → (t : ℝ) ^ 2 ≤ 4 * A → 0 ≤ M →
      ContinuousOn Φ (Set.Icc A B) →
      (∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u) →
      IntegrableOn (deriv Φ) (Set.Icc A B) →
      (∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) →
      ‖allPrimeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u‖ ≤
        Cε * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
          B ^ (3 / 4 + ε) := by
  obtain ⟨C, hC, hb⟩ := TheoremFiveFive.prime_average_bound hRH cited hε
  have hE : 0 ≤ 24 * Real.log 2 := mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  refine ⟨C + 24 * Real.log 2, by linarith, ?_⟩
  intro H G t χ A B M Φ hA hAB hB ht hM hΦ hdΦ hI hMbound
  let V : ℝ := ∫ u in A..B, ‖deriv Φ u‖
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have hroot : M ≤ Real.sqrt M * Real.sqrt (M + V) := by
    calc
      M = Real.sqrt M * Real.sqrt M := (Real.mul_self_sqrt hM).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
  have hp : 1 ≤ B ^ (3 / 4 + ε) := Real.one_le_rpow (by linarith) (by linarith)
  have hscale : M ≤ Real.sqrt M * Real.sqrt (M + V) * B ^ (3 / 4 + ε) :=
    hroot.trans (le_mul_of_one_le_right (by positivity) hp)
  have hold := hb G t χ A B M Φ hA hAB hB ht hM hΦ hdΦ hI hMbound
  have hextra := allPrimeLsum_difference_bound G t χ hA ht hM Φ hMbound
  have heq : allPrimeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u =
      (allPrimeLsum G t χ A B Φ - primeLsum G t χ A B Φ) +
        (primeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u) := by ring
  rw [heq]
  apply (norm_add_le _ _).trans
  apply (add_le_add hextra hold).trans
  have he := mul_le_mul_of_nonneg_left hscale hE
  dsimp [V] at he
  calc
    _ ≤ (24 * Real.log 2) * (Real.sqrt M *
          Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) * B ^ (3 / 4 + ε)) +
        C * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
          B ^ (3 / 4 + ε) := add_le_add he (le_refl _)
    _ = _ := by ring

end DepthAspect.TheoremFiveFiveAllPrimes
