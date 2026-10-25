import DepthAspect.UnsignedRemainder
import DepthAspect.ExplicitFormula

/-!
# Literal signed finite-family density

The weights below are the actual root signs when this module is instantiated
with `SignedArithmeticData`. The finite prime box is the same padded box as
in the unsigned theorem, so arbitrarily small positive Fourier support is
covered. The named pointwise explicit-formula input in the algebraic lemma
is discharged by the general Shin--Templier interface in its final wrapper.
-/
namespace DepthAspect.SignedDensity

open SpectralFamily UnsignedDensity
open scoped BigOperators FourierTransform SchwartzMap

noncomputable def signedMeanDensity {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (ε : ι → ℂ) (s L : ℝ) (φ : 𝓢(ℝ, ℂ)) (γ : ∀ f, κ f → ℂ) : ℂ :=
  average (fun f => ε f * ExplicitFormula.density s L φ (γ f))

noncomputable def signedHeckeAverage {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (a : ι → ℕ → ℂ) (m : ℕ) : ℂ :=
  average (fun f => ε f * a f m)

noncomputable def signedPowerCoefficient {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (α β : ι → ℕ → ℂ) (p j : ℕ) : ℂ :=
  average (fun f => ε f * SatakeCoefficients.powerCoefficient (α f p) (β f p) j)

noncomputable def signedPrimePowerTerm {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (L : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) (pj : ℕ × ℕ) : ℂ :=
  if pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2 then
    (Real.log (pj.1 : ℝ) : ℂ) / (((pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2) : ℝ) : ℂ) *
      signedPowerCoefficient ε α β pj.1 pj.2 * h ((pj.2 : ℝ) * Real.log (pj.1 : ℝ) / L)
  else 0

theorem average_signedPrimePowerTerm {ι : Type*} [Fintype ι] [Nonempty ι]
    (ε : ι → ℂ) (L : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) (pj : ℕ × ℕ) :
    average (fun f => ε f * PrimePowerSupport.primePowerTerm L h
      (ExplicitFormula.primePowerWeight (α f) (β f)) pj) =
        signedPrimePowerTerm ε L h α β pj := by
  by_cases hc : pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2
  · simp only [PrimePowerSupport.primePowerTerm, signedPrimePowerTerm, if_pos hc,
      ExplicitFormula.primePowerWeight]
    have heq (f : ι) : ε f * ((Real.log (pj.1 : ℝ) : ℂ) /
        (((pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2) : ℝ) : ℂ) *
          SatakeCoefficients.powerCoefficient (α f pj.1) (β f pj.1) pj.2 *
            h ((pj.2 : ℝ) * Real.log (pj.1 : ℝ) / L)) =
      ((Real.log (pj.1 : ℝ) : ℂ) / (((pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2) : ℝ) : ℂ) *
        (ε f * SatakeCoefficients.powerCoefficient (α f pj.1) (β f pj.1) pj.2)) *
          h ((pj.2 : ℝ) * Real.log (pj.1 : ℝ) / L) := by ring
    simp_rw [heq]
    rw [average_mul_right, average_mul_left]
    rfl
  · simp only [PrimePowerSupport.primePowerTerm, signedPrimePowerTerm, if_neg hc,
      mul_zero, SpectralFamily.average_const]

theorem signedPowerCoefficient_one {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (p : ℕ)
    (hfirst : ∀ f, α f p + β f p = a f p) :
    signedPowerCoefficient ε α β p 1 = signedHeckeAverage ε a p := by
  unfold signedPowerCoefficient signedHeckeAverage
  simp_rw [SatakeCoefficients.powerCoefficient_one, hfirst]

/-- In the signed square term the subtracted constant is the literal mean
root number, rather than one. -/
theorem signedPowerCoefficient_two {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (p : ℕ)
    (hprod : ∀ f, α f p * β f p = 1)
    (hsquare : ∀ f, tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2)) :
    signedPowerCoefficient ε α β p 2 = signedHeckeAverage ε a (p ^ 2) - average ε := by
  unfold signedPowerCoefficient signedHeckeAverage
  simp_rw [SatakeCoefficients.powerCoefficient_two _ _ (hprod _), hsquare, mul_sub, mul_one]
  exact average_sub _ _

noncomputable def signedPrimeContribution {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p : ℝ) / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
    signedHeckeAverage ε a p * h (Real.log (p : ℝ) / L)

noncomputable def signedSquareContribution {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
    (signedHeckeAverage ε a (p ^ 2) - average ε) * h (2 * Real.log (p : ℝ) / L)

noncomputable def signedHigherContribution {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (L s : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) : ℂ :=
  ∑ pj ∈ primeBases L s ×ˢ Finset.Icc 3 (powerCap L s),
    signedPrimePowerTerm ε L h α β pj

theorem signed_primeBox_split {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (L s : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ)
    (hfirst : ∀ p ∈ primeBases L s, ∀ f, α f p + β f p = a f p)
    (hprod : ∀ p ∈ primeBases L s, ∀ f, α f p * β f p = 1)
    (hsquare : ∀ p ∈ primeBases L s, ∀ f,
      tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2)) :
    (∑ pj ∈ primeBox L s, signedPrimePowerTerm ε L h α β pj) =
      signedPrimeContribution ε L h a (primeBases L s) +
        signedSquareContribution ε L h a (primeBases L s) +
          signedHigherContribution ε L s h α β := by
  rw [primeBox, finite_box_split (primeBases L s) (powerCap L s) (le_max_left _ _)]
  congr 2
  · apply Finset.sum_congr rfl
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    dsimp only [signedPrimePowerTerm]
    rw [if_pos (show p.Prime ∧ p ≠ 2 ∧ 1 ≤ (1 : ℕ) from ⟨hc.1, hc.2, by decide⟩)]
    simp only [Nat.cast_one, one_mul]
    rw [signedPowerCoefficient_one ε α β a p (hfirst p hp)]
    simp only [← Real.sqrt_eq_rpow, Complex.ofReal_div]
  · apply Finset.sum_congr rfl
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    dsimp only [signedPrimePowerTerm]
    rw [if_pos (show p.Prime ∧ p ≠ 2 ∧ 1 ≤ (2 : ℕ) from ⟨hc.1, hc.2, by decide⟩)]
    simp only [Nat.cast_ofNat]
    rw [signedPowerCoefficient_two ε α β a p (hprod p hp) (hsquare p hp)]
    norm_num [Complex.ofReal_div]

/-- The literal signed finite-family identity, including the contribution
of the mean root sign multiplying the archimedean term. -/
theorem signed_low_power_formula {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : ι → Type*} {L s : ℝ} (hL : 0 < L) (ε : ι → ℂ) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (γ : ∀ f, κ f → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (A : ℂ)
    (hfirst : ∀ p ∈ primeBases L s, ∀ f, α f p + β f p = a f p)
    (hprod : ∀ p ∈ primeBases L s, ∀ f, α f p * β f p = 1)
    (hsquare : ∀ p ∈ primeBases L s, ∀ f,
      tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2))
    (h56 : ∀ f, ExplicitFormula.density s L φ (γ f) =
      A - ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (α f) (β f)) :
    signedMeanDensity ε s L φ γ = average ε * A -
      ((2 / L : ℝ) : ℂ) * signedPrimeContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * signedSquareContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * signedHigherContribution ε L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β := by
  have hsum : average (fun f => ε f * ExplicitFormula.primePowerSum L φ (α f) (β f)) =
      ∑ pj ∈ primeBox L s, signedPrimePowerTerm ε L (𝓕 φ : 𝓢(ℝ, ℂ)) α β pj := by
    simp_rw [primePowerSum_eq_primeBox hL φ hsupp, Finset.mul_sum]
    rw [average_finset_sum]
    apply Finset.sum_congr rfl
    intro pj _
    exact average_signedPrimePowerTerm ε L _ α β pj
  unfold signedMeanDensity
  simp_rw [h56, mul_sub]
  have hmul (f : ι) : ε f * (((2 / L : ℝ) : ℂ) *
      ExplicitFormula.primePowerSum L φ (α f) (β f)) =
      ((2 / L : ℝ) : ℂ) * (ε f * ExplicitFormula.primePowerSum L φ (α f) (β f)) := by ring
  simp_rw [hmul]
  rw [average_sub, average_mul_right, average_mul_left, hsum,
    signed_primeBox_split ε L s _ α β a hfirst hprod hsquare]
  ring

/-- The tail estimate (117) for the actual signed finite box. Only the
standard unit Satake norms and unit root-sign norm are required. -/
theorem signedHigherContribution_norm_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (ε : ι → ℂ) (hε : ∀ f, ‖ε f‖ ≤ 1)
    (L s : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ)
    (hα : ∀ p ∈ primeBases L s, ∀ f, ‖α f p‖ = 1)
    (hβ : ∀ p ∈ primeBases L s, ∀ f, ‖β f p‖ = 1)
    (H : ℝ) (hH : 0 ≤ H) (hh : ∀ x, ‖h x‖ ≤ H) :
    ‖signedHigherContribution ε L s h α β‖ ≤ 96 * H := by
  let S := primeBases L s ×ˢ Finset.Icc 3 (powerCap L s)
  have hS : ∀ pj ∈ S, pj.1.Prime ∧ 3 ≤ pj.1 ∧ 3 ≤ pj.2 := by
    intro pj hpj
    obtain ⟨hp, hj⟩ := Finset.mem_product.mp hpj
    have hc := (Finset.mem_filter.mp hp).2
    have hp2 := hc.1.two_le
    exact ⟨hc.1, by omega, (Finset.mem_Icc.mp hj).1⟩
  have ha : ∀ pj ∈ S, ‖signedPowerCoefficient ε α β pj.1 pj.2‖ ≤ 2 := by
    intro pj hpj
    apply norm_average_le
    intro f
    have hp := (Finset.mem_product.mp hpj).1
    rw [norm_mul]
    exact (mul_le_mul (hε f)
      (SatakeCoefficients.norm_powerCoefficient_le_two _ _ (hα _ hp f) (hβ _ hp f) _)
      (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have hb := FinitePrimePowerTail.finite_primePowerTerm_tail_bound S hS
    (signedPowerCoefficient ε α β) ha h H hH hh L
  simpa only [signedHigherContribution, signedPrimePowerTerm,
    PrimePowerSupport.primePowerTerm] using hb

/-- Combine the three separately proved signed estimates. The arithmetic
prime and square errors are explicit intermediate inputs, and are discharged
by the final spectral theorem. -/
theorem signed_density_error_of_terms {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : ι → Type*} {L s EA EP EQ H : ℝ} (hL : 0 < L) (hH : 0 ≤ H)
    (ε : ι → ℂ) (hε : ∀ f, ‖ε f‖ ≤ 1) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (γ : ∀ f, κ f → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (A I : ℂ)
    (hfirst : ∀ p ∈ primeBases L s, ∀ f, α f p + β f p = a f p)
    (hprod : ∀ p ∈ primeBases L s, ∀ f, α f p * β f p = 1)
    (hsquare : ∀ p ∈ primeBases L s, ∀ f,
      tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2))
    (hα : ∀ p ∈ primeBases L s, ∀ f, ‖α f p‖ = 1)
    (hβ : ∀ p ∈ primeBases L s, ∀ f, ‖β f p‖ = 1)
    (hh : ∀ x, ‖(𝓕 φ : 𝓢(ℝ, ℂ)) x‖ ≤ H)
    (hArch : ‖average ε * A‖ ≤ EA)
    (hPrime : ‖((2 / L : ℝ) : ℂ) *
      signedPrimeContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) - I‖ ≤ EP)
    (hSquare : ‖((2 / L : ℝ) : ℂ) *
      signedSquareContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s)‖ ≤ EQ)
    (h56 : ∀ f, ExplicitFormula.density s L φ (γ f) =
      A - ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (α f) (β f)) :
    ‖signedMeanDensity ε s L φ γ + I‖ ≤ EA + EP + EQ + 192 * H / L := by
  have hid := signed_low_power_formula hL ε φ hsupp γ α β a A hfirst hprod hsquare h56
  have ht := signedHigherContribution_norm_bound ε hε L s (𝓕 φ : 𝓢(ℝ, ℂ))
    α β hα hβ H hH hh
  have htail : ‖((2 / L : ℝ) : ℂ) *
      signedHigherContribution ε L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β‖ ≤ 192 * H / L := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
    calc
      _ ≤ (2 / L) * (96 * H) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  rw [hid]
  have heq : average ε * A - ((2 / L : ℝ) : ℂ) *
      signedPrimeContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * signedSquareContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * signedHigherContribution ε L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β + I =
      (average ε * A - (((2 / L : ℝ) : ℂ) *
        signedPrimeContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) - I) -
        ((2 / L : ℝ) : ℂ) * signedSquareContribution ε L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s)) -
        ((2 / L : ℝ) : ℂ) * signedHigherContribution ε L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add hArch hPrime)) hSquare)) htail)

end DepthAspect.SignedDensity
