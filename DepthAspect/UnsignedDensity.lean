import DepthAspect.ExplicitFormulaModel
import DepthAspect.SpectralFamily

/-!
# Literal finite-family assembly of the unsigned density

`h56` below is a named intermediate input supplied by the specialization of
the general explicit formula. It is not classified as an external assumption.
The averaged quantity is the actual finite average of the actual zero sums.
-/
namespace DepthAspect.UnsignedDensity

open SpectralFamily
open scoped BigOperators FourierTransform SchwartzMap

noncomputable def meanDensity {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (s L : ℝ) (φ : 𝓢(ℝ, ℂ)) (γ : ∀ f, κ f → ℂ) : ℂ :=
  average (fun f => ExplicitFormula.density s L φ (γ f))

noncomputable def meanPowerCoefficient {ι : Type*} [Fintype ι]
    (α β : ι → ℕ → ℂ) (p j : ℕ) : ℂ :=
  average (fun f => SatakeCoefficients.powerCoefficient (α f p) (β f p) j)

noncomputable def meanPrimePowerTerm {ι : Type*} [Fintype ι]
    (L : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) (pj : ℕ × ℕ) : ℂ :=
  if pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2 then
    (Real.log (pj.1 : ℝ) : ℂ) / (((pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2) : ℝ) : ℂ) *
      meanPowerCoefficient α β pj.1 pj.2 * h ((pj.2 : ℝ) * Real.log (pj.1 : ℝ) / L)
  else 0

/-- The actual finite average commutes with each local summand. -/
theorem average_primePowerTerm {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) (pj : ℕ × ℕ) :
    average (fun f => PrimePowerSupport.primePowerTerm L h
      (ExplicitFormula.primePowerWeight (α f) (β f)) pj) =
        meanPrimePowerTerm L h α β pj := by
  by_cases hc : pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2
  · simp only [PrimePowerSupport.primePowerTerm, meanPrimePowerTerm, if_pos hc,
      ExplicitFormula.primePowerWeight]
    rw [average_mul_right, average_mul_left]
    rfl
  · simp only [PrimePowerSupport.primePowerTerm, meanPrimePowerTerm, if_neg hc,
      average_const]

/-- Averaging (56) over the literal finite family, with an actual finite
prime-power sum constructed from the Fourier support. -/
theorem averaged_explicit_formula {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : ι → Type*} {L s : ℝ} (hL : 0 < L) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (γ : ∀ f, κ f → ℂ) (α β : ι → ℕ → ℂ) (A : ℂ)
    (h56 : ∀ f, ExplicitFormula.density s L φ (γ f) =
      A - ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (α f) (β f)) :
    meanDensity s L φ γ = A - ((2 / L : ℝ) : ℂ) *
      ∑ pj ∈ PrimePowerSupport.indexBox L s,
        meanPrimePowerTerm L (𝓕 φ : 𝓢(ℝ, ℂ)) α β pj := by
  have hsum : average (fun f => ExplicitFormula.primePowerSum L φ (α f) (β f)) =
      ∑ pj ∈ PrimePowerSupport.indexBox L s,
        meanPrimePowerTerm L (𝓕 φ : 𝓢(ℝ, ℂ)) α β pj := by
    simp_rw [ExplicitFormula.primePowerSum_eq_finite hL φ hsupp]
    rw [average_finset_sum]
    apply Finset.sum_congr rfl
    intro pj _
    exact average_primePowerTerm L _ α β pj
  unfold meanDensity
  simp_rw [h56]
  rw [average_sub, average_const, average_mul_left, hsum]

/-- The degree-one coefficient is the literal Hecke average. -/
theorem meanPowerCoefficient_one {ι : Type*} [Fintype ι]
    (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (p : ℕ)
    (hfirst : ∀ f, α f p + β f p = a f p) :
    meanPowerCoefficient α β p 1 = heckeAverage a p := by
  unfold meanPowerCoefficient heckeAverage
  simp_rw [SatakeCoefficients.powerCoefficient_one, hfirst]

/-- The degree-two average has the exact `-1` whose Mertens contribution
produces the orthogonal main term. -/
theorem meanPowerCoefficient_two {ι : Type*} [Fintype ι] [Nonempty ι]
    (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (p : ℕ)
    (hprod : ∀ f, α f p * β f p = 1)
    (hsquare : ∀ f, tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2)) :
    meanPowerCoefficient α β p 2 = heckeAverage a (p ^ 2) - 1 := by
  unfold meanPowerCoefficient
  simp_rw [SatakeCoefficients.powerCoefficient_two _ _ (hprod _), hsquare]
  rw [average_sub, average_const]
  rfl

/-- Pure finite decomposition into prime, prime-square, and higher-power
terms. No interchange of an unproved convergent series is used. -/
theorem finite_box_split (P : Finset ℕ) (J : ℕ) (hJ : 2 ≤ J)
    (F : ℕ × ℕ → ℂ) :
    (∑ pj ∈ P ×ˢ Finset.Icc 1 J, F pj) =
      (∑ p ∈ P, F (p, 1)) + (∑ p ∈ P, F (p, 2)) +
        ∑ pj ∈ P ×ˢ Finset.Icc 3 J, F pj := by
  have hset : Finset.Icc 1 J = ({1, 2} : Finset ℕ) ∪ Finset.Icc 3 J := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hd : Disjoint ({1, 2} : Finset ℕ) (Finset.Icc 3 J) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hj hj'
    omega
  have hinner : ∀ p : ℕ, (∑ j ∈ Finset.Icc 1 J, F (p, j)) =
      F (p, 1) + F (p, 2) + ∑ j ∈ Finset.Icc 3 J, F (p, j) := by
    intro p
    rw [hset, Finset.sum_union hd]
    norm_num
  rw [Finset.sum_product, Finset.sum_product]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The actual finite set of odd prime bases up to the support endpoint. -/
noncomputable def primeBases (L s : ℝ) : Finset ℕ :=
  (Finset.Icc 2 ⌊Real.exp (s * L)⌋₊).filter (fun p => p.Prime ∧ p ≠ 2)

/-- Padding the exponent range to include one and two only adds zero terms
when the Fourier support is too small for those exponents. -/
noncomputable def powerCap (L s : ℝ) : ℕ :=
  max 2 ⌊s * L / Real.log 2⌋₊

noncomputable def primeBox (L s : ℝ) : Finset (ℕ × ℕ) :=
  primeBases L s ×ˢ Finset.Icc 1 (powerCap L s)

theorem primePowerSum_eq_primeBox {L s : ℝ} (hL : 0 < L) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) (α β : ℕ → ℂ) :
    ExplicitFormula.primePowerSum L φ α β =
      ∑ pj ∈ primeBox L s, PrimePowerSupport.primePowerTerm L
        (𝓕 φ : 𝓢(ℝ, ℂ)) (ExplicitFormula.primePowerWeight α β) pj := by
  unfold ExplicitFormula.primePowerSum
  apply tsum_eq_sum
  intro pj hpj
  by_contra hn
  have hbox := PrimePowerSupport.primePowerTerm_support_subset hL hsupp
    (ExplicitFormula.primePowerWeight α β) hn
  obtain ⟨hp, hj⟩ := Finset.mem_product.mp hbox
  have hcond : pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2 := by
    by_contra hc
    exact hn (by simp only [PrimePowerSupport.primePowerTerm, if_neg hc])
  apply hpj
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hp, hcond.1, hcond.2.1⟩, ?_⟩
  exact Finset.mem_Icc.mpr ⟨hcond.2.2,
    (Finset.mem_Icc.mp hj).2.trans (le_max_right _ _)⟩

noncomputable def primeContribution {ι : Type*} [Fintype ι]
    (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p : ℝ) / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
    heckeAverage a p * h (Real.log (p : ℝ) / L)

noncomputable def squareContribution {ι : Type*} [Fintype ι]
    (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
    (heckeAverage a (p ^ 2) - 1) * h (2 * Real.log (p : ℝ) / L)

noncomputable def higherContribution {ι : Type*} [Fintype ι]
    (L s : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) : ℂ :=
  ∑ pj ∈ primeBases L s ×ˢ Finset.Icc 3 (powerCap L s), meanPrimePowerTerm L h α β pj

/-- Exact prime and prime-square extraction for the canonical prime box. -/
theorem mean_primeBox_split {ι : Type*} [Fintype ι] [Nonempty ι]
    (L s : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ)
    (hfirst : ∀ p ∈ primeBases L s, ∀ f, α f p + β f p = a f p)
    (hprod : ∀ p ∈ primeBases L s, ∀ f, α f p * β f p = 1)
    (hsquare : ∀ p ∈ primeBases L s, ∀ f,
      tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2)) :
    (∑ pj ∈ primeBox L s, meanPrimePowerTerm L h α β pj) =
      primeContribution L h a (primeBases L s) +
        squareContribution L h a (primeBases L s) + higherContribution L s h α β := by
  rw [primeBox, finite_box_split (primeBases L s) (powerCap L s) (le_max_left _ _)]
  congr 2
  · apply Finset.sum_congr rfl
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    dsimp only [meanPrimePowerTerm]
    rw [if_pos (show p.Prime ∧ p ≠ 2 ∧ 1 ≤ (1 : ℕ) from ⟨hc.1, hc.2, by decide⟩)]
    simp only [Nat.cast_one, one_mul]
    rw [meanPowerCoefficient_one α β a p (hfirst p hp)]
    simp only [← Real.sqrt_eq_rpow, Complex.ofReal_div]
  · apply Finset.sum_congr rfl
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    dsimp only [meanPrimePowerTerm]
    rw [if_pos (show p.Prime ∧ p ≠ 2 ∧ 1 ≤ (2 : ℕ) from ⟨hc.1, hc.2, by decide⟩)]
    simp only [Nat.cast_ofNat]
    rw [meanPowerCoefficient_two α β a p (hprod p hp) (hsquare p hp)]
    norm_num [Complex.ofReal_div]

/-- The exact finite-family identity underlying (61), before bounding the
archimedean and higher-power remainders. All prime sums are literal sums. -/
theorem averaged_low_power_formula {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : ι → Type*} {L s : ℝ} (hL : 0 < L) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (γ : ∀ f, κ f → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (A : ℂ)
    (hfirst : ∀ p ∈ primeBases L s, ∀ f, α f p + β f p = a f p)
    (hprod : ∀ p ∈ primeBases L s, ∀ f, α f p * β f p = 1)
    (hsquare : ∀ p ∈ primeBases L s, ∀ f,
      tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2))
    (h56 : ∀ f, ExplicitFormula.density s L φ (γ f) =
      A - ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (α f) (β f)) :
    meanDensity s L φ γ = A - ((2 / L : ℝ) : ℂ) *
      primeContribution L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * squareContribution L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * higherContribution L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β := by
  have hsum : average (fun f => ExplicitFormula.primePowerSum L φ (α f) (β f)) =
      ∑ pj ∈ primeBox L s, meanPrimePowerTerm L (𝓕 φ : 𝓢(ℝ, ℂ)) α β pj := by
    simp_rw [primePowerSum_eq_primeBox hL φ hsupp]
    rw [average_finset_sum]
    apply Finset.sum_congr rfl
    intro pj _
    exact average_primePowerTerm L _ α β pj
  unfold meanDensity
  simp_rw [h56]
  rw [average_sub, average_const, average_mul_left, hsum,
    mean_primeBox_split L s _ α β a hfirst hprod hsquare]
  ring

end DepthAspect.UnsignedDensity
