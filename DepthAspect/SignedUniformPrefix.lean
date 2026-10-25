import DepthAspect.SignedDensityModel
import DepthAspect.SignedDensityExponents

/-!
# A model-independent finite-prefix constant

The finite initial depths are bounded from the literal explicit formula
and the unit Satake bounds. The envelope contains only the fixed test,
conductor, archimedean factor and a finite box of scalar weights. In
particular it contains no eigenvalues, zero ordinates or density errors.
-/
namespace DepthAspect.SignedDensity
open SpectralFamily UnsignedDensity
open scoped BigOperators FourierTransform SchwartzMap

/-- The scalar part of the canonical finite prime-power box. -/
noncomputable def scalarPrimeBox (L s : ℝ) : ℝ :=
  ∑ pj ∈ primeBox L s,
    ‖(Real.log (pj.1 : ℝ) : ℂ) / (((pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2) : ℝ) : ℂ)‖

theorem scalarPrimeBox_nonneg (L s : ℝ) : 0 ≤ scalarPrimeBox L s :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The usual average bound also covers the empty family when its upper
bound is nonnegative; this avoids a separate low-level dimension premise. -/
theorem norm_average_le_nonneg {ι : Type*} [Fintype ι]
    (X : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hX : ∀ f, ‖X f‖ ≤ C) :
    ‖average X‖ ≤ C := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    simpa [SpectralFamily.average] using hC
  | inr h =>
    letI := h
    exact norm_average_le X C hX

/-- A finite prime box gives a bound depending only on scalar weights and
the uniform test norm. It does not depend on the particular Satake roots. -/
theorem primePowerSum_uniform_bound {L s H : ℝ} (hL : 0 < L) (hH : 0 ≤ H)
    (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (hh : ∀ x, ‖(𝓕 φ : 𝓢(ℝ, ℂ)) x‖ ≤ H)
    (α β : ℕ → ℂ)
    (hα : ∀ p ∈ primeBases L s, ‖α p‖ = 1)
    (hβ : ∀ p ∈ primeBases L s, ‖β p‖ = 1) :
    ‖ExplicitFormula.primePowerSum L φ α β‖ ≤ scalarPrimeBox L s * 2 * H := by
  rw [primePowerSum_eq_primeBox hL φ hsupp]
  calc
    _ ≤ ∑ pj ∈ primeBox L s, ‖PrimePowerSupport.primePowerTerm L
        (𝓕 φ : 𝓢(ℝ, ℂ)) (ExplicitFormula.primePowerWeight α β) pj‖ := norm_sum_le _ _
    _ ≤ ∑ pj ∈ primeBox L s,
        ‖(Real.log (pj.1 : ℝ) : ℂ) /
          (((pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2) : ℝ) : ℂ)‖ * 2 * H := by
      apply Finset.sum_le_sum
      intro pj hpj
      obtain ⟨hp, hj⟩ := Finset.mem_product.mp hpj
      obtain ⟨_, hpprime, hp2⟩ := Finset.mem_filter.mp hp
      have hc : pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2 :=
        ⟨hpprime, hp2, (Finset.mem_Icc.mp hj).1⟩
      simp only [PrimePowerSupport.primePowerTerm, if_pos hc,
        ExplicitFormula.primePowerWeight, norm_mul]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (SatakeCoefficients.norm_powerCoefficient_le_two _ _ (hα _ hp) (hβ _ hp) _)
          (norm_nonneg _))
        (hh _) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [scalarPrimeBox, Finset.sum_mul]

/-- The signed density is bounded uniformly over all finite spectral
models having the same conductor, test and archimedean term. The explicit
formula premise here is discharged by `AnalyticData.explicit_formula`. -/
theorem signedMeanDensity_uniform_bound {ι : Type*} [Fintype ι] {κ : ι → Type*}
    {L s H : ℝ} (hL : 0 < L) (hH : 0 ≤ H)
    (ε : ι → ℂ) (hε : ∀ f, ‖ε f‖ ≤ 1) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (hh : ∀ x, ‖(𝓕 φ : 𝓢(ℝ, ℂ)) x‖ ≤ H)
    (γ : ∀ f, κ f → ℂ) (α β : ι → ℕ → ℂ) (A : ℂ)
    (hα : ∀ p ∈ primeBases L s, ∀ f, ‖α f p‖ = 1)
    (hβ : ∀ p ∈ primeBases L s, ∀ f, ‖β f p‖ = 1)
    (h56 : ∀ f, ExplicitFormula.density s L φ (γ f) =
      A - ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (α f) (β f)) :
    ‖signedMeanDensity ε s L φ γ‖ ≤
      ‖A‖ + (2 / L) * (scalarPrimeBox L s * 2 * H) := by
  have hE : 0 ≤ ‖A‖ + (2 / L) * (scalarPrimeBox L s * 2 * H) :=
    add_nonneg (norm_nonneg _) (mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (scalarPrimeBox_nonneg L s) (by norm_num)) hH))
  apply norm_average_le_nonneg _ hE
  intro f
  rw [norm_mul]
  have hD : ‖ExplicitFormula.density s L φ (γ f)‖ ≤
      ‖A‖ + (2 / L) * (scalarPrimeBox L s * 2 * H) := by
    rw [h56 f]
    apply (norm_sub_le _ _).trans
    refine add_le_add le_rfl ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 / L)]
    exact mul_le_mul_of_nonneg_left
      (primePowerSum_uniform_bound hL hH φ hsupp hh (α f) (β f)
        (fun p hp => hα p hp f) (fun p hp => hβ p hp f)) (by positivity)
  exact (mul_le_mul (hε f) hD (norm_nonneg _) (by norm_num)).trans (by simp)

/-- A single finite-prefix envelope extends a tail bound uniformly in any
auxiliary model. Only `E` varies with that model; the displayed constant
uses `L`, `B`, `K` and the cutoff, and contains no value of `E`. -/
theorem extend_finite_prefix_uniform (L B : ℕ → ℝ) (E : ℕ → ℂ)
    (start cutoff : ℕ) (hL : ∀ n, start ≤ n → 0 < L n)
    (hB : ∀ n, 0 ≤ B n) (hE : ∀ n, start ≤ n → ‖E n‖ ≤ B n)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n, start ≤ n → cutoff ≤ n → ‖E n‖ ≤ K / L n) :
    let C := K + ∑ j ∈ Finset.range cutoff, max 0 (L j) * B j
    0 ≤ C ∧ ∀ n, start ≤ n → ‖E n‖ ≤ C / L n := by
  let C₀ := ∑ j ∈ Finset.range cutoff, max 0 (L j) * B j
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg
    (fun j _ => mul_nonneg (le_max_left _ _) (hB j))
  refine ⟨add_nonneg hK hC₀, ?_⟩
  intro n hn
  by_cases hcut : cutoff ≤ n
  · exact (hbound n hn hcut).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right hC₀) (hL n hn).le)
  · have hnmem : n ∈ Finset.range cutoff := Finset.mem_range.mpr (by omega)
    have hsingle : max 0 (L n) * B n ≤ C₀ :=
      Finset.single_le_sum (fun j _ => mul_nonneg (le_max_left _ _) (hB j)) hnmem
    rw [max_eq_right (hL n hn).le] at hsingle
    apply (le_div_iff₀ (hL n hn)).mpr
    have hmul := mul_le_mul_of_nonneg_left (hE n hn) (hL n hn).le
    nlinarith

end DepthAspect.SignedDensity
