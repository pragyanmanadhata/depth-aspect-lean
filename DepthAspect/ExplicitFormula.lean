import DepthAspect.ExplicitFormulaModel
import DepthAspect.FourierScaling
import DepthAspect.EulerFactor
import DepthAspect.GammaLocal
import DepthAspect.PrimePowerReindex

/-! Internal specialization of the general cited explicit-formula identity. -/
open MeasureTheory Set
open scoped BigOperators FourierTransform SchwartzMap
namespace DepthAspect.ExplicitFormula

/-- Different valid support endpoints define the same entire test. -/
theorem extension_support_independent (φ : 𝓢(ℝ, ℂ))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hss : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s)
    (hts : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-t) t) :
    EntireExtension.extension s (𝓕 φ : 𝓢(ℝ, ℂ)) =
      EntireExtension.extension t (𝓕 φ : 𝓢(ℝ, ℂ)) := by
  apply EntireExtension.entire_unique
  · exact EntireExtension.extension_entire hs (𝓕 φ).continuous
  · exact EntireExtension.extension_entire ht (𝓕 φ).continuous
  · intro x
    rw [EntireExtension.schwartz_extension_on_real φ hss,
      EntireExtension.schwartz_extension_on_real φ hts]

/-- The density is independent of the auxiliary Fourier-support endpoint. -/
theorem density_support_independent {ι : Type*} (φ : 𝓢(ℝ, ℂ))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hss : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s)
    (hts : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-t) t)
    (L : ℝ) (γ : ι → ℂ) : density s L φ γ = density t L φ γ := by
  unfold density
  rw [extension_support_independent φ hs ht hss hts]

/-- The actual degree-two local factor at every good prime, with the
bad-prime factor at 2 equal to one. Nonprime slots never enter the formula. -/
noncomputable def finiteEulerFactor (α β : ℕ → ℂ) (p : ℕ) : ℂ → ℂ :=
  if p = 2 then fun _ => 1 else EulerFactor.localFactor (p : ℝ) (α p) (β p)

/-- The bad-prime local integral really vanishes. -/
theorem bad_prime_localIntegral (α β : ℕ → ℂ) (φ : ℝ → ℂ) :
    localIntegral (finiteEulerFactor α β 2) φ = 0 := by
  simp [finiteEulerFactor, localIntegral]

/-- The Gamma contribution after the actual test-function substitution. -/
theorem gamma_localIntegral_scaled (hDLMF : DigammaBound.DLMFSeriesIdentity)
    (a : ℕ) (ha : 1 ≤ a) (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    {c : ℝ} (hc : 0 < c) :
    localIntegral (GammaLocal.gammaFactor (2 * (a : ℝ)))
        (FourierScaling.scale c (ne_of_gt hc) φ) =
      (c⁻¹ : ℂ) * (-(Real.log (2 * Real.pi) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) 0 +
        ∫ x, ArchimedeanBound.gammaIntegrand a c⁻¹ φ x) := by
  have hk : 1 ≤ 2 * (a : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * a)
  unfold localIntegral
  simp_rw [FourierScaling.scale_apply, GammaLocal.gammaFactor_logDeriv_critical hk]
  rw [FourierScaling.integral_kernel_scale _ φ hc]
  congr 1
  have he : (fun x : ℝ =>
      (-(Real.log (2 * Real.pi) : ℂ) +
        Complex.digamma (((2 * (a : ℝ)) / 2 : ℝ) + ((x / c : ℝ) : ℂ) * Complex.I)) * φ x) =
      (fun x => -(Real.log (2 * Real.pi) : ℂ) * φ x +
        Complex.digamma ((a : ℂ) + ((c⁻¹ * x : ℝ) : ℂ) * Complex.I) * φ x) := by
    funext x
    have hhalf : (2 * (a : ℝ)) / 2 = (a : ℝ) := by ring
    rw [hhalf]
    simp [div_eq_mul_inv, mul_comm, add_mul]
  have hi : Integrable (fun x : ℝ =>
      Complex.digamma ((a : ℂ) + ((c⁻¹ * x : ℝ) : ℂ) * Complex.I) * φ x) := by
    simpa only [Complex.ofReal_natCast] using
      (GammaLocal.digamma_kernel_integrable hDLMF
        (by exact_mod_cast ha : (1 : ℝ) ≤ (a : ℝ)) c⁻¹ φ φ.integrable
        (ArchimedeanBound.schwartz_first_moment_integrable φ))
  rw [he, integral_add (φ.integrable.const_mul _) hi, integral_const_mul,
    ← EntireExtension.schwartz_fourier_zero φ,
    GammaLocal.digamma_even_integral hDLMF a ha c⁻¹ φ heven φ.integrable
      (ArchimedeanBound.schwartz_first_moment_integrable φ)]

/-- A good-prime integral is evaluated locally before summing over primes. -/
theorem good_prime_localIntegral_scaled {L : ℝ} (hL : 0 < L)
    (φ : 𝓢(ℝ, ℂ)) (α β : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hα : ‖α p‖ = 1) (hβ : ‖β p‖ = 1) :
    localIntegral (finiteEulerFactor α β p)
        (FourierScaling.scale (L / (2 * Real.pi)) (by positivity) φ) =
      -(((L / (2 * Real.pi))⁻¹ : ℝ) : ℂ) * ∑' j : ℕ,
        primePowerWeight α β p (j + 1) *
          (𝓕 φ : 𝓢(ℝ, ℂ)) (((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ) / L) := by
  have hc : 0 < L / (2 * Real.pi) := by positivity
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  simp only [localIntegral, finiteEulerFactor, if_neg hp2, FourierScaling.scale_apply]
  rw [FourierScaling.integral_kernel_scale _ φ hc]
  have he : ∀ x : ℝ, (1 / 2 : ℂ) + ((x / (L / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
      (1 / 2 : ℂ) + Complex.I * ((2 * Real.pi * x / L : ℝ) : ℂ) := by
    intro x
    push_cast
    field_simp
    <;> ring
  simp_rw [he]
  rw [EulerFactor.integral_local_logDeriv_critical hpR (α p) (β p) hα hβ φ φ.integrable L]
  have hw : (∑' j : ℕ, primePowerWeight α β p (j + 1) *
      (𝓕 φ : 𝓢(ℝ, ℂ)) (((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ) / L)) =
      (Real.log (p : ℝ) : ℂ) * ∑' j : ℕ,
        SatakeCoefficients.powerCoefficient (α p) (β p) (j + 1) /
          (((p : ℝ) ^ (((j + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
            (𝓕 φ : 𝓢(ℝ, ℂ)) (((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ) / L) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    unfold primePowerWeight
    ring
  rw [hw]
  simp only [SchwartzMap.fourier_coe, Complex.ofReal_inv]
  ring

/-- The outer prime sum is identified only after each local integral has
been evaluated; compact support justifies the product-index reindexing. -/
theorem finite_localIntegrals_scaled {L s : ℝ} (hL : 0 < L) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s)
    (α β : ℕ → ℂ)
    (hα : ∀ p, p.Prime → p ≠ 2 → ‖α p‖ = 1)
    (hβ : ∀ p, p.Prime → p ≠ 2 → ‖β p‖ = 1) :
    (∑' p : ℕ, if p.Prime then localIntegral (finiteEulerFactor α β p)
        (FourierScaling.scale (L / (2 * Real.pi)) (by positivity) φ) else 0) =
      -(((L / (2 * Real.pi))⁻¹ : ℝ) : ℂ) * primePowerSum L φ α β := by
  rw [primePowerSum_eq_iterated hL φ hsupp α β, ← tsum_mul_left]
  apply tsum_congr
  intro p
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      simp [bad_prime_localIntegral]
    · simpa [hp, hp2] using
        good_prime_localIntegral_scaled hL φ α β hp hp2 (hα p hp hp2) (hβ p hp hp2)
  · simp [hp]

/-- Equation (56), derived from the cited general local-integral formula.
All Gamma constants, Fourier scaling factors, good-prime coefficients and
the absence of a bad-prime term have been evaluated internally. -/
theorem explicit_formula (hDLMF : DigammaBound.DLMFSeriesIdentity)
    {ι : Type*} (N k : ℝ) (hN : 0 < N) (a : ℕ) (ha : 1 ≤ a)
    (hk : k = 2 * (a : ℝ)) (hL : 0 < Real.log (k ^ 2 * N))
    (γ : ι → ℂ) (α β : ℕ → ℂ)
    (hα : ∀ p, p.Prime → p ≠ 2 → ‖α p‖ = 1)
    (hβ : ∀ p, p.Prime → p ≠ 2 → ‖β p‖ = 1)
    (hST : ShinTemplierFormula N γ (GammaLocal.gammaFactor k) (finiteEulerFactor α β))
    {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    density s (Real.log (k ^ 2 * N)) φ γ =
      ArchimedeanBound.archimedeanTerm N k a φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0) -
        ((2 / Real.log (k ^ 2 * N) : ℝ) : ℂ) *
          primePowerSum (Real.log (k ^ 2 * N)) φ α β := by
  let L := Real.log (k ^ 2 * N)
  let c := L / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c, L]; positivity
  have h := hST (c * s) (mul_nonneg hc.le hs)
    (FourierScaling.scale c (ne_of_gt hc) φ)
    (FourierScaling.scale_even φ heven (ne_of_gt hc))
    (FourierScaling.schwartz_fourier_scale_support φ hc hsupp)
  rw [FourierScaling.schwartz_extension_scale φ hc hs hsupp,
    FourierScaling.schwartz_fourier_scale φ hc, zero_div] at h
  have hGamma := gamma_localIntegral_scaled hDLMF a ha φ heven hc
  rw [← hk] at hGamma
  rw [hGamma, finite_localIntegrals_scaled hL φ hsupp α β hα hβ] at h
  change density s L φ γ = _ at h
  rw [h]
  have hcInv : c⁻¹ = 2 * Real.pi / L := by dsimp [c]; field_simp
  have hlog : Real.log (N / (4 * Real.pi ^ 2)) =
      Real.log N - 2 * Real.log (2 * Real.pi) := by
    have h2pi : (2 * Real.pi) ^ 2 = 4 * Real.pi ^ 2 := by ring
    rw [Real.log_div (ne_of_gt hN) (by positivity), ← h2pi, Real.log_pow]
    norm_num
  simp only [ArchimedeanBound.archimedeanTerm, Complex.real_smul, hcInv, hlog]
  dsimp only [c, L] at *
  push_cast
  field_simp [ne_of_gt hL, Real.pi_ne_zero]
  <;> ring

end DepthAspect.ExplicitFormula
