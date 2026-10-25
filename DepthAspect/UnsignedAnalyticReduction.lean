import DepthAspect.UnsignedErrorAssembly
import DepthAspect.ExplicitFormula

/-!
# The unsigned analytic reduction with equation (56) discharged

The only explicit-formula input here is the cited general local-integral
identity. The pointwise specialization, finite spectral averaging,
archimedean integral, higher prime powers and Mertens main term are all
proved internally. Only the two named finite Hecke sum estimates remain
for the arithmetic assembly.
-/
namespace DepthAspect.UnsignedDensity

open SpectralFamily
open scoped BigOperators FourierTransform SchwartzMap

noncomputable def analyticConstant (a : ℕ) (φ : 𝓢(ℝ, ℂ)) (C : ℝ) : ℝ :=
  archimedeanConstant a φ + 192 * ‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖ +
    (4 * Real.log 2 + 2 * C) *
      (‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖ +
        ∫ u : ℝ, ‖deriv (𝓕 φ : 𝓢(ℝ, ℂ)) u‖)

/-- Actual finite spectral density, with all its analytic errors evaluated.
`hPrime` and `hSquare` are reusable intermediate arithmetic estimates, not
additional assumptions in the final density theorem. -/
theorem density_error_from_general_explicit_formula
    {ι : Type*} [Fintype ι] [Nonempty ι] {κ : ι → Type*}
    (hDLMF : DigammaBound.DLMFSeriesIdentity)
    (N : ℝ) (hN : 1 ≤ N) (a : ℕ) (ha : 1 ≤ a)
    {s C EP EQ : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (hL : 1 ≤ Real.log ((2 * (a : ℝ)) ^ 2 * N))
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (γ : ∀ f, κ f → ℂ) (α β : ι → ℕ → ℂ) (eigenvalues : ι → ℕ → ℂ)
    (hα : ∀ f p, p.Prime → p ≠ 2 → ‖α f p‖ = 1)
    (hβ : ∀ f p, p.Prime → p ≠ 2 → ‖β f p‖ = 1)
    (hfirst : ∀ f p, p.Prime → p ≠ 2 → α f p + β f p = eigenvalues f p)
    (hprod : ∀ f p, p.Prime → p ≠ 2 → α f p * β f p = 1)
    (hsquare : ∀ f p, p.Prime → p ≠ 2 →
      tracePolynomial (α f p + β f p) 1 2 = eigenvalues f (p ^ 2))
    (hST : ∀ f, ExplicitFormula.ShinTemplierFormula N (γ f)
      (GammaLocal.gammaFactor (2 * (a : ℝ)))
      (ExplicitFormula.finiteEulerFactor (α f) (β f)))
    (hPrime : let L := Real.log ((2 * (a : ℝ)) ^ 2 * N)
      (2 / L) * PrimePowerApplications.weightedSum (primeBases L s)
        (-(1 / 2 : ℝ)) (heckeAverage eigenvalues)
        (fun p => (𝓕 φ : 𝓢(ℝ, ℂ)) (Real.log p / L)) ≤ EP)
    (hSquare : let L := Real.log ((2 * (a : ℝ)) ^ 2 * N)
      (2 / L) * PrimePowerApplications.weightedSum (primeBases L s)
        (-1) (fun p => heckeAverage eigenvalues (p ^ 2))
        (fun p => (𝓕 φ : 𝓢(ℝ, ℂ)) (2 * Real.log p / L)) ≤ EQ) :
    ‖meanDensity s (Real.log ((2 * (a : ℝ)) ^ 2 * N)) φ γ -
      ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤
      analyticConstant a φ C / Real.log ((2 * (a : ℝ)) ^ 2 * N) + EP + EQ := by
  let L := Real.log ((2 * (a : ℝ)) ^ 2 * N)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hp (p : ℕ) (hp : p ∈ primeBases L s) : p.Prime ∧ p ≠ 2 :=
    (Finset.mem_filter.mp hp).2
  have h56 := fun f => ExplicitFormula.explicit_formula hDLMF N (2 * (a : ℝ))
    (by linarith) a ha rfl hL0 (γ f) (α f) (β f) (hα f) (hβ f) (hST f)
    hs φ heven hsupp
  have hb := density_error_from_trace_sums hL0 (norm_nonneg _) hC hM φ heven hsupp
    γ α β eigenvalues (ArchimedeanBound.archimedeanTerm N (2 * a) a φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0))
    (fun p hp' f => hfirst f p (hp p hp').1 (hp p hp').2)
    (fun p hp' f => hprod f p (hp p hp').1 (hp p hp').2)
    (fun p hp' f => hsquare f p (hp p hp').1 (hp p hp').2)
    (fun p hp' f => hα f p (hp p hp').1 (hp p hp').2)
    (fun p hp' f => hβ f p (hp p hp').1 (hp p hp').2)
    (fun x => (𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction.norm_coe_le_norm x)
    (actual_archimedean_error hDLMF N hN a ha φ hL) h56 hPrime hSquare
  convert hb using 1 <;> dsimp [analyticConstant, L] <;> ring

end DepthAspect.UnsignedDensity
