import DepthAspect.FourierDecay
import DepthAspect.SatakeCoefficients
import DepthAspect.PrimePowerSupport

/-!
# External explicit-formula interface and its specialization

The external input below is the general self-dual, cuspidal, pole-free
local-integral formula of Shin–Templier, following (4.9), manuscript p. 35.
The local factors are arbitrary parameters of that input. In particular it
does not assume this paper's prime-power coefficients, Gamma normalization,
scaling factors, or equation (56).

Source: https://arxiv.org/pdf/1208.1945, PDF page index 34.
-/
open MeasureTheory Set
open scoped BigOperators FourierTransform SchwartzMap
namespace DepthAspect.ExplicitFormula

noncomputable def localIntegral (F : ℂ → ℂ) (φ : ℝ → ℂ) : ℂ :=
  ∫ r : ℝ, (deriv F ((1 / 2 : ℂ) + (r : ℂ) * Complex.I) /
    F ((1 / 2 : ℂ) + (r : ℂ) * Complex.I)) * φ r

/-- The cited formula over Q, with finite places indexed by prime natural
numbers and the archimedean place written separately. -/
def ShinTemplierFormula {ι : Type*} (N : ℝ) (γ : ι → ℂ)
    (arch : ℂ → ℂ) (finiteFactor : ℕ → ℂ → ℂ) : Prop :=
  ∀ (s : ℝ) (hs : 0 ≤ s) (Φ : 𝓢(ℝ, ℂ)), Function.Even Φ →
    Function.support (𝓕 Φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s →
    (∑' i, EntireExtension.extension s (𝓕 Φ : 𝓢(ℝ, ℂ)) (γ i)) =
      ((Real.log N / (2 * Real.pi) : ℝ) : ℂ) * (𝓕 Φ : 𝓢(ℝ, ℂ)) 0 +
      (((1 / Real.pi : ℝ) : ℂ) *
        (localIntegral arch Φ + ∑' p : ℕ, if p.Prime then localIntegral (finiteFactor p) Φ else 0))

noncomputable def primePowerWeight (α β : ℕ → ℂ) (p j : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) / (((p : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) *
    SatakeCoefficients.powerCoefficient (α p) (β p) j

/-- The literal prime-power expression in equation (56). Its finite support
is established in PrimePowerSupport, independently of the cited formula. -/
noncomputable def primePowerSum (L : ℝ) (φ : 𝓢(ℝ, ℂ)) (α β : ℕ → ℂ) : ℂ :=
  ∑' pj : ℕ × ℕ, PrimePowerSupport.primePowerTerm L
    (𝓕 φ : 𝓢(ℝ, ℂ)) (primePowerWeight α β) pj

/-- The density evaluates the actual entire test at the scaled complex
ordinates. The zero-counting argument proves its absolute convergence. -/
noncomputable def density {ι : Type*} (s L : ℝ) (φ : 𝓢(ℝ, ℂ)) (γ : ι → ℂ) : ℂ :=
  ∑' i, EntireExtension.extension s (𝓕 φ : 𝓢(ℝ, ℂ))
    (((L / (2 * Real.pi) : ℝ) : ℂ) * γ i)

/-- The formula's prime-power expression has the proved finite support. -/
theorem primePowerSum_eq_finite {L s : ℝ} (hL : 0 < L) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) (α β : ℕ → ℂ) :
    primePowerSum L φ α β =
      ∑ pj ∈ PrimePowerSupport.indexBox L s,
        PrimePowerSupport.primePowerTerm L (𝓕 φ : 𝓢(ℝ, ℂ)) (primePowerWeight α β) pj :=
  PrimePowerSupport.primePowerTerm_tsum_eq hL hsupp _

end DepthAspect.ExplicitFormula
