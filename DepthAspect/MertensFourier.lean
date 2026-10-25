import DepthAspect.MertensWeights
import DepthAspect.FourierDecay

/-!
# The prime-square main term for the actual Fourier transform

This combines the proved weighted Mertens estimate with Fourier inversion
and evenness; the only arithmetic input is the cited cumulative Mertens
error estimate (51).
-/
namespace DepthAspect.MertensFourier

open MeasureTheory MertensWeights
open scoped FourierTransform SchwartzMap

/-- Equation (52) and the main-term identity that follows it, for the actual
Fourier transform of the actual even Schwartz test. -/
theorem fourier_mertens_main_term {L C s : ℝ}
    (hL : 0 < L) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupport : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) :
    ‖(2 / L : ℝ) • weightedTotal (2 / L) (𝓕 φ : 𝓢(ℝ, ℂ)) - φ 0 / 2‖ ≤
      (4 * Real.log 2 + 2 * C) *
        (‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖ +
          ∫ u : ℝ, ‖deriv (𝓕 φ : 𝓢(ℝ, ℂ)) u‖) / L := by
  have hb := schwartz_mertens_total_error hL hC hM (𝓕 φ : 𝓢(ℝ, ℂ)) hsupport
  rwa [EntireExtension.schwartz_positive_fourier_integral φ heven] at hb

end DepthAspect.MertensFourier
