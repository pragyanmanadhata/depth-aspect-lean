import DepthAspect.RandomMatrixMainTerms

/-! The unnumbered comparison of orthogonal symmetry types in Section 1.
These statements use the literal integral kernels and include Fourier support
at the endpoints -1 and 1. No evenness or reality of the test is needed. -/
open MeasureTheory Set
open scoped FourierTransform SchwartzMap
namespace DepthAspect.RandomMatrixMainTerms

/-- The identity stated after the three density kernels in Section 1.3. -/
theorem specialOrthogonal_difference (φ : 𝓢(ℝ, ℂ)) :
    specialOrthogonalOdd φ - specialOrthogonalEven φ =
      ∫ ξ in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := by
  rw [← minus_main_term φ, ← plus_main_term φ]
  ring

theorem outside_integral_zero_of_unit_support (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-1) 1) :
    (∫ ξ in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro ξ hξ
  by_contra hne
  exact hξ (hsupp hne)

/-- The two special-orthogonal densities agree on closed Fourier support
[-1,1], as asserted at the start of the Introduction. -/
theorem specialOrthogonal_agree_of_unit_support (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-1) 1) :
    specialOrthogonalEven φ = specialOrthogonalOdd φ := by
  exact (sub_eq_zero.mp ((specialOrthogonal_difference φ).trans
    (outside_integral_zero_of_unit_support φ hsupp))).symm

end DepthAspect.RandomMatrixMainTerms
