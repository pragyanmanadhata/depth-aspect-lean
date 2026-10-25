import DepthAspect.EulerFourier
import DepthAspect.FourierDecay
import DepthAspect.DensityReduction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Actual integral kernels for the orthogonal density main terms.
The point mass at zero acts by evaluation at zero. No Fourier-pairing or
random-matrix integral identity is assumed in this module. -/
open MeasureTheory Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace DepthAspect.RandomMatrixMainTerms

noncomputable def unitBox : ℝ → ℂ := (Icc (-1) 1).indicator (fun _ => 1)

theorem unitBox_integrable : Integrable unitBox :=
  (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem integral_phase_unit (r : ℝ) :
    (∫ t : ℝ in (-1)..1, Complex.exp (((r * t : ℝ) : ℂ) * Complex.I)) =
      2 * (Real.sinc r : ℂ) := by
  by_cases hr : r = 0
  · subst r
    norm_num
  have hc : (r : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) Complex.I_ne_zero
  have he : (fun t : ℝ => Complex.exp (((r * t : ℝ) : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp (((r : ℂ) * Complex.I) * (t : ℂ))) := by
    funext t
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hc, Real.sinc_of_ne_zero hr]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg,
    ← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_div]
  field_simp [hc, Complex.ofReal_ne_zero.mpr hr]
  <;> ring

/-- The exact Fourier transform of the interval indicator, including zero. -/
theorem fourier_unitBox (ξ : ℝ) :
    𝓕 unitBox ξ = 2 * (Real.sinc (2 * Real.pi * ξ) : ℂ) := by
  rw [← EulerFourier.integral_mode]
  have hi : (fun x => EulerFourier.phase ξ x * unitBox x) =
      (Icc (-1) 1).indicator (EulerFourier.phase ξ) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [unitBox, hx]
  rw [hi, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have he : EulerFourier.phase ξ =
      (fun x : ℝ => Complex.exp ((((-2 * Real.pi * ξ) * x : ℝ) : ℂ) * Complex.I)) := by
    funext x
    unfold EulerFourier.phase
    congr 1
    push_cast
    ring
  rw [he, integral_phase_unit]
  simp [show -2 * Real.pi * ξ = -(2 * Real.pi * ξ) by ring]

/-- Bilinear Fourier pairing, specialized from mathlib to real variables. -/
theorem integral_fourier_pairing (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, 𝓕 f ξ * g ξ) = ∫ x, f x * 𝓕 g x := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    ext x y
    simp [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop) hf hg
  rw [hflip] at h
  exact h

/-- The sine kernel is paired with the actual Schwartz Fourier transform. -/
theorem integral_sinc (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * (Real.sinc (2 * Real.pi * x) : ℂ)) =
      (∫ ξ in Icc (-1) 1, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2 := by
  have h := integral_fourier_pairing φ unitBox φ.integrable unitBox_integrable
  have he : (fun ξ => 𝓕 (φ : ℝ → ℂ) ξ * unitBox ξ) =
      (Icc (-1) 1).indicator (fun ξ => (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) := by
    funext ξ
    by_cases hξ : ξ ∈ Icc (-1 : ℝ) 1 <;> simp [unitBox, hξ, SchwartzMap.fourier_coe]
  rw [he, integral_indicator measurableSet_Icc] at h
  simp_rw [fourier_unitBox, show ∀ x : ℝ, φ x * (2 * (Real.sinc (2 * Real.pi * x) : ℂ)) =
    2 * (φ x * (Real.sinc (2 * Real.pi * x) : ℂ)) from fun x => by ring] at h
  rw [integral_const_mul] at h
  linear_combination -h / 2

theorem sinc_product_integrable (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x => φ x * (Real.sinc (2 * Real.pi * x) : ℂ)) := by
  apply φ.integrable.norm.mono'
    (φ.continuous.aestronglyMeasurable.mul (by fun_prop))
  filter_upwards [] with x
  change ‖φ x * (Real.sinc (2 * Real.pi * x) : ℂ)‖ ≤ ‖φ x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sinc_le_one _)

noncomputable def orthogonal (φ : 𝓢(ℝ, ℂ)) : ℂ := (∫ x, φ x) + φ 0 / 2

noncomputable def specialOrthogonalEven (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ x, φ x * (1 + (Real.sinc (2 * Real.pi * x) : ℂ))

noncomputable def specialOrthogonalOdd (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  (∫ x, φ x * (1 - (Real.sinc (2 * Real.pi * x) : ℂ))) + φ 0

theorem orthogonal_eq (φ : 𝓢(ℝ, ℂ)) :
    orthogonal φ = (𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2 := by
  rw [orthogonal, EntireExtension.schwartz_fourier_zero]

theorem specialOrthogonalEven_eq (φ : 𝓢(ℝ, ℂ)) :
    specialOrthogonalEven φ = (𝓕 φ : 𝓢(ℝ, ℂ)) 0 +
      (∫ ξ in Icc (-1) 1, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2 := by
  simp_rw [specialOrthogonalEven, mul_add, mul_one]
  rw [integral_add φ.integrable (sinc_product_integrable φ), integral_sinc,
    ← EntireExtension.schwartz_fourier_zero]

theorem specialOrthogonalOdd_eq (φ : 𝓢(ℝ, ℂ)) :
    specialOrthogonalOdd φ = (𝓕 φ : 𝓢(ℝ, ℂ)) 0 -
      (∫ ξ in Icc (-1) 1, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2 + φ 0 := by
  simp_rw [specialOrthogonalOdd, mul_sub, mul_one]
  rw [integral_sub φ.integrable (sinc_product_integrable φ), integral_sinc,
    ← EntireExtension.schwartz_fourier_zero]

theorem fourier_inside_outside (φ : 𝓢(ℝ, ℂ)) :
    φ 0 = (∫ ξ in Icc (-1) 1, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) +
      ∫ ξ in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ := by
  rw [← EntireExtension.schwartz_integral_fourier φ,
    integral_add_compl measurableSet_Icc (𝓕 φ).integrable]

/-- The actual plus-sign main term equals the SO(even) integral. -/
theorem plus_main_term (φ : 𝓢(ℝ, ℂ)) :
    orthogonal φ - (∫ ξ in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2 =
      specialOrthogonalEven φ := by
  rw [orthogonal_eq, specialOrthogonalEven_eq]
  have h := fourier_inside_outside φ
  linear_combination h / 2

/-- The actual minus-sign main term includes the central point mass. -/
theorem minus_main_term (φ : 𝓢(ℝ, ℂ)) :
    orthogonal φ + (∫ ξ in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2 =
      specialOrthogonalOdd φ := by
  rw [orthogonal_eq, specialOrthogonalOdd_eq]
  have h := fourier_inside_outside φ
  linear_combination -h / 2

end DepthAspect.RandomMatrixMainTerms
