import DepthAspect.FourierDecay
import DepthAspect.EulerFourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp

/-!
# Rescaling the actual Schwartz test in the explicit formula

All scaling factors are proved with mathlib's Fourier normalization. The
entire extension of the rescaled test is identified by uniqueness.
-/
open MeasureTheory Set
open scoped FourierTransform SchwartzMap
namespace DepthAspect.FourierScaling

noncomputable def scale (c : ℝ) (hc : c ≠ 0) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc)) φ

@[simp] theorem scale_apply (c : ℝ) (hc : c ≠ 0) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    scale c hc φ x = φ (c * x) := by
  simp [scale, mul_comm]

/-- A general integral substitution retains its exact Jacobian. -/
theorem integral_scale (f : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ x, f (c * x)) = (c⁻¹ : ℂ) * ∫ x, f x := by
  simpa only [abs_of_pos (inv_pos.mpr hc), Complex.real_smul, Complex.ofReal_inv] using
    Measure.integral_comp_mul_left f c

/-- Scaling the test while leaving the kernel visible. -/
theorem integral_kernel_scale (G φ : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    (∫ r, G r * φ (c * r)) = (c⁻¹ : ℂ) * ∫ x, G (x / c) * φ x := by
  have he : (fun r => G r * φ (c * r)) =
      (fun r => (fun x => G (x / c) * φ x) (c * r)) := by
    funext r
    simp [mul_div_cancel_left₀ r (ne_of_gt hc)]
  rw [he]
  exact integral_scale (fun x => G (x / c) * φ x) hc

/-- The Fourier transform of the actual rescaled function. -/
theorem fourier_scale (φ : ℝ → ℂ) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (fun x => φ (c * x)) ξ = (c⁻¹ : ℂ) * 𝓕 φ (ξ / c) := by
  rw [← EulerFourier.integral_mode, ← EulerFourier.integral_mode]
  have he : (fun x => EulerFourier.phase ξ x * φ (c * x)) =
      (fun x => (fun y => EulerFourier.phase (ξ / c) y * φ y) (c * x)) := by
    funext x
    congr 1
    unfold EulerFourier.phase
    congr 2
    field_simp [ne_of_gt hc]
    <;> ring
  rw [he]
  exact integral_scale (fun y => EulerFourier.phase (ξ / c) y * φ y) hc

theorem schwartz_fourier_scale (φ : 𝓢(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    (𝓕 (scale c (ne_of_gt hc) φ) : 𝓢(ℝ, ℂ)) ξ =
      (c⁻¹ : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) (ξ / c) := by
  have he : (scale c (ne_of_gt hc) φ : ℝ → ℂ) = (fun x => φ (c * x)) :=
    funext (scale_apply c (ne_of_gt hc) φ)
  change 𝓕 (scale c (ne_of_gt hc) φ : ℝ → ℂ) ξ = _
  rw [he]
  exact fourier_scale φ hc ξ

/-- The support endpoint scales by the same positive factor as the test. -/
theorem schwartz_fourier_scale_support (φ : 𝓢(ℝ, ℂ)) {c s : ℝ} (hc : 0 < c)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    Function.support (𝓕 (scale c (ne_of_gt hc) φ) : 𝓢(ℝ, ℂ)) ⊆ Icc (-(c * s)) (c * s) := by
  intro ξ hξ
  have hn : (𝓕 φ : 𝓢(ℝ, ℂ)) (ξ / c) ≠ 0 := by
    intro hz
    exact hξ (by rw [schwartz_fourier_scale φ hc ξ, hz, mul_zero])
  have h := hsupp hn
  constructor
  · have hl := (le_div_iff₀ hc).mp h.1
    nlinarith
  · have hu := (div_le_iff₀ hc).mp h.2
    nlinarith

theorem scale_even (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    {c : ℝ} (hc : c ≠ 0) : Function.Even (scale c hc φ) := by
  intro x
  simp only [scale_apply, mul_neg]
  exact heven (c * x)

/-- The scaled entire test is the original entire extension evaluated at c*z.
This identifies the literal zero ordinates appearing in the density. -/
theorem schwartz_extension_scale (φ : 𝓢(ℝ, ℂ)) {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    EntireExtension.extension (c * s) (𝓕 (scale c (ne_of_gt hc) φ) : 𝓢(ℝ, ℂ)) =
      (fun z => EntireExtension.extension s (𝓕 φ : 𝓢(ℝ, ℂ)) ((c : ℂ) * z)) := by
  apply EntireExtension.entire_unique
  · exact EntireExtension.extension_entire (mul_nonneg hc.le hs) (𝓕 (scale c (ne_of_gt hc) φ)).continuous
  · exact (EntireExtension.extension_entire hs (𝓕 φ).continuous).comp (by fun_prop)
  · intro x
    rw [EntireExtension.schwartz_extension_on_real _ (schwartz_fourier_scale_support φ hc hsupp),
      scale_apply, ← Complex.ofReal_mul, EntireExtension.schwartz_extension_on_real φ hsupp]

end DepthAspect.FourierScaling
