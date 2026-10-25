import DepthAspect.MurmurationKernel
import DepthAspect.BesselFirstKind
import DepthAspect.EulerFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The actual Fourier transform of the compact Chebyshev kernel. -/
open MeasureTheory Set
open scoped FourierTransform
namespace DepthAspect.MurmurationFourier
open MurmurationKernel BesselFirstKind EulerFourier

noncomputable def complexKernel (k : ℕ) (x : ℝ) : ℂ := kernel k x

theorem complexKernel_continuous (k : ℕ) : Continuous (complexKernel k) :=
  Complex.continuous_ofReal.comp (kernel_continuous k)

theorem kernel_cos (k : ℕ) {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    kernel k (Real.cos θ) = Real.sin (((k : ℝ) - 1) * θ) := by
  rw [kernel_eq_sin_arccos k ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩,
    Real.arccos_cos hθ.1 hθ.2]

/-- The boundary terms in the cosine substitution vanish because the actual
kernel is zero at both endpoints of its support. -/
theorem fourier_eq_sine_integral (k : ℕ) (ξ : ℝ) :
    𝓕 (complexKernel k) ξ = ∫ θ : ℝ in (0)..Real.pi,
      Complex.exp (Complex.I * ((-2 * Real.pi * ξ * Real.cos θ : ℝ) : ℂ)) *
        (Real.sin (((k : ℝ) - 1) * θ) : ℂ) * (Real.sin θ : ℂ) := by
  let g : ℝ → ℂ := fun x => phase ξ x * complexKernel k x
  have hg : Continuous g := (phase_continuous ξ).mul (complexKernel_continuous k)
  have hs : Function.support g ⊆ Ioc (-1) 1 := by
    intro x hx
    have hkx : kernel k x ≠ 0 := by
      intro hzero
      apply hx
      simp [g, complexKernel, hzero]
    exact Ioo_subset_Ioc_self (kernel_support_subset k hkx)
  rw [← integral_mode]
  change (∫ x, g x) = _
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  have hcv := intervalIntegral.integral_deriv_smul_comp
    (a := (0 : ℝ)) (b := Real.pi)
    (f := Real.cos) (f' := fun θ => -Real.sin θ) (g := g)
    (fun θ _ => Real.hasDerivAt_cos θ) (Real.continuous_sin.neg.continuousOn) hg
  rw [Real.cos_zero, Real.cos_pi] at hcv
  have he : (fun θ : ℝ => -Real.sin θ • (g ∘ Real.cos) θ) =
      (fun θ => -(g (Real.cos θ) * (Real.sin θ : ℂ))) := by
    funext θ
    simp only [Function.comp_apply, Complex.real_smul, Complex.ofReal_neg]
    ring
  rw [he, intervalIntegral.integral_neg] at hcv
  have hflip : (∫ x : ℝ in (1)..(-1), g x) = -(∫ x : ℝ in (-1)..1, g x) :=
    intervalIntegral.integral_symm _ _
  rw [hflip] at hcv
  have hcv' := neg_injective hcv
  rw [← hcv']
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Icc 0 Real.pi := by simpa [uIcc_of_le Real.pi_pos.le] using hθ
  dsimp [g, complexKernel]
  rw [kernel_cos k hθ']
  congr 2
  unfold phase
  congr 1
  push_cast
  ring

/-- The elementary trigonometric step behind the Bessel recurrence. -/
theorem sine_product (n : ℕ) (θ : ℝ) :
    Real.sin (((n : ℝ) + 1) * θ) * Real.sin θ =
      (Real.cos ((n : ℝ) * θ) - Real.cos (((n : ℝ) + 2) * θ)) / 2 := by
  have h := Real.cos_sub (((n : ℝ) + 1) * θ) θ
  have h' := Real.cos_add (((n : ℝ) + 1) * θ) θ
  have he : ((n : ℝ) + 1) * θ - θ = (n : ℝ) * θ := by ring
  have he' : ((n : ℝ) + 1) * θ + θ = ((n : ℝ) + 2) * θ := by ring
  rw [he] at h
  rw [he'] at h'
  linarith

/-- The two cosine integrals combine through the general Bessel recurrence;
no transform formula for the paper's kernel is assumed. -/
theorem bessel_sine_integral_pair (hDLMF : DLMFIdentities) (n : ℕ) (t : ℝ) :
    (∫ θ : ℝ in (0)..Real.pi,
      Complex.exp (Complex.I * ((t * Real.cos θ : ℝ) : ℂ)) *
        (Real.sin (((n : ℝ) + 1) * θ) : ℂ) * (Real.sin θ : ℂ)) =
      (Real.pi / 2 : ℂ) * Complex.I ^ n * ((J n t : ℂ) + (J (n + 2) t : ℂ)) := by
  let E : ℝ → ℂ := fun θ => Complex.exp (Complex.I * ((t * Real.cos θ : ℝ) : ℂ))
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hi (m : ℕ) : IntervalIntegrable
      (fun θ : ℝ => E θ * (Real.cos ((m : ℝ) * θ) : ℂ)) volume 0 Real.pi :=
    (hE.mul (Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  have he : (fun θ : ℝ => E θ * (Real.sin (((n : ℝ) + 1) * θ) : ℂ) * (Real.sin θ : ℂ)) =
      (fun θ => (2 : ℂ)⁻¹ * (E θ * (Real.cos ((n : ℝ) * θ) : ℂ) -
        E θ * (Real.cos (((n + 2 : ℕ) : ℝ) * θ) : ℂ))) := by
    funext θ
    rw [mul_assoc, ← Complex.ofReal_mul, sine_product]
    push_cast
    ring
  change (∫ θ : ℝ in (0)..Real.pi, E θ * _ * _) = _
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hi n) (hi (n+2))]
  dsimp only [E]
  rw [hDLMF.cosine_integral, hDLMF.cosine_integral]
  rw [pow_add, Complex.I_sq]
  ring

/-- Recurrence combines the two neighboring Bessel orders when t is nonzero. -/
theorem bessel_sine_integral (hDLMF : DLMFIdentities) (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (∫ θ : ℝ in (0)..Real.pi,
      Complex.exp (Complex.I * ((t * Real.cos θ : ℝ) : ℂ)) *
        (Real.sin (((n : ℝ) + 1) * θ) : ℂ) * (Real.sin θ : ℂ)) =
      ((Real.pi * (n + 1 : ℝ) / t : ℝ) : ℂ) * Complex.I ^ n * (J (n + 1) t : ℂ) := by
  rw [bessel_sine_integral_pair hDLMF n t]
  have hrec := congrArg (fun x : ℝ => (x : ℂ)) (hDLMF.recurrence n t ht)
  push_cast at hrec ⊢
  linear_combination (Real.pi : ℂ) / 2 * Complex.I ^ n * hrec

/-- The zero-frequency term is π/2 at weight two and zero at higher even
weights, derived from the same integral and the actual Bessel series. -/
theorem fourier_zero (hDLMF : DLMFIdentities) (a : ℕ) :
    𝓕 (complexKernel (2 * a + 2)) 0 = if a = 0 then (Real.pi / 2 : ℂ) else 0 := by
  rw [fourier_eq_sine_integral]
  have hn : ((2 * a + 2 : ℕ) : ℝ) - 1 = ((2 * a : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hn]
  have h := bessel_sine_integral_pair hDLMF (2 * a) 0
  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul] at h ⊢
  rw [h]
  by_cases ha : a = 0
  · subst a
    simp [J_at_zero]
  · have h2a : 2 * a ≠ 0 := by omega
    have h2a2 : 2 * a + 2 ≠ 0 := by omega
    simp [ha, J_at_zero, h2a, h2a2]

/-- The literal nonzero-frequency identity (127), with even weight written
as 2a+2. The sign is (-1)^a = (-1)^(k/2-1). -/
theorem fourier_eq_bessel (hDLMF : DLMFIdentities) (a : ℕ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (complexKernel (2 * a + 2)) ξ =
      ((((2 * a + 1 : ℕ) : ℝ) * (-1 : ℝ) ^ a / (2 * ξ) : ℝ) : ℂ) *
        (J (2 * a + 1) (2 * Real.pi * ξ) : ℂ) := by
  rw [fourier_eq_sine_integral]
  have hn : ((2 * a + 2 : ℕ) : ℝ) - 1 = ((2 * a : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hn, bessel_sine_integral hDLMF (2 * a) (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ)]
  have ht : -2 * Real.pi * ξ = -(2 * Real.pi * ξ) := by ring
  rw [ht, J_neg, pow_mul, Complex.I_sq]
  have hs : (-1 : ℝ) ^ (2 * a + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hs]
  push_cast
  field_simp [hξ, Real.pi_ne_zero]
  <;> ring

end DepthAspect.MurmurationFourier
