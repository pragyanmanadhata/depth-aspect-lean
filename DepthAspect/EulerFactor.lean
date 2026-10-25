import DepthAspect.EulerFourier
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Actual local Euler factors and their logarithmic derivatives

The unit-root input is the cited Deligne normalization. The local factors,
their absence of poles on Re(s)>0, their logarithmic derivatives and the
central-line Fourier evaluation are proved from that input.
-/

namespace DepthAspect.EulerFactor
open MeasureTheory EulerFourier
open scoped FourierTransform

noncomputable def rootTerm (p : ℝ) (α z : ℂ) : ℂ :=
  α * Complex.exp (-z * (Real.log p : ℂ))

noncomputable def localFactor (p : ℝ) (α β z : ℂ) : ℂ :=
  (1 - rootTerm p α z)⁻¹ * (1 - rootTerm p β z)⁻¹

theorem rootTerm_hasDerivAt (p : ℝ) (α z : ℂ) :
    HasDerivAt (rootTerm p α) (-(Real.log p : ℂ) * rootTerm p α z) z := by
  unfold rootTerm
  apply (((((hasDerivAt_id z).neg).mul_const (Real.log p : ℂ)).cexp).const_mul α).congr_deriv
  dsimp only [Pi.neg_apply, id_eq]
  ring

theorem rootTerm_norm (p : ℝ) (α z : ℂ) (hα : ‖α‖ = 1) :
    ‖rootTerm p α z‖ = Real.exp (-z.re * Real.log p) := by
  simp [rootTerm, norm_mul, hα, Complex.norm_exp, Complex.mul_re]

theorem rootTerm_norm_lt_one {p : ℝ} (hp : 1 < p) (α z : ℂ)
    (hα : ‖α‖ = 1) (hz : 0 < z.re) : ‖rootTerm p α z‖ < 1 := by
  rw [rootTerm_norm p α z hα, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  nlinarith [Real.log_pos hp]

theorem local_denominator_ne_zero {p : ℝ} (hp : 1 < p) (α z : ℂ)
    (hα : ‖α‖ = 1) (hz : 0 < z.re) : 1 - rootTerm p α z ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have ht := rootTerm_norm_lt_one hp α z hα hz
  rw [← h, norm_one] at ht
  exact (lt_irrefl (1 : ℝ)) ht

theorem localFactor_ne_zero {p : ℝ} (hp : 1 < p) (α β z : ℂ)
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hz : 0 < z.re) :
    localFactor p α β z ≠ 0 :=
  mul_ne_zero (inv_ne_zero (local_denominator_ne_zero hp α z hα hz))
    (inv_ne_zero (local_denominator_ne_zero hp β z hβ hz))

/-- The actual factor is holomorphic throughout the required strip. -/
theorem localFactor_hasDerivAt {p : ℝ} (hp : 1 < p) (α β z : ℂ)
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hz : 0 < z.re) :
    HasDerivAt (localFactor p α β)
      (-(Real.log p : ℂ) *
        (rootTerm p α z / (1 - rootTerm p α z) +
          rootTerm p β z / (1 - rootTerm p β z)) * localFactor p α β z) z := by
  have ha := local_denominator_ne_zero hp α z hα hz
  have hb := local_denominator_ne_zero hp β z hβ hz
  have hd := (((rootTerm_hasDerivAt p α z).const_sub 1).inv ha).mul
    (((rootTerm_hasDerivAt p β z).const_sub 1).inv hb)
  apply hd.congr_deriv
  dsimp only [Pi.inv_apply]
  unfold localFactor
  field_simp [ha, hb]
  <;> ring

/-- The logarithmic derivative is evaluated algebraically from the derivative
of the Euler factor; no Euler-series derivative formula is assumed. -/
theorem localFactor_logDeriv {p : ℝ} (hp : 1 < p) (α β z : ℂ)
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hz : 0 < z.re) :
    deriv (localFactor p α β) z / localFactor p α β z =
      -(Real.log p : ℂ) *
        (rootTerm p α z / (1 - rootTerm p α z) +
          rootTerm p β z / (1 - rootTerm p β z)) := by
  rw [(localFactor_hasDerivAt hp α β z hα hβ hz).deriv,
    mul_div_cancel_right₀ _ (localFactor_ne_zero hp α β z hα hβ hz)]

/-- The exponential radial factor on Re(s)=1/2 is exactly p^(-1/2). -/
theorem rootTerm_critical {p : ℝ} (hp : 0 < p) (α : ℂ) (L x : ℝ) :
    rootTerm p α ((1 / 2 : ℂ) + Complex.I * (2 * Real.pi * x / L : ℝ)) =
      α * ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * phase (Real.log p / L) x := by
  unfold rootTerm phase
  have he : -((1 / 2 : ℂ) + Complex.I * (2 * Real.pi * x / L : ℝ)) *
      (Real.log p : ℂ) = ((Real.log p * (-(1 / 2 : ℝ)) : ℝ) : ℂ) +
        ((-2 * Real.pi * x * (Real.log p / L) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.rpow_def_of_pos hp]
  ring

/-- The actual logarithmic-derivative expression on the central line is the
rational local function evaluated in `EulerFourier`. -/
theorem localFactor_logDeriv_critical {p : ℝ} (hp : 1 < p) (α β : ℂ)
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (L x : ℝ) :
    deriv (localFactor p α β)
        ((1 / 2 : ℂ) + Complex.I * (2 * Real.pi * x / L : ℝ)) /
      localFactor p α β ((1 / 2 : ℂ) + Complex.I * (2 * Real.pi * x / L : ℝ)) =
    -(Real.log p : ℂ) * localRational α β (p ^ (-(1 / 2 : ℝ))) (Real.log p / L) x := by
  have hz : 0 < (((1 / 2 : ℂ) + Complex.I * (2 * Real.pi * x / L : ℝ))).re := by
    norm_num [Complex.mul_re]
  rw [localFactor_logDeriv hp α β _ hα hβ hz,
    rootTerm_critical (zero_lt_one.trans hp), rootTerm_critical (zero_lt_one.trans hp)]
  rfl


/-- The geometric coefficient on the critical line is the paper's literal
prime-power coefficient divided by p^(j/2). -/
theorem geometricCoefficient_critical {p : ℝ} (hp : 0 < p) (α β : ℂ) (j : ℕ) :
    geometricCoefficient α β (p ^ (-(1 / 2 : ℝ))) j =
      SatakeCoefficients.powerCoefficient α β (j + 1) /
        ((p ^ (((j + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
  unfold geometricCoefficient
  have he : (p ^ (-(1 / 2 : ℝ))) ^ (j + 1) =
      (p ^ (((j + 1 : ℕ) : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_mul_natCast hp.le, ← Real.rpow_neg hp.le]
    congr 1
    ring
  rw [← Complex.ofReal_pow, he, Complex.ofReal_inv]
  simp only [div_eq_mul_inv]

/-- Each odd-prime local integral evaluates to the actual finite-support
Fourier expression used in the explicit formula. Absolute convergence here
is obtained separately for each local factor. -/
theorem integral_local_logDeriv_critical {p : ℝ} (hp : 1 < p)
    (α β : ℂ) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ) (L : ℝ) :
    (∫ x, (deriv (localFactor p α β)
        ((1 / 2 : ℂ) + Complex.I * (2 * Real.pi * x / L : ℝ)) /
      localFactor p α β ((1 / 2 : ℂ) + Complex.I * (2 * Real.pi * x / L : ℝ))) * φ x) =
    -(Real.log p : ℂ) * ∑' j : ℕ,
      SatakeCoefficients.powerCoefficient α β (j + 1) /
        ((p ^ (((j + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
          𝓕 φ (((j + 1 : ℕ) : ℝ) * Real.log p / L) := by
  have hr0 : 0 ≤ p ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (zero_lt_one.trans hp).le _
  have hr1 : p ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  simp_rw [localFactor_logDeriv_critical hp α β hα hβ, mul_assoc]
  rw [MeasureTheory.integral_const_mul,
    integral_localRational φ hφ α β hα hβ hr0 hr1]
  congr 1
  apply tsum_congr
  intro j
  rw [geometricCoefficient_critical (zero_lt_one.trans hp)]
  congr 2
  ring

end DepthAspect.EulerFactor
