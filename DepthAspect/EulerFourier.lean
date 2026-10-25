import DepthAspect.SatakeCoefficients
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Evaluation of a single Euler-factor integral

Every interchange below is for one fixed Euler factor and is justified by an
absolutely summable geometric majorant. No global prime sum is interchanged
with an integral on the critical line.
-/

open MeasureTheory
open scoped BigOperators FourierTransform
namespace DepthAspect.EulerFourier

noncomputable def phase (ξ x : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)

theorem norm_phase (ξ x : ℝ) : ‖phase ξ x‖ = 1 := by
  simp [phase, Complex.norm_exp]

theorem phase_continuous (ξ : ℝ) : Continuous (phase ξ) := by
  unfold phase
  fun_prop

theorem phase_nat_mul (j : ℕ) (ξ x : ℝ) :
    phase ((j : ℝ) * ξ) x = phase ξ x ^ j := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem integrable_mode {φ : ℝ → ℂ} (hφ : Integrable φ) (ξ : ℝ) :
    Integrable (fun x => phase ξ x * φ x) := by
  apply hφ.norm.mono'
    ((phase_continuous ξ).aestronglyMeasurable.mul hφ.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖phase ξ x * φ x‖ ≤ ‖φ x‖
  rw [norm_mul, norm_phase, one_mul]

theorem integral_mode (φ : ℝ → ℂ) (ξ : ℝ) :
    (∫ x, phase ξ x * φ x) = 𝓕 φ ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rfl

/-- An absolutely summable Fourier series may be paired termwise with an
integrable test. The summability assumption will be proved geometrically for
the actual Euler coefficients in the specialization below. -/
theorem integral_series (φ : ℝ → ℂ) (hφ : Integrable φ)
    (c : ℕ → ℂ) (ξ : ℕ → ℝ) (hc : Summable c) :
    (∫ x, ∑' j, c j * (phase (ξ j) x * φ x)) =
      ∑' j, c j * 𝓕 φ (ξ j) := by
  have hi : ∀ j, Integrable (fun x => c j * (phase (ξ j) x * φ x)) :=
    fun j => (integrable_mode hφ (ξ j)).const_mul (c j)
  have hn : ∀ j, (∫ x, ‖c j * (phase (ξ j) x * φ x)‖) =
      ‖c j‖ * ∫ x, ‖φ x‖ := by
    intro j
    simp only [norm_mul, norm_phase, one_mul]
    exact integral_const_mul _ _
  have hs : Summable (fun j => ∫ x, ‖c j * (phase (ξ j) x * φ x)‖) := by
    simp_rw [hn]
    exact hc.norm.mul_right _
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  apply tsum_congr
  intro j
  rw [integral_const_mul, integral_mode]

noncomputable def geometricCoefficient (α β : ℂ) (r : ℝ) (j : ℕ) : ℂ :=
  SatakeCoefficients.powerCoefficient α β (j + 1) * (r : ℂ) ^ (j + 1)

/-- The actual degree-two Euler coefficients have an absolutely summable
majorant at every radius strictly inside the unit disk. -/
theorem geometricCoefficient_summable (α β : ℂ) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (geometricCoefficient α β r) := by
  have hg : Summable (fun j : ℕ => (2 : ℝ) * r ^ (j + 1)) :=
    ((summable_geometric_of_lt_one hr0 hr1).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left 2
  apply hg.of_norm_bounded
  intro j
  unfold geometricCoefficient
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact mul_le_mul_of_nonneg_right
    (SatakeCoefficients.norm_powerCoefficient_le_two α β hα hβ (j + 1)) (by positivity)

noncomputable def localRational (α β : ℂ) (r ξ x : ℝ) : ℂ :=
  (α * (r : ℂ) * phase ξ x) / (1 - α * (r : ℂ) * phase ξ x) +
  (β * (r : ℂ) * phase ξ x) / (1 - β * (r : ℂ) * phase ξ x)

/-- The rational Euler-factor expression is the sum of its actual geometric
series; this is a local identity, before any sum over primes. -/
theorem localRational_hasSum (α β : ℂ) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ξ x : ℝ) :
    HasSum (fun j : ℕ => geometricCoefficient α β r j * phase (((j + 1 : ℕ) : ℝ) * ξ) x)
      (localRational α β r ξ x) := by
  have hnorm (a : ℂ) (ha : ‖a‖ = 1) : ‖a * (r : ℂ) * phase ξ x‖ < 1 := by
    simpa [norm_mul, ha, norm_phase, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0] using hr1
  have hg (a : ℂ) (ha : ‖a‖ = 1) :
      HasSum (fun j : ℕ => (a * (r : ℂ) * phase ξ x) ^ (j + 1))
        ((a * (r : ℂ) * phase ξ x) / (1 - a * (r : ℂ) * phase ξ x)) := by
    simpa only [pow_succ', div_eq_mul_inv] using
      (hasSum_geometric_of_norm_lt_one (hnorm a ha)).mul_left (a * (r : ℂ) * phase ξ x)
  convert (hg α hα).add (hg β hβ) using 1
  · funext j
    rw [phase_nat_mul]
    simp only [geometricCoefficient, SatakeCoefficients.powerCoefficient, mul_pow]
    ring
  · rfl

/-- Fourier evaluation of the local integral, with all convergence conditions
proved from the unit Satake roots and an integrable test. -/
theorem integral_localRational (φ : ℝ → ℂ) (hφ : Integrable φ)
    (α β : ℂ) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ξ : ℝ) :
    (∫ x, localRational α β r ξ x * φ x) =
      ∑' j : ℕ, geometricCoefficient α β r j * 𝓕 φ (((j + 1 : ℕ) : ℝ) * ξ) := by
  calc
    _ = ∫ x, ∑' j : ℕ,
        geometricCoefficient α β r j * (phase (((j + 1 : ℕ) : ℝ) * ξ) x * φ x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact ((localRational_hasSum α β hα hβ hr0 hr1 ξ x).mul_right (φ x)).tsum_eq.symm.trans
        (tsum_congr fun j => by ring)
    _ = _ := integral_series φ hφ _ _ (geometricCoefficient_summable α β hα hβ hr0 hr1)

end DepthAspect.EulerFourier
