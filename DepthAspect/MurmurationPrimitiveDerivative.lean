import DepthAspect.MurmurationStepPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Local continuity of the literal density and differentiation of its
actual bounded primitive away from the single step endpoint. -/
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace DepthAspect.MurmurationPrimitiveDerivative
open MurmurationKernel MurmurationLattice MurmurationArithmetic
open MurmurationArithmeticIntegral MurmurationPrimitive MurmurationStepPrimitive BesselFirstKind

/-- One finite integer set controls all lattice supports up to a fixed
positive height. This is independent of any cancellation inside the kernel. -/
theorem uniform_lattice_support (k : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {U : ℝ} (hU : 0 < U) :
    ∃ S : Finset ℤ, ∀ y : ℝ, 0 < y → y ≤ U → ∀ r : ℤ, r ∉ S →
      kernel k ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y)) = 0 := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * (ℓ : ℝ) * Real.sqrt U)
  refine ⟨Finset.Icc (-(K : ℤ)) (K : ℤ), ?_⟩
  intro y hy hyU r hr
  have hrK : (K : ℤ) ≤ |r| := by
    simp only [Finset.mem_Icc, not_and_or] at hr
    rcases hr with h | h
    · exact (by omega : (K : ℤ) ≤ -r).trans (neg_le_abs r)
    · exact (by omega : (K : ℤ) ≤ r).trans (le_abs_self r)
  have hrR : (K : ℝ) ≤ |(r : ℝ)| := by exact_mod_cast hrK
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hR : 0 < 2 * (ℓ : ℝ) * Real.sqrt y := by positivity
  apply kernel_zero_of_one_le_abs
  rw [abs_div, abs_of_pos hR]
  apply (le_div_iff₀ hR).mpr
  have hs := Real.sqrt_le_sqrt hyU
  nlinarith

/-- Local finiteness and continuity of the zero-extended kernel give
continuity of every fixed weighted density at every positive argument. -/
theorem weightedDensity_continuousAt (a : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (w : ℤ → ℝ) {V : ℝ} (hV : 0 < V) : ContinuousAt (weightedDensity a ℓ w) V := by
  obtain ⟨S, hS⟩ := uniform_lattice_support (2 * a + 2) hℓ
    (show 0 < V + 1 by linarith)
  let F : ℝ → ℝ := fun y =>
    ((-1 : ℝ) ^ a * (2 * Real.pi * Real.sqrt y) /
      ((((2 * a + 1 : ℕ) : ℝ)) * (1 - (ℓ : ℝ)⁻¹))) *
      ∑ r ∈ S, residueWeight ℓ r * w r *
        kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hF : ContinuousAt F V := by
    dsimp only [F]
    apply ContinuousAt.mul
    · fun_prop
    · apply tendsto_finsetSum S
      intro r _
      apply continuousAt_const.mul
      apply (kernel_continuous _).continuousAt.comp
      exact continuousAt_const.div (by fun_prop) (by positivity)
  apply hF.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hV (show V < V + 1 by linarith)] with y hy
  unfold weightedDensity F
  congr 1
  apply tsum_eq_sum
  intro r hr
  rw [hS y hy.1 hy.2.le r hr, mul_zero]

theorem M_continuousAt (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {V : ℝ} (hV : 0 < V) : ContinuousAt (M a ℓ) V :=
  weightedDensity_continuousAt a hℓ.pos (ArithmeticWeights.integerPrimeWeight ℓ) hV

/-- The derivative used in (115) is the actual logarithmic integrand;
only the genuine jump point V=1 is excluded. -/
theorem P_hasDerivAt (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {V : ℝ} (hV : 0 < V) (hV1 : V ≠ 1) :
    HasDerivAt (P a ℓ) ((M a ℓ V - step V) / V) V := by
  have hm : StronglyMeasurableAtFilter (fun y => M a ℓ y / y) (𝓝 V) :=
    ((M_measurable a ℓ).div measurable_id).aestronglyMeasurable.stronglyMeasurableAtFilter
  have hc : ContinuousAt (fun y => M a ℓ y / y) V :=
    (M_continuousAt a hℓ hV).div continuousAt_id (ne_of_gt hV)
  have hi := intervalIntegral.integral_hasDerivAt_right
    (M_log_intervalIntegrable hDLMF a hℓ hV.le) hm hc
  rcases lt_or_gt_of_ne hV1 with hlt | hgt
  · have he : P a ℓ =ᶠ[𝓝 V] (fun u => ∫ y : ℝ in (0)..u, M a ℓ y / y) := by
      filter_upwards [eventually_lt_nhds hlt] with u hu
      simp [P, max_eq_left hu.le]
    simpa only [step, if_neg (not_le.mpr hlt), sub_zero] using hi.congr_of_eventuallyEq he
  · have hd := hi.sub ((Real.hasDerivAt_log (ne_of_gt hV)).const_mul (1 / 2 : ℝ))
    have he : P a ℓ =ᶠ[𝓝 V] (fun u =>
        (∫ y : ℝ in (0)..u, M a ℓ y / y) - (1 / 2 : ℝ) * Real.log u) := by
      filter_upwards [eventually_gt_nhds hgt] with u hu
      simp only [P, max_eq_right hu.le]
    have hvalue : (M a ℓ V - step V) / V =
        M a ℓ V / V - (1 / 2 : ℝ) * V⁻¹ := by
      simp only [step, if_pos hgt.le, div_eq_mul_inv]
      ring
    rw [hvalue]
    exact hd.congr_of_eventuallyEq he

end DepthAspect.MurmurationPrimitiveDerivative
