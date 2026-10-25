import DepthAspect.GammaVertical
import DepthAspect.DigammaBound
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Group.Ext
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Exponential smoothing as an actual Mellin integral

The series/integral exchange is proved using the literal coefficient bound,
the summable inverse-square sequence, and the actual Gamma integral. No
Mellin representation of the smoothed L-series is assumed.
-/

open Filter MeasureTheory
open scoped Topology BigOperators
namespace DepthAspect.MellinSmoothing

noncomputable def verticalPoint (t : ℝ) : ℂ := 1 + (t : ℂ) * Complex.I
noncomputable def smoothedTerm (a : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  a (n + 1) / (n + 1 : ℕ) * (Real.exp (-((n + 1 : ℕ) : ℝ) / x) : ℂ)
noncomputable def mellinTerm (a : ℕ → ℂ) (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (a (n + 1) / (n + 1 : ℕ)) *
    (((((n + 1 : ℕ) : ℝ) / x) : ℝ) : ℂ) ^ (-verticalPoint t) *
      Complex.Gamma (verticalPoint t)
noncomputable def initialIntegral (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ,
    Complex.Gamma (verticalPoint t) * LSeries a (1 + verticalPoint t) *
      (x : ℂ) ^ verticalPoint t

/-- The positive-real quotient has no branch ambiguity. -/
theorem quotient_cpow {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (w : ℂ) :
    ((u / x : ℝ) : ℂ) ^ (-w) = (u : ℂ) ^ (-w) * (x : ℂ) ^ w := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxarg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hu.le (inv_nonneg.mpr hx.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ hxarg, Complex.cpow_neg (x : ℂ) w, inv_inv]

/-- Each summand is exactly a Gamma-weighted Dirichlet-series term. -/
theorem mellinTerm_eq (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    mellinTerm a x n t = LSeries.term a (1 + verticalPoint t) (n + 1) *
      (Complex.Gamma (verticalPoint t) * (x : ℂ) ^ verticalPoint t) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold mellinTerm
  rw [quotient_cpow (by positivity : (0 : ℝ) < (n + 1 : ℕ)) hx,
    LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_add _ _ (by exact_mod_cast Nat.succ_ne_zero n),
    Complex.cpow_one, Complex.cpow_neg]
  push_cast
  field_simp

/-- The exact norm exposes a summable inverse-square majorant. -/
theorem norm_mellinTerm_le (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) (n : ℕ) (t : ℝ) :
    ‖mellinTerm a x n t‖ ≤
      (x * DigammaBound.inverseSquare n) * ‖Complex.Gamma (verticalPoint t)‖ := by
  have hnR : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  unfold mellinTerm
  rw [norm_mul, norm_mul, norm_div, Complex.norm_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hnR hx)]
  have hre : (-verticalPoint t).re = -1 := by simp [verticalPoint]
  rw [hre, Real.rpow_neg_one]
  calc
    _ ≤ (1 / ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) / x)⁻¹) *
        ‖Complex.Gamma (verticalPoint t)‖ := by gcongr; exact ha (n + 1)
    _ = _ := by
      unfold DigammaBound.inverseSquare
      push_cast
      field_simp [hx.ne']

theorem mellinTerm_integrable (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) (n : ℕ) : Integrable (mellinTerm a x n) := by
  have hbase : (((((n + 1 : ℕ) : ℝ) / x) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) hx.ne')
  have hc : Continuous (fun t : ℝ =>
      (a (n + 1) / (n + 1 : ℕ)) *
        (((((n + 1 : ℕ) : ℝ) / x) : ℝ) : ℂ) ^ (-verticalPoint t)) := by
    have hv : Continuous (fun t : ℝ => -verticalPoint t) := by
      unfold verticalPoint
      fun_prop
    exact continuous_const.mul (hv.const_cpow (Or.inl hbase))
  have hm : AEStronglyMeasurable (mellinTerm a x n) :=
    hc.aestronglyMeasurable.mul GammaVertical.Gamma_vertical_integrable_one.aestronglyMeasurable
  apply (GammaVertical.Gamma_vertical_integrable_one.norm.const_mul
    (x * DigammaBound.inverseSquare n)).mono' hm
  filter_upwards with t
  exact norm_mellinTerm_le a ha hx n t

theorem summable_integral_norm (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ∫ t : ℝ, ‖mellinTerm a x n t‖) := by
  have hΓ := GammaVertical.Gamma_vertical_integrable_one.norm
  apply (DigammaBound.inverseSquare_summable.mul_left
    (x * ∫ t : ℝ, ‖Complex.Gamma (verticalPoint t)‖)).of_nonneg_of_le
  · intro n
    exact integral_nonneg (fun t => norm_nonneg _)
  · intro n
    calc
      _ ≤ ∫ t : ℝ, (x * DigammaBound.inverseSquare n) *
          ‖Complex.Gamma (verticalPoint t)‖ :=
        integral_mono (mellinTerm_integrable a ha hx n).norm (hΓ.const_mul _)
          (fun t => norm_mellinTerm_le a ha hx n t)
      _ = _ := by rw [integral_const_mul]; ring

/-- Evaluation of each actual Mellin integral uses the proved exponential
Gamma inversion, with argument `(n+1)/x`. -/
theorem integral_mellinTerm (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t : ℝ, mellinTerm a x n t) =
      smoothedTerm a x n := by
  have hr : 0 < ((n + 1 : ℕ) : ℝ) / x := div_pos (by positivity) hx
  have h := GammaVertical.mellinInv_Gamma_one hr
  unfold mellinInv at h
  simp only [smul_eq_mul, Complex.real_smul, one_div] at h
  unfold mellinTerm smoothedTerm
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have he : -(((n + 1 : ℕ) : ℝ) / x) = -((n + 1 : ℕ) : ℝ) / x := (neg_div _ _).symm
  rw [← he]
  calc
    _ = (a (n + 1) / (n + 1 : ℕ)) *
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ,
          (((((n + 1 : ℕ) : ℝ) / x) : ℝ) : ℂ) ^ (-verticalPoint t) *
            Complex.Gamma (verticalPoint t)) := by ring
    _ = _ := by rw [show ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t : ℝ, (((((n + 1 : ℕ) : ℝ) / x) : ℝ) : ℂ) ^ (-verticalPoint t) *
          Complex.Gamma (verticalPoint t)) =
        (Real.exp (-(((n + 1 : ℕ) : ℝ) / x)) : ℂ) from by simpa [verticalPoint] using h]

/-- The pointwise series equals the literal L-series on the absolutely
convergent initial line. -/
theorem hasSum_mellinTerm (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    HasSum (fun n : ℕ => mellinTerm a x n t)
      (Complex.Gamma (verticalPoint t) * LSeries a (1 + verticalPoint t) *
        (x : ℂ) ^ verticalPoint t) := by
  have hs : LSeriesSummable a (1 + verticalPoint t) :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => ha n) (by simp [verticalPoint])
  have hshift : HasSum (fun n : ℕ => LSeries.term a (1 + verticalPoint t) (n + 1))
      (LSeries a (1 + verticalPoint t)) := by
    apply (hasSum_nat_add_iff 1).mpr
    have hfull : HasSum (LSeries.term a (1 + verticalPoint t))
        (LSeries a (1 + verticalPoint t)) := by
      convert hs.hasSum using 1 <;> first
        | exact AddCommMonoid.ext rfl
        | rfl
    simpa only [Finset.sum_range_one, LSeries.term_zero, add_zero] using hfull
  convert! hshift.mul_right (Complex.Gamma (verticalPoint t) * (x : ℂ) ^ verticalPoint t) using 1
  · funext n
    exact mellinTerm_eq a hx n t
  · ring

/-- The exponentially smoothed Dirichlet series is the actual initial
Mellin integral. Absolute convergence and exchange have been established
from `‖a(n)‖≤1`, with no smoothing formula supplied as a hypothesis. -/
theorem smoothed_hasSum_initialIntegral (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    HasSum (smoothedTerm a x) (initialIntegral a x) := by
  have hF := hasSum_integral_of_summable_integral_norm
    (mellinTerm_integrable a ha hx) (summable_integral_norm a ha hx)
  have hlim := hF.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  convert! hlim using 1
  · funext n
    exact (integral_mellinTerm a hx n).symm
  · unfold initialIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    exact (hasSum_mellinTerm a ha hx t).tsum_eq.symm

theorem smoothed_eq_initialIntegral (a : ℕ → ℂ) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, smoothedTerm a x n) = initialIntegral a x :=
  (smoothed_hasSum_initialIntegral a ha hx).tsum_eq

end DepthAspect.MellinSmoothing
