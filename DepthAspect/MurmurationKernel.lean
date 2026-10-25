import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The actual compactly supported Chebyshev kernel

This globally continuous formula equals (106), including its boundary
values, because the real square root vanishes for nonpositive arguments.
-/
open Set MeasureTheory
namespace DepthAspect.MurmurationKernel
open Polynomial.Chebyshev

noncomputable def kernel (k : ℕ) (u : ℝ) : ℝ :=
  (U ℝ ((k : ℤ) - 2)).eval u * Real.sqrt (1 - u ^ 2)

theorem kernel_continuous (k : ℕ) : Continuous (kernel k) := by
  unfold kernel
  exact (U ℝ ((k : ℤ) - 2)).continuous.mul (by fun_prop)

/-- This proves equality to the paper's zero extension, including ±1. -/
theorem kernel_zero_of_one_le_abs (k : ℕ) {u : ℝ} (hu : 1 ≤ |u|) : kernel k u = 0 := by
  have hs : 1 ≤ u ^ 2 := by nlinarith [sq_abs u]
  simp [kernel, Real.sqrt_eq_zero_of_nonpos (by linarith : 1 - u ^ 2 ≤ 0)]

theorem kernel_support_subset (k : ℕ) : Function.support (kernel k) ⊆ Ioo (-1) 1 := by
  intro u hu
  by_contra hn
  have habs : 1 ≤ |u| := by
    rw [mem_Ioo, not_and_or] at hn
    rcases hn with h | h
    · exact (by linarith : (1 : ℝ) ≤ -u).trans (neg_le_abs u)
    · exact (le_of_not_gt h).trans (le_abs_self u)
  exact hu (kernel_zero_of_one_le_abs k habs)

theorem kernel_hasCompactSupport (k : ℕ) : HasCompactSupport (kernel k) := by
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal ((kernel_support_subset k).trans Ioo_subset_Icc_self) isClosed_Icc

/-- The defining sine identity holds for the literal kernel throughout its
closed support, so all endpoint limits are controlled. -/
theorem kernel_eq_sin_arccos (k : ℕ) {u : ℝ} (hu : u ∈ Icc (-1) 1) :
    kernel k u = Real.sin (((k : ℝ) - 1) * Real.arccos u) := by
  have h := U_real_cos (Real.arccos u) ((k : ℤ) - 2)
  rw [Real.cos_arccos hu.1 hu.2, Real.sin_arccos] at h
  unfold kernel
  convert h using 2 <;> push_cast <;> ring

theorem kernel_abs_le_one (k : ℕ) (u : ℝ) : |kernel k u| ≤ 1 := by
  by_cases hu : u ∈ Icc (-1) 1
  · rw [kernel_eq_sin_arccos k hu]
    exact Real.abs_sin_le_one _
  · have habs : 1 ≤ |u| := by
      rw [mem_Icc, not_and_or] at hu
      rcases hu with h | h
      · exact (by linarith : (1 : ℝ) ≤ -u).trans (neg_le_abs u)
      · exact (by linarith : (1 : ℝ) ≤ u).trans (le_abs_self u)
    rw [kernel_zero_of_one_le_abs k habs]
    norm_num

theorem kernel_integrable (k : ℕ) : Integrable (kernel k) :=
  (kernel_continuous k).integrable_of_hasCompactSupport (kernel_hasCompactSupport k)

/-- The zero lattice point has precisely the sign in (106). -/
theorem kernel_zero (a : ℕ) : kernel (2 * a + 2) 0 = (-1 : ℝ) ^ a := by
  have he : ((2 * a + 2 : ℕ) : ℤ) - 2 = 2 * (a : ℤ) := by omega
  simp only [kernel, he, U_eval_two_mul_zero, Int.cast_negOnePow_natCast,
    zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_one, mul_one]

/-- Even weight gives an even kernel, as needed for negative Fourier frequencies. -/
theorem kernel_even {k : ℕ} (hk : 2 ≤ k) (heven : Even k) : Function.Even (kernel k) := by
  have hcast : ((k - 2 : ℕ) : ℤ) = (k : ℤ) - 2 := by omega
  have hkZ : Even (k : ℤ) := by exact_mod_cast heven
  have hnZ : Even ((k - 2 : ℕ) : ℤ) := by
    rw [hcast]
    exact hkZ.sub (by decide : Even (2 : ℤ))
  intro u
  unfold kernel
  rw [← hcast, U_eval_neg, Int.negOnePow_even _ hnZ]
  simp

end DepthAspect.MurmurationKernel
