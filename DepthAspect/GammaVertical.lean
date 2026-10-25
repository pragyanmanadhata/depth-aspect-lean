import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinInversion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Decay and Mellin inversion for the actual Gamma function

Euler's convergent integral and the Gamma recurrence suffice for the contour
arguments needed here. In particular the initial vertical-line integrability
and the exponential Mellin inversion are proved without a Stirling premise.
-/

open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace DepthAspect.GammaVertical

/-- The imaginary part has modulus-one effect inside Euler's integral. -/
theorem norm_Gamma_le_Gamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  unfold Complex.GammaIntegral
  calc
    _ ≤ ∫ x : ℝ in Ioi 0, ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

/-- A finite product version of the Gamma recurrence, with the excluded
poles made explicit. -/
theorem Gamma_add_nat (z : ℂ) (n : ℕ)
    (hz : ∀ j ∈ Finset.range n, z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + (n : ℂ)) =
      (∏ j ∈ Finset.range n, (z + (j : ℂ))) * Complex.Gamma z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + (n : ℂ) ≠ 0 := hz n (Finset.mem_range.mpr (Nat.lt_succ_self n))
    have hp : ∀ j ∈ Finset.range n, z + (j : ℂ) ≠ 0 := by
      intro j hj
      exact hz j (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans (Nat.lt_succ_self n)))
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hn, ih hp,
      Finset.prod_range_succ]
    ring

/-- A concrete integrable majorant on the initial Mellin contour. -/
theorem norm_Gamma_one_add_I_mul_le (t : ℝ) :
    ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤ 2 / (1 + t ^ 2) := by
  let z : ℂ := 1 + (t : ℂ) * Complex.I
  have hz : ∀ j ∈ Finset.range 2, z + (j : ℂ) ≠ 0 := by
    intro j hj heq
    have he := congrArg Complex.re heq
    simp [z] at he
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hrec := Gamma_add_nat z 2 hz
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, add_zero, one_mul] at hrec
  have hzsq : ‖z‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, z, pow_two]
  have hz1sq : ‖z + 1‖ ^ 2 = 4 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, z, pow_two]
    ring
  have hnormle : ‖z‖ ≤ ‖z + 1‖ := by
    have h0 := norm_nonneg z
    have h1 := norm_nonneg (z + 1)
    nlinarith
  have hg : ‖Complex.Gamma (z + 2)‖ ≤ 2 := by
    have hb := norm_Gamma_le_Gamma_re (s := z + 2) (by norm_num [z])
    have hthree : Real.Gamma 3 = 2 := by
      simpa using Real.Gamma_nat_eq_factorial 2
    have hzre : (z + 2).re = 3 := by norm_num [z]
    rwa [hzre, hthree] at hb
  have hm : ‖Complex.Gamma z‖ * (1 + t ^ 2) ≤ 2 := by
    calc
      _ = ‖Complex.Gamma z‖ * (‖z‖ * ‖z‖) := by rw [← pow_two, hzsq]
      _ ≤ ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnormle (norm_nonneg z)) (norm_nonneg _)
      _ = ‖Complex.Gamma (z + 2)‖ := by
        rw [hrec, norm_mul, norm_mul]
        ring
      _ ≤ 2 := hg
  exact (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr hm

theorem Gamma_vertical_integrable_one : Complex.VerticalIntegrable Complex.Gamma 1 := by
  have hc : Continuous (fun t : ℝ => Complex.Gamma (1 + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro m he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self,
      add_zero, Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [div_eq_mul_inv] using norm_Gamma_one_add_I_mul_le t

/-- The exponential Mellin inversion used in the smoothing argument is now
an identity for Mathlib's actual Gamma function and actual Bochner integral. -/
theorem mellinInv_Gamma_one {x : ℝ} (hx : 0 < x) :
    mellinInv 1 Complex.Gamma x = (Real.exp (-x) : ℂ) := by
  let f : ℝ → ℂ := fun u => Real.exp (-u)
  have hm (t : ℝ) : mellin f (1 + (t : ℂ) * Complex.I) =
      Complex.Gamma (1 + (t : ℂ) * Complex.I) := by
    rw [Complex.Gamma_eq_integral (by simp)]
    exact (congrFun Complex.GammaIntegral_eq_mellin _).symm
  have hconv : MellinConvergent f (1 : ℂ) := by
    simpa [MellinConvergent, f, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent (s := (1 : ℂ)) (by norm_num))
  have hvert : Complex.VerticalIntegrable (mellin f) 1 := by
    simpa only [Complex.VerticalIntegrable, Complex.ofReal_one, hm] using
      Gamma_vertical_integrable_one
  calc
    mellinInv 1 Complex.Gamma x = mellinInv 1 (mellin f) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [Complex.ofReal_one]
      rw [hm]
    _ = f x := mellinInv_mellin_eq 1 f hx hconv hvert (by dsimp [f]; fun_prop)
    _ = _ := rfl

end DepthAspect.GammaVertical
