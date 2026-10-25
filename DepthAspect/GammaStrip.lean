import DepthAspect.GammaVertical
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open MeasureTheory Set
open scoped BigOperators
namespace DepthAspect.GammaStrip

open GammaVertical

/-- A compact real bound, obtained from the proved convexity of Gamma. -/
theorem Gamma_le_twenty_four {σ : ℝ} (hσ : σ ∈ Icc 1 5) :
    Real.Gamma σ ≤ 24 := by
  have hfive : Real.Gamma 5 = 24 := by
    convert Real.Gamma_nat_eq_factorial 4 using 1 <;> norm_num
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (5 : ℝ) ∈ Ioi 0 by norm_num) hσ
  calc
    Real.Gamma σ ≤ max (Real.Gamma 1) (Real.Gamma 5) := h
    _ = 24 := by rw [Real.Gamma_one, hfive]; norm_num

/-- The recurrence converts any common lower bound for its four factors
into a decay bound for the actual Gamma function. -/
theorem norm_Gamma_mul_lower_pow_le {z : ℂ} {r : ℝ}
    (hre : z.re ∈ Icc (-(1 / 2)) 1) (hr : 0 < r)
    (hfactor : ∀ j ∈ Finset.range 4, r ≤ ‖z + (j : ℂ)‖) :
    ‖Complex.Gamma z‖ * r ^ 4 ≤ 24 := by
  have hz : ∀ j ∈ Finset.range 4, z + (j : ℂ) ≠ 0 := by
    intro j hj
    exact norm_pos_iff.mp (hr.trans_le (hfactor j hj))
  have hrec := Gamma_add_nat z 4 hz
  simp only [Nat.cast_ofNat] at hrec
  have hshift : (z + 4).re ∈ Icc 1 5 := by
    change 1 ≤ z.re + 4 ∧ z.re + 4 ≤ 5
    constructor <;> linarith [hre.1, hre.2]
  have hΓ : ‖Complex.Gamma (z + 4)‖ ≤ 24 :=
    (norm_Gamma_le_Gamma_re (by linarith [hshift.1])).trans (Gamma_le_twenty_four hshift)
  have hp : r ^ 4 ≤ ∏ j ∈ Finset.range 4, ‖z + (j : ℂ)‖ := by
    calc
      r ^ 4 = ∏ _j ∈ Finset.range 4, r := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hr.le) hfactor
  calc
    _ ≤ ‖Complex.Gamma z‖ * ∏ j ∈ Finset.range 4, ‖z + (j : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ‖Complex.Gamma (z + 4)‖ := by
      rw [hrec, norm_mul, norm_prod]
      ring
    _ ≤ 24 := hΓ

/-- Uniform decay on the whole contour strip away from the real axis.
This supplies the horizontal-edge estimate without invoking Stirling. -/
theorem norm_Gamma_strip_le {σ t : ℝ}
    (hσ : σ ∈ Icc (-(1 / 2)) 1) (ht : 0 < |t|) :
    ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 24 / |t| ^ 4 := by
  apply (le_div_iff₀ (pow_pos ht 4)).mpr
  apply norm_Gamma_mul_lower_pow_le (by simpa using hσ) ht
  intro j hj
  simpa using Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I + (j : ℂ))

/-- On the shifted contour -1/2≤σ≤-1/4 every recurrence factor stays away
from zero. Combining this with its imaginary-part bound gives global decay. -/
theorem norm_Gamma_shifted_le {σ : ℝ} (hσ : σ ∈ Icc (-(1 / 2)) (-(1 / 4)))
    (t : ℝ) :
    ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      15000 / (1 + |t|) ^ 4 := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hfactor (j : ℕ) (hj : j ∈ Finset.range 4) :
      (1 + |t|) / 5 ≤ ‖z + (j : ℂ)‖ := by
    have him : |t| ≤ ‖z + (j : ℂ)‖ := by
      simpa [z] using Complex.abs_im_le_norm (z + (j : ℂ))
    have hre : |σ + (j : ℝ)| ≤ ‖z + (j : ℂ)‖ := by
      simpa [z] using Complex.abs_re_le_norm (z + (j : ℂ))
    have hquarter : 1 / 4 ≤ ‖z + (j : ℂ)‖ := by
      by_cases hj0 : j = 0
      · subst j
        simp only [Nat.cast_zero, add_zero] at hre ⊢
        have habs : -σ ≤ |σ| := neg_le_abs σ
        linarith [hσ.2]
      · have hj1 : (1 : ℝ) ≤ j := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hj0)
        have habs : σ + (j : ℝ) ≤ |σ + (j : ℝ)| := le_abs_self _
        linarith [hσ.1]
    nlinarith
  have hpos : 0 < (1 + |t|) / 5 := by positivity
  have h := norm_Gamma_mul_lower_pow_le (z := z)
    (by simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul,
      sub_self, add_zero]; exact ⟨hσ.1, by linarith [hσ.2]⟩) hpos hfactor
  have heq : ((1 + |t|) / 5) ^ 4 = (1 + |t|) ^ 4 / 625 := by ring
  rw [heq] at h
  apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 4)).mpr
  dsimp [z] at h
  nlinarith

/-- The same fourth-order majorant absorbs the small polynomial growth
of a primitive L-function on the shifted vertical line. -/
theorem Gamma_shifted_weight_integrable {σ η : ℝ}
    (hσ : σ ∈ Icc (-(1 / 2)) (-(1 / 4))) (hη : η ≤ 1) :
    Integrable (fun t : ℝ => ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
      (2 + |t|) ^ η) := by
  have hΓcont : Continuous (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    by_cases hm0 : m = 0
    · subst m
      simp only [Nat.cast_zero, neg_zero] at hre
      linarith [hσ.2]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
      linarith [hσ.1]
  have hbase : Continuous (fun t : ℝ => 2 + |t|) :=
    continuous_const.add continuous_abs
  have hweight : Continuous (fun t : ℝ => (2 + |t|) ^ η) :=
    hbase.rpow_const
      (fun t => Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 2 + |t|)))
  have hcont : Continuous (fun t : ℝ => ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
      (2 + |t|) ^ η) := hΓcont.norm.mul hweight
  have hdom : Integrable (fun t : ℝ => 30000 * (1 + |t|) ^ (-3 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := (3 : ℝ)) (by norm_num)).const_mul 30000
  apply hdom.mono' hcont.aestronglyMeasurable
  filter_upwards with t
  have hg := norm_Gamma_shifted_le hσ t
  have ht : (2 + |t|) ^ η ≤ 2 * (1 + |t|) := by
    calc
      _ ≤ (2 + |t|) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hη
      _ ≤ _ := by rw [Real.rpow_one]; linarith [abs_nonneg t]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (by positivity) _))]
  calc
    _ ≤ (15000 / (1 + |t|) ^ 4) * (2 * (1 + |t|)) :=
      mul_le_mul hg ht (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = 30000 * (1 + |t|) ^ (-3 : ℝ) := by
      have ht0 : 1 + |t| ≠ 0 := ne_of_gt (by positivity)
      rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
      field_simp [ht0] <;> ring

/-- The initial contour also has fourth-order decay, from four actual
recurrence factors. This is stronger than the inversion majorant. -/
theorem norm_Gamma_one_le (t : ℝ) :
    ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ ≤
      384 / (1 + |t|) ^ 4 := by
  let z : ℂ := 1 + (t : ℂ) * Complex.I
  have hfactor (j : ℕ) (hj : j ∈ Finset.range 4) :
      (1 + |t|) / 2 ≤ ‖z + (j : ℂ)‖ := by
    have him : |t| ≤ ‖z + (j : ℂ)‖ := by
      simpa [z] using Complex.abs_im_le_norm (z + (j : ℂ))
    have hre : |1 + (j : ℝ)| ≤ ‖z + (j : ℂ)‖ := by
      simpa [z] using Complex.abs_re_le_norm (z + (j : ℂ))
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have habs : 1 + (j : ℝ) ≤ |1 + (j : ℝ)| := le_abs_self _
    linarith
  have h := norm_Gamma_mul_lower_pow_le (z := z)
    (by norm_num [z]) (by positivity : 0 < (1 + |t|) / 2) hfactor
  have heq : ((1 + |t|) / 2) ^ 4 = (1 + |t|) ^ 4 / 16 := by ring
  rw [heq] at h
  apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 4)).mpr
  dsimp [z] at h
  nlinarith

/-- Polynomial L-function growth of exponent at most one is integrable
against the actual Gamma function on the initial contour. -/
theorem Gamma_one_weight_integrable {η : ℝ} (hη : η ≤ 1) :
    Integrable (fun t : ℝ => ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ *
      (2 + |t|) ^ η) := by
  have hΓcont : Continuous (fun t : ℝ => Complex.Gamma (1 + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbase : Continuous (fun t : ℝ => 2 + |t|) :=
    continuous_const.add continuous_abs
  have hweight : Continuous (fun t : ℝ => (2 + |t|) ^ η) :=
    hbase.rpow_const
      (fun t => Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 2 + |t|)))
  have hcont : Continuous (fun t : ℝ => ‖Complex.Gamma (1 + (t : ℂ) * Complex.I)‖ *
      (2 + |t|) ^ η) := hΓcont.norm.mul hweight
  have hdom : Integrable (fun t : ℝ => 768 * (1 + |t|) ^ (-3 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := (3 : ℝ)) (by norm_num)).const_mul 768
  apply hdom.mono' hcont.aestronglyMeasurable
  filter_upwards with t
  have ht : (2 + |t|) ^ η ≤ 2 * (1 + |t|) := by
    calc
      _ ≤ (2 + |t|) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hη
      _ ≤ _ := by rw [Real.rpow_one]; linarith [abs_nonneg t]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (by positivity) _))]
  calc
    _ ≤ (384 / (1 + |t|) ^ 4) * (2 * (1 + |t|)) :=
      mul_le_mul (norm_Gamma_one_le t) ht (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = 768 * (1 + |t|) ^ (-3 : ℝ) := by
      have ht0 : 1 + |t| ≠ 0 := ne_of_gt (by positivity)
      rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
      field_simp [ht0] <;> ring

end DepthAspect.GammaStrip
