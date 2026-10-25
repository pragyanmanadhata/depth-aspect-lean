import DepthAspect.FourierDecay
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FieldSimp

/-!
# Absolute convergence of the zero sum

The only zero-counting input is the standard global count O(T log(BT)).
Zeros are indexed with multiplicity, and their transformed ordinates may be
complex. No Riemann hypothesis for the modular-form L-function is imposed.
-/
open scoped BigOperators FourierTransform SchwartzMap
namespace DepthAspect.ZeroSumConvergence

/-- Polynomial decay on bins with quadratic counting growth gives genuine
absolute summability, even for an arbitrary index type. -/
theorem summable_of_bin_count {ι : Type*} (bin : ι → ℕ) (a : ι → ℂ)
    {Q K : ℝ} (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hcount : ∀ (S : Finset ι) (n : ℕ),
      ((S.filter (fun i => bin i = n)).card : ℝ) ≤ Q * ((n : ℝ) + 1) ^ 2)
    (hdecay : ∀ i, ‖a i‖ ≤ K / ((bin i : ℝ) + 1) ^ 4) :
    Summable (fun i => ‖a i‖) := by
  classical
  let b : ℕ → ℝ := fun n => Q * K / ((n : ℝ) + 1) ^ 2
  have hb : Summable b := by
    have hp := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_right_cancel h)
    simpa only [b, Function.comp_apply, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
      one_mul, mul_assoc]
      using hp.mul_left (Q * K)
  apply summable_of_sum_le (fun i => norm_nonneg (a i))
    (c := ∑' n : ℕ, b n)
  intro S
  calc
    ∑ i ∈ S, ‖a i‖ = ∑ n ∈ S.image bin,
        ∑ i ∈ S.filter (fun i => bin i = n), ‖a i‖ :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem bin hi) _).symm
    _ ≤ ∑ n ∈ S.image bin, b n := by
      apply Finset.sum_le_sum
      intro n _
      calc
        _ ≤ ∑ i ∈ S.filter (fun i => bin i = n), K / ((n : ℝ) + 1) ^ 4 := by
          apply Finset.sum_le_sum
          intro i hi
          simpa only [(Finset.mem_filter.mp hi).2] using hdecay i
        _ = ((S.filter (fun i => bin i = n)).card : ℝ) *
            (K / ((n : ℝ) + 1) ^ 4) := by simp
        _ ≤ (Q * ((n : ℝ) + 1) ^ 2) * (K / ((n : ℝ) + 1) ^ 4) :=
          mul_le_mul_of_nonneg_right (hcount S n) (by positivity)
        _ = b n := by
          dsimp [b]
          have hn : (n : ℝ) + 1 ≠ 0 := by positivity
          field_simp
          <;> ring
    _ ≤ ∑' n : ℕ, b n := hb.sum_le_tsum _ (fun n _ => by dsimp [b]; positivity)

noncomputable def heightBin (z : ℂ) : ℕ := ⌊|z.re|⌋₊

/-- The usual T log(BT) count implies the quadratic bound on each unit bin.
The sets `zerosUpTo` record the actual multiset indices, not just distinct zeros. -/
theorem bin_count_of_zero_count {ι : Type*} [DecidableEq ι] (γ : ι → ℂ)
    (zerosUpTo : ℝ → Finset ι)
    (hmem : ∀ i T, i ∈ zerosUpTo T ↔ |(γ i).re| ≤ T)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B)
    (hcount : ∀ T : ℝ, 1 ≤ T → (zerosUpTo T).card ≤ C * T * Real.log (B * T))
    (S : Finset ι) (n : ℕ) :
    ((S.filter (fun i => heightBin (γ i) = n)).card : ℝ) ≤
      (C * (Real.log B + 1)) * ((n : ℝ) + 1) ^ 2 := by
  classical
  have hT : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hT0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hsub : S.filter (fun i => heightBin (γ i) = n) ⊆ zerosUpTo ((n : ℝ) + 1) := by
    intro i hi
    apply (hmem i _).mpr
    have hi' := (Finset.mem_filter.mp hi).2
    have hlt := Nat.lt_floor_add_one |(γ i).re|
    change heightBin (γ i) = n at hi'
    change |(γ i).re| < (heightBin (γ i) : ℝ) + 1 at hlt
    rw [hi'] at hlt
    exact hlt.le
  calc
    _ ≤ ((zerosUpTo ((n : ℝ) + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ C * ((n : ℝ) + 1) * Real.log (B * ((n : ℝ) + 1)) := hcount _ hT
    _ ≤ C * ((n : ℝ) + 1) * ((Real.log B + 1) * ((n : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hT0.le)
      rw [Real.log_mul (ne_of_gt hB0) (ne_of_gt hT0)]
      have ht := Real.log_le_sub_one_of_pos hT0
      nlinarith [mul_nonneg hlogB (sub_nonneg.mpr hT)]
    _ = _ := by ring

/-- The constant used in the proved Fourier decay bound is nonnegative. -/
theorem decayConstant_nonneg (h : ℝ → ℂ) (J : ℕ) :
    0 ≤ EntireExtension.decayConstant h J := by
  unfold EntireExtension.decayConstant EntireExtension.l1Integral
  apply mul_nonneg (by positivity)
  exact (MeasureTheory.integral_nonneg (fun x => norm_nonneg _)).trans (le_max_left _ _)

/-- Scaling the zero ordinates preserves rapid decay on the whole critical
strip, including non-real ordinates. -/
theorem extension_bin_decay {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c)
    (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (z : ℂ) (hstrip : |z.im| ≤ 1 / 2) :
    ‖EntireExtension.extension s (𝓕 φ : 𝓢(ℝ, ℂ)) ((c : ℂ) * z)‖ ≤
      (EntireExtension.decayConstant (𝓕 φ : 𝓢(ℝ, ℂ)) 4 *
        Real.exp (Real.pi * s * c) / (min 1 c) ^ 4) /
          ((heightBin z : ℝ) + 1) ^ 4 := by
  have hmin : 0 < min 1 c := lt_min zero_lt_one hc
  have hb : (heightBin z : ℝ) ≤ |z.re| := Nat.floor_le (abs_nonneg _)
  have hn : ‖(c : ℂ) * z‖ = c * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  have him : |((c : ℂ) * z).im| = c * |z.im| := by
    simp [Complex.mul_im, abs_mul, abs_of_pos hc]
  have hden : min 1 c * ((heightBin z : ℝ) + 1) ≤ 1 + ‖(c : ℂ) * z‖ := by
    rw [hn]
    have hb' := hb.trans (Complex.abs_re_le_norm z)
    have hnorm := norm_nonneg z
    have hmin1 := min_le_left (1 : ℝ) c
    have hminc := min_le_right (1 : ℝ) c
    nlinarith [mul_nonneg (sub_nonneg.mpr hminc) hnorm]
  have hexp : Real.exp (2 * Real.pi * s * |((c : ℂ) * z).im|) ≤
      Real.exp (Real.pi * s * c) := by
    apply Real.exp_le_exp.mpr
    rw [him]
    nlinarith [mul_le_mul_of_nonneg_left hstrip (by positivity : 0 ≤ 2 * Real.pi * s * c)]
  have hd := EntireExtension.schwartz_extension_decay hs φ hsupp 4 ((c : ℂ) * z)
  calc
    _ ≤ EntireExtension.decayConstant (𝓕 φ : 𝓢(ℝ, ℂ)) 4 *
        Real.exp (Real.pi * s * c) / (1 + ‖(c : ℂ) * z‖) ^ 4 :=
      hd.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (decayConstant_nonneg _ _)) (by positivity))
    _ ≤ EntireExtension.decayConstant (𝓕 φ : 𝓢(ℝ, ℂ)) 4 *
        Real.exp (Real.pi * s * c) /
          (min 1 c * ((heightBin z : ℝ) + 1)) ^ 4 := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (decayConstant_nonneg _ _) (Real.exp_pos _).le) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hden 4
    _ = _ := by rw [mul_pow, div_mul_eq_div_div]

/-- Absolute convergence of the paper's actual zero sum follows from the
cited zero count and the proved Fourier extension bound. -/
theorem schwartz_zero_sum_absolutely_convergent {ι : Type*} [DecidableEq ι]
    (γ : ι → ℂ) (zerosUpTo : ℝ → Finset ι)
    (hmem : ∀ i T, i ∈ zerosUpTo T ↔ |(γ i).re| ≤ T)
    (hstrip : ∀ i, |(γ i).im| ≤ 1 / 2)
    {C B s c : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) (hs : 0 ≤ s) (hc : 0 < c)
    (hcount : ∀ T : ℝ, 1 ≤ T → (zerosUpTo T).card ≤ C * T * Real.log (B * T))
    (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) :
    Summable (fun i => ‖EntireExtension.extension s (𝓕 φ : 𝓢(ℝ, ℂ))
      ((c : ℂ) * γ i)‖) := by
  apply summable_of_bin_count (fun i => heightBin (γ i)) _
    (Q := C * (Real.log B + 1))
    (K := EntireExtension.decayConstant (𝓕 φ : 𝓢(ℝ, ℂ)) 4 *
      Real.exp (Real.pi * s * c) / (min 1 c) ^ 4)
  · exact mul_nonneg hC (by linarith [Real.log_nonneg hB])
  · exact div_nonneg (mul_nonneg (decayConstant_nonneg _ _) (Real.exp_pos _).le)
      (by positivity)
  · exact bin_count_of_zero_count γ zerosUpTo hmem hC hB hcount
  · intro i
    exact extension_bin_decay hs hc φ hsupp (γ i) (hstrip i)

end DepthAspect.ZeroSumConvergence
