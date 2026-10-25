import DepthAspect.MurmurationLeading
import DepthAspect.MurmurationDivisorExpansion

/-! The leading arithmetic divisor series is exactly y^(1/4) A(sqrt y),
including the two reindexings and all summability assertions. -/
open scoped BigOperators
namespace DepthAspect.MurmurationLeadingDivisors
open ArithmeticWeights MurmurationLeading MurmurationDivisorExpansion
  MurmurationOscillationSeries

theorem scaled_quarter {y : ℝ} (hy : 0 < y) {d : ℕ} (hd : 0 < d) :
    (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) =
      y ^ (1 / 4 : ℝ) * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.div_rpow hy.le (sq_nonneg _),
    ← Real.rpow_natCast_mul hdR.le 2 (1 / 4 : ℝ)]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]
  rw [div_eq_mul_inv, ← Real.rpow_neg hdR.le]

theorem scaled_weighted_quarter (ℓ : ℕ) {y : ℝ} (hy : 0 < y) {d : ℕ} (hd : 0 < d) :
    c ℓ d * (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) =
      y ^ (1 / 4 : ℝ) * (b ℓ d * Real.sqrt d) := by
  rw [scaled_quarter hy hd, b_sqrt_eq]
  ring

theorem scaled_negative_quarter {y : ℝ} (hy : 0 < y) {d : ℕ} (hd : 0 < d) :
    (y / (d : ℝ) ^ 2) ^ (-(1 / 4 : ℝ)) =
      y ^ (-(1 / 4 : ℝ)) * Real.sqrt d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.div_rpow hy.le (sq_nonneg _),
    ← Real.rpow_natCast_mul hdR.le 2 (-(1 / 4 : ℝ))]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (-(1 / 4)) = -(1 / 2) by norm_num]
  rw [div_eq_mul_inv, ← Real.rpow_neg hdR.le]
  norm_num only [neg_neg]
  rw [← Real.sqrt_eq_rpow]

theorem scaled_leading_summable (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {y : ℝ} (hy : 0 < y) :
    Summable (fun d : ℕ => c ℓ d * gLeading a ℓ (y / (d : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := gLeading_bound a hℓ
  apply ((b_sqrt_summable_and_bound ℓ).1.mul_left (C * y ^ (1 / 4 : ℝ))).of_norm_bounded
  intro d
  by_cases hd : d = 0
  · subst d
    simp
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (c_nonneg ℓ d)]
  calc
    _ ≤ c ℓ d * (C * (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hb _ (div_pos hy (sq_pos_of_pos hdR))) (c_nonneg ℓ d)
    _ = _ := by
      calc
        _ = C * (c ℓ d * (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [scaled_weighted_quarter ℓ hy hd0]; ring

/-- Each scaled actual Bessel leading term is exactly the term of (131)
with the corresponding divisor and frequency, including its coefficient. -/
theorem scaled_leadingTerm (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) {y : ℝ} (hy : 0 < y)
    (d ν : ℕ+) : B ℓ * c ℓ d * leadingTerm a ℓ (y / (d : ℝ) ^ 2) ν =
      y ^ (1 / 4 : ℝ) * oscillationTerm a ℓ (d, ν) (Real.sqrt y) := by
  have hd : (0 : ℝ) < d := by positivity
  have hydiv : 0 < y / (d : ℝ) ^ 2 := div_pos hy (sq_pos_of_pos hd)
  rw [leadingTerm_cos a hℓ.pos hydiv, sqrt_div_nat_sq hy.le d]
  have h₁ : 4 * Real.pi * (ν : ℝ) * (Real.sqrt y / d) - phase a =
      4 * Real.pi * ν * Real.sqrt y / d - phase a := by ring
  have h₂ : 4 * Real.pi * (ℓ : ℝ) * (ν : ℝ) * (Real.sqrt y / d) - phase a =
      4 * Real.pi * ℓ * ν * Real.sqrt y / d - phase a := by ring
  rw [h₁, h₂]
  have hw := scaled_weighted_quarter ℓ hy d.pos
  unfold oscillationTerm K
  dsimp only [Prod.fst, Prod.snd]
  calc
    _ = (Real.sqrt 2 * B ℓ / (1 - (ℓ : ℝ)⁻¹)) *
        (c ℓ d * (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ)) *
          (ν : ℝ) ^ (-(3 / 2 : ℝ)) *
            (Real.cos (4 * Real.pi * ν * Real.sqrt y / d - phase a) -
              (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) *
                Real.cos (4 * Real.pi * ℓ * ν * Real.sqrt y / d - phase a)) := by ring
    _ = _ := by rw [hw]; ring

/-- Both actual sums are absolutely convergent, so their exact identification
does not depend on a convention for a divergent `tsum`. -/
theorem leading_divisor_series_eq (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) {y : ℝ} (hy : 0 < y) :
    B ℓ * (∑' d : ℕ, c ℓ d * gLeading a ℓ (y / (d : ℝ) ^ 2)) =
      y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y) := by
  rw [← tsum_pnat_eq_tsum_of_eq_zero (f := fun d : ℕ =>
    c ℓ d * gLeading a ℓ (y / (d : ℝ) ^ 2)) (by simp)]
  have hs := (A_absolute a hℓ (Real.sqrt y)).of_norm
  unfold A
  rw [hs.tsum_prod]
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro d
  unfold gLeading
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro ν
  simpa only [mul_assoc] using scaled_leadingTerm a hℓ hy d ν

end DepthAspect.MurmurationLeadingDivisors
