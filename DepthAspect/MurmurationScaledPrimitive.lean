import DepthAspect.MurmurationIntegralSmall
import DepthAspect.MurmurationIntegralError
import DepthAspect.ArithmeticPrimeWeight

/-! The scaled primitive series needed for the actual logarithmic mean. -/
open scoped BigOperators
namespace DepthAspect.MurmurationScaledPrimitive
open BesselFirstKind MurmurationIntegralSeries MurmurationIntegralSmall
open MurmurationIntegralError MurmurationIntegralLimit ArithmeticWeights

/-- The small-argument primitive bound extends to all positive arguments;
the large-argument estimate makes its right side only larger. -/
theorem G_global_sqrt_bound (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, ∀ Z : ℝ, 0 < Z → |G a ℓ Z| ≤ C * Real.sqrt Z := by
  obtain ⟨A, hA, ha⟩ := G_small_bound hDLMF a hℓ
  obtain ⟨D, hD, hd⟩ := G_large_error hDLMF a hℓ
  refine ⟨A + D + |limitValue ℓ|, by positivity, ?_⟩
  intro Z hZ
  by_cases hZ1 : Z ≤ 1
  · apply (ha Z hZ hZ1).trans
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (limitValue ℓ)]) (Real.sqrt_nonneg _)
  · have h1 : 1 ≤ Z := le_of_not_ge hZ1
    have hp : Z ^ (-(1 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
    have hs : 1 ≤ Real.sqrt Z := by simpa using Real.sqrt_le_sqrt h1
    calc
      |G a ℓ Z| = |(G a ℓ Z - limitValue ℓ) + limitValue ℓ| := by congr 1; ring
      _ ≤ |G a ℓ Z - limitValue ℓ| + |limitValue ℓ| := abs_add_le _ _
      _ ≤ D + |limitValue ℓ| := add_le_add
        ((hd Z h1).trans (mul_le_of_le_one_right hD.le hp)) (le_refl _)
      _ ≤ (A + D + |limitValue ℓ|) * Real.sqrt Z := by
        have hm := mul_le_mul_of_nonneg_left hs
          (by positivity : 0 ≤ A + D + |limitValue ℓ|)
        nlinarith

/-- The rescaled primitive is dominated by the actual summable b-weight. -/
theorem scaled_primitive_bound (a ℓ : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ Z : ℝ, 0 < Z → |G a ℓ Z| ≤ C * Real.sqrt Z)
    {Y : ℝ} (hY : 0 < Y) (d : ℕ) :
    ‖c ℓ d * G a ℓ (Y / (d : ℝ) ^ 2)‖ ≤ C * Real.sqrt Y * b ℓ d := by
  by_cases hd : d = 0
  · subst d
    simp
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (c_nonneg ℓ d)]
  calc
    _ ≤ c ℓ d * (C * Real.sqrt (Y / (d : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hb _ (by positivity)) (c_nonneg ℓ d)
    _ = _ := by
      rw [Real.sqrt_div hY.le, Real.sqrt_sq hdR.le, c_apply]
      field_simp [ne_of_gt hdR]
      <;> ring

/-- The primitive series converges absolutely at every fixed positive Y,
allowing the difference in the integrated formula to split into two sums. -/
theorem scaled_primitive_summable (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {Y : ℝ} (hY : 0 < Y) :
    Summable (fun d : ℕ => c ℓ d * G a ℓ (Y / (d : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := G_global_sqrt_bound hDLMF a hℓ
  exact ((b_summable ℓ).mul_left (C * Real.sqrt Y)).of_norm_bounded
    (scaled_primitive_bound a ℓ hC.le hb hY)

/-- The lower endpoint Y=1 contributes a fixed bounded constant. -/
theorem lower_endpoint_bound (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, |B ℓ * ∑' d : ℕ, c ℓ d * G a ℓ (1 / (d : ℝ) ^ 2)| ≤ C := by
  obtain ⟨C, hC, hb⟩ := G_global_sqrt_bound hDLMF a hℓ
  refine ⟨C, hC, ?_⟩
  have hs := scaled_primitive_summable hDLMF a hℓ (by norm_num : (0 : ℝ) < 1)
  rw [abs_mul, abs_of_pos (B_pos ℓ)]
  calc
    _ ≤ B ℓ * ∑' d : ℕ, C * b ℓ d := by
      apply mul_le_mul_of_nonneg_left _ (B_pos ℓ).le
      apply (norm_tsum_le_tsum_norm hs.norm).trans
      apply Summable.tsum_le_tsum _ hs.norm ((b_summable ℓ).mul_left C)
      intro d
      simpa only [Real.sqrt_one, mul_one] using
        scaled_primitive_bound a ℓ hC.le hb (by norm_num : (0 : ℝ) < 1) d
    _ = C := by
      rw [tsum_mul_left]
      calc
        B ℓ * (C * ∑' d : ℕ, b ℓ d) = C * (B ℓ * ∑' d : ℕ, b ℓ d) := by ring
        _ = C := by rw [zero_weight_normalization, mul_one]

end DepthAspect.MurmurationScaledPrimitive
