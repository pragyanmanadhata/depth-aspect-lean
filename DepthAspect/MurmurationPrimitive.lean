import DepthAspect.MurmurationMean

/-! Bounds at the origin and the bounded logarithmic primitive needed in
Proposition 5.7. -/
open MeasureTheory Set
open scoped BigOperators
namespace DepthAspect.MurmurationPrimitive
open BesselFirstKind MurmurationArithmetic MurmurationBesselSeries
open MurmurationDivisorExpansion MurmurationPointwiseBounds
open MurmurationArithmeticIntegral MurmurationMean ArithmeticWeights

/-- The literal arithmetic density retains the square-root bound at zero,
including all its arithmetic weights. -/
theorem M_small_bound (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ y : ℝ, 0 < y → y ≤ 1 → |M a ℓ y| ≤ C * Real.sqrt y := by
  obtain ⟨C, hC, hb⟩ := g_small_bound a hℓ.two_le
  refine ⟨C, hC, ?_⟩
  intro y hy hy1
  obtain ⟨hs, he⟩ := M_divisor_sum a hℓ hy
  have hbound (d : ℕ) : ‖c ℓ d * g a ℓ (y / (d : ℝ) ^ 2)‖ ≤
      (C * Real.sqrt y) * b ℓ d := by
    by_cases hd : d = 0
    · subst d
      simp
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hz : y / (d : ℝ) ^ 2 ≤ 1 :=
      (div_le_one (by positivity : 0 < (d : ℝ) ^ 2)).mpr (by nlinarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (c_nonneg ℓ d)]
    calc
      _ ≤ c ℓ d * (C * Real.sqrt (y / (d : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (hb _ (by positivity) hz) (c_nonneg ℓ d)
      _ = _ := by
        rw [sqrt_div_nat_sq hy.le, c_apply]
        have hdne : (d : ℝ) ≠ 0 := by positivity
        field_simp [hdne]
        <;> ring
  rw [he, abs_mul, abs_of_pos (B_pos ℓ)]
  calc
    _ ≤ B ℓ * ∑' d : ℕ, (C * Real.sqrt y) * b ℓ d := by
      apply mul_le_mul_of_nonneg_left _ (B_pos ℓ).le
      exact (norm_tsum_le_tsum_norm hs.norm).trans
        (Summable.tsum_le_tsum hbound hs.norm ((b_summable ℓ).mul_left _))
    _ = C * Real.sqrt y := by
      rw [tsum_mul_left]
      calc
        _ = (C * Real.sqrt y) * (B ℓ * ∑' d : ℕ, b ℓ d) := by ring
        _ = _ := by rw [zero_weight_normalization, mul_one]

/-- A global integrable majorant for the actual logarithmic density. -/
theorem M_log_integrand_bound (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ y : ℝ, 0 < y → |M a ℓ y / y| ≤ C * y ^ (-(3 / 4 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := g_quarter_bound hDLMF a hℓ.two_le
  let T : ℝ := ∑' d : ℕ, b ℓ d * Real.sqrt d
  have hT : 0 ≤ T := tsum_nonneg (fun d => mul_nonneg (b_nonneg ℓ d) (Real.sqrt_nonneg _))
  let K : ℝ := B ℓ * C * (T + 1)
  have hB := B_pos ℓ
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro y hy
  obtain ⟨hs, he⟩ := M_divisor_sum a hℓ hy
  have ht := (b_sqrt_summable_and_bound ℓ).1
  rw [he, mul_div_assoc, abs_mul, abs_of_pos (B_pos ℓ)]
  have hq : (∑' d : ℕ, c ℓ d * g a ℓ (y / (d : ℝ) ^ 2)) / y =
      ∑' d : ℕ, c ℓ d * g a ℓ (y / (d : ℝ) ^ 2) / y := (tsum_div_const).symm
  rw [hq]
  calc
    _ ≤ B ℓ * ∑' d : ℕ, C * (b ℓ d * Real.sqrt d) * y ^ (-(3 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (B_pos ℓ).le
      exact (norm_tsum_le_tsum_norm (hs.div_const y).norm).trans
        (Summable.tsum_le_tsum (divisor_integrand_bound a ℓ hC.le hb hy)
          (hs.div_const y).norm ((ht.mul_left C).mul_right _))
    _ = B ℓ * C * T * y ^ (-(3 / 4 : ℝ)) := by
      rw [tsum_mul_right, tsum_mul_left]
      dsimp [T]
      ring
    _ ≤ K * y ^ (-(3 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy.le _)
      dsimp [K]
      nlinarith only [mul_nonneg hB.le hC.le]

/-- Absolute integrability of M(y)/y up to every positive endpoint. -/
theorem M_log_intervalIntegrable (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {V : ℝ} (hV : 0 ≤ V) :
    IntervalIntegrable (fun y => M a ℓ y / y) volume 0 V := by
  obtain ⟨C, hC, hb⟩ := M_log_integrand_bound hDLMF a hℓ
  have hi : IntervalIntegrable (fun y : ℝ => C * y ^ (-(3 / 4 : ℝ))) volume 0 V :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))).const_mul C
  apply hi.mono_fun' ((M_measurable a ℓ).div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  rw [uIoc_of_le hV] at hy
  exact hb y hy.1

/-- The primitive near zero is bounded by a square root. -/
theorem small_integral_bound (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ V : ℝ, 0 < V → V ≤ 1 →
      |∫ y : ℝ in (0)..V, M a ℓ y / y| ≤ C * Real.sqrt V := by
  obtain ⟨C, hC, hb⟩ := M_small_bound a hℓ
  refine ⟨2 * C, by positivity, ?_⟩
  intro V hV hV1
  have hi : IntervalIntegrable (fun y : ℝ => C * y ^ (-(1 / 2 : ℝ))) volume 0 V :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).const_mul C
  have hn := intervalIntegral.norm_integral_le_of_norm_le hV.le
    (f := fun y => M a ℓ y / y)
    (g := fun y : ℝ => C * y ^ (-(1 / 2 : ℝ))) (by
      filter_upwards [] with y hy
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hy.1]
      calc
        _ ≤ (C * Real.sqrt y) / y :=
          div_le_div_of_nonneg_right (hb y hy.1 (hy.2.trans hV1)) hy.1.le
        _ = C * y ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_eq_rpow, mul_div_assoc]
          nth_rw 2 [← Real.rpow_one y]
          rw [← Real.rpow_sub hy.1]
          norm_num) hi
  have he : (∫ y : ℝ in (0)..V, C * y ^ (-(1 / 2 : ℝ))) = 2 * C * Real.sqrt V := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
    norm_num [← Real.sqrt_eq_rpow]
    ring
  simpa only [Real.norm_eq_abs, he] using hn

noncomputable def P (a ℓ : ℕ) (V : ℝ) : ℝ :=
  (∫ y : ℝ in (0)..V, M a ℓ y / y) - (1 / 2 : ℝ) * Real.log (max 1 V)

/-- The bounded primitive required by Proposition 5.7, uniformly for all
positive V. The cutoff logarithm has derivative 1/V precisely above one. -/
theorem P_bounded (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ V : ℝ, 0 < V → |P a ℓ V| ≤ C := by
  obtain ⟨A, hA, ha⟩ := small_integral_bound hDLMF a hℓ
  obtain ⟨D, hD, hd⟩ := M_logarithmic_mean hDLMF a hℓ
  refine ⟨A + D, by positivity, ?_⟩
  intro V hV
  by_cases hV1 : V ≤ 1
  · have hs : Real.sqrt V ≤ 1 := by simpa using Real.sqrt_le_sqrt hV1
    simp only [P, max_eq_left hV1, Real.log_one, mul_zero, sub_zero]
    exact (ha V hV hV1).trans ((mul_le_of_le_one_right hA.le hs).trans (by linarith))
  · have h1 : 1 ≤ V := le_of_not_ge hV1
    have hi0 := M_log_intervalIntegrable hDLMF a hℓ (by norm_num : (0 : ℝ) ≤ 1)
    have hiV := M_log_intervalIntegrable hDLMF a hℓ hV.le
    have he : P a ℓ V = (∫ y : ℝ in (0)..1, M a ℓ y / y) +
        ((∫ y : ℝ in (1)..V, M a ℓ y / y) - (1 / 2 : ℝ) * Real.log V) := by
      rw [P, max_eq_right h1,
        ← intervalIntegral.integral_add_adjacent_intervals hi0 (hi0.symm.trans hiV)]
      ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (by simpa using ha 1 (by norm_num) le_rfl) (hd V h1))

end DepthAspect.MurmurationPrimitive
