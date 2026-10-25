import DepthAspect.MurmurationDivisorExpansion
import DepthAspect.MurmurationIntegralSmall
import DepthAspect.ArithmeticWeightedTails

/-! Absolute termwise integration of the actual arithmetic density. -/
open MeasureTheory Set
open scoped BigOperators
namespace DepthAspect.MurmurationArithmeticIntegral
open BesselFirstKind MurmurationKernel MurmurationLattice MurmurationBesselSeries
open MurmurationArithmetic MurmurationDivisorExpansion MurmurationPointwiseBounds
open MurmurationIntegralSeries MurmurationIntegralSmall ArithmeticWeights

/-- Measurability comes from the literal lattice formula, without an
assumed regularity property of the density. -/
theorem weightedDensity_measurable (a ℓ : ℕ) (w : ℤ → ℝ) :
    Measurable (weightedDensity a ℓ w) := by
  have hm : ∀ r : ℤ, Measurable (fun y : ℝ => residueWeight ℓ r * w r *
      kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))) := by
    intro r
    exact measurable_const.mul ((kernel_continuous _).measurable.comp (by fun_prop))
  unfold weightedDensity
  apply Measurable.mul
  · fun_prop
  · exact Measurable.tsum hm

theorem g_measurable (a ℓ : ℕ) : Measurable (g a ℓ) :=
  weightedDensity_measurable a ℓ (fun _ => 1)

theorem M_measurable (a ℓ : ℕ) : Measurable (M a ℓ) :=
  weightedDensity_measurable a ℓ (integerPrimeWeight ℓ)

/-- The rescaled quarter-power majorant simplifies to the summable
b(d)√d coefficient. -/
theorem scaled_quarter_identity {y : ℝ} (hy : 0 < y) {d : ℕ} (hd : 0 < d) :
    (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) / y =
      (d : ℝ) ^ (-(1 / 2 : ℝ)) * y ^ (-(3 / 4 : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.div_rpow hy.le (sq_nonneg _),
    ← Real.rpow_natCast_mul hdR.le 2 (1 / 4 : ℝ)]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]
  have hydiv : y ^ (1 / 4 : ℝ) / y = y ^ (-(3 / 4 : ℝ)) := by
    nth_rw 2 [← Real.rpow_one y]
    rw [← Real.rpow_sub hy]
    norm_num
  calc
    _ = (y ^ (1 / 4 : ℝ) / y) * ((d : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by ring
    _ = _ := by rw [hydiv, ← Real.rpow_neg hdR.le]; ring

/-- The summable majorant for each actual logarithmic-density term. -/
theorem divisor_integrand_bound (a ℓ : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y : ℝ, 0 < y → |g a ℓ y| ≤ C * y ^ (1 / 4 : ℝ))
    {y : ℝ} (hy : 0 < y) (d : ℕ) :
    ‖c ℓ d * g a ℓ (y / (d : ℝ) ^ 2) / y‖ ≤
      C * (b ℓ d * Real.sqrt d) * y ^ (-(3 / 4 : ℝ)) := by
  by_cases hd : d = 0
  · subst d
    simp
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (c_nonneg ℓ d), abs_of_pos hy]
  calc
    _ ≤ (c ℓ d * (C * (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ))) / y :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb _ (by positivity)) (c_nonneg ℓ d)) hy.le
    _ = C * (c ℓ d * (d : ℝ) ^ (-(1 / 2 : ℝ))) * y ^ (-(3 / 4 : ℝ)) := by
      calc
        _ = (C * c ℓ d) * ((y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ) / y) := by ring
        _ = _ := by rw [scaled_quarter_identity hy hd0]; ring
    _ = _ := by rw [← b_sqrt_eq]

/-- The logarithmic integral of one scaled term is a difference of the
actual G values. The square scale cancels its Jacobian exactly. -/
theorem scaled_log_integral (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) {d : ℕ} (hd : 0 < d) {Y : ℝ} (hY : 0 ≤ Y) :
    (∫ y : ℝ in (1)..Y, g a ℓ (y / (d : ℝ) ^ 2) / y) =
      G a ℓ (Y / (d : ℝ) ^ 2) - G a ℓ (1 / (d : ℝ) ^ 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he (y : ℝ) : g a ℓ (y / (d : ℝ) ^ 2) / y =
      ((d : ℝ) ^ 2)⁻¹ * (g a ℓ (y / (d : ℝ) ^ 2) / (y / (d : ℝ) ^ 2)) := by
    by_cases hy : y = 0
    · subst y; simp
    · generalize hg : g a ℓ (y / (d : ℝ) ^ 2) = v
      field_simp [hy, ne_of_gt hdR]
      <;> ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun y => g a ℓ y / y) (by positivity : (d : ℝ) ^ 2 ≠ 0)]
  simp only [smul_eq_mul, inv_mul_cancel_left₀ (by positivity : (d : ℝ) ^ 2 ≠ 0)]
  exact (intervalIntegral.integral_interval_sub_left
    (log_density_intervalIntegrable hDLMF a hℓ (by positivity : 0 ≤ Y / (d : ℝ) ^ 2))
    (log_density_intervalIntegrable hDLMF a hℓ (by positivity : 0 ≤ 1 / (d : ℝ) ^ 2))).symm

/-- Integration of (128) over [1,Y] is justified by a summable absolute
majorant. The result is the actual integral, not a formal definition. -/
theorem M_log_integral_eq_series (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {Y : ℝ} (hY : 1 ≤ Y) :
    Summable (fun d : ℕ => c ℓ d *
      (G a ℓ (Y / (d : ℝ) ^ 2) - G a ℓ (1 / (d : ℝ) ^ 2))) ∧
    (∫ y : ℝ in (1)..Y, M a ℓ y / y) =
      B ℓ * ∑' d : ℕ, c ℓ d *
        (G a ℓ (Y / (d : ℝ) ^ 2) - G a ℓ (1 / (d : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := g_quarter_bound hDLMF a hℓ.two_le
  let F : ℕ → ℝ → ℝ := fun d y => c ℓ d * g a ℓ (y / (d : ℝ) ^ 2) / y
  let bound : ℕ → ℝ → ℝ := fun d y =>
    C * (b ℓ d * Real.sqrt d) * y ^ (-(3 / 4 : ℝ))
  have hsum := (b_sqrt_summable_and_bound ℓ).1
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (f := fun y => (B ℓ)⁻¹ * (M a ℓ y / y))
    (μ := volume) (a := 1) (b := Y) bound
    (by
      intro d
      have hm : Measurable (F d) := by
        dsimp [F]
        exact (measurable_const.mul ((g_measurable a ℓ).comp (by fun_prop))).div measurable_id
      exact hm.aestronglyMeasurable)
    (by
      intro d
      filter_upwards [] with y hy
      rw [uIoc_of_le hY] at hy
      exact divisor_integrand_bound a ℓ hC.le hb (by linarith [hy.1]) d)
    (by
      filter_upwards [] with y _
      exact (hsum.mul_left C).mul_right _)
    (by
      simp only [bound, tsum_mul_right, tsum_mul_left]
      exact (intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))).const_mul _)
    (by
      filter_upwards [] with y hy
      rw [uIoc_of_le hY] at hy
      have hy0 : 0 < y := by linarith [hy.1]
      obtain ⟨hs, he⟩ := M_divisor_sum a hℓ hy0
      have hh := hs.hasSum.div_const y
      rw [he, mul_div_assoc, inv_mul_cancel_left₀ (ne_of_gt (B_pos ℓ))]
      exact hh)
  have hint (d : ℕ) : (∫ y : ℝ in (1)..Y, F d y) =
      c ℓ d * (G a ℓ (Y / (d : ℝ) ^ 2) - G a ℓ (1 / (d : ℝ) ^ 2)) := by
    by_cases hd : d = 0
    · subst d
      simp [F]
    · simp only [F, mul_div_assoc]
      rw [intervalIntegral.integral_const_mul,
        scaled_log_integral hDLMF a hℓ.two_le (Nat.pos_of_ne_zero hd) (by linarith)]
  have ht := hdom.congr_fun (fun d => (hint d).symm)
  refine ⟨ht.summable, ?_⟩
  have he := ht.tsum_eq
  rw [intervalIntegral.integral_const_mul] at he
  rw [he, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (B_pos ℓ)), one_mul]

end DepthAspect.MurmurationArithmeticIntegral
