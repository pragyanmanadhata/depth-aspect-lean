import DepthAspect.MurmurationPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Identification with the exact step-subtracted primitive in (107). -/
open MeasureTheory Set
namespace DepthAspect.MurmurationStepPrimitive
open BesselFirstKind MurmurationArithmetic MurmurationPrimitive

noncomputable def step (y : ℝ) : ℝ := if 1 ≤ y then 1 / 2 else 0

/-- The step term has no singularity at zero. -/
theorem step_log_intervalIntegrable {V : ℝ} (hV : 0 ≤ V) :
    IntervalIntegrable (fun y => step y / y) volume 0 V := by
  have hm : Measurable (fun y => step y / y) := by
    unfold step
    exact (measurable_const.ite measurableSet_Ici measurable_const).div measurable_id
  apply (intervalIntegrable_const (a := 0) (b := V) (c := (1 / 2 : ℝ))).mono_fun'
    hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
  rw [uIoc_of_le hV] at hy
  unfold step
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) / y)]
    exact (div_le_iff₀ hy.1).mpr (by linarith)
  · simp

/-- Removing or including the single endpoint y=1 gives the same integral. -/
theorem step_log_integral {V : ℝ} (hV : 0 ≤ V) :
    (∫ y : ℝ in (0)..V, step y / y) = (1 / 2 : ℝ) * Real.log (max 1 V) := by
  have he : (∫ y : ℝ in (0)..V, step y / y) =
      ∫ y : ℝ in (0)..V, (Ioi (1 : ℝ)).indicator (fun y => (1 / 2 : ℝ) * y⁻¹) y := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (1 : ℝ)] with y hy _
    have hiff : 1 ≤ y ↔ 1 < y := ⟨fun h => lt_of_le_of_ne h (Ne.symm hy), le_of_lt⟩
    simp only [step, hiff, Set.indicator, Set.mem_Ioi]
    split_ifs <;> simp [div_eq_mul_inv]
  rw [he, intervalIntegral.integral_of_le hV, setIntegral_indicator measurableSet_Ioi]
  by_cases hV1 : V ≤ 1
  · have hi : Ioc (0 : ℝ) V ∩ Ioi 1 = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
      intro hy hy1
      linarith [hy.2]
    rw [hi, setIntegral_empty, max_eq_left hV1, Real.log_one, mul_zero]
  · have h1 : 1 ≤ V := le_of_not_ge hV1
    have hi : Ioc (0 : ℝ) V ∩ Ioi 1 = Ioc 1 V := by
      ext y
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · intro h; exact ⟨h.2, h.1.2⟩
      · intro h; exact ⟨⟨by linarith [h.1], h.2⟩, h.1⟩
    rw [hi, ← intervalIntegral.integral_of_le h1,
      intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num : (0 : ℝ) < 1)
        (zero_lt_one.trans_le h1), div_one, max_eq_right h1]

/-- The primitive used for the bound is the integral written in (107),
with the paper's actual non-strict step convention. -/
theorem P_eq_step_integral (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {V : ℝ} (hV : 0 ≤ V) :
    P a ℓ V = ∫ y : ℝ in (0)..V, (M a ℓ y - step y) / y := by
  simp_rw [sub_div]
  rw [intervalIntegral.integral_sub
    (M_log_intervalIntegrable hDLMF a hℓ hV) (step_log_intervalIntegrable hV),
    step_log_integral hV]
  rfl

/-- Proposition 5.7's bounded primitive, for the literal density and step. -/
theorem step_primitive_bounded (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ V : ℝ, 0 < V →
      |∫ y : ℝ in (0)..V, (M a ℓ y - step y) / y| ≤ C := by
  obtain ⟨C, hC, hb⟩ := P_bounded hDLMF a hℓ
  refine ⟨C, hC, ?_⟩
  intro V hV
  rw [← P_eq_step_integral hDLMF a hℓ hV.le]
  exact hb V hV

/-- Both bounds in Proposition 5.7, with one constant independent of the
positive endpoint, for the literal arithmetic density of (106). -/
theorem proposition_5_7 (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0,
      (∀ v : ℝ, 0 < v → v ≤ 1 → |M a ℓ v| ≤ C * Real.sqrt v) ∧
      (∀ V : ℝ, 0 < V →
        |∫ y : ℝ in (0)..V, (M a ℓ y - step y) / y| ≤ C) := by
  obtain ⟨C₀, hC₀, hsmall⟩ := M_small_bound a hℓ
  obtain ⟨C₁, hC₁, hprimitive⟩ := step_primitive_bounded hDLMF a hℓ
  refine ⟨C₀ + C₁, by positivity, ?_, ?_⟩
  · intro v hv hv1
    exact (hsmall v hv hv1).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg v))
  · intro V hV
    exact (hprimitive V hV).trans (by linarith)

end DepthAspect.MurmurationStepPrimitive
