import DepthAspect.BoundedPrimitiveWeight
import DepthAspect.MartinDimension
import DepthAspect.UnsignedExponents

/-! Replacing the actual scalar c_N by one after (115). The scalar error
comes from the general Martin dimension identity through the checked
local dimension calculation, and the integral bound comes from the
actual internally proved bounded-primitive argument. -/
open MeasureTheory Set
open scoped SchwartzMap
namespace DepthAspect.MurmurationNormalization
open BesselFirstKind MurmurationArithmetic BoundedPrimitiveWeight

/-- The normalized integral that occurs literally in (113). -/
noncomputable def normalizedIntegral (a ℓ k n : ℕ) (h : 𝓢(ℝ, ℂ)) : ℂ :=
  (2 / Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n) : ℝ) •
    (∫ v in Ioi 0, (M a ℓ v / v) •
      h (Real.log ((2 : ℝ) ^ n * v) / Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n)))

/-- The c_N replacement in the paragraph following (115), uniformly in
depth. The actual integral and actual dimension coefficient both appear. -/
theorem scalar_replacement (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (k : ℕ) (hk : 2 ≤ k)
    (d : ℕ → ℝ) (hd : MartinDimension.SatisfiesMartinFormula k d)
    {s : ℝ} (h : 𝓢(ℝ, ℂ)) (hsupp : Function.support h ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ n : ℕ, 8 ≤ n →
      ‖MartinDimension.scalarCoefficient k n d • normalizedIntegral a ℓ k n h -
        normalizedIntegral a ℓ k n h‖ ≤ K * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := scaled_main_term hDLMF a hℓ
  let E := 2 * C * (∫ u : ℝ, ‖deriv h u‖) +
    2 * Real.log k * ‖h.toBoundedContinuousFunction‖
  let J : ℂ := ∫ u in Ioi (1 : ℝ), h u
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hE : 0 ≤ E := by
    have hI : 0 ≤ ∫ u : ℝ, ‖deriv h u‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [E]
    positivity
  refine ⟨(8 / ((k : ℝ) - 1)) * (E + ‖J‖), by positivity, ?_⟩
  intro n hn
  have hL := UnsignedExponents.conductor_log_ge_one (k : ℝ) hkR n hn
  have hL0 : 0 < Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n) := by linarith
  have he : ‖normalizedIntegral a ℓ k n h - J‖ ≤
      E / Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n) :=
    hb (k : ℝ) ((2 : ℝ) ^ n) s (by linarith) (by positivity) hL0 h hsupp
  have heL : E / Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n) ≤ E :=
    (div_le_iff₀ hL0).mpr (by nlinarith)
  have hI : ‖normalizedIntegral a ℓ k n h‖ ≤ E + ‖J‖ := by
    calc
      _ = ‖(normalizedIntegral a ℓ k n h - J) + J‖ := by congr 1; abel
      _ ≤ ‖normalizedIntegral a ℓ k n h - J‖ + ‖J‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (he.trans heL) le_rfl
  rw [show MartinDimension.scalarCoefficient k n d • normalizedIntegral a ℓ k n h -
      normalizedIntegral a ℓ k n h =
        (MartinDimension.scalarCoefficient k n d - 1) • normalizedIntegral a ℓ k n h by
    rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (8 / ((k : ℝ) - 1) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * (E + ‖J‖) :=
      mul_le_mul (by simpa only [neg_div] using
        MartinDimension.scalarCoefficient_error k n hk hn d hd) hI
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The replacement constant is chosen before the dimension function,
so it is uniform over all spectral data satisfying the cited formula. -/
theorem scalar_replacement_uniform (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (k : ℕ) (hk : 2 ≤ k)
    {s : ℝ} (h : 𝓢(ℝ, ℂ)) (hsupp : Function.support h ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (d : ℕ → ℝ), MartinDimension.SatisfiesMartinFormula k d →
      ∀ n : ℕ, 8 ≤ n →
      ‖MartinDimension.scalarCoefficient k n d • normalizedIntegral a ℓ k n h -
        normalizedIntegral a ℓ k n h‖ ≤ K * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := scaled_main_term hDLMF a hℓ
  let E := 2 * C * (∫ u : ℝ, ‖deriv h u‖) +
    2 * Real.log k * ‖h.toBoundedContinuousFunction‖
  let J : ℂ := ∫ u in Ioi (1 : ℝ), h u
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hE : 0 ≤ E := by
    have hI : 0 ≤ ∫ u : ℝ, ‖deriv h u‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [E]
    positivity
  refine ⟨(8 / ((k : ℝ) - 1)) * (E + ‖J‖), by positivity, ?_⟩
  intro d hd n hn
  have hL := UnsignedExponents.conductor_log_ge_one (k : ℝ) hkR n hn
  have hL0 : 0 < Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n) := by linarith
  have he : ‖normalizedIntegral a ℓ k n h - J‖ ≤
      E / Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n) :=
    hb (k : ℝ) ((2 : ℝ) ^ n) s (by linarith) (by positivity) hL0 h hsupp
  have heL : E / Real.log ((k : ℝ) ^ 2 * (2 : ℝ) ^ n) ≤ E :=
    (div_le_iff₀ hL0).mpr (by nlinarith)
  have hI : ‖normalizedIntegral a ℓ k n h‖ ≤ E + ‖J‖ := by
    calc
      _ = ‖(normalizedIntegral a ℓ k n h - J) + J‖ := by congr 1; abel
      _ ≤ ‖normalizedIntegral a ℓ k n h - J‖ + ‖J‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (he.trans heL) le_rfl
  rw [show MartinDimension.scalarCoefficient k n d • normalizedIntegral a ℓ k n h -
      normalizedIntegral a ℓ k n h =
        (MartinDimension.scalarCoefficient k n d - 1) • normalizedIntegral a ℓ k n h by
    rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (8 / ((k : ℝ) - 1) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * (E + ‖J‖) :=
      mul_le_mul (by simpa only [neg_div] using
        MartinDimension.scalarCoefficient_error k n hk hn d hd) hI
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end DepthAspect.MurmurationNormalization
