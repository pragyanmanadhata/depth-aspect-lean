import DepthAspect.SignedBlockIdentity
import DepthAspect.SignedDyadicSummation
import DepthAspect.MurmurationPrimitiveDerivative

/-!
# Actual finite-prime telescoping from (112) to (113)

The prefix consists of the literal prime/trace-index sum and the actual
M₂ integral. Its increments are exactly the local discrepancies; the
proved finite dyadic partition supplies both geometric constants.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory MurmurationArithmetic MurmurationPrimitiveDerivative
open scoped BigOperators SchwartzMap

/-- Finite interval splitting for any fixed finite prime set. The inner
trace set depends on the prime itself, so no trace endpoint is changed. -/
theorem primeTraceBlock_add (a : ℕ) (N d L A B C : ℝ)
    (hAB : A ≤ B) (hBC : B ≤ C) (h : 𝓢(ℝ, ℂ))
    (T : Finset ℕ) (V : ℤ → ℕ → ℂ) :
    primeTraceBlock a N d L A B h T V + primeTraceBlock a N d L B C h T V =
      primeTraceBlock a N d L A C h T V := by
  classical
  unfold primeTraceBlock
  rw [← smul_add]
  congr 1
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hAp : A < (p : ℝ)
  · by_cases hpB : (p : ℝ) ≤ B
    · simp [hAp, hpB, hpB.trans hBC, not_lt.mpr hpB]
    · have hBp : B < (p : ℝ) := lt_of_not_ge hpB
      simp [hAp, hpB, hBp]
  · have hnB : ¬ B < (p : ℝ) := not_lt.mpr ((not_lt.mp hAp).trans hAB)
    simp [hAp, hnB]

noncomputable def traceDiscrepancyPrefix (a : ℕ) (N d L : ℝ)
    (h : 𝓢(ℝ, ℂ)) (T : Finset ℕ) (V : ℤ → ℕ → ℂ) (X : ℝ) : ℂ :=
  primeTraceBlock a N d L 2 X h T V -
    (∫ u in (2 : ℝ)..X,
      (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L))

/-- The prefix increment is the literal local block error. -/
theorem traceDiscrepancyPrefix_sub (a : ℕ) (N d L A B : ℝ)
    (hA : 2 ≤ A) (hAB : A ≤ B) (h : 𝓢(ℝ, ℂ))
    (T : Finset ℕ) (V : ℤ → ℕ → ℂ)
    (hI : IntervalIntegrable (fun u =>
      (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L)) volume 2 B) :
    traceDiscrepancyPrefix a N d L h T V B - traceDiscrepancyPrefix a N d L h T V A =
      primeTraceBlock a N d L A B h T V -
        (∫ u in A..B,
          (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L)) := by
  have hI₁ := hI.mono_set (by
    rw [Set.uIcc_of_le hA, Set.uIcc_of_le (hA.trans hAB)]
    exact Set.Icc_subset_Icc le_rfl hAB)
  have hI₂ := hI.mono_set (by
    rw [Set.uIcc_of_le hAB, Set.uIcc_of_le (hA.trans hAB)]
    exact Set.Icc_subset_Icc hA le_rfl)
  have hi := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have hp := primeTraceBlock_add a N d L 2 A B hA hAB h T V
  unfold traceDiscrepancyPrefix
  rw [← hi, ← hp]
  abel

@[simp] theorem traceDiscrepancyPrefix_two (a : ℕ) (N d L : ℝ)
    (h : 𝓢(ℝ, ℂ)) (T : Finset ℕ) (V : ℤ → ℕ → ℂ) :
    traceDiscrepancyPrefix a N d L h T V 2 = 0 := by
  classical
  have hempty : T.filter (fun p : ℕ => (2 : ℝ) < p ∧ (p : ℝ) ≤ 2) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hbad
    exact (not_lt.mpr hbad.2) hbad.1
  simp only [traceDiscrepancyPrefix, primeTraceBlock, hempty, Finset.sum_empty,
    smul_zero, intervalIntegral.integral_same, sub_zero]

/-- The actual M₂ integrand is continuous on every positive compact
interval, so its integrability is not an endpoint premise. -/
theorem trace_main_intervalIntegrable (a : ℕ) {N : ℝ} (hN : 0 < N)
    (d L B : ℝ) (hB : 2 ≤ B) (h : 𝓢(ℝ, ℂ)) :
    IntervalIntegrable (fun u =>
      (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L)) volume 2 B := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [Set.uIcc_of_le hB] at hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hM : ContinuousAt (fun x : ℝ => M a 2 (x / N)) u :=
    (M_continuousAt a Nat.prime_two (div_pos hu0 hN)).comp
      (f := fun x : ℝ => x / N) (x := u) (continuousAt_id.div_const N)
  have hscalar : ContinuousAt (fun x => traceDimensionScale a N d * M a 2 (x / N) / x) u :=
    (continuousAt_const.mul hM).div continuousAt_id hu0.ne'
  have htest : ContinuousAt (fun x => h (Real.log x / L)) u :=
    h.continuous.continuousAt.comp ((Real.continuousAt_log hu0.ne').div_const L)
  exact (hscalar.smul htest).continuousWithinAt

/-- Equation (113)'s two geometric sums for the actual finite trace model.
The local estimate is a named intermediate to be discharged by (104)/(105),
the proved variation bound, and the separate empty block below three. -/
theorem trace_block_dyadic_sum_bound (a : ℕ) (N d L : ℝ) (hN : 0 < N)
    {X ε C₀ C₁ : ℝ} (hX : 2 ≤ X) (hε : 0 < ε)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (h : 𝓢(ℝ, ℂ)) (T : Finset ℕ) (V : ℤ → ℕ → ℂ)
    (hblock : ∀ A B : ℝ, 2 ≤ A → A ≤ B → B ≤ 2 * A →
      ‖primeTraceBlock a N d L A B h T V -
        (∫ u in A..B,
          (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L))‖ ≤
        C₀ * A ^ (1 / 4 + ε) + C₁ * A ^ (3 / 4 + ε)) :
    ‖traceDiscrepancyPrefix a N d L h T V X‖ ≤
      C₀ * X ^ (1 / 4 + ε) / (1 - (2 : ℝ) ^ (-(1 / 4 + ε))) +
      C₁ * X ^ (3 / 4 + ε) / (1 - (2 : ℝ) ^ (-(3 / 4 + ε))) := by
  have hb := SignedDyadicSummation.two_power_sum_bound hX
    (by linarith : 0 < 1 / 4 + ε) (by linarith : 0 < 3 / 4 + ε)
    hC₀ hC₁ (traceDiscrepancyPrefix a N d L h T V) (fun A B hA hAB hB => by
      rw [traceDiscrepancyPrefix_sub a N d L A B hA hAB h T V (trace_main_intervalIntegrable a hN d L B (hA.trans hAB) h)]
      exact hblock A B hA hAB hB)
  simpa using hb

end DepthAspect.SignedDensity
