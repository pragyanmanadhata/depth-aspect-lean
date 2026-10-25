import DepthAspect.SignedMurmurationMain
import DepthAspect.SignedPrimeInterchange
import DepthAspect.TraceWeightVariation

/-!
# The integral main term in the trace-index block sum

The actual coefficient π²p₂(r)/8 and the actual Schwartz trace weight are
summed on the literal active lattice. Equation (108), followed by the
proved moving-endpoint exchange, identifies their integrals with M₂.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set MurmurationArithmetic TraceWeightVariation
open scoped BigOperators SchwartzMap

noncomputable def traceMainScale (N d : ℝ) : ℝ := Real.sqrt N / (2 * Real.pi * d)
noncomputable def traceDimensionScale (a : ℕ) (N d : ℝ) : ℝ :=
  ((2 * a + 1 : ℕ) : ℝ) * N / (32 * d)
noncomputable def averagedTraceWeight (a : ℕ) (N d L : ℝ) (h : 𝓢(ℝ, ℂ))
    (r : ℤ) (u : ℝ) : ℂ :=
  (traceMainScale N d * ((-1 : ℝ) ^ r * meanLValueCoefficient r)) •
    traceWeight (2 * (a : ℝ) + 1) (Real.sqrt N * (r : ℝ) / 4) L h u

theorem traceAngle_main_argument {N u : ℝ} (hN : 0 < N) (hu : 0 < u) (r : ℤ) :
    (Real.sqrt N * (r : ℝ) / 4) / Real.sqrt u =
      (r : ℝ) / (4 * Real.sqrt (u / N)) := by
  rw [Real.sqrt_div hu.le]
  field_simp [(Real.sqrt_pos.mpr hN).ne', (Real.sqrt_pos.mpr hu).ne']

theorem inverse_sqrt_eq_sqrt_div {u : ℝ} (hu : 0 < u) :
    u ^ (-(1 / 2 : ℝ)) = Real.sqrt u / u := by
  rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  apply (eq_div_iff hu.ne').mpr
  calc
    _ = (Real.sqrt u)⁻¹ * (Real.sqrt u * Real.sqrt u) := by rw [Real.mul_self_sqrt hu.le]
    _ = _ := by field_simp [(Real.sqrt_pos.mpr hu).ne']

/-- Pointwise identification of the actual average trace-weight sum with
the literal M-integrand, including its exact dimension coefficient. -/
theorem sum_averagedTraceWeight (a : ℕ) {N d u : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hu : 0 < u) (L : ℝ) (h : 𝓢(ℝ, ℂ)) :
    (∑ r ∈ activeIndices N u, averagedTraceWeight a N d L h r u) =
      (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L) := by
  simp only [averagedTraceWeight, traceWeight, cosineTrace, traceAngle,
    traceAmplitude, smul_smul, traceAngle_main_argument hN hu]
  rw [← Finset.sum_smul]
  congr 1
  have hfactor : traceMainScale N d * u ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt (N * u) / (2 * Real.pi * d)) / u := by
    rw [inverse_sqrt_eq_sqrt_div hu, Real.sqrt_mul hN.le]
    unfold traceMainScale
    ring
  calc
    _ = (traceMainScale N d * u ^ (-(1 / 2 : ℝ))) *
        ∑ r ∈ activeIndices N u, (-1 : ℝ) ^ r *
          Real.cos ((2 * (a : ℝ) + 1) *
            Real.arcsin ((r : ℝ) / (4 * Real.sqrt (u / N)))) * meanLValueCoefficient r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ((Real.sqrt (N * u) / (2 * Real.pi * d)) *
        ∑ r ∈ activeIndices N u, (-1 : ℝ) ^ r *
          Real.cos ((2 * (a : ℝ) + 1) *
            Real.arcsin ((r : ℝ) / (4 * Real.sqrt (u / N)))) * meanLValueCoefficient r) / u := by
      rw [hfactor]
      ring
    _ = _ := by rw [prime_main_term_eq_M a hN hu hd]; rfl

/-- The actual integral main terms over all moving trace intervals combine
into the one M-integral in (112). -/
theorem integral_averagedTraceWeight (a : ℕ) {N d X Y : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hX : 0 < X) (hXY : X ≤ Y)
    (L : ℝ) (h : 𝓢(ℝ, ℂ)) :
    (∑ r ∈ activeIndices N Y,
      ∫ u in max X (N * (r : ℝ) ^ 2 / 16)..Y, averagedTraceWeight a N d L h r u) =
      ∫ u in X..Y, (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L) := by
  have hi (r : ℤ) (hr : r ∈ activeIndices N Y) :
      IntervalIntegrable (averagedTraceWeight a N d L h r) volume X Y := by
    apply ContinuousOn.intervalIntegrable_of_Icc hXY
    change ContinuousOn (fun u =>
      (traceMainScale N d * ((-1 : ℝ) ^ r * meanLValueCoefficient r)) •
        traceWeight (2 * (a : ℝ) + 1) (Real.sqrt N * (r : ℝ) / 4) L h u) (Icc X Y)
    exact (traceWeight_continuousOn (2 * (a : ℝ) + 1)
      (Real.sqrt N * (r : ℝ) / 4) L h hX).const_smul
        (traceMainScale N d * ((-1 : ℝ) ^ r * meanLValueCoefficient r))
  rw [active_integral_sum_comm hN hX hXY _ hi]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc X Y := by simpa only [uIcc_of_le hXY] using hu
  exact sum_averagedTraceWeight a hN hd (hX.trans_le hu'.1) L h

end DepthAspect.SignedDensity
