import DepthAspect.SignedMainInterchange
import DepthAspect.SignedVariationAssembly

/-!
# The literal block discrepancy before applying (104)/(105)

This is the exact finite/integral composition used for (112). Its only
intermediate estimate is the individual arithmetic L-value discrepancy.
All index ranges, endpoint truncations, phases, Schwartz weights, and the
M main term are defined and manipulated literally.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set TraceWeightVariation SignedVariationAssembly MurmurationArithmetic
open scoped BigOperators SchwartzMap

noncomputable def traceIndexError (a : ℕ) (N L X Y : ℝ) (h : 𝓢(ℝ, ℂ))
    (T : Finset ℕ) (V : ℤ → ℕ → ℂ) (r : ℤ) : ℂ :=
  (∑ p ∈ T.filter (fun p : ℕ => max X (N * (r : ℝ) ^ 2 / 16) < (p : ℝ) ∧ (p : ℝ) ≤ Y),
    Real.log (p : ℝ) • (V r p *
      traceWeight (2 * (a : ℝ) + 1) (Real.sqrt N * (r : ℝ) / 4) L h p)) -
    meanLValueCoefficient r •
      (∫ u in max X (N * (r : ℝ) ^ 2 / 16)..Y,
        traceWeight (2 * (a : ℝ) + 1) (Real.sqrt N * (r : ℝ) / 4) L h u)

noncomputable def primeTraceBlock (a : ℕ) (N d L X Y : ℝ) (h : 𝓢(ℝ, ℂ))
    (T : Finset ℕ) (V : ℤ → ℕ → ℂ) : ℂ :=
  traceMainScale N d •
    (∑ p ∈ T.filter (fun p : ℕ => X < (p : ℝ) ∧ (p : ℝ) ≤ Y),
      ∑ r ∈ activeIndices N p, (-1 : ℝ) ^ r •
        (Real.log (p : ℝ) • (V r p *
          traceWeight (2 * (a : ℝ) + 1) (Real.sqrt N * (r : ℝ) / 4) L h p)))

/-- No interchange of infinite sums is used: both index sums are finite,
and the moving-endpoint integral was proved for the actual active lattice. -/
theorem trace_block_error_identity (a : ℕ) {N d L X Y : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hX : 0 < X) (hXY : X ≤ Y)
    (h : 𝓢(ℝ, ℂ)) (T : Finset ℕ) (V : ℤ → ℕ → ℂ) :
    primeTraceBlock a N d L X Y h T V -
      (∫ u in X..Y, (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L)) =
      traceMainScale N d •
        ∑ r ∈ activeIndices N Y, (-1 : ℝ) ^ r • traceIndexError a N L X Y h T V r := by
  classical
  have hmain :
      (∫ u in X..Y, (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L)) =
      traceMainScale N d •
        ∑ r ∈ activeIndices N Y, (-1 : ℝ) ^ r • (meanLValueCoefficient r •
          (∫ u in max X (N * (r : ℝ) ^ 2 / 16)..Y,
            traceWeight (2 * (a : ℝ) + 1) (Real.sqrt N * (r : ℝ) / 4) L h u)) := by
    rw [← integral_averagedTraceWeight a hN hd hX hXY L h, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [averagedTraceWeight, intervalIntegral.integral_smul, smul_smul]
  rw [primeTraceBlock, active_prime_sum_comm hN hX hXY, hmain,
    ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.smul_sum, ← smul_sub]
  rfl

/-- The exact normalized discrepancy satisfies the two-term bound in
(112), once the per-index arithmetic theorem is supplied. No variation,
index count, dimension-normalization or main-term identity is assumed. -/
theorem normalized_trace_block_bound (a : ℕ) {N d L X Y C ε : ℝ}
    (hN : 0 < N) (hdim : N / 64 ≤ d) (hX : 0 < X) (hXY : X ≤ Y)
    (hY : Y ≤ 2 * X) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (h : 𝓢(ℝ, ℂ)) (T : Finset ℕ) (V : ℤ → ℕ → ℂ)
    (hError : ∀ r ∈ activeIndices N Y, ‖traceIndexError a N L X Y h T V r‖ ≤
      C * Real.sqrt
        ((‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))) *
          (‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ)) +
            weightVariation (2 * (a : ℝ) + 1) L X Y N h r)) * X ^ (3 / 4 + ε)) :
    ‖(2 / L : ℝ) • (primeTraceBlock a N d L X Y h T V -
      (∫ u in X..Y, (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L)))‖ ≤
      (512 * Real.sqrt 2 * C *
        ((2 + (2 * (a : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h) / (Real.pi * L)) *
        (N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) + N ^ (-1 : ℝ) * X ^ (3 / 4 + ε)) := by
  have hd : 0 < d := lt_of_lt_of_le (by positivity) hdim
  have hL0 : 0 < L := by linarith
  let E : ℤ → ℂ := fun r => (-1 : ℝ) ^ r • traceIndexError a N L X Y h T V r
  have hPhase (r : ℤ) : ‖E r‖ = ‖traceIndexError a N L X Y h T V r‖ := by
    simp [E]
  have hb := actual_three_quarter_block_bound hX hXY hY hN hL hC
    (by positivity : 0 ≤ 2 * (a : ℝ) + 1) h (activeIndices N Y) E
    (fun r hr => (mem_activeIndices hN (hX.trans_le hXY) r).mp hr)
    (fun r hr => by rw [hPhase]; exact hError r hr)
  have hscale : (2 / L) * traceMainScale N d =
      (N / (Real.pi * d)) * ((1 / L) * N ^ (-(1 / 2 : ℝ))) := by
    rw [inverse_sqrt_eq_sqrt_div hN]
    unfold traceMainScale
    field_simp [hN.ne', hd.ne', Real.pi_ne_zero, hL0.ne']
  have hscalar : N / (Real.pi * d) ≤ 64 / Real.pi := by
    apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * d) Real.pi_pos).mpr
    have hN64 : N ≤ d * 64 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).mp hdim
    nlinarith [mul_le_mul_of_nonneg_left hN64 Real.pi_pos.le]
  rw [trace_block_error_identity a hN hd hX hXY h T V, smul_smul, hscale, ← smul_smul,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < N / (Real.pi * d))]
  calc
    _ ≤ (64 / Real.pi) *
        ((8 * Real.sqrt 2 * C * ((2 + (2 * (a : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h) / L) *
          (N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) + N ^ (-1 : ℝ) * X ^ (3 / 4 + ε))) :=
      mul_le_mul hscalar hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The literal unnormalized two-term estimate displayed in (112).
Its constant is independent of the logarithmic conductor L. -/
theorem trace_block_bound (a : ℕ) {N d L X Y C ε : ℝ}
    (hN : 0 < N) (hdim : N / 64 ≤ d) (hX : 0 < X) (hXY : X ≤ Y)
    (hY : Y ≤ 2 * X) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (h : 𝓢(ℝ, ℂ)) (T : Finset ℕ) (V : ℤ → ℕ → ℂ)
    (hError : ∀ r ∈ activeIndices N Y, ‖traceIndexError a N L X Y h T V r‖ ≤
      C * Real.sqrt
        ((‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))) *
          (‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ)) +
            weightVariation (2 * (a : ℝ) + 1) L X Y N h r)) * X ^ (3 / 4 + ε)) :
    ‖(primeTraceBlock a N d L X Y h T V -
      (∫ u in X..Y, (traceDimensionScale a N d * M a 2 (u / N) / u) • h (Real.log u / L)))‖ ≤
      (256 * Real.sqrt 2 * C *
        ((2 + (2 * (a : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h) / Real.pi) *
        (N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) + N ^ (-1 : ℝ) * X ^ (3 / 4 + ε)) := by
  have hL0 : 0 < L := by linarith
  have hb := normalized_trace_block_bound a hN hdim hX hXY hY hL hC h T V hError
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / L)] at hb
  have hc :
      (512 * Real.sqrt 2 * C *
        ((2 + (2 * (a : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h) / (Real.pi * L)) *
        (N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) + N ^ (-1 : ℝ) * X ^ (3 / 4 + ε)) =
      (2 / L) *
        ((256 * Real.sqrt 2 * C *
          ((2 + (2 * (a : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h) / Real.pi) *
          (N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) + N ^ (-1 : ℝ) * X ^ (3 / 4 + ε))) := by
    field_simp [hL0.ne', Real.pi_ne_zero]
    ring
  rw [hc] at hb
  exact le_of_mul_le_mul_left hb (by positivity : (0 : ℝ) < 2 / L)

end DepthAspect.SignedDensity
