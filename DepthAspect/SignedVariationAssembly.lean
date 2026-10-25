import DepthAspect.TraceWeightVariation
import DepthAspect.SignedBlockAssembly

/-!
# Equations (111)--(112) for the actual trace-index weights

This composes the actual Schwartz variation bound with the actual integer
index count. The individual arithmetic prime-average bound is the sole
intermediate premise, to be supplied by the character-average module.
-/
namespace DepthAspect.SignedVariationAssembly

open MeasureTheory Set TraceWeightVariation SignedBlockAssembly
open scoped BigOperators SchwartzMap

noncomputable def traceParameter (N : ℝ) (r : ℤ) : ℝ := Real.sqrt N * (r : ℝ) / 4
noncomputable def lowerEndpoint (X N : ℝ) (r : ℤ) : ℝ := max X ((traceParameter N r) ^ 2)
noncomputable def weightVariation (m L X Y N : ℝ) (h : 𝓢(ℝ, ℂ)) (r : ℤ) : ℝ :=
  ∫ u in lowerEndpoint X N r..Y, ‖deriv (traceWeight m (traceParameter N r) L h) u‖

theorem traceParameter_sq {N : ℝ} (hN : 0 ≤ N) (r : ℤ) :
    (traceParameter N r) ^ 2 = N * (r : ℝ) ^ 2 / 16 := by
  unfold traceParameter
  rw [div_pow, mul_pow, Real.sq_sqrt hN]
  norm_num

/-- The actual total normalized block error. All weight variation premises
from the abstract assembly are discharged by the literal Schwartz weight. -/
theorem actual_three_quarter_block_bound {X Y N L C m ε : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hY : Y ≤ 2 * X) (hN : 0 < N)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (h : 𝓢(ℝ, ℂ)) (S : Finset ℤ) (E : ℤ → ℂ)
    (hS : ∀ r ∈ S, N * (r : ℝ) ^ 2 / 16 < Y)
    (hE : ∀ r ∈ S, ‖E r‖ ≤ C * Real.sqrt
      ((‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))) *
        (‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ)) +
          weightVariation m L X Y N h r)) * X ^ (3 / 4 + ε)) :
    ‖((1 / L) * N ^ (-(1 / 2 : ℝ))) • (∑ r ∈ S, E r)‖ ≤
      (8 * Real.sqrt 2 * C * ((2 + m * (Real.pi / 2)) * schwartzSize h) / L) *
        (N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) +
          N ^ (-1 : ℝ) * X ^ (3 / 4 + ε)) := by
  have hH : 0 ≤ (2 + m * (Real.pi / 2)) * schwartzSize h := by
    have hpi := Real.pi_pos
    unfold schwartzSize
    positivity
  have hend (r : ℤ) (hr : r ∈ S) : lowerEndpoint X N r ≤ Y := by
    unfold lowerEndpoint
    rw [traceParameter_sq hN.le]
    exact max_le hXY (hS r hr).le
  apply three_quarter_block_bound hX hN (by linarith) hC hH S E
    (fun _ => ‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ)))
    (weightVariation m L X Y N h)
    (fun r hr => (hS r hr).trans_le hY)
    (fun _ _ => by positivity) ?_ ?_ hE
  · intro r hr
    exact intervalIntegral.integral_nonneg (hend r hr) (fun _ _ => norm_nonneg _)
  · intro r hr
    exact (schwartz_traceWeight_variation h hm hL hX
      (le_max_left _ _) (hend r hr) hY (le_max_right _ _)).2.2

end DepthAspect.SignedVariationAssembly
