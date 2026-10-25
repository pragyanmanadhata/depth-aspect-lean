import DepthAspect.ActiveTraceIndices
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite prime/trace exchange and moving lower endpoints

Both identities retain the actual active trace-index set. The integer
condition N*r²/16<p becomes the exact lower endpoint max(X,N*r²/16).
For integrals this is the same strict indicator, so a zero-discriminant
boundary creates no extra boundary term.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set
open scoped BigOperators

/-- Increasing the real prime endpoint only enlarges the actual trace set. -/
theorem activeIndices_mono {N X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hXY : X ≤ Y) :
    activeIndices N X ⊆ activeIndices N Y := by
  intro r hr
  exact (mem_activeIndices hN (hX.trans_le hXY) r).mpr
    (((mem_activeIndices hN hX r).mp hr).trans_le hXY)

theorem activeIndices_filter {N X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hXY : X ≤ Y) :
    (activeIndices N Y).filter (fun r : ℤ => N * (r : ℝ) ^ 2 / 16 < X) = activeIndices N X := by
  classical
  ext r
  rw [Finset.mem_filter, mem_activeIndices hN (hX.trans_le hXY), mem_activeIndices hN hX]
  exact and_iff_right_of_imp (fun hr => hr.trans_le hXY)

/-- Swap the literal finite prime and trace sums. There is no prime-count
or trace-count assumption in this identity. -/
theorem active_prime_sum_comm {N X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (_hXY : X ≤ Y)
    (T : Finset ℕ) (F : ℕ → ℤ → ℂ) :
    (∑ p ∈ T.filter (fun p : ℕ => X < (p : ℝ) ∧ (p : ℝ) ≤ Y),
      ∑ r ∈ activeIndices N p, F p r) =
      ∑ r ∈ activeIndices N Y,
        ∑ p ∈ T.filter (fun p : ℕ => max X (N * (r : ℝ) ^ 2 / 16) < p ∧ (p : ℝ) ≤ Y), F p r := by
  classical
  have hexpand (p : ℕ) (hp : p ∈ T.filter (fun p : ℕ => X < (p : ℝ) ∧ (p : ℝ) ≤ Y)) :
      (∑ r ∈ activeIndices N p, F p r) =
        ∑ r ∈ activeIndices N Y, if N * (r : ℝ) ^ 2 / 16 < p then F p r else 0 := by
    have hb := (Finset.mem_filter.mp hp).2
    rw [← Finset.sum_filter, activeIndices_filter hN (hX.trans hb.1) hb.2]
  calc
    _ = ∑ p ∈ T.filter (fun p : ℕ => X < (p : ℝ) ∧ (p : ℝ) ≤ Y),
        ∑ r ∈ activeIndices N Y, if N * (r : ℝ) ^ 2 / 16 < p then F p r else 0 :=
      Finset.sum_congr rfl hexpand
    _ = ∑ r ∈ activeIndices N Y,
        ∑ p ∈ T.filter (fun p : ℕ => X < (p : ℝ) ∧ (p : ℝ) ≤ Y),
          if N * (r : ℝ) ^ 2 / 16 < p then F p r else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h₁ : X < (p : ℝ) <;>
        by_cases h₂ : (p : ℝ) ≤ Y <;>
          by_cases h₃ : N * (r : ℝ) ^ 2 / 16 < p <;>
            simp [h₁, h₂, h₃]

/-- The strict discriminant cutoff produces precisely the moving lower
endpoint, with equality boundaries ignored only by the Lebesgue integral. -/
theorem integral_strict_cutoff {X Y c : ℝ} (hXY : X ≤ Y) (hcY : c ≤ Y)
    (f : ℝ → ℂ) :
    (∫ u in X..Y, if c < u then f u else 0) = ∫ u in max X c..Y, f u := by
  have hmax : max X c ≤ Y := max_le hXY hcY
  rw [intervalIntegral.integral_of_le hXY, intervalIntegral.integral_of_le hmax]
  change (∫ u, (Ioi c).indicator f u ∂volume.restrict (Ioc X Y)) = _
  rw [MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have he : Ioi c ∩ Ioc X Y = Ioc (max X c) Y := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc, max_lt_iff]
    tauto
  rw [he]

/-- The family of moving lower endpoints is exactly the integral of the
active finite lattice at each real argument. -/
theorem active_integral_sum_comm {N X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hXY : X ≤ Y)
    (F : ℤ → ℝ → ℂ)
    (hF : ∀ r ∈ activeIndices N Y, IntervalIntegrable (F r) volume X Y) :
    (∑ r ∈ activeIndices N Y, ∫ u in max X (N * (r : ℝ) ^ 2 / 16)..Y, F r u) =
      ∫ u in X..Y, ∑ r ∈ activeIndices N u, F r u := by
  classical
  have hY : 0 < Y := hX.trans_le hXY
  have hi (r : ℤ) (hr : r ∈ activeIndices N Y) :
      IntervalIntegrable (fun u => if N * (r : ℝ) ^ 2 / 16 < u then F r u else 0)
        volume X Y := by
    have hFr := hF r hr
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hXY] at hFr ⊢
    exact hFr.indicator measurableSet_Ioi
  have he : (∑ r ∈ activeIndices N Y, ∫ u in max X (N * (r : ℝ) ^ 2 / 16)..Y, F r u) =
      ∑ r ∈ activeIndices N Y,
        ∫ u in X..Y, if N * (r : ℝ) ^ 2 / 16 < u then F r u else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    exact (integral_strict_cutoff hXY ((mem_activeIndices hN hY r).mp hr).le (F r)).symm
  rw [he, ← intervalIntegral.integral_finsetSum hi]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc X Y := by simpa only [uIcc_of_le hXY] using hu
  change (∑ r ∈ activeIndices N Y,
    if N * (r : ℝ) ^ 2 / 16 < u then F r u else 0) =
      ∑ r ∈ activeIndices N u, F r u
  rw [← Finset.sum_filter, activeIndices_filter hN (hX.trans_le hu'.1) hu'.2]

end DepthAspect.SignedDensity
