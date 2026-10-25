import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Choosing a strict Fourier-support endpoint from compact containment. -/
open Set
namespace DepthAspect.SupportEndpoint

/-- Compact containment in an open symmetric interval supplies a strictly
smaller closed interval, including when the compact set is empty. -/
theorem compact_subset_symmetric_interval {K : Set ℝ} (hK : IsCompact K)
    {b : ℝ} (hb : 0 < b) (hsub : K ⊆ Ioo (-b) b) :
    ∃ s : ℝ, 0 < s ∧ s < b ∧ K ⊆ Icc (-s) s := by
  rcases K.eq_empty_or_nonempty with h | hne
  · refine ⟨b / 2, by positivity, by linarith, ?_⟩
    simp [h]
  · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
      (continuous_abs : Continuous (fun x : ℝ => |x|)).continuousOn
    have hxb : |x| < b := abs_lt.mpr (hsub hx)
    refine ⟨(|x| + b) / 2, by linarith [abs_nonneg x], by linarith, ?_⟩
    intro y hy
    have hyx : |y| ≤ |x| := hmax hy
    exact abs_le.mp (by linarith)

/-- This version uses the closed support, the usual meaning of compact
Fourier support in the density theorems. -/
theorem compact_support_endpoint {E : Type*} [Zero E] (f : ℝ → E)
    (hf : HasCompactSupport f) {b : ℝ} (hb : 0 < b)
    (hsub : tsupport f ⊆ Ioo (-b) b) :
    ∃ s : ℝ, 0 < s ∧ s < b ∧ Function.support f ⊆ Icc (-s) s := by
  obtain ⟨s, hs0, hsb, hs⟩ := compact_subset_symmetric_interval hf hb hsub
  exact ⟨s, hs0, hsb, (subset_closure).trans hs⟩

/-- Containment of the closed support in a bounded interval already implies
compact support on the real line; no additional compactness premise is needed. -/
theorem support_endpoint_of_tsupport_subset {E : Type*} [Zero E] (f : ℝ → E)
    {b : ℝ} (hb : 0 < b) (hsub : tsupport f ⊆ Ioo (-b) b) :
    ∃ s : ℝ, 0 < s ∧ s < b ∧ Function.support f ⊆ Icc (-s) s := by
  have hf : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
      (hsub.trans Ioo_subset_Icc_self)
  exact compact_support_endpoint f hf hb hsub

end DepthAspect.SupportEndpoint
