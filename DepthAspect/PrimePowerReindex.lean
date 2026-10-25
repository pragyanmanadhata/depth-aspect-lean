import DepthAspect.ExplicitFormulaModel
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Reindexing the actual finitely supported prime-power expression. -/
open scoped BigOperators FourierTransform SchwartzMap
namespace DepthAspect.ExplicitFormula

/-- The positive-exponent local series has exactly the same value as the
pair-indexed expression; support proves all required summability. -/
theorem primePowerSum_eq_iterated {L s : ℝ} (hL : 0 < L) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (α β : ℕ → ℂ) :
    primePowerSum L φ α β = ∑' p : ℕ, if p.Prime ∧ p ≠ 2 then
      ∑' j : ℕ, primePowerWeight α β p (j + 1) *
        (𝓕 φ : 𝓢(ℝ, ℂ)) (((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ) / L)
      else 0 := by
  have hs := PrimePowerSupport.primePowerTerm_summable hL hsupp (primePowerWeight α β)
  unfold primePowerSum
  rw [hs.tsum_prod]
  apply tsum_congr
  intro p
  by_cases hp : p.Prime ∧ p ≠ 2
  · rw [if_pos hp]
    have he := (hs.prod_factor p).sum_add_tsum_nat_add 1
    simpa [PrimePowerSupport.primePowerTerm, hp.1, hp.2] using he.symm
  · rw [if_neg hp]
    calc
      _ = ∑' j : ℕ, (0 : ℂ) := by
        apply tsum_congr
        intro j
        simp only [PrimePowerSupport.primePowerTerm]
        split_ifs with hj
        · exact (hp ⟨hj.1, hj.2.1⟩).elim
        · rfl
      _ = 0 := tsum_zero

end DepthAspect.ExplicitFormula
