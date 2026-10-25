import DepthAspect.ClassNumberGrowth
import DepthAspect.EulerFactorBounds

/-!
# The printed constant from the shorter ordered-series proof

This route reaches the exact constant stated in Lemma 2.2 independently of
the Euler product. The separate Euler modules still certify the paper's
displayed intermediate identities.
-/

namespace DepthAspect.ImprimitivePaperConstant
open ClassNumberGrowth EulerFactorBounds

theorem imprimitive_exact_constant {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (f : ℕ) (hf : 0 < f) {δ : ℝ} (hδ : 0 < δ) :
    ‖imprimitiveLAtOne χ hχ hq f hf‖ ≤ explicitConstant δ *
      ((q : ℝ) * (f : ℝ) ^ 2) ^ δ := by
  exact (imprimitiveLAtOne_power_bound χ hχ hq f hf hδ).trans
    (mul_le_mul_of_nonneg_right (ordered_constant_le_explicit hδ)
      (Real.rpow_nonneg (by positivity) _))

theorem hurwitz_exact_constant {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (f : ℕ) (hf : 0 < f) {δ H : ℝ} (hδ : 0 < δ)
    (hformula : H = Real.sqrt ((q : ℝ) * (f : ℝ) ^ 2) / Real.pi *
      (imprimitiveLAtOne χ hχ hq f hf).re) :
    H ≤ explicitConstant δ * ((q : ℝ) * (f : ℝ) ^ 2) ^ (1 / 2 + δ) := by
  apply (hurwitz_growth χ hχ hq f hf hδ hformula).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  have hpi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  exact (div_le_self (by positivity : 0 ≤ 2 + δ⁻¹) hpi).trans
    (ordered_constant_le_explicit hδ)

/-- A single constant works simultaneously for every admissible negative
discriminant, and this constant is literally the one printed in the paper. -/
theorem uniform_hurwitz_exact_constant (H : ℤ → ℝ)
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨ Nonempty (ClassFormulaData H D))
    {δ : ℝ} (hδ : 0 < δ) :
    0 < explicitConstant δ ∧ ∀ D : ℤ, D < 0 →
      H D ≤ explicitConstant δ * |(D : ℝ)| ^ (1 / 2 + δ) := by
  refine ⟨explicitConstant_pos hδ, ?_⟩
  intro D hD
  rcases hformula D hD with hz | hdata
  · rw [hz]
    exact mul_nonneg (explicitConstant_pos hδ).le
      (Real.rpow_nonneg (abs_nonneg _) _)
  · let data := Classical.choice hdata
    rw [data.discriminant]
    exact hurwitz_exact_constant data.character data.odd data.modulus_pos
      data.conductor data.conductor_pos hδ data.formula

end DepthAspect.ImprimitivePaperConstant
