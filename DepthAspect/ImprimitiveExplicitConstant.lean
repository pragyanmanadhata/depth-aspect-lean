import DepthAspect.ImprimitiveBoundary
import DepthAspect.EulerFactorBounds

open scoped BigOperators
namespace DepthAspect.ImprimitiveExplicitConstant

open ImprimitiveLSeries ImprimitiveBoundary ClassNumberGrowth

/-- The exact local factor at s=1, with no hidden analytic convention. -/
theorem correction_at_one {q : ℕ} (χ : DirichletCharacter ℂ q) (f p : ℕ) :
    ImprimitiveLSeries.correction χ f p 1 =
      EulerFactorBounds.correction (χ (p : ZMod q)) (p : ℝ) (f.factorization p) := by
  simp only [ImprimitiveLSeries.correction, EulerFactorBounds.correction,
    Complex.cpow_neg_one, Complex.ofReal_natCast]

/-- Equation (7) at one with the actual ordered value and the literal
finite geometric polynomials. -/
theorem imprimitive_one_eq_product {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) :
    imprimitiveLAtOne χ hχ hq f hf = DirichletCharacter.LFunction χ 1 *
      ∏ p ∈ f.primeFactors, EulerFactorBounds.correction (χ (p : ZMod q))
        (p : ℝ) (f.factorization p) := by
  rw [← continuation_one_eq_ordered χ hχ hq f hf]
  simp only [continuationCandidate, correctionProduct, correction_at_one]

/-- The precise constant Cδ=Aδ(2+2/(eδ)) from the proof of Lemma 2.2,
now for the actual imprimitive ordered/analytic value. -/
theorem imprimitive_one_exact_constant_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f)
    {δ : ℝ} (hδ : 0 < δ) :
    ‖imprimitiveLAtOne χ hχ hq f hf‖ ≤ EulerFactorBounds.explicitConstant δ *
      ((q : ℝ) * (f : ℝ) ^ 2) ^ δ := by
  rw [imprimitive_one_eq_product χ hχ hq f hf]
  apply EulerFactorBounds.norm_value_times_correction_bound hδ
    (by exact_mod_cast hq : (1 : ℝ) ≤ q) f hf rfl
    (DirichletCharacter.LFunction χ 1) (primitive_LFunction_one_log_bound χ hχ hq)
    (fun p => χ (p : ZMod q))
  intro p hp
  exact χ.norm_le_one _

/-- The same explicit constant also works for H, exactly as asserted in
Lemma 2.2, assuming only the cited class-number identity. -/
theorem hurwitz_exact_constant_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f)
    {δ H : ℝ} (hδ : 0 < δ)
    (hformula : H = Real.sqrt ((q : ℝ) * (f : ℝ) ^ 2) / Real.pi *
      (imprimitiveLAtOne χ hχ hq f hf).re) :
    H ≤ EulerFactorBounds.explicitConstant δ *
      ((q : ℝ) * (f : ℝ) ^ 2) ^ (1 / 2 + δ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf
  have hD0 : 0 < (q : ℝ) * (f : ℝ) ^ 2 := by positivity
  have hC := (EulerFactorBounds.explicitConstant_pos hδ).le
  have hpi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  calc
    H = _ := hformula
    _ ≤ Real.sqrt ((q : ℝ) * (f : ℝ) ^ 2) / Real.pi *
        (EulerFactorBounds.explicitConstant δ * ((q : ℝ) * (f : ℝ) ^ 2) ^ δ) :=
      mul_le_mul_of_nonneg_left
        ((Complex.re_le_norm _).trans
          (imprimitive_one_exact_constant_bound χ hχ hq f hf hδ)) (by positivity)
    _ = (EulerFactorBounds.explicitConstant δ / Real.pi) *
        ((q : ℝ) * (f : ℝ) ^ 2) ^ (1 / 2 + δ) := by
      rw [Real.rpow_add hD0, ← Real.sqrt_eq_rpow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_self hC hpi)
      (Real.rpow_nonneg hD0.le _)


end DepthAspect.ImprimitiveExplicitConstant
