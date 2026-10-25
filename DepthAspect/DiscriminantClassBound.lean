import DepthAspect.QuadraticDiscriminantL
import DepthAspect.ImprimitivePaperConstant

/-! Lemma 2.2 for the literal discriminant-indexed L-value and Hurwitz
class number, with the exact constant printed in the paper. The only input
is the cited general quadratic class-number formula. -/
namespace DepthAspect.DiscriminantClassBound
open QuadraticClassFormula QuadraticDiscriminantL ImprimitivePaperConstant

theorem conductor_size (D : ℤ) (hD : IsNegativeDiscriminant D) :
    ((datum D hD).fundamental.natAbs : ℝ) * ((datum D hD).conductor : ℝ) ^ 2 =
      (D.natAbs : ℝ) := by
  have h := congrArg Int.natAbs (datum D hD).factorization
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
  exact_mod_cast h.symm

/-- The exact first inequality of (6), for the actual ordered value of
the coefficient sequence ψ_D(n)=χ_d(n/gcd(n,f)). -/
theorem LAtOne_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (D : ℤ) (hD : IsNegativeDiscriminant D) {δ : ℝ} (hδ : 0 < δ) :
    ‖LAtOne G D‖ ≤ EulerFactorBounds.explicitConstant δ * |(D : ℝ)| ^ δ := by
  have h := imprimitive_exact_constant
    (character G D hD) (character_odd G D hD) (modulus_pos D hD)
    (datum D hD).conductor (datum D hD).conductor_pos hδ
  rw [conductor_size D hD] at h
  simpa only [LAtOne, dif_pos hD, Nat.cast_natAbs, Int.cast_abs] using h

/-- The exact second inequality of (6), with the same explicit constant. -/
theorem hurwitz_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (D : ℤ) (hD : IsNegativeDiscriminant D) {δ : ℝ} (hδ : 0 < δ) :
    H D ≤ EulerFactorBounds.explicitConstant δ * |(D : ℝ)| ^ (1 / 2 + δ) := by
  have hneg : (D : ℝ) < 0 := by exact_mod_cast hD.1
  have hformula : H D =
      Real.sqrt (((datum D hD).fundamental.natAbs : ℝ) *
        ((datum D hD).conductor : ℝ) ^ 2) / Real.pi *
      (ClassNumberGrowth.imprimitiveLAtOne (character G D hD)
        (character_odd G D hD) (modulus_pos D hD)
        (datum D hD).conductor (datum D hD).conductor_pos).re := by
    rw [conductor_size D hD]
    simpa only [LAtOne, dif_pos hD, Nat.cast_natAbs, Int.cast_abs,
      abs_of_neg hneg] using QuadraticDiscriminantL.hurwitz_eq G D hD
  have h := hurwitz_exact_constant
    (character G D hD) (character_odd G D hD) (modulus_pos D hD)
    (datum D hD).conductor (datum D hD).conductor_pos hδ hformula
  rw [conductor_size D hD] at h
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h

/-- One positive constant depending only on δ works simultaneously for
both literal quantities at every negative quadratic discriminant. -/
theorem lemma_2_2 {δ : ℝ} (hδ : 0 < δ) :
    0 < EulerFactorBounds.explicitConstant δ ∧
      ∀ {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ), IsNegativeDiscriminant D →
        ‖LAtOne G D‖ ≤ EulerFactorBounds.explicitConstant δ * |(D : ℝ)| ^ δ ∧
        H D ≤ EulerFactorBounds.explicitConstant δ * |(D : ℝ)| ^ (1 / 2 + δ) := by
  refine ⟨EulerFactorBounds.explicitConstant_pos hδ, ?_⟩
  intro H G D hD
  exact ⟨LAtOne_bound G D hD hδ, hurwitz_bound G D hD hδ⟩

end DepthAspect.DiscriminantClassBound
