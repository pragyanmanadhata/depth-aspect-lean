import DepthAspect.ImprimitiveSmoothing
import DepthAspect.QuadraticDiscriminantL

/-!
# The actual discriminant-uniform smoothing estimate

The character at each negative discriminant is its actual primitive quadratic
character. A single general strip-bound constant is chosen before D. The
conductor factors are converted to |D| by the literal fundamental
factorization, giving precisely the uniform dependence needed when summing
(102) over the primes and trace indices.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.NegativeDiscriminantSmoothing
open QuadraticClassFormula QuadraticDiscriminantL ImprimitiveSmoothing

/-- The explicit constant supplied by the proved Mellin argument. -/
def constant (η C : ℝ) : ℝ :=
  ((2 * Real.pi)⁻¹ * MellinContour.gammaMoment (-1 / 2 + η) η) *
    (C * HalfPlaneEulerBound.boundConstant η)

 theorem conductor_size (D : ℤ) (hD : IsNegativeDiscriminant D) :
    ((datum D hD).fundamental.natAbs : ℝ) * ((datum D hD).conductor : ℝ) ^ 2 =
      (D.natAbs : ℝ) := by
  have h := congrArg Int.natAbs (datum D hD).factorization
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at h
  exact_mod_cast h.symm

/-- Equation (102) for the literal discriminant-indexed L-value. No internal
smoothing or imprimitive L-bound is supplied as an assumption. -/
theorem smoothing_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (D : ℤ) (hD : IsNegativeDiscriminant D) {x η C : ℝ}
    (hx : 1 ≤ x) (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hGRH : PrimitiveStripEstimate η C) :
    ‖LAtOne G D - ∑' n : ℕ, MellinSmoothing.smoothedTerm (psi G D) x n‖ ≤
      constant η C * (D.natAbs : ℝ) ^ η * x ^ (-1 / 2 + η) := by
  letI : NeZero (datum D hD).fundamental.natAbs := ⟨(modulus_pos D hD).ne'⟩
  have hpsi : psi G D = ImprimitiveCharacter.psiNat (character G D hD)
      (datum D hD).conductor := by
    funext n
    simp only [psi, dif_pos hD]
  rw [LAtOne, dif_pos hD, hpsi]
  have h := ordered_exponential_smoothing_bound (character G D hD)
    (character_odd G D hD) (modulus_pos D hD) (datum D hD).conductor_pos
    hx hη0 hη hC
    (hGRH _ (character G D hD) (character_isPrimitive G D hD) (character_ne_one G D hD))
  rw [conductor_size D hD] at h
  exact h

end DepthAspect.NegativeDiscriminantSmoothing
