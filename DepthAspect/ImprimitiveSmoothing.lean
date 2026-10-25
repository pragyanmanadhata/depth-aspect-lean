import DepthAspect.MellinContour
import DepthAspect.MellinSmoothing
import DepthAspect.HalfPlaneEulerBound
import DepthAspect.ImprimitiveBoundary

/-!
# Equation (102) for the literal imprimitive character

The only analytic size input is the primitive-character strip bound (100).
The finite Euler correction, entire continuation, Mellin representation,
contour shift, and remainder bound are proved in the imported chain. In
particular neither (101) nor (102) is an assumption of this theorem.
-/

open MeasureTheory
open scoped BigOperators
namespace DepthAspect.ImprimitiveSmoothing

open ImprimitiveCharacter ImprimitiveLSeries

/-- The nonprincipal primitive-character GRH consequence (100), stated for
all moduli before selecting a discriminant. The primitive condition is part
of this external theorem interface, and cannot be inferred from oddness. -/
def PrimitiveStripEstimate (η C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        C * ((q : ℝ) * (2 + |s.im|)) ^ η

/-- The initial contour contains the actual imprimitive Dirichlet series,
by the already proved continuation identity in the absolute half-plane. -/
theorem initial_line_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {f : ℕ} (hf : 0 < f) (x : ℝ) :
    MellinContour.lineIntegral (continuationCandidate χ f) x 1 =
      MellinSmoothing.initialIntegral (psiNat χ f) x := by
  unfold MellinContour.lineIntegral MellinSmoothing.initialIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  unfold MellinContour.kernel ContourShift.point MellinSmoothing.verticalPoint
  rw [continuationCandidate_agrees χ f hf.ne' (by simp)]
  simp only [Complex.ofReal_one]

/-- The precise smoothing conclusion (102), with an explicit finite Gamma
moment in the implied constant. -/
theorem exponential_smoothing_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) {f : ℕ} (hf : 0 < f)
    {x η C : ℝ} (hx : 1 ≤ x) (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hprimitive : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        C * ((q : ℝ) * (2 + |s.im|)) ^ η) :
    ‖continuationCandidate χ f 1 -
      ∑' n : ℕ, MellinSmoothing.smoothedTerm (psiNat χ f) x n‖ ≤
      (((2 * Real.pi)⁻¹ * MellinContour.gammaMoment (-1 / 2 + η) η) *
        (C * HalfPlaneEulerBound.boundConstant η)) *
          ((q : ℝ) * (f : ℝ) ^ 2) ^ η * x ^ (-1 / 2 + η) := by
  let D : ℝ := (q : ℝ) * (f : ℝ) ^ 2
  let K : ℝ := (C * HalfPlaneEulerBound.boundConstant η) * D ^ η
  have hK : 0 ≤ K := mul_nonneg
    (mul_nonneg hC (HalfPlaneEulerBound.boundConstant_pos η).le)
    (Real.rpow_nonneg (by unfold D; positivity) _)
  have hgrowth (s : ℂ) (hs : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) :
      ‖continuationCandidate χ f s‖ ≤ K * (2 + |s.im|) ^ η := by
    exact HalfPlaneEulerBound.continuation_bound χ f hf hs hη0 hC (hprimitive s hs hs2)
  have h := MellinContour.smoothing_remainder_bound
    (continuationCandidate_differentiable χ hχ f) hx hη0 hη hK hgrowth
  rw [initial_line_eq χ hf x,
    ← MellinSmoothing.smoothed_eq_initialIntegral (psiNat χ f)
      (psiNat_norm_le_one χ f) (by linarith)] at h
  rw [norm_sub_rev]
  calc
    _ ≤ ((2 * Real.pi)⁻¹ * MellinContour.gammaMoment (-1 / 2 + η) η) * K *
        x ^ (-1 / 2 + η) := h
    _ = _ := by dsimp [K, D]; ring

/-- Agreement with the ordered boundary value is discharged by the proved
boundary theorem, rather than requested as another hypothesis. -/
theorem ordered_exponential_smoothing_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) {f : ℕ} (hf : 0 < f)
    {x η C : ℝ} (hx : 1 ≤ x) (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hprimitive : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        C * ((q : ℝ) * (2 + |s.im|)) ^ η) :
    ‖ClassNumberGrowth.imprimitiveLAtOne χ hχ hq f hf -
      ∑' n : ℕ, MellinSmoothing.smoothedTerm (psiNat χ f) x n‖ ≤
      (((2 * Real.pi)⁻¹ * MellinContour.gammaMoment (-1 / 2 + η) η) *
        (C * HalfPlaneEulerBound.boundConstant η)) *
          ((q : ℝ) * (f : ℝ) ^ 2) ^ η * x ^ (-1 / 2 + η) := by
  rw [← ImprimitiveBoundary.continuation_one_eq_ordered χ hχ hq f hf]
  exact exponential_smoothing_bound χ hχ hf hx hη0 hη hC hprimitive

/-- The final GRH-facing form requests primitiveness of the actual
character. An arbitrary odd imprimitive character cannot be passed through
the primitive GRH estimate without further argument. -/
theorem smoothing_bound_of_primitive_GRH {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hprim : χ.IsPrimitive)
    {f : ℕ} (hf : 0 < f) {x η C : ℝ}
    (hx : 1 ≤ x) (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hC : 0 ≤ C)
    (hGRH : PrimitiveStripEstimate η C) :
    ‖continuationCandidate χ f 1 -
      ∑' n : ℕ, MellinSmoothing.smoothedTerm (psiNat χ f) x n‖ ≤
      (((2 * Real.pi)⁻¹ * MellinContour.gammaMoment (-1 / 2 + η) η) *
        (C * HalfPlaneEulerBound.boundConstant η)) *
          ((q : ℝ) * (f : ℝ) ^ 2) ^ η * x ^ (-1 / 2 + η) := by
  exact exponential_smoothing_bound χ hχ hf hx hη0 hη hC
    (hGRH q χ hprim (odd_character_ne_one χ hχ))

end DepthAspect.ImprimitiveSmoothing
