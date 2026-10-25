import DepthAspect.ProjectiveCharts
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Fixed lines and roots of the associated binary quadratic form

For an invertible two-by-two matrix over a commutative ring, a primitive
vector lies on a fixed line precisely when its associated quadratic vanishes.
The scalar in the fixed-line condition is proved to be a unit. The predicate
descends to the actual unit-orbit quotient used in `ProjectiveCharts`.
-/

namespace DepthAspect.FixedLines

open ProjectiveCharts

variable {R : Type*} [CommRing R]

/-- The image of a primitive vector is a unit multiple of that vector. -/
def FixedPair (M : Matrix (Fin 2) (Fin 2) R) (p : PrimitivePair R) : Prop :=
  ∃ u : Rˣ,
    M 0 0 * p.1.1 + M 0 1 * p.1.2 = (u : R) * p.1.1 ∧
    M 1 0 * p.1.1 + M 1 1 * p.1.2 = (u : R) * p.1.2

theorem fixedPair_of_orbit (M : Matrix (Fin 2) (Fin 2) R)
    {p q : PrimitivePair R} (h : orbitRel R p q) (hp : FixedPair M p) :
    FixedPair M q := by
  obtain ⟨v, h1, h2⟩ := h
  obtain ⟨u, hp1, hp2⟩ := hp
  refine ⟨u, ?_, ?_⟩
  · rw [h1, h2]
    calc
      _ = (v : R) * (M 0 0 * p.1.1 + M 0 1 * p.1.2) := by ring
      _ = _ := by rw [hp1]; ring
  · rw [h1, h2]
    calc
      _ = (v : R) * (M 1 0 * p.1.1 + M 1 1 * p.1.2) := by ring
      _ = _ := by rw [hp2]; ring

theorem fixedPair_orbit_iff (M : Matrix (Fin 2) (Fin 2) R)
    {p q : PrimitivePair R} (h : orbitRel R p q) : FixedPair M p ↔ FixedPair M q :=
  ⟨fixedPair_of_orbit M h,
    fixedPair_of_orbit M ((orbitSetoid R).iseqv.symm h)⟩

/-- In the `(x,1)` chart the proportionality scalar is the lower coordinate
of the matrix image; the determinant identity proves it is a unit. -/
theorem first_chart_fixed_iff (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : IsUnit (Matrix.det M)) (x : R) :
    FixedPair M (representative R (.inl x)) ↔
      M 1 0 * x ^ 2 + (M 1 1 - M 0 0) * x - M 0 1 = 0 := by
  constructor
  · rintro ⟨u, h1, h2⟩
    change M 0 0 * x + M 0 1 * 1 = (u : R) * x at h1
    change M 1 0 * x + M 1 1 * 1 = (u : R) * 1 at h2
    linear_combination x * h2 - h1
  · intro hQ
    have hprod : (M 1 0 * x + M 1 1) * (M 0 0 - M 1 0 * x) = Matrix.det M := by
      rw [Matrix.det_fin_two]
      linear_combination -M 1 0 * hQ
    have hu : IsUnit (M 1 0 * x + M 1 1) :=
      (IsUnit.mul_iff.mp (hprod.symm ▸ hdet)).1
    obtain ⟨u, hu⟩ := hu
    refine ⟨u, ?_, ?_⟩
    · change M 0 0 * x + M 0 1 * 1 = (u : R) * x
      rw [hu]
      linear_combination -hQ
    · change M 1 0 * x + M 1 1 * 1 = (u : R) * 1
      simp [hu]

theorem second_chart_fixed_iff (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : IsUnit (Matrix.det M)) (y : {y : R // ¬ IsUnit y}) :
    FixedPair M (representative R (.inr y)) ↔
      M 1 0 + (M 1 1 - M 0 0) * y.1 - M 0 1 * y.1 ^ 2 = 0 := by
  constructor
  · rintro ⟨u, h1, h2⟩
    change M 0 0 * 1 + M 0 1 * y.1 = (u : R) * 1 at h1
    change M 1 0 * 1 + M 1 1 * y.1 = (u : R) * y.1 at h2
    linear_combination h2 - y.1 * h1
  · intro hQ
    have hprod : (M 0 0 + M 0 1 * y.1) * (M 1 1 - M 0 1 * y.1) = Matrix.det M := by
      rw [Matrix.det_fin_two]
      linear_combination M 0 1 * hQ
    have hu : IsUnit (M 0 0 + M 0 1 * y.1) :=
      (IsUnit.mul_iff.mp (hprod.symm ▸ hdet)).1
    obtain ⟨u, hu⟩ := hu
    refine ⟨u, ?_, ?_⟩
    · change M 0 0 * 1 + M 0 1 * y.1 = (u : R) * 1
      simp [hu]
    · change M 1 0 * 1 + M 1 1 * y.1 = (u : R) * y.1
      rw [hu]
      linear_combination hQ

theorem fixedPair_iff_form_zero (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : IsUnit (Matrix.det M)) (p : PrimitivePair R) :
    FixedPair M p ↔ form (M 1 0) (M 1 1 - M 0 0) (-M 0 1) p = 0 := by
  obtain ⟨c, hc⟩ := representative_exists p
  rw [← fixedPair_orbit_iff M hc, ← form_zero_invariant _ _ _ hc]
  cases c with
  | inl x => simpa [form, representative, sub_eq_add_neg] using first_chart_fixed_iff M hdet x
  | inr y => simpa [form, representative, sub_eq_add_neg] using second_chart_fixed_iff M hdet y

/-- Fixedness is a well-defined predicate on projective lines. -/
def IsFixed (M : Matrix (Fin 2) (Fin 2) R) : ProjectiveLine R → Prop :=
  Quotient.lift (FixedPair M) (fun _ _ h => propext (fixedPair_orbit_iff M h))

/-- The fixed-line condition is exactly the quotient-root condition used by
the dyadic cancellation argument. -/
theorem isFixed_iff_isRoot (M : Matrix (Fin 2) (Fin 2) R)
    (hdet : IsUnit (Matrix.det M)) (p : ProjectiveLine R) :
    IsFixed M p ↔ IsRoot (M 1 0) (M 1 1 - M 0 0) (-M 0 1) p := by
  refine Quotient.inductionOn p ?_
  exact fixedPair_iff_form_zero M hdet

end DepthAspect.FixedLines
