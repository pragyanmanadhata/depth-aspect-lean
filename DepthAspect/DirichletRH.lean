import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The actual primitive Dirichlet Riemann-hypothesis assumption

This is a zero-location predicate for Mathlib's analytically continued
L-functions. It is not a prime-sum or growth estimate. The primitive principal
character of conductor one is represented explicitly by Mathlib's existing
Riemann hypothesis for zeta, including its exclusion of the totalized pole.
The cited general consequences are packaged separately in GRHConsequences.
-/
namespace DepthAspect.DirichletRH

/-- The trivial zero locations determined by the character parity. For a
nonprincipal even primitive character, zero itself is a trivial zero. -/
def IsTrivialZero {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  (χ.Even ∧ ∃ n : ℕ, s = -2 * (n : ℂ)) ∨
  (χ.Odd ∧ ∃ n : ℕ, s = -(2 * (n : ℂ) + 1))

/-- Primitive Dirichlet RH in zero-location form. The first conjunct is the
actual conductor-one zeta case; the second covers every nonprincipal primitive
character uniformly. Only the nonprincipal functions occur in that conjunct,
so their value at one is not a totalized pole value. -/
def PrimitiveDirichletRH : Prop :=
  RiemannHypothesis ∧
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ,
      DirichletCharacter.LFunction χ s = 0 → ¬ IsTrivialZero χ s → s.re = 1 / 2

/-- The principal character of conductor one is visibly included. -/
theorem level_one_zero_location (hRH : PrimitiveDirichletRH)
    (χ : DirichletCharacter ℂ 1) (s : ℂ)
    (hz : DirichletCharacter.LFunction χ s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (hpole : s ≠ 1) :
    s.re = 1 / 2 := by
  apply hRH.1 s
  · simpa only [DirichletCharacter.LFunction_modOne_eq] using hz
  · exact htriv
  · exact hpole

/-- The nonprincipal component refers directly to the actual L-function. -/
theorem nonprincipal_zero_location (hRH : PrimitiveDirichletRH)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ)
    (hz : DirichletCharacter.LFunction χ s = 0) (htriv : ¬ IsTrivialZero χ s) :
    s.re = 1 / 2 := hRH.2 q χ hprim hne s hz htriv

end DepthAspect.DirichletRH
