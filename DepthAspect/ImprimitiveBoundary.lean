import DepthAspect.ClassNumberGrowth
import DepthAspect.ImprimitiveLSeries
import DepthAspect.OrderedAbel

/-!
# Identification of the actual continuation with the ordered value

The analytic/ordered identification at one is proved using uniform Abel tails.
The only remaining class-number premise is the cited arithmetic identity for
the analytically continued function; it no longer needs to assert any separate
ordered-series identification or any size bound.
-/

open scoped BigOperators

namespace DepthAspect.ImprimitiveBoundary

open ImprimitiveCharacter ImprimitiveLSeries ClassNumberGrowth OrderedAbel

/-- The constructed entire continuation has the ordered value at one. -/
theorem continuation_one_eq_ordered {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) :
    continuationCandidate χ f 1 = imprimitiveLAtOne χ hχ hq f hf := by
  apply continuation_value_eq_ordered (psiNat χ f) (psiNat_norm_le_one χ f)
    (psiNat_partial_sum_norm_le χ hχ hq f hf) (imprimitiveLAtOne_limit χ hχ hq f hf)
    (continuationCandidate χ f) (continuationCandidate_differentiable χ hχ f).continuous.continuousAt
  intro σ hσ
  exact continuationCandidate_agrees χ f (Nat.ne_of_gt hf) (by simpa using hσ)

/-- The Euler identity at one in the canonical correctionProduct notation.
This interface is independent of the later quantitative factor bounds. -/
theorem imprimitive_one_eq_correctionProduct {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) :
    imprimitiveLAtOne χ hχ hq f hf =
      DirichletCharacter.LFunction χ 1 * correctionProduct χ f 1 := by
  rw [← continuation_one_eq_ordered χ hχ hq f hf]
  rfl

@[simp] theorem continuation_conductor_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    continuationCandidate χ 1 s = DirichletCharacter.LFunction χ s := by
  simp [continuationCandidate, correctionProduct]

/-- Equation (8) for Mathlib's actual analytically continued Dirichlet
L-function, obtained from the ordered complete-period argument. -/
theorem primitive_LFunction_one_log_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 + Real.log (q : ℝ) := by
  have heq := continuation_one_eq_ordered χ hχ hq 1 (by decide)
  rw [continuation_conductor_one] at heq
  rw [heq]
  simpa using imprimitiveLAtOne_log_bound χ hχ hq 1 (by decide)

/-- Any entire continuation with the defining agreement on Re(s)>1 also
has that same ordered value. The choice of continuation is immaterial. -/
theorem any_continuation_one_eq_ordered {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hseries : ∀ s : ℂ, 1 < s.re → G s = LSeries (psiNat χ f) s) :
    G 1 = imprimitiveLAtOne χ hχ hq f hf := by
  rw [continuation_eq_product χ hχ f (Nat.ne_of_gt hf) G hG hseries]
  exact continuation_one_eq_ordered χ hχ hq f hf

/-- The cited arithmetic class-number formula in its usual analytic form
constructs the growth module's ordered-form interface. The conversion itself
is a theorem, rather than an additional assumption. -/
theorem classFormulaData_of_analytic_formula (H : ℤ → ℝ) (D : ℤ)
    (q f : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.Odd)
    (hq : 0 < q) (hf : 0 < f)
    (hD : |(D : ℝ)| = (q : ℝ) * (f : ℝ) ^ 2)
    (hformula : H D = Real.sqrt ((q : ℝ) * (f : ℝ) ^ 2) / Real.pi *
      (continuationCandidate χ f 1).re) :
    Nonempty (ClassFormulaData H D) := by
  refine ⟨⟨q, f, χ, hχ, hq, hf, hD, ?_⟩⟩
  rw [continuation_one_eq_ordered χ hχ hq f hf] at hformula
  exact hformula

/-- The cited class-number formula in its usual analytic form. The value is
our uniquely determined entire continuation of the literal imprimitive
Dirichlet series; no growth estimate or ordered-value identification is a field. -/
structure AnalyticClassFormulaData (H : ℤ → ℝ) (D : ℤ) where
  modulus : ℕ
  conductor : ℕ
  character : DirichletCharacter ℂ modulus
  odd : character.Odd
  modulus_pos : 0 < modulus
  conductor_pos : 0 < conductor
  discriminant : |(D : ℝ)| = (modulus : ℝ) * (conductor : ℝ) ^ 2
  formula : H D = Real.sqrt ((modulus : ℝ) * (conductor : ℝ) ^ 2) / Real.pi *
    (@continuationCandidate modulus ⟨Nat.ne_of_gt modulus_pos⟩ character conductor 1).re

/-- The analytic class-number data imply the ordered-form data used by the
proved growth theorem. The conversion follows from the proved Abel boundary
identification. -/
def AnalyticClassFormulaData.toClassFormulaData {H : ℤ → ℝ} {D : ℤ}
    (data : AnalyticClassFormulaData H D) : ClassFormulaData H D := by
  letI : NeZero data.modulus := ⟨Nat.ne_of_gt data.modulus_pos⟩
  refine ⟨data.modulus, data.conductor, data.character, data.odd,
    data.modulus_pos, data.conductor_pos, data.discriminant, ?_⟩
  have h := data.formula
  rw [continuation_one_eq_ordered data.character data.odd data.modulus_pos
    data.conductor data.conductor_pos] at h
  exact h

/-- Uniform class-number growth directly from the cited analytic formula. -/
theorem uniform_hurwitz_growth_of_analytic (H : ℤ → ℝ)
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨ Nonempty (AnalyticClassFormulaData H D))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℤ, D < 0 → H D ≤ C * |(D : ℝ)| ^ (1 / 2 + δ) := by
  apply ClassNumberGrowth.uniform_hurwitz_growth H _ hδ
  intro D hD
  rcases hformula D hD with hz | hd
  · exact Or.inl hz
  · rcases hd with ⟨data⟩
    exact Or.inr ⟨data.toClassFormulaData⟩

end DepthAspect.ImprimitiveBoundary
