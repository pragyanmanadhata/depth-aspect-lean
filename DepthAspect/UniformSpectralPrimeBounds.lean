import DepthAspect.SpectralPrimeBounds
import DepthAspect.UniformTraceBounds
import DepthAspect.ImprimitiveBoundary

/-!
# Spectral prime estimates from the general cited arithmetic inputs

The data below contain the general oldform basis, general Hecke eigenvector
relation, general full-space Popa formula and its general projective local
interpretation, general Martin dimension identity, and general class-number
formula. No dyadic estimate or density conclusion is a field.
-/
namespace DepthAspect.UnsignedDensity

open SpectralFamily TraceBounds TracePrimeApplications PrimePowerApplications Module
open scoped BigOperators

/-- Literal finite primitive-class data. Nonnegativity and existence of a
form at a nonzero primitive weight are derived from this definition. -/
structure PrimitiveClassData where
  labels : ℤ → Type
  finite : ∀ D, Fintype (labels D)
  automorphismCount : ℤ → ℕ
  representatives : ∀ D, labels D → PrimitiveForm D
  value : ℤ → ℝ
  definition : ∀ D : ℤ, D < 0 → value D =
    @primitiveClassWeight (labels D) (finite D) (automorphismCount D)

namespace PrimitiveClassData

theorem nonneg (P : PrimitiveClassData) (D : ℤ) (hD : D < 0) : 0 ≤ P.value D := by
  rw [P.definition D hD]
  exact @primitiveClassWeight_nonneg (P.labels D) (P.finite D) (P.automorphismCount D)

theorem forms (P : PrimitiveClassData) (D : ℤ) (hD : D < 0)
    (hw : P.value D ≠ 0) : Nonempty (PrimitiveForm D) := by
  rw [P.definition D hD] at hw
  exact @primitiveForm_of_nonzero_class_weight D (P.labels D) (P.finite D)
    (P.automorphismCount D) (P.representatives D) hw

end PrimitiveClassData

structure ArithmeticSpectralData (k : ℕ) (Family V : ℕ → Type*)
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)] where
  eigenvalues : ∀ M, Family M → ℕ → ℂ
  normalized_one : ∀ N f, eigenvalues N f 1 = 1
  prime_power_recurrence : ∀ N f p, p.Prime → Nat.Coprime p N → ∀ j : ℕ,
    eigenvalues N f (p ^ (j + 2)) = eigenvalues N f p * eigenvalues N f (p ^ (j + 1)) -
      eigenvalues N f (p ^ j)
  operator : ∀ _m Q, V Q →ₗ[ℂ] V Q
  basis : ∀ Q, 0 < Q → Basis (OldformTrace.OldIndex Family Q) ℂ (V Q)
  eigenvector : ∀ m, 0 < m → ∀ Q (hQ : 0 < Q), Nat.Coprime m Q → ∀ i,
    operator m Q (basis Q hQ i) = OldformTrace.copyEigenvalue
      (fun M f => ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * eigenvalues M f m)) i •
        basis Q hQ i
  primitiveClasses : PrimitiveClassData
  hurwitzClass : ℤ → ℝ
  primitive_decomposition : ∀ D : ℤ, D < 0 →
    hurwitzClass D = ∑ u ∈ positiveSquareContents D, primitiveClasses.value (D / (u : ℤ) ^ 2)
  class_number_formula : ∀ D : ℤ, D < 0 → hurwitzClass D = 0 ∨
    Nonempty (ImprimitiveBoundary.AnalyticClassFormulaData hurwitzClass D)
  kernel : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ
  kernel_interpretation : PopaLocalInterpretation.GeneralPopaLocalFormula kernel
  full_trace_formula : ∀ m : ℕ, 0 < m → Odd m → ∀ Q : ℕ, 0 < Q → Nat.Coprime m Q →
    LinearMap.trace ℂ (V Q) (operator m Q) = PopaTrace.generalTraceExpression k Q m
      primitiveClasses.value kernel
        (selectedRepresentative primitiveClasses.value primitiveClasses.forms (m : ℤ))
  dimension_formula : MartinDimension.SatisfiesMartinFormula (k + 2)
    (fun M => (Fintype.card (Family M) : ℝ))

namespace ArithmeticSpectralData

variable {k : ℕ} {Family V : ℕ → Type*}
  [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]

/-- The primitive class function is exactly the supplied finite-class weight. -/
def primitiveClass (D : ArithmeticSpectralData k Family V) : ℤ → ℝ := D.primitiveClasses.value

theorem primitive_nonneg (D : ArithmeticSpectralData k Family V) :
    ∀ d : ℤ, d < 0 → 0 ≤ D.primitiveClass d := D.primitiveClasses.nonneg

theorem primitive_forms (D : ArithmeticSpectralData k Family V) :
    ∀ d : ℤ, d < 0 → D.primitiveClass d ≠ 0 → Nonempty (PrimitiveForm d) :=
  D.primitiveClasses.forms

/-- The usual analytic class-number identity implies the ordered-value
interface only after the internally proved boundary identification. -/
theorem ordered_class_number_formula (D : ArithmeticSpectralData k Family V) :
    ∀ d : ℤ, d < 0 → D.hurwitzClass d = 0 ∨
      Nonempty (ClassNumberGrowth.ClassFormulaData D.hurwitzClass d) := by
  intro d hd
  rcases D.class_number_formula d hd with hz | hdata
  · exact Or.inl hz
  · rcases hdata with ⟨data⟩
    exact Or.inr ⟨data.toClassFormulaData⟩

/-- The prime-square Hecke coefficient is derived from the general good-prime
recurrence, rather than added as a specialized explicit-formula premise. -/
theorem square_coefficient (D : ArithmeticSpectralData k Family V)
    (N : ℕ) (f : Family N) (p : ℕ) (hp : p.Prime) (hcop : Nat.Coprime p N) :
    tracePolynomial (D.eigenvalues N f p) 1 2 = D.eigenvalues N f (p ^ 2) := by
  have ht := D.prime_power_recurrence N f p hp hcop 0
  simpa only [Nat.zero_add, pow_zero, pow_one, D.normalized_one, tracePolynomial,
    one_mul] using ht.symm

/-- The canonical exact trace identity needed by the finite weighted sums,
now with all its internal dyadic hypotheses discharged. -/
theorem mean_trace (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (hmpos : 0 < m) (hm : Odd m) :
    heckeAverage (D.eigenvalues (2 ^ n)) m =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card (Family (2 ^ n)) : ℝ)) *
        (m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m : ℝ) : ℂ) +
      literalElliptic k n (Fintype.card (Family (2 ^ n)) : ℝ) (m : ℤ) D.primitiveClass
        (selectedRepresentative D.primitiveClass D.primitive_forms (m : ℤ)) +
      (normalizedCusp k n (Fintype.card (Family (2 ^ n)) : ℝ)
        (m : ℝ) m.divisorsAntidiagonal : ℂ) := by
  exact PopaTrace.heckeAverage_canonical_from_general_inputs Family V k n m hn hm hmpos
    D.eigenvalues (D.operator m) D.basis (D.eigenvector m hmpos) D.primitiveClass
    D.primitive_forms D.kernel D.kernel_interpretation (D.full_trace_formula m hmpos hm)

/-- The normalized prime Hecke sum from only the general cited arithmetic
identities and the actual finite support box. -/
theorem prime_sum (D : ArithmeticSpectralData k Family V) (n : ℕ) (hn : 8 ≤ n)
    {L s δ H : ℝ} (hL : 1 ≤ L) (hs : 0 ≤ s) (hδ : 0 < δ) (hH : 0 ≤ H)
    (h : ℝ → ℂ) (hh : ∀ x, ‖h x‖ ≤ H) :
    (2 / L) * weightedSum (primeBases L s) (-(1 / 2 : ℝ))
      (heckeAverage (D.eigenvalues (2 ^ n))) (fun p => h (Real.log p / L)) ≤
      (96 * s * uniformEllipticConstant δ * Real.sqrt 2 /
        (1 - (2 : ℝ) ^ (-1 - δ))) * H *
        ((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 + δ) +
      2 * (576 / ((k : ℝ) + 1)) * H * Real.log 4 * (1 + s) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  apply spectral_prime_sum_bound (D.eigenvalues (2 ^ n)) k n (by omega)
    hL hs hδ (uniformClassConstant_pos hδ).le hH
    (MartinDimension.polynomial_degree_dimension_lower k n hn _ D.dimension_formula)
    D.primitiveClass D.hurwitzClass D.primitive_nonneg D.primitive_decomposition
    (uniform_class_growth D.hurwitzClass D.ordered_class_number_formula hδ)
    (selectedRepresentative D.primitiveClass D.primitive_forms) h ?_ hh ?_
  · intro p hp t ht u hu hw
    have hp' := (Finset.mem_filter.mp hp).2
    have hpOdd : Odd (p : ℤ) := by exact_mod_cast hp'.1.odd_of_ne_two hp'.2
    exact selectedRepresentative_valid D.primitiveClass D.primitive_forms (p : ℤ) hpOdd
      t ht u hu hw
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    exact D.mean_trace n (by omega) p hp'.1.pos (hp'.1.odd_of_ne_two hp'.2)

/-- The prime-square analogue, using the actual four-root count and every
scalar and cusp term, with no internal trace-size premise. -/
theorem square_sum (D : ArithmeticSpectralData k Family V) (n : ℕ) (hn : 8 ≤ n)
    {L s δ H : ℝ} (hL : 1 ≤ L) (hs : 0 ≤ s) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hH : 0 ≤ H) (h : ℝ → ℂ) (hsupp : Function.support h ⊆ Set.Icc (-s) s)
    (hh : ∀ x, ‖h x‖ ≤ H) :
    (2 / L) * weightedSum (primeBases L s) (-1)
      (fun p => heckeAverage (D.eigenvalues (2 ^ n)) (p ^ 2))
      (fun p => h (2 * Real.log p / L)) ≤
      8 * H * Real.log 4 / L +
      squareConstant (uniformEllipticConstant δ) δ * H / L *
        (((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 / 2 + δ) +
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) * (Real.exp (s * L)) ^ δ) +
      2 * (576 / ((k : ℝ) + 1)) * H * Real.log 4 * (1 + s / 2) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  apply spectral_square_sum_bound (D.eigenvalues (2 ^ n)) k n (by omega)
    hL hs hδ hδhalf (uniformClassConstant_pos hδ).le hH
    (MartinDimension.polynomial_degree_dimension_lower k n hn _ D.dimension_formula)
    D.primitiveClass D.hurwitzClass D.primitive_nonneg D.primitive_decomposition
    (uniform_class_growth D.hurwitzClass D.ordered_class_number_formula hδ)
    (fun p => selectedRepresentative D.primitiveClass D.primitive_forms ((p : ℤ) ^ 2))
    h hsupp ?_ hh ?_
  · intro p hp t ht u hu hw
    have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hpOdd : Odd (p : ℤ) := by exact_mod_cast hp'.1.odd_of_ne_two hp'.2
    exact selectedRepresentative_valid D.primitiveClass D.primitive_forms ((p : ℤ) ^ 2)
      hpOdd.pow t ht u hu hw
  · intro p hp
    have hp' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have ht := D.mean_trace n (by omega) (p ^ 2) (pow_pos hp'.1.pos 2)
      (hp'.1.odd_of_ne_two hp'.2).pow
    simpa only [Nat.cast_pow] using ht

end ArithmeticSpectralData
end DepthAspect.UnsignedDensity
