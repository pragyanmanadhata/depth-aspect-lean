import DepthAspect.PopaLiteralBridge
import DepthAspect.UniformSpectralPrimeBounds

/-!
# Proposition 2.4 with the literal Hurwitz coefficient

The general trace and oldform inputs are those of `ArithmeticSpectralData`.
The additional named input is the cited general interpretation of the
literal B function. The finite Hurwitz/Möbius reindexing and every dyadic
specialization are already proved, and are applied here to the same
finite newform family and its actual eigenvalue sum.
-/
namespace DepthAspect.PopaLiteralFunctions

open scoped BigOperators
open TraceBounds

/-- Equation (14), with polynomial degree k and modular weight k+2. -/
noncomputable def literalNewTraceExpression (k n m : ℕ) (H : ℤ → ℝ) : ℂ :=
  ((((k : ℝ) + 1) * (2 : ℝ) ^ n / 32 * (m : ℝ) ^ ((k : ℝ) / 2) *
      PopaTrace.squareIndicator m : ℝ) : ℂ) -
    (∑ t ∈ ellipticTraces (m : ℤ),
      tracePolynomial (t : ℂ) (m : ℂ) k * (K n H t (m : ℤ) : ℂ)) / 2 -
    (((∑ p ∈ m.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) *
      cuspDifference n p.1 p.2) / 2 : ℝ) : ℂ)

theorem newTraceExpression_eq_literal (hB : GeneralBProjectiveInterpretation)
    (k n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hodd : Odd m)
    (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D)) :
    PopaTrace.newTraceExpression k n m h₀
        (selectedRepresentative h₀ hforms (m : ℤ)) =
      literalNewTraceExpression k n m H := by
  have hsum : (∑ t ∈ ellipticTraces (m : ℤ),
      tracePolynomial (t : ℂ) (m : ℂ) k *
        (literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * (m : ℤ)))
          (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * (m : ℤ)) u
            (selectedRepresentative h₀ hforms (m : ℤ) t u)) : ℂ)) =
      ∑ t ∈ ellipticTraces (m : ℤ),
        tracePolynomial (t : ℂ) (m : ℂ) k * (K n H t (m : ℤ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [K_eq_literalContentTrace hB n hn H h₀ hclasses hforms t (m : ℤ)
      (by exact_mod_cast hm) (by exact_mod_cast hodd)
      ((mem_ellipticTraces (m : ℤ) t).mp ht)]
  unfold PopaTrace.newTraceExpression literalNewTraceExpression
  rw [hsum]

theorem literalElliptic_eq_normalized_K (hB : GeneralBProjectiveInterpretation)
    (k n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hodd : Odd m) (d : ℝ)
    (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D)) :
    literalElliptic k n d (m : ℤ) h₀
        (selectedRepresentative h₀ hforms (m : ℤ)) =
      normalizedElliptic k d (m : ℝ) (ellipticTraces (m : ℤ))
        (fun t => K n H t (m : ℤ)) := by
  unfold literalElliptic normalizedElliptic
  simp only [Int.cast_natCast]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  rw [K_eq_literalContentTrace hB n hn H h₀ hclasses hforms t (m : ℤ)
    (by exact_mod_cast hm) (by exact_mod_cast hodd)
    ((mem_ellipticTraces (m : ℤ) t).mp ht)]

end DepthAspect.PopaLiteralFunctions

namespace DepthAspect.UnsignedDensity.ArithmeticSpectralData

open scoped BigOperators
open TraceBounds PopaLiteralFunctions SpectralFamily

variable {k : ℕ} {Family V : ℕ → Type*}
  [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]

/-- Proposition 2.4 for the actual newspace eigenvalue sum, in literal K notation. -/
theorem newform_sum_literal (D : ArithmeticSpectralData k Family V)
    (hB : GeneralBProjectiveInterpretation)
    (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (hm : 0 < m) (hodd : Odd m) :
    (∑ f : Family (2 ^ n),
      ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * D.eigenvalues (2 ^ n) f m)) =
      literalNewTraceExpression k n m D.hurwitzClass := by
  rw [← newTraceExpression_eq_literal hB k n m hn hm hodd D.hurwitzClass
    D.primitiveClass D.primitive_decomposition D.primitive_forms]
  apply PopaTrace.newform_sum_from_general_trace Family V k n m hn hodd
    (fun M f => ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * D.eigenvalues M f m))
    (D.operator m) D.basis (D.eigenvector m hm) D.primitiveClass D.kernel
    (selectedRepresentative D.primitiveClass D.primitive_forms (m : ℤ))
    (D.full_trace_formula m hm hodd)
  intro h hh t ht u hu hw
  exact PopaTrace.selectedRepresentative_local_interpretation
    D.primitiveClass D.primitive_forms D.kernel D.kernel_interpretation
    (m : ℤ) (by exact_mod_cast hm) (by exact_mod_cast hodd) h hh t ht u hu hw

/-- The normalized literal version of the same identity, equation (16). -/
theorem mean_trace_literal (D : ArithmeticSpectralData k Family V)
    (hB : GeneralBProjectiveInterpretation)
    (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (hm : 0 < m) (hodd : Odd m) :
    heckeAverage (D.eigenvalues (2 ^ n)) m =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card (Family (2 ^ n)) : ℝ)) *
        (m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m : ℝ) : ℂ) +
      normalizedElliptic k (Fintype.card (Family (2 ^ n)) : ℝ) (m : ℝ)
        (ellipticTraces (m : ℤ)) (fun t => K n D.hurwitzClass t (m : ℤ)) +
      (normalizedCusp k n (Fintype.card (Family (2 ^ n)) : ℝ)
        (m : ℝ) m.divisorsAntidiagonal : ℂ) := by
  rw [D.mean_trace n hn m hm hodd,
    literalElliptic_eq_normalized_K hB k n m hn hm hodd _ D.hurwitzClass
      D.primitiveClass D.primitive_decomposition D.primitive_forms]

end DepthAspect.UnsignedDensity.ArithmeticSpectralData
