import DepthAspect.SectionSevenSupport
import DepthAspect.PrimitiveRepresentatives

/-!
# The literal trace-pair symmetry used in the final support discussion

The canonical primitive representative at t and at −t uses the same
positive form. Its three quadratic coefficients, and therefore its actual
fixed-line count, agree. This connects the polynomial parity statement to
the actual finite trace model, rather than postulating an even trace kernel.
-/
namespace DepthAspect.SectionSevenSupport

open TraceBounds DyadicFixedLines
open scoped BigOperators

/-- The fixed-line count depends only on the three coefficients of the
matrix quadratic form, once the determinant is odd. -/
theorem matrixDifference_eq_of_coefficients (n : ℕ) (hn : 3 ≤ n)
    (M T : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : Odd (Matrix.det M)) (hT : Odd (Matrix.det T))
    (hA : M 1 0 = T 1 0)
    (hB : M 1 1 - M 0 0 = T 1 1 - T 0 0)
    (hC : -M 0 1 = -T 0 1) : matrixDifference n M = matrixDifference n T := by
  unfold matrixDifference
  rw [fixedLineCount_eq_rho n (by omega) M hM,
    fixedLineCount_eq_rho (n - 1) (by omega) M hM,
    fixedLineCount_eq_rho (n - 2) (by omega) M hM,
    fixedLineCount_eq_rho n (by omega) T hT,
    fixedLineCount_eq_rho (n - 1) (by omega) T hT,
    fixedLineCount_eq_rho (n - 2) (by omega) T hT, hA, hB, hC]

/-- Equal discriminant indices give the same canonical choice. The
negativity and nonzero-weight witnesses are propositions, so their proof
terms do not affect the chosen form. -/
private theorem chosenPrimitiveForm_coefficients_congr (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    {D E : ℤ} (hDE : D = E) (hD : D < 0) (hwD : h₀ D ≠ 0)
    (hE : E < 0) (hwE : h₀ E ≠ 0) :
    (Classical.choice (hforms D hD hwD)).A =
        (Classical.choice (hforms E hE hwE)).A ∧
    (Classical.choice (hforms D hD hwD)).B =
        (Classical.choice (hforms E hE hwE)).B ∧
    (Classical.choice (hforms D hD hwD)).C =
        (Classical.choice (hforms E hE hwE)).C := by
  subst E
  exact ⟨rfl, rfl, rfl⟩

/-- Selecting the same discriminant uses precisely the same form, even
though the integral matrix's diagonal entries change with the trace. -/
theorem selectedRepresentative_neg_coefficients (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m t : ℤ) (u : ℕ) :
    (selectedRepresentative h₀ hforms m (-t) u).A =
        (selectedRepresentative h₀ hforms m t u).A ∧
    (selectedRepresentative h₀ hforms m (-t) u).B =
        (selectedRepresentative h₀ hforms m t u).B ∧
    (selectedRepresentative h₀ hforms m (-t) u).C =
        (selectedRepresentative h₀ hforms m t u).C := by
  by_cases h : t ^ 2 < 4 * m ∧ u ∈ positiveSquareContents (t ^ 2 - 4 * m) ∧
      h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0
  · have hneg : (-t) ^ 2 < 4 * m ∧
        u ∈ positiveSquareContents ((-t) ^ 2 - 4 * m) ∧
        h₀ (((-t) ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 := by
      simpa only [neg_sq] using h
    have hD : t ^ 2 - 4 * m < 0 := by omega
    have hu := (mem_positiveSquareContents _ hD.ne u).mp h.2.1
    have hquot := negative_discriminant_quotient _ hD u hu.1 hu.2
    have hquotneg : ((-t) ^ 2 - 4 * m) / (u : ℤ) ^ 2 < 0 := by
      simpa only [neg_sq] using hquot
    simp only [selectedRepresentative, dif_pos h, dif_pos hneg]
    exact chosenPrimitiveForm_coefficients_congr h₀ hforms
      (D := ((-t) ^ 2 - 4 * m) / (u : ℤ) ^ 2)
      (E := (t ^ 2 - 4 * m) / (u : ℤ) ^ 2)
      (by rw [neg_sq]) hquotneg hneg.2.2 hquot h.2.2
  · have hneg : ¬ ((-t) ^ 2 < 4 * m ∧
        u ∈ positiveSquareContents ((-t) ^ 2 - 4 * m) ∧
        h₀ (((-t) ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0) := by
      simpa only [neg_sq] using h
    simp [selectedRepresentative, h, hneg]

/-- The actual matrix kernel at an active content is unchanged by negating
the strict-elliptic trace index. -/
theorem selectedRepresentative_matrixDifference_neg (n : ℕ) (hn : 3 ≤ n)
    (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m : ℤ) (hm : Odd m) (t : ℤ) (ht : t ^ 2 < 4 * m) (u : ℕ)
    (hu : u ∈ positiveSquareContents (t ^ 2 - 4 * m))
    (hw : h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0) :
    matrixDifference n (selectedRepresentative h₀ hforms m (-t) u).matrix =
      matrixDifference n (selectedRepresentative h₀ hforms m t u).matrix := by
  have hp := selectedRepresentative_valid h₀ hforms m hm t ht u hu hw
  have hm' := selectedRepresentative_valid h₀ hforms m hm (-t)
    (by simpa only [neg_sq] using ht) u
    (by simpa only [neg_sq] using hu) (by simpa only [neg_sq] using hw)
  obtain ⟨hA, hB, hC⟩ := selectedRepresentative_neg_coefficients h₀ hforms m t u
  apply matrixDifference_eq_of_coefficients n hn _ _ hm'.oddDet hp.oddDet
  · rw [hm'.coeffA, hp.coeffA, hA]
  · rw [hm'.coeffB, hp.coeffB, hB]
  · rw [hm'.coeffC, hp.coeffC, hC]

/-- Every positive square content is retained in this actual class-number
sum; zero-weight slots need no representative assumptions. -/
noncomputable def canonicalContentTrace (n : ℕ) (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m t : ℤ) : ℝ :=
  literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
    (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * m) u
      (selectedRepresentative h₀ hforms m t u))

theorem canonicalContentTrace_neg (n : ℕ) (hn : 3 ≤ n) (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m : ℤ) (hm : Odd m) (t : ℤ) (ht : t ^ 2 < 4 * m) :
    canonicalContentTrace n h₀ hforms m (-t) = canonicalContentTrace n h₀ hforms m t := by
  unfold canonicalContentTrace literalContentTrace
  simp only [neg_sq]
  apply Finset.sum_congr rfl
  intro u hu
  dsimp only [classWeightedDatum]
  by_cases hw : h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) = 0
  · simp only [hw, zero_mul]
  · rw [selectedRepresentative_matrixDifference_neg n hn h₀ hforms m hm t ht u hu hw]

/-- The exact unnormalized summand from the actual canonical elliptic trace. -/
noncomputable def canonicalEllipticSummand (k n : ℕ) (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m t : ℤ) : ℂ :=
  tracePolynomial (t : ℂ) (m : ℂ) k * (canonicalContentTrace n h₀ hforms m t : ℂ)

/-- At even weight the two literal trace-index summands agree. In
particular there is no cancellation between the two opposite indices
in the weight-two case discussed after equation (140). -/
theorem canonicalEllipticSummand_neg (k n : ℕ) (hk : Even k) (hn : 3 ≤ n)
    (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m : ℤ) (hm : Odd m) (t : ℤ) (ht : t ^ 2 < 4 * m) :
    canonicalEllipticSummand k n h₀ hforms m (-t) =
      canonicalEllipticSummand k n h₀ hforms m t := by
  unfold canonicalEllipticSummand
  rw [Int.cast_neg, tracePolynomial_neg_even _ _ k hk,
    canonicalContentTrace_neg n hn h₀ hforms m hm t ht]

end DepthAspect.SectionSevenSupport
