import DepthAspect.PopaClassReindex
import DepthAspect.UniformTraceBounds
import DepthAspect.ImprimitiveBoundary

/-!
# Literal Popa coefficients and the actual local matrix model

The external input below is exactly the general projective-root
interpretation of B_Q cited by the paper from Popa (2.17)/Lemma 4.1.
It is formulated at arbitrary positive level coprime to the determinant.
All dyadic specializations, the Xi/K identification, and the discriminant
cutoff are conclusions of this module.
-/
namespace DepthAspect.PopaLiteralFunctions

open scoped BigOperators
open TraceBounds

/-- The cited general interpretation, now attached to the literal unit-residue
B rather than an opaque local-kernel parameter. -/
structure GeneralBProjectiveInterpretation : Prop where
  root_count : ∀ (Q : ℕ) (hQ : 0 < Q) (t m : ℤ),
    0 < m → t ^ 2 < 4 * m → Nat.Coprime m.natAbs Q →
    ∀ (u : ℕ), 0 < u → (u : ℤ) ^ 2 ∣ t ^ 2 - 4 * m →
    ∀ f : PrimitiveForm ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2),
      B Q hQ (Nat.gcd Q u) t m =
        (PopaLocalInterpretation.generalRootCount Q hQ (representativeDatum t u f).matrix : ℝ)

theorem GeneralBProjectiveInterpretation.dyadic (hB : GeneralBProjectiveInterpretation)
    (h : ℕ) (hh : 1 ≤ h) (t m : ℤ) (hm : 0 < m) (hmOdd : Odd m)
    (ht : t ^ 2 < 4 * m) (u : ℕ) (hu : 0 < u)
    (hdiv : (u : ℤ) ^ 2 ∣ t ^ 2 - 4 * m)
    (f : PrimitiveForm ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2)) :
    B (2 ^ h) (by positivity) (Nat.gcd (2 ^ h) u) t m =
      (DyadicFixedLines.fixedLineCount h (representativeDatum t u f).matrix : ℝ) := by
  have hdet := (representativeDatum_trace_det t m u hdiv f).2
  rw [hB.root_count (2 ^ h) (by positivity) t m hm ht
    ((Int.natAbs_odd.mpr hmOdd).coprime_two_right.pow_right h) u hu hdiv f,
    PopaLocalInterpretation.generalRootCount_two_pow h hh _ (by rwa [hdet])]

theorem Xi_eq_matrix_sum (hB : GeneralBProjectiveInterpretation)
    (h : ℕ) (hh : 1 ≤ h) (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (t m : ℤ) (hm : 0 < m) (hmOdd : Odd m) (ht : t ^ 2 < 4 * m) :
    Xi h H t m =
      ∑ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
        h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) *
          (DyadicFixedLines.fixedLineCount h (selectedRepresentative h₀ hforms m t u).matrix : ℝ) := by
  rw [Xi_eq_primitive h H h₀ hclasses t m (by omega)]
  unfold primitiveCoefficient
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hw : h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) = 0
  · rw [hw, zero_mul, zero_mul]
  · have hu' := (mem_positiveSquareContents _ (by omega) u).mp hu
    unfold selectedRepresentative
    rw [dif_pos ⟨ht, hu, hw⟩]
    congr 1
    exact hB.dyadic h hh t m hm hmOdd ht u hu'.1 hu'.2 _

theorem K_eq_literalContentTrace (hB : GeneralBProjectiveInterpretation)
    (n : ℕ) (hn : 3 ≤ n) (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (t m : ℤ) (hm : 0 < m) (hmOdd : Odd m) (ht : t ^ 2 < 4 * m) :
    K n H t m = literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
      (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * m) u (selectedRepresentative h₀ hforms m t u)) := by
  unfold K
  rw [Xi_eq_matrix_sum hB n (by omega) H h₀ hclasses hforms t m hm hmOdd ht,
    Xi_eq_matrix_sum hB (n - 1) (by omega) H h₀ hclasses hforms t m hm hmOdd ht,
    Xi_eq_matrix_sum hB (n - 2) (by omega) H h₀ hclasses hforms t m hm hmOdd ht,
    PopaTrace.sum_second_difference]
  unfold literalContentTrace
  apply Finset.sum_congr rfl
  intro u hu
  simp only [classWeightedDatum, matrixDifference]
  ring

/-- Corollary 3.2 for the literal Hurwitz/C_Q definition of K. -/
theorem literal_K_discriminant_support (hB : GeneralBProjectiveInterpretation)
    (n : ℕ) (hn : 3 ≤ n) (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (t m : ℤ) (hm : 0 < m) (hmOdd : Odd m) (ht : t ^ 2 < 4 * m)
    (hbad : ¬ (2 : ℤ) ^ (n - 2) ∣ t ^ 2 - 4 * m) :
    K n H t m = 0 := by
  rw [K_eq_literalContentTrace hB n hn H h₀ hclasses hforms t m hm hmOdd ht]
  apply Finset.sum_eq_zero
  intro u hu
  change h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) *
    matrixDifference n (selectedRepresentative h₀ hforms m t u).matrix = 0
  by_cases hw : h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) = 0
  · rw [hw, zero_mul]
  · have hf := selectedRepresentative_valid h₀ hforms m hmOdd t ht u hu hw
    rw [matrixDifference_zero n hn _ hf.oddDet (by rwa [hf.discriminant]), mul_zero]

/-- Equation (28) for the literal K, with the global growth estimate as a
reusable intermediate premise. The next theorem discharges that premise. -/
theorem literal_K_bound (hB : GeneralBProjectiveInterpretation)
    (n : ℕ) (hn : 3 ≤ n) (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hgrowth : ∀ D : ℤ, D < 0 → h₀ D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (t m : ℤ) (hm : 0 < m) (hmOdd : Odd m) (ht : t ^ 2 < 4 * m) :
    |K n H t m| ≤
      16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * |((t ^ 2 - 4 * m : ℤ) : ℝ)| ^ (1 / 2 + δ) *
        zetaMajorant δ / (1 - decayRatio δ) := by
  let D := t ^ 2 - 4 * m
  let F := fun u => classWeightedDatum h₀ D u (selectedRepresentative h₀ hforms m t u)
  let U := (positiveSquareContents D).filter (fun u => (F u).weight ≠ 0)
  have hD : D < 0 := by dsimp [D]; omega
  rw [K_eq_literalContentTrace hB n hn H h₀ hclasses hforms t m hm hmOdd ht]
  change |literalContentTrace n (positiveSquareContents D) F| ≤ _
  rw [literalContentTrace_filter]
  rw [literalContentTrace_eq n U
    (fun u hu => positiveSquareContents_positive D u (Finset.mem_filter.mp hu).1) F]
  apply contentTrace_bound n hn (encodedContents U) (fun p => F (contentValue p)) D hD Ccl δ hC hδ
  intro p hp
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hu, hw⟩ := Finset.mem_filter.mp hu
  have hu' := (mem_positiveSquareContents D hD.ne u).mp hu
  rw [contentValue_contentIndex u hu'.1]
  apply isContentDatum_contentIndex u hu'.1 D Ccl δ (F u)
  apply isLiteralContentDatum_classWeighted h₀ Ccl δ h₀nonneg hgrowth D hD u hu'.1 hu'.2
  exact selectedRepresentative_valid h₀ hforms m hmOdd t ht u hu hw

/-- The literal K bound from the genuine general class identities, with no
class-number size premise and no local-root estimate supplied by the caller. -/
theorem literal_K_uniform_bound (hB : GeneralBProjectiveInterpretation)
    (n : ℕ) (hn : 3 ≤ n) (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨
      Nonempty (ImprimitiveBoundary.AnalyticClassFormulaData H D))
    (δ : ℝ) (hδ : 0 < δ) (t m : ℤ) (hm : 0 < m) (hmOdd : Odd m)
    (ht : t ^ 2 < 4 * m) :
    |K n H t m| ≤
      16 * uniformClassConstant δ * (2 : ℝ) ^ ((n : ℝ) / 2) *
        |((t ^ 2 - 4 * m : ℤ) : ℝ)| ^ (1 / 2 + δ) *
        zetaMajorant δ / (1 - decayRatio δ) := by
  have hordered : ∀ D : ℤ, D < 0 → H D = 0 ∨
      Nonempty (ClassNumberGrowth.ClassFormulaData H D) := by
    intro D hD
    rcases hformula D hD with hz | hdata
    · exact Or.inl hz
    · rcases hdata with ⟨data⟩
      exact Or.inr ⟨data.toClassFormulaData⟩
  have hgrowth := uniform_class_growth H hordered hδ
  apply literal_K_bound hB n hn H h₀ hclasses hforms h₀nonneg (uniformClassConstant δ) δ
    (uniformClassConstant_pos hδ).le hδ
    (primitive_class_number_growth h₀ H (uniformClassConstant δ) δ h₀nonneg hclasses hgrowth)
    t m hm hmOdd ht

end DepthAspect.PopaLiteralFunctions
