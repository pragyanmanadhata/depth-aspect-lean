import DepthAspect.TraceBounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

/-!
# Exact reindexing of the primitive class-number sum

The original positive-content index `u` in (9) is encoded by its dyadic
valuation and positive odd part minus one. This file proves the finite-sum
identity and applies the checked bounds to the literal square-divisor sum.
-/
namespace DepthAspect.TraceBounds
open scoped BigOperators

/-- Decode the dyadic exponent and positive odd-part index. -/
def contentValue (p : ℕ × ℕ) : ℕ := 2 ^ p.1 * (p.2 + 1)

/-- The canonical valuation and odd-part coordinates of a positive content. -/
noncomputable def contentIndex (u : ℕ) : ℕ × ℕ :=
  (u.factorization 2, u / 2 ^ (u.factorization 2) - 1)

theorem contentValue_contentIndex (u : ℕ) (hu : 0 < u) :
    contentValue (contentIndex u) = u := by
  have hv := Nat.ordCompl_pos 2 hu.ne'
  unfold contentValue contentIndex
  dsimp
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hv)]
  exact Nat.ordProj_mul_ordCompl_eq_self u 2

theorem contentIndex_oddPart (u : ℕ) (hu : 0 < u) :
    Odd ((contentIndex u).2 + 1) := by
  have hv := Nat.ordCompl_pos 2 hu.ne'
  unfold contentIndex
  dsimp
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hv)]
  apply Nat.not_even_iff_odd.mp
  intro he
  exact Nat.not_dvd_ordCompl Nat.prime_two hu.ne' he.two_dvd

theorem contentIndex_injective_on_positive (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (heq : contentIndex u = contentIndex v) : u = v := by
  calc
    u = contentValue (contentIndex u) := (contentValue_contentIndex u hu).symm
    _ = contentValue (contentIndex v) := congrArg contentValue heq
    _ = v := contentValue_contentIndex v hv

noncomputable def encodedContents (U : Finset ℕ) : Finset (ℕ × ℕ) := U.image contentIndex

/-- Exact finite reindexing, with no estimate or lost multiplicity. -/
theorem content_reindex_sum {α : Type*} [AddCommMonoid α] (U : Finset ℕ)
    (hU : ∀ u ∈ U, 0 < u) (f : ℕ → α) :
    (∑ u ∈ U, f u) = ∑ p ∈ encodedContents U, f (contentValue p) := by
  unfold encodedContents
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [contentValue_contentIndex u (hU u hu)]
  · intro u hu v hv heq
    exact contentIndex_injective_on_positive u v (hU u hu) (hU v hv) heq

/-- Every positive integer whose square divides the integer discriminant. -/
noncomputable def positiveSquareContents (D : ℤ) : Finset ℕ :=
  D.natAbs.divisors.filter (fun u => u ^ 2 ∣ D.natAbs)

theorem positiveSquareContents_positive (D : ℤ) (u : ℕ)
    (hu : u ∈ positiveSquareContents D) : 0 < u :=
  Nat.pos_of_mem_divisors (Finset.mem_filter.mp hu).1

theorem mem_positiveSquareContents (D : ℤ) (hD : D ≠ 0) (u : ℕ) :
    u ∈ positiveSquareContents D ↔ 0 < u ∧ (u : ℤ) ^ 2 ∣ D := by
  have hDnat : D.natAbs ≠ 0 := by simpa using hD
  have hcast : (u : ℤ) ^ 2 ∣ D ↔ u ^ 2 ∣ D.natAbs := by
    have hpow : ((u ^ 2 : ℕ) : ℤ) = (u : ℤ) ^ 2 := by norm_cast
    rw [← hpow]
    exact Int.natCast_dvd
  rw [hcast]
  constructor
  · intro hu
    exact ⟨positiveSquareContents_positive D u hu, (Finset.mem_filter.mp hu).2⟩
  · rintro ⟨hu, hsq⟩
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨?_, hDnat⟩, hsq⟩
    exact (dvd_pow_self u (by decide : 2 ≠ 0)).trans hsq

/-- A negative discriminant divided by an actual positive square divisor
is again negative. -/
theorem negative_discriminant_quotient (D : ℤ) (hD : D < 0) (u : ℕ)
    (hu : 0 < u) (hdiv : (u : ℤ) ^ 2 ∣ D) : D / (u : ℤ) ^ 2 < 0 := by
  have huZ : (0 : ℤ) < (u : ℤ) ^ 2 := by positivity
  by_contra h
  have hnonneg : 0 ≤ D := by
    rw [← Int.ediv_mul_cancel hdiv]
    exact mul_nonneg (le_of_not_gt h) huZ.le
  exact (not_le_of_gt hD) hnonneg

/-- The global negative-discriminant growth bound specializes to the exact
integer quotient appearing in (9). Divisibility discharges the cast through
integer division; no independent scaled growth estimate is assumed. -/
theorem class_number_growth_scaled (H : ℤ → ℝ) (Ccl δ : ℝ)
    (hH : ∀ d : ℤ, d < 0 → H d ≤ Ccl * |(d : ℝ)| ^ (1 / 2 + δ))
    (D : ℤ) (hD : D < 0) (u : ℕ) (hu : 0 < u) (hdiv : (u : ℤ) ^ 2 ∣ D) :
    H (D / (u : ℤ) ^ 2) ≤ Ccl * (|(D : ℝ)| / (u : ℝ) ^ 2) ^ (1 / 2 + δ) := by
  have hquot := negative_discriminant_quotient D hD u hu hdiv
  have hden : (((u : ℤ) ^ 2 : ℤ) : ℝ) ≠ 0 := by
    push_cast
    positivity
  have hcast : ((D / (u : ℤ) ^ 2 : ℤ) : ℝ) = (D : ℝ) / (u : ℝ) ^ 2 := by
    rw [Int.cast_div hdiv hden]
    push_cast
    rfl
  have hb := hH (D / (u : ℤ) ^ 2) hquot
  rw [hcast, abs_div, abs_of_nonneg (sq_nonneg (u : ℝ))] at hb
  exact hb

/-- Primitive-content data indexed by the original integer `u`, as in (9).
The growth field is the internal Lemma 2.2 obligation; the other fields record
the actual representative and its primitive associated form. -/
structure IsLiteralContentDatum (u : ℕ) (D : ℤ) (Ccl δ : ℝ) (F : ContentDatum) : Prop where
  oddDet : Odd (Matrix.det F.matrix)
  primitive : Odd F.A ∨ Odd F.B ∨ Odd F.C
  coeffA : F.matrix 1 0 = (u : ℤ) * F.A
  coeffB : F.matrix 1 1 - F.matrix 0 0 = (u : ℤ) * F.B
  coeffC : -F.matrix 0 1 = (u : ℤ) * F.C
  discriminant : (Matrix.trace F.matrix) ^ 2 - 4 * Matrix.det F.matrix = D
  weight_nonneg : 0 ≤ F.weight
  class_number_growth : F.weight ≤ Ccl * (|(D : ℝ)| / (u : ℝ) ^ 2) ^ (1 / 2 + δ)

/-- The original primitive representative supplies the checked dyadic datum. -/
theorem isContentDatum_contentIndex (u : ℕ) (hu : 0 < u) (D : ℤ) (Ccl δ : ℝ)
    (F : ContentDatum) (hF : IsLiteralContentDatum u D Ccl δ F) :
    IsContentDatum (contentIndex u) D Ccl δ F := by
  have huNat : u = 2 ^ (contentIndex u).1 * ((contentIndex u).2 + 1) :=
    (contentValue_contentIndex u hu).symm
  have huZ : (u : ℤ) = (2 : ℤ) ^ (contentIndex u).1 * (((contentIndex u).2 : ℤ) + 1) := by
    exact_mod_cast huNat
  have huR : (u : ℝ) = (2 : ℝ) ^ (contentIndex u).1 * (((contentIndex u).2 : ℝ) + 1) := by
    exact_mod_cast huNat
  refine ⟨hF.oddDet, ?_, hF.primitive, ?_, ?_, ?_, hF.discriminant,
    hF.weight_nonneg, ?_⟩
  · exact_mod_cast contentIndex_oddPart u hu
  · rw [hF.coeffA, huZ]; ring
  · rw [hF.coeffB, huZ]; ring
  · rw [hF.coeffC, huZ]; ring
  · simpa only [huR] using hF.class_number_growth

/-- The original finite weighted sum over positive contents. -/
noncomputable def literalContentTrace (n : ℕ) (U : Finset ℕ) (F : ℕ → ContentDatum) : ℝ :=
  ∑ u ∈ U, (F u).weight * matrixDifference n (F u).matrix

/-- Zero class weights can be retained in the literal sum without asking for
an associated primitive representative at those indices. -/
theorem literalContentTrace_filter (n : ℕ) (U : Finset ℕ) (F : ℕ → ContentDatum) :
    literalContentTrace n U F =
      literalContentTrace n (U.filter (fun u => (F u).weight ≠ 0)) F := by
  unfold literalContentTrace
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : (F u).weight = 0 <;> simp [h]

/-- The literal class-number sum equals its distinct dyadic-coordinate model. -/
theorem literalContentTrace_eq (n : ℕ) (U : Finset ℕ) (hU : ∀ u ∈ U, 0 < u)
    (F : ℕ → ContentDatum) :
    literalContentTrace n U F = contentTrace n (encodedContents U) (fun p => F (contentValue p)) := by
  exact content_reindex_sum U hU (fun u => (F u).weight * matrixDifference n (F u).matrix)

/-- Equation (35) for the literal `u² | D` class-number sum from (9).
There is no reindexing premise and no assumed root-count or trace estimate. -/
theorem normalizedElliptic_literal_bound (k n : ℕ) (hn : 4 ≤ n) (m : ℤ)
    (hm : 0 < m) (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (T : Finset ℤ) (F : ℤ → ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * m)
    (hF : ∀ t ∈ T, ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
      (F t u).weight ≠ 0 → IsLiteralContentDatum u (t ^ 2 - 4 * m) Ccl δ (F t u)) :
    ‖normalizedElliptic k d (m : ℝ) T
      (fun t => literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m)) (F t))‖ ≤
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) := by
  let U := fun t => (positiveSquareContents (t ^ 2 - 4 * m)).filter
    (fun u => (F t u).weight ≠ 0)
  have heq : (fun t => literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m)) (F t)) =
      fun t => contentTrace n (encodedContents (U t)) (fun p => F t (contentValue p)) := by
    funext t
    rw [literalContentTrace_filter]
    exact literalContentTrace_eq n (U t)
      (fun u hu => positiveSquareContents_positive _ u (Finset.mem_filter.mp hu).1) (F t)
  rw [heq]
  apply normalizedElliptic_bound_surviving k n hn m hm d Ccl δ hC hδ hd T
    (fun t => encodedContents (U t)) (fun t p => F t (contentValue p)) hT
  intro t ht p hp
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hu, hweight⟩ := Finset.mem_filter.mp hu
  have hupos := positiveSquareContents_positive (t ^ 2 - 4 * m) u hu
  rw [contentValue_contentIndex u hupos]
  exact isContentDatum_contentIndex u hupos (t ^ 2 - 4 * m) Ccl δ (F t u)
    (hF t ht u hu hweight)

/-- Arithmetic data of the primitive representative, without a weight or a
size-estimate field. -/
structure IsPrimitiveContentMatrix (u : ℕ) (D : ℤ) (F : ContentDatum) : Prop where
  oddDet : Odd (Matrix.det F.matrix)
  primitive : Odd F.A ∨ Odd F.B ∨ Odd F.C
  coeffA : F.matrix 1 0 = (u : ℤ) * F.A
  coeffB : F.matrix 1 1 - F.matrix 0 0 = (u : ℤ) * F.B
  coeffC : -F.matrix 0 1 = (u : ℤ) * F.C
  discriminant : (Matrix.trace F.matrix) ^ 2 - 4 * Matrix.det F.matrix = D

/-- Insert the literal class-number weight h₀(D/u²). -/
noncomputable def classWeightedDatum (H : ℤ → ℝ) (D : ℤ) (u : ℕ) (F : ContentDatum) :
    ContentDatum := { F with weight := H (D / (u : ℤ) ^ 2) }

theorem isLiteralContentDatum_classWeighted (H : ℤ → ℝ) (Ccl δ : ℝ)
    (hH0 : ∀ d : ℤ, d < 0 → 0 ≤ H d)
    (hHgrowth : ∀ d : ℤ, d < 0 → H d ≤ Ccl * |(d : ℝ)| ^ (1 / 2 + δ))
    (D : ℤ) (hD : D < 0) (u : ℕ) (hu : 0 < u) (hdiv : (u : ℤ) ^ 2 ∣ D)
    (F : ContentDatum) (hF : IsPrimitiveContentMatrix u D F) :
    IsLiteralContentDatum u D Ccl δ (classWeightedDatum H D u F) := by
  exact ⟨hF.oddDet, hF.primitive, hF.coeffA, hF.coeffB, hF.coeffC,
    hF.discriminant, hH0 _ (negative_discriminant_quotient D hD u hu hdiv),
    class_number_growth_scaled H Ccl δ hHgrowth D hD u hu hdiv⟩

/-- Equation (35) for the literal class-number weighted sum in (9), assuming
only the global class-number bound to be proved in Lemma 2.2. Primitive matrix
data are required only when the class weight is nonzero, so invalid quotient
discriminants with zero class number impose no representative obligation.
The data contain no local growth estimates, cancellation conclusions, or trace bounds. -/
theorem normalizedElliptic_class_number_bound (k n : ℕ) (hn : 4 ≤ n) (m : ℤ)
    (hm : 0 < m) (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (H : ℤ → ℝ) (hH0 : ∀ D : ℤ, D < 0 → 0 ≤ H D)
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (T : Finset ℤ) (F : ℤ → ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * m)
    (hF : ∀ t ∈ T, ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
      H ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 →
      IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (F t u)) :
    ‖normalizedElliptic k d (m : ℝ) T
      (fun t => literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
        (fun u => classWeightedDatum H (t ^ 2 - 4 * m) u (F t u)))‖ ≤
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) := by
  apply normalizedElliptic_literal_bound k n hn m hm d Ccl δ hC hδ hd T
    (fun t u => classWeightedDatum H (t ^ 2 - 4 * m) u (F t u)) hT
  intro t ht u hu hweight
  have hD : t ^ 2 - 4 * m < 0 := by linarith [hT t ht]
  have hu' := (mem_positiveSquareContents (t ^ 2 - 4 * m) (ne_of_lt hD) u).mp hu
  exact isLiteralContentDatum_classWeighted H Ccl δ hH0 hHgrowth
    (t ^ 2 - 4 * m) hD u hu'.1 hu'.2 (F t u) (hF t ht u hu hweight)

end DepthAspect.TraceBounds
