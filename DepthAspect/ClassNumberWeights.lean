import DepthAspect.ContentReindex

/-!
# Primitive class weights and Hurwitz class numbers

The cited identity expressing a Hurwitz class number as a sum of primitive
class weights is an external arithmetic input. Its nonnegativity and the
comparison of the primitive weight with the whole sum are proved here using
the literal square-divisor index set and its actual u=1 term.
-/
namespace DepthAspect.TraceBounds
open scoped BigOperators

/-- Every integer trace satisfying the strict elliptic inequality. -/
noncomputable def ellipticTraces (m : ℤ) : Finset ℤ :=
  (SurvivingTraces.squareInterval (4 * m)).filter (fun t => t ^ 2 < 4 * m)

@[simp] theorem mem_ellipticTraces (m t : ℤ) :
    t ∈ ellipticTraces m ↔ t ^ 2 < 4 * m := by
  constructor
  · exact fun ht => (Finset.mem_filter.mp ht).2
  · exact fun ht => Finset.mem_filter.mpr
      ⟨SurvivingTraces.mem_squareInterval_of_square_lt ht, ht⟩

/-- The surviving index set is exactly the congruence filter of the complete
strict-elliptic set. -/
theorem survivingTraces_eq_elliptic_filter (q m : ℤ) :
    SurvivingTraces.survivingTraces q m =
      (ellipticTraces m).filter (fun t => 4 * q ∣ 4 * m - t ^ 2) := by
  ext t
  simp only [SurvivingTraces.mem_survivingTraces, Finset.mem_filter, mem_ellipticTraces]

theorem one_mem_positiveSquareContents (D : ℤ) (hD : D ≠ 0) :
    1 ∈ positiveSquareContents D := by
  apply (mem_positiveSquareContents D hD 1).mpr
  simp

/-- Nonnegative primitive weights imply the Hurwitz class number is nonnegative. -/
theorem hurwitz_nonneg (h₀ H : ℤ → ℝ)
    (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (D : ℤ) (hD : D < 0) : 0 ≤ H D := by
  rw [hidentity D hD]
  apply Finset.sum_nonneg
  intro u hu
  obtain ⟨hupos, hudiv⟩ := (mem_positiveSquareContents D hD.ne u).mp hu
  exact h₀nonneg _ (negative_discriminant_quotient D hD u hupos hudiv)

/-- The u=1 term proves the primitive-to-Hurwitz comparison in (5). -/
theorem primitive_le_hurwitz (h₀ H : ℤ → ℝ)
    (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (D : ℤ) (hD : D < 0) : h₀ D ≤ H D := by
  rw [hidentity D hD]
  have hs := Finset.single_le_sum (f := fun u : ℕ => h₀ (D / (u : ℤ) ^ 2))
    (fun u hu => by
      obtain ⟨hupos, hudiv⟩ := (mem_positiveSquareContents D hD.ne u).mp hu
      exact h₀nonneg _ (negative_discriminant_quotient D hD u hupos hudiv))
    (one_mem_positiveSquareContents D hD.ne)
  simpa using hs

/-- A proved bound for Hurwitz class numbers automatically bounds the primitive
weights. The primitive upper bound is not an additional input. -/
theorem primitive_class_number_growth (h₀ H : ℤ → ℝ) (Ccl δ : ℝ)
    (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ)) :
    ∀ D : ℤ, D < 0 → h₀ D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ) := by
  intro D hD
  exact (primitive_le_hurwitz h₀ H h₀nonneg hidentity D hD).trans (hHgrowth D hD)

/-- The literal primitive-weight elliptic sum satisfies (35), using only a
Hurwitz growth theorem and the cited primitive decomposition identity. -/
theorem normalizedElliptic_hurwitz_bound (k n : ℕ) (hn : 4 ≤ n) (m : ℤ)
    (hm : 0 < m) (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (h₀ H : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (T : Finset ℤ) (F : ℤ → ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * m)
    (hF : ∀ t ∈ T, ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
      h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 →
      IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (F t u)) :
    ‖normalizedElliptic k d (m : ℝ) T
      (fun t => literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
        (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * m) u (F t u)))‖ ≤
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) :=
  normalizedElliptic_class_number_bound k n hn m hm d Ccl δ hC hδ hd h₀ h₀nonneg
    (primitive_class_number_growth h₀ H Ccl δ h₀nonneg hidentity hHgrowth) T F hT hF

/-- The complete literal normalized elliptic expression in equation (9), with
all integer traces t²<4m and all positive square divisors of their discriminant. -/
noncomputable def literalElliptic (k n : ℕ) (d : ℝ) (m : ℤ) (h₀ : ℤ → ℝ)
    (F : ℤ → ℕ → ContentDatum) : ℂ :=
  normalizedElliptic k d (m : ℝ) (ellipticTraces m)
    (fun t => literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
      (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * m) u (F t u)))

/-- Canonical (35): the complete literal elliptic expression is bounded, with
no selected trace-index subset and no assumed primitive class-number bound. -/
theorem literalElliptic_bound (k n : ℕ) (hn : 4 ≤ n) (m : ℤ)
    (hm : 0 < m) (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (h₀ H : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (F : ℤ → ℕ → ContentDatum)
    (hF : ∀ t : ℤ, t ^ 2 < 4 * m → ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
      h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 →
      IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (F t u)) :
    ‖literalElliptic k n d m h₀ F‖ ≤
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) := by
  exact normalizedElliptic_hurwitz_bound k n hn m hm d Ccl δ hC hδ hd
    h₀ H h₀nonneg hidentity hHgrowth (ellipticTraces m) F
    (fun t ht => (mem_ellipticTraces m t).mp ht)
    (fun t ht => hF t ((mem_ellipticTraces m t).mp ht))

end DepthAspect.TraceBounds
