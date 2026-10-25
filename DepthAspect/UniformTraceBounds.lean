import DepthAspect.ClassNumberWeights
import DepthAspect.PrimitiveRepresentatives
import DepthAspect.MartinDimension
import DepthAspect.ClassNumberGrowth

/-!
# Uniform elliptic estimates with every internal growth premise discharged

The remaining inputs are the general Martin identity, the cited arithmetic
class-number identity, the primitive class decomposition/nonnegativity, and
the actual primitive representative data. No dimension lower bound, class
number size bound, local root estimate, or elliptic trace estimate is assumed.
-/
namespace DepthAspect.TraceBounds
open scoped BigOperators

noncomputable def uniformClassConstant (δ : ℝ) : ℝ := (2 + δ⁻¹) / Real.pi
noncomputable def uniformEllipticConstant (δ : ℝ) : ℝ :=
  ellipticConstant (uniformClassConstant δ) δ

theorem uniformClassConstant_pos {δ : ℝ} (hδ : 0 < δ) : 0 < uniformClassConstant δ :=
  OrderedDirichlet.class_number_constant_pos hδ

theorem uniformEllipticConstant_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < uniformEllipticConstant δ := by
  have hC := uniformClassConstant_pos hδ
  have hz : 1 ≤ zetaMajorant δ := by
    simpa [zetaMajorant] using (content_pseries_summable hδ).le_tsum 0
      (fun j _ => by positivity)
  have hzpos : 0 < zetaMajorant δ := lt_of_lt_of_le zero_lt_one hz
  have hq := decayRatio_lt_one hδ
  have hden : 0 < 1 - decayRatio δ := sub_pos.mpr hq
  unfold uniformEllipticConstant ellipticConstant
  positivity

/-- The actual class-number formula uniformly bounds all admissible negative
arguments. Inadmissible arguments are zero by the stated class convention. -/
theorem uniform_class_growth (H : ℤ → ℝ)
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨ Nonempty (ClassNumberGrowth.ClassFormulaData H D))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ D : ℤ, D < 0 → H D ≤ uniformClassConstant δ * |(D : ℝ)| ^ (1 / 2 + δ) := by
  intro D hD
  rcases hformula D hD with hz | hdata
  · rw [hz]
    exact mul_nonneg (uniformClassConstant_pos hδ).le
      (Real.rpow_nonneg (abs_nonneg _) _)
  · let data := Classical.choice hdata
    rw [data.discriminant]
    exact ClassNumberGrowth.hurwitz_growth data.character data.odd data.modulus_pos
      data.conductor data.conductor_pos hδ data.formula

/-- The complete literal elliptic sum satisfies (35), with a constant depending
only on δ and with all internal dimension/class-size estimates proved. -/
theorem literalElliptic_bound_from_general_inputs (k n : ℕ) (hn : 8 ≤ n)
    (m : ℤ) (hm : 0 < m) (d : ℕ → ℝ)
    (hdim : MartinDimension.SatisfiesMartinFormula (k + 2) d)
    (h₀ H : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨ Nonempty (ClassNumberGrowth.ClassFormulaData H D))
    (δ : ℝ) (hδ : 0 < δ) (F : ℤ → ℕ → ContentDatum)
    (hF : ∀ t : ℤ, t ^ 2 < 4 * m → ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
      h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 →
      IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (F t u)) :
    ‖literalElliptic k n (d (2 ^ n)) m h₀ F‖ ≤
      uniformEllipticConstant δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) := by
  have hb := literalElliptic_bound k n (by omega) m hm (d (2 ^ n))
    (uniformClassConstant δ) δ (uniformClassConstant_pos hδ).le hδ
    (MartinDimension.polynomial_degree_dimension_lower k n hn d hdim)
    h₀ H h₀nonneg hidentity (uniform_class_growth H hformula hδ) F hF
  simpa only [uniformEllipticConstant] using hb

/-- A canonical literal sum with matrices constructed from primitive forms. -/
noncomputable def canonicalLiteralElliptic (k n : ℕ) (d : ℝ) (m : ℤ)
    (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D)) : ℂ :=
  literalElliptic k n d m h₀ (selectedRepresentative h₀ hforms m)

/-- The canonical (35) estimate now needs only the general external identities
and primitive-class data; the matrix representative conditions are discharged. -/
theorem canonicalLiteralElliptic_bound (k n : ℕ) (hn : 8 ≤ n)
    (m : ℤ) (hm : 0 < m) (hmOdd : Odd m) (d : ℕ → ℝ)
    (hdim : MartinDimension.SatisfiesMartinFormula (k + 2) d)
    (h₀ H : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨ Nonempty (ClassNumberGrowth.ClassFormulaData H D))
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (δ : ℝ) (hδ : 0 < δ) :
    ‖canonicalLiteralElliptic k n (d (2 ^ n)) m h₀ hforms‖ ≤
      uniformEllipticConstant δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) := by
  apply literalElliptic_bound_from_general_inputs k n hn m hm d hdim h₀ H
    h₀nonneg hidentity hformula δ hδ (selectedRepresentative h₀ hforms m)
  intro t ht u hu hw
  exact selectedRepresentative_valid h₀ hforms m hmOdd t ht u hu hw

end DepthAspect.TraceBounds
