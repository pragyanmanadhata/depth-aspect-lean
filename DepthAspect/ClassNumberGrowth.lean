import DepthAspect.OrderedDirichlet
import DepthAspect.ImprimitiveCharacter

/-!
# Uniform class-number growth from actual imprimitive characters

This gives an alternative proof of Lemma 2.2 with the constant
(2 + δ⁻¹)/π for H. The L-value is explicitly the limit of ordered partial
sums. The classical class-number formula, when supplied, must refer to
this value (or supply its standard identification with analytic continuation).
No L-value size estimate or class-number growth estimate is an input.
-/

open Filter
open scoped Topology
namespace DepthAspect.ClassNumberGrowth
open OrderedDirichlet ImprimitiveCharacter

/-- The value at one exists in the ordered sense for the literal imprimitive
character. Its definition does not use an unordered complex `tsum`. -/
theorem imprimitive_ordered_limit_exists {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) :
    ∃ L : ℂ, Tendsto (partialL (psiNat χ f)) atTop (𝓝 L) :=
  ordered_limit_exists _ (psiNat_partial_sum_norm_le χ hχ hq f hf)

noncomputable def imprimitiveLAtOne {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) : ℂ :=
  Classical.choose (imprimitive_ordered_limit_exists χ hχ hq f hf)

theorem imprimitiveLAtOne_limit {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) :
    Tendsto (partialL (psiNat χ f)) atTop (𝓝 (imprimitiveLAtOne χ hχ hq f hf)) :=
  Classical.choose_spec (imprimitive_ordered_limit_exists χ hχ hq f hf)

/-- The complete period is q*f, strictly smaller than or equal to the
absolute discriminant q*f². The logarithmic estimate is proved for the
actual character values. -/
theorem imprimitiveLAtOne_log_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) :
    ‖imprimitiveLAtOne χ hχ hq f hf‖ ≤ 2 + Real.log ((q : ℝ) * (f : ℝ) ^ 2) := by
  have hp : 0 < q * f := Nat.mul_pos hq hf
  have hbound := norm_ordered_limit_le (psiNat χ f) hp (psiNat_norm_le_one χ f)
    (psiNat_period_sum_zero χ hχ f) (psiNat_partial_sum_norm_le χ hχ hq f hf)
    (imprimitiveLAtOne_limit χ hχ hq f hf)
  apply hbound.trans
  apply add_le_add le_rfl
  apply Real.log_le_log (by exact_mod_cast hp)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast (show 1 ≤ f from hf)
  push_cast
  exact mul_le_mul_of_nonneg_left (by nlinarith : (f : ℝ) ≤ (f : ℝ) ^ 2) hqR.le

/-- The first bound in Lemma 2.2, with a uniform explicit constant. -/
theorem imprimitiveLAtOne_power_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) {δ : ℝ} (hδ : 0 < δ) :
    ‖imprimitiveLAtOne χ hχ hq f hf‖ ≤
      (2 + δ⁻¹) * ((q : ℝ) * (f : ℝ) ^ 2) ^ δ := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q from hq)
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast (show 1 ≤ f from hf)
  have hD : 1 ≤ (q : ℝ) * (f : ℝ) ^ 2 := by
    simpa using mul_le_mul hqR (by nlinarith : 1 ≤ (f : ℝ) ^ 2)
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ q)
  apply norm_ordered_limit_rpow hD hδ
  exact imprimitiveLAtOne_log_bound χ hχ hq f hf

/-- The second bound in Lemma 2.2 follows from the cited class-number formula.
The only analytic boundary in `hformula` is identification of the ordered
L-value with the value appearing in that formula. -/
theorem hurwitz_growth {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) {δ H : ℝ} (hδ : 0 < δ)
    (hformula : H = Real.sqrt ((q : ℝ) * (f : ℝ) ^ 2) / Real.pi *
      (imprimitiveLAtOne χ hχ hq f hf).re) :
    H ≤ ((2 + δ⁻¹) / Real.pi) * ((q : ℝ) * (f : ℝ) ^ 2) ^ (1 / 2 + δ) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q from hq)
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast (show 1 ≤ f from hf)
  have hD : 1 ≤ (q : ℝ) * (f : ℝ) ^ 2 := by
    simpa using mul_le_mul hqR (by nlinarith : 1 ≤ (f : ℝ) ^ 2)
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ q)
  exact class_number_bound_of_formula hD hδ
    (imprimitiveLAtOne_log_bound χ hχ hq f hf) hformula

/-- A precise interface for the cited class-number identity and the standard
negative-fundamental-discriminant character. It contains only identities and
arithmetic data; it contains no upper bound on a class number or L-value. -/
structure ClassFormulaData (H : ℤ → ℝ) (D : ℤ) where
  modulus : ℕ
  conductor : ℕ
  character : DirichletCharacter ℂ modulus
  odd : character.Odd
  modulus_pos : 0 < modulus
  conductor_pos : 0 < conductor
  discriminant : |(D : ℝ)| = (modulus : ℝ) * (conductor : ℝ) ^ 2
  formula : H D = Real.sqrt ((modulus : ℝ) * (conductor : ℝ) ^ 2) / Real.pi *
    (imprimitiveLAtOne character odd modulus_pos conductor conductor_pos).re

/-- The single global bound needed by the actual elliptic trace development.
Inadmissible arguments have zero class number; admissible ones use precisely
the cited formula data. The growth conclusion is derived uniformly. -/
theorem uniform_hurwitz_growth (H : ℤ → ℝ)
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨ Nonempty (ClassFormulaData H D))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℤ, D < 0 → H D ≤ C * |(D : ℝ)| ^ (1 / 2 + δ) := by
  refine ⟨(2 + δ⁻¹) / Real.pi, class_number_constant_pos hδ, ?_⟩
  intro D hD
  rcases hformula D hD with hz | hdata
  · rw [hz]
    exact mul_nonneg (class_number_constant_pos hδ).le
      (Real.rpow_nonneg (abs_nonneg _) _)
  · let data := Classical.choice hdata
    rw [data.discriminant]
    exact hurwitz_growth data.character data.odd data.modulus_pos data.conductor
      data.conductor_pos hδ data.formula

end DepthAspect.ClassNumberGrowth
