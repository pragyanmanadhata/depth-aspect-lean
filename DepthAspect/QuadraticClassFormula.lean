import DepthAspect.QuadraticCharacterEight
import DepthAspect.DyadicClassScaling
import DepthAspect.OddDiscriminantValues
import DepthAspect.DiscriminantFactorization
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# A general quadratic class-number interface and its small discriminants

The input is the cited analytic class-number identity for every negative
fundamental discriminant and every positive conductor. Character values are
fixed by the defining quadratic-symbol identities. The modulus-four and
modulus-eight characters, and the needed specializations, are conclusions.
-/
namespace DepthAspect.QuadraticClassFormula
open FundamentalDiscriminant OddDiscriminantValues QuadraticCharacterValues
open DyadicClassScaling ImprimitiveBoundary ClassNumberGrowth

/-- The cited general analytic class-number identity. No evaluation, growth
bound, conductor recurrence, or signed-count formula is an input. -/
structure GeneralFormula (H : ℤ → ℝ) where
  quadratic : ∀ d : ℤ, IsFundamental d → d < 0 → QuadraticCharacterData d
  odd : ∀ d hd hneg, (quadratic d hd hneg).character.Odd
  /-- The standard defining conductor property of the primitive quadratic
  character attached to a fundamental discriminant. -/
  primitive : ∀ d hd hneg, (quadratic d hd hneg).character.IsPrimitive
  formula : ∀ (d : ℤ) (hd : IsFundamental d) (hneg : d < 0)
    (f : ℕ) (hf : 0 < f),
    H (d * (f : ℤ) ^ 2) = Real.sqrt ((d.natAbs : ℝ) * (f : ℝ) ^ 2) / Real.pi *
      (@ImprimitiveLSeries.continuationCandidate d.natAbs
        ⟨by simpa using (ne_of_lt hneg : d ≠ 0)⟩
        (quadratic d hd hneg).character f 1).re

theorem minus_four_fundamental : IsFundamental (-4) := by
  right
  refine ⟨-1, by norm_num, ?_, Or.inr (by norm_num)⟩
  norm_num

theorem minus_eight_fundamental : IsFundamental (-8) := by
  right
  refine ⟨-2, by norm_num, ?_, Or.inl (by norm_num)⟩
  simpa using Nat.prime_two.squarefree

/-- Equality of characters after normalizing an equal modulus is sufficient
for equality of the corresponding ordered class values. This avoids any
reliance on elaborator reduction of the integer absolute-value index. -/
theorem classValue_eq_of_heq {q q' : ℕ} (hq : q = q')
    {χ : DirichletCharacter ℂ q} {ψ : DirichletCharacter ℂ q'}
    (hχψ : HEq χ ψ) (hχ : χ.Odd) (hψ : ψ.Odd)
    (hqpos : 0 < q) (hq'pos : 0 < q') (f : ℕ) (hf : 0 < f) :
    classValue χ hχ hqpos f hf = classValue ψ hψ hq'pos f hf := by
  subst q'
  have heq : χ = ψ := eq_of_heq hχψ
  subst ψ
  rfl

private theorem four_character_unique {q : ℕ} (hq : q = 4)
    (χ : DirichletCharacter ℂ q)
    (h2 : χ (2 : ZMod q) = 0) (h3 : χ (3 : ZMod q) = -1) :
    HEq χ chiMinusFour := by
  subst q
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  apply heq_of_eq
  apply DFunLike.ext
  intro x
  fin_cases x
  · change χ (0 : ZMod 4) = chiMinusFour (0 : ZMod 4)
    exact χ.map_zero.trans chiMinusFour.map_zero.symm
  · change χ (1 : ZMod 4) = chiMinusFour (1 : ZMod 4)
    exact χ.map_one.trans chiMinusFour.map_one.symm
  · have hc := chiMinusFour_even 1
    norm_num at hc
    exact h2.trans hc.symm
  · have hc := chiMinusFour_odd_value 1
    norm_num at hc
    exact h3.trans hc.symm

/-- The defining quadratic-symbol values determine the actual modulus-four
character. The heterogeneous equality only records the proved equality
`(-4).natAbs = 4` between its two displayed indices. -/
theorem minus_four_character (χ : QuadraticCharacterData (-4)) :
    HEq χ.character chiMinusFour := by
  have h2 := χ.two_value
  rw [twoSymbol_even (by decide : Even (-4 : ℤ))] at h2
  norm_num only [Int.cast_zero] at h2
  have h3 := χ.odd_prime_value 3 (by decide) (by decide)
  norm_num at h3
  exact four_character_unique (q := (-4 : ℤ).natAbs) (by norm_num) χ.character h2 h3

private theorem eight_character_unique {q : ℕ} (hq : q = 8)
    (χ : DirichletCharacter ℂ q)
    (h2 : χ (2 : ZMod q) = 0) (h3 : χ (3 : ZMod q) = 1)
    (h5 : χ (5 : ZMod q) = -1) (h7 : χ (7 : ZMod q) = -1) :
    HEq χ chiMinusEight := by
  subst q
  letI : Fact (1 < (8 : ℕ)) := ⟨by decide⟩
  apply heq_of_eq
  have h4 : χ (4 : ZMod 8) = 0 := by
    change χ ((2 : ZMod 8) * 2) = 0
    rw [map_mul, h2, zero_mul]
  have h6 : χ (6 : ZMod 8) = 0 := by
    change χ ((2 : ZMod 8) * 3) = 0
    rw [map_mul, h2, zero_mul]
  have hc2 := chiMinusEight_even 1
  have hc3 := chiMinusEight_four_add_three 0
  have hc4 := chiMinusEight_even 2
  have hc5 := chiMinusEight_four_add_one 1
  have hc6 := chiMinusEight_even 3
  have hc7 := chiMinusEight_four_add_three 1
  norm_num at hc2 hc3 hc4 hc5 hc6 hc7
  apply DFunLike.ext
  intro x
  fin_cases x
  · change χ (0 : ZMod 8) = chiMinusEight (0 : ZMod 8)
    exact χ.map_zero.trans chiMinusEight.map_zero.symm
  · change χ (1 : ZMod 8) = chiMinusEight (1 : ZMod 8)
    exact χ.map_one.trans chiMinusEight.map_one.symm
  · exact h2.trans hc2.symm
  · exact h3.trans hc3.symm
  · exact h4.trans hc4.symm
  · exact h5.trans hc5.symm
  · exact h6.trans hc6.symm
  · exact h7.trans hc7.symm

/-- Likewise the actual negative-eight character is determined by its values
at the primes 2,3,5,7; the index equality is kept explicit. -/
theorem minus_eight_character (χ : QuadraticCharacterData (-8)) :
    HEq χ.character chiMinusEight := by
  have h2 := χ.two_value
  rw [twoSymbol_even (by decide : Even (-8 : ℤ))] at h2
  norm_num only [Int.cast_zero] at h2
  have h3 := χ.odd_prime_value 3 (by decide) (by decide)
  have h5 := χ.odd_prime_value 5 (by decide) (by decide)
  have h7 := χ.odd_prime_value 7 (by decide) (by decide)
  norm_num at h3 h5 h7
  exact eight_character_unique (q := (-8 : ℤ).natAbs) (by norm_num) χ.character h2 h3 h5 h7

/-- The general analytic identity gives the ordered class value by the
proved continuation-at-one theorem. -/
theorem GeneralFormula.ordered {H : ℤ → ℝ} (G : GeneralFormula H)
    (d : ℤ) (hd : IsFundamental d) (hneg : d < 0) (f : ℕ) (hf : 0 < f) :
    H (d * (f : ℤ) ^ 2) = classValue (G.quadratic d hd hneg).character
      (G.odd d hd hneg) (Int.natAbs_pos.mpr (ne_of_lt hneg)) f hf := by
  have hq : 0 < d.natAbs := Int.natAbs_pos.mpr (ne_of_lt hneg)
  letI : NeZero d.natAbs := ⟨Nat.ne_of_gt hq⟩
  rw [G.formula d hd hneg f hf,
    continuation_one_eq_ordered _ (G.odd d hd hneg) hq f hf]
  rfl

/-- The fixed-fundamental-character formula used by the conductor
recurrence is obtained by writing the negative discriminant as minus its
absolute value. -/
theorem GeneralFormula.negative_modulus {H : ℤ → ℝ} (G : GeneralFormula H)
    (d : ℤ) (hd : IsFundamental d) (hneg : d < 0) (f : ℕ) (hf : 0 < f) :
    H (-(d.natAbs : ℤ) * (f : ℤ) ^ 2) =
      classValue (G.quadratic d hd hneg).character (G.odd d hd hneg)
        (Int.natAbs_pos.mpr (ne_of_lt hneg)) f hf := by
  have heq : -(d.natAbs : ℤ) = d := by
    rw [Int.natCast_natAbs, abs_of_neg hneg, neg_neg]
  rw [heq]
  exact G.ordered d hd hneg f hf

/-- The general analytic formula supplies the growth module's exact data
for every actual negative quadratic discriminant. Fundamental-conductor
existence is proved, rather than requested as a new arithmetic input. -/
theorem GeneralFormula.classFormulaData {H : ℤ → ℝ} (G : GeneralFormula H)
    (D : ℤ) (hD : D < 0) (hmod : D % 4 = 0 ∨ D % 4 = 1) :
    Nonempty (ClassFormulaData H D) := by
  obtain ⟨d, f, hd, hneg, hf, heq⟩ := exists_fundamental_factorization D hD hmod
  refine ⟨{
    modulus := d.natAbs
    conductor := f
    character := (G.quadratic d hd hneg).character
    odd := G.odd d hd hneg
    modulus_pos := Int.natAbs_pos.mpr (ne_of_lt hneg)
    conductor_pos := hf
    discriminant := ?_
    formula := ?_
  }⟩
  · have hdabs : |(d : ℝ)| = (d.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hfabs : |(f : ℝ)| = (f : ℝ) := abs_of_nonneg (Nat.cast_nonneg f)
    rw [heq]
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, abs_mul, abs_pow, hfabs, hdabs]
  · rw [heq]
    exact G.ordered d hd hneg f hf

/-- This supplies the fixed-character formula used in the even-depth sign
count from the one general external class-number identity. -/
theorem GeneralFormula.minus_four {H : ℤ → ℝ} (G : GeneralFormula H)
    (f : ℕ) (hf : 0 < f) :
    H (-4 * (f : ℤ) ^ 2) = classValue chiMinusFour chiMinusFour_odd (by decide) f hf := by
  have h := G.ordered (-4) minus_four_fundamental (by norm_num) f hf
  exact h.trans (classValue_eq_of_heq (q := (-4 : ℤ).natAbs) (q' := 4) (by norm_num)
    (minus_four_character (G.quadratic (-4) minus_four_fundamental (by norm_num)))
    (G.odd (-4) minus_four_fundamental (by norm_num)) chiMinusFour_odd
    (by norm_num) (by norm_num) f hf)

/-- The analogous fixed-character formula for odd depth, without assuming
the special H(-2^j) values. -/
theorem GeneralFormula.minus_eight {H : ℤ → ℝ} (G : GeneralFormula H)
    (f : ℕ) (hf : 0 < f) :
    H (-8 * (f : ℤ) ^ 2) = classValue chiMinusEight chiMinusEight_odd (by decide) f hf := by
  have h := G.ordered (-8) minus_eight_fundamental (by norm_num) f hf
  exact h.trans (classValue_eq_of_heq (q := (-8 : ℤ).natAbs) (q' := 8) (by norm_num)
    (minus_eight_character (G.quadratic (-8) minus_eight_fundamental (by norm_num)))
    (G.odd (-8) minus_eight_fundamental (by norm_num)) chiMinusEight_odd
    (by norm_num) (by norm_num) f hf)

end DepthAspect.QuadraticClassFormula
