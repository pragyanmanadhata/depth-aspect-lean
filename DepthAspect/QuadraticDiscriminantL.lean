import DepthAspect.QuadraticClassFormula
import DepthAspect.QuadraticCharacterReality

/-!
# Actual imprimitive characters indexed by negative discriminants

The fundamental part and conductor are selected from the proved integer
classification. The coefficient sequence is literally χ(n/gcd(n,f)), and
the value at one is its proved ordered-series limit. This supplies the
discriminant-indexed objects in the prime trace formulas without assuming
any conductor exponent, local weight, or class-number recurrence.
-/
namespace DepthAspect.QuadraticDiscriminantL
open FundamentalDiscriminant OddDiscriminantValues QuadraticClassFormula
open ClassNumberGrowth ImprimitiveCharacter OrderedDirichlet
open scoped Topology

def IsNegativeDiscriminant (D : ℤ) : Prop := D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

structure Datum (D : ℤ) where
  fundamental : ℤ
  conductor : ℕ
  fundamental_shape : IsFundamental fundamental
  fundamental_neg : fundamental < 0
  conductor_pos : 0 < conductor
  factorization : D = fundamental * (conductor : ℤ) ^ 2

theorem datum_nonempty (D : ℤ) (hD : IsNegativeDiscriminant D) : Nonempty (Datum D) := by
  obtain ⟨d, f, hd, hneg, hf, heq⟩ := exists_fundamental_factorization D hD.1 hD.2
  exact ⟨⟨d, f, hd, hneg, hf, heq⟩⟩

noncomputable def datum (D : ℤ) (hD : IsNegativeDiscriminant D) : Datum D :=
  Classical.choice (datum_nonempty D hD)

noncomputable def character {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) :
    DirichletCharacter ℂ (datum D hD).fundamental.natAbs :=
  (G.quadratic _ (datum D hD).fundamental_shape (datum D hD).fundamental_neg).character

theorem character_odd {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) : (character G D hD).Odd :=
  G.odd _ (datum D hD).fundamental_shape (datum D hD).fundamental_neg

theorem character_isPrimitive {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) : (character G D hD).IsPrimitive :=
  G.primitive _ (datum D hD).fundamental_shape (datum D hD).fundamental_neg

theorem character_ne_one {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) : character G D hD ≠ 1 := by
  intro h
  have hodd := character_odd G D hD
  rw [h] at hodd
  change (1 : DirichletCharacter ℂ _) (-1) = -1 at hodd
  rw [MulChar.one_apply isUnit_one.neg] at hodd
  norm_num at hodd

theorem modulus_pos (D : ℤ) (hD : IsNegativeDiscriminant D) :
    0 < (datum D hD).fundamental.natAbs :=
  Int.natAbs_pos.mpr (ne_of_lt (datum D hD).fundamental_neg)

/-- The actual coefficient sequence of the paper at a negative
discriminant; the extension outside that domain is set to zero. -/
noncomputable def psi {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ) (n : ℕ) : ℂ := by
  classical
  exact if hD : IsNegativeDiscriminant D then
    psiNat (character G D hD) (datum D hD).conductor n else 0

/-- The actual ordered value at one of the preceding coefficient sequence. -/
noncomputable def LAtOne {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ) : ℂ := by
  classical
  exact if hD : IsNegativeDiscriminant D then
    imprimitiveLAtOne (character G D hD) (character_odd G D hD) (modulus_pos D hD)
      (datum D hD).conductor (datum D hD).conductor_pos else 0

theorem LAtOne_limit {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) :
    Filter.Tendsto (partialL (psi G D)) Filter.atTop (𝓝 (LAtOne G D)) := by
  have hpsi : psi G D = psiNat (character G D hD) (datum D hD).conductor := by
    funext n
    simp only [psi, dif_pos hD]
  rw [hpsi]
  simp only [LAtOne, dif_pos hD]
  exact imprimitiveLAtOne_limit _ _ _ _ _

/-- The canonical discriminant-indexed ordered value is the actual real
quadratic L-value, viewed in the complex numbers. -/
theorem LAtOne_ofReal_re {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ) :
    ((LAtOne G D).re : ℂ) = LAtOne G D := by
  by_cases hD : IsNegativeDiscriminant D
  · simp only [LAtOne, dif_pos hD]
    exact (G.quadratic _ (datum D hD).fundamental_shape
      (datum D hD).fundamental_neg).LAtOne_ofReal_re _ _ _ _
  · simp [LAtOne, hD]

/-- Specializing the general analytic class formula to the actual
discriminant-indexed ordered value. -/
theorem hurwitz_eq {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) :
    H D = Real.sqrt (-(D : ℝ)) / Real.pi * (LAtOne G D).re := by
  have h := G.ordered _ (datum D hD).fundamental_shape
    (datum D hD).fundamental_neg _ (datum D hD).conductor_pos
  have hsize : ((datum D hD).fundamental.natAbs : ℝ) *
      ((datum D hD).conductor : ℝ) ^ 2 = -(D : ℝ) := by
    have habs : ((datum D hD).fundamental.natAbs : ℝ) =
        -((datum D hD).fundamental : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs,
        abs_of_neg (by exact_mod_cast (datum D hD).fundamental_neg)]
    have hfac : (D : ℝ) = ((datum D hD).fundamental : ℝ) *
        ((datum D hD).conductor : ℝ) ^ 2 := by
      exact_mod_cast (datum D hD).factorization
    rw [habs]
    nlinarith [hfac]
  rw [← (datum D hD).factorization] at h
  simpa only [DyadicClassScaling.classValue, LAtOne, dif_pos hD, character, hsize] using h

/-- The prime trace's discriminant always lies in the declared domain. -/
theorem elliptic_isNegativeDiscriminant (t m : ℤ) (ht : t ^ 2 < 4 * m) :
    IsNegativeDiscriminant (t ^ 2 - 4 * m) := by
  refine ⟨by omega, ?_⟩
  have htmod : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases htmod with h | h | h | h <;>
    norm_num [pow_two, Int.sub_emod, Int.mul_emod, h]

end DepthAspect.QuadraticDiscriminantL
