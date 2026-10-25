import DepthAspect.DyadicFixedLines
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Real.Basic

/-!
# The cited general local interpretation and its proved dyadic specialization

The external statement here is Popa (2.17)/Lemma 4.1 as used on manuscript
page 6: the primitive local kernel counts the projective roots of the
associated matrix quadratic. It is stated at every positive level Q, on
actual unimodular residue pairs modulo simultaneous unit multiplication.
Unimodularity is the Bezout condition, not the stronger one-coordinate-unit
condition, which would be incorrect at arbitrary composite level.

The identification with the trace formula's kernel remains a named cited
external input. Everything reducing that general input to the dyadic
fixedLineCount used in the estimates is proved below.
-/
namespace DepthAspect.PopaLocalInterpretation
open scoped Classical

variable (R : Type*) [CommRing R]

/-- Unimodularity at arbitrary level, expressed by the actual Bezout identity. -/
abbrev UnimodularPair := {p : R × R // ∃ a b : R, a * p.1 + b * p.2 = 1}

def unitOrbit (p q : UnimodularPair R) : Prop :=
  ∃ u : Rˣ, q.1.1 = (u : R) * p.1.1 ∧ q.1.2 = (u : R) * p.1.2

def unitOrbitSetoid : Setoid (UnimodularPair R) where
  r := unitOrbit R
  iseqv := {
    refl := fun p => ⟨1, by simp, by simp⟩
    symm := by
      intro p q h
      obtain ⟨u, h1, h2⟩ := h
      exact ⟨u⁻¹, by simp [h1], by simp [h2]⟩
    trans := by
      intro p q r h k
      obtain ⟨u, h1, h2⟩ := h
      obtain ⟨v, k1, k2⟩ := k
      exact ⟨v * u, by simp [k1, h1, mul_assoc], by simp [k2, h2, mul_assoc]⟩ }

abbrev GeneralProjectiveLine := Quotient (unitOrbitSetoid R)

noncomputable instance [Fintype R] : Fintype (UnimodularPair R) := Fintype.ofFinite _
noncomputable instance [Fintype R] : Fintype (GeneralProjectiveLine R) := Fintype.ofFinite _

def homogeneousForm (A B C : R) (p : UnimodularPair R) : R :=
  A * p.1.1 ^ 2 + B * p.1.1 * p.1.2 + C * p.1.2 ^ 2

theorem homogeneous_zero_invariant (A B C : R) {p q : UnimodularPair R}
    (h : unitOrbit R p q) :
    homogeneousForm R A B C p = 0 ↔ homogeneousForm R A B C q = 0 := by
  obtain ⟨u, h1, h2⟩ := h
  have heq : homogeneousForm R A B C q = (u : R) ^ 2 * homogeneousForm R A B C p := by
    unfold homogeneousForm
    rw [h1, h2]
    ring
  rw [heq, pow_two, mul_assoc, u.mul_right_eq_zero, u.mul_right_eq_zero]

def IsGeneralRoot (A B C : R) : GeneralProjectiveLine R → Prop :=
  Quotient.lift (fun p => homogeneousForm R A B C p = 0)
    (fun _ _ h => propext (homogeneous_zero_invariant R A B C h))

/-- A unit coordinate implies the genuine unimodular condition over any ring. -/
theorem bezout_of_unit_coordinate (p : R × R) (hp : IsUnit p.1 ∨ IsUnit p.2) :
    ∃ a b : R, a * p.1 + b * p.2 = 1 := by
  rcases hp with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact ⟨↑(u⁻¹), 0, by simp [← hu]⟩
  · exact ⟨0, ↑(u⁻¹), by simp [← hu]⟩

/-- General and one-unit-coordinate primitive pairs coincide when the latter
condition follows from unimodularity. -/
noncomputable def primitivePairEquiv
    (hlocal : ∀ p : R × R, (∃ a b : R, a * p.1 + b * p.2 = 1) →
      IsUnit p.1 ∨ IsUnit p.2) :
    UnimodularPair R ≃ ProjectiveCharts.PrimitivePair R where
  toFun p := ⟨p.1, hlocal p.1 p.property⟩
  invFun p := ⟨p.1, bezout_of_unit_coordinate R p.1 p.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl

/-- This is an equivalence of actual orbit quotients, not just an equality
of informal cardinality expressions. -/
noncomputable def projectiveEquiv
    (hlocal : ∀ p : R × R, (∃ a b : R, a * p.1 + b * p.2 = 1) →
      IsUnit p.1 ∨ IsUnit p.2) :
    GeneralProjectiveLine R ≃ ProjectiveCharts.ProjectiveLine R :=
  Quotient.congr (primitivePairEquiv R hlocal) (fun _ _ => Iff.rfl)

theorem projectiveEquiv_root
    (hlocal : ∀ p : R × R, (∃ a b : R, a * p.1 + b * p.2 = 1) →
      IsUnit p.1 ∨ IsUnit p.2) (A B C : R) (p : GeneralProjectiveLine R) :
    IsGeneralRoot R A B C p ↔
      ProjectiveCharts.IsRoot A B C (projectiveEquiv R hlocal p) := by
  refine Quotient.inductionOn p ?_
  intro q
  rfl

/-- Reduction modulo two proves the required local condition at every
positive dyadic depth. -/
theorem dyadic_unit_coordinate (h : ℕ) (hh : 0 < h) (p : ZMod (2 ^ h) × ZMod (2 ^ h))
    (hp : ∃ a b : ZMod (2 ^ h), a * p.1 + b * p.2 = 1) :
    IsUnit p.1 ∨ IsUnit p.2 := by
  by_contra hn
  push Not at hn
  obtain ⟨a, b, hab⟩ := hp
  let red : ZMod (2 ^ h) →+* ZMod 2 :=
    ZMod.castHom (dvd_pow_self 2 (by omega : h ≠ 0)) (ZMod 2)
  have hzero (x : ZMod (2 ^ h)) (hx : ¬ IsUnit x) : red x = 0 := by
    have hEven := (ProjectiveCharts.dyadic_nonunit_iff_even_val h (by omega) x).mp hx
    change ZMod.cast x = (0 : ZMod 2)
    rw [ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_zero_iff x.val 2).mpr hEven.two_dvd
  have hz := congrArg red hab
  rw [map_add, map_mul, map_mul, map_one, hzero p.1 hn.1, hzero p.2 hn.2] at hz
  norm_num at hz

/-- The literal general projective-root count of a matrix quadratic modulo Q. -/
noncomputable def generalRootCount (Q : ℕ) (hQ : 0 < Q)
    (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := by
  letI : NeZero Q := ⟨ne_of_gt hQ⟩
  exact Fintype.card {p : GeneralProjectiveLine (ZMod Q) //
    IsGeneralRoot (ZMod Q) (M 1 0 : ZMod Q)
      ((M 1 1 - M 0 0 : ℤ) : ZMod Q) ((-M 0 1 : ℤ) : ZMod Q) p}

/-- The general root quotient specializes to the already checked dyadic
fixed-projective-line count. -/
theorem generalRootCount_two_pow (h : ℕ) (hh : 0 < h)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : Odd (Matrix.det M)) :
    generalRootCount (2 ^ h) (by positivity) M = DyadicFixedLines.fixedLineCount h M := by
  rw [DyadicFixedLines.fixedLineCount_eq_rootCount h M hdet]
  unfold generalRootCount ProjectiveCharts.dyadicRootCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (projectiveEquiv (ZMod (2 ^ h)) (dyadic_unit_coordinate h hh))
  intro p
  exact projectiveEquiv_root (ZMod (2 ^ h)) (dyadic_unit_coordinate h hh) _ _ _ p

/-- The named external semantic input: Popa's primitive local kernel is the
projective-root count at every positive level coprime to the determinant.
This is precisely the general interpretation cited at (17)–(19), not a
specialized dyadic identity, cancellation, or size estimate. -/
structure GeneralPopaLocalFormula
    (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ) : Prop where
  projectiveInterpretation : ∀ (Q : ℕ) (hQ : 0 < Q) (M : Matrix (Fin 2) (Fin 2) ℤ),
    0 < Matrix.det M → (Matrix.trace M) ^ 2 < 4 * Matrix.det M →
    Nat.Coprime (Matrix.det M).natAbs Q →
      κ Q M = (generalRootCount Q hQ M : ℝ)

/-- The hlocal premise used in intermediate trace lemmas is a proved
specialization of the explicit general cited interpretation. -/
theorem GeneralPopaLocalFormula.dyadic
    {κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ}
    (hκ : GeneralPopaLocalFormula κ) (h : ℕ) (hh : 0 < h)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : Odd (Matrix.det M))
    (hdetpos : 0 < Matrix.det M) (helliptic : (Matrix.trace M) ^ 2 < 4 * Matrix.det M) :
    κ (2 ^ h) M = (DyadicFixedLines.fixedLineCount h M : ℝ) := by
  have hcop : Nat.Coprime (Matrix.det M).natAbs (2 ^ h) :=
    (Int.natAbs_odd.mpr hdet).coprime_two_right.pow_right h
  rw [hκ.projectiveInterpretation (2 ^ h) (by positivity) M hdetpos helliptic hcop,
    generalRootCount_two_pow h hh M hdet]

end DepthAspect.PopaLocalInterpretation
