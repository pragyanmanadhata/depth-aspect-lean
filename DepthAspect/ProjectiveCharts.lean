import DepthAspect.ContentReduction
import DepthAspect.ResidueBridge
import DepthAspect.LocalCancellation
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The actual unit-orbit quotient and its two projective charts

Primitive pairs have at least one unit coordinate. Two pairs are identified
exactly when one is a unit multiple of the other. Over a dyadic residue ring
this is the projective line used in Section 3.
-/
namespace DepthAspect.ProjectiveCharts

open scoped Classical

variable (R : Type*) [CommRing R]

/-- Pairs primitive over a local ring. -/
def PrimitivePair := {p : R × R // IsUnit p.1 ∨ IsUnit p.2}

/-- Actual simultaneous multiplication of both coordinates by a unit. -/
def orbitRel (p q : PrimitivePair R) : Prop :=
  ∃ u : Rˣ, q.1.1 = (u : R) * p.1.1 ∧ q.1.2 = (u : R) * p.1.2

/-- The orbit equivalence relation, proved directly from the unit group. -/
def orbitSetoid : Setoid (PrimitivePair R) where
  r := orbitRel R
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

/-- The quotient itself, rather than a replacement count. -/
def ProjectiveLine := Quotient (orbitSetoid R)

/-- The charts `(x,1)` and `(1,y)` with `y` a nonunit. -/
def Chart := R ⊕ {y : R // ¬ IsUnit y}

/-- Each chart gives an actual primitive pair. -/
def representative : Chart R → PrimitivePair R
  | .inl x => ⟨(x, 1), Or.inr isUnit_one⟩
  | .inr y => ⟨(1, y.1), Or.inl isUnit_one⟩

/-- The chart map lands in the orbit quotient. -/
def chartMap (c : Chart R) : ProjectiveLine R :=
  Quotient.mk (orbitSetoid R) (representative R c)

variable {R}

/-- Whether the second coordinate is a unit is constant on an orbit. -/
theorem orbit_unit_second {p q : PrimitivePair R} (h : orbitRel R p q) :
    IsUnit p.1.2 ↔ IsUnit q.1.2 := by
  obtain ⟨u, _, h2⟩ := h
  rw [h2, IsUnit.mul_iff]
  simp [u.isUnit]

/-- Distinct canonical chart representatives never belong to the same orbit. -/
theorem representative_unique {c d : Chart R}
    (h : orbitRel R (representative R c) (representative R d)) : c = d := by
  cases c with
  | inl x =>
    cases d with
    | inl y =>
      obtain ⟨u, h1, h2⟩ := h
      change y = (u : R) * x at h1
      change 1 = (u : R) * 1 at h2
      have hu : (u : R) = 1 := by simpa using h2.symm
      simp only [hu, one_mul] at h1
      exact congrArg Sum.inl h1.symm
    | inr y =>
      have hu := (orbit_unit_second h).mp isUnit_one
      exact False.elim (y.property hu)
  | inr x =>
    cases d with
    | inl y =>
      have hu := (orbit_unit_second h).mpr isUnit_one
      exact False.elim (x.property hu)
    | inr y =>
      obtain ⟨u, h1, h2⟩ := h
      change 1 = (u : R) * 1 at h1
      change y.1 = (u : R) * x.1 at h2
      have hu : (u : R) = 1 := by simpa using h1.symm
      simp only [hu, one_mul] at h2
      exact congrArg Sum.inr (Subtype.ext h2.symm)

/-- Every primitive pair admits a canonical representative in exactly one chart. -/
theorem representative_exists (p : PrimitivePair R) :
    ∃ c : Chart R, orbitRel R (representative R c) p := by
  classical
  by_cases hy : IsUnit p.1.2
  · obtain ⟨u, hu⟩ := hy
    refine ⟨.inl ((↑(u⁻¹) : R) * p.1.1), u, ?_, ?_⟩
    · change p.1.1 = (u : R) * ((↑(u⁻¹) : R) * p.1.1)
      simp
    · change p.1.2 = (u : R) * 1
      simpa using hu.symm
  · have hx : IsUnit p.1.1 := p.property.resolve_right hy
    obtain ⟨u, hu⟩ := hx
    have hn : ¬ IsUnit ((↑(u⁻¹) : R) * p.1.2) := by
      intro h
      exact hy (IsUnit.mul_iff.mp h).2
    refine ⟨.inr ⟨(↑(u⁻¹) : R) * p.1.2, hn⟩, u, ?_, ?_⟩
    · change p.1.1 = (u : R) * 1
      simpa using hu.symm
    · change p.1.2 = (u : R) * ((↑(u⁻¹) : R) * p.1.2)
      simp

/-- The map from charts is injective as a map into the actual quotient. -/
theorem chartMap_injective : Function.Injective (chartMap R) := by
  intro c d h
  exact representative_unique (Quotient.exact h)

/-- The map from charts is surjective onto the actual quotient. -/
theorem chartMap_surjective : Function.Surjective (chartMap R) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  obtain ⟨c, hc⟩ := representative_exists p
  exact ⟨c, Quotient.sound hc⟩

/-- A genuine equivalence from the two canonical charts to the unit-orbit quotient. -/
noncomputable def chartsEquiv : Chart R ≃ ProjectiveLine R :=
  Equiv.ofBijective (chartMap R) ⟨chartMap_injective, chartMap_surjective⟩

/-- The homogeneous binary quadratic form evaluated at a primitive pair. -/
def form (A B C : R) (p : PrimitivePair R) : R :=
  A * p.1.1 ^ 2 + B * p.1.1 * p.1.2 + C * p.1.2 ^ 2

/-- The zero locus is invariant under the unit action. -/
theorem form_zero_invariant (A B C : R) {p q : PrimitivePair R}
    (h : orbitRel R p q) : form A B C p = 0 ↔ form A B C q = 0 := by
  obtain ⟨u, h1, h2⟩ := h
  have heq : form A B C q = (u : R) ^ 2 * form A B C p := by
    unfold form
    rw [h1, h2]
    ring
  rw [heq, pow_two, mul_assoc, u.mul_right_eq_zero, u.mul_right_eq_zero]

/-- Roots are defined on the quotient by descent of the actual homogeneous form. -/
def IsRoot (A B C : R) : ProjectiveLine R → Prop :=
  Quotient.lift (fun p => form A B C p = 0)
    (fun _ _ h => propext (form_zero_invariant A B C h))

/-- Root equations in the two charts. -/
def ChartRoot (A B C : R) : Chart R → Prop
  | .inl x => A * x ^ 2 + B * x + C = 0
  | .inr y => A + B * y.1 + C * y.1 ^ 2 = 0

/-- The quotient equivalence respects the root equation. -/
theorem chart_root_iff (A B C : R) (c : Chart R) :
    ChartRoot A B C c ↔ IsRoot A B C (chartsEquiv c) := by
  cases c <;> simp [ChartRoot, IsRoot, chartsEquiv, chartMap, representative, form]

/-- Actual projective roots correspond to roots in the two charts. -/
noncomputable def rootChartsEquiv (A B C : R) :
    {c : Chart R // ChartRoot A B C c} ≃
      {p : ProjectiveLine R // IsRoot A B C p} :=
  chartsEquiv.subtypeEquiv (chart_root_iff A B C)

/-- Splitting the chart-root subtype gives the two explicit affine root sets. -/
def chartRootSumEquiv (A B C : R) :
    {c : Chart R // ChartRoot A B C c} ≃
      ({x : R // A * x ^ 2 + B * x + C = 0} ⊕
        {y : R // ¬ IsUnit y ∧ A + B * y + C * y ^ 2 = 0}) where
  toFun c := match c with
    | ⟨.inl x, hx⟩ => .inl ⟨x, hx⟩
    | ⟨.inr y, hy⟩ => .inr ⟨y.1, y.property, hy⟩
  invFun c := match c with
    | .inl ⟨x, hx⟩ => ⟨.inl x, hx⟩
    | .inr ⟨y, hy, hz⟩ => ⟨.inr ⟨y, hy⟩, hz⟩
  left_inv := by rintro ⟨c, hc⟩; cases c <;> rfl
  right_inv := by
    intro c
    cases c with
    | inl x => rfl
    | inr y => obtain ⟨y, hy, hz⟩ := y; rfl

noncomputable instance [Fintype R] : Fintype (Chart R) := by
  unfold Chart
  infer_instance

noncomputable instance [Fintype R] : Fintype (ProjectiveLine R) := by
  classical
  exact Fintype.ofEquiv (Chart R) chartsEquiv

/-- Cardinality of actual quotient roots is the sum of the two affine chart counts. -/
theorem projective_root_card [Fintype R] (A B C : R) :
    Fintype.card {p : ProjectiveLine R // IsRoot A B C p} =
      Fintype.card {x : R // A * x ^ 2 + B * x + C = 0} +
      Fintype.card {y : R // ¬ IsUnit y ∧ A + B * y + C * y ^ 2 = 0} := by
  classical
  have he := (rootChartsEquiv A B C).symm.trans (chartRootSumEquiv A B C)
  rw [Fintype.card_congr he, Fintype.card_sum]

/-- At every positive dyadic depth, the nonunit chart is precisely the chart
whose canonical coordinate is even. -/
theorem dyadic_nonunit_iff_even_val (h : ℕ) (hh : 1 ≤ h) (y : ZMod (2 ^ h)) :
    ¬ IsUnit y ↔ Even y.val := by
  have hu := ZMod.isUnit_natCast_iff_not_dvd_pow (a := y.val) Nat.prime_two (by omega : 0 < h)
  simp only [ZMod.natCast_zmod_val] at hu
  rw [hu, not_not, ← even_iff_two_dvd]

/-- The nonunit condition for an arbitrary integer representative is exactly parity. -/
theorem dyadic_nonunit_intCast_iff_even (h : ℕ) (hh : 1 ≤ h) (x : ℤ) :
    ¬ IsUnit (x : ZMod (2 ^ h)) ↔ Even x := by
  rw [dyadic_nonunit_iff_even_val h hh, ← Int.even_coe_nat, ZMod.val_intCast]
  have hd : (2 : ℤ) ∣ 2 ^ h := dvd_pow_self 2 (by omega : h ≠ 0)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (ContentReduction.even_periodic ((2 : ℤ) ^ h) x hd).symm

/-- The second actual residue-ring chart has exactly the integer count in `rho`. -/
theorem second_chart_card (h : ℕ) (hh : 1 ≤ h) (A B C : ℤ) :
    Fintype.card {y : ZMod (2 ^ h) // ¬ IsUnit y ∧
      (A : ZMod (2 ^ h)) + (B : ZMod (2 ^ h)) * y + C * y ^ 2 = 0} =
      (ContentReduction.secondChart h A B C).card := by
  have he := ResidueBridge.canonicalPredicateEquiv h
    (fun y => Even y ∧ (2 : ℤ) ^ h ∣ A + B * y + C * y ^ 2)
    (fun y : ZMod (2 ^ h) => ¬ IsUnit y ∧
      (A : ZMod (2 ^ h)) + (B : ZMod (2 ^ h)) * y + C * y ^ 2 = 0)
    (fun y => by
      rw [dyadic_nonunit_intCast_iff_even h hh]
      apply and_congr_right
      intro _
      have hy := ZMod.intCast_zmod_eq_zero_iff_dvd (A + B * y + C * y ^ 2) (2 ^ h)
      push_cast at hy
      exact hy)
  simpa only [ContentReduction.secondChart, Fintype.card_coe] using
    (Fintype.card_congr he).symm

/-- Equation (18)'s two-chart count is exactly the number of roots in the
actual quotient of primitive pairs by multiplication by units. -/
theorem dyadic_projective_root_card (h : ℕ) (hh : 1 ≤ h) (A B C : ℤ) :
    Fintype.card {p : ProjectiveLine (ZMod (2 ^ h)) //
      IsRoot (A : ZMod (2 ^ h)) (B : ZMod (2 ^ h)) (C : ZMod (2 ^ h)) p} =
        ContentReduction.rho h A B C := by
  rw [projective_root_card]
  convert congrArg₂ (fun x y : ℕ => x + y)
    (ResidueBridge.integer_quadratic_card h A B C).symm
    (second_chart_card h hh A B C) using 1 <;> congr!

/-- The number of actual projective roots modulo a dyadic prime power. -/
noncomputable def dyadicRootCount (h : ℕ) (A B C : ℤ) : ℕ :=
  Fintype.card {p : ProjectiveLine (ZMod (2 ^ h)) //
    IsRoot (A : ZMod (2 ^ h)) (B : ZMod (2 ^ h)) (C : ZMod (2 ^ h)) p}

/-- Content reduction (20), expressed directly on the projective quotient. -/
theorem projective_content_reduction (e j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) :
    dyadicRootCount (e + j) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) =
      2 ^ e * dyadicRootCount j A B C := by
  simp only [dyadicRootCount, dyadic_projective_root_card (e + j) (by omega),
    dyadic_projective_root_card j hj]
  exact ContentReduction.rho_content_reduction e j A B C hj

/-- The all-scalar branch (20), on the actual quotient. -/
theorem projective_all_scalar (h e : ℕ) (A B C : ℤ) (hh : 1 ≤ h) (he : h ≤ e) :
    dyadicRootCount h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) = 3 * 2 ^ (h - 1) := by
  simp only [dyadicRootCount, dyadic_projective_root_card h hh]
  exact ContentReduction.rho_all_scalar h e A B C hh he

/-- Local cancellation for the genuine projective quotient, after removing
any common power of two from the coefficients. All three depths are positive. -/
theorem projective_local_cancellation (n e : ℕ) (hn : 3 ≤ n) (A B C : ℤ)
    (hprim : Odd A ∨ Odd B ∨ Odd C)
    (hbad : ¬ (2 : ℤ) ^ (n + e - 2) ∣
      ((2 : ℤ) ^ e * B) ^ 2 - 4 * ((2 : ℤ) ^ e * A) * ((2 : ℤ) ^ e * C)) :
    (dyadicRootCount n (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) -
      2 * (dyadicRootCount (n - 1) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) +
      (dyadicRootCount (n - 2) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) = 0 := by
  simp only [dyadicRootCount, dyadic_projective_root_card n (by omega),
    dyadic_projective_root_card (n - 1) (by omega),
    dyadic_projective_root_card (n - 2) (by omega)]
  exact LocalCancellation.local_cancellation n e (by omega) A B C hprim hbad

end DepthAspect.ProjectiveCharts
