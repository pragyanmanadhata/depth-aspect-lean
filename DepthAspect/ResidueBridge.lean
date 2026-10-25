import DepthAspect.SquareDivisibility
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Canonical integer representatives and ZMod solutions

This equivalence connects the actual integer root counts to the quadratic
completion-of-the-square equivalence over the residue ring.
-/

namespace DepthAspect.ResidueBridge
open SquareDivisibility

/-- A generic bridge for any predicate defined on residue classes. -/
def canonicalPredicateEquiv (j : ℕ) (P : ℤ → Prop) [DecidablePred P]
    (Q : ZMod (2 ^ j) → Prop) (h : ∀ x : ℤ, Q (x : ZMod (2 ^ j)) ↔ P x) :
    {x : ℤ // x ∈ (Finset.Ico 0 ((2 : ℤ) ^ j)).filter P} ≃
      {y : ZMod (2 ^ j) // Q y} where
  toFun x := ⟨(x : ℤ), (h x).mpr (Finset.mem_filter.mp x.property).2⟩
  invFun y := ⟨((y : ZMod (2 ^ j)).val : ℤ), by
    have hylt : (((y : ZMod (2 ^ j)).val : ℕ) : ℤ) < (2 : ℤ) ^ j := by
      exact_mod_cast (y : ZMod (2 ^ j)).val_lt
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by positivity, hylt⟩, ?_⟩
    apply (h _).mp
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using y.property⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨hx0, hxlt⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp x.property).1
    change (((x : ℤ) : ZMod (2 ^ j)).val : ℤ) = (x : ℤ)
    rw [ZMod.val_intCast]
    apply Int.emod_eq_of_lt hx0
    exact_mod_cast hxlt
  right_inv y := by
    apply Subtype.ext
    change ((((y : ZMod (2 ^ j)).val : ℕ) : ℤ) : ZMod (2 ^ j)) = (y : ZMod (2 ^ j))
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Polynomial roots in canonical integer representatives have exactly the
same cardinality as roots in the residue ring. -/
theorem integer_quadratic_card (j : ℕ) (A B C : ℤ) :
    ((Finset.Ico 0 ((2 : ℤ) ^ j)).filter
      (fun x => (2 : ℤ) ^ j ∣ A * x ^ 2 + B * x + C)).card =
    Fintype.card {x : ZMod (2 ^ j) //
      (A : ZMod (2 ^ j)) * x ^ 2 + (B : ZMod (2 ^ j)) * x + C = 0} := by
  classical
  have h := canonicalPredicateEquiv j
    (fun x => (2 : ℤ) ^ j ∣ A * x ^ 2 + B * x + C)
    (fun x => (A : ZMod (2 ^ j)) * x ^ 2 + (B : ZMod (2 ^ j)) * x + C = 0)
    (fun x => by
      have hx := ZMod.intCast_zmod_eq_zero_iff_dvd (A * x ^ 2 + B * x + C) (2 ^ j)
      push_cast at hx
      exact hx)
  simpa only [Fintype.card_coe] using Fintype.card_congr h

theorem square_zero_iff_dvd (j : ℕ) (d x : ℤ) :
    (x : ZMod (2 ^ j)) ^ 2 - (d : ZMod (2 ^ j)) = 0 ↔
      (2 : ℤ) ^ j ∣ x ^ 2 - d := by
  have h := ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 2 - d) (2 ^ j)
  push_cast at h
  exact h

def canonicalSquareEquiv (j : ℕ) (d : ℤ) :
    {x : ℤ // x ∈ squareRoots j d} ≃
      {y : ZMod (2 ^ j) // y ^ 2 - (d : ZMod (2 ^ j)) = 0} where
  toFun x := ⟨(x : ℤ), (square_zero_iff_dvd j d x).mpr (Finset.mem_filter.mp x.property).2⟩
  invFun y := ⟨((y : ZMod (2 ^ j)).val : ℤ), by
    have hylt : (((y : ZMod (2 ^ j)).val : ℕ) : ℤ) < (2 : ℤ) ^ j := by
      exact_mod_cast (y : ZMod (2 ^ j)).val_lt
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by positivity, hylt⟩, ?_⟩
    apply (square_zero_iff_dvd j d _).mp
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using y.property⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨hx0, hxlt⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp x.property).1
    change (((x : ℤ) : ZMod (2 ^ j)).val : ℤ) = (x : ℤ)
    rw [ZMod.val_intCast]
    apply Int.emod_eq_of_lt hx0
    exact_mod_cast hxlt
  right_inv y := by
    apply Subtype.ext
    change ((((y : ZMod (2 ^ j)).val : ℕ) : ℤ) : ZMod (2 ^ j)) = (y : ZMod (2 ^ j))
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem zmod_square_card (j : ℕ) (d : ℤ) :
    Fintype.card {y : ZMod (2 ^ j) // y ^ 2 - (d : ZMod (2 ^ j)) = 0} =
      (squareRoots j d).card := by
  classical
  rw [← Fintype.card_congr (canonicalSquareEquiv j d)]
  exact Fintype.card_coe _

end DepthAspect.ResidueBridge
