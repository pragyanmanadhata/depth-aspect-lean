import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The actual additive-character sum in (74)

The sum is taken over the odd residues 2a+1 modulo 2Q. At dyadic modulus
these are exactly the reduced residues. Its indicator formula and alternating
value are proved from a finite geometric sum of the standard additive character.
-/
namespace DepthAspect.DyadicRamanujan
open scoped BigOperators

noncomputable def residueCharacter (q : ℕ) [NeZero q] (t : ℤ) : ℂ :=
  ZMod.stdAddChar (t : ZMod q)

@[simp] theorem residueCharacter_eq_one (q : ℕ) [NeZero q] (t : ℤ) :
    residueCharacter q t = 1 ↔ (q : ℤ) ∣ t := by
  unfold residueCharacter
  rw [← (ZMod.stdAddChar (N := q)).map_zero_eq_one,
    ZMod.injective_stdAddChar.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem residueCharacter_add (q : ℕ) [NeZero q] (s t : ℤ) :
    residueCharacter q (s + t) = residueCharacter q s * residueCharacter q t := by
  simp only [residueCharacter, Int.cast_add, AddChar.map_add_eq_mul]

theorem residueCharacter_nat_mul (q : ℕ) [NeZero q] (a : ℕ) (t : ℤ) :
    residueCharacter q ((a : ℤ) * t) = residueCharacter q t ^ a := by
  simp only [residueCharacter, Int.cast_mul, Int.cast_natCast]
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

/-- Literal odd residue character sum, with modulus 2Q. -/
noncomputable def oddResidueSum (Q : ℕ) [NeZero Q] (t : ℤ) : ℂ :=
  ∑ a ∈ Finset.range Q, residueCharacter (2 * Q) ((2 * (a : ℤ) + 1) * t)

theorem oddResidueSum_geometric (Q : ℕ) [NeZero Q] (t : ℤ) :
    oddResidueSum Q t = residueCharacter (2 * Q) t *
      ∑ a ∈ Finset.range Q, residueCharacter (2 * Q) (2 * t) ^ a := by
  unfold oddResidueSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show (2 * (a : ℤ) + 1) * t = t + (a : ℤ) * (2 * t) by ring,
    residueCharacter_add, residueCharacter_nat_mul]

theorem doubledCharacter_eq_one (Q : ℕ) [NeZero Q] (t : ℤ) :
    residueCharacter (2 * Q) (2 * t) = 1 ↔ (Q : ℤ) ∣ t := by
  rw [residueCharacter_eq_one]
  push_cast
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)

theorem doubledCharacter_pow (Q : ℕ) [NeZero Q] (t : ℤ) :
    residueCharacter (2 * Q) (2 * t) ^ Q = 1 := by
  rw [← residueCharacter_nat_mul, residueCharacter_eq_one]
  refine ⟨t, ?_⟩
  push_cast
  ring

/-- The finite geometric sum is zero unless Q divides the frequency. -/
theorem oddResidueSum_eq_zero (Q : ℕ) [NeZero Q] (t : ℤ) (ht : ¬ (Q : ℤ) ∣ t) :
    oddResidueSum Q t = 0 := by
  rw [oddResidueSum_geometric]
  have hz : residueCharacter (2 * Q) (2 * t) ≠ 1 :=
    fun h => ht ((doubledCharacter_eq_one Q t).mp h)
  rw [geom_sum_eq hz, doubledCharacter_pow]
  simp

/-- The exact indicator formula (74), before restricting Q to powers of two. -/
theorem oddResidueSum_formula (Q : ℕ) [NeZero Q] (t : ℤ) :
    oddResidueSum Q t =
      (if ((2 * Q : ℕ) : ℤ) ∣ t then (2 * Q : ℂ) else 0) -
        (if (Q : ℤ) ∣ t then (Q : ℂ) else 0) := by
  classical
  by_cases ht : (Q : ℤ) ∣ t
  · have hz := (doubledCharacter_eq_one Q t).mpr ht
    have hs : residueCharacter (2 * Q) t ^ 2 = 1 := by
      rw [← residueCharacter_nat_mul (2 * Q) 2 t]
      exact hz
    rw [oddResidueSum_geometric, hz]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      ht, if_true]
    by_cases hbig : ((2 * Q : ℕ) : ℤ) ∣ t
    · rw [if_pos hbig, (residueCharacter_eq_one (2 * Q) t).mpr hbig]
      push_cast
      ring
    · have hn : residueCharacter (2 * Q) t ≠ 1 :=
        fun h => hbig ((residueCharacter_eq_one (2 * Q) t).mp h)
      have hminus := (sq_eq_one_iff.mp hs).resolve_left hn
      rw [if_neg hbig, hminus]
      ring
  · have hbig : ¬ ((2 * Q : ℕ) : ℤ) ∣ t := by
      intro h
      apply ht
      exact dvd_trans (by exact ⟨2, by push_cast; ring⟩) h
    rw [oddResidueSum_eq_zero Q t ht, if_neg ht, if_neg hbig]
    ring

/-- The actual sum at a multiple of the half modulus is alternating. -/
theorem oddResidueSum_scaled (Q : ℕ) [NeZero Q] (r : ℤ) :
    oddResidueSum Q ((Q : ℤ) * r) = (Q : ℂ) * (-1 : ℂ) ^ r := by
  rw [oddResidueSum_formula, neg_one_zpow_eq_ite]
  have hQ : (Q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have hbig : (((2 * Q : ℕ) : ℤ) ∣ (Q : ℤ) * r) ↔ Even r := by
    rw [show ((2 * Q : ℕ) : ℤ) = (Q : ℤ) * 2 by push_cast; ring,
      mul_dvd_mul_iff_left hQ, even_iff_two_dvd]
  rw [if_pos (dvd_mul_right (Q : ℤ) r)]
  by_cases hr : Even r
  · rw [if_pos hr, if_pos (hbig.mpr hr)]
    push_cast
    ring
  · rw [if_neg hr, if_neg (fun h => hr (hbig.mp h))]
    ring

/-- The character sum over the reduced residues modulo 2^(a+1). -/
noncomputable def ramanujanTwoPow (a : ℕ) (t : ℤ) : ℂ :=
  oddResidueSum (2 ^ a) t

theorem ramanujanTwoPow_formula (a : ℕ) (t : ℤ) :
    ramanujanTwoPow a t =
      (if (2 : ℤ) ^ (a + 1) ∣ t then (2 : ℂ) ^ (a + 1) else 0) -
        (if (2 : ℤ) ^ a ∣ t then (2 : ℂ) ^ a else 0) := by
  simpa only [ramanujanTwoPow, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    pow_succ, mul_comm] using oddResidueSum_formula (2 ^ a) t

theorem ramanujanTwoPow_scaled (a : ℕ) (r : ℤ) :
    ramanujanTwoPow a ((2 : ℤ) ^ a * r) = (2 : ℂ) ^ a * (-1 : ℂ) ^ r := by
  simpa only [ramanujanTwoPow, Nat.cast_pow, Nat.cast_ofNat] using
    oddResidueSum_scaled (2 ^ a) r

end DepthAspect.DyadicRamanujan
