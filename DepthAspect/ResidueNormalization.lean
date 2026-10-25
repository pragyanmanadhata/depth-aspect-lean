import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp

/-!
# Normalizing an actual discriminant residue

These lemmas identify the normalized nonzero digit of a residue modulo p^(r+1)
with the integer quotient D/p^r. They supply the representative-independence
step used by the actual local Fourier strata.
-/
namespace DepthAspect.ResidueNormalization

 theorem val_modEq (N : ℕ) [NeZero N] (D : ℤ) :
    ((D : ZMod N).val : ℤ) ≡ D [ZMOD (N : ℤ)] := by
  rw [ZMod.val_intCast]
  exact Int.mod_modEq D N

 theorem divides_val_iff {a N : ℕ} [NeZero N] (haN : a ∣ N) (D : ℤ) :
    a ∣ (D : ZMod N).val ↔ (a : ℤ) ∣ D := by
  have h := (val_modEq N D).of_dvd (show (a : ℤ) ∣ (N : ℤ) by exact_mod_cast haN)
  simpa only [Int.natCast_dvd_natCast] using h.dvd_iff

 theorem val_ne_zero_iff {N : ℕ} [NeZero N] (D : ℤ) :
    (D : ZMod N).val ≠ 0 ↔ ¬ (N : ℤ) ∣ D := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd D N]
  exact not_congr (ZMod.val_eq_zero (D : ZMod N))

/-- Normalization by any known divisor respects the remaining modulus.
This includes the two- and three-digit moduli needed by the dyadic strata. -/
theorem normalized_modEq_mul {a N : ℕ} [NeZero a] [NeZero N] (D : ℤ)
    (hD : (a : ℤ) ∣ D) :
    (((D : ZMod (a * N)).val / a : ℕ) : ℤ) ≡
      D / (a : ℤ) [ZMOD (N : ℤ)] := by
  have ha : (a : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne a)
  have hdiv : a ∣ (D : ZMod (a * N)).val :=
    (divides_val_iff (dvd_mul_right a N) D).mpr hD
  have hdivz : (a : ℤ) ∣ ((D : ZMod (a * N)).val : ℤ) := by
    exact_mod_cast hdiv
  apply Int.ModEq.mul_left_cancel' ha
  rw [Int.natCast_ediv, Int.mul_ediv_cancel' hdivz, Int.mul_ediv_cancel' hD]
  simpa only [Nat.cast_mul] using val_modEq (a * N) D

/-- The power-modulus version of the preceding normalization identity. -/
theorem normalized_modEq_pow {p : ℕ} [NeZero p] (r k : ℕ) (D : ℤ)
    (hD : (p : ℤ) ^ r ∣ D) :
    (((D : ZMod (p ^ (r + k))).val / p ^ r : ℕ) : ℤ) ≡
      D / (p : ℤ) ^ r [ZMOD (p : ℤ) ^ k] := by
  have h := normalized_modEq_mul (a := p ^ r) (N := p ^ k) D
    (by simpa only [Nat.cast_pow] using hD)
  rw [pow_add]
  simpa only [Nat.cast_pow] using h

/-- The actual degree-r residue stratum is exactly the integer divisibility
condition p^r∣D, p^(r+1)∤D. -/
theorem exact_stratum_iff {p : ℕ} (hp : p.Prime) (r : ℕ) (D : ℤ) :
    p ^ r ∣ (D : ZMod (p ^ (r + 1))).val ∧
        (D : ZMod (p ^ (r + 1))).val ≠ 0 ↔
      (p : ℤ) ^ r ∣ D ∧ ¬ (p : ℤ) ^ (r + 1) ∣ D := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [divides_val_iff (pow_dvd_pow p (by omega)), val_ne_zero_iff]
  simp only [Nat.cast_pow]

/-- Dividing a residue by a known prime-power divisor gives the same residue
modulo p as dividing the integer discriminant itself. -/
theorem normalized_modEq {p : ℕ} (hp : p.Prime) (r : ℕ) (D : ℤ)
    (hD : (p : ℤ) ^ r ∣ D) :
    (((D : ZMod (p ^ (r + 1))).val / p ^ r : ℕ) : ℤ) ≡
      D / (p : ℤ) ^ r [ZMOD (p : ℤ)] := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdiv : p ^ r ∣ (D : ZMod (p ^ (r + 1))).val :=
    (divides_val_iff (pow_dvd_pow p (by omega)) D).mpr (by simpa using hD)
  have hdivz : (p : ℤ) ^ r ∣ ((D : ZMod (p ^ (r + 1))).val : ℤ) := by
    exact_mod_cast hdiv
  apply Int.ModEq.mul_left_cancel' (pow_ne_zero r hpz)
  rw [Int.natCast_ediv, Nat.cast_pow, Int.mul_ediv_cancel' hdivz,
    Int.mul_ediv_cancel' hD]
  simpa only [Nat.cast_pow, pow_succ, Nat.cast_mul] using val_modEq (p ^ (r + 1)) D

/-- The quadratic symbol of the actual normalized digit is independent of the
choice of integer representative. -/
theorem normalized_symbol {p : ℕ} (hp : p.Prime) (r : ℕ) (D : ℤ)
    (hD : (p : ℤ) ^ r ∣ D) :
    @legendreSym p ⟨hp⟩ (((D : ZMod (p ^ (r + 1))).val / p ^ r : ℕ) : ℤ) =
      @legendreSym p ⟨hp⟩ (D / (p : ℤ) ^ r) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := normalized_modEq hp r D hD
  change quadraticChar (ZMod p) _ = quadraticChar (ZMod p) _
  congr 1
  exact (ZMod.intCast_eq_intCast_iff _ _ p).mpr h

end DepthAspect.ResidueNormalization
