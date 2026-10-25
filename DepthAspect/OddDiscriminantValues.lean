import DepthAspect.ImprimitiveEuler
import DepthAspect.FundamentalDiscriminant
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Actual imprimitive coefficients and odd-prime discriminant valuations

The only character-identification interface is the defining quadratic-character
value at a prime. All conductor exponents, normalized discriminants, and local
coefficient cases are derived below from the literal `psiNat` definition.
-/

open scoped BigOperators

namespace DepthAspect.OddDiscriminantValues

open ImprimitiveCharacter ImprimitiveEuler FundamentalDiscriminant

/-- Defining quadratic-character data. This does not assume a local coefficient
formula, a residue mean, or a Fourier estimate. -/
structure QuadraticCharacterData (d : ℤ) where
  character : DirichletCharacter ℂ d.natAbs
  odd_prime_value : ∀ (p : ℕ) (hp : p.Prime), p ≠ 2 →
    character (p : ZMod d.natAbs) = (@legendreSym p ⟨hp⟩ d : ℂ)
  two_value : character (2 : ZMod d.natAbs) = (twoSymbol d : ℂ)

/-- The complement of the actual conductor prime power is prime to `p`. -/
theorem conductor_decomposition {p f : ℕ} (hp : p.Prime) (hf : f ≠ 0) :
    f = p ^ f.factorization p * (ordCompl[p] f) ∧ ¬ p ∣ (ordCompl[p] f) := by
  constructor
  · simpa only using (Nat.ordProj_mul_ordCompl_eq_self f p).symm
  · exact Nat.not_dvd_ordCompl hp hf

/-- Factoring the actual discriminant gives its exact odd-prime exponent. -/
theorem discriminant_factorization {d : ℤ} (hd : d ≠ 0) {f : ℕ} (hf : f ≠ 0)
    (p : ℕ) :
    (d * (f : ℤ) ^ 2).natAbs.factorization p =
      d.natAbs.factorization p + 2 * f.factorization p := by
  have hda : d.natAbs ≠ 0 := by simpa using hd
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
    Nat.factorization_mul hda (pow_ne_zero 2 hf), Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Dividing by the square of the conductor's `p` part leaves exactly the
fundamental discriminant times a square prime to `p`. -/
theorem normalized_discriminant {p f : ℕ} (hp : p.Prime) (hf : f ≠ 0) (d : ℤ) :
    d * (f : ℤ) ^ 2 / (p : ℤ) ^ (2 * f.factorization p) =
      d * ((ordCompl[p] f : ℕ) : ℤ) ^ 2 := by
  have hfac := (conductor_decomposition hp hf).1
  have hcast : (f : ℤ) = (p : ℤ) ^ f.factorization p * ((ordCompl[p] f : ℕ) : ℤ) := by
    exact_mod_cast hfac
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  conv_lhs => rw [hcast]
  have heq : d * ((p : ℤ) ^ f.factorization p * ((ordCompl[p] f : ℕ) : ℤ)) ^ 2 =
      (d * ((ordCompl[p] f : ℕ) : ℤ) ^ 2) * (p : ℤ) ^ (2 * f.factorization p) := by
    rw [mul_comm 2 (f.factorization p), pow_mul]
    ring
  rw [heq, Int.mul_ediv_cancel _ (pow_ne_zero _ hpz)]

/-- Removing the conductor square does not change the quadratic symbol. -/
theorem normalized_symbol {p f : ℕ} (hp : p.Prime) (hf : f ≠ 0) (d : ℤ) :
    @legendreSym p ⟨hp⟩ (d * (f : ℤ) ^ 2 / (p : ℤ) ^ (2 * f.factorization p)) =
      @legendreSym p ⟨hp⟩ d := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [normalized_discriminant hp hf, legendreSym.mul]
  have hunit : (((ordCompl[p] f : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply (conductor_decomposition hp hf).2
    apply (ZMod.natCast_eq_zero_iff (ordCompl[p] f : ℕ) p).mp
    exact_mod_cast hz
  rw [legendreSym.sq_one' p hunit, mul_one]

/-- A prime divides an integer exactly when its quadratic symbol vanishes. -/
theorem symbol_eq_zero_iff_dvd {p : ℕ} (hp : p.Prime) (d : ℤ) :
    @legendreSym p ⟨hp⟩ d = 0 ↔ (p : ℤ) ∣ d := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [legendreSym.eq_zero_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The actual discriminant determines the conductor exponent at odd primes. -/
theorem conductor_exponent_from_discriminant {d : ℤ} (hd : IsFundamental d)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : f ≠ 0) :
    (d * (f : ℤ) ^ 2).natAbs.factorization p / 2 = f.factorization p ∧
    (d * (f : ℤ) ^ 2).natAbs.factorization p % 2 = d.natAbs.factorization p := by
  rw [discriminant_factorization hd.ne_zero hf]
  have h := hd.odd_prime_factorization_le_one hp hp2
  omega

/-- This formula uses only the actual valuation and normalized integer
residue of `D`; its equivalence with `psiNat` is proved below. -/
noncomputable def localCoefficient (p : ℕ) [Fact p.Prime] (D : ℤ) (b : ℕ) : ℂ :=
  if D = 0 then 1 else
  let e := D.natAbs.factorization p / 2
  if b ≤ e then 1 else if D.natAbs.factorization p % 2 = 0 then
    (legendreSym p (D / (p : ℤ) ^ (2 * e)) : ℂ) ^ (b - e)
  else 0

@[simp] theorem localCoefficient_zero (p : ℕ) [Fact p.Prime] (b : ℕ) :
    localCoefficient p 0 b = 1 := by simp [localCoefficient]

private theorem pow_dvd_iff_valuation {p : ℕ} (hp : p.Prime) {D : ℤ}
    (hD : D ≠ 0) (a : ℕ) :
    (p : ℤ) ^ a ∣ D ↔ a ≤ D.natAbs.factorization p := by
  have hDa : D.natAbs ≠ 0 := by simpa using hD
  rw [← Nat.cast_pow, Int.natCast_dvd, hp.pow_dvd_iff_le_factorization hDa]

/-- The exact finite stratum expansion (94), including the convention at zero.
The residue-class dependence is a separate arithmetic consequence. -/
theorem localCoefficient_strata (p : ℕ) [Fact p.Prime] (D : ℤ) (b : ℕ) :
    localCoefficient p D b =
      (if (p : ℤ) ^ (2 * b) ∣ D then 1 else 0) +
      ∑ e ∈ Finset.range b,
        if (p : ℤ) ^ (2 * e) ∣ D ∧ ¬ (p : ℤ) ^ (2 * e + 1) ∣ D then
          (legendreSym p (D / (p : ℤ) ^ (2 * e)) : ℂ) ^ (b - e)
        else 0 := by
  classical
  by_cases hD : D = 0
  · simp [hD]
  have hp : p.Prime := Fact.out
  simp only [localCoefficient, if_neg hD, pow_dvd_iff_valuation hp hD]
  let v := D.natAbs.factorization p
  change (if b ≤ v / 2 then (1 : ℂ) else if v % 2 = 0 then
      (legendreSym p (D / (p : ℤ) ^ (2 * (v / 2))) : ℂ) ^ (b - v / 2) else 0) =
    (if 2 * b ≤ v then 1 else 0) + ∑ e ∈ Finset.range b,
      if 2 * e ≤ v ∧ ¬ 2 * e + 1 ≤ v then
        (legendreSym p (D / (p : ℤ) ^ (2 * e)) : ℂ) ^ (b - e) else 0
  by_cases hb : b ≤ v / 2
  · have hvb : 2 * b ≤ v := by omega
    rw [if_pos hb, if_pos hvb]
    have hz : (∑ e ∈ Finset.range b,
        if 2 * e ≤ v ∧ ¬ 2 * e + 1 ≤ v then
          (legendreSym p (D / (p : ℤ) ^ (2 * e)) : ℂ) ^ (b - e) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have heb := Finset.mem_range.mp he
      rw [if_neg (by omega)]
    rw [hz, add_zero]
  · have hvb : ¬ 2 * b ≤ v := by omega
    rw [if_neg hb, if_neg hvb, zero_add]
    by_cases hv : v % 2 = 0
    · rw [if_pos hv]
      symm
      rw [Finset.sum_eq_single (v / 2)]
      · rw [if_pos (by omega)]
      · intro e he hne
        rw [if_neg (by omega)]
      · intro he
        exact (he (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg hv]
      symm
      apply Finset.sum_eq_zero
      intro e he
      rw [if_neg (by omega)]

/-- The normalized valuation formula for the literal imprimitive character,
with ramification derived from fundamental-discriminant squarefreeness. -/
theorem psiNat_eq_localCoefficient {d : ℤ} (hd : IsFundamental d)
    (χ : QuadraticCharacterData d) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f ≠ 0) (b : ℕ) :
    psiNat χ.character f (p ^ b) =
      @localCoefficient p ⟨hp⟩ (d * (f : ℤ) ^ 2) b := by
  letI : Fact p.Prime := ⟨hp⟩
  have he := conductor_exponent_from_discriminant hd hp hp2 hf
  have hD : d * (f : ℤ) ^ 2 ≠ 0 := by
    exact mul_ne_zero hd.ne_zero (pow_ne_zero 2 (by exact_mod_cast hf))
  rw [psiNat_prime_power χ.character hp hf, χ.odd_prime_value p hp hp2]
  simp only [localCoefficient, if_neg hD, he.1, he.2]
  by_cases hb : b ≤ f.factorization p
  · simp [hb, Nat.sub_eq_zero_of_le hb]
  · rw [if_neg hb]
    by_cases hdv : d.natAbs.factorization p = 0
    · rw [if_pos hdv, normalized_symbol hp hf]
    · rw [if_neg hdv]
      have hdabs : d.natAbs ≠ 0 := by simpa using hd.ne_zero
      have hpd : p ∣ d.natAbs :=
        (hp.dvd_iff_one_le_factorization hdabs).mpr (Nat.one_le_iff_ne_zero.mpr hdv)
      have hs : legendreSym p d = 0 :=
        (symbol_eq_zero_iff_dvd hp d).mpr (Int.natCast_dvd.mpr hpd)
      simp only [hs, Int.cast_zero]
      exact zero_pow (by omega)

/-- The coefficient is one exactly in the valuation range used for the
terminal divisible stratum in (94). -/
theorem psiNat_eq_one_of_square_power_dvd {d : ℤ} (hd : IsFundamental d)
    (χ : QuadraticCharacterData d) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f ≠ 0) (b : ℕ)
    (hdiv : (p : ℤ) ^ (2 * b) ∣ d * (f : ℤ) ^ 2) :
    psiNat χ.character f (p ^ b) = 1 := by
  have hD : (d * (f : ℤ) ^ 2).natAbs ≠ 0 := by
    have hfz : (f : ℤ) ≠ 0 := by exact_mod_cast hf
    simpa using mul_ne_zero hd.ne_zero (pow_ne_zero 2 hfz)
  have hv : 2 * b ≤ (d * (f : ℤ) ^ 2).natAbs.factorization p := by
    apply (hp.pow_dvd_iff_le_factorization hD).mp
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_pow] using hdiv
  have he := conductor_exponent_from_discriminant hd hp hp2 hf
  have hbe : b ≤ f.factorization p := by omega
  rw [psiNat_prime_power χ.character hp hf]
  simp [Nat.sub_eq_zero_of_le hbe]

end DepthAspect.OddDiscriminantValues
