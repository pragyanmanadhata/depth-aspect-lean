import DepthAspect.ImprimitiveCharacter
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp

/-!
# Arithmetic input to the imprimitive Euler-factor identity

This module concerns the literal ψ(n)=χ(n/gcd(n,f)). Multiplicativity and
its values at prime powers are proved from gcd and factorization identities.
The global Euler product and continuation are separate analytic steps.
-/

open scoped BigOperators
namespace DepthAspect.ImprimitiveEuler

open ImprimitiveCharacter

@[simp] theorem psiNat_one {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ) :
    psiNat χ f 1 = 1 := by simp [psiNat_eq]

/-- The varying gcd still respects multiplication of coprime arguments. -/
theorem psiNat_mul_of_coprime {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f m n : ℕ) (hmn : Nat.Coprime m n) :
    psiNat χ f (m * n) = psiNat χ f m * psiNat χ f n := by
  rw [psiNat_eq, psiNat_eq, psiNat_eq]
  have hg : Nat.gcd (m * n) f = Nat.gcd m f * Nat.gcd n f := by
    rw [Nat.gcd_comm (m * n) f, Nat.Coprime.gcd_mul f hmn, Nat.gcd_comm f m, Nat.gcd_comm f n]
  rw [hg, Nat.mul_div_mul_comm (Nat.gcd_dvd_left m f) (Nat.gcd_dvd_left n f),
    Nat.cast_mul, map_mul]

/-- The exact gcd at a prime power, with its exponent obtained from the
actual natural-number factorization of the conductor. -/
theorem gcd_prime_power {p f : ℕ} (hp : p.Prime) (hf : f ≠ 0) (b : ℕ) :
    Nat.gcd (p ^ b) f = p ^ min b (f.factorization p) := by
  have hpow : p ^ b ≠ 0 := pow_ne_zero _ hp.ne_zero
  apply Nat.eq_of_factorization_eq
    (by intro h; exact hpow (Nat.gcd_eq_zero_iff.mp h).1) (pow_ne_zero _ hp.ne_zero)
  intro r
  rw [Nat.factorization_gcd hpow hf, hp.factorization_pow, hp.factorization_pow]
  simp only [Finsupp.inf_apply]
  by_cases hr : r = p
  · subst r
    simp
  · simp [Finsupp.single_apply, hr, Ne.symm hr]

/-- The prime-power assertion preceding (7). Natural subtraction is the
paper's max(b-e,0), and e is the actual exponent of p in f. -/
theorem psiNat_prime_power {q p f : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hf : f ≠ 0) (b : ℕ) :
    psiNat χ f (p ^ b) = χ (p : ZMod q) ^ (b - f.factorization p) := by
  rw [psiNat_eq, gcd_prime_power hp hf,
    Nat.pow_div (Nat.min_le_left _ _) hp.pos, Nat.cast_pow, map_pow]
  congr 1
  omega

/-- At a prime not dividing the conductor, ψ has the ordinary character
values at every prime power, so only the finite set of primes dividing f
can alter the Euler product. -/
theorem psiNat_prime_power_of_not_dvd {q p f : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hf : f ≠ 0) (hpf : ¬ p ∣ f) (b : ℕ) :
    psiNat χ f (p ^ b) = χ (p : ZMod q) ^ b := by
  rw [psiNat_prime_power χ hp hf]
  simp [Nat.factorization_eq_zero_of_not_dvd hpf]


/-- Multiplying the local coefficient sequence by 1-cX leaves exactly the
finite correction polynomial in (7). This is a coefficient identity, with no
analytic or formal-series existence assumption. -/
theorem localCoefficient_difference (c : ℂ) (e b : ℕ) :
    c ^ (b + 1 - e) - c * c ^ (b - e) =
      if b + 1 ≤ e then 1 - c else 0 := by
  split_ifs with hb
  · have h1 : b + 1 - e = 0 := by omega
    have h2 : b - e = 0 := by omega
    simp [h1, h2]
  · have he : b + 1 - e = (b - e) + 1 := by omega
    rw [he, pow_succ]
    ring

/-- The same finite correction identity for the actual imprimitive character,
with the conductor exponent read from its factorization. -/
theorem psiNat_prime_power_difference {q p f : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hf : f ≠ 0) (b : ℕ) :
    psiNat χ f (p ^ (b + 1)) - χ (p : ZMod q) * psiNat χ f (p ^ b) =
      if b + 1 ≤ f.factorization p then 1 - χ (p : ZMod q) else 0 := by
  rw [psiNat_prime_power χ hp hf, psiNat_prime_power χ hp hf]
  exact localCoefficient_difference (χ (p : ZMod q)) (f.factorization p) b

/-- Exact finite-polynomial algebra behind the geometric local factor. -/
theorem localCorrection_polynomial (c x : ℂ) (e : ℕ) :
    (1 - c * x) * (∑ b ∈ Finset.range (e + 1), x ^ b) + c * x ^ (e + 1) =
      1 + (1 - c) * ∑ j ∈ Finset.range e, x ^ (j + 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    simp only [Nat.succ_eq_add_one, Finset.sum_range_succ, pow_add, pow_one] at *
    linear_combination ih


/-- The actual local series converges to the correction polynomial divided by
the ordinary Euler denominator. Only geometric convergence is required. -/
theorem localFactor_hasSum (c x : ℂ) (e : ℕ) (hcx : ‖c * x‖ < 1) :
    HasSum (fun b : ℕ => c ^ (b - e) * x ^ b)
      ((1 + (1 - c) * ∑ j ∈ Finset.range e, x ^ (j + 1)) / (1 - c * x)) := by
  have htail : HasSum (fun b : ℕ => c ^ (b + e - e) * x ^ (b + e))
      (x ^ e * (1 - c * x)⁻¹) := by
    have hgeo := (hasSum_geometric_of_norm_lt_one hcx).mul_left (x ^ e)
    have heq : (fun b : ℕ => c ^ (b + e - e) * x ^ (b + e)) =
        (fun b : ℕ => x ^ e * (c * x) ^ b) := by
      funext b
      simp only [Nat.add_sub_cancel, pow_add, mul_pow]
      ring
    rw [heq]
    exact hgeo
  have hfull := (hasSum_nat_add_iff (f := fun b : ℕ => c ^ (b - e) * x ^ b) e).mp htail
  have hpre : (∑ b ∈ Finset.range e, c ^ (b - e) * x ^ b) =
      ∑ b ∈ Finset.range e, x ^ b := by
    apply Finset.sum_congr rfl
    intro b hb
    have hbe : b - e = 0 := by have := Finset.mem_range.mp hb; omega
    simp [hbe]
  rw [hpre] at hfull
  have hne : c * x ≠ 1 := by intro h; simp [h] at hcx
  have hden : 1 - c * x ≠ 0 := sub_ne_zero.mpr hne.symm
  have hpol := localCorrection_polynomial c x e
  rw [Finset.sum_range_succ, pow_succ] at hpol
  have heq : x ^ e * (1 - c * x)⁻¹ + ∑ b ∈ Finset.range e, x ^ b =
      (1 + (1 - c) * ∑ j ∈ Finset.range e, x ^ (j + 1)) / (1 - c * x) := by
    field_simp [hden]
    linear_combination hpol
  simpa only [heq] using hfull

/-- The local geometric identity for the literal imprimitive ψ coefficients. -/
theorem psiNat_localFactor_hasSum {q p f : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hf : f ≠ 0) (x : ℂ) (hx : ‖χ (p : ZMod q) * x‖ < 1) :
    HasSum (fun b : ℕ => psiNat χ f (p ^ b) * x ^ b)
      ((1 + (1 - χ (p : ZMod q)) *
          ∑ j ∈ Finset.range (f.factorization p), x ^ (j + 1)) /
        (1 - χ (p : ZMod q) * x)) := by
  simpa only [psiNat_prime_power χ hp hf] using
    localFactor_hasSum (χ (p : ZMod q)) x (f.factorization p) hx

end DepthAspect.ImprimitiveEuler
