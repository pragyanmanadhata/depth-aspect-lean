import DepthAspect.OddAverageEuler
import DepthAspect.ArithmeticPrimeWeight
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The literal at-one value in (84)

The odd local rational factors are simplified at one, and their actual
convergent product is identified using the zeta Euler product and ζ(2)=π²/6.
The remaining product is exactly the arithmetic weight used in (106),
including the zero trace index. No local or global L-value is assumed.
-/
noncomputable section
open scoped BigOperators Classical Topology
namespace DepthAspect.OddEulerAtOne
open OddAverageEuler ArithmeticWeights

/-- The Euler factor of ζ(2), with the factor at two removed. -/
def oddZetaFactor (p : Nat.Primes) : ℂ :=
  if p.val = 2 then 1 else (1 - (p.val : ℂ)⁻¹ ^ 2)⁻¹

 theorem oddZeta_hasProd :
    HasProd oddZetaFactor ((Real.pi : ℂ) ^ 2 / 8) := by
  have hz := riemannZeta_eulerProduct_hasProd (s := (2 : ℂ)) (by norm_num)
  have htwo := hasProd_ite_eq (⟨2, Nat.prime_two⟩ : Nat.Primes) (3 / 4 : ℂ)
  have h := htwo.mul hz
  rw [riemannZeta_two] at h
  have hvalue : (3 / 4 : ℂ) * ((Real.pi : ℂ) ^ 2 / 6) =
      (Real.pi : ℂ) ^ 2 / 8 := by ring
  rw [hvalue] at h
  apply h.congr_fun
  intro p
  by_cases hp : p.val = 2
  · have heq : p = (⟨2, Nat.prime_two⟩ : Nat.Primes) := Subtype.ext hp
    subst p
    norm_num [oddZetaFactor, Complex.cpow_neg, Complex.cpow_two]
  · have heq : p ≠ (⟨2, Nat.prime_two⟩ : Nat.Primes) :=
      fun h => hp (congrArg Subtype.val h)
    simp only [oddZetaFactor, if_neg hp, if_neg heq, one_mul,
      Complex.cpow_neg, Complex.cpow_two, inv_pow]

/-- A single odd local factor at one splits into its zeta and arithmetic
parts; the condition is exactly that the prime does not divide 2t. -/
theorem localFactor_one (t : ℤ) (p : Nat.Primes) :
    localFactor t p 1 = oddZetaFactor p *
      (if ((p.val : ℕ) : ℤ) ∣ 2 * t then 1 else (baseFactor p.val : ℂ)) := by
  have hp0 : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hp1 : (p.val : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast p.property.ne_one)
  have hpR : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hpR0 : (0 : ℝ) < p.val := by linarith
  have hi : (p.val : ℝ)⁻¹ < 1 := (inv_lt_one₀ hpR0).mpr hpR
  have hi0 : 0 < (p.val : ℝ)⁻¹ := inv_pos.mpr hpR0
  have hden1 : (1 - (p.val : ℂ)⁻¹ ^ 2) ≠ 0 := by
    have hr : (1 - (p.val : ℝ)⁻¹ ^ 2) ≠ 0 := by nlinarith
    have hc := Complex.ofReal_ne_zero.mpr hr
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow,
      Complex.ofReal_inv, Complex.ofReal_natCast] using hc
  have hden2 : (p.val : ℂ) ^ 2 - (p.val : ℂ)⁻¹ ≠ 0 := by
    have hr : (p.val : ℝ) ^ 2 - (p.val : ℝ)⁻¹ ≠ 0 := by nlinarith
    have hc := Complex.ofReal_ne_zero.mpr hr
    simpa only [Complex.ofReal_sub, Complex.ofReal_pow,
      Complex.ofReal_inv, Complex.ofReal_natCast] using hc
  by_cases hp2 : p.val = 2
  · simp [localFactor, oddZetaFactor, hp2]
  have hpInt : Prime (p.val : ℤ) := Nat.prime_iff_prime_int.mp p.property
  have hnot2 : ¬ (p.val : ℤ) ∣ 2 := by
    intro hd
    have hdn : p.val ∣ 2 := by exact_mod_cast hd
    exact hp2 ((Nat.prime_two.dvd_iff_eq p.property.ne_one).mp hdn).symm
  have hdiv : (p.val : ℤ) ∣ 2 * t ↔ (p.val : ℤ) ∣ t := by
    rw [hpInt.dvd_mul, or_iff_right hnot2]
  have ht : (t : ZMod p.val) = 0 ↔ (p.val : ℤ) ∣ t := ZMod.intCast_zmod_eq_zero_iff_dvd t p.val
  simp only [localFactor, hp2, ↓reduceDIte, oddZetaFactor, ↓reduceIte,
    hdiv, ← ht, Complex.cpow_neg, Complex.cpow_one]
  by_cases hz : (t : ZMod p.val) = 0
  · simp [hz]
  · rw [if_neg hz, if_neg hz]
    rw [div_eq_iff (mul_ne_zero hden1 hden2)]
    have hcancel :
        (1 - (p.val : ℂ)⁻¹ ^ 2)⁻¹ * (baseFactor p.val : ℂ) *
          ((1 - (p.val : ℂ)⁻¹ ^ 2) * ((p.val : ℂ) ^ 2 - (p.val : ℂ)⁻¹)) =
        (baseFactor p.val : ℂ) * ((p.val : ℂ) ^ 2 - (p.val : ℂ)⁻¹) := by
      calc
        _ = ((1 - (p.val : ℂ)⁻¹ ^ 2)⁻¹ * (1 - (p.val : ℂ)⁻¹ ^ 2)) *
          ((baseFactor p.val : ℂ) * ((p.val : ℂ) ^ 2 - (p.val : ℂ)⁻¹)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hden1, one_mul]
    rw [hcancel]
    unfold baseFactor
    push_cast
    field_simp [hp0, hp1]
    ring

/-- The exact correction product at every integer trace, with convergence
proved by the arithmetic coefficient construction, including t=0. -/
theorem correction_hasProd (t : ℤ) :
    HasProd (fun p : Nat.Primes =>
      if (p.val : ℤ) ∣ 2 * t then (1 : ℂ) else (baseFactor p.val : ℂ))
      (integerPrimeWeight 2 t : ℂ) := by
  have hr : HasProd (fun p : Nat.Primes =>
      if p.val ∣ 2 * t.natAbs then (1 : ℝ) else baseFactor p.val)
      (primeWeight 2 t.natAbs) := by
    by_cases ht : t = 0
    · subst t
      simpa [primeWeight] using (hasProd_one : HasProd (fun _ : Nat.Primes => (1 : ℝ)) 1)
    · have h := primeWeight_hasProd Nat.prime_two (Int.natAbs_ne_zero.mpr ht)
      simpa only [primeWeight] using h.multipliable.hasProd
  have hc := hr.map Complex.ofRealHom Complex.continuous_ofReal
  apply hc.congr_fun
  intro p
  simp only [Function.comp_apply, Complex.ofRealHom_eq_coe]
  have hd : (p.val : ℤ) ∣ 2 * t ↔ p.val ∣ 2 * t.natAbs := by
    rw [Int.natCast_dvd, Int.natAbs_mul]
    norm_num
  by_cases hp : (p.val : ℤ) ∣ 2 * t
  · simp only [if_pos hp, if_pos (hd.mp hp), Complex.ofReal_one]
  · simp only [if_neg hp, if_neg (fun hn => hp (hd.mpr hn))]

/-- The full at-one value in (84), with the paper's literal arithmetic
prime product, and no exception for t=0. -/
theorem odd_series_at_one (t : ℤ) :
    LSeries (coefficient t) 1 =
      ((Real.pi : ℂ) ^ 2 / 8) * (integerPrimeWeight 2 t : ℂ) := by
  have h := oddZeta_hasProd.mul (correction_hasProd t)
  have hlocal := localFactor_hasProd t (s := (1 : ℂ)) (by norm_num)
  exact hlocal.unique (by simpa only [← localFactor_one] using h)

@[simp] theorem odd_series_at_one_zero :
    LSeries (coefficient 0) 1 = (Real.pi : ℂ) ^ 2 / 8 := by
  simp [odd_series_at_one]

/-- Multiplication by any power of two preserves the actual odd main term. -/
theorem odd_series_at_one_two_pow_mul (t : ℤ) (a : ℕ) :
    LSeries (coefficient ((2 : ℤ) ^ a * t)) 1 = LSeries (coefficient t) 1 := by
  have hw : integerPrimeWeight 2 ((2 : ℤ) ^ a * t) = integerPrimeWeight 2 t := by
    simpa only [Nat.cast_ofNat] using integerPrimeWeight_omitted_pow_mul 2 a t
  rw [odd_series_at_one, odd_series_at_one, hw]

end DepthAspect.OddEulerAtOne
