import DepthAspect.OddSpecialFourier
import DepthAspect.OddCoefficientPeriodicity
import DepthAspect.FiniteCharacterTranslation

/-!
# The odd-prime Fourier estimate for t² − 8X, for every trace parameter

This is the standalone assertion following (95). Multiplication by two is a
permutation of the residue units at every odd prime, so replacing four by eight
preserves the literal Fourier norm. No two-adic restriction on t is needed.
The fundamental-discriminant identification is algebraic and applies to both
signs; the local coefficient also retains its already defined D = 0 convention.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.OddEightFourier
open FiniteCharacterFourier

variable {p : ℕ} [Fact p.Prime]

/-- The literal minus-eight local coefficient on units modulo p^(2j). -/
def localOnUnits (j : ℕ) (t : ℤ) (x : (ZMod (p ^ (2 * j)))ˣ) : ℂ :=
  OddDiscriminantValues.localCoefficient p
    (t ^ 2 - 8 * ((x : ZMod (p ^ (2 * j))).val : ℤ)) j

/-- Every integer representative gives the same literal local coefficient. -/
theorem localOnUnits_eq_coefficient (j : ℕ) (t : ℤ)
    (x : (ZMod (p ^ (2 * j)))ˣ) (X : ℤ)
    (hX : (X : ZMod (p ^ (2 * j))) = x) :
    localOnUnits j t x = OddDiscriminantValues.localCoefficient p (t ^ 2 - 8 * X) j := by
  unfold localOnUnits
  apply OddCoefficientPeriodicity.localCoefficient_eq_of_modEq
  have he : t ^ 2 - 8 * ((x : ZMod (p ^ (2 * j))).val : ℤ) ≡
      t ^ 2 - 8 * X [ZMOD ((p ^ (2 * j) : ℕ) : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, ZMod.natCast_zmod_val, hX]
  simpa only [Nat.cast_pow] using he

/-- The actual imprimitive coefficient for t²−8X, with arbitrary t and X.
The character data are the defining quadratic-symbol data, not a size bound. -/
theorem localOnUnits_eq_psi (hp2 : p ≠ 2) (j : ℕ) (t : ℤ)
    (x : (ZMod (p ^ (2 * j)))ˣ) (X : ℤ)
    (hX : (X : ZMod (p ^ (2 * j))) = x) {d : ℤ}
    (hd : FundamentalDiscriminant.IsFundamental d)
    (χ : OddDiscriminantValues.QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : t ^ 2 - 8 * X = d * (f : ℤ) ^ 2) :
    localOnUnits j t x = ImprimitiveCharacter.psiNat χ.character f (p ^ j) := by
  rw [localOnUnits_eq_coefficient j t x X hX, hD]
  exact (OddDiscriminantValues.psiNat_eq_localCoefficient hd χ (Fact.out : p.Prime)
    hp2 hf j).symm

/-- The unit represented by two, including the degree-zero modulus one. -/
def twoUnit (hp2 : p ≠ 2) (j : ℕ) : (ZMod (p ^ (2 * j)))ˣ :=
  ZMod.unitOfCoprime 2
    (((Fact.out : p.Prime).odd_of_ne_two hp2).coprime_two_left.pow_right (2 * j))

/-- The literal replacement of four by eight is translation on the unit group. -/
theorem localOnUnits_eq_translate (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) :
    localOnUnits (p := p) j t = fun x =>
      OddCoefficientFourier.localOnUnits j t (twoUnit hp2 j * x) := by
  funext x
  unfold localOnUnits OddCoefficientFourier.localOnUnits
  apply OddCoefficientPeriodicity.localCoefficient_eq_of_modEq
  have he : t ^ 2 - 8 * ((x : ZMod (p ^ (2 * j))).val : ℤ) ≡
      t ^ 2 - 4 * (((twoUnit hp2 j * x : (ZMod (p ^ (2 * j)))ˣ) :
        ZMod (p ^ (2 * j))).val : ℤ) [ZMOD ((p ^ (2 * j) : ℕ) : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, ZMod.natCast_zmod_val, Units.val_mul, twoUnit,
      ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
    ring
  simpa only [Nat.cast_pow] using he

/-- The principal coefficient is unchanged for every t, including t = 0. -/
theorem principal_coefficient (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) :
    coefficient (localOnUnits (p := p) j t) 1 =
      coefficient (OddCoefficientFourier.localOnUnits (p := p) j t) 1 := by
  rw [localOnUnits_eq_translate hp2 j t, FiniteCharacterTranslation.principal_translate]

/-- The entire Fourier L¹ norm is unchanged. -/
theorem beta_eq (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) :
    beta (localOnUnits (p := p) j t) =
      beta (OddCoefficientFourier.localOnUnits (p := p) j t) := by
  rw [localOnUnits_eq_translate hp2 j t, FiniteCharacterTranslation.beta_translate]

/-- The first bound in (95) after replacing four by eight, for arbitrary t. -/
theorem beta_localOnUnits (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) :
    beta (localOnUnits (p := p) j t) ≤ 1 + j * Real.sqrt p := by
  rw [beta_eq hp2 j t]
  exact OddCoefficientFourier.beta_localOnUnits hp2 j t

/-- The coarser bound in (95), including degree zero. -/
theorem beta_localOnUnits_le (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) :
    beta (localOnUnits (p := p) j t) ≤ (j + 1) * Real.sqrt p := by
  rw [beta_eq hp2 j t]
  exact OddCoefficientFourier.beta_localOnUnits_le hp2 j t

/-- Minus eight is a unit at every odd prime. -/
theorem neg_eight_unit (hp2 : p ≠ 2) : IsUnit (-8 : ZMod p) := by
  have h8 : IsUnit (8 : ZMod p) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hp8 : p ∣ (8 : ℕ) :=
      (ZMod.natCast_eq_zero_iff 8 p).mp (by simpa using hz)
    have hp2div : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
      (show p ∣ 2 ^ 3 by norm_num; exact hp8)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp2div)
  exact h8.neg

/-- When p divides t, the actual coefficient is χ_p(−8)^j times an inflated
quadratic character. This assertion has no two-adic hypothesis on t. -/
theorem localOnUnits_eq_character (hp2 : p ≠ 2) {j : ℕ} (hj : 0 < j)
    {t : ℤ} (ht : (p : ℤ) ∣ t) (x : (ZMod (p ^ (2 * j)))ˣ) :
    localOnUnits (p := p) j t x =
      OddSpecialFourier.quadratic (p := p) (-8) ^ j *
        (((OddSpecialFourier.quadratic (p := p)).changeLevel
          (by simpa only [pow_one] using pow_dvd_pow p (by omega : 1 ≤ 2 * j))) ^ j) x := by
  let hdiv : p ∣ p ^ (2 * j) := by
    simpa only [pow_one] using pow_dvd_pow p (by omega : 1 ≤ 2 * j)
  let y : (ZMod p)ˣ := ZMod.unitsMap hdiv x
  let X : ℤ := (x : ZMod (p ^ (2 * j))).val
  have hX : (X : ZMod p) = y := by
    simp only [X, y, ZMod.unitsMap_val, Int.cast_natCast, ZMod.cast_eq_val]
  have ht0 : (t : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mpr ht
  have hD : ((t ^ 2 - 8 * X : ℤ) : ZMod p) = (-8 : ZMod p) * y := by
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, ht0, hX]
    ring
  have hn : ¬ (p : ℤ) ∣ t ^ 2 - 8 * X := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hD]
    exact ((neg_eight_unit hp2).mul y.isUnit).ne_zero
  have htheta : ((OddSpecialFourier.quadratic (p := p)).changeLevel hdiv) x =
      OddSpecialFourier.quadratic (p := p) y := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    rfl
  change OddDiscriminantValues.localCoefficient p (t ^ 2 - 8 * X) j = _
  rw [LocalValueRecursion.localCoefficient_of_not_dvd hn]
  change OddSpecialFourier.quadratic (p := p) ((t ^ 2 - 8 * X : ℤ) : ZMod p) ^ j = _
  rw [hD, map_mul, mul_pow, MulChar.pow_apply_coe, htheta]

/-- The exact p∣t refinement following (95), also valid at j = 0. -/
theorem beta_localOnUnits_eq_one (hp2 : p ≠ 2) (j : ℕ) {t : ℤ}
    (ht : (p : ℤ) ∣ t) : beta (localOnUnits (p := p) j t) = 1 := by
  rw [beta_eq hp2 j t]
  exact OddSpecialFourier.beta_localOnUnits_eq_one hp2 j ht

end DepthAspect.OddEightFourier
