import DepthAspect.OddCoefficientFourier
import DepthAspect.LocalValueRecursion

/-! The sharper odd Fourier statement following (95): beta=1 when p divides t. -/
noncomputable section
open scoped BigOperators
namespace DepthAspect.OddSpecialFourier
open OddCoefficientFourier FiniteCharacterFourier
variable {p : ℕ} [Fact p.Prime]

/-- The literal complex-valued quadratic Dirichlet character modulo p. -/
def quadratic : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

 theorem neg_four_unit (hp2 : p ≠ 2) : IsUnit (-4 : ZMod p) := by
  have h4 : IsUnit (4 : ZMod p) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hp4 : p ∣ (4 : ℕ) :=
      (ZMod.natCast_eq_zero_iff 4 p).mp (by simpa using hz)
    have hp2div : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
      (show p ∣ 2 ^ 2 by norm_num; exact hp4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp2div)
  exact h4.neg

/-- Divisibility of the trace parameter turns the actual discriminant
coefficient into a constant of norm one times an inflated character. -/
theorem localOnUnits_eq_character (hp2 : p ≠ 2) {j : ℕ} (hj : 0 < j)
    {t : ℤ} (ht : (p : ℤ) ∣ t) (x : (ZMod (p ^ (2 * j)))ˣ) :
    localOnUnits (p := p) j t x =
      quadratic (p := p) (-4) ^ j *
        (((quadratic (p := p)).changeLevel
          (by simpa only [pow_one] using pow_dvd_pow p (by omega : 1 ≤ 2 * j))) ^ j) x := by
  let hdiv : p ∣ p ^ (2 * j) := by
    simpa only [pow_one] using pow_dvd_pow p (by omega : 1 ≤ 2 * j)
  let y : (ZMod p)ˣ := ZMod.unitsMap hdiv x
  let X : ℤ := (x : ZMod (p ^ (2 * j))).val
  have hX : (X : ZMod p) = y := by
    simp only [X, y, ZMod.unitsMap_val, Int.cast_natCast, ZMod.cast_eq_val]
  have ht0 : (t : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mpr ht
  have hD : ((t ^ 2 - 4 * X : ℤ) : ZMod p) = (-4 : ZMod p) * y := by
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, ht0, hX]
    ring
  have hn : ¬ (p : ℤ) ∣ t ^ 2 - 4 * X := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hD]
    exact ((neg_four_unit hp2).mul y.isUnit).ne_zero
  have htheta : ((quadratic (p := p)).changeLevel hdiv) x = quadratic (p := p) y := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    rfl
  change OddDiscriminantValues.localCoefficient p (t ^ 2 - 4 * X) j = _
  rw [LocalValueRecursion.localCoefficient_of_not_dvd hn]
  change quadratic (p := p) ((t ^ 2 - 4 * X : ℤ) : ZMod p) ^ j = _
  rw [hD, map_mul, mul_pow, MulChar.pow_apply_coe, htheta]

/-- The exact sharper Fourier norm asserted after (95), including degree zero. -/
theorem beta_localOnUnits_eq_one (hp2 : p ≠ 2) (j : ℕ) {t : ℤ}
    (ht : (p : ℤ) ∣ t) : beta (localOnUnits (p := p) j t) = 1 := by
  by_cases hj : j = 0
  · subst j
    have he : localOnUnits (p := p) 0 t =
        fun x : (ZMod (p ^ (2 * 0)))ˣ =>
          (1 : DirichletCharacter ℂ (p ^ (2 * 0))) x := by
      funext x
      rw [MulChar.one_apply_coe]
      simp [localOnUnits, OddDiscriminantValues.localCoefficient]
    rw [he, beta_character]
  · have hj0 : 0 < j := Nat.pos_of_ne_zero hj
    have he : localOnUnits (p := p) j t = fun x : (ZMod (p ^ (2 * j)))ˣ =>
        quadratic (p := p) (-4) ^ j *
          (((quadratic (p := p)).changeLevel
            (by simpa only [pow_one] using pow_dvd_pow p (by omega : 1 ≤ 2 * j))) ^ j) x := by
      funext x
      exact localOnUnits_eq_character hp2 hj0 ht x
    have hnorm : ‖quadratic (p := p) (-4)‖ = 1 := by
      have hu := neg_four_unit (p := p) hp2
      simpa only [hu.unit_spec] using (quadratic (p := p)).unit_norm_eq_one hu.unit
    rw [he, beta_const_mul, norm_pow, hnorm, one_pow, beta_character, mul_one]

end DepthAspect.OddSpecialFourier
