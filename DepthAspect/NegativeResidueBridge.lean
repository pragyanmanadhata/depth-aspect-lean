import DepthAspect.GlobalResidueMean
import DepthAspect.QuadraticDiscriminantL
import DepthAspect.CharacterPrimeAverages
import Mathlib.Data.Nat.GCD.Prime

/-!
# Identifying the periodic residue function at the actual prime discriminants

The negative-discriminant character is selected by the proved fundamental
factorization. This module connects that literal ψ to the periodic function
used in the character expansion. The bad primes are exactly those dividing
2m; no equality with an arbitrarily extended character function is assumed.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.NegativeResidueBridge
open GlobalResidueCoefficient GlobalResidueMean QuadraticClassFormula
open QuadraticDiscriminantL CharacterPrimeAverages

 theorem prime_dvd_modulus_iff (m : ℕ) {p : ℕ} (hp : p.Prime) :
    p ∣ modulus m ↔ p = 2 ∨ p ∣ m := by
  rw [modulus, hp.dvd_lcm]
  have h8 : p ∣ 8 ↔ p = 2 := by
    change p ∣ 2 ^ 3 ↔ p = 2
    rw [hp.prime.dvd_pow_iff_dvd (by decide : (3 : ℕ) ≠ 0),
      Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
  rw [h8, hp.prime.dvd_pow_iff_dvd (by decide : (2 : ℕ) ≠ 0)]

 theorem prime_coprime_modulus (m : ℕ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpm : ¬p ∣ m) : p.Coprime (modulus m) := by
  rw [hp.coprime_iff_not_dvd, prime_dvd_modulus_iff m hp]
  exact not_or.mpr ⟨hp2, hpm⟩

 theorem coefficient_eq_negative_psi {H : ℤ → ℝ} (G : GeneralFormula H)
    {m : ℕ} (hm : m ≠ 0) (t X : ℤ) (hX : Odd X)
    (hD : IsNegativeDiscriminant (t ^ 2 - 4 * X))
    (x : (ZMod (modulus m))ˣ) (hx : (X : ZMod (modulus m)) = x) :
    coefficientFunction m t x = psi G (t ^ 2 - 4 * X) m := by
  rw [psi, dif_pos hD]
  exact coefficientFunction_eq_psi hm t X hX x hx
    (datum _ hD).fundamental_shape
    (G.quadratic _ (datum _ hD).fundamental_shape (datum _ hD).fundamental_neg)
    (datum _ hD).conductor_pos.ne' (datum _ hD).factorization

/-- For every counted good prime, the actual periodic function used in the
Fourier expansion equals the literal character-twisted ψ from the prime sum. -/
theorem twistedFunction_good_prime {H : ℤ → ℝ} (G : GeneralFormula H)
    {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬p ∣ m)
    (t : ℤ) (χ : DirichletCharacter ℂ 8)
    (hD : IsNegativeDiscriminant (t ^ 2 - 4 * (p : ℤ))) :
    twistedFunction m t χ (ZMod.unitOfCoprime p (prime_coprime_modulus m hp hp2 hpm)) =
      χ (-(p : ℤ)) * psi G (t ^ 2 - 4 * (p : ℤ)) m := by
  have hodd : Odd (p : ℤ) := by exact_mod_cast hp.odd_of_ne_two hp2
  have hx : ((p : ℤ) : ZMod (modulus m)) =
      (ZMod.unitOfCoprime p (prime_coprime_modulus m hp hp2 hpm) : ZMod (modulus m)) := by
    simp
  rw [twistedFunction, coefficient_eq_negative_psi G hm t p hodd hD _ hx]
  congr 1
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  simp only [ZMod.coe_unitOfCoprime, Int.cast_neg, Int.cast_natCast]
  calc
    _ = χ (-1) * χ (p : ZMod 8) :=
      congrArg (fun z : ZMod 8 => χ (-1) * χ z)
        (ZMod.cast_natCast (Nat.dvd_lcm_left 8 (m ^ 2)) p)
    _ = _ := by
      simpa only [neg_one_mul] using (map_mul χ (-1) (p : ZMod 8)).symm

/-- The nonunit-zero extension required by the character expansion removes
exactly the primes dividing 2m, and agrees with ψ on the remaining primes. -/
theorem extend_twisted_good_prime {H : ℤ → ℝ} (G : GeneralFormula H)
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬p ∣ m)
    (t : ℤ) (χ : DirichletCharacter ℂ 8)
    (hD : IsNegativeDiscriminant (t ^ 2 - 4 * (p : ℤ))) :
    extend (twistedFunction m t χ) (p : ZMod (modulus m)) =
      χ (-(p : ℤ)) * psi G (t ^ 2 - 4 * (p : ℤ)) m := by
  let x := ZMod.unitOfCoprime p (prime_coprime_modulus m hp hp2 hpm)
  have hx : (x : ZMod (modulus m)) = p := by simp [x]
  rw [← hx]
  have he : extend (twistedFunction m t χ) (x : ZMod (modulus m)) =
      twistedFunction m t χ x := by
    unfold extend
    rw [dif_pos x.isUnit]
    congr 1
    exact Units.ext x.isUnit.unit_spec
  rw [he]
  exact twistedFunction_good_prime G (NeZero.ne m) hp hp2 hpm t χ hD

end DepthAspect.NegativeResidueBridge
