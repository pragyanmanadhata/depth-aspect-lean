import DepthAspect.OddResidueFourier
import DepthAspect.OddDiscriminantValues
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# The odd-prime coefficient Fourier estimate

The coefficient function below is the actual normalized-discriminant formula
already identified with ψ. Its stratum decomposition and coefficient-norm
bound are proved through literal reduction maps between residue rings.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.OddCoefficientFourier
open OddResidueFourier FiniteCharacterFourier

variable {p : ℕ} [Fact p.Prime]

/-- The actual local coefficient on the reduced residue classes modulo p^(2j). -/
def localOnUnits (j : ℕ) (t : ℤ) (x : (ZMod (p ^ (2 * j)))ˣ) : ℂ :=
  OddDiscriminantValues.localCoefficient p
    (t ^ 2 - 4 * ((x : ZMod (p ^ (2 * j))).val : ℤ)) j

/-- Identification with the actual imprimitive coefficient at any residue
whose discriminant is supplied in its defining fundamental form. -/
theorem localOnUnits_eq_psi (hp2 : p ≠ 2) (j : ℕ) (t : ℤ)
    (x : (ZMod (p ^ (2 * j)))ˣ) {d : ℤ}
    (hd : FundamentalDiscriminant.IsFundamental d)
    (χ : OddDiscriminantValues.QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : t ^ 2 - 4 * ((x : ZMod (p ^ (2 * j))).val : ℤ) = d * (f : ℤ) ^ 2) :
    localOnUnits j t x = ImprimitiveCharacter.psiNat χ.character f (p ^ j) := by
  rw [localOnUnits, hD]
  exact (OddDiscriminantValues.psiNat_eq_localCoefficient hd χ (Fact.out : p.Prime)
    hp2 hf j).symm

private theorem lower_dvd (j : ℕ) (e : Fin j) : p ^ (2 * (e : ℕ) + 1) ∣ p ^ (2 * j) :=
  pow_dvd_pow p (by have := e.isLt; omega)

/-- The actual e-th stratum inflated by the canonical reduction of units. -/
def inflatedStratum (j : ℕ) (t : ℤ) (e : Fin j) (x : (ZMod (p ^ (2 * j)))ˣ) : ℂ :=
  stratum (e : ℕ) j t (ZMod.unitsMap (lower_dvd j e) x)

 theorem inflatedStratum_eq (j : ℕ) (t : ℤ) (e : Fin j)
    (x : (ZMod (p ^ (2 * j)))ˣ) :
    inflatedStratum j t e x =
      if (p : ℤ) ^ (2 * (e : ℕ)) ∣ t ^ 2 - 4 * ((x : ZMod (p ^ (2 * j))).val : ℤ) ∧
          ¬ (p : ℤ) ^ (2 * (e : ℕ) + 1) ∣
            t ^ 2 - 4 * ((x : ZMod (p ^ (2 * j))).val : ℤ) then
        (legendreSym p ((t ^ 2 - 4 * ((x : ZMod (p ^ (2 * j))).val : ℤ)) /
          (p : ℤ) ^ (2 * (e : ℕ))) : ℂ) ^ (j - e)
      else 0 := by
  apply stratum_eq_of_intCast
  simp only [Int.cast_natCast, ZMod.unitsMap_val, ZMod.cast_eq_val]

 theorem divisibleTerm_eq (j : ℕ) (t : ℤ) (x : (ZMod (p ^ (2 * j)))ˣ) :
    divisibleTerm (2 * j) t x =
      if (p : ℤ) ^ (2 * j) ∣ t ^ 2 - 4 * ((x : ZMod (p ^ (2 * j))).val : ℤ) then
        1 else 0 := by
  have hD : discriminant (2 * j) t x =
      ((t ^ 2 - 4 * ((x : ZMod (p ^ (2 * j))).val : ℤ) : ℤ) : ZMod (p ^ (2 * j))) := by
    simp only [discriminant, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [divisibleTerm, hD, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]

/-- The actual character function satisfies exactly (94) on its claimed modulus. -/
theorem localOnUnits_strata (j : ℕ) (t : ℤ) :
    localOnUnits (p := p) j t = fun x =>
      divisibleTerm (2 * j) t x + ∑ e : Fin j, inflatedStratum j t e x := by
  funext x
  rw [localOnUnits, OddDiscriminantValues.localCoefficient_strata, divisibleTerm_eq]
  congr 1
  simp_rw [inflatedStratum_eq]
  exact Finset.sum_range _

 theorem beta_inflatedStratum (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) (e : Fin j) :
    beta (inflatedStratum (p := p) j t e) ≤ Real.sqrt p := by
  unfold inflatedStratum
  rw [beta_inflation]
  exact beta_stratum hp2 (e : ℕ) j t

/-- The first inequality in (95), now for the actual coefficient function. -/
theorem beta_localOnUnits (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) :
    beta (localOnUnits (p := p) j t) ≤ 1 + j * Real.sqrt p := by
  by_cases hj : j = 0
  · subst j
    have hg : localOnUnits (p := p) 0 t = fun x : (ZMod (p ^ (2 * 0)))ˣ =>
        (1 : DirichletCharacter ℂ (p ^ (2 * 0))) (x : ZMod (p ^ (2 * 0))) := by
      funext x
      rw [MulChar.one_apply_coe]
      simp [localOnUnits, OddDiscriminantValues.localCoefficient]
    rw [hg, beta_character]
    simp
  · rw [localOnUnits_strata]
    calc
      _ ≤ beta (divisibleTerm (p := p) (2 * j) t) +
          beta (fun x => ∑ e : Fin j, inflatedStratum j t e x) :=
        beta_add _ _
      _ ≤ 1 + ∑ e : Fin j, beta (inflatedStratum j t e) := by
        exact add_le_add (beta_divisibleTerm hp2 (by omega) t) (beta_sum Finset.univ _)
      _ ≤ 1 + ∑ e : Fin j, Real.sqrt p := by
        gcongr with e
        exact beta_inflatedStratum hp2 j t e
      _ = _ := by simp

/-- The convenient square-root-prime majorant in (95). -/
theorem beta_localOnUnits_le (hp2 : p ≠ 2) (j : ℕ) (t : ℤ) :
    beta (localOnUnits (p := p) j t) ≤ (j + 1) * Real.sqrt p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hs : 1 ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by simpa using hp1)
  exact (beta_localOnUnits hp2 j t).trans (by nlinarith)

end DepthAspect.OddCoefficientFourier
