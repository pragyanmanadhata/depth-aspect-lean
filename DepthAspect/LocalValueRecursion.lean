import DepthAspect.OddDiscriminantValues
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The residue recursion of the literal local discriminant coefficients

These are arithmetic identities for `OddDiscriminantValues.localCoefficient`,
which has already been identified with the globally defined ψ at odd primes.
They are the bridge from the paired-digit averaging calculation to that actual
coefficient, so no independently defined local mean is taken as an input.
-/
noncomputable section
namespace DepthAspect.LocalValueRecursion
open OddDiscriminantValues

variable {p : ℕ} [Fact p.Prime]

@[simp] theorem localCoefficient_degree_zero (D : ℤ) : localCoefficient p D 0 = 1 := by
  simp [localCoefficient]

theorem factorization_mul_prime_square {D : ℤ} (hD : D ≠ 0) :
    ((p : ℤ) ^ 2 * D).natAbs.factorization p = 2 + D.natAbs.factorization p := by
  have hp : p.Prime := Fact.out
  have hDa : D.natAbs ≠ 0 := by simpa using hD
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast,
    Nat.factorization_mul (pow_ne_zero 2 hp.ne_zero) hDa,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization_self, mul_one]

/-- Removing two leading zero base-p digits lowers the degree by one. -/
theorem localCoefficient_mul_square (D : ℤ) (b : ℕ) :
    localCoefficient p ((p : ℤ) ^ 2 * D) (b + 1) = localCoefficient p D b := by
  by_cases hD : D = 0
  · simp [hD]
  have hp : p.Prime := Fact.out
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hprod : (p : ℤ) ^ 2 * D ≠ 0 := mul_ne_zero (pow_ne_zero 2 hpz) hD
  have hv := factorization_mul_prime_square (p := p) hD
  have he : (2 + D.natAbs.factorization p) / 2 = D.natAbs.factorization p / 2 + 1 := by omega
  have hr : (2 + D.natAbs.factorization p) % 2 = D.natAbs.factorization p % 2 := by omega
  have hnorm : (p : ℤ) ^ 2 * D /
      (p : ℤ) ^ (2 * (D.natAbs.factorization p / 2 + 1)) =
        D / (p : ℤ) ^ (2 * (D.natAbs.factorization p / 2)) := by
    rw [show 2 * (D.natAbs.factorization p / 2 + 1) =
      2 + 2 * (D.natAbs.factorization p / 2) by omega, pow_add,
      ← Int.ediv_ediv_of_nonneg (sq_nonneg (p : ℤ)),
      Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hpz)]
  simp only [localCoefficient, if_neg hD, if_neg hprod, hv, he, hr, hnorm,
    Nat.add_le_add_iff_right, Nat.add_sub_add_right]

/-- A unit discriminant has exactly its quadratic-symbol power as coefficient. -/
theorem localCoefficient_of_not_dvd {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) (b : ℕ) :
    localCoefficient p D b = (legendreSym p D : ℂ) ^ b := by
  have hp : p.Prime := Fact.out
  have hDz : D ≠ 0 := by intro h; exact hD (h ▸ dvd_zero _)
  have hv : D.natAbs.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h; exact hD (Int.natCast_dvd.mpr h))
  cases b with
  | zero => simp
  | succ b => simp [localCoefficient, hDz, hv]

/-- Exactly one leading zero digit is the ramified, vanishing case. -/
theorem localCoefficient_of_one_dvd {D : ℤ} (hD : (p : ℤ) ∣ D)
    (hD2 : ¬ (p : ℤ) ^ 2 ∣ D) {b : ℕ} (hb : 0 < b) : localCoefficient p D b = 0 := by
  have hp : p.Prime := Fact.out
  have hDz : D ≠ 0 := by intro h; exact hD2 (h ▸ dvd_zero _)
  have hDa : D.natAbs ≠ 0 := by simpa using hDz
  have hlow : 1 ≤ D.natAbs.factorization p :=
    (hp.dvd_iff_one_le_factorization hDa).mp (Int.natCast_dvd.mp hD)
  have hhigh : D.natAbs.factorization p < 2 := by
    by_contra hn
    apply hD2
    have h := (hp.pow_dvd_iff_le_factorization hDa).mpr (by omega : 2 ≤ D.natAbs.factorization p)
    exact_mod_cast (Int.natCast_dvd.mpr h)
  have hv : D.natAbs.factorization p = 1 := by omega
  simp [localCoefficient, hDz, hv, Nat.ne_of_gt hb]

end DepthAspect.LocalValueRecursion
