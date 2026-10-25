import DepthAspect.FiniteCharacterFourier
import DepthAspect.ResidueNormalization
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp

/-!
# The actual odd-prime strata in the Fourier bound

The degree-e stratum is a literal function of t²−4x modulo p^(2e+1).
Its support injects into the p−1 nonzero residues modulo p, giving the
square-root support bound used in (95). No local Fourier norm is assumed.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.OddResidueFourier

variable {p : ℕ} [Fact p.Prime]

 def discriminant (k : ℕ) (t : ℤ) (x : (ZMod (p ^ k))ˣ) : ZMod (p ^ k) :=
  (t : ZMod (p ^ k)) ^ 2 - 4 * x

 theorem four_unit (hp2 : p ≠ 2) {k : ℕ} (hk : 0 < k) :
    IsUnit (4 : ZMod (p ^ k)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hk).mpr
  intro h
  have hd : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
    (show p ∣ (2 : ℕ) ^ 2 by norm_num; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
  · exact (Fact.out : p.Prime).ne_one h1
  · exact hp2 h2

 theorem discriminant_injective (hp2 : p ≠ 2) {k : ℕ} (hk : 0 < k) (t : ℤ) :
    Function.Injective (discriminant (p := p) k t) := by
  intro x y h
  apply Units.ext
  apply (four_unit hp2 hk).mul_left_cancel
  exact sub_right_injective h

/-- The exact-valuation stratum modulo p^(2e+1). Its normalized nonzero digit
is evaluated by the actual quadratic character on the prime field. -/
def stratum (e j : ℕ) (t : ℤ) (x : (ZMod (p ^ (2 * e + 1)))ˣ) : ℂ :=
  let D := discriminant (2 * e + 1) t x
  if p ^ (2 * e) ∣ D.val ∧ D.val ≠ 0 then
    (quadraticChar (ZMod p) ((D.val / p ^ (2 * e) : ℕ) : ZMod p) : ℂ) ^ (j - e)
  else 0

/-- The finite-ring stratum is the actual integer discriminant stratum,
with its normalized quadratic symbol, for any integer representative. -/
theorem stratum_eq_of_intCast (e j : ℕ) (t X : ℤ)
    (x : (ZMod (p ^ (2 * e + 1)))ˣ) (hx : (X : ZMod (p ^ (2 * e + 1))) = x) :
    stratum e j t x =
      if (p : ℤ) ^ (2 * e) ∣ t ^ 2 - 4 * X ∧
          ¬ (p : ℤ) ^ (2 * e + 1) ∣ t ^ 2 - 4 * X then
        (legendreSym p ((t ^ 2 - 4 * X) / (p : ℤ) ^ (2 * e)) : ℂ) ^ (j - e)
      else 0 := by
  have hD : discriminant (2 * e + 1) t x =
      ((t ^ 2 - 4 * X : ℤ) : ZMod (p ^ (2 * e + 1))) := by
    simp only [discriminant, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, hx]
  dsimp only [stratum]
  simp only [hD, ResidueNormalization.exact_stratum_iff (Fact.out : p.Prime)]
  split_ifs with h
  · have hs := ResidueNormalization.normalized_symbol (Fact.out : p.Prime)
      (2 * e) (t ^ 2 - 4 * X) h.1
    simpa only [legendreSym, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℂ) ^ (j - e)) hs
  · rfl

 theorem stratum_active {e j : ℕ} {t : ℤ} {x : (ZMod (p ^ (2 * e + 1)))ˣ}
    (hx : stratum e j t x ≠ 0) :
    p ^ (2 * e) ∣ (discriminant (2 * e + 1) t x).val ∧
      (discriminant (2 * e + 1) t x).val ≠ 0 := by
  dsimp only [stratum] at hx
  split_ifs at hx with h
  · exact h
  · exact (hx rfl).elim

 theorem normalized_lt (e : ℕ) (t : ℤ) (x : (ZMod (p ^ (2 * e + 1)))ˣ) :
    (discriminant (2 * e + 1) t x).val / p ^ (2 * e) < p := by
  apply (Nat.div_lt_iff_lt_mul (pow_pos (Fact.out : p.Prime).pos _)).mpr
  simpa only [pow_succ, mul_comm] using
    ZMod.val_lt (discriminant (2 * e + 1) t x)

 theorem normalized_ne_zero {e j : ℕ} {t : ℤ} {x : (ZMod (p ^ (2 * e + 1)))ˣ}
    (hx : stratum e j t x ≠ 0) :
    (((discriminant (2 * e + 1) t x).val / p ^ (2 * e) : ℕ) : ZMod p) ≠ 0 := by
  obtain ⟨hdiv, hne⟩ := stratum_active hx
  have hpos : 0 < (discriminant (2 * e + 1) t x).val / p ^ (2 * e) :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdiv)
      (pow_pos (Fact.out : p.Prime).pos _)
  intro hz
  have hval := congrArg ZMod.val hz
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (normalized_lt e t x), ZMod.val_zero] at hval
  omega

 theorem stratum_norm_le (e j : ℕ) (t : ℤ) (x : (ZMod (p ^ (2 * e + 1)))ˣ) :
    ‖stratum e j t x‖ ≤ 1 := by
  dsimp only [stratum]
  split_ifs with h
  · have hsym := quadraticChar_isQuadratic (ZMod p)
      (((discriminant (2 * e + 1) t x).val / p ^ (2 * e) : ℕ) : ZMod p)
    have hnorm : ‖(quadraticChar (ZMod p)
        (((discriminant (2 * e + 1) t x).val / p ^ (2 * e) : ℕ) : ZMod p) : ℂ)‖ ≤ 1 := by
      rcases hsym with hz | ho | hm
      · simp [hz]
      · simp [ho]
      · simp [hm]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hnorm
  · simp

private def supportMap (e j : ℕ) (t : ℤ)
    (x : {x : (ZMod (p ^ (2 * e + 1)))ˣ // stratum e j t x ≠ 0}) : (ZMod p)ˣ :=
  Units.mk0 (((discriminant (2 * e + 1) t x.val).val / p ^ (2 * e) : ℕ) : ZMod p)
    (normalized_ne_zero x.property)

 theorem supportMap_injective (hp2 : p ≠ 2) (e j : ℕ) (t : ℤ) :
    Function.Injective (supportMap (p := p) e j t) := by
  intro x y h
  apply Subtype.ext
  apply discriminant_injective hp2 (by omega : 0 < 2 * e + 1) t
  apply ZMod.val_injective
  have hv := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p).val) h
  change (((discriminant (2 * e + 1) t x.val).val / p ^ (2 * e) : ℕ) : ZMod p).val =
    (((discriminant (2 * e + 1) t y.val).val / p ^ (2 * e) : ℕ) : ZMod p).val at hv
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (normalized_lt e t x.val),
    Nat.mod_eq_of_lt (normalized_lt e t y.val)] at hv
  have hx := Nat.mul_div_cancel' (stratum_active x.property).1
  have hy := Nat.mul_div_cancel' (stratum_active y.property).1
  rw [← hx, ← hy, hv]

/-- Each actual stratum has at most p−1 supporting unit residue classes. -/
theorem stratum_support_card (hp2 : p ≠ 2) (e j : ℕ) (t : ℤ) :
    (Finset.univ.filter fun x : (ZMod (p ^ (2 * e + 1)))ˣ => stratum e j t x ≠ 0).card ≤
      p.totient := by
  classical
  have h := Fintype.card_le_of_injective (supportMap (p := p) e j t) (supportMap_injective hp2 e j t)
  simpa only [Fintype.card_subtype, ZMod.card_units_eq_totient] using h

/-- The square-root stratum bound in the proof of (95). -/
theorem beta_stratum (hp2 : p ≠ 2) (e j : ℕ) (t : ℤ) :
    FiniteCharacterFourier.beta (stratum (p := p) e j t) ≤ Real.sqrt p := by
  apply (FiniteCharacterFourier.beta_le_sqrt_support (stratum e j t)
    (stratum_norm_le e j t)).trans
  apply Real.sqrt_le_sqrt
  exact_mod_cast (stratum_support_card hp2 e j t).trans (Nat.totient_le p)

/-- The first term in (94) at its own defining modulus. -/
def divisibleTerm (k : ℕ) (t : ℤ) (x : (ZMod (p ^ k))ˣ) : ℂ :=
  if discriminant k t x = 0 then 1 else 0

 theorem beta_divisibleTerm (hp2 : p ≠ 2) {k : ℕ} (hk : 0 < k) (t : ℤ) :
    FiniteCharacterFourier.beta (divisibleTerm (p := p) k t) ≤ 1 := by
  classical
  have hcard : (Finset.univ.filter fun x => divisibleTerm (p := p) k t x ≠ 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx0 : discriminant k t x = 0 := by
      simpa [divisibleTerm] using (Finset.mem_filter.mp hx).2
    have hy0 : discriminant k t y = 0 := by
      simpa [divisibleTerm] using (Finset.mem_filter.mp hy).2
    exact discriminant_injective hp2 hk t (hx0.trans hy0.symm)
  have h := FiniteCharacterFourier.beta_le_sqrt_support (divisibleTerm (p := p) k t)
    (by intro x; unfold divisibleTerm; split_ifs <;> norm_num)
  apply h.trans
  calc
    _ ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hcard)
    _ = 1 := Real.sqrt_one

end DepthAspect.OddResidueFourier
