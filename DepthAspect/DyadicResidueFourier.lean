import DepthAspect.FiniteCharacterFourier
import DepthAspect.FundamentalDiscriminant
import DepthAspect.ResidueNormalization
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The actual dyadic residue strata behind (97)

For z=u²−x the affine map on unit classes is injective. A stratum modulo
2^(2a+r), supported on 2^(2a)∣z, has at most 2^r classes. The quadratic
symbol here is the actual character modulo eight. Thus r≤3 yields the
square-root-eight bound used for each term of (96).
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.DyadicResidueFourier
open FundamentalDiscriminant

/-- The literal affine variable in (96), on its defining residue ring. -/
def residual (n : ℕ) (u : ℤ) (x : (ZMod (2 ^ n))ˣ) : ZMod (2 ^ n) :=
  (u : ZMod (2 ^ n)) ^ 2 - x

theorem residual_injective (n : ℕ) (u : ℤ) :
    Function.Injective (residual n u) := by
  intro x y h
  apply Units.ext
  exact sub_right_injective h

/-- The stratum at valuation 2a, including the required residue one modulo
four and the exact power of the quadratic symbol. The extra digit count r
will be two for the final stratum and three for the preceding strata. -/
def stratum (a r b : ℕ) (u : ℤ) (x : (ZMod (2 ^ (2 * a + r)))ˣ) : ℂ :=
  let z := residual (2 * a + r) u x
  if 2 ^ (2 * a) ∣ z.val ∧ (z.val / 2 ^ (2 * a)) % 4 = 1 then
    (twoSymbol ((z.val / 2 ^ (2 * a) : ℕ) : ℤ) : ℂ) ^ b
  else 0

/-- The residue stratum is independent of the representative. Two remaining
digits determine the indicator; three determine the quadratic symbol, unless
its exponent is zero. This is exactly the modulus distinction after (96). -/
theorem stratum_eq_of_intCast (a r b : ℕ) (hr : 2 ≤ r)
    (hb : b = 0 ∨ 3 ≤ r) (u X : ℤ)
    (x : (ZMod (2 ^ (2 * a + r)))ˣ)
    (hx : (X : ZMod (2 ^ (2 * a + r))) = x) :
    stratum a r b u x =
      if (2 : ℤ) ^ (2 * a) ∣ u ^ 2 - X ∧
          ((u ^ 2 - X) / (2 : ℤ) ^ (2 * a)) % 4 = 1 then
        (twoSymbol ((u ^ 2 - X) / (2 : ℤ) ^ (2 * a)) : ℂ) ^ b
      else 0 := by
  have hres : residual (2 * a + r) u x =
      ((u ^ 2 - X : ℤ) : ZMod (2 ^ (2 * a + r))) := by
    simp only [residual, Int.cast_sub, Int.cast_pow, hx]
  have hdvd : 2 ^ (2 * a) ∣ ((u ^ 2 - X : ℤ) : ZMod (2 ^ (2 * a + r))).val ↔
      (2 : ℤ) ^ (2 * a) ∣ u ^ 2 - X := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      ResidueNormalization.divides_val_iff (pow_dvd_pow 2 (by omega)) (u ^ 2 - X)
  dsimp only [stratum]
  rw [hres]
  by_cases hD : (2 : ℤ) ^ (2 * a) ∣ u ^ 2 - X
  · have hn := ResidueNormalization.normalized_modEq_pow (p := 2)
      (2 * a) r (u ^ 2 - X) hD
    have hn4 := hn.of_dvd (show (4 : ℤ) ∣ 2 ^ r from by
      simpa only [show (2 : ℤ) ^ 2 = 4 by norm_num] using pow_dvd_pow (2 : ℤ) hr)
    have hmod4 : (((u ^ 2 - X : ℤ) : ZMod (2 ^ (2 * a + r))).val /
          2 ^ (2 * a)) % 4 = 1 ↔
        ((u ^ 2 - X) / (2 : ℤ) ^ (2 * a)) % 4 = 1 := by
      have heq := hn4
      change _ % 4 = _ % 4 at heq
      let v : ℕ := ((u ^ 2 - X : ℤ) : ZMod (2 ^ (2 * a + r))).val / 2 ^ (2 * a)
      have hi : (v : ℤ) % 4 = 1 ↔
          ((u ^ 2 - X) / (2 : ℤ) ^ (2 * a)) % 4 = 1 := by
        change _ % 4 = 1 ↔ _
        rw [heq]
        norm_num only [Nat.cast_ofNat]
      exact_mod_cast hi
    simp only [hdvd, hD, true_and, hmod4]
    split_ifs with h4
    · rcases hb with rfl | hb
      · simp
      · have hn8 := hn.of_dvd (show (8 : ℤ) ∣ 2 ^ r from by
          simpa only [show (2 : ℤ) ^ 3 = 8 by norm_num] using pow_dvd_pow (2 : ℤ) hb)
        have hs : twoSymbol (((((u ^ 2 - X : ℤ) : ZMod (2 ^ (2 * a + r))).val /
            2 ^ (2 * a) : ℕ) : ℤ)) =
            twoSymbol ((u ^ 2 - X) / (2 : ℤ) ^ (2 * a)) := by
          unfold twoSymbol
          congr 1
          exact (ZMod.intCast_eq_intCast_iff _ _ 8).mpr hn8
        rw [hs]
    · rfl
  · simp only [hdvd, hD, false_and, ↓reduceIte]

theorem stratum_active {a r b : ℕ} {u : ℤ}
    {x : (ZMod (2 ^ (2 * a + r)))ˣ} (hx : stratum a r b u x ≠ 0) :
    2 ^ (2 * a) ∣ (residual (2 * a + r) u x).val := by
  dsimp only [stratum] at hx
  split_ifs at hx with h
  · exact h.1
  · exact (hx rfl).elim

theorem normalized_lt (a r : ℕ) (u : ℤ) (x : (ZMod (2 ^ (2 * a + r)))ˣ) :
    (residual (2 * a + r) u x).val / 2 ^ (2 * a) < 2 ^ r := by
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (2 * a))).mpr
  simpa only [pow_add, mul_comm] using ZMod.val_lt (residual (2 * a + r) u x)

private def supportMap (a r b : ℕ) (u : ℤ)
    (x : {x : (ZMod (2 ^ (2 * a + r)))ˣ // stratum a r b u x ≠ 0}) : Fin (2 ^ r) :=
  ⟨(residual (2 * a + r) u x.val).val / 2 ^ (2 * a), normalized_lt a r u x.val⟩

theorem supportMap_injective (a r b : ℕ) (u : ℤ) :
    Function.Injective (supportMap a r b u) := by
  intro x y h
  apply Subtype.ext
  apply residual_injective (2 * a + r) u
  apply ZMod.val_injective
  have hv := congrArg Fin.val h
  change (residual (2 * a + r) u x.val).val / 2 ^ (2 * a) =
    (residual (2 * a + r) u y.val).val / 2 ^ (2 * a) at hv
  have hx := Nat.mul_div_cancel' (stratum_active x.property)
  have hy := Nat.mul_div_cancel' (stratum_active y.property)
  rw [← hx, ← hy, hv]

/-- This support estimate is proved for the actual residue function, without
assuming a Fourier norm or a residue-counting formula. -/
theorem stratum_support_card (a r b : ℕ) (u : ℤ) :
    (Finset.univ.filter fun x : (ZMod (2 ^ (2 * a + r)))ˣ =>
      stratum a r b u x ≠ 0).card ≤ 2 ^ r := by
  classical
  have h := Fintype.card_le_of_injective (supportMap a r b u)
    (supportMap_injective a r b u)
  simpa only [Fintype.card_subtype, Fintype.card_fin] using h

theorem stratum_norm_le (a r b : ℕ) (u : ℤ)
    (x : (ZMod (2 ^ (2 * a + r)))ˣ) : ‖stratum a r b u x‖ ≤ 1 := by
  dsimp only [stratum]
  split_ifs with h
  · have hn : ‖(twoSymbol (((residual (2 * a + r) u x).val /
        2 ^ (2 * a) : ℕ) : ℤ) : ℂ)‖ ≤ 1 := by
      rcases twoSymbol_cases (((residual (2 * a + r) u x).val /
          2 ^ (2 * a) : ℕ) : ℤ) with hs | hs | hs <;> rw [hs] <;> norm_num
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hn
  · simp

theorem beta_stratum (a r b : ℕ) (u : ℤ) :
    FiniteCharacterFourier.beta (stratum a r b u) ≤ Real.sqrt ((2 : ℝ) ^ r) := by
  apply (FiniteCharacterFourier.beta_le_sqrt_support (stratum a r b u)
    (stratum_norm_le a r b u)).trans
  apply Real.sqrt_le_sqrt
  exact_mod_cast stratum_support_card a r b u

theorem beta_stratum_le_sqrt_eight (a r b : ℕ) (hr : r ≤ 3) (u : ℤ) :
    FiniteCharacterFourier.beta (stratum a r b u) ≤ Real.sqrt 8 := by
  apply (beta_stratum a r b u).trans
  apply Real.sqrt_le_sqrt
  calc
    (2 : ℝ) ^ r ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hr
    _ = 8 := by norm_num

/-- The terminal divisibility indicator on its own defining modulus. -/
def divisibleTerm (j : ℕ) (u : ℤ) (x : (ZMod (2 ^ (2 * j)))ˣ) : ℂ :=
  if residual (2 * j) u x = 0 then 1 else 0

theorem beta_divisibleTerm (j : ℕ) (u : ℤ) :
    FiniteCharacterFourier.beta (divisibleTerm j u) ≤ 1 := by
  classical
  have hcard : (Finset.univ.filter fun x => divisibleTerm j u x ≠ 0).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx0 : residual (2 * j) u x = 0 := by
      simpa [divisibleTerm] using (Finset.mem_filter.mp hx).2
    have hy0 : residual (2 * j) u y = 0 := by
      simpa [divisibleTerm] using (Finset.mem_filter.mp hy).2
    exact residual_injective (2 * j) u (hx0.trans hy0.symm)
  have h := FiniteCharacterFourier.beta_le_sqrt_support (divisibleTerm j u)
    (by intro x; unfold divisibleTerm; split_ifs <;> norm_num)
  apply h.trans
  calc
    _ ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hcard)
    _ = 1 := Real.sqrt_one

end DepthAspect.DyadicResidueFourier
