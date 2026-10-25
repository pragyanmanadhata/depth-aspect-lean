import DepthAspect.LocalValueRecursion
import DepthAspect.LocalResidueAverages

/-!
# Identifying the computed residue means with the actual ψ coefficient

The paired base-p chart used for the finite average is the ordinary base-p
encoding. Its recursive value is proved equal to the local discriminant
coefficient, using the unit, valuation-one, and p²-scaling identities.
-/
noncomputable section
namespace DepthAspect.LocalResidueIdentification
open LocalResidueAverages LocalValueRecursion OddDiscriminantValues

variable {p : ℕ} [Fact p.Prime]

private theorem low_digit_cast (b : ℕ) (lo hi : ZMod p) (D : Digits p b) :
    (((residueEquiv (b + 1) (lo, hi, D)).val : ℕ) : ZMod p) = lo := by
  rw [residueEquiv_succ_val]
  simp

private theorem one_zero_digit_dvd (b : ℕ) (hi : ZMod p) (D : Digits p b) :
    (p : ℤ) ∣ ((residueEquiv (b + 1) (0, hi, D)).val : ℤ) := by
  rw [residueEquiv_succ_val]
  refine ⟨(hi.val : ℤ) + p * (residueEquiv b D).val, ?_⟩
  push_cast
  simp only [ZMod.val_zero]
  ring

private theorem one_zero_digit_not_square (b : ℕ) (hi : ZMod p) (hhi : hi ≠ 0)
    (D : Digits p b) :
    ¬ (p : ℤ) ^ 2 ∣ ((residueEquiv (b + 1) (0, hi, D)).val : ℤ) := by
  intro hdiv
  obtain ⟨k, hk⟩ := hdiv
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have heq : (p : ℤ) * ((hi.val : ℤ) + p * (residueEquiv b D).val) = p * (p * k) := by
    rw [residueEquiv_succ_val] at hk
    push_cast at hk
    simp only [ZMod.val_zero, Nat.cast_zero, zero_add] at hk
    nlinarith [hk]
  have hcancel := mul_left_cancel₀ hp heq
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hcancel
  apply hhi
  simpa using hcast

/-- The actual finite digit function agrees pointwise with the coefficient
already identified with ψ. This discharges the finite-average model boundary. -/
theorem value_eq_localCoefficient : ∀ (b : ℕ) (D : Digits p b),
    (value b D : ℂ) = localCoefficient p ((residueEquiv b D).val : ℤ) b := by
  intro b
  induction b with
  | zero => intro D; simp [value]
  | succ b ih =>
    rintro ⟨lo, hi, D⟩
    by_cases hlo : lo = 0
    · subst lo
      by_cases hhi : hi = 0
      · subst hi
        have heq : ((residueEquiv (b + 1) (0, 0, D)).val : ℤ) =
            (p : ℤ) ^ 2 * ((residueEquiv b D).val : ℤ) := by
          rw [residueEquiv_succ_val]
          simp
        rw [heq, localCoefficient_mul_square, ← ih D]
        simp [value, unitPower]
      · rw [localCoefficient_of_one_dvd (one_zero_digit_dvd b hi D)
          (one_zero_digit_not_square b hi hhi D) (Nat.succ_pos b)]
        simp [value, unitPower, hhi]
    · have hn : ¬ (p : ℤ) ∣ ((residueEquiv (b + 1) (lo, hi, D)).val : ℤ) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simpa only [Int.cast_natCast, low_digit_cast] using hlo
      rw [localCoefficient_of_not_dvd hn]
      simp only [value, unitPower, hlo, ↓reduceIte, false_and, add_zero,
        Complex.ofReal_pow, symbol, legendreSym, Int.cast_natCast, low_digit_cast]
      norm_cast

/-- On the ordinary residue ring, the finite average has the literal local
coefficient as its integrand. -/
theorem residueValue_eq_localCoefficient (b : ℕ) (D : ZMod (p ^ (2 * b))) :
    (residueValue b D : ℂ) = localCoefficient p (D.val : ℤ) b := by
  unfold residueValue
  rw [value_eq_localCoefficient, Equiv.apply_symm_apply]

end DepthAspect.LocalResidueIdentification
