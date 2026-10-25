import DepthAspect.OddDiscriminantValues
import DepthAspect.ResidueNormalization

/-!
# Representative independence of the literal odd-prime coefficients

The finite stratum expansion (94) is applied directly to arbitrary congruent
integer discriminants. This includes zero and square discriminants, using
the actual convention in localCoefficient.
-/
noncomputable section
namespace DepthAspect.OddCoefficientPeriodicity
open OddDiscriminantValues

variable {p : ℕ} [Fact p.Prime]

theorem normalized_symbol_eq {r : ℕ} {D E : ℤ}
    (h : D ≡ E [ZMOD (p : ℤ) ^ (r + 1)])
    (hD : (p : ℤ) ^ r ∣ D) (hE : (p : ℤ) ^ r ∣ E) :
    legendreSym p (D / (p : ℤ) ^ r) = legendreSym p (E / (p : ℤ) ^ r) := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hn : D / (p : ℤ) ^ r ≡ E / (p : ℤ) ^ r [ZMOD (p : ℤ)] := by
    apply Int.ModEq.mul_left_cancel' (pow_ne_zero r hpz)
    rw [Int.mul_ediv_cancel' hD, Int.mul_ediv_cancel' hE]
    simpa only [pow_succ] using h
  change quadraticChar (ZMod p) _ = quadraticChar (ZMod p) _
  congr 1
  exact (ZMod.intCast_eq_intCast_iff _ _ p).mpr hn

/-- Exact periodicity at the modulus claimed in (81) and (94). -/
theorem localCoefficient_eq_of_modEq (b : ℕ) {D E : ℤ}
    (h : D ≡ E [ZMOD (p : ℤ) ^ (2 * b)]) :
    localCoefficient p D b = localCoefficient p E b := by
  rw [localCoefficient_strata, localCoefficient_strata]
  have hterminal : (p : ℤ) ^ (2 * b) ∣ D ↔ (p : ℤ) ^ (2 * b) ∣ E := h.dvd_iff
  simp only [hterminal]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have heb := Finset.mem_range.mp he
  have he0 := h.of_dvd (pow_dvd_pow (p : ℤ) (by omega : 2 * e ≤ 2 * b))
  have he1 := h.of_dvd (pow_dvd_pow (p : ℤ) (by omega : 2 * e + 1 ≤ 2 * b))
  have hstratum : (p : ℤ) ^ (2 * e) ∣ D ∧ ¬ (p : ℤ) ^ (2 * e + 1) ∣ D ↔
      (p : ℤ) ^ (2 * e) ∣ E ∧ ¬ (p : ℤ) ^ (2 * e + 1) ∣ E :=
    and_congr he0.dvd_iff (not_congr he1.dvd_iff)
  by_cases hD : (p : ℤ) ^ (2 * e) ∣ D ∧ ¬ (p : ℤ) ^ (2 * e + 1) ∣ D
  · have hE := hstratum.mp hD
    rw [if_pos hD, if_pos hE, normalized_symbol_eq he1 hD.1 hE.1]
  · rw [if_neg hD, if_neg (fun hE => hD (hstratum.mpr hE))]

/-- In particular, replacing D by its standard residue representative leaves
the local coefficient unchanged. -/
theorem localCoefficient_residue (b : ℕ) (D : ℤ) :
    localCoefficient p (((D : ZMod (p ^ (2 * b))).val : ℕ) : ℤ) b =
      localCoefficient p D b := by
  apply localCoefficient_eq_of_modEq
  simpa only [Nat.cast_pow] using ResidueNormalization.val_modEq (p ^ (2 * b)) D

end DepthAspect.OddCoefficientPeriodicity
