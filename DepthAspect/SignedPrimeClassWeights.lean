import DepthAspect.QuadraticDiscriminantL
import DepthAspect.PrimeTraceWeights

/-!
# Actual discriminant weights in the prime trace

The conductor and fundamental part are constructed from the strict
elliptic discriminant. Their dyadic valuation and quadratic symbol are
then computed by the local table, while the class-number difference is
derived from the general analytic identity and the proved Euler factors.
-/
namespace DepthAspect.QuadraticDiscriminantL
open FundamentalDiscriminant OddDiscriminantValues QuadraticClassFormula
open PrimeTraceWeights

noncomputable def primeWeight (P : ℤ) : ℝ :=
  if P % 4 = 1 then 1 / 2 else if P % 8 = 3 then 3 / 8 else 1 / 4

theorem negative_modulus_factorization (D : ℤ) (hD : IsNegativeDiscriminant D) :
    D = -((datum D hD).fundamental.natAbs : ℤ) *
      ((datum D hD).conductor : ℤ) ^ 2 := by
  rw [Int.natCast_natAbs, abs_of_neg (datum D hD).fundamental_neg, neg_neg]
  exact (datum D hD).factorization

/-- General (77), now for the actual discriminant selected by its integer
value. No factorization witness or recurrence is an input. -/
theorem class_scaling {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) (j : ℕ) :
    H ((4 : ℤ) ^ (j + 1) * D) - H ((4 : ℤ) ^ j * D) =
      (2 : ℝ) ^ j * (H (4 * D) - H D) := by
  let Z := datum D hD
  let χ := G.quadratic Z.fundamental Z.fundamental_shape Z.fundamental_neg
  have hq : 0 < Z.fundamental.natAbs := Int.natAbs_pos.mpr (ne_of_lt Z.fundamental_neg)
  letI : NeZero Z.fundamental.natAbs := ⟨Nat.ne_of_gt hq⟩
  have hα : χ.character (2 : ZMod Z.fundamental.natAbs) =
      ((twoSymbol Z.fundamental : ℝ) : ℂ) := by simpa using χ.two_value
  have h := DyadicClassScaling.hurwitz_four_pow_difference χ.character
    (G.odd _ Z.fundamental_shape Z.fundamental_neg) hq H
    (G.negative_modulus _ Z.fundamental_shape Z.fundamental_neg)
    Z.conductor Z.conductor_pos j (twoSymbol Z.fundamental : ℝ) hα
  have hfactor : D = -(Z.fundamental.natAbs : ℤ) * (Z.conductor : ℤ) ^ 2 :=
    negative_modulus_factorization D hD
  simpa only [← hfactor] using h

/-- The actual class-number ratio at the conductor chosen by integer
factorization. This is used only as an intermediate before the prime
residue table removes that conductor from the final formula. -/
theorem class_difference {H : ℤ → ℝ} (G : GeneralFormula H) (D : ℤ)
    (hD : IsNegativeDiscriminant D) :
    H (4 * D) - H D =
      4 * localPrimeWeight ((datum D hD).conductor.factorization 2)
        (twoSymbol (datum D hD).fundamental : ℝ) * H D := by
  let Z := datum D hD
  let χ := G.quadratic Z.fundamental Z.fundamental_shape Z.fundamental_neg
  have hq : 0 < Z.fundamental.natAbs := Int.natAbs_pos.mpr (ne_of_lt Z.fundamental_neg)
  letI : NeZero Z.fundamental.natAbs := ⟨Nat.ne_of_gt hq⟩
  have hα : χ.character (2 : ZMod Z.fundamental.natAbs) =
      ((twoSymbol Z.fundamental : ℝ) : ℂ) := by simpa using χ.two_value
  have hαle : (twoSymbol Z.fundamental : ℝ) ≤ 1 := by
    exact_mod_cast (le_abs_self (twoSymbol Z.fundamental)).trans
      (abs_twoSymbol_le_one Z.fundamental)
  have h := DyadicClassScaling.hurwitz_difference_ratio χ.character
    (G.odd _ Z.fundamental_shape Z.fundamental_neg) hq H
    (G.negative_modulus _ Z.fundamental_shape Z.fundamental_neg)
    Z.conductor Z.conductor_pos (twoSymbol Z.fundamental : ℝ) hα hαle
  rw [← negative_modulus_factorization D hD] at h
  change H (4 * D) - H D =
    4 * localPrimeWeight (Z.conductor.factorization 2) (twoSymbol Z.fundamental : ℝ) * H D
  rw [h]
  unfold localPrimeWeight
  have hT := ne_of_gt (DyadicClassScaling.localClassFactor_pos
    (twoSymbol Z.fundamental : ℝ) (Z.conductor.factorization 2) hαle)
  field_simp [hT] <;> ring

/-- The even-depth class-number difference on the true Ramanujan support
is exactly four times the displayed residue-class weight. -/
theorem even_prime_class_difference {H : ℤ → ℝ} (G : GeneralFormula H)
    (t P : ℤ) (ht : 8 ∣ t) (hP : Odd P) (hbound : t ^ 2 < 4 * P) :
    H (4 * (t ^ 2 - 4 * P)) - H (t ^ 2 - 4 * P) =
      4 * primeWeight P * H (t ^ 2 - 4 * P) := by
  let hD := elliptic_isNegativeDiscriminant t P hbound
  let Z := datum (t ^ 2 - 4 * P) hD
  let χ := G.quadratic Z.fundamental Z.fundamental_shape Z.fundamental_neg
  have hweight := localPrimeWeight_prime_table t P ht hP Z.fundamental_shape χ
    (Nat.ne_of_gt Z.conductor_pos) Z.factorization
  rw [class_difference G _ hD, hweight]
  rfl

/-- At odd depth the actual conductor is odd and the quadratic character
at two is ramified, so the class-number difference is twice H(D). -/
theorem odd_prime_class_difference {H : ℤ → ℝ} (G : GeneralFormula H)
    (t P : ℤ) (ht : 8 ∣ t) (hP : Odd P) (hbound : t ^ 2 < 8 * P) :
    H (4 * (t ^ 2 - 8 * P)) - H (t ^ 2 - 8 * P) =
      2 * H (t ^ 2 - 8 * P) := by
  have hbound' : t ^ 2 < 4 * (2 * P) := by nlinarith
  let hD : IsNegativeDiscriminant (t ^ 2 - 8 * P) := by
    convert elliptic_isNegativeDiscriminant t (2 * P) hbound' using 1 <;> ring
  let Z := datum (t ^ 2 - 8 * P) hD
  let χ := G.quadratic Z.fundamental Z.fundamental_shape Z.fundamental_neg
  obtain ⟨he, hα⟩ := odd_prime_conductor_zero t P ht hP Z.fundamental_shape χ
    (Nat.ne_of_gt Z.conductor_pos) Z.factorization
  rw [class_difference G _ hD, he, hα]
  norm_num

end DepthAspect.QuadraticDiscriminantL
