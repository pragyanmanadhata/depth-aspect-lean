import DepthAspect.DyadicDiscriminantValues
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FinCases

/-!
# The actual four-class dyadic average and its generating functions

The twists use Mathlib's actual characters χ₄, χ₈, and χ₈'. The average is
literally over (Z/8Z)ˣ. An explicit bijection with its four odd classes proves
(91), and actual convergent geometric series prove (89).
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.DyadicLocalMeans
open FundamentalDiscriminant OddDiscriminantValues ImprimitiveCharacter
open DyadicDiscriminantValues

/-- The four twists, in the order 1, χ−4, χ8, χ−8. -/
def twistValue (χ : Fin 4) (K : ZMod 8) : ℤ :=
  ![1, ZMod.χ₄ (ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) K),
    ZMod.χ₈ K, ZMod.χ₈' K] χ

/-- The literal local coefficient in an odd discriminant quotient K. -/
def residueCoefficient (b : ℕ) (K : ZMod 8) : ℂ :=
  if b = 0 then 1 else
    if ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) K = 1 then
      (ZMod.χ₈ K : ℂ) ^ (b - 1)
    else 0

/-- The definition of the dyadic average at modulus eight. -/
def average (χ : Fin 4) (b : ℕ) : ℂ :=
  (∑ K : (ZMod 8)ˣ, (twistValue χ K : ℂ) * residueCoefficient b K) / 4

private def unitClass (i : Fin 4) : (ZMod 8)ˣ :=
  ZMod.unitOfCoprime (2 * i.val + 1) (by fin_cases i <;> decide)

private theorem unitClass_val (i : Fin 4) :
    ((unitClass i : (ZMod 8)ˣ) : ZMod 8).val = 2 * i.val + 1 := by
  fin_cases i <;> rfl

/-- The four classes have equal frequency because this is an actual bijection. -/
def unitsEquivFour : Fin 4 ≃ (ZMod 8)ˣ :=
  Equiv.ofBijective unitClass (by
    constructor
    · intro i j h
      have hv := congrArg (fun x : (ZMod 8)ˣ => (x : ZMod 8).val) h
      rw [unitClass_val, unitClass_val] at hv
      apply Fin.ext
      omega
    · intro x
      have hlt := (x : ZMod 8).val_lt
      have hc := ZMod.val_coe_unit_coprime x
      have hc2 : (x : ZMod 8).val.Coprime 2 :=
        (Nat.coprime_pow_right_iff (by omega : 0 < 3) (x : ZMod 8).val 2).mp
          (by norm_num; exact hc)
      have ho := Nat.odd_iff.mp (Nat.coprime_two_right.mp hc2)
      refine ⟨⟨(x : ZMod 8).val / 2, by omega⟩, ?_⟩
      apply Units.ext
      apply ZMod.val_injective
      rw [unitClass_val]
      change 2 * ((x : ZMod 8).val / 2) + 1 = (x : ZMod 8).val
      omega)

private theorem unitsEquivFour_coe (i : Fin 4) :
    ((unitsEquivFour i : (ZMod 8)ˣ) : ZMod 8) =
      (![1, 3, 5, 7] : Fin 4 → ZMod 8) i := by
  fin_cases i <;> rfl

private theorem cast_eight_four_one : (ZMod.cast (1 : ZMod 8) : ZMod 4) = 1 := by
  decide

private theorem cast_eight_four_three : (ZMod.cast (3 : ZMod 8) : ZMod 4) = 3 := by
  decide

private theorem cast_eight_four_five : (ZMod.cast (5 : ZMod 8) : ZMod 4) = 1 := by
  decide

private theorem cast_eight_four_seven : (ZMod.cast (7 : ZMod 8) : ZMod 4) = 3 := by
  decide

private theorem three_ne_one_mod_four : (3 : ZMod 4) ≠ 1 := by
  decide

theorem card_units_eight : Fintype.card (ZMod 8)ˣ = 4 := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr unitsEquivFour).symm

/-- The denominator four is exactly the order of the reduced residue group. -/
theorem average_eq_normalized (χ : Fin 4) (b : ℕ) :
    average χ b =
      (∑ K : (ZMod 8)ˣ, (twistValue χ K : ℂ) * residueCoefficient b K) /
        Fintype.card (ZMod 8)ˣ := by
  rw [card_units_eight]
  rfl

/-- Evaluation of the literal four-class average in degree zero. -/
theorem average_zero (χ : Fin 4) : average χ 0 = if χ = 0 then 1 else 0 := by
  unfold average
  rw [← Equiv.sum_comp unitsEquivFour]
  simp only [unitsEquivFour_coe]
  fin_cases χ <;>
    norm_num [twistValue, residueCoefficient, Fin.sum_univ_succ,
      cast_eight_four_one, cast_eight_four_three, cast_eight_four_five,
      cast_eight_four_seven, three_ne_one_mod_four, ZMod.χ₄, ZMod.χ₈, ZMod.χ₈']

/-- Equation (91), with the four residue classes actually summed. -/
theorem average_succ (χ : Fin 4) (b : ℕ) :
    average χ (b + 1) = (1 + (twistValue χ 5 : ℂ) * (-1 : ℂ) ^ b) / 4 := by
  unfold average
  rw [← Equiv.sum_comp unitsEquivFour]
  simp only [unitsEquivFour_coe]
  fin_cases χ <;>
    norm_num [twistValue, residueCoefficient, Fin.sum_univ_succ,
      cast_eight_four_one, cast_eight_four_three, cast_eight_four_five,
      cast_eight_four_seven, three_ne_one_mod_four, ZMod.χ₄, ZMod.χ₈, ZMod.χ₈']

/-- The residue function is the actual imprimitive value in table (82). -/
theorem residueCoefficient_eq_psi {K d : ℤ} (hK : Odd K)
    (hd : IsFundamental d) (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : 4 * K = d * (f : ℤ) ^ 2) (b : ℕ) :
    residueCoefficient b (K : ZMod 8) = psiNat χ.character f (2 ^ b) := by
  have hKmod : K % 4 = 1 ∨ K % 4 = 3 := by
    have h := Int.odd_iff.mp hK
    omega
  have htest : ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) (K : ZMod 8) = 1 ↔
      K % 4 = 1 := by
    rw [map_intCast]
    change (K : ZMod 4) = ((1 : ℤ) : ZMod 4) ↔ _
    rw [ZMod.intCast_eq_intCast_iff]
    norm_num [Int.ModEq]
  by_cases hb : b = 0
  · simp [residueCoefficient, hb, ImprimitiveEuler.psiNat_one]
  · unfold residueCoefficient
    rw [if_neg hb]
    simp only [htest]
    rcases hKmod with hK1 | hK3
    · rw [if_pos hK1, psi_two_even_one hd hK χ hf 0 b (by simpa using hD) hK1]
      rfl
    · rw [if_neg (by omega), psi_two_even_three hd hK χ hf 0 b (by simpa using hD) hK3,
        if_neg (by omega)]

/-- The change from the averaging variable x to K=-x is a permutation of
units, so the paper's χ(-x) convention produces exactly this average. -/
theorem average_negated_classes (χ : Fin 4) (b : ℕ) :
    (∑ x : (ZMod 8)ˣ,
      (twistValue χ (-(x : ZMod 8)) : ℂ) * residueCoefficient b (-(x : ZMod 8))) / 4 =
      average χ b := by
  unfold average
  congr 1
  exact Equiv.sum_comp (Equiv.neg (ZMod 8)ˣ)
    (fun x => (twistValue χ (x : ZMod 8) : ℂ) * residueCoefficient b (x : ZMod 8))

/-- The genuine convergent geometric-series expression before simplification. -/
theorem average_hasSum {z : ℂ} (hz : ‖z‖ < 1) (χ : Fin 4) :
    HasSum (fun b : ℕ => average χ b * z ^ b)
      ((if χ = 0 then 1 else 0) +
        z / 4 * ((1 - z)⁻¹ + (twistValue χ 5 : ℂ) * (1 + z)⁻¹)) := by
  have hzneg : ‖-z‖ < 1 := by simpa using hz
  have hgeom := hasSum_geometric_of_norm_lt_one hz
  have halt := hasSum_geometric_of_norm_lt_one hzneg
  have hsum := (hgeom.add (halt.mul_left (twistValue χ 5 : ℂ))).mul_left (z / 4)
  have htail : HasSum (fun b : ℕ => average χ (b + 1) * z ^ (b + 1))
      (z / 4 * ((1 - z)⁻¹ + (twistValue χ 5 : ℂ) * (1 + z)⁻¹)) := by
    convert! hsum using 1
    · funext b
      rw [average_succ, pow_succ, neg_eq_neg_one_mul, mul_pow]
      ring
    · congr 3
      ring
  apply (hasSum_nat_add_iff' 1).mp
  simpa only [Finset.sum_range_one, pow_zero, mul_one, average_zero, add_sub_cancel_left]
    using htail

/-- The four rational functions in (89), now as actual convergent sums. -/
theorem generating_functions {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun b : ℕ => average 0 b * z ^ b) ((2 + z - 2 * z ^ 2) / (2 * (1 - z ^ 2))) ∧
    HasSum (fun b : ℕ => average 1 b * z ^ b) (z / (2 * (1 - z ^ 2))) ∧
    HasSum (fun b : ℕ => average 2 b * z ^ b) (z ^ 2 / (2 * (1 - z ^ 2))) ∧
    HasSum (fun b : ℕ => average 3 b * z ^ b) (z ^ 2 / (2 * (1 - z ^ 2))) := by
  have hminus : 1 - z ≠ 0 := by
    intro h
    have hz1 := sub_eq_zero.mp h
    rw [← hz1, norm_one] at hz
    exact (lt_irrefl 1) hz
  have hplus : 1 + z ≠ 0 := by
    intro h
    have hz1 : z = -1 := by linear_combination h
    rw [hz1, norm_neg, norm_one] at hz
    exact (lt_irrefl 1) hz
  have hsquare : 1 - z ^ 2 ≠ 0 := by
    have hid : 1 - z ^ 2 = (1 - z) * (1 + z) := by ring
    rw [hid]
    exact mul_ne_zero hminus hplus
  have ht0 : twistValue (0 : Fin 4) 5 = 1 := by decide
  have ht1 : twistValue (1 : Fin 4) 5 = 1 := by decide
  have ht2 : twistValue (2 : Fin 4) 5 = -1 := by decide
  have ht3 : twistValue (3 : Fin 4) 5 = -1 := by decide
  have hi1 : (1 : Fin 4) ≠ 0 := by decide
  have hi2 : (2 : Fin 4) ≠ 0 := by decide
  have hi3 : (3 : Fin 4) ≠ 0 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! average_hasSum hz (0 : Fin 4) using 1
    simp only [ht0, ite_true, Int.cast_one]
    field_simp [hminus, hplus, hsquare]
    ring
  · convert! average_hasSum hz (1 : Fin 4) using 1
    simp only [ht1, if_neg hi1, Int.cast_one]
    field_simp [hminus, hplus, hsquare]
    ring
  · convert! average_hasSum hz (2 : Fin 4) using 1
    simp only [ht2, if_neg hi2, Int.cast_neg, Int.cast_one]
    field_simp [hminus, hplus, hsquare]
    ring
  · convert! average_hasSum hz (3 : Fin 4) using 1
    simp only [ht3, if_neg hi3, Int.cast_neg, Int.cast_one]
    field_simp [hminus, hplus, hsquare]
    ring

end DepthAspect.DyadicLocalMeans
