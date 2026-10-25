import DepthAspect.CoefficientBounds
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp

/-!
# Concrete odd-prime residue averages

A residue modulo p^(2b) is represented by its b pairs of base-p digits.
The function below is the recursive local discriminant function: a unit gives
the appropriate power of its quadratic symbol, valuation one gives zero, and
a multiple of p² reduces to the preceding pair of digits. The finite averages
are computed from these values, rather than supplied as hypotheses.

The separate identification with the globally defined imprimitive character
requires its fundamental-discriminant factorization; it is not asserted here.
-/

open scoped BigOperators
namespace DepthAspect.LocalResidueAverages

noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- The quadratic symbol in the prime field, with values viewed in ℝ. -/
def symbol (x : ZMod p) : ℝ := quadraticChar (ZMod p) x

/-- The degree-b unit contribution, extended by zero at the zero residue. -/
def unitPower (b : ℕ) (x : ZMod p) : ℝ := if x = 0 then 0 else symbol x ^ b

 theorem symbol_sq {x : ZMod p} (hx : x ≠ 0) : symbol x ^ 2 = 1 := by
  unfold symbol
  exact_mod_cast quadraticChar_sq_one hx

 theorem symbol_zero : symbol (0 : ZMod p) = 0 := by simp [symbol]

 theorem symbol_sum (hp2 : p ≠ 2) : (∑ x : ZMod p, symbol x) = 0 := by
  unfold symbol
  exact_mod_cast quadraticChar_sum_zero
    (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp2)

 theorem unitPower_even (j : ℕ) (x : ZMod p) :
    unitPower (2 * j) x = if x = 0 then 0 else 1 := by
  unfold unitPower
  split_ifs with hx
  · rfl
  · rw [pow_mul, symbol_sq hx, one_pow]

 theorem unitPower_odd (j : ℕ) (x : ZMod p) :
    unitPower (2 * j + 1) x = symbol x := by
  by_cases hx : x = 0
  · simp [unitPower, hx, symbol_zero]
  · simp only [unitPower, hx, ↓reduceIte, pow_add, pow_mul, symbol_sq hx,
      one_pow, pow_one, one_mul]

 theorem sum_unitPower_even (j : ℕ) :
    (∑ x : ZMod p, unitPower (2 * j) x) = (p : ℝ) - 1 := by
  classical
  simp_rw [unitPower_even]
  have h : (∑ x : ZMod p, if x = 0 then (0 : ℝ) else 1) + 1 = p := by
    calc
      _ = (∑ x : ZMod p, if x = 0 then (0 : ℝ) else 1) +
          ∑ x : ZMod p, if x = 0 then (1 : ℝ) else 0 := by simp
      _ = ∑ x : ZMod p, (1 : ℝ) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> norm_num
      _ = _ := by simp
  linarith

 theorem sum_unitPower_odd (hp2 : p ≠ 2) (j : ℕ) :
    (∑ x : ZMod p, unitPower (2 * j + 1) x) = 0 := by
  simp only [unitPower_odd, symbol_sum hp2]

 theorem sum_unitPower (hp2 : p ≠ 2) (b : ℕ) :
    (∑ x : ZMod p, unitPower b x) = if Even b then (p : ℝ) - 1 else 0 := by
  rcases Nat.even_or_odd b with hb | hb
  · obtain ⟨j, rfl⟩ := hb
    simpa [two_mul] using sum_unitPower_even (p := p) j
  · obtain ⟨j, rfl⟩ := hb
    have hodd : ¬ Even (j + j + 1) :=
      Nat.not_even_iff_odd.mpr ⟨j, by omega⟩
    simpa only [two_mul, hodd, ↓reduceIte] using sum_unitPower_odd (p := p) hp2 j

/-- Paired base-p digits, least significant pair first. -/
def Digits (p : ℕ) : ℕ → Type
  | 0 => PUnit
  | b + 1 => ZMod p × ZMod p × Digits p b

instance digitsFintype [NeZero p] (b : ℕ) : Fintype (Digits p b) := by
  induction b with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ b ih =>
    letI : Fintype (Digits p b) := ih
    exact inferInstanceAs (Fintype (ZMod p × ZMod p × Digits p b))

instance digitsNonempty [NeZero p] : (b : ℕ) → Nonempty (Digits p b)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | b + 1 => ⟨(0, 0, Classical.choice (digitsNonempty b))⟩

 theorem digits_card (b : ℕ) : Fintype.card (Digits p b) = p ^ (2 * b) := by
  induction b with
  | zero => simp [Digits]
  | succ b ih =>
    change Fintype.card (ZMod p × ZMod p × Digits p b) = _
    simp only [Fintype.card_prod, ZMod.card, ih]
    rw [show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]
    ring

/-- The base-p paired digit encoding, with the low digit first. -/
def digitEquiv : (b : ℕ) → Digits p b ≃ Fin (p ^ (2 * b))
  | 0 => by
    change PUnit ≃ Fin 1
    exact Equiv.ofUnique _ _
  | b + 1 =>
    let pair : (ZMod p × ZMod p) ≃ Fin (p ^ 2) :=
      ((Equiv.prodComm (ZMod p) (ZMod p)).trans
        ((ZMod.finEquiv p).symm.toEquiv.prodCongr (ZMod.finEquiv p).symm.toEquiv)).trans
        (finProdFinEquiv.trans (finCongr (by ring)))
    (((Equiv.prodAssoc (ZMod p) (ZMod p) (Digits p b)).symm.trans
      (Equiv.prodComm (ZMod p × ZMod p) (Digits p b))).trans
      ((digitEquiv b).prodCongr pair)).trans
      (finProdFinEquiv.trans (finCongr (by
        rw [show 2 * (b + 1) = 2 * b + 2 by omega, pow_add])))

/-- The digit chart is an actual bijection onto residues modulo p^(2b). -/
def residueEquiv (b : ℕ) : Digits p b ≃ ZMod (p ^ (2 * b)) :=
  (digitEquiv b).trans (ZMod.finEquiv (p ^ (2 * b))).toEquiv

private theorem finEquiv_val {n : ℕ} [NeZero n] (x : Fin n) :
    (ZMod.finEquiv n x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

private theorem finEquiv_symm_val {n : ℕ} [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The encoding is the ordinary base-p encoding, rather than an arbitrary
bijection between sets of the same size. -/
theorem residueEquiv_succ_val (b : ℕ) (lo hi : ZMod p) (D : Digits p b) :
    (residueEquiv (b + 1) (lo, hi, D)).val =
      lo.val + p * hi.val + p ^ 2 * (residueEquiv b D).val := by
  change ((ZMod.finEquiv (p ^ (2 * (b + 1)))) (digitEquiv (b + 1) (lo, hi, D))).val =
    lo.val + p * hi.val + p ^ 2 * ((ZMod.finEquiv (p ^ (2 * b))) (digitEquiv b D)).val
  rw [finEquiv_val, finEquiv_val]
  change ((ZMod.finEquiv p).symm lo).val + p * ((ZMod.finEquiv p).symm hi).val +
    p ^ 2 * (digitEquiv b D).val =
      lo.val + p * hi.val + p ^ 2 * (digitEquiv b D).val
  rw [finEquiv_symm_val, finEquiv_symm_val]

/-- The exact recursive local discriminant coefficient on the paired digits. -/
def value : (b : ℕ) → Digits p b → ℝ
  | 0, _ => 1
  | b + 1, D => unitPower (b + 1) D.1 +
      if D.1 = 0 ∧ D.2.1 = 0 then value b D.2.2 else 0

/-- The same literal local function on the usual residue ring. -/
def residueValue (b : ℕ) (D : ZMod (p ^ (2 * b))) : ℝ :=
  value b ((residueEquiv b).symm D)

 theorem residueValue_sum (b : ℕ) :
    (∑ D : ZMod (p ^ (2 * b)), residueValue b D) =
      ∑ d : Digits p b, value b d := by
  exact Equiv.sum_comp (residueEquiv b).symm (value b)

/-- Uniform average over all discriminant residues represented by the digits. -/
def mean (b : ℕ) : ℝ :=
  (∑ D : Digits p b, value b D) / (p : ℝ) ^ (2 * b)

@[simp] theorem mean_zero : mean (p := p) 0 = 1 := by simp [mean, value, Digits]

/-- The exact sum separates the unit residues and those divisible by p². -/
theorem value_sum_succ (b : ℕ) :
    (∑ D : Digits p (b + 1), value (b + 1) D) =
      (p : ℝ) * (p : ℝ) ^ (2 * b) * (∑ x : ZMod p, unitPower (b + 1) x) +
      ∑ D : Digits p b, value b D := by
  classical
  change (∑ D : ZMod p × ZMod p × Digits p b,
    (unitPower (b + 1) D.1 +
      if D.1 = 0 ∧ D.2.1 = 0 then value b D.2.2 else 0)) = _
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, digits_card,
    Nat.cast_pow, ZMod.card]
  simp only [← Finset.mul_sum]
  have hz : (∑ x : ZMod p, ∑ y : ZMod p,
      ∑ D : Digits p b, if x = 0 ∧ y = 0 then value b D else 0) =
        ∑ D : Digits p b, value b D := by
    have hh (x y : ZMod p) (D : Digits p b) :
        (if x = 0 ∧ y = 0 then value b D else 0) =
          (if x = 0 then if y = 0 then value b D else 0 else 0) := by
      split_ifs <;> simp_all
    simp_rw [hh]
    simp
  rw [hz]
  ring

/-- The recurrence in (86), now proved for the actual finite residue average. -/
theorem mean_succ (hp2 : p ≠ 2) (b : ℕ) :
    mean (p := p) (b + 1) =
      (if Even (b + 1) then 1 - 1 / (p : ℝ) else 0) + mean (p := p) b / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [mean, value_sum_succ, sum_unitPower hp2]
  rw [show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]
  unfold mean
  split_ifs <;> field_simp <;> ring

/-- This is the concrete average to which the previously verified recurrence
and coefficient inequalities apply. -/
theorem mean_eq_recurrence (hp2 : p ≠ 2) (b : ℕ) :
    mean (p := p) b = CoefficientBounds.unrestrictedLocalAverage p b := by
  induction b with
  | zero => simp [CoefficientBounds.unrestrictedLocalAverage]
  | succ b ih =>
    rw [mean_succ hp2, CoefficientBounds.unrestrictedLocalAverage, ih]
    simp [CoefficientBounds.localMeanStep]

 theorem mean_bounds (hp2 : p ≠ 2) (b : ℕ) :
    0 ≤ mean (p := p) b ∧ mean (p := p) b ≤ 1 := by
  rw [mean_eq_recurrence hp2]
  exact CoefficientBounds.unrestrictedLocalAverage_bounds p
    (by exact_mod_cast (Fact.out : p.Prime).two_le) b

/-- The average after excluding the discriminant class D=t² mod p. This is
the unit-x average under the invertible affine change D=t²−4x; that affine
identification is kept separate from the present finite sum calculation. -/
def unitMean : (b : ℕ) → ZMod p → ℝ
  | 0, _ => 1
  | b + 1, t =>
    (∑ lo : ZMod p, ∑ hi : ZMod p, ∑ D : Digits p b,
      if lo ≠ t ^ 2 then value (b + 1) (lo, hi, D) else 0) /
      (((p : ℝ) - 1) * p * (p : ℝ) ^ (2 * b))

private theorem sum_except {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) (c : α) :
    (∑ x : α, if x ≠ c then f x else 0) = (∑ x : α, f x) - f c := by
  classical
  calc
    _ = ∑ x : α, (f x - if x = c then f c else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x = c <;> simp [h]
    _ = _ := by rw [Finset.sum_sub_distrib]; simp

 theorem value_slice_sum (b : ℕ) (c : ZMod p) :
    (∑ hi : ZMod p, ∑ D : Digits p b, value (b + 1) (c, hi, D)) =
      (p : ℝ) * (p : ℝ) ^ (2 * b) * unitPower (b + 1) c +
        if c = 0 then ∑ D : Digits p b, value b D else 0 := by
  classical
  by_cases hc : c = 0
  · subst c
    simp [value, unitPower, digits_card]
  · simp [value, hc, digits_card, mul_assoc, mul_left_comm, mul_comm]

 theorem unitMean_numerator (b : ℕ) (t : ZMod p) :
    (∑ lo : ZMod p, ∑ hi : ZMod p, ∑ D : Digits p b,
      if lo ≠ t ^ 2 then value (b + 1) (lo, hi, D) else 0) =
      (∑ D : Digits p (b + 1), value (b + 1) D) -
        ((p : ℝ) * (p : ℝ) ^ (2 * b) * unitPower (b + 1) (t ^ 2) +
          if t = 0 then ∑ D : Digits p b, value b D else 0) := by
  classical
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [sum_except]
  rw [value_slice_sum]
  simp only [sq_eq_zero_iff]
  congr 1
  change _ = ∑ D : ZMod p × ZMod p × Digits p b, value (b + 1) D
  simp only [Fintype.sum_prod_type]

 theorem unitPower_square (b : ℕ) {t : ZMod p} (ht : t ≠ 0) :
    unitPower b (t ^ 2) = 1 := by
  have h : symbol (t ^ 2) = 1 := by
    unfold symbol
    exact_mod_cast quadraticChar_sq_one' ht
  simp [unitPower, sq_eq_zero_iff, ht, h]

/-- For p∣t, the actual unit average is one in even degrees and zero in odd
ones, as used in the first branch of (83). -/
theorem unitMean_zero (hp2 : p ≠ 2) (b : ℕ) :
    unitMean (p := p) b 0 = if Even b then 1 else 0 := by
  cases b with
  | zero => simp [unitMean]
  | succ b =>
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have h : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      linarith
    rw [unitMean, unitMean_numerator, value_sum_succ, sum_unitPower hp2]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), unitPower, ↓reduceIte,
      mul_zero, add_zero, sub_self, sub_add_cancel, zero_add]
    split_ifs <;> field_simp <;> ring

/-- For p∤t, exclusion of the square residue gives exactly the two coefficients
in (86). This statement computes a finite sum, rather than assuming its mean. -/
theorem unitMean_nonzero (hp2 : p ≠ 2) (b : ℕ) {t : ZMod p} (ht : t ≠ 0) :
    unitMean (p := p) (b + 1) t =
      (if Even (b + 1) then ((p : ℝ) - 2) / ((p : ℝ) - 1)
        else -(1 / ((p : ℝ) - 1))) + mean (p := p) b / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    linarith
  rw [unitMean, unitMean_numerator, value_sum_succ, sum_unitPower hp2,
    unitPower_square (b + 1) ht]
  simp only [ht, ↓reduceIte, add_zero, mul_one]
  unfold mean
  split_ifs <;> field_simp <;> ring

/-- The actual residue means have the precise parity majorant used in (87). -/
theorem abs_unitMean_le (hp2 : p ≠ 2) (b : ℕ) (t : ZMod p) :
    |unitMean (p := p) b t| ≤ if Even b then 1 else 1 / ((p : ℝ) - 1) := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  by_cases ht : t = 0
  · subst t
    rw [unitMean_zero hp2]
    split_ifs <;> simp only [abs_one, abs_zero]
    · exact le_refl _
    · exact one_div_nonneg.mpr (by linarith)
  · cases b with
    | zero => simp [unitMean]
    | succ b =>
      have hU := mean_bounds (p := p) hp2 b
      rw [unitMean_nonzero hp2 b ht]
      by_cases hb : Even (b + 1)
      · simpa only [hb, ↓reduceIte, CoefficientBounds.evenLocalCoefficient] using
          CoefficientBounds.evenLocalCoefficient_abs_le p (mean (p := p) b) hpr hU.1 hU.2
      · simpa only [hb, ↓reduceIte, CoefficientBounds.oddLocalCoefficient] using
          CoefficientBounds.oddLocalCoefficient_abs_le p (mean (p := p) b) hpr hU.1 hU.2

 theorem abs_unitMean_le_one (hp2 : p ≠ 2) (b : ℕ) (t : ZMod p) :
    |unitMean (p := p) b t| ≤ 1 := by
  apply (abs_unitMean_le hp2 b t).trans
  split_ifs
  · exact le_refl _
  · have hpr : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    exact (div_le_one (by linarith : 0 < (p : ℝ) - 1)).mpr (by linarith)

end
end DepthAspect.LocalResidueAverages
