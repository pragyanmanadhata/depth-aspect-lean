import DepthAspect.ClassNumberGrowth
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.Real.Pi.Leibniz

/-!
# Actual ordered quadratic-character values

The modulus-four character is mathlib's actual quadratic character, embedded
in ℂ. Its value at one is proved by reindexing its literal ordered partial
sums into Leibniz's series. No L-value evaluation is assumed.
-/
namespace DepthAspect.QuadraticCharacterValues
open scoped BigOperators Topology
open Filter OrderedDirichlet ImprimitiveCharacter ClassNumberGrowth

noncomputable def chiMinusFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

noncomputable def chiMinusEight : DirichletCharacter ℂ 8 :=
  ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

theorem chiMinusFour_odd : chiMinusFour.Odd := by
  change ((ZMod.χ₄ (-1) : ℤ) : ℂ) = -1
  have h : ZMod.χ₄ (-1) = -1 := by decide
  rw [h]
  norm_num

theorem chiMinusEight_odd : chiMinusEight.Odd := by
  change ((ZMod.χ₈' (-1) : ℤ) : ℂ) = -1
  have h : ZMod.χ₈' (-1) = -1 := by decide
  rw [h]
  norm_num

@[simp] theorem chiMinusFour_even (n : ℕ) : chiMinusFour (2 * n : ℕ) = 0 := by
  change ((ZMod.χ₄ (2 * n : ℕ) : ℤ) : ℂ) = 0
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  simp

@[simp] theorem chiMinusFour_odd_value (n : ℕ) :
    chiMinusFour (2 * n + 1 : ℕ) = (-1 : ℂ) ^ n := by
  change ((ZMod.χ₄ (2 * n + 1 : ℕ) : ℤ) : ℂ) = _
  rw [ZMod.χ₄_eq_neg_one_pow (by omega : (2 * n + 1) % 2 = 1)]
  have he : (2 * n + 1) / 2 = n := by omega
  rw [he]
  push_cast
  rfl

/-- Reindexing the actual first 2n character terms leaves exactly the n odd terms. -/
theorem partialL_chiMinusFour_even (n : ℕ) :
    partialL (fun j : ℕ => chiMinusFour (j : ZMod 4)) (2 * n) =
      ∑ j ∈ Finset.range n, (-1 : ℂ) ^ j / (2 * (j : ℂ) + 1) := by
  induction n with
  | zero => simp [partialL]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      partialL_succ, partialL_succ, ih, Finset.sum_range_succ]
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
      chiMinusFour_even, chiMinusFour_odd_value]
    push_cast
    ring

/-- The primitive modulus-four ordered L-value in equation (69). -/
theorem chiMinusFour_LAtOne :
    imprimitiveLAtOne chiMinusFour chiMinusFour_odd (by decide) 1 (by decide) =
      ((Real.pi / 4 : ℝ) : ℂ) := by
  have htwo : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn => by omega⟩
  have hL := (imprimitiveLAtOne_limit chiMinusFour chiMinusFour_odd
    (by decide) 1 (by decide)).comp htwo
  have hπ := (Complex.continuous_ofReal.tendsto (Real.pi / 4)).comp
    Real.tendsto_sum_pi_div_four
  have he : (fun n => partialL (psiNat chiMinusFour 1) (2 * n)) =
      (fun n => ((∑ j ∈ Finset.range n, (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) : ℝ) : ℂ)) := by
    funext n
    have hpsi : psiNat chiMinusFour 1 = (fun j : ℕ => chiMinusFour (j : ZMod 4)) :=
      funext (psiNat_conductor_one chiMinusFour)
    rw [hpsi, partialL_chiMinusFour_even]
    push_cast
    rfl
  change Tendsto (fun n => partialL (psiNat chiMinusFour 1) (2 * n)) atTop _ at hL
  rw [he] at hL
  have hvalue := tendsto_nhds_unique hL hπ
  simpa using hvalue

end DepthAspect.QuadraticCharacterValues
