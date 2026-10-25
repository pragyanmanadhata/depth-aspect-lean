import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# The convergent squarefree product in the coefficient tail (85)

The squarefree weight is the literal 1/(sqrt(u) φ(u)). It is reindexed by the
actual set of prime divisors, and bounded by the convergent finite-subset
expansion of the Euler product. No divisor-function growth estimate is needed
for this convergence argument.
-/
noncomputable section
open scoped BigOperators
open Finset
namespace DepthAspect.SquarefreeCoefficientProduct

/-- The nonzero factors of the exact product printed in (85). -/
def primeWeight (p : ℕ) : ℝ :=
  if p.Prime ∧ p ≠ 2 then 1 / (Real.sqrt p * ((p : ℝ) - 1)) else 0

theorem primeWeight_nonneg (p : ℕ) : 0 ≤ primeWeight p := by
  unfold primeWeight
  split_ifs with hp
  · have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
    exact one_div_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
  · rfl

theorem primeWeight_le (p : ℕ) : primeWeight p ≤ 2 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  unfold primeWeight
  split_ifs with hp
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have hpow : (p : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt p * p := by
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hp0,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [Real.rpow_neg hp0.le, hpow]
    apply (div_le_iff₀ (mul_pos hs (by linarith : 0 < (p : ℝ) - 1))).mpr
    have heq : 2 * (Real.sqrt p * p)⁻¹ * (Real.sqrt p * ((p : ℝ) - 1)) =
        2 * ((p : ℝ) - 1) / p := by field_simp <;> ring
    rw [heq]
    apply (le_div_iff₀ hp0).mpr
    nlinarith
  · positivity

theorem primeWeight_summable : Summable primeWeight := by
  apply Summable.of_nonneg_of_le primeWeight_nonneg primeWeight_le
  exact (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 2

/-- Finite-subset expansion of the actual convergent prime product. -/
theorem finite_products_summable : Summable (fun s : Finset ℕ => ∏ p ∈ s, primeWeight p) :=
  summable_finsetProd_of_summable_nonneg primeWeight_nonneg primeWeight_summable

def productConstant : ℝ := ∏' p : ℕ, (1 + primeWeight p)

theorem productConstant_eq_sum : productConstant =
    ∑' s : Finset ℕ, ∏ p ∈ s, primeWeight p :=
  tprod_one_add finite_products_summable

theorem product_multipliable : Multipliable (fun p : ℕ => 1 + primeWeight p) :=
  multipliable_one_add_of_summable_prod finite_products_summable

theorem productConstant_eq_odd_primes : productConstant =
    ∏' p : {p : ℕ // p.Prime ∧ p ≠ 2},
      (1 + 1 / (Real.sqrt (p : ℕ) * (((p : ℕ) : ℝ) - 1))) := by
  rw [productConstant, ← tprod_subtype_eq_of_mulSupport_subset
    (s := {p : ℕ | p.Prime ∧ p ≠ 2})]
  · apply tprod_congr
    intro p
    have hp : (p : ℕ).Prime ∧ (p : ℕ) ≠ 2 := p.property
    simp only [primeWeight, if_pos hp]
  · intro p hp
    by_contra hn
    have hnot : ¬ (p.Prime ∧ p ≠ 2) := hn
    exact hp (by simp only [primeWeight, if_neg hnot, add_zero])

/-- The finite set of prime factors determines a squarefree integer. -/
theorem primeFactors_injective :
    Function.Injective (fun u : {u : ℕ // Squarefree u ∧ Odd u} => u.val.primeFactors) := by
  intro u v h
  change u.val.primeFactors = v.val.primeFactors at h
  apply Subtype.ext
  calc
    u.val = ∏ p ∈ u.val.primeFactors, p := (Nat.prod_primeFactors_of_squarefree u.property.1).symm
    _ = ∏ p ∈ v.val.primeFactors, p := by rw [h]
    _ = v.val := Nat.prod_primeFactors_of_squarefree v.property.1

theorem totient_squarefree {u : ℕ} (hu : Squarefree u) :
    u.totient = ∏ p ∈ u.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors u
  rw [Nat.prod_primeFactors_of_squarefree hu] at h
  apply mul_right_cancel₀ hu.ne_zero
  simpa only [mul_comm] using h

private theorem sqrt_prod (s : Finset ℕ) :
    Real.sqrt ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, Real.sqrt p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg p), ih]

/-- The literal squarefree weight equals the product of its actual local factors. -/
theorem squarefree_weight_eq_product (u : {u : ℕ // Squarefree u ∧ Odd u}) :
    1 / (Real.sqrt (u : ℕ) * ((u : ℕ).totient : ℝ)) =
      ∏ p ∈ (u : ℕ).primeFactors, primeWeight p := by
  have hu := u.property.1
  have ho := u.property.2
  have hprime (p : ℕ) (hp : p ∈ (u : ℕ).primeFactors) : p.Prime ∧ p ≠ 2 := by
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    intro heq
    have hd := Nat.dvd_of_mem_primeFactors hp
    rw [heq] at hd
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
  calc
    _ = 1 / ((∏ p ∈ (u : ℕ).primeFactors, Real.sqrt p) *
        ∏ p ∈ (u : ℕ).primeFactors, ((p : ℝ) - 1)) := by
      congr 2
      · rw [← sqrt_prod, Nat.prod_primeFactors_of_squarefree hu]
      · rw [totient_squarefree hu, Nat.cast_prod]
        apply Finset.prod_congr rfl
        intro p hp
        simpa only [Nat.cast_one] using
          (Nat.cast_sub (R := ℝ) (hprime p hp).1.one_lt.le)
    _ = ∏ p ∈ (u : ℕ).primeFactors,
        1 / (Real.sqrt p * ((p : ℝ) - 1)) := by
      rw [← Finset.prod_mul_distrib]
      simp only [one_div, Finset.prod_inv_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [primeWeight, if_pos (hprime p hp)]

/-- Absolute summability of the squarefree series entering (85). -/
theorem squarefree_weight_summable :
    Summable (fun u : {u : ℕ // Squarefree u ∧ Odd u} =>
      1 / (Real.sqrt (u : ℕ) * ((u : ℕ).totient : ℝ))) := by
  have h := finite_products_summable.comp_injective primeFactors_injective
  simpa only [Function.comp_def, squarefree_weight_eq_product] using h

/-- The exact product in the paper bounds the squarefree coefficient sum. -/
theorem squarefree_weight_sum_le :
    (∑' u : {u : ℕ // Squarefree u ∧ Odd u},
      1 / (Real.sqrt (u : ℕ) * ((u : ℕ).totient : ℝ))) ≤ productConstant := by
  rw [productConstant_eq_sum]
  have h := tsum_comp_le_tsum_of_inj finite_products_summable
    (fun s => Finset.prod_nonneg fun p _ => primeWeight_nonneg p) primeFactors_injective
  simpa only [Function.comp_def, squarefree_weight_eq_product] using h

end DepthAspect.SquarefreeCoefficientProduct
