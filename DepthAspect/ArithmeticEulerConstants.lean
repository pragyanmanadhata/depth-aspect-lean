import DepthAspect.ArithmeticWeights
import DepthAspect.EulerCoefficientSummability
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The actual arithmetic Euler product in (121)

The normalization constant is defined by its stated prime product. Its
convergence, positivity, and inverse divisor sum are derived from the actual
squarefree coefficients, rather than supplied as hypotheses.
-/
namespace DepthAspect.ArithmeticWeights

open ArithmeticFunction
open scoped BigOperators Topology

noncomputable def baseFactor (p : ℕ) : ℝ := 1 - 1 / ((p : ℝ) * (p - 1))
noncomputable def omittedBaseFactor (ℓ p : ℕ) : ℝ := if p = ℓ then 1 else baseFactor p
noncomputable def B (ℓ : ℕ) : ℝ := ∏' p : Nat.Primes, omittedBaseFactor ℓ p

theorem b_local_sum (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, b ℓ (p ^ j)) = 1 + excludedFactor ℓ p := by
  rw [tsum_eq_sum (s := Finset.range 2) (fun j hj => by
    rw [b_prime_power ℓ hp (by simp only [Finset.mem_range] at hj; omega),
      if_neg (by simp only [Finset.mem_range] at hj; omega)])]
  have hb : b ℓ p = excludedFactor ℓ p := by
    simpa using b_prime_power ℓ hp (by norm_num : (1 : ℕ) ≠ 0)
  norm_num [Finset.sum_range_succ, hb]

theorem b_local_summable (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖b ℓ (p ^ j)‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range 2)
  intro j hj
  rw [b_prime_power ℓ hp (by simp only [Finset.mem_range] at hj; omega),
    if_neg (by simp only [Finset.mem_range] at hj; omega), norm_zero]

theorem excludedFactor_bound (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    excludedFactor ℓ p ≤ 4 * (p : ℝ) ^ (-2 : ℝ) := by
  have hc := second_local_coefficient_bound hp
  rw [abs_neg, abs_of_pos (one_div_pos.mpr (denominator_pos hp))] at hc
  unfold excludedFactor
  split_ifs
  · positivity
  · simpa only [Real.rpow_neg (Nat.cast_nonneg p), Real.rpow_two, div_eq_mul_inv] using hc

theorem b_summable (ℓ : ℕ) : Summable (fun n : ℕ => b ℓ n) := by
  apply EulerCoefficientSummability.summable_of_local_majorant
    (by simp) (b_one ℓ) (b_nonneg ℓ) (b_isMultiplicative ℓ).2
    (b_local_summable ℓ) (g := fun p : ℕ => 4 * (p : ℝ) ^ (-2 : ℝ))
    (fun p => by positivity)
    ((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).mul_left 4)
  intro p hp
  rw [b_local_sum ℓ hp]
  exact add_le_add le_rfl (excludedFactor_bound ℓ hp)

theorem b_tsum_ge_one (ℓ : ℕ) : 1 ≤ ∑' n : ℕ, b ℓ n := by
  simpa only [b_one] using (b_summable ℓ).le_tsum 1 (fun n _ => b_nonneg ℓ n)

theorem b_euler_product (ℓ : ℕ) :
    HasProd (fun p : Nat.Primes => 1 + excludedFactor ℓ p) (∑' n : ℕ, b ℓ n) := by
  have hnorm : Summable (fun n : ℕ => ‖b ℓ n‖) := by
    simpa only [Real.norm_of_nonneg (b_nonneg ℓ _)] using b_summable ℓ
  have ht := (b_isMultiplicative ℓ).eulerProduct_hasProd hnorm
  simpa only [b_local_sum ℓ (Subtype.property _)] using ht

theorem inverse_local_factor (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    (1 + excludedFactor ℓ p)⁻¹ = omittedBaseFactor ℓ p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hd := (denominator_pos hp).ne'
  by_cases hpl : p = ℓ
  · simp [excludedFactor, omittedBaseFactor, hpl]
  · simp only [excludedFactor, omittedBaseFactor, if_neg hpl]
    have hsum : 1 + 1 / denominator p =
        ((p : ℝ) * ((p : ℝ) - 1)) / denominator p := by
      field_simp [hd]
      unfold denominator
      ring
    rw [hsum, inv_div]
    unfold baseFactor
    field_simp [hp0, hp1]
    unfold denominator
    ring

/-- Inversion is applied only after proving that the sum is at least one,
so the zero-limit caveat for products in a field is handled explicitly. -/
theorem base_euler_product (ℓ : ℕ) :
    HasProd (fun p : Nat.Primes => omittedBaseFactor ℓ p)
      (∑' n : ℕ, b ℓ n)⁻¹ := by
  have ht := b_euler_product ℓ
  have hn : (∑' n : ℕ, b ℓ n) ≠ 0 := by have := b_tsum_ge_one ℓ; linarith
  unfold HasProd at ht ⊢
  have hi := ht.inv₀ hn
  simpa only [← Finset.prod_inv_distrib, inverse_local_factor ℓ (Subtype.property _)] using hi

theorem B_eq_inverse_sum (ℓ : ℕ) : B ℓ = (∑' n : ℕ, b ℓ n)⁻¹ :=
  (base_euler_product ℓ).tprod_eq

theorem B_pos (ℓ : ℕ) : 0 < B ℓ := by
  rw [B_eq_inverse_sum]
  exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (b_tsum_ge_one ℓ))

/-- The value at zero in (121), using its actual infinite divisor sum. -/
theorem zero_weight_normalization (ℓ : ℕ) : B ℓ * (∑' n : ℕ, b ℓ n) = 1 := by
  rw [B_eq_inverse_sum]
  exact inv_mul_cancel₀ (by have := b_tsum_ge_one ℓ; linarith)

end DepthAspect.ArithmeticWeights
