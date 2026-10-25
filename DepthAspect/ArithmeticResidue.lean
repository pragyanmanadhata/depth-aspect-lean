import DepthAspect.ArithmeticEulerConstants
import DepthAspect.ArithmeticSummatoryLimit
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! Multiplication of the actual local factors in the final line of (123). -/
namespace DepthAspect.ArithmeticWeights

open scoped BigOperators Topology

noncomputable def inverseSquare : ℕ →*₀ ℝ where
  toFun n := ((n : ℝ) ^ 2)⁻¹
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by simp [Nat.cast_mul, mul_pow, mul_inv_rev, mul_comm]

/-- Euler's actual ζ(2) product, expressed over real primes. -/
theorem inverse_square_euler_product :
    HasProd (fun p : Nat.Primes => (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) (Real.pi ^ 2 / 6) := by
  have hs : Summable (fun n : ℕ => ‖inverseSquare n‖) := by
    have he : (fun n : ℕ => ‖inverseSquare n‖) = fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
      funext n
      change |((n : ℝ) ^ 2)⁻¹| = ((n : ℝ) ^ 2)⁻¹
      exact abs_of_nonneg (by positivity)
    rw [he]
    simpa only [one_div] using hasSum_zeta_two.summable
  have ht := EulerProduct.eulerProduct_completely_multiplicative_hasProd hs
  change HasProd (fun p : Nat.Primes => (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹)
    (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) at ht
  simpa only [← one_div, hasSum_zeta_two.tsum_eq] using ht

/-- Inversion is justified by the nonzero value of ζ(2). -/
theorem square_euler_product :
    HasProd (fun p : Nat.Primes => 1 - ((p : ℝ) ^ 2)⁻¹) (6 / Real.pi ^ 2) := by
  have ht := inverse_square_euler_product
  have hn : Real.pi ^ 2 / 6 ≠ 0 := by positivity
  unfold HasProd at ht ⊢
  have hi := ht.inv₀ hn
  simpa only [← Finset.prod_inv_distrib, inv_inv, inv_div, inv_pow] using hi

/-- Actual real local coefficient sum for Hℓ(0). -/
theorem h_real_local_sum (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, h ℓ (p ^ j)) = 1 + ((p : ℝ) - 1) * excludedFactor ℓ p - (p : ℝ)⁻¹ := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun j hj =>
    h_prime_power_zero ℓ hp (by simpa only [Finset.mem_range, not_lt] using hj))]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
    zero_add, h_one, h_prime ℓ hp, h_prime_square ℓ hp]
  ring

/-- The literal Bℓ factor times the literal Hℓ(0) factor simplifies as claimed. -/
theorem combined_local_factor (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    omittedBaseFactor ℓ p * (1 + ((p : ℝ) - 1) * excludedFactor ℓ p - (p : ℝ)⁻¹) =
      if p = ℓ then 1 - (p : ℝ)⁻¹ else 1 - ((p : ℝ) ^ 2)⁻¹ := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hd := (denominator_pos hp).ne'
  by_cases hpl : p = ℓ
  · simp [omittedBaseFactor, excludedFactor, hpl]
  · simp only [omittedBaseFactor, excludedFactor, if_neg hpl]
    unfold baseFactor denominator at *
    have hcancel : ((p : ℝ) ^ 2 - p - 1) * ((p : ℝ) ^ 2 - p - 1)⁻¹ = 1 :=
      mul_inv_cancel₀ hd
    field_simp [hp0, hp1, hd]
    linear_combination (p : ℝ) * ((p : ℝ) - 1) * hcancel

/-- The actual product Bℓ Rℓ, before evaluating its remaining elementary
prime product. -/
theorem B_R_euler_product (ℓ : ℕ) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) = ℓ then 1 - (p : ℝ)⁻¹ else
      1 - ((p : ℝ) ^ 2)⁻¹) (B ℓ * R ℓ) := by
  have hb : HasProd (fun p : Nat.Primes => omittedBaseFactor ℓ p) (B ℓ) := by
    rw [B_eq_inverse_sum]
    exact base_euler_product ℓ
  have hh := (h_isMultiplicative ℓ).eulerProduct_hasProd (by
    simpa only [Real.norm_eq_abs] using coefficient_abs_summable ℓ)
  have hm := hb.mul hh
  simpa only [h_real_local_sum ℓ (Subtype.property _), combined_local_factor ℓ (Subtype.property _), R]
    using hm

/-- Changing the single ℓ factor in Euler's ζ(2) product contributes exactly
ℓ/(ℓ+1), rather than an unspecified product constant. -/
theorem modified_square_euler_product {ℓ : ℕ} (hℓ : ℓ.Prime) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) = ℓ then 1 - (p : ℝ)⁻¹ else
      1 - ((p : ℝ) ^ 2)⁻¹) ((6 / Real.pi ^ 2) * ((ℓ : ℝ) / ((ℓ : ℝ) + 1))) := by
  classical
  have hs := hasProd_ite_eq (β := Nat.Primes) (⟨ℓ, hℓ⟩ : Nat.Primes) ((ℓ : ℝ) / ((ℓ : ℝ) + 1))
  have hm := square_euler_product.mul hs
  apply hm.congr_fun
  intro p
  by_cases hp : (p : ℕ) = ℓ
  · have hp' : p = (⟨ℓ, hℓ⟩ : Nat.Primes) := Subtype.ext hp
    rw [if_pos hp, if_pos hp']
    have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have hℓ1 : (ℓ : ℝ) + 1 ≠ 0 := by positivity
    rw [hp']
    simp only [Subtype.coe_mk]
    field_simp
    <;> ring
  · have hp' : p ≠ (⟨ℓ, hℓ⟩ : Nat.Primes) := fun h => hp (congrArg Subtype.val h)
    simp [hp, hp']

/-- The final normalization identity in (123), with ζ(2) evaluated. -/
theorem B_mul_R {ℓ : ℕ} (hℓ : ℓ.Prime) :
    B ℓ * R ℓ = 6 * (ℓ : ℝ) / (((ℓ : ℝ) + 1) * Real.pi ^ 2) := by
  have h := (B_R_euler_product ℓ).unique (modified_square_euler_product hℓ)
  rw [h]
  have hℓ1 : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, hℓ1]
  <;> ring

/-- The same normalization, in the paper's ζ(2) notation. -/
theorem B_mul_R_zeta {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ((B ℓ * R ℓ : ℝ) : ℂ) = (ℓ : ℂ) / (((ℓ : ℂ) + 1) * riemannZeta 2) := by
  rw [B_mul_R hℓ, riemannZeta_two]
  push_cast
  have hℓ1 : (ℓ : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (ℓ : ℝ) + 1 ≠ 0 by positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hℓ1, hpi]
  <;> ring

theorem R_pos {ℓ : ℕ} (hℓ : ℓ.Prime) : 0 < R ℓ := by
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  have hp : 0 < B ℓ * R ℓ := by rw [B_mul_R hℓ]; positivity
  exact (mul_pos_iff_of_pos_left (B_pos ℓ)).mp hp

end DepthAspect.ArithmeticWeights
