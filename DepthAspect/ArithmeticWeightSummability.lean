import DepthAspect.ArithmeticWeights
import DepthAspect.EulerCoefficientSummability
import Mathlib.Analysis.PSeries

/-! Absolute convergence of the actual `hℓ` coefficients in Lemma 6.2. -/
namespace DepthAspect.ArithmeticWeights

open scoped BigOperators

noncomputable def weightedAbs (ℓ : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  |h ℓ n| * (n : ℝ) ^ σ

@[simp] theorem weightedAbs_zero (ℓ : ℕ) (σ : ℝ) : weightedAbs ℓ σ 0 = 0 := by
  simp [weightedAbs]

@[simp] theorem weightedAbs_one (ℓ : ℕ) (σ : ℝ) : weightedAbs ℓ σ 1 = 1 := by
  simp [weightedAbs]

theorem weightedAbs_nonneg (ℓ : ℕ) (σ : ℝ) (n : ℕ) : 0 ≤ weightedAbs ℓ σ n := by
  exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem weightedAbs_mul (ℓ : ℕ) (σ : ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    weightedAbs ℓ σ (m * n) = weightedAbs ℓ σ m * weightedAbs ℓ σ n := by
  simp only [weightedAbs, (h_isMultiplicative ℓ).2 hmn, abs_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem weightedAbs_prime_power_zero (ℓ : ℕ) (σ : ℝ) {p j : ℕ}
    (hp : p.Prime) (hj : 3 ≤ j) : weightedAbs ℓ σ (p ^ j) = 0 := by
  simp only [weightedAbs, h_prime_power_zero ℓ hp hj, abs_zero, zero_mul]

theorem weightedAbs_local_summable (ℓ : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖weightedAbs ℓ σ (p ^ j)‖) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro j hj
  rw [weightedAbs_prime_power_zero ℓ σ hp (by simpa only [Finset.mem_range, not_lt] using hj),
    norm_zero]

theorem weightedAbs_local_sum (ℓ : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, weightedAbs ℓ σ (p ^ j)) =
      1 + weightedAbs ℓ σ p + weightedAbs ℓ σ (p ^ 2) := by
  have ht : (∑' j : ℕ, weightedAbs ℓ σ (p ^ j)) =
      ∑ j ∈ Finset.range 3, weightedAbs ℓ σ (p ^ j) := by
    apply tsum_eq_sum
    intro j hj
    exact weightedAbs_prime_power_zero ℓ σ hp
      (by simpa only [Finset.mem_range, not_lt] using hj)
  rw [ht]
  norm_num [Finset.sum_range_succ]

theorem coefficient_square_bound (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    |h ℓ (p ^ 2)| ≤ 4 / (p : ℝ) ^ 2 := by
  rw [h_prime_square ℓ hp]
  unfold excludedFactor
  split_ifs
  · simp only [neg_zero, abs_zero]
    positivity
  · exact second_local_coefficient_bound hp

/-- A uniform bound for the first nonconstant local term. The omitted
prime contributes a single harmless exceptional term. -/
theorem weightedAbs_prime_bound (ℓ : ℕ) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1 / 2)
    {p : ℕ} (hp : p.Prime) :
    weightedAbs ℓ σ p ≤ (if p = ℓ then 1 else 0) + 6 * (p : ℝ) ^ (-2 + 2 * σ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  by_cases hpl : p = ℓ
  · have hid : weightedAbs ℓ σ p = (p : ℝ) ^ (σ - 1) := by
      simp only [weightedAbs, h_prime ℓ hp, excludedFactor, if_pos hpl, mul_zero,
        zero_sub, abs_neg, abs_of_pos (inv_pos.mpr hp0)]
      rw [Real.rpow_sub hp0, Real.rpow_one]
      ring
    rw [hid, if_pos hpl]
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith : σ - 1 ≤ 0)
    have hx : 0 ≤ 6 * (p : ℝ) ^ (-2 + 2 * σ) := by positivity
    linarith
  · have hc : |h ℓ p| ≤ 6 / (p : ℝ) ^ 2 := by
      simpa only [h_prime ℓ hp, excludedFactor, if_neg hpl, mul_one_div] using
        first_local_coefficient_bound hp
    rw [if_neg hpl, zero_add]
    unfold weightedAbs
    calc
      _ ≤ (6 / (p : ℝ) ^ 2) * (p : ℝ) ^ σ :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 6 * (p : ℝ) ^ (-2 + σ) := by
        rw [show (-2 : ℝ) + σ = σ - 2 by ring, Real.rpow_sub hp0, Real.rpow_two]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)) (by norm_num)

theorem weightedAbs_prime_square_bound (ℓ : ℕ) (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    weightedAbs ℓ σ (p ^ 2) ≤ 4 * (p : ℝ) ^ (-2 + 2 * σ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold weightedAbs
  calc
    _ ≤ (4 / (p : ℝ) ^ 2) * ((p ^ 2 : ℕ) : ℝ) ^ σ :=
      mul_le_mul_of_nonneg_right (coefficient_square_bound ℓ hp) (by positivity)
    _ = 4 * (p : ℝ) ^ (-2 + 2 * σ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0.le, Nat.cast_ofNat,
        show (-2 : ℝ) + 2 * σ = 2 * σ - 2 by ring,
        Real.rpow_sub hp0, Real.rpow_two]
      ring

noncomputable def localMajorant (ℓ : ℕ) (σ : ℝ) (p : ℕ) : ℝ :=
  (if p = ℓ then 1 else 0) + 10 * (p : ℝ) ^ (-2 + 2 * σ)

theorem localMajorant_nonneg (ℓ : ℕ) (σ : ℝ) (p : ℕ) : 0 ≤ localMajorant ℓ σ p := by
  unfold localMajorant
  split_ifs <;> positivity

theorem localMajorant_summable (ℓ : ℕ) {σ : ℝ} (hσ : σ < 1 / 2) :
    Summable (localMajorant ℓ σ) := by
  have hi : Summable (fun p : ℕ => if p = ℓ then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {ℓ})
    intro p hp
    exact if_neg (by simpa only [Finset.mem_singleton] using hp)
  have hp := (Real.summable_nat_rpow.mpr (show -2 + 2 * σ < -1 by linarith)).mul_left 10
  exact hi.add hp

/-- Lemma 6.2's weighted absolute convergence throughout the required
half-plane; in particular σ=3/8 gives the stated coefficient moment. -/
theorem weightedAbs_summable (ℓ : ℕ) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1 / 2) :
    Summable (weightedAbs ℓ σ) := by
  apply EulerCoefficientSummability.summable_of_local_majorant
    (weightedAbs_zero ℓ σ) (weightedAbs_one ℓ σ) (weightedAbs_nonneg ℓ σ)
    (weightedAbs_mul ℓ σ) (weightedAbs_local_summable ℓ σ)
    (localMajorant_nonneg ℓ σ) (localMajorant_summable ℓ hσ1)
  intro p hp
  rw [weightedAbs_local_sum ℓ σ hp]
  have h₁ := weightedAbs_prime_bound ℓ hσ0 hσ1 hp
  have h₂ := weightedAbs_prime_square_bound ℓ σ hp
  dsimp [localMajorant]
  linarith

/-- The exact weighted absolute summability asserted after (122). -/
theorem coefficient_three_eighth_moment (ℓ : ℕ) :
    Summable (fun n : ℕ => |h ℓ n| * (n : ℝ) ^ (3 / 8 : ℝ)) :=
  weightedAbs_summable ℓ (by norm_num) (by norm_num)

end DepthAspect.ArithmeticWeights
