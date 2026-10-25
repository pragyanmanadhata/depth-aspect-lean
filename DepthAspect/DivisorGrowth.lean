import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp

/-!
# The actual divisor-function bound used in (97)

For every δ>0 an explicit finite product bounds τ(n)/n^δ uniformly. The
small-prime factors bound the complete geometric derivative series, so no
supremum existence or divisor-growth theorem is assumed.
-/

noncomputable section
open scoped BigOperators
namespace DepthAspect.DivisorGrowth

 def threshold (δ : ℝ) : ℝ := (2 : ℝ) ^ δ⁻¹
 def smallPrimes (δ : ℝ) : Finset ℕ := ⌈threshold δ⌉₊.primesBelow
 def localConstant (δ : ℝ) (p : ℕ) : ℝ := 1 / (1 - (p : ℝ) ^ (-δ)) ^ 2
 def boundConstant (δ : ℝ) : ℝ := ∏ p ∈ smallPrimes δ, localConstant δ p

 theorem mem_smallPrimes (δ : ℝ) (p : ℕ) :
    p ∈ smallPrimes δ ↔ p.Prime ∧ (p : ℝ) < threshold δ := by
  simp only [smallPrimes, Nat.mem_primesBelow, Nat.lt_ceil, and_comm]

 theorem succ_le_two_pow (j : ℕ) : (j : ℝ) + 1 ≤ (2 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith

 theorem localConstant_hasSum {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) * ((p : ℝ) ^ (-δ)) ^ j)
      (localConstant δ p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : 0 ≤ (p : ℝ) ^ (-δ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hr1 : (p : ℝ) ^ (-δ) < 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_lt hp1 (neg_lt_zero.mpr hδ)
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := (p : ℝ) ^ (-δ)) 1
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
  simpa [localConstant] using h

 theorem localConstant_one_le {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : p.Prime) :
    1 ≤ localConstant δ p := by
  have hs := localConstant_hasSum hδ hp
  have h := hs.summable.sum_le_tsum {0} (fun j _ => by positivity)
  simpa only [Finset.sum_singleton, Nat.cast_zero, zero_add, one_mul, pow_zero,
    hs.tsum_eq] using h

 theorem local_prime_power_bound {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (j : ℝ) + 1 ≤ localConstant δ p * ((p : ℝ) ^ δ) ^ j := by
  have hs := localConstant_hasSum hδ hp
  have h := hs.summable.sum_le_tsum {j} (fun k _ => by positivity)
  rw [Finset.sum_singleton, hs.tsum_eq, Real.rpow_neg (Nat.cast_nonneg p), inv_pow,
    ← div_eq_mul_inv] at h
  exact (div_le_iff₀ (pow_pos (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) δ) j)).mp h

 theorem large_prime_power_bound {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : p.Prime)
    (hlarge : threshold δ ≤ (p : ℝ)) (j : ℕ) :
    (j : ℝ) + 1 ≤ ((p : ℝ) ^ δ) ^ j := by
  have htwo : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) δ⁻¹) hlarge hδ.le
    simpa only [threshold, Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 2) hδ.ne'] using h
  exact (succ_le_two_pow j).trans (pow_le_pow_left₀ (by norm_num) htwo j)

 theorem boundConstant_one_le {δ : ℝ} (hδ : 0 < δ) : 1 ≤ boundConstant δ := by
  apply Finset.one_le_prod
  intro p hp
  exact localConstant_one_le hδ ((mem_smallPrimes δ p).mp hp).1

 theorem boundConstant_pos {δ : ℝ} (hδ : 0 < δ) : 0 < boundConstant δ :=
  zero_lt_one.trans_le (boundConstant_one_le hδ)

/-- The paper's elementary subpower estimate for the literal number of
positive divisors. The constant is independent of n. -/
theorem divisors_card_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    (n.divisors.card : ℝ) ≤ boundConstant δ * (n : ℝ) ^ δ := by
  classical
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hδ.ne']
  let S := n.primeFactors.filter (fun p : ℕ => (p : ℝ) < threshold δ)
  have hloc (p : ℕ) (hp : p ∈ n.primeFactors) :
      ((n.factorization p : ℝ) + 1) ≤
        (if (p : ℝ) < threshold δ then localConstant δ p else 1) *
          ((p : ℝ) ^ δ) ^ n.factorization p := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    split_ifs with hs
    · exact local_prime_power_bound hδ hprime _
    · simpa only [one_mul] using
        large_prime_power_bound hδ hprime (le_of_not_gt hs) _
  have hS : S ⊆ smallPrimes δ := by
    intro p hp
    obtain ⟨hp, hsmall⟩ := Finset.mem_filter.mp hp
    exact (mem_smallPrimes δ p).mpr ⟨Nat.prime_of_mem_primeFactors hp, hsmall⟩
  have hconstants : (∏ p ∈ S, localConstant δ p) ≤ boundConstant δ := by
    apply Finset.prod_le_prod_of_subset_of_one_le hS
    · intro p hp
      exact zero_le_one.trans (localConstant_one_le hδ
        (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
    · intro p hp hnot
      exact localConstant_one_le hδ ((mem_smallPrimes δ p).mp hp).1
  have hpower : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ δ) ^ n.factorization p) =
      (n : ℝ) ^ δ := by
    simp_rw [Real.rpow_pow_comm (Nat.cast_nonneg _) δ]
    rw [Real.finsetProd_rpow _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_one]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if (p : ℝ) < threshold δ then localConstant δ p else 1) *
          ((p : ℝ) ^ δ) ^ n.factorization p :=
      Finset.prod_le_prod (fun p hp => by positivity) hloc
    _ = (∏ p ∈ S, localConstant δ p) * (n : ℝ) ^ δ := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter, hpower]
    _ ≤ boundConstant δ * (n : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_right hconstants (Real.rpow_nonneg (Nat.cast_nonneg n) δ)

/-- The final simplification in (97), ready to apply to the actual Fourier
bound after its local strata have been proved. -/
theorem four_divisors_sqrt_le {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) :
    4 * (n.divisors.card : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) ≤
      (4 * boundConstant δ) * (n : ℝ) ^ (1 / 2 + δ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ 4 * (boundConstant δ * (n : ℝ) ^ δ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (divisors_card_le hδ n)
        (by norm_num)) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [Real.rpow_add hn0]; ring

end DepthAspect.DivisorGrowth
