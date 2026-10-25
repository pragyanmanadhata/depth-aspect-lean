import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic coefficients in equations (121)--(124)

The coefficient sequences below are actual arithmetic functions. In
particular the convolution giving (124) is proved by Möbius inversion,
rather than assumed from uniqueness of a Dirichlet series.
-/
namespace DepthAspect.ArithmeticWeights

open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable def denominator (p : ℕ) : ℝ := (p : ℝ) ^ 2 - p - 1

noncomputable def excludedFactor (ℓ p : ℕ) : ℝ :=
  if p = ℓ then 0 else 1 / denominator p

/-- The squarefree, coprime divisor weight in (121). -/
noncomputable def b (ℓ : ℕ) : ArithmeticFunction ℝ :=
  ((moebius : ArithmeticFunction ℝ).ppow 2).pmul
    (prodPrimeFactors (excludedFactor ℓ))

noncomputable def c (ℓ : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.id : ArithmeticFunction ℝ).pmul (b ℓ)

noncomputable def reciprocal : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)⁻¹, by simp⟩

@[simp] theorem reciprocal_apply (n : ℕ) : reciprocal n = (n : ℝ)⁻¹ := rfl

/-- The Möbius transform used to construct the coefficients of `Hℓ`.
Identifying every local value and proving the infinite product/series
convergence are separate obligations. -/
noncomputable def h (ℓ : ℕ) : ArithmeticFunction ℝ :=
  c ℓ * (moebius : ArithmeticFunction ℝ).pmul reciprocal

@[simp] theorem c_apply (ℓ n : ℕ) : c ℓ n = (n : ℝ) * b ℓ n := by
  simp [c]

theorem b_isMultiplicative (ℓ : ℕ) : (b ℓ).IsMultiplicative :=
  isMultiplicative_moebius.intCast.ppow.pmul
    (IsMultiplicative.prodPrimeFactors _)

theorem c_isMultiplicative (ℓ : ℕ) : (c ℓ).IsMultiplicative :=
  isMultiplicative_id.natCast.pmul (b_isMultiplicative ℓ)

theorem reciprocal_isMultiplicative : reciprocal.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n _
  simp only [reciprocal_apply, Nat.cast_mul, mul_inv_rev]
  ring

theorem h_isMultiplicative (ℓ : ℕ) : (h ℓ).IsMultiplicative :=
  (c_isMultiplicative ℓ).mul
    (isMultiplicative_moebius.intCast.pmul reciprocal_isMultiplicative)

@[simp] theorem b_one (ℓ : ℕ) : b ℓ 1 = 1 := (b_isMultiplicative ℓ).1
@[simp] theorem c_one (ℓ : ℕ) : c ℓ 1 = 1 := (c_isMultiplicative ℓ).1
@[simp] theorem h_one (ℓ : ℕ) : h ℓ 1 = 1 := (h_isMultiplicative ℓ).1

/-- Equality with the literal squarefree and coprimality expression in (121). -/
theorem b_formula {ℓ n : ℕ} (hℓ : ℓ.Prime) (hn : n ≠ 0) :
    b ℓ n = (moebius n : ℝ) ^ 2 * (if n.Coprime ℓ then 1 else 0) *
      ∏ p ∈ n.primeFactors, (1 / denominator p) := by
  simp only [b, pmul_apply, ppow_apply (by norm_num : 0 < 2), intCoe_apply,
    prodPrimeFactors_apply hn]
  by_cases hcop : n.Coprime ℓ
  · have hnot : ℓ ∉ n.primeFactors := by
      intro hmem
      exact (hℓ.coprime_iff_not_dvd.mp hcop.symm)
        (Nat.mem_primeFactors.mp hmem).2.1
    rw [if_pos hcop, mul_one]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    exact if_neg (by intro he; exact hnot (he ▸ hp))
  · rw [if_neg hcop, mul_zero, zero_mul]
    have hdiv : ℓ ∣ n := by
      by_contra hd
      exact hcop (hℓ.coprime_iff_not_dvd.mpr hd).symm
    have hmem := hℓ.mem_primeFactors hdiv hn
    have hp : (∏ p ∈ n.primeFactors, excludedFactor ℓ p) = 0 :=
      Finset.prod_eq_zero hmem (by simp [excludedFactor])
    rw [hp, mul_zero]

theorem denominator_pos {p : ℕ} (hp : p.Prime) : 0 < denominator p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  dsimp [denominator]
  nlinarith

theorem b_nonneg (ℓ n : ℕ) : 0 ≤ b ℓ n := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [b, pmul_apply, ppow_apply (by norm_num : 0 < 2), intCoe_apply,
    prodPrimeFactors_apply hn]
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro p hp
  unfold excludedFactor
  split_ifs
  · exact le_rfl
  · exact (one_div_pos.mpr (denominator_pos (Nat.prime_of_mem_primeFactors hp))).le

theorem c_nonneg (ℓ n : ℕ) : 0 ≤ c ℓ n := by
  rw [c_apply]
  exact mul_nonneg (Nat.cast_nonneg _) (b_nonneg ℓ n)

/-- The squarefree weight has no prime powers beyond the first. -/
theorem b_prime_power (ℓ : ℕ) {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) :
    b ℓ (p ^ j) = if j = 1 then excludedFactor ℓ p else 0 := by
  simp only [b, pmul_apply, ppow_apply (by norm_num : 0 < 2), intCoe_apply,
    prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hj hp,
    Finset.prod_singleton, moebius_apply_prime_pow hp hj]
  split_ifs <;> norm_num

/-- The full divisor sum is a product of the first local squarefree terms,
valid even when the original integer is not squarefree. -/
theorem b_mul_zeta (ℓ : ℕ) :
    b ℓ * (ζ : ArithmeticFunction ℝ) =
      prodPrimeFactors (fun p => 1 + excludedFactor ℓ p) := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((b_isMultiplicative ℓ).mul isMultiplicative_zeta.natCast) _
    (IsMultiplicative.prodPrimeFactors _)).mpr
  intro p i hp
  by_cases hi : i = 0
  · subst i
    simp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ', Finset.sum_range_succ',
    prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton]
  have hz : ∀ a : ℕ, b ℓ (p ^ (a + 1 + 1)) = 0 := by
    intro a
    rw [b_prime_power ℓ hp (by omega), if_neg (by omega)]
  simp only [hz, Finset.sum_const_zero, pow_zero, b_one]
  have hb := b_prime_power ℓ hp (by norm_num : (1 : ℕ) ≠ 0)
  have hb' : b ℓ p = excludedFactor ℓ p := by simpa using hb
  simp only [pow_one, hb', zero_add]
  ring

theorem b_divisor_sum {ℓ r : ℕ} (hr : r ≠ 0) :
    (∑ d ∈ r.divisors, b ℓ d) =
      ∏ p ∈ r.primeFactors, (1 + excludedFactor ℓ p) := by
  rw [← coe_mul_zeta_apply, b_mul_zeta, prodPrimeFactors_apply hr]

theorem c_prime (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    c ℓ p = (p : ℝ) * excludedFactor ℓ p := by
  rw [c_apply]
  have hb := b_prime_power ℓ hp (by norm_num : (1 : ℕ) ≠ 0)
  simpa using congrArg ((p : ℝ) * ·) hb

theorem c_prime_power_zero (ℓ : ℕ) {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    c ℓ (p ^ j) = 0 := by
  rw [c_apply, b_prime_power ℓ hp (by omega), if_neg (by omega), mul_zero]

/-- Removing the reciprocal-zeta factor is an actual prime-power
coefficient subtraction for the Möbius convolution. -/
theorem h_prime_power_recurrence (ℓ : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    h ℓ (p ^ (j + 1)) = c ℓ (p ^ (j + 1)) - c ℓ (p ^ j) / (p : ℝ) := by
  have hμ : ∀ i : ℕ, (moebius (p ^ (i + 1 + 1)) : ℝ) = 0 := by
    intro i
    rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega), Int.cast_zero]
  unfold h
  rw [mul_apply, Nat.sum_divisorsAntidiagonal'
    (fun x y => c ℓ x * ((moebius : ArithmeticFunction ℝ).pmul reciprocal) y),
    Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pmul_apply, intCoe_apply, reciprocal_apply, Nat.zero_add,
    pow_zero, pow_one,
    Nat.div_one, moebius_apply_one, Int.cast_one, Nat.cast_one, inv_one,
    mul_one, moebius_apply_prime hp, Int.cast_neg, hμ, zero_mul, mul_zero,
    Finset.sum_const_zero]
  rw [show p ^ (j + 1) / p = p ^ j by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]]
  ring

theorem h_prime (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    h ℓ p = (p : ℝ) * excludedFactor ℓ p - (p : ℝ)⁻¹ := by
  have ht := h_prime_power_recurrence ℓ hp 0
  simpa only [zero_add, pow_one, pow_zero, c_one, one_div, c_prime ℓ hp] using ht

theorem h_prime_square (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    h ℓ (p ^ 2) = -excludedFactor ℓ p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ht := h_prime_power_recurrence ℓ hp 1
  norm_num only [c_prime_power_zero ℓ hp (by norm_num : 2 ≤ 2), pow_one,
    c_prime ℓ hp] at ht
  rw [ht]
  field_simp
  ring

theorem h_prime_power_zero (ℓ : ℕ) {p j : ℕ} (hp : p.Prime) (hj : 3 ≤ j) :
    h ℓ (p ^ j) = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 3 + i = (2 + i) + 1 by omega, h_prime_power_recurrence ℓ hp,
    c_prime_power_zero ℓ hp (by omega), c_prime_power_zero ℓ hp (by omega)]
  simp

/-- Multiplication by `1/n` respects Dirichlet convolution. -/
theorem reciprocal_pmul_convolution (f g : ArithmeticFunction ℝ) :
    reciprocal.pmul (f * g) = (reciprocal.pmul f) * (reciprocal.pmul g) := by
  ext n
  simp only [pmul_apply, mul_apply, reciprocal_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xy hxy
  have hm : xy.1 * xy.2 = n := (Nat.mem_divisorsAntidiagonal.mp hxy).1
  have hcast : (n : ℝ) = (xy.1 : ℝ) * (xy.2 : ℝ) := by exact_mod_cast hm.symm
  rw [hcast, mul_inv_rev]
  ring

@[simp] theorem reciprocal_pmul_one : reciprocal.pmul (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases hn : n = 1 <;> simp [pmul_apply, one_apply, hn]

/-- The actual reciprocal sequence and its actual Möbius inverse. -/
theorem reciprocal_mul_moebius :
    reciprocal * (moebius : ArithmeticFunction ℝ).pmul reciprocal = 1 := by
  have ht := reciprocal_pmul_convolution (ζ : ArithmeticFunction ℝ)
    (moebius : ArithmeticFunction ℝ)
  rw [coe_zeta_mul_coe_moebius, reciprocal_pmul_one, pmul_zeta,
    pmul_comm reciprocal (moebius : ArithmeticFunction ℝ)] at ht
  exact ht.symm

/-- The coefficient identity used in equation (124). -/
theorem h_convolution_reciprocal (ℓ : ℕ) : h ℓ * reciprocal = c ℓ := by
  unfold h
  rw [mul_assoc, mul_comm ((moebius : ArithmeticFunction ℝ).pmul reciprocal) reciprocal,
    reciprocal_mul_moebius, mul_one]

/-- Literal finite antidiagonal form of that coefficient identity. -/
theorem c_divisor_sum (ℓ n : ℕ) :
    c ℓ n = ∑ ab ∈ n.divisorsAntidiagonal, h ℓ ab.1 / (ab.2 : ℝ) := by
  rw [← h_convolution_reciprocal ℓ, mul_apply]
  simp only [reciprocal_apply, div_eq_mul_inv]

/-- The two local coefficients obtained by removing the zeta factor. -/
theorem local_factor_identity (p : ℕ) (w : ℂ) :
    (1 + (((p : ℝ) / denominator p : ℝ) : ℂ) * w) *
      (1 - (((p : ℝ)⁻¹ : ℝ) : ℂ) * w) =
      1 + (((p : ℝ) / denominator p - (p : ℝ)⁻¹ : ℝ) : ℂ) * w -
        (((p : ℝ) / denominator p * (p : ℝ)⁻¹ : ℝ) : ℂ) * w ^ 2 := by
  push_cast
  ring

theorem second_local_coefficient {p : ℕ} (hp : p.Prime) :
    (p : ℝ) / denominator p * (p : ℝ)⁻¹ = 1 / denominator p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd := (denominator_pos hp).ne'
  field_simp

/-- The actual `hℓ` prime-power coefficients give precisely the two Euler
factors displayed in (122), with the exceptional factor at the omitted prime. -/
theorem h_local_factor (ℓ : ℕ) {p : ℕ} (hp : p.Prime) (w : ℂ) :
    1 + (h ℓ p : ℂ) * w + (h ℓ (p ^ 2) : ℂ) * w ^ 2 =
      if p = ℓ then 1 - (((p : ℝ)⁻¹ : ℝ) : ℂ) * w
      else (1 + (((p : ℝ) / denominator p : ℝ) : ℂ) * w) *
        (1 - (((p : ℝ)⁻¹ : ℝ) : ℂ) * w) := by
  rw [h_prime ℓ hp, h_prime_square ℓ hp]
  by_cases hpl : p = ℓ
  · simp only [excludedFactor, if_pos hpl, mul_zero, zero_sub, neg_zero,
      Complex.ofReal_neg, Complex.ofReal_zero, zero_mul, add_zero]
    ring
  · rw [if_neg hpl, local_factor_identity p w, second_local_coefficient hp]
    simp only [excludedFactor, if_neg hpl, mul_one_div]
    push_cast
    ring

theorem first_local_coefficient {p : ℕ} (hp : p.Prime) :
    (p : ℝ) / denominator p - (p : ℝ)⁻¹ =
      ((p : ℝ) + 1) / ((p : ℝ) * denominator p) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd := (denominator_pos hp).ne'
  field_simp [hp0, hd]
  unfold denominator
  ring

theorem first_local_coefficient_bound {p : ℕ} (hp : p.Prime) :
    |(p : ℝ) / denominator p - (p : ℝ)⁻¹| ≤ 6 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hd := denominator_pos hp
  rw [first_local_coefficient hp, abs_of_pos (by positivity)]
  apply (div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr
  dsimp [denominator]
  have hf : 0 ≤ (p : ℝ) * (p - 2) * (5 * p + 3) := by
    apply mul_nonneg
    · exact mul_nonneg hp0.le (by linarith)
    · linarith
  nlinarith [hf]

theorem second_local_coefficient_bound {p : ℕ} (hp : p.Prime) :
    |-(1 / denominator p)| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hd := denominator_pos hp
  rw [abs_neg, abs_of_pos (one_div_pos.mpr hd)]
  apply (div_le_div_iff₀ hd (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr
  dsimp [denominator]
  have hf : 0 ≤ ((p : ℝ) - 2) * (3 * p + 2) := mul_nonneg (by linarith) (by linarith)
  nlinarith [hf]

end DepthAspect.ArithmeticWeights
