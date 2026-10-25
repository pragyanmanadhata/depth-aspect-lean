import DepthAspect.ArithmeticEulerConstants
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The literal arithmetic weight in (106) and (121)

The weight is defined by the actual omitted-prime product. Its divisor-sum
expansion is proved both at nonzero integers and at zero, where every
positive integer divides the index and absolute convergence is essential.
-/
namespace DepthAspect.ArithmeticWeights

open scoped BigOperators Topology
open Filter

noncomputable def primeWeight (ℓ r : ℕ) : ℝ :=
  ∏' p : Nat.Primes, if (p : ℕ) ∣ ℓ * r then 1 else baseFactor p

noncomputable def integerPrimeWeight (ℓ : ℕ) (r : ℤ) : ℝ :=
  primeWeight ℓ r.natAbs

@[simp] theorem primeWeight_zero (ℓ : ℕ) : primeWeight ℓ 0 = 1 := by
  simp [primeWeight]

@[simp] theorem integerPrimeWeight_zero (ℓ : ℕ) : integerPrimeWeight ℓ 0 = 1 := by
  simp [integerPrimeWeight]

@[simp] theorem integerPrimeWeight_neg (ℓ : ℕ) (r : ℤ) :
    integerPrimeWeight ℓ (-r) = integerPrimeWeight ℓ r := by
  simp [integerPrimeWeight]

theorem excludedFactor_nonneg (ℓ : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ excludedFactor ℓ p := by
  unfold excludedFactor
  split_ifs
  · exact le_rfl
  · exact (one_div_pos.mpr (denominator_pos hp)).le

/-- The finite correction product restores precisely those factors whose
prime divides the integer index. -/
theorem correction_hasProd (ℓ : ℕ) {r : ℕ} (hr : r ≠ 0) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ r then 1 + excludedFactor ℓ p else 1)
      (∏ p ∈ r.primeFactors, (1 + excludedFactor ℓ p)) := by
  classical
  have hc : HasProd
      (fun q : Nat.Primes => ∏ p ∈ r.primeFactors,
        if (q : ℕ) = p then 1 + excludedFactor ℓ p else 1)
      (∏ p ∈ r.primeFactors, (1 + excludedFactor ℓ p)) := by
    apply hasProd_prod
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have he : (fun q : Nat.Primes => if (q : ℕ) = p then 1 + excludedFactor ℓ p else 1) =
        (fun q : Nat.Primes => if q = (⟨p, hprime⟩ : Nat.Primes) then
          1 + excludedFactor ℓ p else 1) := by
      funext q
      by_cases hq : (q : ℕ) = p
      · have hq' : q = (⟨p, hprime⟩ : Nat.Primes) := Subtype.ext hq
        simp only [if_pos hq, if_pos hq']
      · have hq' : q ≠ (⟨p, hprime⟩ : Nat.Primes) := fun h => hq (congrArg Subtype.val h)
        simp only [if_neg hq, if_neg hq']
    rw [he]
    exact hasProd_ite_eq (β := Nat.Primes) (⟨p, hprime⟩ : Nat.Primes) (1 + excludedFactor ℓ p)
  convert hc using 1
  funext p
  rw [Finset.prod_ite_eq]
  have hm : (p : ℕ) ∈ r.primeFactors ↔ (p : ℕ) ∣ r := by
    exact ⟨fun h => (Nat.mem_primeFactors.mp h).2.1,
      fun h => (Subtype.property p).mem_primeFactors h hr⟩
  simp only [hm]

/-- Cancellation of one actual prime factor, including the excluded prime. -/
theorem prime_weight_local_factor {ℓ : ℕ} (hℓ : ℓ.Prime) (r : ℕ)
    (p : Nat.Primes) :
    omittedBaseFactor ℓ p * (if (p : ℕ) ∣ r then 1 + excludedFactor ℓ p else 1) =
      if (p : ℕ) ∣ ℓ * r then 1 else baseFactor p := by
  have hp := Subtype.property p
  by_cases hpl : (p : ℕ) = ℓ
  · subst ℓ
    simp [omittedBaseFactor, excludedFactor]
  have hnℓ : ¬ (p : ℕ) ∣ ℓ := by
    intro hd
    exact hpl ((hℓ.dvd_iff_eq hp.ne_one).mp hd).symm
  simp only [hp.dvd_mul, hnℓ, false_or]
  by_cases hd : (p : ℕ) ∣ r
  · simp only [if_pos hd]
    rw [← inverse_local_factor ℓ hp]
    exact inv_mul_cancel₀ (by have := excludedFactor_nonneg ℓ hp; linarith)
  · simp [hd, omittedBaseFactor, hpl]

/-- Convergence and the nonzero-index expansion in (121), before taking the
unique value of the infinite product. -/
theorem primeWeight_hasProd {ℓ r : ℕ} (hℓ : ℓ.Prime) (hr : r ≠ 0) :
    HasProd (fun p : Nat.Primes => if (p : ℕ) ∣ ℓ * r then 1 else baseFactor p)
      (B ℓ * ∑ d ∈ r.divisors, b ℓ d) := by
  have hb : HasProd (fun p : Nat.Primes => omittedBaseFactor ℓ p) (B ℓ) := by
    rw [B_eq_inverse_sum]
    exact base_euler_product ℓ
  have ht := hb.mul (correction_hasProd ℓ hr)
  simpa only [prime_weight_local_factor hℓ r, b_divisor_sum hr] using ht

theorem primeWeight_divisor_sum {ℓ r : ℕ} (hℓ : ℓ.Prime) (hr : r ≠ 0) :
    primeWeight ℓ r = B ℓ * ∑ d ∈ r.divisors, b ℓ d :=
  (primeWeight_hasProd hℓ hr).tprod_eq

/-- The defining prime product agrees with the product over primes not
covering the integer ℓr, including negative and zero trace indices. -/
theorem integerPrimeWeight_product (ℓ : ℕ) (r : ℤ) :
    integerPrimeWeight ℓ r =
      ∏' p : Nat.Primes, if ((p : ℕ) : ℤ) ∣ (ℓ : ℤ) * r then 1 else baseFactor p := by
  unfold integerPrimeWeight primeWeight
  congr 1
  funext p
  simp only [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]

/-- The factor in the defining product written exactly in the rational
form displayed in (106). -/
theorem baseFactor_rational {p : ℕ} (hp : p.Prime) :
    baseFactor p = ((p : ℝ) ^ 2 - p - 1) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold baseFactor
  field_simp [hp0, hp1] <;> ring

/-- The literal omitted-prime product in (106), at every integer index. -/
theorem integerPrimeWeight_rational_product (ℓ : ℕ) (r : ℤ) :
    integerPrimeWeight ℓ r =
      ∏' p : Nat.Primes, if ((p : ℕ) : ℤ) ∣ (ℓ : ℤ) * r then 1 else
        ((p : ℝ) ^ 2 - p - 1) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [integerPrimeWeight_product]
  congr 1
  funext p
  split_ifs
  · rfl
  · exact baseFactor_rational p.property

/-- Multiplying the index by a power of the omitted prime does not
change any factor of the defining product. -/
theorem primeWeight_omitted_pow_mul (ℓ a r : ℕ) :
    primeWeight ℓ (ℓ ^ a * r) = primeWeight ℓ r := by
  unfold primeWeight
  congr 1
  funext p
  have hp := p.property
  have he : (p : ℕ) ∣ ℓ * (ℓ ^ a * r) ↔ (p : ℕ) ∣ ℓ * r := by
    simp only [hp.dvd_mul]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inl (hp.dvd_of_dvd_pow h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  simp only [he]

/-- The invariance G_t=G_r in the prime main term also holds at zero and
negative trace indices, through the literal arithmetic product. -/
theorem integerPrimeWeight_omitted_pow_mul (ℓ a : ℕ) (r : ℤ) :
    integerPrimeWeight ℓ ((ℓ : ℤ) ^ a * r) = integerPrimeWeight ℓ r := by
  unfold integerPrimeWeight
  rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, primeWeight_omitted_pow_mul]

/-- The full positive-divisor coefficient at an integer trace. -/
noncomputable def divisorCoefficient (ℓ : ℕ) (r : ℤ) (d : ℕ) : ℝ :=
  if 0 < d ∧ (d : ℤ) ∣ r then b ℓ d else 0

theorem divisorCoefficient_summable (ℓ : ℕ) (r : ℤ) :
    Summable (divisorCoefficient ℓ r) := by
  apply Summable.of_nonneg_of_le
    (f := fun d => b ℓ d) (g := divisorCoefficient ℓ r)
    (fun d => by
      dsimp [divisorCoefficient]
      split_ifs
      · exact b_nonneg ℓ d
      · exact le_rfl)
  · intro d
    unfold divisorCoefficient
    split_ifs
    · exact le_rfl
    · exact b_nonneg ℓ d
  · exact b_summable ℓ

/-- At every nonzero integer the infinite positive-divisor sum reduces to
its actual finite natural divisor set. -/
theorem divisorCoefficient_tsum {ℓ : ℕ} {r : ℤ} (hr : r ≠ 0) :
    (∑' d : ℕ, divisorCoefficient ℓ r d) = ∑ d ∈ r.natAbs.divisors, b ℓ d := by
  classical
  have habs : r.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hr
  rw [tsum_eq_sum (s := r.natAbs.divisors)]
  · apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero habs)
    simp only [divisorCoefficient, Int.natCast_dvd, hd0, hdvd, and_self, if_true]
  · intro d hd
    unfold divisorCoefficient
    split_ifs with hc
    · exact False.elim (hd (Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hc.2, habs⟩))
    · rfl

/-- At zero all positive divisors occur; the zero coefficient vanishes. -/
theorem divisorCoefficient_zero (ℓ : ℕ) :
    divisorCoefficient ℓ 0 = fun d => b ℓ d := by
  funext d
  by_cases hd : d = 0
  · subst d
    simp [divisorCoefficient]
  · simp [divisorCoefficient, Nat.pos_of_ne_zero hd]

/-- The single formula in (121), valid at every integer including zero,
with the infinite divisor sum justified by actual absolute summability. -/
theorem integerPrimeWeight_divisor_sum {ℓ : ℕ} (hℓ : ℓ.Prime) (r : ℤ) :
    integerPrimeWeight ℓ r = B ℓ * ∑' d : ℕ, divisorCoefficient ℓ r d := by
  by_cases hr : r = 0
  · subst r
    rw [integerPrimeWeight_zero, divisorCoefficient_zero, zero_weight_normalization]
  · rw [divisorCoefficient_tsum hr]
    exact primeWeight_divisor_sum hℓ (Int.natAbs_ne_zero.mpr hr)

/-- Every actual local density factor lies in the unit interval. -/
theorem baseFactor_bounds {p : ℕ} (hp : p.Prime) : 0 ≤ baseFactor p ∧ baseFactor p ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hd : 1 ≤ (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  have hd0 : 0 < (p : ℝ) * ((p : ℝ) - 1) := by linarith
  have hi : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := (div_le_one hd0).mpr hd
  have hi0 : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
  unfold baseFactor
  constructor <;> linarith

/-- Positivity follows from the convergent product's divisor expansion. -/
theorem primeWeight_pos {ℓ : ℕ} (hℓ : ℓ.Prime) (r : ℕ) : 0 < primeWeight ℓ r := by
  by_cases hr : r = 0
  · subst r
    simp
  rw [primeWeight_divisor_sum hℓ hr]
  apply mul_pos (B_pos ℓ)
  have hmem : 1 ∈ r.divisors := Nat.mem_divisors.mpr ⟨one_dvd r, hr⟩
  have hs : b ℓ 1 ≤ ∑ d ∈ r.divisors, b ℓ d :=
    Finset.single_le_sum (fun d _ => b_nonneg ℓ d) hmem
  rw [b_one] at hs
  linarith

/-- The infinite prime product retains the upper bound of its finite
partial products. This gives the literal arithmetic weight used in (106)
the required pointwise unit bound. -/
theorem primeWeight_le_one {ℓ : ℕ} (hℓ : ℓ.Prime) (r : ℕ) : primeWeight ℓ r ≤ 1 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp
  have ht := (primeWeight_hasProd hℓ hr).multipliable.hasProd
  change Tendsto (fun s : Finset Nat.Primes =>
    ∏ p ∈ s, if (p : ℕ) ∣ ℓ * r then (1 : ℝ) else baseFactor p)
      atTop (𝓝 (primeWeight ℓ r)) at ht
  apply le_of_tendsto ht
  filter_upwards [] with S
  apply Finset.prod_le_one
  · intro p _
    split_ifs
    · exact zero_le_one
    · exact (baseFactor_bounds p.property).1
  · intro p _
    split_ifs
    · exact le_rfl
    · exact (baseFactor_bounds p.property).2

theorem integerPrimeWeight_bounds {ℓ : ℕ} (hℓ : ℓ.Prime) (r : ℤ) :
    0 < integerPrimeWeight ℓ r ∧ integerPrimeWeight ℓ r ≤ 1 :=
  ⟨primeWeight_pos hℓ _, primeWeight_le_one hℓ _⟩

/-- Every nonzero arithmetic coefficient is supported on integers coprime
to the omitted prime; this is the condition needed in the lattice scaling. -/
theorem b_ne_zero_coprime {ℓ d : ℕ} (hℓ : ℓ.Prime) (hb : b ℓ d ≠ 0) :
    d.Coprime ℓ := by
  have hd : d ≠ 0 := by intro hz; subst d; simp at hb
  by_contra hcop
  rw [b_formula hℓ hd, if_neg hcop, mul_zero, zero_mul] at hb
  exact hb rfl

theorem c_ne_zero_coprime {ℓ d : ℕ} (hℓ : ℓ.Prime) (hc : c ℓ d ≠ 0) :
    d.Coprime ℓ := by
  apply b_ne_zero_coprime hℓ
  intro hb
  rw [c_apply, hb, mul_zero] at hc
  exact hc rfl

end DepthAspect.ArithmeticWeights
