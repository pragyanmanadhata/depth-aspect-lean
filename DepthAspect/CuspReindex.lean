import DepthAspect.TraceCusp
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Literal cusp-factor pairs and trace normalizations

The cusp factor Φ_Q is defined over all positive divisor pairs r*s=Q.
Its exact specialization to Q=2^h is proved by a finite bijection.
-/
namespace DepthAspect.TraceBounds
open scoped BigOperators

/-- Every divisor pair of 2^h is uniquely (2^j,2^(h−j)). -/
theorem sum_divisorsAntidiagonal_two_pow {α : Type*} [AddCommMonoid α]
    (h : ℕ) (f : ℕ × ℕ → α) :
    (∑ p ∈ (2 ^ h).divisorsAntidiagonal, f p) =
      ∑ j ∈ Finset.range (h + 1), f (2 ^ j, 2 ^ (h - j)) := by
  symm
  apply Finset.sum_bij (fun j _ => (2 ^ j, 2 ^ (h - j)))
  · intro j hj
    have hj' : j ≤ h := by simpa using (Finset.mem_range.mp hj)
    apply Nat.mem_divisorsAntidiagonal.mpr
    constructor
    · dsimp
      rw [← pow_add]
      congr 1
      omega
    · positivity
  · intro a ha b hb heq
    exact Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (congrArg Prod.fst heq)
  · intro p hp
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hdvd : p.1 ∣ 2 ^ h := ⟨p.2, hprod.symm⟩
    obtain ⟨j, hj, hval⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext hval.symm
    have heq : 2 ^ j * p.2 = 2 ^ j * 2 ^ (h - j) := by
      calc
        2 ^ j * p.2 = p.1 * p.2 := by rw [hval]
        _ = 2 ^ h := hprod
        _ = 2 ^ j * 2 ^ (h - j) := by rw [← pow_add]; congr 1; omega
    exact (mul_left_cancel₀ (by positivity : (2 : ℕ) ^ j ≠ 0) heq).symm
  · intro j hj
    rfl

theorem gcd_two_powers (a b : ℕ) : Nat.gcd (2 ^ a) (2 ^ b) = 2 ^ min a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, Nat.gcd_eq_left (pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_right (pow_dvd_pow 2 h)]

/-- The literal cusp factor from equation (2). -/
noncomputable def divisorCuspPhi (Q a d : ℕ) : ℕ :=
  ∑ p ∈ Q.divisorsAntidiagonal.filter
    (fun p => (Nat.gcd p.1 p.2 : ℤ) ∣ (a : ℤ) - d),
      Nat.totient (Nat.gcd p.1 p.2)

/-- Exact specialization of the original Φ_Q definition to a dyadic level. -/
theorem divisorCuspPhi_two_pow (h a d : ℕ) : divisorCuspPhi (2 ^ h) a d = cuspPhi h a d := by
  unfold divisorCuspPhi cuspPhi CuspBounds.restrictedCuspSum
  rw [Finset.sum_filter, sum_divisorsAntidiagonal_two_pow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [gcd_two_powers, Nat.cast_pow, Nat.cast_ofNat]

/-- The second difference using the literal divisor-pair definition. -/
noncomputable def originalCuspDifference (n a d : ℕ) : ℝ :=
  (divisorCuspPhi (2 ^ n) a d : ℝ) - 2 * (divisorCuspPhi (2 ^ (n - 1)) a d : ℝ) +
    (divisorCuspPhi (2 ^ (n - 2)) a d : ℝ)

theorem originalCuspDifference_eq (n a d : ℕ) :
    originalCuspDifference n a d = cuspDifference n a d := by
  simp only [originalCuspDifference, cuspDifference, divisorCuspPhi_two_pow]

/-- Pulling the common normalizing power through the literal cusp sum. -/
theorem normalizedCusp_eq_original (k n : ℕ) (d m : ℝ) (s : Finset (ℕ × ℕ)) :
    normalizedCusp k n d m s =
      -(∑ p ∈ s, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) *
        originalCuspDifference n p.1 p.2) / (2 * d * (Real.sqrt m) ^ (k + 1)) := by
  simp only [normalizedCusp, originalCuspDifference_eq, div_pow]
  have hs : (∑ p ∈ s, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) /
      (Real.sqrt m) ^ (k + 1) * cuspDifference n p.1 p.2) =
      (∑ p ∈ s, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) * cuspDifference n p.1 p.2) /
        (Real.sqrt m) ^ (k + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hs]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The square-root powers in the checked model equal the paper's real powers. -/
theorem sqrt_nat_pow_eq_rpow (m : ℝ) (hm : 0 ≤ m) (k : ℕ) :
    (Real.sqrt m) ^ k = m ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hm]
  congr 1
  ring

theorem normalizedElliptic_eq_original_power (k : ℕ) (d m : ℝ) (hm : 0 ≤ m)
    (T : Finset ℤ) (H : ℤ → ℝ) :
    normalizedElliptic k d m T H =
      -(∑ t ∈ T, tracePolynomial (t : ℂ) (m : ℂ) k * (H t : ℂ)) /
        ((2 * d * m ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) := by
  unfold normalizedElliptic
  rw [sqrt_nat_pow_eq_rpow m hm]
  simp only [Nat.cast_add, Nat.cast_one]

theorem normalizedCusp_eq_original_power (k n : ℕ) (d m : ℝ) (hm : 0 ≤ m)
    (s : Finset (ℕ × ℕ)) :
    normalizedCusp k n d m s =
      -(∑ p ∈ s, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) *
        originalCuspDifference n p.1 p.2) / (2 * d * m ^ (((k : ℝ) + 1) / 2)) := by
  rw [normalizedCusp_eq_original, sqrt_nat_pow_eq_rpow m hm]
  simp only [Nat.cast_add, Nat.cast_one]

end DepthAspect.TraceBounds
