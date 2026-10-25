import DepthAspect.SignedPrimeStrata
import DepthAspect.SignedPrimeAuxiliary

/-!
# The whole prime-index signed expression on one common interval

The general signed trace's actual admissible sums are reindexed, its
weight-two correction is cancelled, and its hyperbolic term is evaluated.
The result is the finite class-number weighted expression used in (78)/(80).
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

noncomputable def commonStratumWeight (c s m : ℕ) (H : ℤ → ℝ) (t : ℤ) : ℂ :=
  (if ((2 * c * s : ℕ) : ℤ) ∣ t then
    (H (((2 * s : ℕ) : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) -
      (H ((s : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) else 0) -
  (if ((4 * c * s : ℕ) : ℤ) ∣ t then
    (H (((4 * s : ℕ) : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) -
      (H (((2 * s : ℕ) : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) else 0)

/-- Both depth parities share exactly the same finite algebraic expression,
with c=1 or c=2 and the smallest scale s=2^a. -/
theorem ellipticSieve_common_interval (r a m : ℕ) (b : ℕ) (hb : b ≤ 1)
    (hm : 0 < m) (H : ℤ → ℝ) :
    ellipticSieve r (2 * a + b + 4) m H =
      -(∑ t ∈ closedTraces (2 ^ b) m,
        tracePolynomial (((t : ℝ) / Real.sqrt (2 ^ b) : ℝ) : ℂ) (m : ℂ) r *
          commonStratumWeight (2 ^ b) (2 ^ a) m H t) := by
  have hv0 : (2 : ℕ) ^ (2 * a + b + 4) =
      2 ^ b * (4 * 2 ^ a) ^ 2 := by
    rw [show 2 * a + b + 4 = b + (a * 2 + 4) by omega,
      pow_add, pow_add, pow_mul]
    norm_num
    ring
  have hv2 : (2 : ℕ) ^ (2 * a + b + 4 - 2) =
      2 ^ b * (2 * 2 ^ a) ^ 2 := by
    rw [show 2 * a + b + 4 - 2 = b + (a * 2 + 2) by omega,
      pow_add, pow_add, pow_mul]
    norm_num
    ring
  have hv4 : (2 : ℕ) ^ (2 * a + b + 4 - 4) =
      2 ^ b * (2 ^ a) ^ 2 := by
    rw [show 2 * a + b + 4 - 4 = b + a * 2 by omega, pow_add, pow_mul]
  unfold ellipticSieve
  rw [elliptic_sieve_four_strata r (2 * a + b + 4) m (by omega) hm H,
    hv0, hv2, hv4]
  simpa only [commonStratumWeight, Nat.cast_pow, Nat.cast_ofNat] using
    four_strata_common_interval r (2 ^ b) (2 ^ a) m
      (by positivity) (by positivity) hm H

/-- The entire even-depth prime arithmetic expression, including its actual
hyperbolic correction. The later class formula supplies the L-value weight. -/
theorem newSignedExpression_prime_even (r a P : ℕ) (hP : P.Prime) (H : ℤ → ℝ) :
    newSignedExpression r (2 ^ (2 * a + 4)) P H =
      (∑ t ∈ closedTraces 1 P,
        tracePolynomial (t : ℂ) (P : ℂ) r * commonStratumWeight 1 (2 ^ a) P H t) / 2 -
      DyadicRamanujan.ramanujanTwoPow (a + 1) ((P + 1 : ℕ) : ℤ) / 2 := by
  have he := ellipticSieve_common_interval r a P 0 (by decide) hP.pos H
  norm_num only [pow_zero, add_zero, Real.sqrt_one, div_one, Complex.ofReal_intCast] at he
  rw [newSignedExpression_elliptic_hyperbolic r (2 * a + 4) P (by omega) H, he]
  have hh : hyperbolicSieve r (2 * a + 4) P =
      -DyadicRamanujan.ramanujanTwoPow (a + 1) ((P + 1 : ℕ) : ℤ) / 2 :=
    hyperbolic_prime_even_sieve r a P hP
  rw [hh]
  ring

/-- The entire odd-depth prime arithmetic expression has no auxiliary term. -/
theorem newSignedExpression_prime_odd (r a P : ℕ) (hP : P.Prime) (H : ℤ → ℝ) :
    newSignedExpression r (2 ^ (2 * a + 5)) P H =
      (∑ t ∈ closedTraces 2 P,
        tracePolynomial (((t : ℝ) / Real.sqrt 2 : ℝ) : ℂ) (P : ℂ) r *
          commonStratumWeight 2 (2 ^ a) P H t) / 2 := by
  have he := ellipticSieve_common_interval r a P 1 (by decide) hP.pos H
  norm_num only [pow_one, show 2 * a + 1 + 4 = 2 * a + 5 by omega] at he
  rw [newSignedExpression_elliptic_hyperbolic r (2 * a + 5) P (by omega) H, he]
  have hh : hyperbolicSieve r (2 * a + 5) P = 0 := hyperbolic_prime_odd_sieve r a P hP
  rw [hh]
  ring

end DepthAspect.SignedSieve
