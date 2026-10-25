import DepthAspect.SignedPrimeReindex

/-!
# Combining the literal four signed elliptic strata

First the true coefficient table is applied to the general signed elliptic
sum. Then one common finite interval is obtained by the exact integer
rescaling. No trace-weight formula is supplied as an assumption.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

noncomputable def stratumTerm (r v m : ℕ) (H : ℤ → ℝ) (u : ℤ) : ℂ :=
  tracePolynomial (((((v : ℤ) * u : ℤ) : ℝ) / Real.sqrt v : ℝ) : ℂ) (m : ℂ) r *
    (H (((v : ℤ) * u) ^ 2 - 4 * v * m) : ℂ)

/-- The actual coefficient table is precisely the all/all/even/even grouping
used in the proof of Proposition 5.2. -/
theorem elliptic_sieve_four_strata (r n m : ℕ) (hn : 4 ≤ n) (hm : 0 < m)
    (H : ℤ → ℝ) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      ∑ v ∈ (2 ^ (n - j)).divisors,
        ∑ t ∈ admissibleTraces (2 ^ (n - j)) v m,
          tracePolynomial (((t : ℝ) / Real.sqrt v : ℝ) : ℂ) (m : ℂ) r *
            (H (t ^ 2 - 4 * v * m) : ℂ)) =
      (∑ u ∈ quotientTraces (2 ^ n) m, stratumTerm r (2 ^ n) m H u) -
      (∑ u ∈ quotientTraces (2 ^ (n - 2)) m, stratumTerm r (2 ^ (n - 2)) m H u) -
      (∑ u ∈ quotientTraces (2 ^ (n - 2)) m,
        if Even u then stratumTerm r (2 ^ (n - 2)) m H u else 0) +
      (∑ u ∈ quotientTraces (2 ^ (n - 4)) m,
        if Even u then stratumTerm r (2 ^ (n - 4)) m H u else 0) := by
  classical
  rw [signed_elliptic_stratum_reindex n m (by omega) hm]
  change (∑ b ∈ Finset.range (n + 1), ∑ u ∈ quotientTraces (2 ^ (n - b)) m,
    (SignedAdmissibility.actualStratumCoefficient n b u : ℂ) *
      stratumTerm r (2 ^ (n - b)) m H u) = _
  rw [coefficient_sum_four_strata n hn]
  simp only [Nat.sub_zero]
  have hmid :
      (∑ u ∈ quotientTraces (2 ^ (n - 2)) m,
        (if Odd u then (-1 : ℂ) else -2) * stratumTerm r (2 ^ (n - 2)) m H u) =
      -(∑ u ∈ quotientTraces (2 ^ (n - 2)) m, stratumTerm r (2 ^ (n - 2)) m H u) -
        (∑ u ∈ quotientTraces (2 ^ (n - 2)) m,
          if Even u then stratumTerm r (2 ^ (n - 2)) m H u else 0) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases hodd : Odd u
    · simp only [hodd, if_true, Int.not_even_iff_odd.mpr hodd, if_false]
      ring
    · simp only [hodd, if_false, Int.not_odd_iff_even.mp hodd, if_true]
      ring
  rw [hmid]
  ring

/-- A generic common-interval form of the all/all/even/even grouping. Here
c=1 or c=2 gives the even and odd depth formulas, with s the smallest scale. -/
theorem four_strata_common_interval (r c s m : ℕ) (hc : 0 < c) (hs : 0 < s)
    (hm : 0 < m) (H : ℤ → ℝ) :
    (∑ u ∈ quotientTraces (c * (4 * s) ^ 2) m,
      stratumTerm r (c * (4 * s) ^ 2) m H u) -
    (∑ u ∈ quotientTraces (c * (2 * s) ^ 2) m,
      stratumTerm r (c * (2 * s) ^ 2) m H u) -
    (∑ u ∈ quotientTraces (c * (2 * s) ^ 2) m,
      if Even u then stratumTerm r (c * (2 * s) ^ 2) m H u else 0) +
    (∑ u ∈ quotientTraces (c * s ^ 2) m,
      if Even u then stratumTerm r (c * s ^ 2) m H u else 0) =
    -(∑ t ∈ closedTraces c m,
      tracePolynomial (((t : ℝ) / Real.sqrt c : ℝ) : ℂ) (m : ℂ) r *
        ((if ((2 * c * s : ℕ) : ℤ) ∣ t then
          (H (((2 * s : ℕ) : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) -
            (H ((s : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) else 0) -
         (if ((4 * c * s : ℕ) : ℤ) ∣ t then
          (H (((4 * s : ℕ) : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) -
            (H (((2 * s : ℕ) : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ) else 0))) := by
  classical
  unfold stratumTerm
  rw [weighted_quotient_scale r c (4 * s) m hc (by positivity) hm H,
    weighted_quotient_scale r c (2 * s) m hc (by positivity) hm H,
    weighted_quotient_scale_even r c (2 * s) m hc (by positivity) hm H,
    weighted_quotient_scale_even r c s m hc hs hm H]
  have htwo : ((c * (2 * s) : ℕ) : ℤ) = ((2 * c * s : ℕ) : ℤ) := by
    push_cast
    ring
  have hfour : ((c * (4 * s) : ℕ) : ℤ) = ((4 * c * s : ℕ) : ℤ) := by
    push_cast
    ring
  have hevenTwo : 2 * ((c * (2 * s) : ℕ) : ℤ) = ((4 * c * s : ℕ) : ℤ) := by
    push_cast
    ring
  have hevenOne : 2 * ((c * s : ℕ) : ℤ) = ((2 * c * s : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hevenTwo, hevenOne, htwo, hfour]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> ring

end DepthAspect.SignedSieve
