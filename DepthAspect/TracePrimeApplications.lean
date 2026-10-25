import DepthAspect.ClassNumberWeights
import DepthAspect.PrimeSumBounds

/-!
# Prime sums for the actual finite elliptic trace model

This composes the proved matrix/content estimate (35), the actual surviving
integer trace count (44), and the finite dyadic partition. The remaining
class-number-growth premises are reusable interfaces supplied by the proved
`ClassNumberGrowth` theorem; no pointwise or averaged elliptic trace estimate
is assumed.
-/
namespace DepthAspect.TracePrimeApplications

open TraceBounds PrimeSumBounds
open scoped BigOperators

/-- Equation (45) for the actual finite polynomial/content/matrix expression.
Taking `M` to be the odd primes below `X` gives the paper's prime sum. -/
theorem normalizedElliptic_prime_sum_bound (k n : ℕ) (hn : 4 ≤ n)
    {X L δ Ccl H s d : ℝ}
    (hX : 1 ≤ X) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 ≤ Ccl)
    (hs : 0 ≤ s) (hH : 0 ≤ H) (hlogX : Real.log X ≤ s * L)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (M : Finset ℤ) (T : ℤ → Finset ℤ)
    (S : ℤ → ℤ → Finset (ℕ × ℕ))
    (F : ℤ → ℤ → ℕ × ℕ → ContentDatum) (h : ℝ → ℂ)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (hT : ∀ m ∈ M, ∀ t ∈ T m, t ^ 2 < 4 * m)
    (hF : ∀ m ∈ M, ∀ t ∈ T m, ∀ p ∈ S m t,
      IsContentDatum p (t ^ 2 - 4 * m) Ccl δ (F m t p))
    (hh : ∀ m ∈ M, ‖h (Real.log (m : ℝ) / L)‖ ≤ H) :
    (2 / L) * (∑ m ∈ M,
      weightedTerm L (fun m => normalizedElliptic k d (m : ℝ) (T m)
        (fun t => contentTrace n (S m t) (F m t))) h m) ≤
      (96 * s * ellipticConstant Ccl δ * Real.sqrt 2 /
        (1 - (2 : ℝ) ^ (-1 - δ))) * H *
        ((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * X ^ (1 + δ) := by
  have hq : 0 < (2 : ℤ) ^ (n - 4) := by positivity
  have hN : (2 : ℝ) ^ n = 16 * (((2 : ℤ) ^ (n - 4) : ℤ) : ℝ) := by
    push_cast
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 4) + 4) := by congr 1; omega
      _ = 16 * (2 : ℝ) ^ (n - 4) := by rw [pow_add]; norm_num; ring
  apply prime_sum_bound hX hL hδ.le hs (ellipticConstant_nonneg Ccl δ hC hδ)
    hH hq hN hlogX M (SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)))
    _ h hM
  · intro m hm t ht
    exact (SurvivingTraces.mem_survivingTraces _ _ _).mp ht
  · intro m hm
    have hm0 : 0 < m := by
      have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast (hM m hm).1
      omega
    simpa only [neg_div] using normalizedElliptic_bound_surviving k n hn m hm0 d Ccl δ hC hδ hd
      (T m) (S m) (F m) (hT m hm) (hF m hm)
  · exact hh

/-- Canonical (45), using every strict-elliptic trace and every positive
square content with its actual primitive class-number weight. No internal
pointwise elliptic estimate is an input. -/
theorem literalElliptic_prime_sum_bound (k n : ℕ) (hn : 4 ≤ n)
    {X L δ Ccl H s d : ℝ}
    (hX : 1 ≤ X) (hL : 0 < L) (hδ : 0 < δ) (hC : 0 ≤ Ccl)
    (hs : 0 ≤ s) (hH : 0 ≤ H) (hlogX : Real.log X ≤ s * L)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (h₀ Hurwitz : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      Hurwitz D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hHgrowth : ∀ D : ℤ, D < 0 → Hurwitz D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (M : Finset ℤ) (F : ℤ → ℤ → ℕ → ContentDatum) (h : ℝ → ℂ)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (hF : ∀ m ∈ M, ∀ t : ℤ, t ^ 2 < 4 * m →
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
        h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 →
        IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (F m t u))
    (hh : ∀ m ∈ M, ‖h (Real.log (m : ℝ) / L)‖ ≤ H) :
    (2 / L) * (∑ m ∈ M,
      weightedTerm L (fun m => literalElliptic k n d m h₀ (F m)) h m) ≤
      (96 * s * ellipticConstant Ccl δ * Real.sqrt 2 /
        (1 - (2 : ℝ) ^ (-1 - δ))) * H *
        ((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * X ^ (1 + δ) := by
  have hq : 0 < (2 : ℤ) ^ (n - 4) := by positivity
  have hN : (2 : ℝ) ^ n = 16 * (((2 : ℤ) ^ (n - 4) : ℤ) : ℝ) := by
    push_cast
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 4) + 4) := by congr 1; omega
      _ = 16 * (2 : ℝ) ^ (n - 4) := by rw [pow_add]; norm_num; ring
  apply prime_sum_bound hX hL hδ.le hs (ellipticConstant_nonneg Ccl δ hC hδ)
    hH hq hN hlogX M (SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)))
    _ h hM
  · intro m hm t ht
    exact (SurvivingTraces.mem_survivingTraces _ _ _).mp ht
  · intro m hm
    have hm0 : 0 < m := by
      have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast (hM m hm).1
      omega
    simpa only [neg_div] using literalElliptic_bound k n hn m hm0 d Ccl δ hC hδ hd
      h₀ Hurwitz h₀nonneg hidentity hHgrowth (F m) (hF m hm)
  · exact hh

end DepthAspect.TracePrimeApplications
