import DepthAspect.TraceSquares
import DepthAspect.ClassNumberWeights
import DepthAspect.PrimePowerApplications

/-!
# Equation (48) for the literal canonical elliptic trace

This composes the proved prime-square count and actual matrix/content trace
estimate with the actual weighted Chebyshev prime sum. The pointwise estimate
(40) is a conclusion of the imported theorem, not an input here.
-/
namespace DepthAspect.TracePrimeApplications

open TraceBounds PrimePowerApplications
open scoped BigOperators

theorem literalElliptic_square_sum_bound (k n : ℕ) (hn : 4 ≤ n)
    {X L δ Ccl H d : ℝ}
    (hX : 1 ≤ X) (hL : 0 < L) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hC : 0 ≤ Ccl) (hH : 0 ≤ H)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (h₀ Hurwitz : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      Hurwitz D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hHgrowth : ∀ D : ℤ, D < 0 → Hurwitz D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Real.sqrt X⌋₊)
    (hModd : ∀ p ∈ M, p ≠ 2)
    (F : ℕ → ℤ → ℕ → ContentDatum) (w : ℕ → ℂ)
    (hF : ∀ p ∈ M, ∀ t : ℤ, t ^ 2 < 4 * (p : ℤ) ^ 2 →
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * (p : ℤ) ^ 2),
        h₀ ((t ^ 2 - 4 * (p : ℤ) ^ 2) / (u : ℤ) ^ 2) ≠ 0 →
        IsPrimitiveContentMatrix u (t ^ 2 - 4 * (p : ℤ) ^ 2) (F p t u))
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1)
      (fun p => literalElliptic k n d ((p : ℤ) ^ 2) h₀ (F p)) w ≤
      squareConstant (ellipticConstant Ccl δ) δ * H / L *
        (((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * X ^ (1 / 2 + δ) +
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) * X ^ δ) := by
  apply elliptic_square_sum_bound hX (by positivity) hL
    (ellipticConstant_nonneg Ccl δ hC hδ) hH hδ hδhalf M hM _ w _ hw
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp (hM hp)).2
  have hpos : (0 : ℤ) < p := by exact_mod_cast hpprime.pos
  have hodd : Odd (p : ℤ) := by
    obtain ⟨a, ha⟩ := hpprime.odd_of_ne_two (hModd p hp)
    exact ⟨(a : ℤ), by exact_mod_cast ha⟩
  have hb := classElliptic_prime_square_bound k n hn (p : ℤ) hpos hodd d Ccl δ hC hδ hd
    h₀ h₀nonneg (primitive_class_number_growth h₀ Hurwitz Ccl δ h₀nonneg hidentity hHgrowth)
    (ellipticTraces ((p : ℤ) ^ 2)) (F p)
    (fun t ht => (mem_ellipticTraces _ _).mp ht)
    (fun t ht => hF p hp t ((mem_ellipticTraces _ _).mp ht))
  simpa only [classElliptic, literalElliptic, Int.cast_natCast, neg_div] using hb

end DepthAspect.TracePrimeApplications
