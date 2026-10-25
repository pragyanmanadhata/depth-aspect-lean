import DepthAspect.TraceCusp
import DepthAspect.PrimePowerApplications

/-! Equations (46) and (49) for the actual normalized cusp sum. -/
namespace DepthAspect.TracePrimeApplications

open TraceBounds PrimePowerApplications
open scoped BigOperators

/-- The actual prime cusp term, including its dimension normalization, is
summed using the proved Chebyshev estimate. -/
theorem normalizedCusp_prime_sum_bound (k n : ℕ) {X L H s d : ℝ}
    (hX : 1 ≤ X) (hL : 1 ≤ L) (hH : 0 ≤ H) (hs : 0 ≤ s)
    (hlog : Real.log X ≤ s * L)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊X⌋₊) (w : ℕ → ℂ)
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-(1 / 2 : ℝ))
      (fun p => (normalizedCusp k n d (p : ℝ) p.divisorsAntidiagonal : ℂ)) w ≤
      2 * (576 / ((k : ℝ) + 1)) * H * Real.log 4 * (1 + s) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  apply cusp_prime_sum_bound hX (by positivity) hL
    (show 2 ≤ (k : ℝ) + 2 by have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by positivity) hH hs hlog M hM _ w _ hw
  intro p hp
  have hb := normalizedCusp_prime_bound k n p (Nat.mem_primesLE.mp (hM hp)).2 d hd
  rw [Complex.norm_real, Real.norm_eq_abs]
  have he : -((k : ℝ) + 2 - 1) / 2 = -((k : ℝ) + 1) / 2 := by ring
  rw [he]
  simpa only [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ n), div_eq_mul_inv, mul_assoc] using hb

/-- The same composition for the actual prime-square cusp term. -/
theorem normalizedCusp_square_sum_bound (k n : ℕ) {Z L H s d : ℝ}
    (hZ : 1 ≤ Z) (hL : 1 ≤ L) (hH : 0 ≤ H) (hs : 0 ≤ s)
    (hlog : Real.log Z ≤ s * L)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (w : ℕ → ℂ)
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1)
      (fun p => (normalizedCusp k n d ((p ^ 2 : ℕ) : ℝ)
        (p ^ 2).divisorsAntidiagonal : ℂ)) w ≤
      2 * (576 / ((k : ℝ) + 1)) * H * Real.log 4 * (1 + s) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  apply cusp_square_sum_bound hZ (by positivity) hL (by positivity) hH hs hlog M hM _ w _ hw
  intro p hp
  have hb := normalizedCusp_prime_square_bound k n p (Nat.mem_primesLE.mp (hM hp)).2 d hd
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ n), div_eq_mul_inv, mul_assoc] using hb

/-- The scalar term is its actual coefficient times `1/p`; the coefficient
bounds are supplied by Martin's general dimension formula. -/
theorem scalarCoefficient_square_sum_bound {Z L H c : ℝ}
    (hZ : 1 ≤ Z) (hL : 0 < L) (hH : 0 ≤ H) (hc0 : 0 ≤ c) (hc2 : c ≤ 2)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (w : ℕ → ℂ)
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1) (fun p => ((c / (p : ℝ) : ℝ) : ℂ)) w ≤
      8 * H * Real.log 4 / L := by
  apply scalar_square_sum_bound hZ hL hH M hM _ w _ hw
  intro p hp
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.rpow_neg_one]
  simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_right hc2 (Nat.cast_nonneg p)

end DepthAspect.TracePrimeApplications
