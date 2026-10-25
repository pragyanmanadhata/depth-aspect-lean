import DepthAspect.SignedEllipticBound

/-!
# The numerical normalization in Lemma 5.1

These identities remove the polynomial-degree power and expose the two
terms N^(1/2+δ)p^(2δ) and N^δ p^(1+2δ) in the signed square-index estimate.
-/
namespace DepthAspect.SignedSieve

/-- Separation of every actual real power in the normalized elliptic bound. -/
theorem signed_power_separation (r : ℕ) (N m δ : ℝ) (hN : 0 < N) (hm : 0 < m) :
    m ^ r * (4 * N * m) ^ (1 / 2 + δ) / m ^ ((r : ℝ) + 1 / 2) =
      (4 : ℝ) ^ (1 / 2 + δ) * N ^ (1 / 2 + δ) * m ^ δ := by
  have hmr : m ^ r ≠ 0 := pow_ne_zero r (ne_of_gt hm)
  have hmh : m ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hm _)
  rw [Real.mul_rpow (by positivity) hm.le,
    Real.mul_rpow (by norm_num) hN.le, Real.rpow_add hm,
    Real.rpow_add hm, Real.rpow_natCast]
  field_simp [hmr, hmh]

/-- Dividing the first level factor by sqrt N lowers its exponent by one half. -/
theorem signed_level_power (N δ : ℝ) (hN : 0 < N) :
    N ^ (1 / 2 + δ) / Real.sqrt N = N ^ δ := by
  rw [Real.rpow_add hN, ← Real.sqrt_eq_rpow]
  exact mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hN).ne'

/-- The constant 48 in (73) dominates the constants obtained from the exact
absolute coefficient total (four) and the interval-length count. -/
theorem signed_numeric_bound (r : ℕ) (N m C δ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hC : 0 ≤ C) :
    (4 * (1 + 16 * Real.sqrt m / Real.sqrt N) *
      (((2 * r + 1 : ℕ) : ℝ) * m ^ r * C *
        (4 * N * m) ^ (1 / 2 + δ))) / 2 / m ^ ((r : ℝ) + 1 / 2) ≤
      48 * ((2 * r + 1 : ℕ) : ℝ) * C * (4 : ℝ) ^ (1 / 2 + δ) *
        (N ^ (1 / 2 + δ) * m ^ δ + N ^ δ * m ^ (1 / 2 + δ)) := by
  have hsep := signed_power_separation r N m δ hN hm
  have hlev := signed_level_power N δ hN
  have hmhalf : m ^ (1 / 2 + δ) = Real.sqrt m * m ^ δ := by
    rw [Real.rpow_add hm, ← Real.sqrt_eq_rpow]
  have hrewrite :
      (4 * (1 + 16 * Real.sqrt m / Real.sqrt N) *
        (((2 * r + 1 : ℕ) : ℝ) * m ^ r * C *
          (4 * N * m) ^ (1 / 2 + δ))) / 2 / m ^ ((r : ℝ) + 1 / 2) =
      ((2 * r + 1 : ℕ) : ℝ) * C * (4 : ℝ) ^ (1 / 2 + δ) *
        (2 * (N ^ (1 / 2 + δ) * m ^ δ) +
          32 * (N ^ δ * m ^ (1 / 2 + δ))) := by
    calc
      _ = 2 * (1 + 16 * Real.sqrt m / Real.sqrt N) *
          ((2 * r + 1 : ℕ) : ℝ) * C *
          (m ^ r * (4 * N * m) ^ (1 / 2 + δ) / m ^ ((r : ℝ) + 1 / 2)) := by ring
      _ = _ := by
        rw [hsep, hmhalf]
        have hs : Real.sqrt m / Real.sqrt N * N ^ (1 / 2 + δ) =
            Real.sqrt m * N ^ δ := by
          calc
            _ = Real.sqrt m * (N ^ (1 / 2 + δ) / Real.sqrt N) := by ring
            _ = _ := by rw [hlev]
        calc
          _ = ((2 * r + 1 : ℕ) : ℝ) * C * (4 : ℝ) ^ (1 / 2 + δ) *
            (2 * (N ^ (1 / 2 + δ) * m ^ δ) +
              32 * ((Real.sqrt m / Real.sqrt N * N ^ (1 / 2 + δ)) * m ^ δ)) := by ring
          _ = _ := by rw [hs]; ring
  rw [hrewrite]
  have hA : 0 ≤ N ^ (1 / 2 + δ) * m ^ δ := by positivity
  have hB : 0 ≤ N ^ δ * m ^ (1 / 2 + δ) := by positivity
  have hK : 0 ≤ ((2 * r + 1 : ℕ) : ℝ) * C * (4 : ℝ) ^ (1 / 2 + δ) := by positivity
  nlinarith [mul_nonneg hK hA, mul_nonneg hK hB]

/-- Replacing m by the actual square p² gives the powers displayed in (73). -/
theorem square_rpow_exponents (p δ : ℝ) (hp : 0 ≤ p) :
    (p ^ 2) ^ δ = p ^ (2 * δ) ∧
      (p ^ 2) ^ (1 / 2 + δ) = p ^ (1 + 2 * δ) := by
  constructor
  · rw [← Real.rpow_natCast_mul hp]
    norm_num
  · rw [← Real.rpow_natCast_mul hp]
    congr 1
    ring

end DepthAspect.SignedSieve
