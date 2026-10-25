import DepthAspect.UnsignedExponents

/-! Fixed-constant absorption and exact conductor endpoints in (62). -/
namespace DepthAspect.UnsignedExponents

/-- The support endpoint is literally `(k²N)^s`, also for nonintegral s. -/
theorem support_endpoint_power {k N : ℝ} (hk : 0 < k) (hN : 0 < N) (s u : ℝ) :
    (Real.exp (s * Real.log (k ^ 2 * N))) ^ u = (k ^ 2 * N) ^ (s * u) := by
  have hx : 0 < k ^ 2 * N := by positivity
  have he : Real.exp (s * Real.log (k ^ 2 * N)) = (k ^ 2 * N) ^ s := by
    rw [Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [he, ← Real.rpow_mul hx.le]

/-- Nonnegative coefficients can be replaced by their sum without hiding
any dependence on the level. This is the fixed-constant step in (62). -/
theorem four_coefficient_absorption {A B C D t₀ t₁ t₂ t₃ t₄ E : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ht₀ : 0 ≤ t₀) (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (ht₃ : 0 ≤ t₃) (ht₄ : 0 ≤ t₄)
    (hE : E ≤ A * t₀ + B * t₁ + C * t₂ + D * (t₃ + t₄)) :
    E ≤ (A + B + C + D) * (t₀ + t₁ + t₂ + t₃ + t₄) := by
  have ha : A ≤ A + B + C + D := by linarith
  have hb : B ≤ A + B + C + D := by linarith
  have hc : C ≤ A + B + C + D := by linarith
  have hd : D ≤ A + B + C + D := by linarith
  have h₀ := mul_le_mul_of_nonneg_right ha ht₀
  have h₁ := mul_le_mul_of_nonneg_right hb ht₁
  have h₂ := mul_le_mul_of_nonneg_right hc ht₂
  have h₃ := mul_le_mul_of_nonneg_right hd (add_nonneg ht₃ ht₄)
  nlinarith

/-- The actual four coefficient groups from the analytic and arithmetic
assembly give exactly the five-error shape used in (62). -/
theorem weighted_error_to_five_terms {k N L s δ A B C D E : ℝ}
    (hk : 0 < k) (hN : 0 < N) (hL : 0 < L)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hLdef : L = Real.log (k ^ 2 * N))
    (hE : E ≤ A / L + B * N ^ (-(1 / 2 : ℝ)) +
      C * N ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 + δ) +
      D / L * (N ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 / 2 + δ) +
        N ^ (-(1 / 2 : ℝ)) * (Real.exp (s * L)) ^ δ)) :
    E ≤ (A + B + C + D) * (1 / L + N ^ (-(1 / 2 : ℝ)) +
      N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 + δ)) +
      (1 / L) * (N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 / 2 + δ))) +
      (1 / L) * (N ^ (-(1 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * δ))) := by
  have he : E ≤ A * (1 / L) + B * N ^ (-(1 / 2 : ℝ)) +
      C * (N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 + δ))) +
      D * ((1 / L) * (N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 / 2 + δ))) +
        (1 / L) * (N ^ (-(1 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * δ))) := by
    have h := hE
    rw [hLdef, support_endpoint_power hk hN, support_endpoint_power hk hN,
      support_endpoint_power hk hN] at h
    rw [hLdef]
    convert h using 1 <;> ring
  exact four_coefficient_absorption hA hB hC hD (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) he

end DepthAspect.UnsignedExponents
