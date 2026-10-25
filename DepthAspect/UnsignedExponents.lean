import DepthAspect.Support
import DepthAspect.ErrorBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The last estimates in Theorem 4.1

This module proves the passage from the five-term error (62) to (42), and
then the uniform inverse-logarithmic estimate (41). The five-term estimate
is an intermediate hypothesis to be supplied by the density assembly.
-/
namespace DepthAspect.UnsignedExponents

/-- The paper's depth and weight range guarantees the logarithmic
normalization used in all estimates; this is not an extra analytic premise. -/
theorem conductor_log_ge_one (k : ℝ) (hk : 2 ≤ k) (n : ℕ) (hn : 8 ≤ n) :
    1 ≤ Real.log (k ^ 2 * (2 : ℝ) ^ n) := by
  have hk0 : k ≠ 0 := by linarith
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogk := Real.log_nonneg hk2
  have hlog2 := Real.log_two_gt_d9
  have hprod := mul_le_mul_of_nonneg_right hnR
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [Real.log_mul (pow_ne_zero _ hk0) (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
    Real.log_pow (2 : ℝ) n]
  linarith

theorem dyadic_level_gt_one (n : ℕ) (hn : 8 ≤ n) : 1 < (2 : ℝ) ^ n := by
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  norm_num only [show (2 : ℝ) ^ (8 : ℕ) = 256 by norm_num] at hp
  linarith

theorem level_endpoint_identity {k N : ℝ} (_hk : 0 < k) (hN : 0 < N) (u v : ℝ) :
    N ^ u * (k ^ 2 * N) ^ v = (k ^ 2) ^ v * N ^ (u + v) := by
  rw [Real.mul_rpow (sq_nonneg _) hN.le, Real.rpow_add hN]
  ring

theorem level_endpoint_bound {k N u v w : ℝ} (hk : 0 < k) (hN : 1 ≤ N)
    (hexp : u + v ≤ w) :
    N ^ u * (k ^ 2 * N) ^ v ≤ (k ^ 2) ^ v * N ^ w := by
  rw [level_endpoint_identity hk (by linarith : 0 < N)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hexp) (by positivity)

/-- The precise small parameter (63), including all endpoint factors
depending on the fixed weight, converts (62) into (42). -/
theorem five_term_to_three_term {k N L s η C E : ℝ}
    (hk : 0 < k) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hs : 0 < s) (hs' : s < 3 / 2) (hη : 0 < η) (hη' : η < 1 / 2)
    (hC : 0 ≤ C)
    (hE : let δ := η / (2 * (1 + s))
      E ≤ C * (1 / L + N ^ (-(1 / 2 : ℝ)) +
        N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 + δ)) +
        (1 / L) * (N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 / 2 + δ))) +
        (1 / L) * (N ^ (-(1 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * δ)))) :
    let δ := η / (2 * (1 + s))
    E ≤ (C * (2 + (k ^ 2) ^ (s * (1 + δ)) +
        (k ^ 2) ^ (s * (1 / 2 + δ)) + (k ^ 2) ^ (s * δ))) *
      (1 / L + N ^ (s - 3 / 2 + η) + N ^ (-(1 / 2 : ℝ) + η)) := by
  dsimp only at hE ⊢
  let δ := η / (2 * (1 + s))
  obtain ⟨hδ, hδ', hsδ, he₁, he₂, he₃⟩ := unsigned_parameter_choice hs hs' hη hη'
  let F := 1 / L + N ^ (s - 3 / 2 + η) + N ^ (-(1 / 2 : ℝ) + η)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hL0 : 0 < L := by linarith
  have hLinv : 0 ≤ 1 / L := by positivity
  have hLinv1 : 1 / L ≤ 1 := (div_le_iff₀ hL0).mpr (by linarith)
  have hp₁ : 0 ≤ N ^ (s - 3 / 2 + η) := by positivity
  have hp₂ : 0 ≤ N ^ (-(1 / 2 : ℝ) + η) := by positivity
  have hA : 1 / L ≤ F := by dsimp [F]; linarith
  have hB : N ^ (-(1 / 2 : ℝ)) ≤ F := by
    have hp := Real.rpow_le_rpow_of_exponent_le hN
      (show -(1 / 2 : ℝ) ≤ -(1 / 2 : ℝ) + η by linarith)
    exact hp.trans (by dsimp [F]; linarith)
  have h₁ : N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 + δ)) ≤
      (k ^ 2) ^ (s * (1 + δ)) * F := by
    exact (level_endpoint_bound hk hN he₁).trans
      (mul_le_mul_of_nonneg_left (by dsimp [F]; linarith) (by positivity))
  have h₂ : (1 / L) * (N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 / 2 + δ))) ≤
      (k ^ 2) ^ (s * (1 / 2 + δ)) * F := by
    calc
      _ ≤ N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 / 2 + δ)) :=
        mul_le_of_le_one_left (by positivity) hLinv1
      _ ≤ (k ^ 2) ^ (s * (1 / 2 + δ)) * N ^ (-(1 / 2 : ℝ) + η) :=
        level_endpoint_bound hk hN (by simpa only [δ, neg_div] using he₂)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [F]; linarith) (by positivity)
  have h₃ : (1 / L) * (N ^ (-(1 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * δ)) ≤
      (k ^ 2) ^ (s * δ) * F := by
    calc
      _ ≤ N ^ (-(1 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * δ) :=
        mul_le_of_le_one_left (by positivity) hLinv1
      _ ≤ (k ^ 2) ^ (s * δ) * N ^ (-(1 / 2 : ℝ) + η) :=
        level_endpoint_bound hk hN (by simpa only [δ, neg_div] using he₃)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [F]; linarith) (by positivity)
  have hsum : 1 / L + N ^ (-(1 / 2 : ℝ)) +
        N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 + δ)) +
        (1 / L) * (N ^ (-(3 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * (1 / 2 + δ))) +
        (1 / L) * (N ^ (-(1 / 2 : ℝ)) * (k ^ 2 * N) ^ (s * δ)) ≤
      (2 + (k ^ 2) ^ (s * (1 + δ)) + (k ^ 2) ^ (s * (1 / 2 + δ)) +
        (k ^ 2) ^ (s * δ)) * F := by nlinarith
  have ht := hE.trans (mul_le_mul_of_nonneg_left hsum hC)
  simpa only [δ, F, mul_assoc] using ht

/-- The negative exponents in (42) imply (41) uniformly for every `N>1`.
This is a quantitative inequality, not just a limiting assertion. -/
theorem three_term_to_inverse_log {k N s η C E : ℝ}
    (hk : 1 ≤ k ^ 2) (hN : 1 < N) (hC : 0 ≤ C)
    (hη : η < min (1 / 2) (3 / 2 - s))
    (hE : E ≤ C * (1 / Real.log (k ^ 2 * N) +
      N ^ (s - 3 / 2 + η) + N ^ (-(1 / 2 : ℝ) + η))) :
    E ≤ C * (1 + 2 * Real.log (k ^ 2) +
      1 / (-(s - 3 / 2 + η)) + 1 / (-(-(1 / 2 : ℝ) + η))) /
        Real.log (k ^ 2 * N) := by
  obtain ⟨ha, hb⟩ := unsigned_exponents_negative hη
  have hA := negative_power_le_inverse_conductor_log hN hk ha
  have hB := negative_power_le_inverse_conductor_log hN hk hb
  calc
    E ≤ C * (1 / Real.log (k ^ 2 * N) +
        N ^ (s - 3 / 2 + η) + N ^ (-(1 / 2 : ℝ) + η)) := hE
    _ ≤ C * (1 / Real.log (k ^ 2 * N) +
        (Real.log (k ^ 2) + 1 / (-(s - 3 / 2 + η))) / Real.log (k ^ 2 * N) +
        (Real.log (k ^ 2) + 1 / (-(-(1 / 2 : ℝ) + η))) / Real.log (k ^ 2 * N)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hA) hB) hC
    _ = _ := by ring

end DepthAspect.UnsignedExponents
