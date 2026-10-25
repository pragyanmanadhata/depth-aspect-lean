import DepthAspect.MurmurationMeanExistence
import DepthAspect.BohrMeanSquare

/-! The quantitative mean-square and signed-part claims following (134),
for the actual arithmetic trigonometric series. -/
open Filter
open scoped Topology
namespace DepthAspect.MurmurationSignedMeans
open MurmurationOscillationSeries MurmurationMeanExistence MurmurationBohrCoefficient
  UniformPeriodicMean BohrMeanSquare

theorem A_mean_square (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ E : ℝ, 2 * (q ℓ) ^ 2 ≤ E ∧
      Tendsto (realAverage (fun x => (A a ℓ x) ^ 2)) atTop (𝓝 E) := by
  obtain ⟨E, hE⟩ := A_square_mean_exists a hℓ
  refine ⟨E, ?_, hE⟩
  exact mean_square_lower_bound (A_continuous a hℓ)
    (by positivity : 4 * Real.pi ≠ 0) (A_coefficient a hℓ) hE

theorem real_decomposition (u : ℝ) : max u 0 - max (-u) 0 = u := by
  by_cases hu : 0 ≤ u
  · rw [max_eq_left hu, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge hu), max_eq_left (by linarith)]
    ring

theorem square_le_parts {u Q : ℝ} (hu : |u| ≤ Q) :
    u ^ 2 ≤ Q * (max u 0 + max (-u) 0) := by
  by_cases h : 0 ≤ u
  · rw [max_eq_left h, max_eq_right (by linarith), add_zero]
    rw [abs_of_nonneg h] at hu
    nlinarith
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith), zero_add]
    rw [abs_of_neg (lt_of_not_ge h)] at hu
    nlinarith

/-- Both signed parts have actual limits, are equal, and each limit is at
least q²/Q as asserted in the text. -/
theorem A_signed_part_means (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ p n : ℝ, p = n ∧ (q ℓ) ^ 2 / Q ℓ ≤ p ∧ (q ℓ) ^ 2 / Q ℓ ≤ n ∧
      Tendsto (realAverage (fun x => max (A a ℓ x) 0)) atTop (𝓝 p) ∧
      Tendsto (realAverage (fun x => max (-A a ℓ x) 0)) atTop (𝓝 n) := by
  obtain ⟨p, hp⟩ := A_positive_mean_exists a hℓ
  obtain ⟨n, hn⟩ := A_negative_mean_exists a hℓ
  obtain ⟨E, hElo, hE⟩ := A_mean_square a hℓ
  have hQ : 0 < Q ℓ := by linarith [q_pos hℓ, two_q_le_Q hℓ]
  have hc := A_continuous a hℓ
  have hpc : Continuous (fun x => max (A a ℓ x) 0) := hc.max continuous_const
  have hnc : Continuous (fun x => max (-A a ℓ x) 0) := hc.neg.max continuous_const
  have hpn : p = n := by
    have hd := hp.sub hn
    have he : (fun T => realAverage (fun x => max (A a ℓ x) 0) T -
        realAverage (fun x => max (-A a ℓ x) 0) T) = realAverage (A a ℓ) := by
      funext T
      rw [← realAverage_sub hpc hnc]
      congr 1
      funext x
      exact real_decomposition _
    rw [he] at hd
    have hz := tendsto_nhds_unique hd (A_real_mean_zero a hℓ)
    linarith
  have hEB : E ≤ Q ℓ * (p + n) := by
    apply le_of_tendsto_of_tendsto hE ((hp.add hn).const_mul (Q ℓ))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hm := realAverage_mono
      (f := fun x => (A a ℓ x) ^ 2)
      (g := fun x => Q ℓ * (max (A a ℓ x) 0 + max (-A a ℓ x) 0)) (hc.pow 2)
      (continuous_const.mul (hpc.add hnc))
      (fun x => square_le_parts (A_bounded a hℓ x)) hT
    simpa only [realAverage_const_mul, realAverage_add hpc hnc] using hm
  have hrp : (q ℓ) ^ 2 / Q ℓ ≤ p := by
    apply (div_le_iff₀ hQ).mpr
    rw [hpn] at hEB ⊢
    nlinarith
  exact ⟨p, n, hpn, hrp, hpn ▸ hrp, hp, hn⟩

/-- Each sign attains a definite size before recurrence is used to move
the same sign arbitrarily far to the right. -/
theorem A_signed_values (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (∃ x : ℝ, (3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ) < A a ℓ x) ∧
      (∃ x : ℝ, A a ℓ x < -(3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ)) := by
  obtain ⟨p, n, _, hrp, hrn, hp, hn⟩ := A_signed_part_means a hℓ
  have hQ : 0 < Q ℓ := by linarith [q_pos hℓ, two_q_le_Q hℓ]
  have hr : 0 < (q ℓ) ^ 2 / Q ℓ := div_pos (sq_pos_of_pos (q_pos hℓ)) hQ
  constructor
  · by_contra! h
    have hbound : p ≤ (3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ) := by
      apply le_of_tendsto hp
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hb : ∀ x, |max (A a ℓ x) 0| ≤ (3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ) := by
        intro x
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (h x) (by positivity)
      exact (le_abs_self _).trans (realAverage_abs_le hT hb)
    linarith
  · by_contra! h
    have hbound : n ≤ (3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ) := by
      apply le_of_tendsto hn
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hb : ∀ x, |max (-A a ℓ x) 0| ≤ (3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ) := by
        intro x
        rw [abs_of_nonneg (le_max_right _ _)]
        apply max_le _ (by positivity)
        linarith [h x]
      exact (le_abs_self _).trans (realAverage_abs_le hT hb)
    linarith

end DepthAspect.MurmurationSignedMeans
