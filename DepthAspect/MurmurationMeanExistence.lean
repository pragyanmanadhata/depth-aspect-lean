import DepthAspect.MurmurationRecurrence
import DepthAspect.MurmurationBohrCoefficient
import DepthAspect.UniformPeriodicMean

/-! Means of the square and the two signed parts of the literal function A.
Uniform approximation is proved from its actual absolutely convergent series. -/
open Filter
open scoped BigOperators Topology
namespace DepthAspect.MurmurationMeanExistence
open MurmurationOscillationSeries MurmurationRecurrence MurmurationBohrCoefficient
  UniformPeriodicMean

theorem A_periodic_approximation (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∃ P > 0, Function.Periodic g P) ∧
      ∀ x, |A a ℓ x - g x| ≤ ε := by
  obtain ⟨s, hs⟩ := (Metric.tendstoUniformly_iff.mp (A_uniform a hℓ) ε hε).exists
  obtain ⟨P, hP, hp⟩ := finite_sum_period a ℓ s
  refine ⟨fun x => ∑ i ∈ s, oscillationTerm a ℓ i x, ?_, ⟨P, ?_, hp⟩, ?_⟩
  · apply continuous_finset_sum
    intro i _
    unfold oscillationTerm
    fun_prop
  · exact_mod_cast hP
  · intro x
    have h := (hs x).le
    simpa only [Real.dist_eq, abs_sub_comm] using h

/-- Positive and negative parts retain the same uniform approximation error. -/
theorem A_positive_mean_exists (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ L : ℝ, Tendsto (realAverage (fun x => max (A a ℓ x) 0)) atTop (𝓝 L) := by
  apply mean_exists_of_uniform_periodic (f := fun x => max (A a ℓ x) 0)
    ((A_continuous a hℓ).max continuous_const)
  intro ε hε
  obtain ⟨g, hg, ⟨P, hP, hp⟩, he⟩ := A_periodic_approximation a hℓ hε
  refine ⟨fun x => max (g x) 0, hg.max continuous_const,
    ⟨P, hP, ?_⟩, ?_⟩
  · intro x
    change max (g (x + P)) 0 = max (g x) 0
    rw [hp x]
  · intro x
    exact (abs_max_sub_max_le_abs (A a ℓ x) (g x) 0).trans (he x)

theorem A_negative_mean_exists (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ L : ℝ, Tendsto (realAverage (fun x => max (-A a ℓ x) 0)) atTop (𝓝 L) := by
  apply mean_exists_of_uniform_periodic (f := fun x => max (-A a ℓ x) 0)
    ((A_continuous a hℓ).neg.max continuous_const)
  intro ε hε
  obtain ⟨g, hg, ⟨P, hP, hp⟩, he⟩ := A_periodic_approximation a hℓ hε
  refine ⟨fun x => max (-g x) 0, hg.neg.max continuous_const,
    ⟨P, hP, ?_⟩, ?_⟩
  · intro x
    change max (-g (x + P)) 0 = max (-g x) 0
    rw [hp x]
  · intro x
    have ht := abs_max_sub_max_le_abs (-A a ℓ x) (-g x) 0
    have hn : |-A a ℓ x - -g x| = |A a ℓ x - g x| := by
      rw [neg_sub_neg, abs_sub_comm]
    rw [hn] at ht
    exact ht.trans (he x)

/-- Boundedness of A controls the square when passing from the finite
periodic sums to the full series; uniform convergence alone is not silently
used as a global Lipschitz statement for squaring. -/
theorem A_square_mean_exists (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ L : ℝ, Tendsto (realAverage (fun x => (A a ℓ x) ^ 2)) atTop (𝓝 L) := by
  have hq := q_pos hℓ
  have hQ : 0 < Q ℓ := by linarith [two_q_le_Q hℓ]
  apply mean_exists_of_uniform_periodic (f := fun x => (A a ℓ x) ^ 2)
    ((A_continuous a hℓ).pow 2)
  intro ε hε
  let δ : ℝ := min 1 (ε / (2 * Q ℓ + 1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  obtain ⟨g, hg, ⟨P, hP, hp⟩, he⟩ := A_periodic_approximation a hℓ hδ
  refine ⟨fun x => (g x) ^ 2, hg.pow 2, ⟨P, hP, ?_⟩, ?_⟩
  · intro x
    change (g (x + P)) ^ 2 = (g x) ^ 2
    rw [hp x]
  · intro x
    change |(A a ℓ x) ^ 2 - (g x) ^ 2| ≤ ε
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδε : δ * (2 * Q ℓ + 1) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hgB : |g x| ≤ Q ℓ + 1 := by
      have ht := abs_sub_le (g x) (A a ℓ x) 0
      simp only [sub_zero, abs_sub_comm (g x) (A a ℓ x)] at ht
      linarith [he x, A_bounded a hℓ x]
    have hsum : |A a ℓ x + g x| ≤ 2 * Q ℓ + 1 :=
      (abs_add_le _ _).trans (by linarith [A_bounded a hℓ x])
    rw [show (A a ℓ x) ^ 2 - (g x) ^ 2 =
      (A a ℓ x - g x) * (A a ℓ x + g x) by ring, abs_mul]
    exact (mul_le_mul (he x) hsum (abs_nonneg _) hδ.le).trans hδε

/-- The complex zero-mean statement gives the actual real mean. -/
theorem A_real_mean_zero (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Tendsto (realAverage (A a ℓ)) atTop (𝓝 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (A_mean_zero a hℓ)
  simpa only [Function.comp_def, ← realAverage_cast, Complex.ofReal_re, Complex.zero_re] using h

end DepthAspect.MurmurationMeanExistence
