import DepthAspect.MurmurationOscillationSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! The explicit rational-period recurrence used after (134). -/
open Filter
open scoped BigOperators Topology
namespace DepthAspect.MurmurationRecurrence
open MurmurationOscillationSeries

/-- Every actual summand has the positive integer d as a period. -/
theorem oscillationTerm_period (a ℓ : ℕ) (i : ℕ+ × ℕ+) :
    Function.Periodic (oscillationTerm a ℓ i) (i.1 : ℝ) := by
  intro x
  have hd : (i.1 : ℝ) ≠ 0 := by exact_mod_cast i.1.ne_zero
  have h1 : 4 * Real.pi * (i.2 : ℝ) * (x + i.1) / i.1 - phase a =
      (4 * Real.pi * i.2 * x / i.1 - phase a) +
        (((2 * (i.2 : ℕ) : ℕ) : ℝ)) * (2 * Real.pi) := by
    push_cast
    field_simp [hd]
    <;> ring
  have h2 : 4 * Real.pi * (ℓ : ℝ) * (i.2 : ℝ) * (x + i.1) / i.1 - phase a =
      (4 * Real.pi * ℓ * i.2 * x / i.1 - phase a) +
        (((2 * ℓ * (i.2 : ℕ) : ℕ) : ℝ)) * (2 * Real.pi) := by
    push_cast
    field_simp [hd]
    <;> ring
  unfold oscillationTerm
  rw [h1, h2, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]

/-- The product of the finitely many d indices is a common positive
integer period; repeated denominators cause no difficulty. -/
theorem finite_sum_period (a ℓ : ℕ) (s : Finset (ℕ+ × ℕ+)) :
    ∃ P : ℕ, 0 < P ∧ Function.Periodic
      (fun x => ∑ i ∈ s, oscillationTerm a ℓ i x) (P : ℝ) := by
  let P : ℕ := ∏ i ∈ s, (i.1 : ℕ)
  have hP : 0 < P := Finset.prod_pos (fun i _ => i.1.pos)
  refine ⟨P, hP, ?_⟩
  intro x
  apply Finset.sum_congr rfl
  intro i hi
  have hdvd : (i.1 : ℕ) ∣ P := Finset.dvd_prod_of_mem (fun i : ℕ+ × ℕ+ => (i.1 : ℕ)) hi
  obtain ⟨n, hn⟩ := hdvd
  have hp := (oscillationTerm_period a ℓ i).nat_mul n
  have hc : (P : ℝ) = (n : ℝ) * (i.1 : ℝ) := by rw [hn]; push_cast; ring
  rw [hc]
  exact hp x

/-- Uniform approximation by a finite sum gives arbitrarily accurate
integer-multiple periods for the entire actual series. -/
theorem approximate_periods (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℕ, 0 < P ∧ ∀ j : ℕ, ∀ x : ℝ,
      |A a ℓ (x + (j : ℝ) * P) - A a ℓ x| < ε := by
  obtain ⟨s, hs⟩ := (Metric.tendstoUniformly_iff.mp (A_uniform a hℓ)
    (ε / 2) (by positivity)).exists
  obtain ⟨P, hP, hp⟩ := finite_sum_period a ℓ s
  refine ⟨P, hP, ?_⟩
  intro j x
  have he := hp.nat_mul j x
  have h₁ := hs (x + (j : ℝ) * P)
  have h₂ := hs x
  rw [Real.dist_eq] at h₁ h₂
  calc
    _ ≤ |A a ℓ (x + (j : ℝ) * P) - ∑ i ∈ s, oscillationTerm a ℓ i (x + (j : ℝ) * P)| +
        |(∑ i ∈ s, oscillationTerm a ℓ i (x + (j : ℝ) * P)) - A a ℓ x| := abs_sub_le _ _ _
    _ < ε := by
      rw [he] at h₁ ⊢
      have h₂' : |(∑ i ∈ s, oscillationTerm a ℓ i x) - A a ℓ x| < ε / 2 := by
        simpa only [abs_sub_comm] using h₂
      linarith

/-- Every value recurs to arbitrary accuracy arbitrarily far to the right.
This supplies the recurrence argument without assuming almost periodicity. -/
theorem recurrent_values (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (x L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ, L < u ∧ |A a ℓ u - A a ℓ x| < ε := by
  obtain ⟨P, hP, hp⟩ := approximate_periods a hℓ hε
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  obtain ⟨j, hj⟩ := exists_nat_gt ((L - x) / P)
  refine ⟨x + (j : ℝ) * P, ?_, hp j x⟩
  have hh := (div_lt_iff₀ hPR).mp hj
  linarith

end DepthAspect.MurmurationRecurrence
