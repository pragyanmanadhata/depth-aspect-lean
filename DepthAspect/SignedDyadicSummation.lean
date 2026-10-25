import DepthAspect.DyadicSummation
import DepthAspect.UnsignedExponents
import Mathlib.Tactic.Abel

/-!
# The actual finite dyadic summation in (113)

The final interval is truncated at 2. The proof telescopes literal prefix
values on an actual finite partition and retains both geometric constants.
The per-block arithmetic estimate is an explicitly named intermediate.
-/
namespace DepthAspect.SignedDyadicSummation

open DyadicSummation
open scoped BigOperators

noncomputable def cutoff (X : ℝ) (j : ℕ) : ℝ := max 2 (endpoint X j)

theorem finite_telescope (F : ℝ → ℂ) (X : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, (F (cutoff X j) - F (cutoff X (j + 1)))) =
      F (cutoff X 0) - F (cutoff X J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    abel

/-- Consecutive dyadic intervals beginning at 2, with the last one
truncated, give the two geometric factors in (113). -/
theorem two_power_sum_bound {X a b C₀ C₁ : ℝ} (hX : 2 ≤ X)
    (ha : 0 < a) (hb : 0 < b) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (F : ℝ → ℂ)
    (hblock : ∀ A B : ℝ, 2 ≤ A → A ≤ B → B ≤ 2 * A →
      ‖F B - F A‖ ≤ C₀ * A ^ a + C₁ * A ^ b) :
    ‖F X - F 2‖ ≤ C₀ * X ^ a / (1 - (2 : ℝ) ^ (-a)) +
      C₁ * X ^ b / (1 - (2 : ℝ) ^ (-b)) := by
  have hX0 : 0 ≤ X := by linarith
  obtain ⟨J, hJ⟩ := exists_cutoff X
  have hzero : cutoff X 0 = X := by simp [cutoff, endpoint, max_eq_right hX]
  have hlast : cutoff X J = 2 := max_eq_left (by linarith)
  have hpoint (j : ℕ) :
      ‖F (cutoff X j) - F (cutoff X (j + 1))‖ ≤
        C₀ * endpoint X j ^ a + C₁ * endpoint X j ^ b := by
    by_cases hsmall : endpoint X j ≤ 2
    · have hnext := (endpoint_succ_le hX0 j).trans hsmall
      simp only [cutoff, max_eq_left hsmall, max_eq_left hnext, sub_self, norm_zero]
      have hend : 0 ≤ endpoint X j := by unfold endpoint; positivity
      exact add_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg hend a))
        (mul_nonneg hC₁ (Real.rpow_nonneg hend b))
    · have hlarge : 2 < endpoint X j := lt_of_not_ge hsmall
      have hcurrent : cutoff X j = endpoint X j := max_eq_right hlarge.le
      have hA : 2 ≤ cutoff X (j + 1) := le_max_left _ _
      have hAB : cutoff X (j + 1) ≤ cutoff X j :=
        max_le_max_left _ (endpoint_succ_le hX0 j)
      have hB : cutoff X j ≤ 2 * cutoff X (j + 1) := by
        rw [hcurrent, cutoff, endpoint_succ]
        have hm := le_max_right (2 : ℝ) (endpoint X j / 2)
        linarith
      have hp := hblock (cutoff X (j + 1)) (cutoff X j) hA hAB hB
      have hle : cutoff X (j + 1) ≤ endpoint X j := by rwa [hcurrent] at hAB
      exact hp.trans (add_le_add
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith : 0 ≤ cutoff X (j + 1)) hle ha.le) hC₀)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith : 0 ≤ cutoff X (j + 1)) hle hb.le) hC₁))
  have ht : F X - F 2 =
      ∑ j ∈ Finset.range J, (F (cutoff X j) - F (cutoff X (j + 1))) := by
    simpa only [hzero, hlast] using (finite_telescope F X J).symm
  rw [ht]
  calc
    _ ≤ ∑ j ∈ Finset.range J, ‖F (cutoff X j) - F (cutoff X (j + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, (C₀ * endpoint X j ^ a + C₁ * endpoint X j ^ b) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = C₀ * (∑ j ∈ Finset.range J, endpoint X j ^ a) +
        C₁ * (∑ j ∈ Finset.range J, endpoint X j ^ b) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ C₀ * (X ^ a / (1 - (2 : ℝ) ^ (-a))) +
        C₁ * (X ^ b / (1 - (2 : ℝ) ^ (-b))) := add_le_add
      (mul_le_mul_of_nonneg_left (endpoint_power_sum_bound hX0 ha J) hC₀)
      (mul_le_mul_of_nonneg_left (endpoint_power_sum_bound hX0 hb J) hC₁)
    _ = _ := by ring

/-- The same finite partition only needs block estimates below its actual
upper endpoint; this retains the compact-support cutoff in applications. -/
theorem two_power_sum_bound_bounded {X a b C₀ C₁ : ℝ} (hX : 2 ≤ X)
    (ha : 0 < a) (hb : 0 < b) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (F : ℝ → ℂ)
    (hblock : ∀ A B : ℝ, 2 ≤ A → A ≤ B → B ≤ 2 * A → B ≤ X →
      ‖F B - F A‖ ≤ C₀ * A ^ a + C₁ * A ^ b) :
    ‖F X - F 2‖ ≤ C₀ * X ^ a / (1 - (2 : ℝ) ^ (-a)) +
      C₁ * X ^ b / (1 - (2 : ℝ) ^ (-b)) := by
  have hX0 : 0 ≤ X := by linarith
  obtain ⟨J, hJ⟩ := exists_cutoff X
  have hzero : cutoff X 0 = X := by simp [cutoff, endpoint, max_eq_right hX]
  have hlast : cutoff X J = 2 := max_eq_left (by linarith)
  have hpoint (j : ℕ) :
      ‖F (cutoff X j) - F (cutoff X (j + 1))‖ ≤
        C₀ * endpoint X j ^ a + C₁ * endpoint X j ^ b := by
    by_cases hsmall : endpoint X j ≤ 2
    · have hnext := (endpoint_succ_le hX0 j).trans hsmall
      simp only [cutoff, max_eq_left hsmall, max_eq_left hnext, sub_self, norm_zero]
      have hend : 0 ≤ endpoint X j := by unfold endpoint; positivity
      exact add_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg hend a))
        (mul_nonneg hC₁ (Real.rpow_nonneg hend b))
    · have hlarge : 2 < endpoint X j := lt_of_not_ge hsmall
      have hcurrent : cutoff X j = endpoint X j := max_eq_right hlarge.le
      have hA : 2 ≤ cutoff X (j + 1) := le_max_left _ _
      have hAB : cutoff X (j + 1) ≤ cutoff X j :=
        max_le_max_left _ (endpoint_succ_le hX0 j)
      have hB : cutoff X j ≤ 2 * cutoff X (j + 1) := by
        rw [hcurrent, cutoff, endpoint_succ]
        have hm := le_max_right (2 : ℝ) (endpoint X j / 2)
        linarith
      have hp := hblock (cutoff X (j + 1)) (cutoff X j) hA hAB hB
        (max_le hX (endpoint_le hX0 j))
      have hle : cutoff X (j + 1) ≤ endpoint X j := by rwa [hcurrent] at hAB
      exact hp.trans (add_le_add
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith : 0 ≤ cutoff X (j + 1)) hle ha.le) hC₀)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith : 0 ≤ cutoff X (j + 1)) hle hb.le) hC₁))
  have ht : F X - F 2 =
      ∑ j ∈ Finset.range J, (F (cutoff X j) - F (cutoff X (j + 1))) := by
    simpa only [hzero, hlast] using (finite_telescope F X J).symm
  rw [ht]
  calc
    _ ≤ ∑ j ∈ Finset.range J, ‖F (cutoff X j) - F (cutoff X (j + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, (C₀ * endpoint X j ^ a + C₁ * endpoint X j ^ b) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = C₀ * (∑ j ∈ Finset.range J, endpoint X j ^ a) +
        C₁ * (∑ j ∈ Finset.range J, endpoint X j ^ b) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ C₀ * (X ^ a / (1 - (2 : ℝ) ^ (-a))) +
        C₁ * (X ^ b / (1 - (2 : ℝ) ^ (-b))) := add_le_add
      (mul_le_mul_of_nonneg_left (endpoint_power_sum_bound hX0 ha J) hC₀)
      (mul_le_mul_of_nonneg_left (endpoint_power_sum_bound hX0 hb J) hC₁)
    _ = _ := by ring

end DepthAspect.SignedDyadicSummation
