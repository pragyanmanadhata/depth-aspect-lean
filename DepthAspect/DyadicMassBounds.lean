import DepthAspect.DyadicSummation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Weighted finite sums from actual dyadic interval masses, for (125). -/
namespace DepthAspect.DyadicMassBounds

open scoped BigOperators

/-- Prefix moments are controlled by a uniform mass bound on actual
intervals `(x,2x]`, with the geometric constant displayed. -/
theorem prefix_bound {X a C : ℝ} (hX : 0 < X) (ha : 0 < a) (hC : 0 ≤ C)
    (S : Finset ℤ) (f : ℤ → ℝ)
    (hS : ∀ n ∈ S, 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X)
    (hf : ∀ n ∈ S, 0 ≤ f n)
    (hmass : ∀ x : ℝ, 0 < x →
      (∑ n ∈ S.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x), f n) ≤ C) :
    (∑ n ∈ S, f n * (n : ℝ) ^ a) ≤ C * X ^ a / (1 - (2 : ℝ) ^ (-a)) := by
  apply DyadicSummation.sum_bound hX.le ha hC S (fun n => f n * (n : ℝ) ^ a) hS
  intro j
  let U := DyadicSummation.endpoint X j
  have hU : 0 < U := DyadicSummation.endpoint_pos hX j
  have hset : DyadicSummation.block X j S =
      S.filter (fun n : ℤ => U / 2 < (n : ℝ) ∧ (n : ℝ) ≤ 2 * (U / 2)) := by
    unfold DyadicSummation.block
    rw [DyadicSummation.endpoint_succ]
    congr 1
    funext n
    simp only [U, show (2 : ℝ) * (DyadicSummation.endpoint X j / 2) =
      DyadicSummation.endpoint X j by ring]
  calc
    _ ≤ ∑ n ∈ DyadicSummation.block X j S, f n * U ^ a := by
      apply Finset.sum_le_sum
      intro n hn
      have hns := (Finset.mem_filter.mp hn).1
      have hnu := (Finset.mem_filter.mp hn).2.2
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith [(hS n hns).1]) hnu ha.le) (hf n hns)
    _ = (∑ n ∈ DyadicSummation.block X j S, f n) * U ^ a := (Finset.sum_mul ..).symm
    _ ≤ C * U ^ a := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [hset]
      exact hmass (U / 2) (by positivity)

noncomputable def outwardEndpoint (X : ℝ) (j : ℕ) : ℝ := X * (2 : ℝ) ^ j
noncomputable def outwardBlock (X : ℝ) (j : ℕ) (S : Finset ℤ) : Finset ℤ :=
  S.filter (fun n : ℤ => outwardEndpoint X j < (n : ℝ) ∧
    (n : ℝ) ≤ outwardEndpoint X (j + 1))

theorem outwardEndpoint_succ (X : ℝ) (j : ℕ) :
    outwardEndpoint X (j + 1) = 2 * outwardEndpoint X j := by
  simp only [outwardEndpoint, pow_succ]
  ring

theorem outward_partial_partition {X : ℝ} (hX : 0 ≤ X)
    (S : Finset ℤ) (f : ℤ → ℝ) (J : ℕ) :
    (∑ n ∈ S.filter (fun n : ℤ => (n : ℝ) ≤ outwardEndpoint X J), f n) =
      (∑ j ∈ Finset.range J, ∑ n ∈ outwardBlock X j S, f n) +
        ∑ n ∈ S.filter (fun n : ℤ => (n : ℝ) ≤ X), f n := by
  induction J with
  | zero => simp [outwardEndpoint]
  | succ J ih =>
    have hmono : outwardEndpoint X J ≤ outwardEndpoint X (J + 1) := by
      rw [outwardEndpoint_succ]
      have hp : 0 ≤ outwardEndpoint X J := by unfold outwardEndpoint; positivity
      linarith
    rw [DyadicSummation.cutoff_split S f hmono, ih, Finset.sum_range_succ]
    change (∑ n ∈ outwardBlock X J S, f n) +
      ((∑ j ∈ Finset.range J, ∑ n ∈ outwardBlock X j S, f n) +
        ∑ n ∈ S.filter (fun n : ℤ => (n : ℝ) ≤ X), f n) = _
    ring

/-- Every actual finite integer set lies below some outward dyadic endpoint. -/
theorem exists_outward_cutoff {X : ℝ} (hX : 0 < X) (S : Finset ℤ) :
    ∃ J : ℕ, ∀ n ∈ S, (n : ℝ) ≤ outwardEndpoint X J := by
  let Y : ℝ := ((S.sup Int.natAbs : ℕ) : ℝ) + 1
  obtain ⟨J, hJ⟩ := exists_nat_gt (Y / X)
  have hp : (J : ℝ) < (2 : ℝ) ^ J := by exact_mod_cast (Nat.lt_two_pow_self (n := J))
  have hY : Y < outwardEndpoint X J := by
    dsimp [outwardEndpoint]
    have h := (div_lt_iff₀ hX).mp (hJ.trans hp)
    simpa only [mul_comm] using h
  refine ⟨J, ?_⟩
  intro n hn
  have hnabs : (n : ℝ) ≤ (n.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact le_abs_self _
  have hnsup : (n.natAbs : ℝ) ≤ ((S.sup Int.natAbs : ℕ) : ℝ) := by
    exact_mod_cast Finset.le_sup hn
  exact (by dsimp [Y]; linarith : (n : ℝ) ≤ Y).trans hY.le

/-- The positive tail has an exact finite dyadic partition. -/
theorem outward_partition {X : ℝ} (hX : 0 ≤ X) (S : Finset ℤ) (f : ℤ → ℝ)
    (hS : ∀ n ∈ S, X < (n : ℝ)) (J : ℕ)
    (hJ : ∀ n ∈ S, (n : ℝ) ≤ outwardEndpoint X J) :
    (∑ n ∈ S, f n) = ∑ j ∈ Finset.range J, ∑ n ∈ outwardBlock X j S, f n := by
  have hfull : S.filter (fun n : ℤ => (n : ℝ) ≤ outwardEndpoint X J) = S :=
    Finset.filter_eq_self.mpr hJ
  have hempty : S.filter (fun n : ℤ => (n : ℝ) ≤ X) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    exact (not_le.mpr (hS n (Finset.mem_filter.mp hn).1)) (Finset.mem_filter.mp hn).2
  simpa only [hfull, hempty, Finset.sum_empty, add_zero] using
    outward_partial_partition hX S f J

/-- The negative powers of the outward endpoints give a convergent geometric
majorant, uniformly in the actual finite cutoff. -/
theorem outward_power_sum {X a : ℝ} (hX : 0 ≤ X) (ha : 0 < a) (J : ℕ) :
    (∑ j ∈ Finset.range J, outwardEndpoint X j ^ (-a)) ≤
      X ^ (-a) / (1 - (2 : ℝ) ^ (-a)) := by
  have he (j : ℕ) : outwardEndpoint X j ^ (-a) =
      X ^ (-a) * ((2 : ℝ) ^ (-a)) ^ j := by
    rw [outwardEndpoint, Real.mul_rpow hX (by positivity),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm (j : ℝ) (-a), Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  have hr0 : 0 ≤ (2 : ℝ) ^ (-a) := by positivity
  have hr1 : (2 : ℝ) ^ (-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : (∑ j ∈ Finset.range J, ((2 : ℝ) ^ (-a)) ^ j) ≤
      1 / (1 - (2 : ℝ) ^ (-a)) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0 hr1
  simp_rw [he]
  rw [← Finset.mul_sum]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ X ^ (-a))

/-- Uniform weighted tails over arbitrary actual finite integer sets.
The infinite tails in (125) follow by the nonnegative finite-sum criterion. -/
theorem tail_bound {X a C : ℝ} (hX : 0 < X) (ha : 0 < a) (hC : 0 ≤ C)
    (S : Finset ℤ) (f : ℤ → ℝ) (hS : ∀ n ∈ S, X < (n : ℝ))
    (hf : ∀ n ∈ S, 0 ≤ f n)
    (hmass : ∀ x : ℝ, X ≤ x →
      (∑ n ∈ S.filter (fun n : ℤ => x < (n : ℝ) ∧ (n : ℝ) ≤ 2 * x), f n) ≤ C) :
    (∑ n ∈ S, f n * (n : ℝ) ^ (-a)) ≤ C * X ^ (-a) / (1 - (2 : ℝ) ^ (-a)) := by
  obtain ⟨J, hJ⟩ := exists_outward_cutoff hX S
  rw [outward_partition hX.le S (fun n => f n * (n : ℝ) ^ (-a)) hS J hJ]
  have hb (j : ℕ) :
      (∑ n ∈ outwardBlock X j S, f n * (n : ℝ) ^ (-a)) ≤
        C * outwardEndpoint X j ^ (-a) := by
    have hj0 : 0 < outwardEndpoint X j := by unfold outwardEndpoint; positivity
    have hjX : X ≤ outwardEndpoint X j := by
      unfold outwardEndpoint
      exact le_mul_of_one_le_right hX.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    calc
      _ ≤ ∑ n ∈ outwardBlock X j S, f n * outwardEndpoint X j ^ (-a) := by
        apply Finset.sum_le_sum
        intro n hn
        have hns := (Finset.mem_filter.mp hn).1
        have hnj := (Finset.mem_filter.mp hn).2.1
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hj0 hnj.le (by linarith)) (hf n hns)
      _ = (∑ n ∈ outwardBlock X j S, f n) * outwardEndpoint X j ^ (-a) :=
        (Finset.sum_mul ..).symm
      _ ≤ C * outwardEndpoint X j ^ (-a) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        unfold outwardBlock
        rw [outwardEndpoint_succ]
        exact hmass _ hjX
  calc
    _ ≤ ∑ j ∈ Finset.range J, C * outwardEndpoint X j ^ (-a) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = C * ∑ j ∈ Finset.range J, outwardEndpoint X j ^ (-a) := (Finset.mul_sum ..).symm
    _ ≤ C * (X ^ (-a) / (1 - (2 : ℝ) ^ (-a))) :=
      mul_le_mul_of_nonneg_left (outward_power_sum hX.le ha J) hC
    _ = _ := by ring

end DepthAspect.DyadicMassBounds
