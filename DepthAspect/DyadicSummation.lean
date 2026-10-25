import DepthAspect.PrimePairBound
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# An actual finite dyadic partition and its geometric majorant

The partition covers any finite set of integers in `[1,X]`. Its number of
blocks is constructed by the Archimedean property; no infinite partition or
interchange of infinite sums is assumed.
-/
namespace DepthAspect.DyadicSummation

open scoped BigOperators

/-- Upper endpoint of the j-th dyadic interval. -/
noncomputable def endpoint (X : ℝ) (j : ℕ) : ℝ := X / (2 : ℝ) ^ j

/-- The actual finite subset in `(X/2^(j+1), X/2^j]`. -/
noncomputable def block (X : ℝ) (j : ℕ) (M : Finset ℤ) : Finset ℤ :=
  M.filter (fun m : ℤ => endpoint X (j + 1) < (m : ℝ) ∧ (m : ℝ) ≤ endpoint X j)

theorem endpoint_succ (X : ℝ) (j : ℕ) : endpoint X (j + 1) = endpoint X j / 2 := by
  simp only [endpoint, pow_succ]
  ring

theorem endpoint_pos {X : ℝ} (hX : 0 < X) (j : ℕ) : 0 < endpoint X j := by
  unfold endpoint
  positivity

theorem endpoint_le {X : ℝ} (hX : 0 ≤ X) (j : ℕ) : endpoint X j ≤ X := by
  unfold endpoint
  exact div_le_self hX (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem endpoint_succ_le {X : ℝ} (hX : 0 ≤ X) (j : ℕ) :
    endpoint X (j + 1) ≤ endpoint X j := by
  rw [endpoint_succ]
  have hx : 0 ≤ endpoint X j := by unfold endpoint; positivity
  linarith

/-- A finite cutoff splits exactly into the next annulus and smaller cutoff. -/
theorem cutoff_split (M : Finset ℤ) (f : ℤ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∑ m ∈ M.filter (fun m : ℤ => (m : ℝ) ≤ b), f m) =
      (∑ m ∈ M.filter (fun m : ℤ => a < (m : ℝ) ∧ (m : ℝ) ≤ b), f m) +
      (∑ m ∈ M.filter (fun m : ℤ => (m : ℝ) ≤ a), f m) := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ha : (m : ℝ) ≤ a
  · have hb : (m : ℝ) ≤ b := ha.trans hab
    simp [ha, hb, not_lt.mpr ha]
  · have halt : a < (m : ℝ) := lt_of_not_ge ha
    by_cases hb : (m : ℝ) ≤ b <;> simp [ha, halt, hb]

/-- The finite partition identity, with its final cutoff retained. -/
theorem partial_partition (M : Finset ℤ) (f : ℤ → ℝ) {X : ℝ} (hX : 0 ≤ X)
    (J : ℕ) :
    (∑ m ∈ M.filter (fun m : ℤ => (m : ℝ) ≤ X), f m) =
      (∑ j ∈ Finset.range J, ∑ m ∈ block X j M, f m) +
      (∑ m ∈ M.filter (fun m : ℤ => (m : ℝ) ≤ endpoint X J), f m) := by
  induction J with
  | zero => simp [endpoint]
  | succ J ih =>
    rw [Finset.sum_range_succ]
    rw [cutoff_split M f (endpoint_succ_le hX J)] at ih
    simpa only [block, add_assoc] using ih

/-- The cutoff vanishes once its endpoint is less than one. -/
theorem partition_sum (M : Finset ℤ) (f : ℤ → ℝ) {X : ℝ} (hX : 0 ≤ X)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (J : ℕ) (hJ : endpoint X J < 1) :
    (∑ m ∈ M, f m) = ∑ j ∈ Finset.range J, ∑ m ∈ block X j M, f m := by
  have hfull : M.filter (fun m : ℤ => (m : ℝ) ≤ X) = M := by
    apply Finset.filter_eq_self.mpr
    exact fun m hm => (hM m hm).2
  have hempty : M.filter (fun m : ℤ => (m : ℝ) ≤ endpoint X J) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    obtain ⟨hmM, hmlo⟩ := Finset.mem_filter.mp hm
    linarith [(hM m hmM).1]
  simpa only [hfull, hempty, Finset.sum_empty, add_zero] using partial_partition M f hX J

/-- Every positive real upper endpoint admits a finite dyadic cutoff. -/
theorem exists_cutoff (X : ℝ) : ∃ J : ℕ, endpoint X J < 1 := by
  obtain ⟨J, hJ⟩ := exists_nat_gt X
  have hp : (J : ℝ) < (2 : ℝ) ^ J := by exact_mod_cast (show J < 2 ^ J from Nat.lt_two_pow_self)
  refine ⟨J, ?_⟩
  exact (div_lt_one (by positivity : (0 : ℝ) < 2 ^ J)).mpr (hJ.trans hp)

/-- Powers of actual interval endpoints form the claimed geometric progression. -/
theorem endpoint_rpow {X : ℝ} (hX : 0 ≤ X) (a : ℝ) (j : ℕ) :
    endpoint X j ^ a = X ^ a * ((2 : ℝ) ^ (-a)) ^ j := by
  rw [endpoint, Real.div_rpow hX (by positivity),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (j : ℝ) a,
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    div_eq_mul_inv, ← inv_pow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The exact finite geometric majorant, uniform in the number of dyadic blocks. -/
theorem endpoint_power_sum_bound {X a : ℝ} (hX : 0 ≤ X) (ha : 0 < a) (J : ℕ) :
    (∑ j ∈ Finset.range J, endpoint X j ^ a) ≤
      X ^ a / (1 - (2 : ℝ) ^ (-a)) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-a) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-a) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ha)
  have hg : (∑ j ∈ Finset.range J, ((2 : ℝ) ^ (-a)) ^ j) ≤
      1 / (1 - (2 : ℝ) ^ (-a)) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0 hr1)
  simp_rw [endpoint_rpow hX a]
  rw [← Finset.mul_sum]
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hX a)

/-- Dyadic summation over an actual finite set, with the geometric denominator
that appears in equation (45). -/
theorem sum_bound {X a C : ℝ} (hX : 0 ≤ X) (ha : 0 < a) (hC : 0 ≤ C)
    (M : Finset ℤ) (f : ℤ → ℝ)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (hb : ∀ j : ℕ, (∑ m ∈ block X j M, f m) ≤ C * endpoint X j ^ a) :
    (∑ m ∈ M, f m) ≤ C * X ^ a / (1 - (2 : ℝ) ^ (-a)) := by
  obtain ⟨J, hJ⟩ := exists_cutoff X
  rw [partition_sum M f hX hM J hJ]
  calc
    _ ≤ ∑ j ∈ Finset.range J, C * endpoint X j ^ a :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = C * (∑ j ∈ Finset.range J, endpoint X j ^ a) := (Finset.mul_sum ..).symm
    _ ≤ C * (X ^ a / (1 - (2 : ℝ) ^ (-a))) :=
      mul_le_mul_of_nonneg_left (endpoint_power_sum_bound hX ha J) hC
    _ = _ := by ring

end DepthAspect.DyadicSummation
