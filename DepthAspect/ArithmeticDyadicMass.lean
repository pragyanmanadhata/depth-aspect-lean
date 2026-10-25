import DepthAspect.ArithmeticSummatoryLimit
import Mathlib.Algebra.BigOperators.Intervals

/-! The actual uniform dyadic masses needed in (125), derived from (123). -/
namespace DepthAspect.ArithmeticWeights

open scoped BigOperators

noncomputable def asymptoticConstant (ℓ : ℕ) : ℝ :=
  ((14 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * coefficientMoment ℓ

noncomputable def dyadicMassConstant (ℓ : ℕ) : ℝ :=
  1 + |R ℓ| * Real.log 2 + 2 * asymptoticConstant ℓ

noncomputable def dyadicMass (ℓ : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, c ℓ n

theorem asymptoticConstant_nonneg (ℓ : ℕ) : 0 ≤ asymptoticConstant ℓ := by
  unfold asymptoticConstant coefficientMoment
  positivity

theorem dyadicMassConstant_ge_one (ℓ : ℕ) : 1 ≤ dyadicMassConstant ℓ := by
  have hK := asymptoticConstant_nonneg ℓ
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold dyadicMassConstant
  nlinarith [mul_nonneg (abs_nonneg (R ℓ)) hlog]

/-- Exact difference of the literal partial sums, including real endpoints. -/
theorem dyadicMass_eq (ℓ : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    dyadicMass ℓ X = partialC ℓ (2 * X) - partialC ℓ X := by
  have ht := Finset.sum_Ioc_consecutive (c ℓ) (Nat.zero_le ⌊X⌋₊)
    (Nat.floor_mono (show X ≤ 2 * X by linarith))
  change partialC ℓ X + dyadicMass ℓ X = partialC ℓ (2 * X) at ht
  linarith

/-- Uniform mass on every dyadic interval with endpoint at least one. -/
theorem dyadicMass_bound_large (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    dyadicMass ℓ X ≤ |R ℓ| * Real.log 2 + 2 * asymptoticConstant ℓ := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have h2X : 1 ≤ 2 * X := by linarith
  have hK := asymptoticConstant_nonneg ℓ
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h₁ : |partialC ℓ X - (R ℓ * Real.log X + constantTerm ℓ)| ≤ asymptoticConstant ℓ := by
    apply (summatory_asymptotic ℓ hX).trans
    simpa only [asymptoticConstant, mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num : (-1 / 4 : ℝ) ≤ 0)) hK
  have h₂ : |partialC ℓ (2 * X) - (R ℓ * Real.log (2 * X) + constantTerm ℓ)| ≤
      asymptoticConstant ℓ := by
    apply (summatory_asymptotic ℓ h2X).trans
    simpa only [asymptoticConstant, mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos h2X (by norm_num : (-1 / 4 : ℝ) ≤ 0)) hK
  have hR := mul_le_mul_of_nonneg_right (le_abs_self (R ℓ)) hlog
  rw [dyadicMass_eq ℓ hX0.le, Real.log_mul (by norm_num) hX0.ne'] at *
  have hu := (abs_le.mp h₂).2
  have hl := (abs_le.mp h₁).1
  nlinarith

/-- The small interval contains at most the single integer one. -/
theorem dyadicMass_bound_small (ℓ : ℕ) {X : ℝ} (hX0 : 0 < X) (hX1 : X < 1) :
    dyadicMass ℓ X ≤ 1 := by
  have hfloor : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr hX1
  have htop : ⌊2 * X⌋₊ < 2 := (Nat.floor_lt (by positivity)).mpr (by norm_num; linarith)
  by_cases ht : ⌊2 * X⌋₊ = 0
  · simp [dyadicMass, hfloor, ht]
  · have ht1 : ⌊2 * X⌋₊ = 1 := by omega
    have hset : Finset.Ioc (0 : ℕ) 1 = {1} := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_singleton]
      omega
    simp [dyadicMass, hfloor, ht1, hset, c_one]

/-- A single constant bounds every actual interval `(X,2X]`, including the
small final prefix interval in a descending dyadic partition. -/
theorem dyadicMass_bound (ℓ : ℕ) {X : ℝ} (hX : 0 < X) :
    dyadicMass ℓ X ≤ dyadicMassConstant ℓ := by
  by_cases hX1 : 1 ≤ X
  · have ht := dyadicMass_bound_large ℓ hX1
    unfold dyadicMassConstant
    linarith
  · exact (dyadicMass_bound_small ℓ hX (lt_of_not_ge hX1)).trans
      (dyadicMassConstant_ge_one ℓ)

/-- Every actual finite subset of an interval obeys the same mass bound,
since the cℓ coefficients were proved nonnegative from their definition. -/
theorem finite_interval_mass (ℓ : ℕ) (S : Finset ℕ) {X : ℝ} (hX : 0 < X) :
    (∑ n ∈ S.filter (fun n : ℕ => X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X), c ℓ n) ≤
      dyadicMassConstant ℓ := by
  apply le_trans _ (dyadicMass_bound ℓ hX)
  unfold dyadicMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨_, hnlo, hnhi⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hX.le).mpr hnlo, Nat.le_floor hnhi⟩
  · intro n _ _
    exact c_nonneg ℓ n

end DepthAspect.ArithmeticWeights
