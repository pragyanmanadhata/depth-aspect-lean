import DepthAspect.ArithmeticSummatory
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The actual summatory asymptotic in (123)

The main sums are extended to infinity using the proved coefficient moment.
The argument retains `log (n / X)` in the tail and therefore obtains the
stronger `X^(-3/8)` error before weakening it to the paper's `X^(-1/4)`.
-/
namespace DepthAspect.ArithmeticWeights

open scoped BigOperators

noncomputable def coefficientMoment (ℓ : ℕ) : ℝ :=
  ∑' n : ℕ, |h ℓ n| * (n : ℝ) ^ (3 / 8 : ℝ)

noncomputable def R (ℓ : ℕ) : ℝ := ∑' n : ℕ, h ℓ n
noncomputable def constantTerm (ℓ : ℕ) : ℝ :=
  Real.eulerMascheroniConstant * R ℓ - ∑' n : ℕ, h ℓ n * Real.log n

/-- Absolute convergence of the constant coefficient sum in (123). -/
theorem coefficient_abs_summable (ℓ : ℕ) : Summable (fun n : ℕ => |h ℓ n|) := by
  have hs := weightedAbs_summable ℓ
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1 / 2)
  change Summable (fun n : ℕ => |h ℓ n| * (n : ℝ) ^ (0 : ℝ)) at hs
  simpa only [Real.rpow_zero, mul_one] using hs

theorem coefficient_summable (ℓ : ℕ) : Summable (fun n : ℕ => h ℓ n) := by
  have hn : Summable (fun n : ℕ => ‖h ℓ n‖) := by
    simpa only [Real.norm_eq_abs] using coefficient_abs_summable ℓ
  exact hn.of_norm

/-- The logarithmic coefficient sum is genuinely absolutely convergent. -/
theorem coefficient_log_summable (ℓ : ℕ) : Summable (fun n : ℕ => h ℓ n * Real.log n) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun n : ℕ => (8 / 3 : ℝ) * (|h ℓ n| * (n : ℝ) ^ (3 / 8 : ℝ)))
  · intro n
    rw [norm_mul, Real.norm_eq_abs]
    have ht : ‖Real.log (n : ℝ)‖ ≤ (n : ℝ) ^ (3 / 8 : ℝ) / (3 / 8) := by
      by_cases hn : n = 0
      · subst n
        norm_num
      · rw [Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn))]
        exact Real.log_natCast_le_rpow_div n (by norm_num)
    have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg (h ℓ n))
    calc
      _ ≤ |h ℓ n| * ((n : ℝ) ^ (3 / 8 : ℝ) / (3 / 8)) := hm
      _ = (8 / 3 : ℝ) * (|h ℓ n| * (n : ℝ) ^ (3 / 8 : ℝ)) := by ring
  · exact (coefficient_three_eighth_moment ℓ).mul_left (8 / 3)

noncomputable def mainCoefficient (ℓ : ℕ) (X : ℝ) (n : ℕ) : ℝ :=
  h ℓ n * (Real.log X - Real.log n + Real.eulerMascheroniConstant)

theorem mainCoefficient_summable (ℓ : ℕ) (X : ℝ) : Summable (mainCoefficient ℓ X) := by
  have hm := (coefficient_summable ℓ).mul_right
    (Real.log X + Real.eulerMascheroniConstant)
  have hs := hm.sub (coefficient_log_summable ℓ)
  apply hs.congr
  intro n
  unfold mainCoefficient
  ring

theorem mainCoefficient_tsum (ℓ : ℕ) (X : ℝ) :
    (∑' n : ℕ, mainCoefficient ℓ X n) = R ℓ * Real.log X + constantTerm ℓ := by
  have he : mainCoefficient ℓ X = fun n : ℕ =>
      h ℓ n * (Real.log X + Real.eulerMascheroniConstant) - h ℓ n * Real.log n := by
    funext n
    unfold mainCoefficient
    ring
  rw [he, Summable.tsum_sub ((coefficient_summable ℓ).mul_right _)
    (coefficient_log_summable ℓ), tsum_mul_right]
  simp only [constantTerm, R]
  ring

/-- The logarithmic kernel on the omitted range is controlled by the same
three-eighth moment, uniformly in the endpoint. -/
theorem logarithmic_tail_kernel {X t : ℝ} (hX : 1 ≤ X) (ht : X < t) :
    |Real.log X - Real.log t + Real.eulerMascheroniConstant| ≤
      ((8 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * (t / X) ^ (3 / 8 : ℝ) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have ht0 : 0 < t := hX0.trans ht
  have hratio : 1 ≤ t / X := (le_div_iff₀ hX0).mpr (by simpa using ht.le)
  have hlog : Real.log X ≤ Real.log t := Real.log_le_log hX0 ht.le
  have hid : |Real.log X - Real.log t| = Real.log (t / X) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), Real.log_div ht0.ne' hX0.ne']
    ring
  have hl := Real.log_le_rpow_div (div_nonneg ht0.le hX0.le)
    (by norm_num : (0 : ℝ) < 3 / 8)
  have hp := Real.one_le_rpow hratio (by norm_num : (0 : ℝ) ≤ 3 / 8)
  calc
    _ ≤ |Real.log X - Real.log t| + |Real.eulerMascheroniConstant| := abs_add_le _ _
    _ = Real.log (t / X) + |Real.eulerMascheroniConstant| := by rw [hid]
    _ ≤ ((8 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * (t / X) ^ (3 / 8 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg Real.eulerMascheroniConstant)]

/-- A pointwise bound on every omitted coefficient, including the harmless
zero index of the natural-number encoding. -/
theorem mainCoefficient_tail_bound (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 ⌊X⌋₊) :
    ‖mainCoefficient ℓ X n‖ ≤
      (((8 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * X ^ (-3 / 8 : ℝ)) *
        (|h ℓ n| * (n : ℝ) ^ (3 / 8 : ℝ)) := by
  by_cases hn0 : n = 0
  · subst n
    simp [mainCoefficient]
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hnf : ⌊X⌋₊ < n := by
    simp only [Finset.mem_Ioc, not_and] at hn
    exact lt_of_not_ge (hn hnpos)
  have hnX : X < (n : ℝ) := (Nat.floor_lt (by positivity)).mp hnf
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [mainCoefficient, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |h ℓ n| * (((8 / 3 : ℝ) + |Real.eulerMascheroniConstant|) *
        ((n : ℝ) / X) ^ (3 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (logarithmic_tail_kernel hX hnX) (abs_nonneg _)
    _ = _ := by
      rw [Real.div_rpow hnr.le hX0.le,
        show (-3 / 8 : ℝ) = -(3 / 8) by norm_num, Real.rpow_neg hX0.le]
      ring

/-- Passing from the actual finite main sum to the actual infinite main
sum costs at most a fixed multiple of the coefficient moment. -/
theorem finite_main_tail_error (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, mainCoefficient ℓ X n) -
      (R ℓ * Real.log X + constantTerm ℓ)| ≤
      ((8 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * coefficientMoment ℓ *
        X ^ (-3 / 8 : ℝ) := by
  let S := Finset.Ioc 0 ⌊X⌋₊
  let C := ((8 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * X ^ (-3 / 8 : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnorm := (mainCoefficient_summable ℓ X).norm
  have hbound : (∑' n : {n // n ∉ S}, ‖mainCoefficient ℓ X n‖) ≤
      C * coefficientMoment ℓ := by
    calc
      _ ≤ ∑' n : {n // n ∉ S}, C * (|h ℓ n| * (n : ℝ) ^ (3 / 8 : ℝ)) :=
        (hnorm.subtype _).tsum_le_tsum (fun n => mainCoefficient_tail_bound ℓ hX n n.property)
          (((coefficient_three_eighth_moment ℓ).mul_left C).subtype _)
      _ = C * ∑' n : {n // n ∉ S}, |h ℓ n| * (n : ℝ) ^ (3 / 8 : ℝ) := tsum_mul_left
      _ ≤ C * coefficientMoment ℓ := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact Summable.tsum_le_tsum_of_inj ((↑) : {n // n ∉ S} → ℕ)
          Subtype.coe_injective (fun _ _ => by positivity) (fun _ => le_rfl)
          ((coefficient_three_eighth_moment ℓ).subtype _) (coefficient_three_eighth_moment ℓ)
  have hid := (mainCoefficient_summable ℓ X).sum_add_tsum_subtype_compl S
  have he : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, mainCoefficient ℓ X n) -
      (R ℓ * Real.log X + constantTerm ℓ) =
        -(∑' n : {n // n ∉ S}, mainCoefficient ℓ X n) := by
    rw [← mainCoefficient_tsum]
    change (∑ n ∈ S, mainCoefficient ℓ X n) - _ = _
    linarith [hid]
  rw [he, abs_neg]
  have ht := (norm_tsum_le_tsum_norm (hnorm.subtype (fun n => n ∉ S))).trans hbound
  simpa only [Real.norm_eq_abs, C, coefficientMoment, mul_assoc, mul_comm, mul_left_comm] using ht

/-- A stronger quantitative form of the first line of (123), for the
literal finite sum over `d ≤ X`. -/
theorem summatory_asymptotic_strong (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |partialC ℓ X - (R ℓ * Real.log X + constantTerm ℓ)| ≤
      ((14 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * coefficientMoment ℓ *
        X ^ (-3 / 8 : ℝ) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have he : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      h ℓ n * (Real.log (X / n) + Real.eulerMascheroniConstant)) =
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, mainCoefficient ℓ X n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.ne'
    rw [Real.log_div hX0.ne' hn0]
    rfl
  have h₁ := partialC_harmonic_moment_error ℓ hX
  rw [he] at h₁
  have h₂ := finite_main_tail_error ℓ hX
  calc
    _ ≤ |partialC ℓ X - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, mainCoefficient ℓ X n| +
        |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, mainCoefficient ℓ X n) -
          (R ℓ * Real.log X + constantTerm ℓ)| := abs_sub_le _ _ _
    _ ≤ (2 * ∑' a : ℕ, |h ℓ a| * (a : ℝ) ^ (3 / 8 : ℝ)) * X ^ (-3 / 8 : ℝ) +
        ((8 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * coefficientMoment ℓ *
          X ^ (-3 / 8 : ℝ) := add_le_add h₁ h₂
    _ = _ := by
      unfold coefficientMoment
      ring

/-- Equation (123), with an explicit finite constant depending only on ℓ. -/
theorem summatory_asymptotic (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |partialC ℓ X - (R ℓ * Real.log X + constantTerm ℓ)| ≤
      ((14 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * coefficientMoment ℓ *
        X ^ (-1 / 4 : ℝ) := by
  apply (summatory_asymptotic_strong ℓ hX).trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (-3 / 8 : ℝ) ≤ -1 / 4))
  unfold coefficientMoment
  positivity

end DepthAspect.ArithmeticWeights
