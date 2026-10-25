import DepthAspect.MurmurationExpansion
import DepthAspect.MurmurationSignedMeans

/-! The literal sequences (135), with the displayed constant q²/(4Q),
and both unboundedness and failure of pointwise convergence. -/
open Filter
open scoped Topology
namespace DepthAspect.MurmurationOscillation
open BesselFirstKind MurmurationArithmetic MurmurationOscillationSeries
  MurmurationRecurrence MurmurationSignedMeans MurmurationExpansion

noncomputable def oscillationConstant (ℓ : ℕ) : ℝ := (q ℓ) ^ 2 / (4 * Q ℓ)

theorem oscillationConstant_pos {ℓ : ℕ} (hℓ : ℓ.Prime) : 0 < oscillationConstant ℓ := by
  have hQ : 0 < Q ℓ := by linarith [q_pos hℓ, two_q_le_Q hℓ]
  exact div_pos (sq_pos_of_pos (q_pos hℓ)) (mul_pos (by norm_num) hQ)

/-- A value of either sign is moved beyond every prescribed bound, then
the proved bounded error is absorbed in the quarter-power main term. -/
theorem signed_large_value (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {σ x : ℝ} (hσ : |σ| = 1)
    (hvalue : 3 * oscillationConstant ℓ < σ * A a ℓ x) (R : ℝ) :
    ∃ y : ℝ, R < y ∧ 1 ≤ y ∧
      oscillationConstant ℓ * y ^ (1 / 4 : ℝ) ≤ σ * M a ℓ y := by
  obtain ⟨C, hC, hb⟩ := M_leading_error hDLMF a hℓ
  let c := oscillationConstant ℓ
  have hc : 0 < c := oscillationConstant_pos hℓ
  obtain ⟨u, hu, hnear⟩ := recurrent_values a hℓ x
    (max 1 (max R ((C / c) ^ 2))) hc
  have hu1 : 1 < u := lt_of_le_of_lt (le_max_left _ _) hu
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have huR : R < u := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hu
  have huC : (C / c) ^ 2 ≤ u :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hu.le)
  have hAu : 2 * c < σ * A a ℓ u := by
    have hdiff : |σ * A a ℓ u - σ * A a ℓ x| < c := by
      rw [← mul_sub, abs_mul, hσ, one_mul]
      exact hnear
    have hlow := (abs_lt.mp hdiff).1
    change 3 * c < σ * A a ℓ x at hvalue
    linarith
  have hy1 : 1 ≤ u ^ 2 := by nlinarith
  have hyR : R < u ^ 2 := by nlinarith
  have hpow : (u ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt u := by
    rw [← Real.rpow_natCast_mul hu0.le 2 (1 / 4 : ℝ)]
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]
    rw [← Real.sqrt_eq_rpow]
  have hcost : C ≤ c * (u ^ 2) ^ (1 / 4 : ℝ) := by
    have hs : C / c ≤ Real.sqrt u := Real.le_sqrt_of_sq_le huC
    have hm := (div_le_iff₀ hc).mp hs
    rw [hpow]
    nlinarith
  have he := hb (u ^ 2) hy1
  rw [Real.sqrt_sq hu0.le] at he
  have heσ : |σ * M a ℓ (u ^ 2) - (u ^ 2) ^ (1 / 4 : ℝ) * (σ * A a ℓ u)| ≤ C := by
    calc
      _ = |σ| * |M a ℓ (u ^ 2) - (u ^ 2) ^ (1 / 4 : ℝ) * A a ℓ u| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ C := by rw [hσ, one_mul]; exact he
  refine ⟨u ^ 2, hyR, hy1, ?_⟩
  have hlo := (abs_le.mp heσ).1
  have hp : 0 < (u ^ 2) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (sq_pos_of_pos hu0) _
  have hmain := mul_le_mul_of_nonneg_left hAu.le hp.le
  nlinarith

theorem both_signs_far_out (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (R : ℝ) :
    (∃ y : ℝ, R < y ∧ 1 ≤ y ∧ oscillationConstant ℓ * y ^ (1 / 4 : ℝ) ≤ M a ℓ y) ∧
      (∃ y : ℝ, R < y ∧ 1 ≤ y ∧ M a ℓ y ≤ -oscillationConstant ℓ * y ^ (1 / 4 : ℝ)) := by
  obtain ⟨⟨xPos, hxPos⟩, ⟨xNeg, hxNeg⟩⟩ := A_signed_values a hℓ
  have he : (3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ) = 3 * oscillationConstant ℓ := by
    unfold oscillationConstant
    ring
  rw [he] at hxPos
  have hxNeg' : 3 * oscillationConstant ℓ < (-1 : ℝ) * A a ℓ xNeg := by
    have he' : -(3 / 4 : ℝ) * ((q ℓ) ^ 2 / Q ℓ) = -3 * oscillationConstant ℓ := by
      unfold oscillationConstant
      ring
    rw [he'] at hxNeg
    linarith
  constructor
  · simpa only [one_mul] using signed_large_value hDLMF a hℓ
      (σ := 1) (x := xPos) (by norm_num) (by simpa using hxPos) R
  · obtain ⟨y, hyR, hy1, hy⟩ := signed_large_value hDLMF a hℓ
      (σ := -1) (x := xNeg) (by norm_num) hxNeg' R
    exact ⟨y, hyR, hy1, by linarith⟩

/-- The exact conclusion (135), with one constant for both sequences and
no extra assumption on pointwise signs or recurrence. -/
theorem oscillating_sequences (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ yPos yNeg : ℕ → ℝ,
      Tendsto yPos atTop atTop ∧ Tendsto yNeg atTop atTop ∧
      (∀ j, 1 ≤ yPos j ∧ oscillationConstant ℓ * (yPos j) ^ (1 / 4 : ℝ) ≤ M a ℓ (yPos j)) ∧
      (∀ j, 1 ≤ yNeg j ∧ M a ℓ (yNeg j) ≤ -oscillationConstant ℓ * (yNeg j) ^ (1 / 4 : ℝ)) := by
  classical
  choose yPos hp using fun j : ℕ => (both_signs_far_out hDLMF a hℓ (j : ℝ)).1
  choose yNeg hn using fun j : ℕ => (both_signs_far_out hDLMF a hℓ (j : ℝ)).2
  refine ⟨yPos, yNeg, ?_, ?_, fun j => (hp j).2, fun j => (hn j).2⟩
  · exact tendsto_atTop_mono (fun j => (hp j).1.le) tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono (fun j => (hn j).1.le) tendsto_natCast_atTop_atTop

/-- Along the two actual sequences the density tends to opposite infinities. -/
theorem unbounded_both_signs (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ yPos yNeg : ℕ → ℝ, Tendsto yPos atTop atTop ∧ Tendsto yNeg atTop atTop ∧
      Tendsto (fun j => M a ℓ (yPos j)) atTop atTop ∧
      Tendsto (fun j => M a ℓ (yNeg j)) atTop atBot := by
  obtain ⟨yPos, yNeg, hp, hn, hpb, hnb⟩ := oscillating_sequences hDLMF a hℓ
  have hc := oscillationConstant_pos hℓ
  have hpow := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hpl := (hpow.comp hp).const_mul_atTop hc
  have hnl := tendsto_neg_atTop_atBot.comp ((hpow.comp hn).const_mul_atTop hc)
  refine ⟨yPos, yNeg, hp, hn, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun j => (hpb j).2) hpl
  · apply tendsto_atBot_mono (fun j => ?_) hnl
    simpa only [Function.comp_apply, neg_mul] using (hnb j).2

theorem M_no_limit (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (L : ℝ) :
    ¬ Tendsto (M a ℓ) atTop (𝓝 L) := by
  obtain ⟨_, yNeg, _, hyNeg, _, hMNeg⟩ := unbounded_both_signs hDLMF a hℓ
  intro h
  exact not_tendsto_nhds_of_tendsto_atBot hMNeg L (h.comp hyNeg)

end DepthAspect.MurmurationOscillation
