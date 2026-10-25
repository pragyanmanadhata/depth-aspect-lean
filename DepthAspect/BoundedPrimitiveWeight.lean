import DepthAspect.MurmurationPrimitiveDerivative
import DepthAspect.MertensWeights
import DepthAspect.FourierDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The actual compact logarithmic test against the bounded primitive in
(115). A split at the step discontinuity keeps all endpoint regularity
explicit; no differentiability of the primitive at one is assumed. -/
open MeasureTheory Set
open scoped Interval
namespace DepthAspect.BoundedPrimitiveWeight

/-- Integration by parts across one exceptional derivative point. -/
theorem split_integration_by_parts {A c B : ℝ} (hAc : A ≤ c) (hcB : c ≤ B)
    {P q : ℝ → ℝ} {w w' : ℝ → ℂ}
    (hP : ContinuousOn P (Icc A B)) (hw : ContinuousOn w (Icc A B))
    (hdP : ∀ x ∈ Ioo A B, x ≠ c → HasDerivAt P (q x) x)
    (hdw : ∀ x ∈ Ioo A B, HasDerivAt w (w' x) x)
    (hiq : IntervalIntegrable q volume A B)
    (hiw : IntervalIntegrable w' volume A B) :
    (∫ x in A..B, q x • w x) =
      P B • w B - P A • w A - ∫ x in A..B, P x • w' x := by
  have hab := hAc.trans hcB
  have hleft : uIcc A c ⊆ Icc A B := by
    rw [uIcc_of_le hAc]
    exact Icc_subset_Icc le_rfl hcB
  have hright : uIcc c B ⊆ Icc A B := by
    rw [uIcc_of_le hcB]
    exact Icc_subset_Icc hAc le_rfl
  have hfull : uIcc A B = Icc A B := uIcc_of_le hab
  have hL := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (hP.mono hleft) (hw.mono hleft)
    (fun x hx => hdP x (by
      simp only [min_eq_left hAc, max_eq_right hAc, mem_Ioo] at hx
      exact ⟨hx.1, hx.2.trans_le hcB⟩) (by
      simp only [min_eq_left hAc, max_eq_right hAc, mem_Ioo] at hx
      exact ne_of_lt hx.2))
    (fun x hx => hdw x (by
      simp only [min_eq_left hAc, max_eq_right hAc, mem_Ioo] at hx
      exact ⟨hx.1, hx.2.trans_le hcB⟩))
    (hiq.mono_set (by simpa only [hfull] using hleft)) (hiw.mono_set (by simpa only [hfull] using hleft))
  have hR := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (hP.mono hright) (hw.mono hright)
    (fun x hx => hdP x (by
      simp only [min_eq_left hcB, max_eq_right hcB, mem_Ioo] at hx
      exact ⟨hAc.trans_lt hx.1, hx.2⟩) (by
      simp only [min_eq_left hcB, max_eq_right hcB, mem_Ioo] at hx
      exact ne_of_gt hx.1))
    (fun x hx => hdw x (by
      simp only [min_eq_left hcB, max_eq_right hcB, mem_Ioo] at hx
      exact ⟨hAc.trans_lt hx.1, hx.2⟩))
    (hiq.mono_set (by simpa only [hfull] using hright)) (hiw.mono_set (by simpa only [hfull] using hright))
  have hiqw := hiq.smul_continuousOn (by simpa only [hfull] using hw)
  have hiPw := hiw.continuousOn_smul (by simpa only [hfull] using hP)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hiqw.mono_set (by simpa only [hfull] using hleft)) (hiqw.mono_set (by simpa only [hfull] using hright)),
    ← intervalIntegral.integral_add_adjacent_intervals
    (hiPw.mono_set (by simpa only [hfull] using hleft)) (hiPw.mono_set (by simpa only [hfull] using hright))]
  linear_combination hL + hR

/-- Vanishing endpoint tests leave only the variation integral. -/
theorem compact_test_bound {A c B C : ℝ} (hAc : A ≤ c) (hcB : c ≤ B)
    (hC : 0 ≤ C) {P q : ℝ → ℝ} {w w' : ℝ → ℂ}
    (hP : ContinuousOn P (Icc A B)) (hw : ContinuousOn w (Icc A B))
    (hdP : ∀ x ∈ Ioo A B, x ≠ c → HasDerivAt P (q x) x)
    (hdw : ∀ x ∈ Ioo A B, HasDerivAt w (w' x) x)
    (hiq : IntervalIntegrable q volume A B)
    (hiw : IntervalIntegrable w' volume A B)
    (hb : ∀ x ∈ Icc A B, |P x| ≤ C) (hA : w A = 0) (hB : w B = 0) :
    ‖∫ x in A..B, q x • w x‖ ≤ C * ∫ x in A..B, ‖w' x‖ := by
  rw [split_integration_by_parts hAc hcB hP hw hdP hdw hiq hiw,
    hA, hB, smul_zero, smul_zero, sub_self, zero_sub, norm_neg,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (hAc.trans hcB) _ (hiw.norm.const_mul C)
  apply Filter.Eventually.of_forall
  intro x hx
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb x ⟨hx.1.le, hx.2⟩) (norm_nonneg _)

noncomputable def logTest (N L : ℝ) (h : ℝ → ℂ) (v : ℝ) : ℂ :=
  h ((Real.log N + Real.log v) / L)

/-- The Jacobian in (115), including the factor 1/L. -/
theorem logTest_hasDerivAt (N L : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h)
    {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt (logTest N L h)
      ((v⁻¹ / L) • deriv h ((Real.log N + Real.log v) / L)) v := by
  exact (hh.differentiable_one _).hasDerivAt.scomp v
    (((Real.hasDerivAt_log hv).const_add (Real.log N)).div_const L)

/-- Actual logarithmic substitution, without an assumed variation bound. -/
theorem logTest_variation {A B L : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hL : 0 < L)
    (N : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) :
    (∫ v in A..B, ‖deriv (logTest N L h) v‖) =
      ∫ u in (Real.log N + Real.log A) / L..
        (Real.log N + Real.log B) / L, ‖deriv h u‖ := by
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := A) (b := B) (f := fun v : ℝ => (Real.log N + Real.log v) / L)
    (f' := fun v : ℝ => v⁻¹ / L)
    (fun v hv => ((Real.hasDerivAt_log (by
      rw [uIcc_of_le hAB] at hv; exact ne_of_gt (hA.trans_le hv.1))).const_add
      (Real.log N)).div_const L)
    (by
      rw [uIcc_of_le hAB]
      exact (continuousOn_id.inv₀ (fun v hv => ne_of_gt (hA.trans_le hv.1))).div_const L)
    hh.continuous_deriv_one.norm
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hAB] at hv
  have hv0 := hA.trans_le hv.1
  change ‖deriv (logTest N L h) v‖ =
    (v⁻¹ / L) • ‖deriv h ((Real.log N + Real.log v) / L)‖
  rw [(logTest_hasDerivAt N L hh hv0.ne').deriv, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos (inv_pos.mpr hv0) hL)]
  rfl

/-- The derivative integral is at most the full Schwartz derivative L¹ norm. -/
theorem logTest_variation_le {A B L : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hL : 0 < L)
    (N : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hd : Integrable (deriv h)) :
    (∫ v in A..B, ‖deriv (logTest N L h) v‖) ≤ ∫ u : ℝ, ‖deriv h u‖ := by
  rw [logTest_variation hA hAB hL N hh]
  have hlog : (Real.log N + Real.log A) / L ≤ (Real.log N + Real.log B) / L := by
    exact div_le_div_of_nonneg_right (add_le_add le_rfl (Real.log_le_log hA hAB)) hL.le
  rw [intervalIntegral.integral_of_le hlog]
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun u => norm_nonneg (deriv h u))) hd.norm

/-- Half-line integrals with a genuine compact positive support can be
replaced by the literal finite interval, including zero endpoint tests. -/
theorem positive_integral_truncate {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    {f : ℝ → ℂ} (hz : ∀ v : ℝ, 0 < v → v ≤ A ∨ B < v → f v = 0) :
    (∫ v in Ioi 0, f v) = ∫ v in A..B, f v := by
  rw [intervalIntegral.integral_of_le hAB]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun v hv => hA.trans hv.1)
  intro v hv
  apply hz v hv.1
  by_cases h : v ≤ A
  · exact Or.inl h
  · exact Or.inr (lt_of_not_ge (fun hb => hv.2 ⟨lt_of_not_ge h, hb⟩))

open MurmurationKernel MurmurationArithmetic MurmurationPrimitive
open MurmurationStepPrimitive MurmurationPrimitiveDerivative BesselFirstKind

/-- Continuity is obtained from the actual integral defining the primitive,
including at the step point. -/
theorem P_continuousOn (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    ContinuousOn (P a ℓ) (Icc A B) := by
  have hB := hA.trans hAB
  have hi := M_log_intervalIntegrable hDLMF a hℓ hB
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 B)
  have hlog : Continuous (fun v : ℝ => Real.log (max 1 v)) :=
    (continuous_const.max continuous_id).log (fun v =>
      ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 v)))
  exact (hc.sub (continuousOn_const.mul hlog.continuousOn)).mono (by
    rw [uIcc_of_le hB]
    exact Icc_subset_Icc hA le_rfl)

theorem logTest_continuousOn {A B : ℝ} (hA : 0 < A) (N L : ℝ)
    {h : ℝ → ℂ} (hh : Continuous h) : ContinuousOn (logTest N L h) (Icc A B) := by
  apply hh.comp_continuousOn
  exact (continuousOn_const.add (continuousOn_id.log (fun v hv =>
    ne_of_gt (hA.trans_le hv.1)))).div_const L

theorem logTest_deriv_continuousOn {A B : ℝ} (hA : 0 < A) (N L : ℝ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) :
    ContinuousOn (deriv (logTest N L h)) (Icc A B) := by
  have hc : ContinuousOn (fun v : ℝ =>
      (v⁻¹ / L) • deriv h ((Real.log N + Real.log v) / L)) (Icc A B) :=
    ((continuousOn_id.inv₀ (fun v hv => ne_of_gt (hA.trans_le hv.1))).div_const L).smul
      (logTest_continuousOn hA N L hh.continuous_deriv_one)
  apply hc.congr
  intro v hv
  exact (logTest_hasDerivAt N L hh (ne_of_gt (hA.trans_le hv.1))).deriv

/-- The actual density error, tested on any compact positive interval
containing the step point, is bounded by the full derivative L¹ norm. -/
theorem finite_weighted_error (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {A B N L C : ℝ}
    (hA : 0 < A) (hA1 : A ≤ 1) (h1B : 1 ≤ B) (hL : 0 < L) (hC : 0 ≤ C)
    {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hd : Integrable (deriv h))
    (hPbound : ∀ v : ℝ, 0 < v → |P a ℓ v| ≤ C)
    (hwA : logTest N L h A = 0) (hwB : logTest N L h B = 0) :
    ‖∫ v in A..B, ((M a ℓ v - step v) / v) • logTest N L h v‖ ≤
      C * ∫ u : ℝ, ‖deriv h u‖ := by
  have hAB := hA1.trans h1B
  have hB : 0 ≤ B := (zero_lt_one.trans_le h1B).le
  have hq : IntervalIntegrable (fun v => (M a ℓ v - step v) / v) volume A B := by
    simp_rw [sub_div]
    exact ((M_log_intervalIntegrable hDLMF a hℓ hB).sub (step_log_intervalIntegrable hB)).mono_set
      (by rw [uIcc_of_le hAB, uIcc_of_le hB]; exact Icc_subset_Icc hA.le le_rfl)
  have hw := logTest_continuousOn (B := B) hA N L hh.continuous
  have hiw : IntervalIntegrable (deriv (logTest N L h)) volume A B :=
    (logTest_deriv_continuousOn hA N L hh).intervalIntegrable_of_Icc hAB
  have hb := compact_test_bound hA1 h1B hC (P_continuousOn hDLMF a hℓ hA.le hAB) hw
    (fun v hv hv1 => P_hasDerivAt hDLMF a hℓ (hA.trans hv.1) hv1)
    (fun v hv => (logTest_hasDerivAt N L hh (ne_of_gt (hA.trans hv.1))).differentiableAt.hasDerivAt)
    hq hiw (fun v hv => hPbound v (hA.trans_le hv.1)) hwA hwB
  exact hb.trans (mul_le_mul_of_nonneg_left (logTest_variation_le hA hAB hL N hh hd) hC)

/-- Compact support in logarithmic coordinates gives positive cutoffs on
both sides; they can always be chosen to straddle the step point. -/
theorem exists_log_cutoffs (N : ℝ) {L s : ℝ} (hL : 0 < L) :
    ∃ A B : ℝ, 0 < A ∧ A ≤ 1 ∧ 1 ≤ B ∧
      (Real.log N + Real.log A) / L < -s ∧
      s < (Real.log N + Real.log B) / L := by
  let A := Real.exp (min 0 (-s * L - Real.log N) - 1)
  let B := Real.exp (max 0 (s * L - Real.log N) + 1)
  refine ⟨A, B, Real.exp_pos _, ?_, ?_, ?_, ?_⟩
  · dsimp [A]
    rw [Real.exp_le_one_iff]
    linarith [min_le_left (0 : ℝ) (-s * L - Real.log N)]
  · dsimp [B]
    rw [Real.one_le_exp_iff]
    linarith [le_max_left (0 : ℝ) (s * L - Real.log N)]
  · dsimp [A]
    rw [Real.log_exp, div_lt_iff₀ hL]
    linarith [min_le_right (0 : ℝ) (-s * L - Real.log N)]
  · dsimp [B]
    rw [Real.log_exp, lt_div_iff₀ hL]
    linarith [le_max_right (0 : ℝ) (s * L - Real.log N)]

theorem logTest_zero_left {A N L s : ℝ} (hL : 0 < L)
    (hcut : (Real.log N + Real.log A) / L < -s)
    {h : ℝ → ℂ} (hsupp : Function.support h ⊆ Icc (-s) s)
    {v : ℝ} (hv : 0 < v) (hvA : v ≤ A) : logTest N L h v = 0 := by
  by_contra hn
  have hm := (hsupp hn).1
  have he : (Real.log N + Real.log v) / L ≤ (Real.log N + Real.log A) / L :=
    div_le_div_of_nonneg_right
      (add_le_add (le_refl (Real.log N)) (Real.log_le_log hv hvA)) hL.le
  exact (not_lt_of_ge hm) (he.trans_lt hcut)

theorem logTest_zero_right {B N L s : ℝ} (hB : 0 < B) (hL : 0 < L)
    (hcut : s < (Real.log N + Real.log B) / L)
    {h : ℝ → ℂ} (hsupp : Function.support h ⊆ Icc (-s) s)
    {v : ℝ} (hBv : B ≤ v) : logTest N L h v = 0 := by
  by_contra hn
  have hm := (hsupp hn).2
  have he : (Real.log N + Real.log B) / L ≤ (Real.log N + Real.log v) / L :=
    div_le_div_of_nonneg_right
      (add_le_add (le_refl (Real.log N)) (Real.log_le_log hB hBv)) hL.le
  exact (not_lt_of_ge hm) (hcut.trans_le he)

/-- First line of (115) for the literal M and the literal step. Its constant
comes from the internally proved primitive bound, and its derivative term
is the actual test-function L¹ integral. -/
theorem weighted_error (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ (N L s : ℝ), 0 < N → 0 < L →
      ∀ h : ℝ → ℂ, ContDiff ℝ 1 h → Integrable (deriv h) →
      Function.support h ⊆ Icc (-s) s →
      ‖∫ v in Ioi 0, ((M a ℓ v - step v) / v) • h (Real.log (N * v) / L)‖ ≤
        C * ∫ u : ℝ, ‖deriv h u‖ := by
  obtain ⟨C, hC, hb⟩ := P_bounded hDLMF a hℓ
  refine ⟨C, hC, ?_⟩
  intro N L s hN hL h hh hd hsupp
  obtain ⟨A, B, hA, hA1, h1B, hcutA, hcutB⟩ := exists_log_cutoffs N (s := s) hL
  have hAB := hA1.trans h1B
  have hB := zero_lt_one.trans_le h1B
  have hzeroA := logTest_zero_left hL hcutA hsupp hA le_rfl
  have hzeroB := logTest_zero_right hB hL hcutB hsupp le_rfl
  have he : (∫ v in Ioi 0, ((M a ℓ v - step v) / v) • h (Real.log (N * v) / L)) =
      ∫ v in A..B, ((M a ℓ v - step v) / v) • logTest N L h v := by
    calc
      _ = ∫ v in Ioi 0, ((M a ℓ v - step v) / v) • logTest N L h v := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v hv
        simp only [logTest, Real.log_mul hN.ne' (ne_of_gt hv)]
      _ = _ := positive_integral_truncate hA hAB (by
        intro v hv hvoutside
        rcases hvoutside with hvA | hBv
        · rw [logTest_zero_left hL hcutA hsupp hv hvA, smul_zero]
        · rw [logTest_zero_right hB hL hcutB hsupp hBv.le, smul_zero])
  rw [he]
  exact finite_weighted_error hDLMF a hℓ hA hA1 h1B hL hC.le hh hd hb hzeroA hzeroB

open scoped SchwartzMap FourierTransform

/-- The paper's h is the actual Fourier transform of its Schwartz test;
its derivative integrability is proved by the Schwartz-space structure. -/
theorem fourier_weighted_error (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ (N L s : ℝ), 0 < N → 0 < L →
      ∀ φ : 𝓢(ℝ, ℂ),
      Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s →
      ‖∫ v in Ioi 0, ((M a ℓ v - step v) / v) •
        (𝓕 φ : 𝓢(ℝ, ℂ)) (Real.log (N * v) / L)‖ ≤
        C * ∫ u : ℝ, ‖deriv (𝓕 φ : 𝓢(ℝ, ℂ)) u‖ := by
  obtain ⟨C, hC, hb⟩ := weighted_error hDLMF a hℓ
  refine ⟨C, hC, ?_⟩
  intro N L s hN hL φ hsupp
  apply hb N L s hN hL (𝓕 φ : 𝓢(ℝ, ℂ)) ((𝓕 φ : 𝓢(ℝ, ℂ)).smooth 1) _ hsupp
  exact (SchwartzMap.derivCLM ℝ ℂ (𝓕 φ : 𝓢(ℝ, ℂ))).integrable

/-- Compact positive support upgrades local integrability to the actual
half-line Bochner integrability used when splitting the two main terms. -/
theorem positive_integrable_of_compact {A B : ℝ} {f : ℝ → ℂ}
    (hi : IntegrableOn f (Icc A B))
    (hz : ∀ v : ℝ, 0 < v → v < A ∨ B < v → f v = 0) :
    IntegrableOn f (Ioi 0) := by
  apply IntegrableOn.of_inter_support measurableSet_Ioi
  apply hi.mono_set
  intro v hv
  constructor
  · by_contra hn
    exact hv.2 (hz v hv.1 (Or.inl (lt_of_not_ge hn)))
  · by_contra hn
    exact hv.2 (hz v hv.1 (Or.inr (lt_of_not_ge hn)))

theorem upper_integral_truncate {a B : ℝ} (haB : a ≤ B) {f : ℝ → ℂ}
    (htail : ∀ u : ℝ, B ≤ u → f u = 0) :
    (∫ u in Ioi a, f u) = ∫ u in a..B, f u := by
  rw [intervalIntegral.integral_of_le haB]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ hu => hu.1)
  intro u hu
  exact htail u (le_of_lt (lt_of_not_ge (fun h => hu.2 ⟨hu.1, h⟩)))

/-- The literal lower endpoint of the step main term is log N/L. -/
theorem step_log_main_term {N L s : ℝ} (hL : 0 < L)
    {h : ℝ → ℂ} (hh : Continuous h) (hsupp : Function.support h ⊆ Icc (-s) s) :
    (∫ v in Ioi 0, (step v / v) • logTest N L h v) =
      (L / 2 : ℝ) • ∫ u in Ioi (Real.log N / L), h u := by
  obtain ⟨A, B, hA, hA1, h1B, hcutA, hcutB⟩ := exists_log_cutoffs N (s := s) hL
  have hB := zero_lt_one.trans_le h1B
  have hz : ∀ u : ℝ, (Real.log N + Real.log B) / L ≤ u → h u = 0 := by
    intro u hu
    by_contra hn
    exact (not_lt_of_ge (hsupp hn).2) (hcutB.trans_le hu)
  have hlog : Real.log N / L ≤ (Real.log N + Real.log B) / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    linarith [Real.log_nonneg h1B]
  have he : (∫ v in Ioi 0, (step v / v) • logTest N L h v) =
      (1 / 2 : ℝ) • ∫ v in Ioi 1, v⁻¹ • logTest N L h v := by
    have hi : (∫ v in Ioi 0, (step v / v) • logTest N L h v) =
        ∫ v in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun v => (1 / 2 : ℝ) • (v⁻¹ • logTest N L h v)) v := by
      apply setIntegral_congr_ae measurableSet_Ioi
      filter_upwards [volume.ae_ne (1 : ℝ)] with v hv _
      have hiff : 1 ≤ v ↔ 1 < v := ⟨fun h => lt_of_le_of_ne h (Ne.symm hv), le_of_lt⟩
      simp only [step, hiff, Set.indicator, Set.mem_Ioi]
      split_ifs <;> simp [div_eq_mul_inv, smul_smul, mul_assoc]
    rw [hi, setIntegral_indicator measurableSet_Ioi]
    have hint : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 :=
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    rw [hint, integral_smul]
  rw [he, upper_integral_truncate h1B (by
    intro v hv
    rw [logTest_zero_right hB hL hcutB hsupp hv, smul_zero]),
    upper_integral_truncate hlog hz]
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := (1 : ℝ)) (b := B) (f := fun v : ℝ => (Real.log N + Real.log v) / L)
    (f' := fun v : ℝ => v⁻¹ / L)
    (fun v hv => ((Real.hasDerivAt_log (by
      rw [uIcc_of_le h1B] at hv; exact ne_of_gt (zero_lt_one.trans_le hv.1))).const_add
      (Real.log N)).div_const L)
    (by
      rw [uIcc_of_le h1B]
      exact (continuousOn_id.inv₀ (fun v hv => ne_of_gt (zero_lt_one.trans_le hv.1))).div_const L)
    hh
  simp only [Real.log_one, add_zero] at hsub
  rw [← hsub, ← intervalIntegral.integral_smul, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro v _
  simp only [logTest, smul_smul]
  congr 1
  field_simp [hL.ne']

/-- The compact logarithmic test makes every locally integrable density
an integrable function on the whole positive half-line. -/
theorem logTest_weight_integrable (N : ℝ) {L s : ℝ} (hL : 0 < L)
    {h : ℝ → ℂ} (hh : Continuous h) (hsupp : Function.support h ⊆ Icc (-s) s)
    {q : ℝ → ℝ} (hq : ∀ B : ℝ, 0 ≤ B → IntervalIntegrable q volume 0 B) :
    IntegrableOn (fun v => q v • logTest N L h v) (Ioi 0) := by
  obtain ⟨A, B, hA, hA1, h1B, hcutA, hcutB⟩ := exists_log_cutoffs N (s := s) hL
  have hAB := hA1.trans h1B
  have hB := zero_lt_one.trans_le h1B
  have hiq : IntervalIntegrable q volume A B := (hq B hB.le).mono_set (by
    rw [uIcc_of_le hAB, uIcc_of_le hB.le]
    exact Icc_subset_Icc hA.le le_rfl)
  have hfin := hiq.smul_continuousOn (by
    rw [uIcc_of_le hAB]
    exact logTest_continuousOn hA N L hh)
  apply positive_integrable_of_compact
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mp hfin)
  intro v hv hout
  rcases hout with hleft | hright
  · rw [logTest_zero_left hL hcutA hsupp hv hleft.le, smul_zero]
  · rw [logTest_zero_right hB hL hcutB hsupp hright.le, smul_zero]

/-- Exact conductor shift in the step term. -/
theorem conductor_shift {k N : ℝ} (hk : 1 ≤ k) (hN : 0 < N)
    (hL : 0 < Real.log (k ^ 2 * N)) :
    Real.log N / Real.log (k ^ 2 * N) ≤ 1 ∧
      1 - Real.log N / Real.log (k ^ 2 * N) =
        2 * Real.log k / Real.log (k ^ 2 * N) := by
  have hk0 := zero_lt_one.trans_le hk
  have he : Real.log (k ^ 2 * N) = 2 * Real.log k + Real.log N := by
    rw [Real.log_mul (pow_ne_zero _ hk0.ne') hN.ne', Real.log_pow]
    norm_num
  constructor
  · apply (div_le_iff₀ hL).mpr
    rw [one_mul, he]
    linarith [Real.log_nonneg hk]
  · apply (eq_div_iff hL.ne').mpr
    field_simp [hL.ne']
    linarith

/-- Moving the step endpoint from log N/L to one costs its exact interval
length, with the actual supremum norm of the Schwartz test. -/
theorem step_endpoint_error {k N : ℝ} (hk : 1 ≤ k) (hN : 0 < N)
    (hL : 0 < Real.log (k ^ 2 * N)) (h : 𝓢(ℝ, ℂ)) :
    ‖(∫ u in Ioi (Real.log N / Real.log (k ^ 2 * N)), h u) -
        ∫ u in Ioi (1 : ℝ), h u‖ ≤
      2 * Real.log k * ‖h.toBoundedContinuousFunction‖ / Real.log (k ^ 2 * N) := by
  obtain ⟨hle, heq⟩ := conductor_shift hk hN hL
  rw [intervalIntegral.integral_Ioi_sub_Ioi h.integrable.integrableOn hle]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun u _ => h.toBoundedContinuousFunction.norm_coe_le_norm u)
    (a := Real.log N / Real.log (k ^ 2 * N)) (b := (1 : ℝ))
  rw [abs_of_nonneg (sub_nonneg.mpr hle), heq] at hb
  simp only [SchwartzMap.toBoundedContinuousFunction_apply] at hb
  convert hb using 1 <;> ring

/-- Second line of (115), with every scaling and step-endpoint error
explicit. The constant is independent of the level N. -/
theorem scaled_main_term (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ (k N s : ℝ), 1 ≤ k → 0 < N →
      0 < Real.log (k ^ 2 * N) → ∀ h : 𝓢(ℝ, ℂ),
      Function.support h ⊆ Icc (-s) s →
      ‖(2 / Real.log (k ^ 2 * N) : ℝ) •
        (∫ v in Ioi 0, (M a ℓ v / v) • h (Real.log (N * v) / Real.log (k ^ 2 * N))) -
          ∫ u in Ioi (1 : ℝ), h u‖ ≤
        (2 * C * (∫ u : ℝ, ‖deriv h u‖) +
          2 * Real.log k * ‖h.toBoundedContinuousFunction‖) / Real.log (k ^ 2 * N) := by
  obtain ⟨C, hC, hb⟩ := weighted_error hDLMF a hℓ
  refine ⟨C, hC, ?_⟩
  intro k N s hk hN hL h hsupp
  let L := Real.log (k ^ 2 * N)
  let IM := ∫ v in Ioi 0, (M a ℓ v / v) • logTest N L h v
  let IS := ∫ v in Ioi 0, (step v / v) • logTest N L h v
  let J0 := ∫ u in Ioi (Real.log N / L), h u
  let J1 := ∫ u in Ioi (1 : ℝ), h u
  have hiM := logTest_weight_integrable N hL h.continuous hsupp
    (fun B hB => M_log_intervalIntegrable hDLMF a hℓ (V := B) hB)
  have hiS := logTest_weight_integrable N hL h.continuous hsupp
    (fun B hB => step_log_intervalIntegrable hB)
  have hsub : IM - IS =
      ∫ v in Ioi 0, ((M a ℓ v - step v) / v) • h (Real.log (N * v) / L) := by
    change (∫ v in Ioi 0, (M a ℓ v / v) • logTest N L h v) -
      (∫ v in Ioi 0, (step v / v) • logTest N L h v) = _
    rw [← integral_sub hiM hiS]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp [L, logTest, Real.log_mul hN.ne' (ne_of_gt hv), sub_div, sub_smul]
  have herror : ‖IM - IS‖ ≤ C * ∫ u : ℝ, ‖deriv h u‖ := by
    rw [hsub]
    exact hb N L s hN hL h (h.smooth 1) (SchwartzMap.derivCLM ℝ ℂ h).integrable hsupp
  have hmain : (2 / L : ℝ) • IS = J0 := by
    change (2 / L : ℝ) • (∫ v in Ioi 0, (step v / v) • logTest N L h v) =
      ∫ u in Ioi (Real.log N / L), h u
    rw [step_log_main_term (N := N) (L := L) hL h.continuous hsupp, smul_smul]
    have he : (2 / L : ℝ) * (L / 2) = 1 := by
      have hL0 : L ≠ 0 := hL.ne'
      field_simp [hL0]
    rw [he, one_smul]
  have hraw : (∫ v in Ioi 0, (M a ℓ v / v) •
      h (Real.log (N * v) / L)) = IM := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp only [logTest, Real.log_mul hN.ne' (ne_of_gt hv)]
  change ‖(2 / L : ℝ) • (∫ v in Ioi 0, (M a ℓ v / v) •
    h (Real.log (N * v) / L)) - J1‖ ≤ _
  rw [hraw]
  have he : (2 / L : ℝ) • IM - J1 =
      (2 / L : ℝ) • (IM - IS) + (J0 - J1) := by rw [smul_sub, hmain]; abel
  rw [he]
  calc
    _ ≤ ‖(2 / L : ℝ) • (IM - IS)‖ + ‖J0 - J1‖ := norm_add_le _ _
    _ ≤ (2 / L) * (C * ∫ u : ℝ, ‖deriv h u‖) +
        2 * Real.log k * ‖h.toBoundedContinuousFunction‖ / L := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hL)]
        exact mul_le_mul_of_nonneg_left herror (by positivity)
      · exact step_endpoint_error hk hN hL h
    _ = _ := by dsimp [L]; ring

end DepthAspect.BoundedPrimitiveWeight
