import DepthAspect.BoundedPrimitiveWeight
import DepthAspect.SmallMurmurationWeight

/-!
# The actual integral extension in (113)

The substitution u=Nv retains the exact Jacobian. The upper tail vanishes
by the support of the actual test, and the missing interval [0,2/N] is
bounded by the proved square-root estimate for the actual density M.
-/
namespace DepthAspect.MurmurationPrimeIntegral
open MeasureTheory Set MurmurationArithmetic MurmurationPrimitive BoundedPrimitiveWeight
open BesselFirstKind
open scoped SchwartzMap

noncomputable def weightedIntegrand (a ℓ : ℕ) (N L : ℝ) (h : ℝ → ℂ) (v : ℝ) : ℂ :=
  (M a ℓ v / v) • h (Real.log (N * v) / L)

/-- The exact substitution used between the prime-variable integral and
the density-variable integral. It also handles the zero value of the
integrand by the ordinary field division convention. -/
theorem change_variable (a ℓ : ℕ) {N : ℝ} (hN : 0 < N)
    (L A B : ℝ) (h : ℝ → ℂ) :
    (∫ u in A..B, (M a ℓ (u / N) / u) • h (Real.log u / L)) =
      ∫ v in (A / N)..(B / N), weightedIntegrand a ℓ N L h v := by
  calc
    _ = N⁻¹ • ∫ u in A..B, weightedIntegrand a ℓ N L h (u / N) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro u hu
      have harg : N * (u / N) = u := by field_simp [hN.ne']
      simp only [weightedIntegrand, harg, smul_smul]
      congr 1
      by_cases hu0 : u = 0
      · simp [hu0]
      · field_simp [hN.ne', hu0]
    _ = _ := intervalIntegral.inv_smul_integral_comp_div _ N

/-- The literal upper support cutoff kills the entire positive tail. -/
theorem weightedIntegrand_zero_above (a ℓ : ℕ) {N L s : ℝ}
    (hN : 0 < N) (hL : 0 < L) (h : ℝ → ℂ)
    (hsupp : Function.support h ⊆ Icc (-s) s) {v : ℝ}
    (hv : Real.exp (s * L) / N < v) : weightedIntegrand a ℓ N L h v = 0 := by
  have hNv : Real.exp (s * L) < N * v := by
    have := (div_lt_iff₀ hN).mp hv
    nlinarith
  have hlog := Real.log_lt_log (Real.exp_pos (s * L)) hNv
  rw [Real.log_exp] at hlog
  have hq : s < Real.log (N * v) / L := (lt_div_iff₀ hL).mpr hlog
  have hz : h (Real.log (N * v) / L) = 0 := by
    by_contra hh
    exact (not_lt.mpr (hsupp hh).2) hq
  simp [weightedIntegrand, hz]

/-- Actual absolute integrability on the positive half-line follows from
the actual local density estimate and compact logarithmic support. -/
theorem weightedIntegrand_integrable (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {N L s : ℝ} (hN : 0 < N) (hL : 0 < L)
    (h : 𝓢(ℝ, ℂ)) (hsupp : Function.support h ⊆ Icc (-s) s) :
    IntegrableOn (weightedIntegrand a ℓ N L h) (Ioi 0) := by
  have hi := logTest_weight_integrable N hL h.continuous hsupp
    (fun B hB => M_log_intervalIntegrable hDLMF a hℓ hB)
  apply hi.congr_fun _ measurableSet_Ioi
  intro v hv
  simp only [weightedIntegrand, logTest, Real.log_mul hN.ne' (ne_of_gt hv)]

/-- Truncating at the actual support endpoint is exact. -/
theorem positive_integral_eq_truncation (a ℓ : ℕ) {N L s : ℝ}
    (hN : 0 < N) (hL : 0 < L) (h : ℝ → ℂ)
    (hsupp : Function.support h ⊆ Icc (-s) s) :
    (∫ v in Ioi 0, weightedIntegrand a ℓ N L h v) =
      ∫ v in (0 : ℝ)..(Real.exp (s * L) / N), weightedIntegrand a ℓ N L h v := by
  have hU : 0 < Real.exp (s * L) / N := by positivity
  rw [intervalIntegral.integral_of_le hU.le]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun v hv => hv.1)
  intro v hv
  have hUv : Real.exp (s * L) / N < v := by
    by_contra hbad
    exact hv.2 ⟨hv.1, le_of_not_gt hbad⟩
  exact weightedIntegrand_zero_above a ℓ hN hL h hsupp hUv

/-- The exact decomposition of the prime-range main integral. Its omitted
lower piece is the only difference from the full positive integral. -/
theorem prime_range_integral_identity (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) {N L s : ℝ} (hN : 0 < N) (hL : 0 < L)
    (hX : 2 ≤ Real.exp (s * L)) (h : 𝓢(ℝ, ℂ))
    (hsupp : Function.support h ⊆ Icc (-s) s) :
    (∫ u in (2 : ℝ)..Real.exp (s * L),
      (M a ℓ (u / N) / u) • h (Real.log u / L)) -
        (∫ v in Ioi 0, weightedIntegrand a ℓ N L h v) =
      -(∫ v in (0 : ℝ)..(2 / N), weightedIntegrand a ℓ N L h v) := by
  have h0 : 0 ≤ 2 / N := by positivity
  have hU : 0 < Real.exp (s * L) / N := by positivity
  have hsub : 2 / N ≤ Real.exp (s * L) / N := div_le_div_of_nonneg_right hX hN.le
  have hi := weightedIntegrand_integrable hDLMF a hℓ hN hL h hsupp
  have hiU : IntervalIntegrable (weightedIntegrand a ℓ N L h) volume
      0 (Real.exp (s * L) / N) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hU.le).mpr
      (hi.mono_set (fun v hv => hv.1))
  have hi₁ : IntervalIntegrable (weightedIntegrand a ℓ N L h) volume 0 (2 / N) :=
    hiU.mono_set (by
      rw [uIcc_of_le h0, uIcc_of_le hU.le]
      exact Icc_subset_Icc le_rfl hsub)
  have hi₂ : IntervalIntegrable (weightedIntegrand a ℓ N L h) volume
      (2 / N) (Real.exp (s * L) / N) := hiU.mono_set (by
    rw [uIcc_of_le hsub, uIcc_of_le hU.le]
    exact Icc_subset_Icc h0 le_rfl)
  rw [change_variable a ℓ hN, positive_integral_eq_truncation a ℓ hN hL h hsupp,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  abel

/-- The lower extension in (113), with a constant independent of every
spectral family and all depths. -/
theorem prime_range_integral_error (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ N L s : ℝ, 2 ≤ N → 0 < L → 2 ≤ Real.exp (s * L) →
      ∀ h : 𝓢(ℝ, ℂ), Function.support h ⊆ Icc (-s) s →
      ‖(∫ u in (2 : ℝ)..Real.exp (s * L),
          (M a ℓ (u / N) / u) • h (Real.log u / L)) -
        (∫ v in Ioi 0, weightedIntegrand a ℓ N L h v)‖ ≤
        C * ‖h.toBoundedContinuousFunction‖ * N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := SmallMurmurationWeight.schwartz_small_weighted_integral a hℓ
  refine ⟨C * Real.sqrt 2, by positivity, ?_⟩
  intro N L s hN hL hX h hsupp
  have hN0 : 0 < N := by linarith
  rw [prime_range_integral_identity hDLMF a hℓ hN0 hL hX h hsupp, norm_neg]
  have ht := hb (2 / N) N L (by positivity) ((div_le_one hN0).mpr hN) h
  apply ht.trans_eq
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow]
  ring

end DepthAspect.MurmurationPrimeIntegral
