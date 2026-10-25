import DepthAspect.BesselBounds

/-! The full two-regime bound and the leading Bessel remainder in (126),
with constants uniform down to t=1. -/
open Filter Set Asymptotics
namespace DepthAspect.BesselRemainder
open BesselFirstKind BesselBounds

/-- Compactness needs continuity only on the positive half-line where the
asymptotic expression is defined without a singular endpoint. -/
theorem bounded_Ici_of_eventually {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 1)) {C : ℝ} (hC : ∀ᶠ t in atTop, |f t| ≤ C) :
    ∃ K > 0, ∀ t : ℝ, 1 ≤ t → |f t| ≤ K := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC
  obtain ⟨x, hx, hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 : ℝ) (max 1 T)).Nonempty from ⟨1, le_rfl, le_max_left _ _⟩)
    (hf.abs.mono (fun _ h => h.1))
  refine ⟨max 1 (max C |f x|), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  by_cases htM : t ≤ max 1 T
  · exact (hm ⟨ht, htM⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (hT t ((le_max_right 1 T).trans (lt_of_not_ge htM).le)).trans
      ((le_max_left _ _).trans (le_max_right _ _))

noncomputable def leading (m : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (2 / (Real.pi * t)) * Real.cos (t - ((2 * m + 1 : ℝ) * Real.pi / 4))

theorem leading_continuousOn (m : ℕ) : ContinuousOn (leading m) (Ici 1) := by
  unfold leading
  apply ContinuousOn.mul
  · apply Real.continuous_sqrt.comp_continuousOn
    exact continuousOn_const.div (by fun_prop) (fun t ht => by
      have ht0 : 0 < t := zero_lt_one.trans_le ht
      positivity)
  · fun_prop

/-- The asymptotic remainder asserted in (126), uniformly for every t≥1. -/
theorem large_remainder_bound (hDLMF : DLMFIdentities) (m : ℕ) :
    ∃ C > 0, ∀ t : ℝ, 1 ≤ t →
      |J m t - leading m t| ≤ C * t ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := (hDLMF.asymptotic m).exists_nonneg
  let f : ℝ → ℝ := fun t => (J m t - leading m t) * t ^ (3 / 2 : ℝ)
  have hf : ContinuousOn f (Ici 1) :=
    ((hDLMF.continuous m).continuousOn.sub (leading_continuousOn m)).mul
      (Real.continuous_rpow_const (by norm_num)).continuousOn
  have he : ∀ᶠ t in atTop, |f t| ≤ C := by
    filter_upwards [hc.bound, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have ht0 : 0 < t := zero_lt_one.trans_le ht1
    have hp : 0 < t ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hp' : 0 < t ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
    have hcancel : t ^ (-(3 / 2 : ℝ)) * t ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add ht0]
      norm_num
    simp only [Real.norm_eq_abs, abs_of_pos hp'] at ht
    dsimp [f]
    rw [abs_mul, abs_of_pos hp]
    exact (mul_le_mul_of_nonneg_right ht hp.le).trans_eq (by rw [mul_assoc, hcancel, mul_one])
  obtain ⟨K, hK, hk⟩ := bounded_Ici_of_eventually hf he
  refine ⟨K, hK, ?_⟩
  intro t ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp : 0 < t ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have h := hk t ht
  change |(J m t - leading m t) * t ^ (3 / 2 : ℝ)| ≤ K at h
  rw [abs_mul, abs_of_pos hp] at h
  rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr h

/-- The literal min(t^m,t^(-1/2)) estimate, including both sides of t=1. -/
theorem two_regime_bound (hDLMF : DLMFIdentities) (m : ℕ) :
    ∃ C > 0, ∀ t : ℝ, 0 < t →
      |J m t| ≤ C * min (t ^ m) (t ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hbound, hdecay⟩ := J_bounded_and_decay hDLMF m
  let C := K + Real.exp 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : K ≤ C := by dsimp [C]; linarith [Real.exp_pos 1]
  have hEC : Real.exp 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hsmall : |J m t| ≤ C * t ^ m := by
    by_cases ht1 : t ≤ 1
    · exact (small_argument_bound m ht.le ht1).trans
        (mul_le_mul_of_nonneg_right hEC (pow_nonneg ht.le _))
    · have hp : 1 ≤ t ^ m := one_le_pow₀ (le_of_not_ge ht1)
      exact (hbound t ht.le).trans (hKC.trans (le_mul_of_one_le_right hC.le hp))
  have hlarge : |J m t| ≤ C * t ^ (-(1 / 2 : ℝ)) := by
    by_cases ht1 : 1 ≤ t
    · exact (hdecay t ht1).trans
        (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg ht.le _))
    · have hp : 1 ≤ t ^ (-(1 / 2 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht (le_of_not_ge ht1) (by norm_num)
      exact (hbound t ht.le).trans (hKC.trans (le_mul_of_one_le_right hC.le hp))
  rw [mul_min_of_nonneg _ _ hC.le]
  exact le_min hsmall hlarge

end DepthAspect.BesselRemainder
