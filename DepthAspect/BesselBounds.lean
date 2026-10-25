import DepthAspect.BesselFirstKind
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The Bessel bounds in (126), derived from the cited general asymptotic. -/
open Filter Set Asymptotics MeasureTheory
open scoped BigOperators
namespace DepthAspect.BesselBounds
open BesselFirstKind

theorem sqrt_amplitude {t : ℝ} (ht : 0 < t) :
    Real.sqrt (2 / (Real.pi * t)) = Real.sqrt (2 / Real.pi) * t ^ (-(1 / 2 : ℝ)) := by
  have he : 2 / (Real.pi * t) = (2 / Real.pi) * t⁻¹ := by ring
  have hi : Real.sqrt t⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
  rw [he, Real.sqrt_mul (by positivity), hi]

/-- The leading oscillatory term plus the remainder yields the required
half-power decay, without assuming that decay separately. -/
theorem J_isBigO_atTop (hDLMF : DLMFIdentities) (m : ℕ) :
    J m =O[atTop] (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := (hDLMF.asymptotic m).exists_nonneg
  apply IsBigO.of_bound (C + Real.sqrt (2 / Real.pi))
  filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
  have hr1 : 0 < t ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
  have hpow : t ^ (-(3 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hcos : |Real.sqrt (2 / (Real.pi * t)) *
      Real.cos (t - ((2 * m + 1 : ℝ) * Real.pi / 4))| ≤
      Real.sqrt (2 / Real.pi) * t ^ (-(1 / 2 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (2 / (Real.pi * t)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_one, sqrt_amplitude ht0]
  have htri := norm_le_norm_sub_add (J m t)
    (Real.sqrt (2 / (Real.pi * t)) * Real.cos (t - ((2 * m + 1 : ℝ) * Real.pi / 4)))
  simp only [Real.norm_eq_abs, abs_of_pos hr0, abs_of_pos hr1] at ht htri ⊢
  have hCp := mul_le_mul_of_nonneg_left hpow hC
  nlinarith

/-- A continuous function that is eventually bounded is bounded on every
fixed right half-line. This fills the compact interval left by asymptotics. -/
theorem bounded_on_Ici_of_eventually {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ᶠ t in atTop, |f t| ≤ C) :
    ∃ K > 0, ∀ t : ℝ, 1 ≤ t → |f t| ≤ K := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 : ℝ) (max 1 T)).Nonempty from ⟨1, le_rfl, le_max_left _ _⟩)
    hf.abs.continuousOn
  refine ⟨max 1 (max C |f x|), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  by_cases htM : t ≤ max 1 T
  · exact (hmax ⟨ht, htM⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hTt : T ≤ t := (le_max_right 1 T).trans (lt_of_not_ge htM).le
    exact (hT t hTt).trans ((le_max_left _ _).trans (le_max_right _ _))

/-- The large-argument estimate is uniform down to t=1. Its constant depends
only on the Bessel order and the cited general identities. -/
theorem large_argument_bound (hDLMF : DLMFIdentities) (m : ℕ) :
    ∃ K > 0, ∀ t : ℝ, 1 ≤ t → |J m t| ≤ K * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, _, hC⟩ := (J_isBigO_atTop hDLMF m).exists_nonneg
  let g : ℝ → ℝ := fun t => J m t * t ^ (1 / 2 : ℝ)
  have hg : Continuous g := (hDLMF.continuous m).mul
    (Real.continuous_rpow_const (by norm_num))
  have hgb : ∀ᶠ t in atTop, |g t| ≤ C := by
    filter_upwards [hC.bound, eventually_ge_atTop (1 : ℝ)] with t ht ht1
    have ht0 : 0 < t := by linarith
    have hp : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have hp' : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
    have he : t ^ (-(1 / 2 : ℝ)) * t ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add ht0]
      norm_num
    simp only [Real.norm_eq_abs, abs_of_pos hp'] at ht
    dsimp [g]
    rw [abs_mul, abs_of_pos hp]
    exact (mul_le_mul_of_nonneg_right ht hp.le).trans_eq (by rw [mul_assoc, he, mul_one])
  obtain ⟨K, hK, hKbound⟩ := bounded_on_Ici_of_eventually hg hgb
  refine ⟨K, hK, ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith
  have hp : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
  have h := hKbound t ht
  change |J m t * t ^ (1 / 2 : ℝ)| ≤ K at h
  rw [abs_mul, abs_of_pos hp] at h
  rw [Real.rpow_neg ht0.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr h

/-- One order-dependent constant bounds J on the nonnegative half-line and
also controls its half-power decay above one. -/
theorem J_bounded_and_decay (hDLMF : DLMFIdentities) (m : ℕ) :
    ∃ C > 0, (∀ t : ℝ, 0 ≤ t → |J m t| ≤ C) ∧
      (∀ t : ℝ, 1 ≤ t → |J m t| ≤ C * t ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hlarge⟩ := large_argument_bound hDLMF m
  refine ⟨Real.exp 1 + K, by positivity, ?_, ?_⟩
  · intro t ht
    by_cases ht1 : t ≤ 1
    · have hsmall := small_argument_bound m ht ht1
      have hp : t ^ m ≤ 1 := by
        simpa using pow_le_pow_left₀ ht ht1 m
      exact hsmall.trans ((mul_le_of_le_one_right (Real.exp_pos _).le hp).trans
        (by linarith))
    · have hp := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge ht1) (by norm_num :
          -(1 / 2 : ℝ) ≤ 0)
      exact (hlarge t (le_of_not_ge ht1)).trans
        ((mul_le_of_le_one_right hK.le hp).trans (by linarith [Real.exp_pos 1]))
  · intro t ht
    exact (hlarge t ht).trans (mul_le_mul_of_nonneg_right
      (by linarith [Real.exp_pos 1]) (Real.rpow_nonneg (by linarith) _))

/-- The two quantitative bounds for the actual odd-order antiderivative
in (126) follow from its cited finite identity and proved Bessel bounds. -/
theorem odd_integral_bounds (hDLMF : DLMFIdentities) (n : ℕ) :
    ∃ K > 0,
      (∀ T : ℝ, 0 ≤ T → |∫ t : ℝ in (0)..T, J (2 * n + 1) t| ≤ K) ∧
      (∀ T : ℝ, 1 ≤ T → |(∫ t : ℝ in (0)..T, J (2 * n + 1) t) - 1| ≤
        K * T ^ (-(1 / 2 : ℝ))) := by
  classical
  choose C hC hbound hdecay using J_bounded_and_decay hDLMF
  let S := Finset.Icc 1 n
  let K : ℝ := 1 + C 0 + 2 * ∑ j ∈ S, C (2 * j)
  have hsum0 : 0 ≤ ∑ j ∈ S, C (2 * j) :=
    Finset.sum_nonneg (fun j _ => (hC _).le)
  have hK : 0 < K := by dsimp [K]; linarith [hC 0]
  have hsum (T : ℝ) (hT : 0 ≤ T) :
      |∑ j ∈ S, J (2 * j) T| ≤ ∑ j ∈ S, C (2 * j) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun j _ => hbound _ T hT))
  have hsumD (T : ℝ) (hT : 1 ≤ T) :
      |∑ j ∈ S, J (2 * j) T| ≤
        (∑ j ∈ S, C (2 * j)) * T ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ S, |J (2 * j) T| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ S, C (2 * j) * T ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum (fun j _ => hdecay _ T hT)
      _ = _ := (Finset.sum_mul _ _ _).symm
  refine ⟨K, hK, ?_, ?_⟩
  · intro T hT
    rw [hDLMF.odd_integral n T hT]
    have h1 := abs_sub (1 - J 0 T) (2 * ∑ j ∈ S, J (2 * j) T)
    have h2 := abs_sub (1 : ℝ) (J 0 T)
    simp only [abs_one, abs_mul, Nat.abs_ofNat] at h1 h2
    have h3 := hbound 0 T hT
    have h4 := hsum T hT
    dsimp [K, S] at *
    linarith
  · intro T hT
    rw [hDLMF.odd_integral n T (by linarith)]
    have he : 1 - J 0 T - 2 * ∑ j ∈ S, J (2 * j) T - 1 =
        -J 0 T - 2 * ∑ j ∈ S, J (2 * j) T := by ring
    change |1 - J 0 T - 2 * ∑ j ∈ S, J (2 * j) T - 1| ≤ _
    rw [he]
    have h1 := abs_sub (-J 0 T) (2 * ∑ j ∈ S, J (2 * j) T)
    simp only [abs_neg, abs_mul, Nat.abs_ofNat] at h1
    have h2 := hdecay 0 T hT
    have h3 := hsumD T hT
    have hp : 0 ≤ T ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    dsimp [K]
    nlinarith

/-- Each fixed Bessel order tends to zero at positive infinity. -/
theorem J_tendsto_zero (hDLMF : DLMFIdentities) (m : ℕ) :
    Tendsto (J m) atTop (nhds 0) :=
  (J_isBigO_atTop hDLMF m).trans_tendsto
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))

/-- The improper odd-order integral in (126) is a limit of actual finite
interval integrals. No absolutely convergent integral of J itself is asserted. -/
theorem odd_integral_tendsto_one (hDLMF : DLMFIdentities) (n : ℕ) :
    Tendsto (fun T : ℝ => ∫ t : ℝ in (0)..T, J (2 * n + 1) t) atTop (nhds 1) := by
  have hs : Tendsto (fun T : ℝ => ∑ j ∈ Finset.Icc 1 n, J (2 * j) T) atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.Icc 1 n)
      (fun j _ => J_tendsto_zero hDLMF (2 * j))
  have h : Tendsto (fun T : ℝ => 1 - J 0 T -
      2 * ∑ j ∈ Finset.Icc 1 n, J (2 * j) T) atTop (nhds (1 - 0 - 2 * 0)) :=
    (tendsto_const_nhds.sub (J_tendsto_zero hDLMF 0)).sub
      (tendsto_const_nhds.mul hs)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (hDLMF.odd_integral n T hT).symm

end DepthAspect.BesselBounds
