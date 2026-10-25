import DepthAspect.MurmurationFourier
import DepthAspect.BesselBounds
import DepthAspect.FourierScaling
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! Decay and Poisson summation for the actual compact kernel. -/
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform
namespace DepthAspect.MurmurationDecay
open MurmurationKernel MurmurationFourier BesselFirstKind BesselBounds

theorem complexKernel_hasCompactSupport (k : ℕ) : HasCompactSupport (complexKernel k) :=
  (kernel_hasCompactSupport k).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

theorem complexKernel_even (a : ℕ) : Function.Even (complexKernel (2 * a + 2)) := by
  intro x
  unfold complexKernel
  rw [kernel_even (by omega) (show Even (2 * a + 2) from ⟨a + 1, by omega⟩)]

theorem fourier_even (a : ℕ) : Function.Even (𝓕 (complexKernel (2 * a + 2))) := by
  intro x
  rw [← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg]
  have he : (fun y : ℝ => complexKernel (2 * a + 2) (-y)) =
      complexKernel (2 * a + 2) := funext (complexKernel_even a)
  rw [he]

/-- The Bessel transform gives actual decay stronger than 1/|ξ|. -/
theorem fourier_decay_positive (hDLMF : DLMFIdentities) (a : ℕ) :
    ∃ C > 0, ∀ ξ : ℝ, 1 ≤ ξ →
      ‖𝓕 (complexKernel (2 * a + 2)) ξ‖ ≤ C * ξ ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨K, hK, hJ⟩ := large_argument_bound hDLMF (2 * a + 1)
  let m : ℝ := ((2 * a + 1 : ℕ) : ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  refine ⟨K * m, by positivity, ?_⟩
  intro ξ hξ
  have hξ0 : 0 < ξ := by linarith
  have ht : ξ ≤ 2 * Real.pi * ξ := by nlinarith [Real.two_le_pi]
  have ht1 : 1 ≤ 2 * Real.pi * ξ := hξ.trans ht
  have hp : (2 * Real.pi * ξ) ^ (-(1 / 2 : ℝ)) ≤ ξ ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hξ0 ht (by norm_num)
  have hb := (hJ (2 * Real.pi * ξ) ht1).trans (mul_le_mul_of_nonneg_left hp hK.le)
  have hn : ‖𝓕 (complexKernel (2 * a + 2)) ξ‖ =
      m / (2 * ξ) * |J (2 * a + 1) (2 * Real.pi * ξ)| := by
    rw [fourier_eq_bessel hDLMF a (ne_of_gt hξ0), norm_mul,
      Complex.norm_real, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_pos hξ0,
      m, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (a : ℝ) + 1)]
  have he : ξ⁻¹ * ξ ^ (-(1 / 2 : ℝ)) = ξ ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hξ0]
    norm_num
  rw [hn]
  calc
    _ ≤ m / (2 * ξ) * (K * ξ ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (K * m / 2) * ξ ^ (-(3 / 2 : ℝ)) := by
      rw [← he]
      ring
    _ ≤ (K * m) * ξ ^ (-(3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hξ0.le _)
      nlinarith

theorem fourier_decay_abs (hDLMF : DLMFIdentities) (a : ℕ) :
    ∃ C > 0, ∀ ξ : ℝ, 1 ≤ |ξ| →
      ‖𝓕 (complexKernel (2 * a + 2)) ξ‖ ≤ C * |ξ| ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := fourier_decay_positive hDLMF a
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  have h := hb |ξ| hξ
  by_cases hξ0 : 0 ≤ ξ
  · simpa only [abs_of_nonneg hξ0] using h
  · simpa only [abs_of_neg (lt_of_not_ge hξ0), fourier_even a ξ] using h

theorem fourier_continuous (k : ℕ) : Continuous (𝓕 (complexKernel k)) := by
  have hi : Integrable (complexKernel k) :=
    (complexKernel_continuous k).integrable_of_hasCompactSupport
      (complexKernel_hasCompactSupport k)
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hi

/-- The complete bound in (127), including zero and the intervening compact
interval, follows from continuity and the proved large-frequency bound. -/
theorem fourier_decay_global (hDLMF : DLMFIdentities) (a : ℕ) :
    ∃ C > 0, ∀ ξ : ℝ, ‖𝓕 (complexKernel (2 * a + 2)) ξ‖ ≤
      C * (1 + |ξ|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := fourier_decay_abs hDLMF a
  let g : ℝ → ℂ := fun x => 𝓕 (complexKernel (2 * a + 2)) x *
    ((1 + |x|) ^ (3 / 2 : ℝ) : ℝ)
  have hg : Continuous g := (fourier_continuous _).mul
    (Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp
        (continuous_const.add continuous_abs)))
  have hgo : g =O[cocompact ℝ] (1 : ℝ → ℝ) := by
    apply IsBigO.of_bound (C * (2 : ℝ) ^ (3 / 2 : ℝ))
    have hnorm : ∀ᶠ x : ℝ in cocompact ℝ, 1 ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)
    filter_upwards [hnorm] with x hx
    have hx1 : 1 ≤ |x| := by simpa only [Real.norm_eq_abs] using hx
    have hx0 : 0 < |x| := by linarith
    have hp : (1 + |x|) ^ (3 / 2 : ℝ) ≤
        (2 * |x|) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have he : |x| ^ (-(3 / 2 : ℝ)) * |x| ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hx0]
      norm_num
    simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (by positivity : 0 < 1 + |x|) _),
      Pi.one_apply, norm_one, mul_one]
    calc
      _ ≤ (C * |x| ^ (-(3 / 2 : ℝ))) * (1 + |x|) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (hb x hx1) (by positivity)
      _ ≤ (C * |x| ^ (-(3 / 2 : ℝ))) * (2 * |x|) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = C * (2 : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hx0.le]
        calc
          _ = (C * (2 : ℝ) ^ (3 / 2 : ℝ)) *
              (|x| ^ (-(3 / 2 : ℝ)) * |x| ^ (3 / 2 : ℝ)) := by ring
          _ = _ := by rw [he, mul_one]
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp
    (hg.isBounded_range_iff_isBigO.mpr hgo)
  refine ⟨max 1 D, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  have hp : 0 < (1 + |x|) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hx := hD (g x) ⟨x, rfl⟩
  simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at hx
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + |x|), ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr (hx.trans (le_max_right _ _))

/-- Compact support supplies every spatial decay bound needed by Poisson. -/
theorem compact_isBigO {f : ℝ → ℂ} (hf : HasCompactSupport f) (b : ℝ) :
    f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-b)) := by
  have hz : (fun _ : ℝ => (0 : ℂ)) =ᶠ[cocompact ℝ] f := by
    filter_upwards [hf.isCompact.compl_mem_cocompact] with x hx
    exact (image_eq_zero_of_notMem_tsupport hx).symm
  exact (isBigO_zero (fun x : ℝ => |x| ^ (-b)) (cocompact ℝ)).congr'
    hz Filter.EventuallyEq.rfl

theorem fourier_isBigO (hDLMF : DLMFIdentities) (a : ℕ) :
    (𝓕 (complexKernel (2 * a + 2))) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, _, hb⟩ := fourier_decay_abs hDLMF a
  apply IsBigO.of_bound C
  have hnorm : ∀ᶠ x : ℝ in cocompact ℝ, 1 ≤ ‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hnorm] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    using hb x (by simpa only [Real.norm_eq_abs] using hx)

/-- Poisson is applied to the continuous zero extension, so the endpoints
±1 require no ad hoc boundary convention or extra smoothness assumption. -/
theorem poisson (hDLMF : DLMFIdentities) (a : ℕ) (x : ℝ) :
    (∑' n : ℤ, complexKernel (2 * a + 2) (x + n)) =
      ∑' n : ℤ, 𝓕 (complexKernel (2 * a + 2)) n *
        fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier_of_rpow_decay
    (complexKernel_continuous _) (by norm_num : (1 : ℝ) < 3 / 2)
    (compact_isBigO (complexKernel_hasCompactSupport _) _)
    (fourier_isBigO hDLMF a) x

theorem scaled_hasCompactSupport (k : ℕ) {c : ℝ} (hc : 0 < c) :
    HasCompactSupport (fun x => complexKernel k (c * x)) :=
  (complexKernel_hasCompactSupport k).comp_homeomorph
    (Homeomorph.mulLeft₀ c (ne_of_gt hc))

theorem scaled_lattice_summable (k : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => complexKernel k (c * n)) :=
  summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2))
    ((compact_isBigO (scaled_hasCompactSupport k hc) (3 / 2)).comp_tendsto
      Int.tendsto_coe_cofinite)

/-- The decay proof is retained after every positive lattice rescaling. -/
theorem fourier_scaled_isBigO (hDLMF : DLMFIdentities) (a : ℕ)
    {c : ℝ} (hc : 0 < c) :
    (𝓕 (fun x => complexKernel (2 * a + 2) (c * x))) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := fourier_decay_abs hDLMF a
  apply IsBigO.of_bound (c⁻¹ * C / c ^ (-(3 / 2 : ℝ)))
  have hnorm : ∀ᶠ x : ℝ in cocompact ℝ, max 1 c ≤ ‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (max 1 c))
  filter_upwards [hnorm] with x hx
  have hx' : c ≤ |x| := (le_max_right 1 c).trans (by simpa using hx)
  have hxc : 1 ≤ |x / c| := by
    rw [abs_div, abs_of_pos hc]
    exact (le_div_iff₀ hc).mpr (by simpa using hx')
  rw [FourierScaling.fourier_scale _ hc, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hc]
  have hn : ‖|x| ^ (-(3 / 2 : ℝ))‖ = |x| ^ (-(3 / 2 : ℝ)) :=
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)
  rw [hn]
  calc
    _ ≤ c⁻¹ * (C * |x / c| ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hb _ hxc) (inv_pos.mpr hc).le
    _ = (c⁻¹ * C / c ^ (-(3 / 2 : ℝ))) * |x| ^ (-(3 / 2 : ℝ)) := by
      rw [abs_div, abs_of_pos hc, Real.div_rpow (abs_nonneg x) hc.le]
      ring

/-- Poisson summation on the actual rescaled lattice, with its exact
Jacobian. Both series are justified by the proved support and decay. -/
theorem poisson_scaled (hDLMF : DLMFIdentities) (a : ℕ)
    {c : ℝ} (hc : 0 < c) :
    (∑' n : ℤ, complexKernel (2 * a + 2) (c * n)) =
      ∑' n : ℤ, (c⁻¹ : ℂ) * 𝓕 (complexKernel (2 * a + 2)) ((n : ℝ) / c) := by
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay
    ((complexKernel_continuous _).comp (continuous_const.mul continuous_id))
    (by norm_num : (1 : ℝ) < 3 / 2)
    (compact_isBigO (scaled_hasCompactSupport (2 * a + 2) hc) _)
    (fourier_scaled_isBigO hDLMF a hc) (0 : ℝ)
  simpa only [Function.comp_def, Pi.mul_apply, id_eq, zero_add, AddCircle.coe_zero,
    fourier_eval_zero, mul_one, FourierScaling.fourier_scale _ hc] using h

theorem scaled_fourier_integer_summable (hDLMF : DLMFIdentities) (a : ℕ)
    {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => (c⁻¹ : ℂ) *
      𝓕 (complexKernel (2 * a + 2)) ((n : ℝ) / c)) := by
  have h := summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2))
    ((fourier_scaled_isBigO hDLMF a hc).comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [Function.comp_def, FourierScaling.fourier_scale _ hc] using h

/-- Pairing the nonzero integer frequencies is justified by absolute
summability; the zero frequency remains explicit for its later cancellation. -/
theorem poisson_scaled_positive (hDLMF : DLMFIdentities) (a : ℕ)
    {c : ℝ} (hc : 0 < c) :
    (∑' n : ℤ, complexKernel (2 * a + 2) (c * n)) =
      (c⁻¹ : ℂ) * 𝓕 (complexKernel (2 * a + 2)) 0 +
        2 * (c⁻¹ : ℂ) * ∑' ν : ℕ+,
          𝓕 (complexKernel (2 * a + 2)) ((ν : ℝ) / c) := by
  rw [poisson_scaled hDLMF a hc]
  have heven : Function.Even (fun n : ℤ => (c⁻¹ : ℂ) *
      𝓕 (complexKernel (2 * a + 2)) ((n : ℝ) / c)) := by
    intro n
    simp only [Int.cast_neg, neg_div, (fourier_even a) ((n : ℝ) / c)]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven
    (scaled_fourier_integer_summable hDLMF a hc)]
  simp only [Int.cast_zero, zero_div, Int.cast_natCast, tsum_mul_left, nsmul_eq_mul,
    Nat.cast_ofNat]
  ring

end DepthAspect.MurmurationDecay
