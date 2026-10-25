import DepthAspect.RandomMatrixMainTerms
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Elementary exponential means and their interchange with uniformly
absolutely convergent series. These are internal analytic lemmas. -/
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace DepthAspect.OscillatoryMean

noncomputable def wave (ω x : ℝ) : ℂ := Complex.exp (((ω * x : ℝ) : ℂ) * Complex.I)
noncomputable def average (f : ℝ → ℂ) (T : ℝ) : ℂ := (T : ℂ)⁻¹ * ∫ x : ℝ in (0)..T, f x

theorem wave_continuous (ω : ℝ) : Continuous (wave ω) := by unfold wave; fun_prop
@[simp] theorem wave_norm (ω x : ℝ) : ‖wave ω x‖ = 1 := by simp [wave, Complex.norm_exp]
@[simp] theorem wave_zero (x : ℝ) : wave 0 x = 1 := by simp [wave]

/-- The exact finite integral, before taking a mean. -/
theorem integral_wave {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    (∫ x : ℝ in (0)..T, wave ω x) = (wave ω T - 1) / ((ω : ℂ) * Complex.I) := by
  have hc : (ω : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hω) Complex.I_ne_zero
  have he : wave ω = fun x : ℝ => Complex.exp (((ω : ℂ) * Complex.I) * (x : ℂ)) := by
    funext x
    unfold wave
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- A nonzero exponential has a uniformly bounded primitive. -/
theorem integral_wave_bound {ω : ℝ} (hω : ω ≠ 0) (T : ℝ) :
    ‖∫ x : ℝ in (0)..T, wave ω x‖ ≤ 2 / |ω| := by
  rw [integral_wave hω, norm_div, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact (norm_sub_le _ _).trans_eq (by norm_num)

/-- Averaging a uniformly bounded function preserves its bound. -/
theorem average_norm_bound {f : ℝ → ℂ} {C T : ℝ} (hT : 0 < T)
    (hb : ∀ x : ℝ, ‖f x‖ ≤ C) : ‖average f T‖ ≤ C := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T) (fun x _ => hb x)
  simp only [sub_zero, abs_of_pos hT] at hi
  unfold average
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ T⁻¹ * (C * T) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hT.le)
    _ = C := by field_simp

/-- Every nonzero frequency has mean zero over real endpoints T→∞. -/
theorem average_wave_tendsto_zero {ω : ℝ} (hω : ω ≠ 0) :
    Tendsto (average (wave ω)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun T : ℝ => (2 / |ω|) / T)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    unfold average
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    calc
      _ ≤ T⁻¹ * (2 / |ω|) :=
        mul_le_mul_of_nonneg_left (integral_wave_bound hω T) (inv_nonneg.mpr hT.le)
      _ = _ := by ring
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- The zero frequency has mean one. -/
theorem average_wave_tendsto (ω : ℝ) :
    Tendsto (average (wave ω)) atTop (𝓝 (if ω = 0 then 1 else 0)) := by
  by_cases hω : ω = 0
  · subst ω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp [average, wave, ne_of_gt hT]
  · rw [if_neg hω]
    exact average_wave_tendsto_zero hω

/-- The finite-interval integral commutes with an absolutely uniformly
convergent series, with an explicit summable constant majorant. -/
theorem average_tsum {ι : Type*} [Countable ι] (F : ι → ℝ → ℂ)
    (hF : ∀ i, Continuous (F i)) {bound : ι → ℝ} (hs : Summable bound)
    (hb : ∀ i x, ‖F i x‖ ≤ bound i) (T : ℝ) :
    average (fun x => ∑' i, F i x) T = ∑' i, average (F i) T := by
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := F) (f := fun x => ∑' i, F i x) (a := (0 : ℝ)) (b := T) (μ := volume)
    (fun i _ => bound i)
    (fun i => (hF i).aestronglyMeasurable)
    (fun i => by filter_upwards [] with x _; exact hb i x)
    (by filter_upwards [] with x _; exact hs)
    intervalIntegrable_const
    (by
      filter_upwards [] with x _
      exact (hs.of_norm_bounded (fun i => hb i x)).hasSum)
  unfold average
  rw [tsum_mul_left, hdom.tsum_eq]

/-- Taking the large-interval mean commutes with the same actual series. -/
theorem average_tsum_tendsto {ι : Type*} [Countable ι] (F : ι → ℝ → ℂ)
    (hF : ∀ i, Continuous (F i)) {bound : ι → ℝ} (hs : Summable bound)
    (hb : ∀ i x, ‖F i x‖ ≤ bound i) (L : ι → ℂ)
    (hL : ∀ i, Tendsto (average (F i)) atTop (𝓝 (L i))) :
    Tendsto (average (fun x => ∑' i, F i x)) atTop (𝓝 (∑' i, L i)) := by
  have ht := tendsto_tsum_of_dominated_convergence hs hL (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT i
    exact average_norm_bound hT (hb i))
  apply ht.congr'
  filter_upwards [] with T
  exact (average_tsum F hF hs hb T).symm

end DepthAspect.OscillatoryMean
