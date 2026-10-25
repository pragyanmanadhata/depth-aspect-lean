import DepthAspect.CosineMeans
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic

/-! Existence of means for uniform limits of continuous periodic functions.
This also applies to their positive parts and squares. -/
open MeasureTheory Filter Set
open scoped Topology
namespace DepthAspect.UniformPeriodicMean
open OscillatoryMean

noncomputable def realAverage (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  T⁻¹ * ∫ x : ℝ in (0)..T, f x

theorem realAverage_cast (f : ℝ → ℝ) (T : ℝ) :
    (realAverage f T : ℂ) = average (fun x => (f x : ℂ)) T := by
  simp only [realAverage, OscillatoryMean.average, Complex.ofReal_mul, Complex.ofReal_inv,
    intervalIntegral.integral_ofReal]

theorem realAverage_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (T : ℝ) :
    realAverage (fun x => f x - g x) T = realAverage f T - realAverage g T := by
  unfold realAverage
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 T) (hg.intervalIntegrable 0 T), mul_sub]

theorem realAverage_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (T : ℝ) :
    realAverage (fun x => f x + g x) T = realAverage f T + realAverage g T := by
  unfold realAverage
  rw [intervalIntegral.integral_add (hf.intervalIntegrable 0 T) (hg.intervalIntegrable 0 T), mul_add]

theorem realAverage_const_mul (c : ℝ) (f : ℝ → ℝ) (T : ℝ) :
    realAverage (fun x => c * f x) T = c * realAverage f T := by
  unfold realAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem realAverage_abs_le {f : ℝ → ℝ} {C T : ℝ} (hT : 0 < T)
    (hb : ∀ x, |f x| ≤ C) : |realAverage f T| ≤ C := by
  have h := average_norm_bound (f := fun x => (f x : ℂ)) hT
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb x)
  rw [← realAverage_cast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem realAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x ≤ g x) {T : ℝ} (hT : 0 < T) :
    realAverage f T ≤ realAverage g T := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hT.le)
  exact intervalIntegral.integral_mono_on hT.le (hf.intervalIntegrable 0 T) (hg.intervalIntegrable 0 T)
    (fun x _ => hfg x)

/-- Periodic means over arbitrary real endpoints are proved by the actual
integer-floor bounds on the finite primitive. -/
theorem periodic_mean {g : ℝ → ℝ} {P : ℝ} (hg : Continuous g)
    (hp : Function.Periodic g P) (hP : 0 < P) :
    Tendsto (realAverage g) atTop (𝓝 (realAverage g P)) := by
  let I : ℝ := ∫ x : ℝ in (0)..P, g x
  let lo := sInf ((fun t => ∫ x : ℝ in (0)..t, g x) '' Icc 0 P)
  let hi := sSup ((fun t => ∫ x : ℝ in (0)..t, g x) '' Icc 0 P)
  have hfloor : Tendsto (fun t : ℝ => ((⌊t / P⌋ : ℤ) : ℝ) / t)
      atTop (𝓝 P⁻¹) := by
    have h := tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hP.le)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [mul_comm, ← div_eq_mul_inv,
      natCast_floor_eq_intCast_floor (div_nonneg ht.le hP.le)]
  have hlim (C : ℝ) : Tendsto
      (fun t : ℝ => (C + ((⌊t / P⌋ : ℤ) : ℝ) * I) / t)
      atTop (𝓝 (realAverage g P)) := by
    have h := ((tendsto_const_nhds (x := C)).div_atTop tendsto_id).add (hfloor.mul_const I)
    convert h using 1
    · funext t
      dsimp only [id]
      ring
    · simp only [zero_add, realAverage, I]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim lo) (hlim hi)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hp.sInf_add_zsmul_le_integral_of_pos (hg.intervalIntegrable 0 P) hP t
    dsimp [realAverage, lo, I]
    rw [← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by simpa only [zsmul_eq_mul] using h) ht.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have h := hp.integral_le_sSup_add_zsmul_of_pos (hg.intervalIntegrable 0 P) hP t
    dsimp [realAverage, hi, I]
    rw [← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (by simpa only [zsmul_eq_mul] using h) ht.le

/-- Uniformly close continuous functions have uniformly close finite means
for every positive averaging endpoint. -/
theorem realAverage_dist_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {ε : ℝ} (hε : ∀ x, |f x - g x| ≤ ε) {T : ℝ} (hT : 0 < T) :
    dist (realAverage f T) (realAverage g T) ≤ ε := by
  rw [Real.dist_eq, ← realAverage_sub hf hg]
  exact realAverage_abs_le hT hε

/-- The mean-existence step used for A, its square and its two signed parts.
The approximants may have different positive periods. -/
theorem mean_exists_of_uniform_periodic {f : ℝ → ℝ} (hf : Continuous f)
    (happrox : ∀ ε > 0, ∃ g : ℝ → ℝ, Continuous g ∧
      (∃ P > 0, Function.Periodic g P) ∧ ∀ x, |f x - g x| ≤ ε) :
    ∃ L : ℝ, Tendsto (realAverage f) atTop (𝓝 L) := by
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨g, hg, ⟨P, hP, hp⟩, hfg⟩ := happrox (ε / 4) (by positivity)
  have hc := (periodic_mean hg hp hP).cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε / 2) (by positivity)
  refine ⟨max 1 N, ?_⟩
  intro U hU V hV
  have hU0 : 0 < U := zero_lt_one.trans_le ((le_max_left _ _).trans hU)
  have hV0 : 0 < V := zero_lt_one.trans_le ((le_max_left _ _).trans hV)
  have h₁ := realAverage_dist_le hf hg hfg hU0
  have h₂ := realAverage_dist_le hf hg hfg hV0
  have h₃ := hN U ((le_max_right _ _).trans hU) V ((le_max_right _ _).trans hV)
  calc
    _ ≤ dist (realAverage f U) (realAverage g U) +
        dist (realAverage g U) (realAverage f V) := dist_triangle _ _ _
    _ ≤ dist (realAverage f U) (realAverage g U) +
        (dist (realAverage g U) (realAverage g V) +
          dist (realAverage g V) (realAverage f V)) :=
      add_le_add (le_refl _) (dist_triangle _ _ _)
    _ < ε := by rw [dist_comm (realAverage g V) (realAverage f V)]; linarith

end DepthAspect.UniformPeriodicMean
