import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-!
# The Mertens-weighted main term

The only arithmetic premise is the cited bounded-error Mertens estimate for
the actual odd-prime cumulative sum. Abel summation and the analytic change
of variables are proved for the actual finite weighted sum.
-/
namespace DepthAspect.MertensWeights

open Finset MeasureTheory
open scoped BigOperators SchwartzMap Classical

/-- The coefficient `log p/p` at odd primes, and zero at other integers. -/
noncomputable def oddPrimeWeight (n : ℕ) : ℝ :=
  if n.Prime ∧ Odd n then Real.log n / (n : ℝ) else 0

@[simp] theorem oddPrimeWeight_zero : oddPrimeWeight 0 = 0 := by simp [oddPrimeWeight]
@[simp] theorem oddPrimeWeight_one : oddPrimeWeight 1 = 0 := by simp [oddPrimeWeight]

/-- The actual cumulative function appearing in the cited Mertens estimate. -/
noncomputable def mertensSum (Y : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊Y⌋₊, oddPrimeWeight n

/-- An actual finite odd-prime weighted sum. -/
noncomputable def weightedSum (Y : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊Y⌋₊, f n * (oddPrimeWeight n : ℂ)

theorem cumulative_cast (Y : ℝ) :
    (∑ n ∈ Icc 0 ⌊Y⌋₊, (oddPrimeWeight n : ℂ)) = (mertensSum Y : ℂ) := by
  simp only [mertensSum, Complex.ofReal_sum]

/-- Abel summation for these coefficients, with no arithmetic approximation. -/
theorem weightedSum_abel {Y : ℝ} (hY : 2 ≤ Y) {f : ℝ → ℂ}
    (hf : ∀ x ∈ Set.Icc (2 : ℝ) Y, DifferentiableAt ℝ f x)
    (hdf : IntegrableOn (deriv f) (Set.Icc 2 Y)) :
    weightedSum Y f = f Y * (mertensSum Y : ℂ) -
      ∫ x in (2 : ℝ)..Y, deriv f x * (mertensSum x : ℂ) := by
  have hs := sum_mul_eq_sub_integral_mul₁ (fun n => (oddPrimeWeight n : ℂ))
    (by simp) (by simp) Y hf hdf
  simp_rw [cumulative_cast] at hs
  rw [← intervalIntegral.integral_of_le hY] at hs
  exact hs

/-- The norm of the Abel error is controlled by the total variation of the
weight and the cited Mertens error bound. -/
theorem mertens_error_integral_bound {Y C : ℝ} (hY : 2 ≤ Y)
    (hM : ∀ x : ℝ, 2 ≤ x → |mertensSum x - Real.log x| ≤ C)
    {f : ℝ → ℂ} (hdf : IntervalIntegrable (deriv f) volume 2 Y) :
    ‖∫ x in (2 : ℝ)..Y, deriv f x *
      ((mertensSum x : ℂ) - (Real.log x : ℂ))‖ ≤
        C * ∫ x in (2 : ℝ)..Y, ‖deriv f x‖ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun x : ℝ => deriv f x * ((mertensSum x : ℂ) - (Real.log x : ℂ)))
    (g := fun x : ℝ => C * ‖deriv f x‖) hY
    (Filter.Eventually.of_forall (fun x hx => by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hM x hx.1.le) (norm_nonneg _)).trans_eq
        (mul_comm _ _))) (hdf.norm.const_mul C)
  simpa only [intervalIntegral.integral_const_mul] using hb

/-- Finite partial summation with the endpoint beyond the support of the
weight. This derives the main integral from (51); it does not assume (52). -/
theorem weightedSum_integral_error {Y C H : ℝ} (hY : 2 ≤ Y)
    (hM : ∀ x : ℝ, 2 ≤ x → |mertensSum x - Real.log x| ≤ C)
    {f : ℝ → ℂ} (hf : ∀ x ∈ Set.Icc (2 : ℝ) Y, DifferentiableAt ℝ f x)
    (hdf : ContinuousOn (deriv f) (Set.Icc 2 Y))
    (hfY : f Y = 0) (hf2 : ‖f 2‖ ≤ H) :
    ‖weightedSum Y f - ∫ x in (2 : ℝ)..Y, f x * (x⁻¹ : ℝ)‖ ≤
      H * Real.log 2 + C * ∫ x in (2 : ℝ)..Y, ‖deriv f x‖ := by
  have hdfI : IntervalIntegrable (deriv f) volume 2 Y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hY).mpr hdf.integrableOn_Icc
  have hlog : ContinuousOn (fun x : ℝ => (Real.log x : ℂ)) (Set.Icc 2 Y) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))
  have hinv : ContinuousOn (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)) (Set.Icc 2 Y) := by
    exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.inv₀ (fun x hx => by change x ≠ 0; linarith [hx.1]))
  have hiA : IntervalIntegrable
      (fun x : ℝ => deriv f x * (mertensSum x : ℂ)) volume 2 Y := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hY).mpr
    have hi := integrableOn_mul_sum_Icc (fun n => (oddPrimeWeight n : ℂ))
      (m := 0) (by norm_num : (0 : ℝ) ≤ 2) hdf.integrableOn_Icc
    simpa only [cumulative_cast] using hi
  have hilog : IntervalIntegrable
      (fun x : ℝ => deriv f x * (Real.log x : ℂ)) volume 2 Y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hY).mpr (hdf.mul hlog).integrableOn_Icc
  have hsub : (∫ x in (2 : ℝ)..Y, deriv f x *
      ((mertensSum x : ℂ) - (Real.log x : ℂ))) =
      (∫ x in (2 : ℝ)..Y, deriv f x * (mertensSum x : ℂ)) -
        ∫ x in (2 : ℝ)..Y, deriv f x * (Real.log x : ℂ) := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub hiA hilog
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (2 : ℝ)) (b := Y) (u := f) (u' := deriv f) (v := fun x : ℝ => (Real.log x : ℂ))
    (v' := fun x : ℝ => ((x⁻¹ : ℝ) : ℂ))
    (fun x hx => (hf x (by simpa only [Set.uIcc_of_le hY] using hx)).hasDerivAt)
    (fun x hx => (Real.hasDerivAt_log
      (by have hx' : x ∈ Set.Icc (2 : ℝ) Y := by simpa only [Set.uIcc_of_le hY] using hx
          linarith [hx'.1])).ofReal_comp)
    hdfI ((intervalIntegrable_iff_integrableOn_Icc_of_le hY).mpr hinv.integrableOn_Icc)
  have hab := weightedSum_abel hY hf hdf.integrableOn_Icc
  have hid : weightedSum Y f - (∫ x in (2 : ℝ)..Y, f x * (x⁻¹ : ℝ)) =
      f 2 * (Real.log 2 : ℂ) -
        ∫ x in (2 : ℝ)..Y, deriv f x * ((mertensSum x : ℂ) - (Real.log x : ℂ)) := by
    rw [hab, hparts, hsub, hfY]
    ring
  rw [hid]
  calc
    _ ≤ ‖f 2 * (Real.log 2 : ℂ)‖ +
        ‖∫ x in (2 : ℝ)..Y, deriv f x *
          ((mertensSum x : ℂ) - (Real.log x : ℂ))‖ := norm_sub_le _ _
    _ ≤ H * Real.log 2 + C * ∫ x in (2 : ℝ)..Y, ‖deriv f x‖ := by
      apply add_le_add _ (mertens_error_integral_bound hY hM hdfI)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
      exact mul_le_mul_of_nonneg_right hf2 (Real.log_nonneg (by norm_num))

/-- The logarithmically rescaled test in equation (52). -/
noncomputable def logWeight (a : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℂ := h (a * Real.log x)

theorem hasDerivAt_logWeight (a : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logWeight a h) ((a * x⁻¹) • deriv h (a * Real.log x)) x := by
  exact ((hh.differentiable (by norm_num)).differentiableAt.hasDerivAt).scomp x
    ((Real.hasDerivAt_log hx).const_mul a)

theorem logWeight_differentiable {Y a : ℝ} {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) :
    ∀ x ∈ Set.Icc (2 : ℝ) Y, DifferentiableAt ℝ (logWeight a h) x := by
  intro x hx
  exact (hasDerivAt_logWeight a hh (by linarith [hx.1])).differentiableAt

theorem logWeight_continuous_deriv {Y a : ℝ} {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) :
    ContinuousOn (deriv (logWeight a h)) (Set.Icc 2 Y) := by
  have hc : ContinuousOn (fun x : ℝ =>
      (a * x⁻¹) • deriv h (a * Real.log x)) (Set.Icc 2 Y) :=
    (continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => by change x ≠ 0; linarith [hx.1]))).smul
      (hh.continuous_deriv_one.comp_continuousOn
        (continuousOn_const.mul (continuousOn_id.log (fun x hx => by change x ≠ 0; linarith [hx.1]))))
  apply hc.congr
  intro x hx
  exact (hasDerivAt_logWeight a hh (by linarith [hx.1])).deriv

/-- Logarithmic substitution for the main integral. -/
theorem logWeight_integral {Y a : ℝ} (hY : 2 ≤ Y) {h : ℝ → ℂ} (hh : Continuous h) :
    a • (∫ x in (2 : ℝ)..Y, logWeight a h x * (x⁻¹ : ℝ)) =
      ∫ u in a * Real.log 2..a * Real.log Y, h u := by
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := (2 : ℝ)) (b := Y) (f := fun x : ℝ => a * Real.log x) (f' := fun x : ℝ => a * x⁻¹)
    (fun x hx => (Real.hasDerivAt_log
      (by have hx' : x ∈ Set.Icc (2 : ℝ) Y := by simpa only [Set.uIcc_of_le hY] using hx
          linarith [hx'.1])).const_mul a)
    (by
      rw [Set.uIcc_of_le hY]
      exact continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => by change x ≠ 0; linarith [hx.1]))) hh
  rw [← intervalIntegral.integral_smul]
  convert hsub using 1
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [logWeight, Function.comp_apply, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- Change of variables also controls the total variation, with its exact
Jacobian. -/
theorem logWeight_variation {Y a : ℝ} (hY : 2 ≤ Y) (ha : 0 ≤ a)
    {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) :
    (∫ x in (2 : ℝ)..Y, ‖deriv (logWeight a h) x‖) =
      ∫ u in a * Real.log 2..a * Real.log Y, ‖deriv h u‖ := by
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (a := (2 : ℝ)) (b := Y) (f := fun x : ℝ => a * Real.log x) (f' := fun x : ℝ => a * x⁻¹)
    (fun x hx => (Real.hasDerivAt_log
      (by have hx' : x ∈ Set.Icc (2 : ℝ) Y := by simpa only [Set.uIcc_of_le hY] using hx
          linarith [hx'.1])).const_mul a)
    (by
      rw [Set.uIcc_of_le hY]
      exact continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => by change x ≠ 0; linarith [hx.1])))
    hh.continuous_deriv_one.norm
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Set.Icc (2 : ℝ) Y := by simpa only [Set.uIcc_of_le hY] using hx
  have hx0 : 0 < x := by linarith [hx'.1]
  change ‖deriv (logWeight a h) x‖ = (a * x⁻¹) * ‖deriv h (a * Real.log x)‖
  rw [(hasDerivAt_logWeight a hh hx0.ne').deriv, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ha (inv_nonneg.mpr hx0.le))]

/-- The positive half-line can be truncated once the compactly supported
test vanishes past the endpoint. -/
theorem positive_integral_truncate {U : ℝ} (hU : 0 ≤ U) {h : ℝ → ℂ}
    (htail : ∀ u : ℝ, U ≤ u → h u = 0) :
    (∫ u in Set.Ioi 0, h u) = ∫ u in (0 : ℝ)..U, h u := by
  rw [intervalIntegral.integral_of_le hU]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun _ hx => hx.1)
  intro u hu
  apply htail u
  have hu0 : 0 < u := hu.1
  have hun : ¬ (0 < u ∧ u ≤ U) := hu.2
  by_contra hbad
  exact hun ⟨hu0, le_of_lt (lt_of_not_ge hbad)⟩

/-- Equation (52) with the sharper explicit error before enlarging its
constant. All summation and changes of variables are proved for the actual
odd-prime coefficient sequence. -/
theorem scaled_mertens_error {Y a C H : ℝ}
    (hY : 2 ≤ Y) (ha : 0 < a) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |mertensSum x - Real.log x| ≤ C)
    {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hhd : Integrable (deriv h))
    (hH : ∀ u : ℝ, ‖h u‖ ≤ H)
    (htail : ∀ u : ℝ, a * Real.log Y ≤ u → h u = 0) :
    ‖a • weightedSum Y (logWeight a h) - (∫ u in Set.Ioi 0, h u)‖ ≤
      a * (2 * H * Real.log 2 + C * ∫ u : ℝ, ‖deriv h u‖) := by
  have hl : 0 ≤ a * Real.log 2 := mul_nonneg ha.le (Real.log_nonneg (by norm_num))
  have hlu : a * Real.log 2 ≤ a * Real.log Y :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hY) ha.le
  have hU : 0 ≤ a * Real.log Y := hl.trans hlu
  have he := weightedSum_integral_error hY hM (logWeight_differentiable hh)
    (logWeight_continuous_deriv hh) (htail _ le_rfl) (hH _)
  have hv : (∫ x in (2 : ℝ)..Y, ‖deriv (logWeight a h) x‖) ≤
      ∫ u : ℝ, ‖deriv h u‖ := by
    rw [logWeight_variation hY ha.le hh, intervalIntegral.integral_of_le hlu]
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun u => norm_nonneg (deriv h u))) hhd.norm
  have hmain := logWeight_integral (a := a) hY hh.continuous
  have hfull := positive_integral_truncate hU htail
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hh.continuous.intervalIntegrable (μ := volume) (a := 0) (b := a * Real.log 2))
    (hh.continuous.intervalIntegrable (μ := volume) (a := a * Real.log 2) (b := a * Real.log Y))
  have hid : a • weightedSum Y (logWeight a h) - (∫ u in Set.Ioi 0, h u) =
      a • (weightedSum Y (logWeight a h) -
        (∫ x in (2 : ℝ)..Y, logWeight a h x * (x⁻¹ : ℝ))) -
        ∫ u in (0 : ℝ)..a * Real.log 2, h u := by
    rw [smul_sub, hmain, hfull, ← hsplit]
    abel
  have hstart : ‖∫ u in (0 : ℝ)..a * Real.log 2, h u‖ ≤ H * (a * Real.log 2) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (fun u _ => hH u)
      (a := (0 : ℝ)) (b := a * Real.log 2)
    simpa only [sub_zero, abs_of_nonneg hl] using hb
  rw [hid]
  calc
    _ ≤ ‖a • (weightedSum Y (logWeight a h) -
        (∫ x in (2 : ℝ)..Y, logWeight a h x * (x⁻¹ : ℝ)))‖ +
        ‖∫ u in (0 : ℝ)..a * Real.log 2, h u‖ := norm_sub_le _ _
    _ ≤ a * (H * Real.log 2 + C * ∫ u : ℝ, ‖deriv h u‖) + H * (a * Real.log 2) := by
      apply add_le_add _ hstart
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      apply mul_le_mul_of_nonneg_left _ ha.le
      exact he.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hC))
    _ = _ := by ring

/-- The paper's `1/L` error, with a concrete admissible `C'_M`. -/
theorem mertens_error_over_L {Y L C H : ℝ}
    (hY : 2 ≤ Y) (hL : 0 < L) (hC : 0 ≤ C) (hH0 : 0 ≤ H)
    (hM : ∀ x : ℝ, 2 ≤ x → |mertensSum x - Real.log x| ≤ C)
    {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hhd : Integrable (deriv h))
    (hH : ∀ u : ℝ, ‖h u‖ ≤ H)
    (htail : ∀ u : ℝ, (2 / L) * Real.log Y ≤ u → h u = 0) :
    ‖(2 / L : ℝ) • weightedSum Y (logWeight (2 / L) h) -
      (∫ u in Set.Ioi 0, h u)‖ ≤
      (4 * Real.log 2 + 2 * C) * (H + ∫ u : ℝ, ‖deriv h u‖) / L := by
  have he := scaled_mertens_error hY (by positivity : (0 : ℝ) < 2 / L) hC hM hh hhd hH htail
  have hV : 0 ≤ ∫ u : ℝ, ‖deriv h u‖ := integral_nonneg (fun u => norm_nonneg _)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  apply he.trans
  apply (le_div_iff₀ hL).mpr
  have hcancel : (2 / L * (2 * H * Real.log 2 + C * ∫ u : ℝ, ‖deriv h u‖)) * L =
      2 * (2 * H * Real.log 2 + C * ∫ u : ℝ, ‖deriv h u‖) := by field_simp [hL.ne']
  rw [hcancel]
  nlinarith [mul_nonneg hC hH0, mul_nonneg hlog2 hV]

/-- The bounded factor and derivative integral in (52) are the actual
supremum norm and derivative L¹ norm of a Schwartz test. -/
theorem schwartz_mertens_error {Y L C : ℝ}
    (hY : 2 ≤ Y) (hL : 0 < L) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |mertensSum x - Real.log x| ≤ C)
    (h : 𝓢(ℝ, ℂ))
    (htail : ∀ u : ℝ, (2 / L) * Real.log Y ≤ u → h u = 0) :
    ‖(2 / L : ℝ) • weightedSum Y (logWeight (2 / L) h) -
      (∫ u in Set.Ioi 0, h u)‖ ≤
      (4 * Real.log 2 + 2 * C) *
        (‖h.toBoundedContinuousFunction‖ + ∫ u : ℝ, ‖deriv h u‖) / L := by
  apply mertens_error_over_L hY hL hC (norm_nonneg _) hM (h.smooth 1)
  · have hd : (fun x : ℝ => SchwartzMap.derivCLM ℝ ℂ h x) = deriv h := by
      funext x
      rfl
    rw [← hd]
    exact (SchwartzMap.derivCLM ℝ ℂ h).integrable
  · intro u
    exact h.toBoundedContinuousFunction.norm_coe_le_norm u
  · exact htail

/-- The sum over all integer indices is the actual odd-prime sum, since the
coefficient is zero elsewhere. Compact support makes this sum finite. -/
noncomputable def weightedTotal (a : ℝ) (h : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, logWeight a h n * (oddPrimeWeight n : ℂ)

theorem weightedTotal_eq_finite {Y a : ℝ} (hY : 2 ≤ Y) (ha : 0 ≤ a)
    {h : ℝ → ℂ} (htail : ∀ u : ℝ, a * Real.log Y ≤ u → h u = 0) :
    weightedTotal a h = weightedSum Y (logWeight a h) := by
  unfold weightedTotal weightedSum
  apply tsum_eq_sum
  intro n hn
  have hnf : ⌊Y⌋₊ < n := by
    have hn' : ¬ (0 ≤ n ∧ n ≤ ⌊Y⌋₊) := by simpa only [Finset.mem_Icc] using hn
    omega
  have hn0 : n ≠ 0 := by omega
  have hnY : Y < (n : ℝ) := (Nat.floor_lt' hn0).mp hnf
  have hY0 : 0 < Y := by linarith
  have hz : logWeight a h n = 0 := by
    apply htail
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hY0 hnY.le) ha
  rw [hz, zero_mul]

/-- A cutoff beyond any fixed compact support always exists. -/
theorem exists_logarithmic_cutoff {a : ℝ} (ha : 0 < a) (s : ℝ) :
    ∃ Y : ℝ, 2 ≤ Y ∧ s < a * Real.log Y := by
  refine ⟨Real.exp (max (Real.log 2) (s / a) + 1), ?_, ?_⟩
  · calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
      _ ≤ Real.exp (max (Real.log 2) (s / a) + 1) :=
        Real.exp_le_exp.mpr (by linarith [le_max_left (Real.log 2) (s / a)])
  · rw [Real.log_exp]
    have hh : s / a < max (Real.log 2) (s / a) + 1 := by
      linarith [le_max_right (Real.log 2) (s / a)]
    simpa only [mul_comm] using (div_lt_iff₀ ha).mp hh

/-- Equation (52) for the complete actual odd-prime sum and a compactly
supported Schwartz test, without a cutoff hypothesis in the conclusion. -/
theorem schwartz_mertens_total_error {L C s : ℝ}
    (hL : 0 < L) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |mertensSum x - Real.log x| ≤ C)
    (h : 𝓢(ℝ, ℂ)) (hsupport : Function.support h ⊆ Set.Icc (-s) s) :
    ‖(2 / L : ℝ) • weightedTotal (2 / L) h - (∫ u in Set.Ioi 0, h u)‖ ≤
      (4 * Real.log 2 + 2 * C) *
        (‖h.toBoundedContinuousFunction‖ + ∫ u : ℝ, ‖deriv h u‖) / L := by
  have ha : 0 < (2 / L : ℝ) := by positivity
  obtain ⟨Y, hY, hcut⟩ := exists_logarithmic_cutoff ha s
  have htail : ∀ u : ℝ, (2 / L) * Real.log Y ≤ u → h u = 0 := by
    intro u hu
    by_contra hne
    have hs := hsupport hne
    linarith [hs.2]
  rw [weightedTotal_eq_finite hY ha.le htail]
  exact schwartz_mertens_error hY hL hC hM h htail

end DepthAspect.MertensWeights
