import DepthAspect.DigammaBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Tactic.Abel

/-!
The actual real part of the digamma factor in the archimedean integral is
integrable against any complex test function whose first moment is integrable.
The cited DLMF series identity is the sole special-function interface.
-/

open MeasureTheory

namespace DepthAspect.ArchimedeanBound

open DigammaBound

/-- Continuity of the actual digamma along the vertical line follows from the
proved series Lipschitz estimate, rather than being an extra analytic premise. -/
theorem digamma_vertical_lipschitz (hDLMF : DLMFSeriesIdentity)
    (a : ℝ) (ha : 1 ≤ a) :
    LipschitzWith 2 (fun t : ℝ => Complex.digamma ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  have hz : 1 ≤ ((a : ℂ) + (x : ℂ) * Complex.I).re := by simpa using ha
  have hw : 1 ≤ ((a : ℂ) + (y : ℂ) * Complex.I).re := by simpa using ha
  rw [hDLMF _ hz, hDLMF _ hw]
  have h := seriesDigamma_norm_sub_le hz hw
  have heq : ((a : ℂ) + (x : ℂ) * Complex.I) -
      ((a : ℂ) + (y : ℂ) * Complex.I) = ((x - y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simpa only [heq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one] using h

noncomputable def harmonicConstant (a : ℕ) : ℝ :=
  |(harmonic (a - 1) : ℝ) - Real.eulerMascheroniConstant|

/-- The exact bound on the Gamma factor used in (59). -/
theorem digamma_re_bound (hDLMF : DLMFSeriesIdentity) (a : ℕ) (ha : 1 ≤ a)
    (s x : ℝ) (hs : 0 ≤ s) :
    |(Complex.digamma ((a : ℂ) + ((s * x : ℝ) : ℂ) * Complex.I)).re| ≤
      harmonicConstant a + 2 * s * |x| := by
  have hdiff := digamma_vertical_bound_of_dlmf hDLMF (a : ℝ) (s * x)
    (by exact_mod_cast ha)
  have hnorm := norm_le_norm_sub_add
    (Complex.digamma ((a : ℂ) + ((s * x : ℝ) : ℂ) * Complex.I))
    (Complex.digamma (a : ℂ))
  have hvalue : ‖Complex.digamma (a : ℂ)‖ = harmonicConstant a := by
    rw [digamma_positive_integer a ha]
    unfold harmonicConstant
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hr := Complex.abs_re_le_norm
    (Complex.digamma ((a : ℂ) + ((s * x : ℝ) : ℂ) * Complex.I))
  simp only [Complex.ofReal_natCast, abs_mul, abs_of_nonneg hs] at hdiff
  rw [hvalue] at hnorm
  linarith

noncomputable def gammaIntegrand (a : ℕ) (s : ℝ) (φ : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Complex.digamma ((a : ℂ) + ((s * x : ℝ) : ℂ) * Complex.I)).re • φ x

theorem gammaIntegrand_norm_bound (hDLMF : DLMFSeriesIdentity)
    (a : ℕ) (ha : 1 ≤ a) (s : ℝ) (hs : 0 ≤ s) (φ : ℝ → ℂ) (x : ℝ) :
    ‖gammaIntegrand a s φ x‖ ≤ harmonicConstant a * ‖φ x‖ +
      (2 * s) * ‖x • φ x‖ := by
  unfold gammaIntegrand
  rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (digamma_re_bound hDLMF a ha s x hs) (norm_nonneg (φ x))
  nlinarith

theorem gammaIntegrand_integrable (hDLMF : DLMFSeriesIdentity)
    (a : ℕ) (ha : 1 ≤ a) (s : ℝ) (hs : 0 ≤ s) (φ : ℝ → ℂ)
    (hφ : Integrable φ) (hxφ : Integrable (fun x : ℝ => x • φ x)) :
    Integrable (gammaIntegrand a s φ) := by
  have hc : Continuous (fun x : ℝ =>
      (Complex.digamma ((a : ℂ) + ((s * x : ℝ) : ℂ) * Complex.I)).re) := by
    have hv : Continuous (fun t : ℝ =>
        Complex.digamma ((a : ℂ) + (t : ℂ) * Complex.I)) := by
      convert! (digamma_vertical_lipschitz hDLMF (a : ℝ)
        (by exact_mod_cast ha)).continuous using 1
    exact Complex.continuous_re.comp (hv.comp (continuous_const.mul continuous_id))
  exact ((hφ.norm.const_mul (harmonicConstant a)).add
    (hxφ.norm.const_mul (2 * s))).mono'
    (hc.aestronglyMeasurable.smul hφ.aestronglyMeasurable)
    (Filter.Eventually.of_forall (gammaIntegrand_norm_bound hDLMF a ha s hs φ))

/-- The actual integral occurring in (59), with no assumed bound on that integral. -/
theorem gammaIntegral_bound (hDLMF : DLMFSeriesIdentity)
    (a : ℕ) (ha : 1 ≤ a) (s : ℝ) (hs : 0 ≤ s) (φ : ℝ → ℂ)
    (hφ : Integrable φ) (hxφ : Integrable (fun x : ℝ => x • φ x)) :
    ‖∫ x : ℝ, gammaIntegrand a s φ x‖ ≤
      harmonicConstant a * (∫ x : ℝ, ‖φ x‖) +
        (2 * s) * (∫ x : ℝ, ‖x • φ x‖) := by
  have h := norm_integral_le_of_norm_le
    ((hφ.norm.const_mul (harmonicConstant a)).add (hxφ.norm.const_mul (2 * s)))
    (Filter.Eventually.of_forall (gammaIntegrand_norm_bound hDLMF a ha s hs φ))
  simpa only [Pi.add_apply, integral_add (hφ.norm.const_mul _) (hxφ.norm.const_mul _), integral_const_mul]
    using h

/-- The conductor logarithm is simplified exactly before taking its norm. -/
theorem conductor_log_difference (N k : ℝ) (hN : 0 < N) (hk : 0 < k) :
    Real.log (N / (4 * Real.pi ^ 2)) - Real.log (k ^ 2 * N) =
      -Real.log (4 * Real.pi ^ 2 * k ^ 2) := by
  have hden : (4 : ℝ) * Real.pi ^ 2 ≠ 0 := by positivity
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hk)
  rw [Real.log_div (ne_of_gt hN) hden, Real.log_mul hk2 (ne_of_gt hN),
    Real.log_mul hden hk2]
  ring

theorem conductor_log_nonneg (k : ℝ) (hk : 1 ≤ k) :
    0 ≤ Real.log (4 * Real.pi ^ 2 * k ^ 2) := by
  apply Real.log_nonneg
  have hk2 : 1 ≤ k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
  have hpi2 : 1 ≤ 4 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  exact hpi2.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hk2 (by positivity : 0 ≤ 4 * Real.pi ^ 2))

noncomputable def archimedeanTerm (N k : ℝ) (a : ℕ) (φ : ℝ → ℂ) (h0 : ℂ) : ℂ :=
  (Real.log (N / (4 * Real.pi ^ 2)) / Real.log (k ^ 2 * N)) • h0 +
    (2 / Real.log (k ^ 2 * N)) •
      ∫ x : ℝ, gammaIntegrand a (2 * Real.pi / Real.log (k ^ 2 * N)) φ x

/-- The explicit inequality (59). Setting `k = 2*a` gives the paper's weight
parameter. The integral is the actual digamma integral, with its integrability
proved above from the two stated test-function integrability properties. -/
theorem archimedean_remainder_bound (hDLMF : DLMFSeriesIdentity)
    (N k : ℝ) (hN : 0 < N) (hk : 1 ≤ k) (hL : 0 < Real.log (k ^ 2 * N))
    (a : ℕ) (ha : 1 ≤ a) (φ : ℝ → ℂ) (h0 : ℂ)
    (hφ : Integrable φ) (hxφ : Integrable (fun x : ℝ => x • φ x)) :
    ‖archimedeanTerm N k a φ h0 - h0‖ ≤
      (Real.log (4 * Real.pi ^ 2 * k ^ 2) * ‖h0‖ +
        2 * harmonicConstant a * (∫ x : ℝ, ‖φ x‖)) / Real.log (k ^ 2 * N) +
      (8 * Real.pi / Real.log (k ^ 2 * N) ^ 2) * (∫ x : ℝ, ‖x • φ x‖) := by
  let L := Real.log (k ^ 2 * N)
  have hL' : 0 < L := hL
  have hcoef : Real.log (N / (4 * Real.pi ^ 2)) / L - 1 =
      -Real.log (4 * Real.pi ^ 2 * k ^ 2) / L := by
    rw [div_sub_one (ne_of_gt hL')]
    congr 1
    exact conductor_log_difference N k hN (by linarith)
  have hnormcoef : |Real.log (N / (4 * Real.pi ^ 2)) / L - 1| =
      Real.log (4 * Real.pi ^ 2 * k ^ 2) / L := by
    rw [hcoef, abs_div, abs_neg, abs_of_nonneg (conductor_log_nonneg k hk), abs_of_pos hL']
  have hdecomp : archimedeanTerm N k a φ h0 - h0 =
      (Real.log (N / (4 * Real.pi ^ 2)) / L - 1) • h0 +
      (2 / L) • (∫ x : ℝ, gammaIntegrand a (2 * Real.pi / L) φ x) := by
    unfold archimedeanTerm
    rw [sub_smul, one_smul]
    dsimp only [L]
    abel
  rw [hdecomp]
  have hs : 0 ≤ 2 * Real.pi / L := by positivity
  have hgamma := gammaIntegral_bound hDLMF a ha (2 * Real.pi / L) hs φ hφ hxφ
  calc
    _ ≤ ‖(Real.log (N / (4 * Real.pi ^ 2)) / L - 1) • h0‖ +
        ‖(2 / L) • (∫ x : ℝ, gammaIntegrand a (2 * Real.pi / L) φ x)‖ := norm_add_le _ _
    _ = (Real.log (4 * Real.pi ^ 2 * k ^ 2) / L) * ‖h0‖ +
        (2 / L) * ‖∫ x : ℝ, gammaIntegrand a (2 * Real.pi / L) φ x‖ := by
      rw [norm_smul, Real.norm_eq_abs, hnormcoef, norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos (by norm_num) hL')]
    _ ≤ (Real.log (4 * Real.pi ^ 2 * k ^ 2) / L) * ‖h0‖ +
        (2 / L) * (harmonicConstant a * (∫ x : ℝ, ‖φ x‖) +
          (2 * (2 * Real.pi / L)) * (∫ x : ℝ, ‖x • φ x‖)) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left hgamma (show (0 : ℝ) ≤ 2 / L by positivity)
    _ = _ := by dsimp [L]; ring

/-- For the paper's even weight `k = 2*a` and `N ≥ 1`, positivity of the
conductor logarithm is itself a consequence, not an extra hypothesis. -/
theorem even_weight_remainder_bound (hDLMF : DLMFSeriesIdentity)
    (N : ℝ) (hN : 1 ≤ N) (a : ℕ) (ha : 1 ≤ a) (φ : ℝ → ℂ) (h0 : ℂ)
    (hφ : Integrable φ) (hxφ : Integrable (fun x : ℝ => x • φ x)) :
    ‖archimedeanTerm N (2 * a) a φ h0 - h0‖ ≤
      (Real.log (4 * Real.pi ^ 2 * (2 * a) ^ 2) * ‖h0‖ +
        2 * harmonicConstant a * (∫ x : ℝ, ‖φ x‖)) / Real.log ((2 * a) ^ 2 * N) +
      (8 * Real.pi / Real.log ((2 * a) ^ 2 * N) ^ 2) * (∫ x : ℝ, ‖x • φ x‖) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hk : (1 : ℝ) ≤ 2 * a := by linarith
  have hk2 : (4 : ℝ) ≤ (2 * a) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - 1)]
  have hprod : (2 * (a : ℝ)) ^ 2 ≤ (2 * a) ^ 2 * N := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hN (sq_nonneg (2 * (a : ℝ)))
  have hL : 0 < Real.log ((2 * (a : ℝ)) ^ 2 * N) := Real.log_pos (by linarith)
  exact archimedean_remainder_bound hDLMF N (2 * a) (by linarith) hk hL a ha φ h0 hφ hxφ

/-- The first absolute moment required above is proved for an actual Schwartz
map. No decay or integrability estimate is added to the paper's test class. -/
theorem schwartz_first_moment_integrable (φ : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => x • φ x) := by
  have hnorm : Integrable (fun x : ℝ => ‖x‖ * ‖φ x‖) := by
    simpa only [pow_one] using φ.integrable_pow_mul volume 1
  exact hnorm.mono' (continuous_id.smul φ.continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simp only [norm_smul, le_refl]))

/-- Equation (59) directly for the actual Schwartz test class of the paper. -/
theorem schwartz_even_weight_remainder_bound (hDLMF : DLMFSeriesIdentity)
    (N : ℝ) (hN : 1 ≤ N) (a : ℕ) (ha : 1 ≤ a) (φ : SchwartzMap ℝ ℂ) (h0 : ℂ) :
    ‖archimedeanTerm N (2 * a) a φ h0 - h0‖ ≤
      (Real.log (4 * Real.pi ^ 2 * (2 * a) ^ 2) * ‖h0‖ +
        2 * harmonicConstant a * (∫ x : ℝ, ‖φ x‖)) / Real.log ((2 * a) ^ 2 * N) +
      (8 * Real.pi / Real.log ((2 * a) ^ 2 * N) ^ 2) * (∫ x : ℝ, ‖x • φ x‖) :=
  even_weight_remainder_bound hDLMF N hN a ha φ h0 φ.integrable
    (schwartz_first_moment_integrable φ)

end DepthAspect.ArchimedeanBound
