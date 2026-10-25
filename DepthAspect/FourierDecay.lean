import DepthAspect.EntireExtension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.Positivity

/-!
# The explicit decay bound in Lemma 4.5

The constants below use the actual L¹ integrals of the Fourier transform and
its derivatives. The estimate is obtained from the integral identities in
`EntireExtension`, and Fourier inversion identifies the real-axis values.
-/

open MeasureTheory Set
open scoped Topology FourierTransform ContDiff SchwartzMap

namespace DepthAspect.EntireExtension

/-- Entire functions agreeing on the real axis agree on the whole plane. -/
theorem entire_unique {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hreal : ∀ x : ℝ, f x = g x) : f = g := by
  have hc : (0 : ℂ) ∈ closure ({z | f z = g z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨hreal _, ?_⟩, ?_⟩
    · simpa only [mem_singleton_iff, Complex.ofReal_eq_zero] using
        (ne_of_gt (by linarith : (0 : ℝ) < ε / 2))
    · simpa [dist_eq_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hε] using
        (show ε / 2 < ε by linarith)
  have he := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure
    (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z)
    isPreconnected_univ (mem_univ (0 : ℂ)) hc
  exact funext fun z => he (mem_univ z)


noncomputable def l1Integral (h : ℝ → ℂ) : ℝ := ∫ t, ‖h t‖

noncomputable def decayConstant (h : ℝ → ℂ) (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J * max (l1Integral h)
    (l1Integral (iteratedDeriv J h) / (2 * Real.pi) ^ J)

theorem norm_twoPiI : ‖twoPiI‖ = 2 * Real.pi := by
  simp [twoPiI, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- Compact support identifies the interval norm integral with the global
L¹ integral, including the two endpoints. -/
theorem interval_norm_eq_l1 {s : ℝ} {h : ℝ → ℂ} (hh : Continuous h)
    (hsupp : Function.support h ⊆ Icc (-s) s) :
    (∫ t in -s..s, ‖h t‖) = l1Integral h := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hn : h t ≠ 0 := fun hz => ht (by simp [hz])
  have hi : Function.support h ⊆ Ioo (-s) s := by
    simpa only [interior_Icc] using hh.isOpen_support.subset_interior_iff.mpr hsupp
  exact ⟨(hi hn).1, (hi hn).2.le⟩

/-- Every derivative used in the decay constant is genuinely integrable. -/
theorem iteratedDeriv_integrable {s : ℝ} {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : Function.support h ⊆ Icc (-s) s) (J : ℕ) :
    Integrable (iteratedDeriv J h) := by
  have hc : HasCompactSupport (iteratedDeriv J h) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport (iteratedDeriv J h)) (iteratedDeriv_support hsupp J)
  exact (hh.continuous_iteratedDeriv J (ENat.natCast_le_of_coe_top_le_withTop le_rfl J)).integrable_of_hasCompactSupport hc

/-- The direct and integration-by-parts estimates combine with exactly the
factor 2^J appearing in (54). -/
theorem combine_decay_bounds {A B C E r : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hr : 0 ≤ r) (J : ℕ) (hzero : A ≤ B * E) (hhigh : r ^ J * A ≤ C * E) :
    A ≤ (2 : ℝ) ^ J * max B C * E / (1 + r) ^ J := by
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1 + r) J)).mpr
  rw [mul_comm A]
  by_cases hr1 : r ≤ 1
  · calc
      (1 + r) ^ J * A ≤ (2 : ℝ) ^ J * A :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) J) hA
      _ ≤ (2 : ℝ) ^ J * (B * E) := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ (2 : ℝ) ^ J * (max B C * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left B C) hE)
          (by positivity)
      _ = _ := by ring
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    calc
      (1 + r) ^ J * A ≤ (2 * r) ^ J * A :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) J) hA
      _ = (2 : ℝ) ^ J * (r ^ J * A) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ J * (C * E) := mul_le_mul_of_nonneg_left hhigh (by positivity)
      _ ≤ (2 : ℝ) ^ J * (max B C * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_right B C) hE)
          (by positivity)
      _ = _ := by ring

/-- Equation (54), expressed with division by (1+‖z‖)^J. No decay estimate
is assumed: the derivative factor comes from repeated integration by parts. -/
theorem norm_extension_decay {s : ℝ} (hs : 0 ≤ s) {h : ℝ → ℂ}
    (hh : ContDiff ℝ ∞ h) (hsupp : Function.support h ⊆ Icc (-s) s)
    (J : ℕ) (z : ℂ) :
    ‖extension s h z‖ ≤ decayConstant h J *
      Real.exp (2 * Real.pi * s * |z.im|) / (1 + ‖z‖) ^ J := by
  have hj : Continuous (iteratedDeriv J h) := hh.continuous_iteratedDeriv J (ENat.natCast_le_of_coe_top_le_withTop le_rfl J)
  have hjs : Function.support (iteratedDeriv J h) ⊆ Icc (-s) s :=
    (subset_tsupport (iteratedDeriv J h)).trans (iteratedDeriv_support hsupp J)
  have hzero := norm_extension_le hs hh.continuous z
  rw [interval_norm_eq_l1 hh.continuous hsupp] at hzero
  have hhigh := norm_extension_le hs hj z
  rw [interval_norm_eq_l1 hj hjs] at hhigh
  have hid := congrArg norm (extension_iteratedDeriv hh hsupp J z)
  simp only [norm_mul, norm_pow, norm_neg, norm_twoPiI] at hid
  have hweighted : ‖z‖ ^ J * ‖extension s h z‖ ≤
      (l1Integral (iteratedDeriv J h) / (2 * Real.pi) ^ J) *
        Real.exp (2 * Real.pi * s * |z.im|) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 2 * Real.pi) J)).mpr
    calc
      ‖z‖ ^ J * ‖extension s h z‖ * (2 * Real.pi) ^ J =
          ‖extension s (iteratedDeriv J h) z‖ := by rw [hid, mul_pow]; ring
      _ ≤ _ := hhigh
  exact combine_decay_bounds (norm_nonneg _) (Real.exp_pos _).le (norm_nonneg _) J hzero hweighted

/-- The compact Fourier–Laplace integral restricts to the inverse Fourier
transform with mathlib's 2π normalization. -/
theorem extension_eq_fourierInv {s : ℝ} {h : ℝ → ℂ} (hh : Continuous h)
    (hsupp : Function.support h ⊆ Icc (-s) s) (x : ℝ) :
    extension s h x = 𝓕⁻ h x := by
  unfold extension
  rw [intervalIntegral.integral_eq_integral_of_support_subset, Real.fourierInv_eq']
  · apply integral_congr_ae
    filter_upwards [] with t
    rw [smul_eq_mul, mul_comm (h t)]
    congr 1
    unfold kernel twoPiI
    congr 1
    simp only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  · intro t ht
    have hn : h t ≠ 0 := fun hz => ht (by simp [hz])
    have hi : Function.support h ⊆ Ioo (-s) s := by
      simpa only [interior_Icc] using hh.isOpen_support.subset_interior_iff.mpr hsupp
    exact ⟨(hi hn).1, (hi hn).2.le⟩

/-- Fourier inversion proves that (53) really extends the original Schwartz
function, rather than merely defining a separate entire function. -/
theorem schwartz_extension_on_real {s : ℝ} (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) (x : ℝ) :
    extension s (𝓕 φ : 𝓢(ℝ, ℂ)) x = φ x := by
  rw [extension_eq_fourierInv (𝓕 φ).continuous hsupp, ← SchwartzMap.fourierInv_coe]
  exact congrArg (fun f : 𝓢(ℝ, ℂ) => f x) (FourierTransform.fourierInv_fourier_eq φ)

/-- Existence and uniqueness of the entire extension asserted in Lemma 4.5. -/
theorem schwartz_entire_extension_unique {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    ∃! F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = φ x := by
  refine ⟨extension s (𝓕 φ : 𝓢(ℝ, ℂ)),
    ⟨extension_entire hs (𝓕 φ).continuous, schwartz_extension_on_real φ hsupp⟩, ?_⟩
  intro F hF
  exact entire_unique hF.1 (extension_entire hs (𝓕 φ).continuous)
    (fun x => (hF.2 x).trans (schwartz_extension_on_real φ hsupp x).symm)

/-- Lemma 4.5's quantitative estimate for the original Schwartz test function. -/
theorem schwartz_extension_decay {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s)
    (J : ℕ) (z : ℂ) :
    ‖extension s (𝓕 φ : 𝓢(ℝ, ℂ)) z‖ ≤ decayConstant (𝓕 φ : 𝓢(ℝ, ℂ)) J *
      Real.exp (2 * Real.pi * s * |z.im|) / (1 + ‖z‖) ^ J :=
  norm_extension_decay hs ((𝓕 φ).smooth ⊤) hsupp J z

/-- The Fourier transform at zero is the actual integral of the test. -/
theorem schwartz_fourier_zero (φ : 𝓢(ℝ, ℂ)) :
    (𝓕 φ : 𝓢(ℝ, ℂ)) 0 = ∫ x, φ x := by
  change 𝓕 (φ : ℝ → ℂ) 0 = _
  rw [Real.fourier_eq']
  simp

/-- Inversion at zero gives the integral identity used for density main terms. -/
theorem schwartz_integral_fourier (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 φ : 𝓢(ℝ, ℂ)) x) = φ 0 := by
  have hi : (𝓕⁻ (𝓕 φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) 0 = φ 0 :=
    congrArg (fun f : 𝓢(ℝ, ℂ) => f 0)
    (FourierTransform.fourierInv_fourier_eq φ)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hi
  simpa using hi

/-- Evenness is preserved by the actual Fourier transform. -/
theorem schwartz_fourier_even (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ) :
    Function.Even (𝓕 φ : 𝓢(ℝ, ℂ)) := by
  intro x
  change 𝓕 (φ : ℝ → ℂ) (-x) = 𝓕 (φ : ℝ → ℂ) x
  rw [← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_comp_neg]
  have hn : (fun y : ℝ => φ (-y)) = (φ : ℝ → ℂ) := funext heven
  rw [hn]

/-- An even integrable complex test has half of its integral on each half-line. -/
theorem even_integral_positive_half {h : ℝ → ℂ} (hint : Integrable h)
    (heven : Function.Even h) : (∫ x in Ioi 0, h x) = (∫ x, h x) / 2 := by
  have hleft : (∫ x in Iic 0, h x) = ∫ x in Ioi 0, h x := by
    calc
      _ = ∫ x in Iic 0, h (-x) :=
        setIntegral_congr_fun measurableSet_Iic (fun x _ => (heven x).symm)
      _ = _ := by simpa using integral_comp_neg_Iic 0 h
  have hs := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint
  rw [compl_Ioi, hleft] at hs
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
  simpa only [mul_two] using hs

/-- The main-term identity immediately following (52), for the actual even
Schwartz function and its actual Fourier transform. -/
theorem schwartz_positive_fourier_integral (φ : 𝓢(ℝ, ℂ))
    (heven : Function.Even φ) :
    (∫ x in Ioi 0, (𝓕 φ : 𝓢(ℝ, ℂ)) x) = φ 0 / 2 := by
  rw [even_integral_positive_half (𝓕 φ).integrable (schwartz_fourier_even φ heven),
    schwartz_integral_fourier]

end DepthAspect.EntireExtension
