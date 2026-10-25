import DepthAspect.UnsignedZeroConvergence
import DepthAspect.RandomMatrixMainTerms

/-! The unsigned theorem with its actual orthogonal integral functional.
This wrapper also records the limit of the convergent zero averages. -/
open Filter
open scoped FourierTransform SchwartzMap
namespace DepthAspect.UnsignedDensity

/-- Theorem 1.1 with the orthogonal main term written as its actual
Lebesgue integral and the mass at the origin. -/
theorem unsigned_orthogonal_error {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) (ha : 1 ≤ a)
    (Z : AnalyticSpectralData D a) (hDLMF : DigammaBound.DLMFSeriesIdentity)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(3 / 2 : ℝ)) (3 / 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 8 ≤ n →
      ‖meanDensity (3 / 2) (Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n)) φ
        (Z.zeroOrdinate n) - RandomMatrixMainTerms.orthogonal φ‖ ≤
        K / Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n) := by
  simpa only [RandomMatrixMainTerms.orthogonal_eq] using
    unsigned_density_theorem_1_1 D a ha Z hDLMF hC hM φ heven hsupp

/-- The finite-family zero averages tend to the orthogonal distribution.
Absolute convergence of every constituent zero sum is supplied separately
by `zero_sum_absolutely_convergent`, from the actual zero-counting data. -/
theorem unsigned_orthogonal_limit {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) (ha : 1 ≤ a)
    (Z : AnalyticSpectralData D a) (hDLMF : DigammaBound.DLMFSeriesIdentity)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(3 / 2 : ℝ)) (3 / 2)) :
    Tendsto (fun n : ℕ => meanDensity (3 / 2)
      (Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n)) φ (Z.zeroOrdinate n))
        atTop (nhds (RandomMatrixMainTerms.orthogonal φ)) := by
  obtain ⟨K, _, hK⟩ := unsigned_orthogonal_error D a ha Z hDLMF hC hM φ heven hsupp
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hlevel : Tendsto (fun n : ℕ => (2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlog := Real.tendsto_log_atTop.comp hlevel
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (by filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn; exact hK n hn)
  exact hlog.const_div_atTop K

end DepthAspect.UnsignedDensity
