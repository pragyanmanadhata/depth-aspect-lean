import DepthAspect.SignedAnalyticData
import DepthAspect.SignedUniformPrefix

/-! An explicit initial-depth envelope depending only on weight and test. -/
namespace DepthAspect.SignedDensity
open SpectralFamily UnsignedDensity
open scoped BigOperators FourierTransform SchwartzMap

noncomputable def conductorLog (r n : ℕ) : ℝ :=
  Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n)

theorem conductorLog_pos (r n : ℕ) : 0 < conductorLog r n := by
  have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hN : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hsq : (4 : ℝ) ≤ (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hN
    (sq_nonneg (2 * ((r + 1 : ℕ) : ℝ)))
  exact Real.log_pos (by nlinarith)

/-- Every entry is determined by r,s,φ,n; there is no family or spectral
parameter in this constant. The archimedean term is retained literally,
so no asymptotic estimate is used at the finitely many initial depths. -/
noncomputable def initialEnvelope (r : ℕ) (s : ℝ) (φ : 𝓢(ℝ, ℂ)) (n : ℕ) : ℝ :=
  ‖ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) (2 * ((r + 1 : ℕ) : ℝ))
    (r + 1) φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0)‖ +
      (2 / conductorLog r n) * (scalarPrimeBox (conductorLog r n) s * 2 *
        ‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖)

theorem initialEnvelope_nonneg (r : ℕ) (s : ℝ) (φ : 𝓢(ℝ, ℂ)) (n : ℕ) :
    0 ≤ initialEnvelope r s φ n := by
  exact add_nonneg (norm_nonneg _) (mul_nonneg (div_nonneg (by norm_num) (conductorLog_pos r n).le)
    (mul_nonneg (mul_nonneg (scalarPrimeBox_nonneg _ _) (by norm_num)) (norm_nonneg _)))

variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- A single bound valid for every allowed spectral model, including n=7.
The formula and Satake hypotheses are obtained from general analytic data;
the constant is the explicit model-independent expression above. -/
theorem signed_density_initial_bound
    (S : SignedSieve.SignedArithmeticData r Family Full New) (Z : AnalyticData S)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (n : ℕ) (hn : 7 ≤ n)
    {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) :
    ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
      (conductorLog r n) φ (Z.zeroOrdinate n)‖ ≤ initialEnvelope r s φ n := by
  refine signedMeanDensity_uniform_bound (conductorLog_pos r n) (norm_nonneg _)
    (fun f => (S.rootNumber (2 ^ n) f : ℂ)) ?_ φ hsupp ?_ (Z.zeroOrdinate n)
    (Z.alpha n) (Z.beta n)
    (ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) (2 * ((r + 1 : ℕ) : ℝ))
      (r + 1) φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0)) ?_ ?_ ?_
  · intro f
    rcases S.rootNumber_sign (2 ^ n) f with h | h <;> simp [h]
  · intro x
    exact (𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction.norm_coe_le_norm x
  · intro p hp f
    have hc := (Finset.mem_filter.mp hp).2
    exact Z.alpha_norm n hn f p hc.1 hc.2
  · intro p hp f
    have hc := (Finset.mem_filter.mp hp).2
    exact Z.beta_norm n hn f p hc.1 hc.2
  · exact Z.explicit_formula hDLMF n hn hs φ heven hsupp

/-- The actual finite-prefix constant can be chosen uniformly in all
spectral data. All dependence beyond the tail constant is displayed. -/
theorem signed_density_finite_prefix
    (S : SignedSieve.SignedArithmeticData r Family Full New) (Z : AnalyticData S)
    (hDLMF : DigammaBound.DLMFSeriesIdentity)
    {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (I : ℂ) (cutoff : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hTail : ∀ n, 7 ≤ n → cutoff ≤ n →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
        (conductorLog r n) φ (Z.zeroOrdinate n) + I‖ ≤ K / conductorLog r n) :
    let C := K + ∑ j ∈ Finset.range cutoff,
      max 0 (conductorLog r j) * (initialEnvelope r s φ j + ‖I‖)
    0 ≤ C ∧ ∀ n, 7 ≤ n →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
        (conductorLog r n) φ (Z.zeroOrdinate n) + I‖ ≤ C / conductorLog r n := by
  apply extend_finite_prefix_uniform (conductorLog r)
    (fun n => initialEnvelope r s φ n + ‖I‖) _ 7 cutoff
    (fun n _ => conductorLog_pos r n)
    (fun n => add_nonneg (initialEnvelope_nonneg r s φ n) (norm_nonneg _)) _ K hK hTail
  intro n hn
  exact (norm_add_le _ _).trans (add_le_add
    (signed_density_initial_bound S Z hDLMF n hn hs φ heven hsupp) le_rfl)

end DepthAspect.SignedDensity
