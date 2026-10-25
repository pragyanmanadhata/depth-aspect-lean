import DepthAspect.SignedProjection
import DepthAspect.UnsignedOrthogonalTheorem

/-!
# The quantitative join for the two actual sign-family zero averages

This reusable step combines the two analytic error bounds. The final
Corollary 1.3 wrapper supplies them from the unsigned and signed theorems;
the density here is already the actual convergent zero-sum observation.
-/
open Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
namespace DepthAspect.SignedSieve.SignedArithmeticData
variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

noncomputable def densityConductorLog (r n : ℕ) : ℝ :=
  Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n)

/-- The literal sign-filter mean, using the entire test at the fixed
support endpoint of Corollary 1.3. -/
noncomputable def signMeanDensity (S : SignedArithmeticData r Family Full New)
    {κ : ∀ n : ℕ, Family (2 ^ n) → Type*} (γ : ∀ n f, κ n f → ℂ)
    (n : ℕ) (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  S.signAverage (2 ^ n) σ (fun f =>
    ExplicitFormula.density (4 / 3) (densityConductorLog r n) φ (γ n f))

noncomputable def signedMeanDensity (S : SignedArithmeticData r Family Full New)
    {κ : ∀ n : ℕ, Family (2 ^ n) → Type*} (γ : ∀ n f, κ n f → ℂ)
    (n : ℕ) (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ) *
    ExplicitFormula.density (4 / 3) (densityConductorLog r n) φ (γ n f))

noncomputable def specialOrthogonalMain (σ : ℝ) (φ : 𝓢(ℝ, ℂ)) : ℂ :=
  if σ = 1 then RandomMatrixMainTerms.specialOrthogonalEven φ
  else RandomMatrixMainTerms.specialOrthogonalOdd φ

theorem specialOrthogonalMain_eq (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (φ : 𝓢(ℝ, ℂ)) :
    specialOrthogonalMain σ φ = RandomMatrixMainTerms.orthogonal φ + (σ : ℂ) *
      (-(∫ ξ in (Set.Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2) := by
  rcases hσ with rfl | rfl
  · rw [specialOrthogonalMain, if_pos rfl]
    simpa only [Complex.ofReal_one, one_mul, neg_div, sub_eq_add_neg] using
      (RandomMatrixMainTerms.plus_main_term φ).symm
  · norm_num only [specialOrthogonalMain, show (-1 : ℝ) ≠ 1 by norm_num,
      if_false, Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, neg_div, neg_neg]
    exact (RandomMatrixMainTerms.minus_main_term φ).symm

theorem densityConductorLog_pos (r n : ℕ) (hn : 8 ≤ n) :
    0 < densityConductorLog r n := by
  have h := UnsignedExponents.conductor_log_ge_one (2 * ((r + 1 : ℕ) : ℝ))
    (by have : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + 1)
        linarith) n hn
  unfold densityConductorLog
  linarith

/-- The imbalance contribution is bounded uniformly at every depth n≥8,
with an explicit weight-dependent coefficient. -/
theorem inverse_sqrt_level_le_inverse_log (r n : ℕ) (hn : 8 ≤ n) :
    1 / Real.sqrt ((2 : ℝ) ^ n) ≤
      (Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2) + 2) / densityConductorLog r n := by
  have hN : (1 : ℝ) < 2 ^ n := UnsignedExponents.dyadic_level_gt_one n hn
  have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + 1)
  have hk : (1 : ℝ) ≤ (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith
  have hb := negative_power_le_inverse_conductor_log hN hk
    (by norm_num : (-(1 / 2 : ℝ)) < 0)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 ^ n),
    ← Real.sqrt_eq_rpow] at hb
  simpa only [densityConductorLog, one_div, neg_neg, one_div_div, div_one, inv_inv] using hb

/-- All denominator and family-count errors in Corollary 1.3 are removed
here. The two analytic error inputs are explicitly intermediate hypotheses. -/
theorem split_error_from_unsigned_and_signed
    (S : SignedArithmeticData r Family Full New)
    {κ : ∀ n : ℕ, Family (2 ^ n) → Type*} (γ : ∀ n f, κ n f → ℂ)
    (φ : 𝓢(ℝ, ℂ)) (Ku Ks : ℝ) (hKu : 0 ≤ Ku) (hKs : 0 ≤ Ks)
    (hU : ∀ n : ℕ, 8 ≤ n →
      ‖UnsignedDensity.meanDensity (4 / 3) (densityConductorLog r n) φ (γ n) -
        RandomMatrixMainTerms.orthogonal φ‖ ≤ Ku / densityConductorLog r n)
    (hS : ∀ n : ℕ, 8 ≤ n →
      ‖S.signedMeanDensity γ n φ +
        (∫ ξ in (Set.Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2‖ ≤
          Ks / densityConductorLog r n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 8 ≤ n → ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ‖S.signMeanDensity γ n σ φ - specialOrthogonalMain σ φ‖ ≤
        K / densityConductorLog r n := by
  let A := RandomMatrixMainTerms.orthogonal φ
  let B := -(∫ ξ in (Set.Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) ξ) / 2
  let Q := Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2) + 2
  let K := 2 * (Ku + Ks) + 16 / ((2 * r + 1 : ℕ) : ℝ) * Q * (‖A‖ + ‖B‖)
  have hden : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + 1)
  have hQ : 0 ≤ Q := by
    have hlog := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ (2 * ((r + 1 : ℕ) : ℝ)) ^ 2)
    dsimp [Q]
    linarith
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n hn σ hσ
  let X : Family (2 ^ n) → ℂ := fun f =>
    ExplicitFormula.density (4 / 3) (densityConductorLog r n) φ (γ n f)
  have hs : ‖SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ) * X f) - B‖ ≤
      Ks / densityConductorLog r n := by
    simpa only [signedMeanDensity, B, X, neg_div, sub_neg_eq_add] using hS n hn
  have he := S.signAverage_error n (by omega) σ hσ X A B
    (Ku / densityConductorLog r n) (Ks / densityConductorLog r n)
    (hU n hn) hs
  have himb := mul_le_mul_of_nonneg_left
    (inverse_sqrt_level_le_inverse_log r n hn)
    (show 0 ≤ 16 / ((2 * r + 1 : ℕ) : ℝ) * (‖A‖ + ‖B‖) by positivity)
  rw [specialOrthogonalMain_eq σ hσ φ]
  change ‖S.signAverage (2 ^ n) σ X - (A + (σ : ℂ) * B)‖ ≤ K / densityConductorLog r n
  calc
    _ ≤ 2 * (Ku / densityConductorLog r n + Ks / densityConductorLog r n) +
        16 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) * (‖A‖ + ‖B‖) := he
    _ ≤ K / densityConductorLog r n := by
      dsimp [K, Q] at himb ⊢
      calc
        _ = 2 * (Ku / densityConductorLog r n + Ks / densityConductorLog r n) +
            (16 / ((2 * r + 1 : ℕ) : ℝ) * (‖A‖ + ‖B‖)) *
              (1 / Real.sqrt ((2 : ℝ) ^ n)) := by ring
        _ ≤ 2 * (Ku / densityConductorLog r n + Ks / densityConductorLog r n) +
            (16 / ((2 * r + 1 : ℕ) : ℝ) * (‖A‖ + ‖B‖)) *
              ((Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2) + 2) / densityConductorLog r n) :=
          add_le_add (le_refl _) himb
        _ = _ := by ring

/-- The quantitative rate gives the actual weak-density limit, through
both parities of the depth. -/
theorem signMeanDensity_limit_of_rate
    (S : SignedArithmeticData r Family Full New)
    {κ : ∀ n : ℕ, Family (2 ^ n) → Type*} (γ : ∀ n f, κ n f → ℂ)
    (φ : 𝓢(ℝ, ℂ)) (σ : ℝ) (K : ℝ)
    (hK : ∀ n : ℕ, 8 ≤ n →
      ‖S.signMeanDensity γ n σ φ - specialOrthogonalMain σ φ‖ ≤
        K / densityConductorLog r n) :
    Tendsto (fun n => S.signMeanDensity γ n σ φ) atTop
      (nhds (specialOrthogonalMain σ φ)) := by
  have hlevel : Tendsto (fun n : ℕ => (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n)
      atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlog := Real.tendsto_log_atTop.comp hlevel
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (by filter_upwards [eventually_ge_atTop (8 : ℕ)] with n hn; exact hK n hn)
  exact hlog.const_div_atTop K

end DepthAspect.SignedSieve.SignedArithmeticData
