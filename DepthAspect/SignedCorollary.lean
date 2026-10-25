import DepthAspect.SignedSplitReduction
import DepthAspect.SignedDensityTheorem

/-!
# Corollary 1.3 for the literal root-number subfamilies

The two analytic bounds are supplied by the proved unsigned and signed
theorems. The final result uses the same family, eigenvalues, zero ordinates,
entire test, and root-number filters. Primitive Dirichlet RH is kept distinct
from the cited general theorems that imply its analytic consequences.
-/
open Filter MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap
namespace DepthAspect.SignedSieve.SignedArithmeticData
variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- Corollary 1.3, quantitatively and simultaneously for both actual
root-number classes. No unsigned density, signed density, trace-size,
sign-balance, or nonemptiness estimate is an independent premise. -/
theorem root_number_density_corollary_1_3
    (S : SignedArithmeticData r Family Full New) (Z : SignedDensity.AnalyticData S)
    (hRH : DirichletRH.PrimitiveDirichletRH)
    (cited : GRHConsequences.CitedGeneralTheorems)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(4 / 3 : ℝ)) (4 / 3)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 8 ≤ n → ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ‖S.signMeanDensity Z.zeroOrdinate n σ φ - specialOrthogonalMain σ φ‖ ≤
        K / densityConductorLog r n := by
  have hsupU : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(3 / 2 : ℝ)) (3 / 2) := by
    intro x hx
    have h := hsupp hx
    constructor <;> linarith [h.1, h.2]
  have hsup4 : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-(4 / 3 : ℝ)) (4 / 3) :=
    subset_closure.trans (hsupp.trans Set.Ioo_subset_Icc_self)
  have hsup3 : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-(3 / 2 : ℝ)) (3 / 2) :=
    subset_closure.trans (hsupU.trans Set.Ioo_subset_Icc_self)
  obtain ⟨Ku, hKu, hU⟩ := UnsignedDensity.unsigned_orthogonal_error
    S.unsigned (r + 1) (by omega) Z.toUnsigned hDLMF hC hM φ heven hsupU
  obtain ⟨Ks, hKs, hS⟩ := SignedDensity.signed_density_theorem_1_2
    S Z hRH cited hDLMF hBessel φ heven hsupp
  apply S.split_error_from_unsigned_and_signed Z.zeroOrdinate φ Ku Ks hKu hKs
  · intro n hn
    rw [UnsignedDensity.meanDensity_support_independent φ
      (by norm_num : (0 : ℝ) ≤ 4 / 3) (by norm_num : (0 : ℝ) ≤ 3 / 2)
      hsup4 hsup3]
    exact hU n hn
  · intro n hn
    simpa only [signedMeanDensity, SignedDensity.signedMeanDensity,
      densityConductorLog, SignedDensity.conductorLog] using hS n (by omega)

/-- The limits in Corollary 1.3 are the literal SO(even) and SO(odd)
Lebesgue-integral functionals, including the central mass for the latter. -/
theorem root_number_density_limits
    (S : SignedArithmeticData r Family Full New) (Z : SignedDensity.AnalyticData S)
    (hRH : DirichletRH.PrimitiveDirichletRH)
    (cited : GRHConsequences.CitedGeneralTheorems)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(4 / 3 : ℝ)) (4 / 3)) :
    Tendsto (fun n => S.signMeanDensity Z.zeroOrdinate n 1 φ) atTop
      (nhds (RandomMatrixMainTerms.specialOrthogonalEven φ)) ∧
    Tendsto (fun n => S.signMeanDensity Z.zeroOrdinate n (-1) φ) atTop
      (nhds (RandomMatrixMainTerms.specialOrthogonalOdd φ)) := by
  obtain ⟨K, _, hK⟩ := S.root_number_density_corollary_1_3 Z hRH cited hDLMF hBessel
    hC hM φ heven hsupp
  constructor
  · have hmain : specialOrthogonalMain 1 φ = RandomMatrixMainTerms.specialOrthogonalEven φ := by
      unfold specialOrthogonalMain
      exact if_pos rfl
    simpa only [hmain] using
      S.signMeanDensity_limit_of_rate Z.zeroOrdinate φ 1 K
        (fun n hn => hK n hn 1 (Or.inl rfl))
  · have hmain : specialOrthogonalMain (-1) φ = RandomMatrixMainTerms.specialOrthogonalOdd φ := by
      unfold specialOrthogonalMain
      exact if_neg (by norm_num : (-1 : ℝ) ≠ 1)
    simpa only [hmain] using
      S.signMeanDensity_limit_of_rate Z.zeroOrdinate φ (-1) K
        (fun n hn => hK n hn (-1) (Or.inr rfl))

/-- Every zero sum used in either sign filter is absolutely convergent,
from the same general zero-counting data used in the unsigned theorem. -/
theorem root_number_zero_sums_absolutely_convergent
    (S : SignedArithmeticData r Family Full New) (Z : SignedDensity.AnalyticData S)
    (ZC : SignedDensity.ZeroCountingData Z) (n : ℕ) (hn : 8 ≤ n)
    (φ : 𝓢(ℝ, ℂ))
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(4 / 3 : ℝ)) (4 / 3))
    (f : Family (2 ^ n)) :
    Summable (fun i => ‖EntireExtension.extension (4 / 3) (𝓕 φ : 𝓢(ℝ, ℂ))
      ((((densityConductorLog r n) / (2 * Real.pi) : ℝ) : ℂ) * Z.zeroOrdinate n f i)‖) := by
  exact UnsignedDensity.zero_sum_absolutely_convergent Z.toUnsigned (by omega)
    ZC.toUnsigned n hn (by norm_num) φ
    (subset_closure.trans (hsupp.trans Set.Ioo_subset_Icc_self)) f

end DepthAspect.SignedSieve.SignedArithmeticData
