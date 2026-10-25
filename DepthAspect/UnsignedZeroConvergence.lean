import DepthAspect.UnsignedDensityTheorem
import DepthAspect.ZeroSumConvergence

/-!
# Genuine convergence of the zero sums in the unsigned density theorem

The zero count is the general global `O(T log(BT))` input, indexed with
multiplicity. Absolute convergence itself is a conclusion. Complex zero
ordinates are retained throughout; the strip condition is not a modular
Riemann hypothesis.
-/
namespace DepthAspect.UnsignedDensity

open scoped BigOperators FourierTransform SchwartzMap

/-- Standard zero-location and zero-counting data, separate from the general
local-integral explicit formula. The constants may depend on the individual
form and level, as only pointwise absolute convergence is required here. -/
structure ZeroCountingData {k a : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    {D : ArithmeticSpectralData k Family V} (Z : AnalyticSpectralData D a) where
  zerosUpTo : ∀ n f, ℝ → Finset (Z.zeroIndex n f)
  countConstant : ∀ n, Family (2 ^ n) → ℝ
  countScale : ∀ n, Family (2 ^ n) → ℝ
  countConstant_nonneg : ∀ n, 8 ≤ n → ∀ f, 0 ≤ countConstant n f
  countScale_ge_one : ∀ n, 8 ≤ n → ∀ f, 1 ≤ countScale n f
  membership : ∀ n, 8 ≤ n → ∀ f i T,
    i ∈ zerosUpTo n f T ↔ |(Z.zeroOrdinate n f i).re| ≤ T
  critical_strip : ∀ n, 8 ≤ n → ∀ f i, |(Z.zeroOrdinate n f i).im| ≤ 1 / 2
  global_count : ∀ n, 8 ≤ n → ∀ f T, 1 ≤ T →
    ((zerosUpTo n f T).card : ℝ) ≤ countConstant n f * T * Real.log (countScale n f * T)

/-- Every literal zero sum appearing in the density has an absolutely
summable complex summand, derived from its general zero count. -/
theorem zero_sum_absolutely_convergent {k a : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    {D : ArithmeticSpectralData k Family V} (Z : AnalyticSpectralData D a)
    (ha : 1 ≤ a) (ZC : ZeroCountingData Z) (n : ℕ) (hn : 8 ≤ n)
    {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (f : Family (2 ^ n)) :
    let L := Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n)
    Summable (fun i => ‖EntireExtension.extension s (𝓕 φ : 𝓢(ℝ, ℂ))
      (((L / (2 * Real.pi) : ℝ) : ℂ) * Z.zeroOrdinate n f i)‖) := by
  classical
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hL := UnsignedExponents.conductor_log_ge_one (2 * (a : ℝ)) (by linarith) n hn
  have hL0 : 0 < Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n) := by linarith
  exact ZeroSumConvergence.schwartz_zero_sum_absolutely_convergent
    (Z.zeroOrdinate n f) (ZC.zerosUpTo n f) (ZC.membership n hn f)
    (ZC.critical_strip n hn f) (ZC.countConstant_nonneg n hn f)
    (ZC.countScale_ge_one n hn f) hs (by positivity) (ZC.global_count n hn f) φ hsupp

/-- Theorem 1.1 with both the uniform density error and convergence of each
actual zero sum certified. No zero-sum summability premise is added. -/
theorem unsigned_density_convergent {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) (ha : 1 ≤ a)
    (Z : AnalyticSpectralData D a) (ZC : ZeroCountingData Z)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(3 / 2 : ℝ)) (3 / 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 8 ≤ n →
      let L := Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n)
      (∀ f : Family (2 ^ n), Summable (fun i =>
        ‖EntireExtension.extension (3 / 2) (𝓕 φ : 𝓢(ℝ, ℂ))
          (((L / (2 * Real.pi) : ℝ) : ℂ) * Z.zeroOrdinate n f i)‖)) ∧
      ‖meanDensity (3 / 2) L φ (Z.zeroOrdinate n) -
        ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤ K / L := by
  obtain ⟨K, hK0, hK⟩ := unsigned_density_theorem_1_1 D a ha Z hDLMF hC hM φ heven hsupp
  refine ⟨K, hK0, ?_⟩
  intro n hn
  constructor
  · intro f
    exact zero_sum_absolutely_convergent Z ha ZC n hn (by norm_num) φ
      (subset_closure.trans (hsupp.trans Set.Ioo_subset_Icc_self)) f
  · exact hK n hn

end DepthAspect.UnsignedDensity
