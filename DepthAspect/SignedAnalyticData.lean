import DepthAspect.SignedArithmeticData
import DepthAspect.UnsignedZeroConvergence
import DepthAspect.SignedDensityModel

/-!
# Analytic data for the actual signed family

The data are available from depth seven, as required by Theorem 1.2. Their
restriction is exactly the unsigned analytic interface at depth eight.
Only the general local-integral explicit formula, unit Satake roots and
standard zero-counting estimate are inputs; equation (56), the square
coefficient, and absolute convergence are derived.
-/
namespace DepthAspect.SignedDensity

open scoped BigOperators FourierTransform SchwartzMap

structure AnalyticData {r : ℕ} {Family Full New : ℕ → Type*}
    [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
    [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]
    (S : SignedSieve.SignedArithmeticData r Family Full New) where
  zeroIndex : ∀ n, Family (2 ^ n) → Type
  zeroOrdinate : ∀ n f, zeroIndex n f → ℂ
  alpha : ∀ n, Family (2 ^ n) → ℕ → ℂ
  beta : ∀ n, Family (2 ^ n) → ℕ → ℂ
  alpha_norm : ∀ n, 7 ≤ n → ∀ f p, p.Prime → p ≠ 2 → ‖alpha n f p‖ = 1
  beta_norm : ∀ n, 7 ≤ n → ∀ f p, p.Prime → p ≠ 2 → ‖beta n f p‖ = 1
  first_coefficient : ∀ n, 7 ≤ n → ∀ f p, p.Prime → p ≠ 2 →
    alpha n f p + beta n f p = S.unsigned.eigenvalues (2 ^ n) f p
  product : ∀ n, 7 ≤ n → ∀ f p, p.Prime → p ≠ 2 → alpha n f p * beta n f p = 1
  general_explicit_formula : ∀ n, 7 ≤ n → ∀ f,
    ExplicitFormula.ShinTemplierFormula ((2 : ℝ) ^ n) (zeroOrdinate n f)
      (GammaLocal.gammaFactor (2 * ((r + 1 : ℕ) : ℝ)))
      (ExplicitFormula.finiteEulerFactor (alpha n f) (beta n f))

namespace AnalyticData

variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]
  {S : SignedSieve.SignedArithmeticData r Family Full New}

/-- Restriction to the previously checked unsigned interface; all zero
indices and ordinates are definitionally preserved. -/
def toUnsigned (Z : AnalyticData S) : UnsignedDensity.AnalyticSpectralData S.unsigned (r + 1) where
  weight_relation := by omega
  zeroIndex := Z.zeroIndex
  zeroOrdinate := Z.zeroOrdinate
  alpha := Z.alpha
  beta := Z.beta
  alpha_norm n hn := Z.alpha_norm n (by omega)
  beta_norm n hn := Z.beta_norm n (by omega)
  first_coefficient n hn := Z.first_coefficient n (by omega)
  product n hn := Z.product n (by omega)
  general_explicit_formula n hn := Z.general_explicit_formula n (by omega)

theorem square_coefficient (Z : AnalyticData S)
    (n : ℕ) (hn : 7 ≤ n) (f : Family (2 ^ n)) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    tracePolynomial (Z.alpha n f p + Z.beta n f p) 1 2 =
      S.unsigned.eigenvalues (2 ^ n) f (p ^ 2) := by
  rw [Z.first_coefficient n hn f p hp hp2]
  exact S.unsigned.square_coefficient (2 ^ n) f p hp
    ((hp.odd_of_ne_two hp2).coprime_two_right.pow_right n)

/-- Equation (56) is a theorem of the general analytic data at every depth
needed in the signed result, including the separate smallest depth seven. -/
theorem explicit_formula (Z : AnalyticData S)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (n : ℕ) (hn : 7 ≤ n)
    {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (f : Family (2 ^ n)) :
    let L := Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n)
    ExplicitFormula.density s L φ (Z.zeroOrdinate n f) =
      ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) (2 * ((r + 1 : ℕ) : ℝ))
        (r + 1) φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0) -
      ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (Z.alpha n f) (Z.beta n f) := by
  have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hN : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hL : 0 < Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n) := by
    apply Real.log_pos
    have hsq : 4 ≤ (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hN
      (sq_nonneg (2 * ((r + 1 : ℕ) : ℝ)))
    nlinarith
  exact ExplicitFormula.explicit_formula hDLMF ((2 : ℝ) ^ n)
    (2 * ((r + 1 : ℕ) : ℝ)) (by positivity) (r + 1) (by omega) rfl hL
    (Z.zeroOrdinate n f) (Z.alpha n f) (Z.beta n f)
    (Z.alpha_norm n hn f) (Z.beta_norm n hn f) (Z.general_explicit_formula n hn f)
    hs φ heven hsupp

end AnalyticData

structure ZeroCountingData {r : ℕ} {Family Full New : ℕ → Type*}
    [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
    [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]
    {S : SignedSieve.SignedArithmeticData r Family Full New} (Z : AnalyticData S) where
  zerosUpTo : ∀ n f, ℝ → Finset (Z.zeroIndex n f)
  countConstant : ∀ n, Family (2 ^ n) → ℝ
  countScale : ∀ n, Family (2 ^ n) → ℝ
  countConstant_nonneg : ∀ n, 7 ≤ n → ∀ f, 0 ≤ countConstant n f
  countScale_ge_one : ∀ n, 7 ≤ n → ∀ f, 1 ≤ countScale n f
  membership : ∀ n, 7 ≤ n → ∀ f i T,
    i ∈ zerosUpTo n f T ↔ |(Z.zeroOrdinate n f i).re| ≤ T
  critical_strip : ∀ n, 7 ≤ n → ∀ f i, |(Z.zeroOrdinate n f i).im| ≤ 1 / 2
  global_count : ∀ n, 7 ≤ n → ∀ f T, 1 ≤ T →
    ((zerosUpTo n f T).card : ℝ) ≤ countConstant n f * T * Real.log (countScale n f * T)

namespace ZeroCountingData
variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]
  {S : SignedSieve.SignedArithmeticData r Family Full New} {Z : AnalyticData S}

def toUnsigned (ZC : ZeroCountingData Z) : UnsignedDensity.ZeroCountingData Z.toUnsigned where
  zerosUpTo := ZC.zerosUpTo
  countConstant := ZC.countConstant
  countScale := ZC.countScale
  countConstant_nonneg n hn := ZC.countConstant_nonneg n (by omega)
  countScale_ge_one n hn := ZC.countScale_ge_one n (by omega)
  membership n hn := ZC.membership n (by omega)
  critical_strip n hn := ZC.critical_strip n (by omega)
  global_count n hn := ZC.global_count n (by omega)

theorem zero_sum_absolutely_convergent (ZC : ZeroCountingData Z)
    (n : ℕ) (hn : 7 ≤ n) {s : ℝ} (hs : 0 ≤ s) (φ : 𝓢(ℝ, ℂ))
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (f : Family (2 ^ n)) :
    let L := Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n)
    Summable (fun i => ‖EntireExtension.extension s (𝓕 φ : 𝓢(ℝ, ℂ))
      (((L / (2 * Real.pi) : ℝ) : ℂ) * Z.zeroOrdinate n f i)‖) := by
  classical
  have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hN : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hL : 0 < Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n) := by
    apply Real.log_pos
    have hsq : 4 ≤ (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hN
      (sq_nonneg (2 * ((r + 1 : ℕ) : ℝ)))
    nlinarith
  exact ZeroSumConvergence.schwartz_zero_sum_absolutely_convergent
    (Z.zeroOrdinate n f) (ZC.zerosUpTo n f) (ZC.membership n hn f)
    (ZC.critical_strip n hn f) (ZC.countConstant_nonneg n hn f)
    (ZC.countScale_ge_one n hn f) hs (by positivity) (ZC.global_count n hn f) φ hsupp

end ZeroCountingData
end DepthAspect.SignedDensity
