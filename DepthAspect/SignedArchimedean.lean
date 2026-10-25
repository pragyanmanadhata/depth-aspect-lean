import DepthAspect.SignedAnalyticData
import DepthAspect.SignedBalance

/-! The form-independent contribution to the signed explicit formula is
small because the actual root-number sum is small. Both ingredients are
proved from their general inputs, rather than supplied as size premises. -/
namespace DepthAspect.SignedDensity
open SpectralFamily UnsignedDensity
open scoped FourierTransform SchwartzMap

variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- The small mean root sign times the actual gamma-factor contribution,
including its conductor term, is O(N^-1/2) uniformly in depth. -/
theorem signed_archimedean_bound (S : SignedSieve.SignedArithmeticData r Family Full New)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (n : ℕ) (hn : 8 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) :
    ‖average (fun f => (S.rootNumber (2 ^ n) f : ℂ)) *
      ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) (2 * ((r + 1 : ℕ) : ℝ))
        (r + 1) φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0)‖ ≤
      (8 / ((2 * r + 1 : ℕ) : ℝ) *
        (‖(𝓕 φ : 𝓢(ℝ, ℂ)) 0‖ + archimedeanConstant (r + 1) φ)) *
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  let L := Real.log ((2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n)
  have hN : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hL : 1 ≤ L := UnsignedExponents.conductor_log_ge_one
    (2 * ((r + 1 : ℕ) : ℝ)) (by linarith) n hn
  have hC := archimedeanConstant_nonneg (r + 1) (by omega) φ
  have hA := actual_archimedean_error hDLMF ((2 : ℝ) ^ n) hN (r + 1) (by omega) φ hL
  have hA' : ‖ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) (2 * ((r + 1 : ℕ) : ℝ))
      (r + 1) φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0)‖ ≤
      ‖(𝓕 φ : 𝓢(ℝ, ℂ)) 0‖ + archimedeanConstant (r + 1) φ := by
    have hdiv : archimedeanConstant (r + 1) φ / L ≤ archimedeanConstant (r + 1) φ :=
      div_le_self hC hL
    have ht := norm_le_norm_sub_add
      (ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) (2 * ((r + 1 : ℕ) : ℝ))
        (r + 1) φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0)) ((𝓕 φ : 𝓢(ℝ, ℂ)) 0)
    linarith
  obtain ⟨hR0, _, hRb⟩ := S.relativeRootSum_bounds n (by omega)
  have havg : average (fun f => (S.rootNumber (2 ^ n) f : ℂ)) =
      (S.relativeRootSum (2 ^ n) : ℂ) := by
    unfold average SignedSieve.SignedArithmeticData.relativeRootSum
    push_cast
    rfl
  rw [norm_mul, havg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
  calc
    _ ≤ (8 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n))) *
        (‖(𝓕 φ : 𝓢(ℝ, ℂ)) 0‖ + archimedeanConstant (r + 1) φ) :=
      mul_le_mul hRb hA' (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n), ← Real.sqrt_eq_rpow]
      ring

end DepthAspect.SignedDensity
