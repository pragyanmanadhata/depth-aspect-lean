import DepthAspect.SignedBalance
import DepthAspect.DensityReduction

/-!
# Projection onto the actual root-number families

The cardinality normalization is removed using the proved exact dimensions
and root-number counts. Only the two observation errors are hypotheses of
this reusable analytic reduction; all sign-family and denominator claims
are conclusions about the literal filters in the shared spectral family.
-/
namespace DepthAspect.SignedSieve.SignedArithmeticData
open scoped BigOperators
variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

theorem root_average_eq_relativeRootSum (S : SignedArithmeticData r Family Full New)
    (N : ℕ) :
    SpectralFamily.average (fun f => (S.rootNumber N f : ℂ)) =
      (S.relativeRootSum N : ℂ) := by
  unfold SpectralFamily.average relativeRootSum
  push_cast
  rfl

theorem signAverage_projection_real (S : SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 7 ≤ n) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (X : Family (2 ^ n) → ℂ) :
    S.signAverage (2 ^ n) σ X =
      (SpectralFamily.average X + (σ : ℂ) *
        SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ) * X f)) /
      ((1 + σ * S.relativeRootSum (2 ^ n) : ℝ) : ℂ) := by
  rw [S.signAverage_projection n hn σ hσ X, S.root_average_eq_relativeRootSum]
  push_cast
  rfl

/-- Quantitative (119), with no independent sign-imbalance or sign-class
nonemptiness premise. It applies directly to complex zero-sum observations. -/
theorem signAverage_error (S : SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 7 ≤ n) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (X : Family (2 ^ n) → ℂ) (A B : ℂ) (eu es : ℝ)
    (hU : ‖SpectralFamily.average X - A‖ ≤ eu)
    (hS : ‖SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ) * X f) - B‖ ≤ es) :
    ‖S.signAverage (2 ^ n) σ X - (A + (σ : ℂ) * B)‖ ≤
      2 * (eu + es) +
        16 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) * (‖A‖ + ‖B‖) := by
  obtain ⟨hδ0, hδhalf, hδbound⟩ := S.relativeRootSum_bounds n hn
  have hδ : |S.relativeRootSum (2 ^ n)| ≤ (1 / 2 : ℝ) := by
    rw [abs_of_nonneg hδ0]
    exact hδhalf
  have hraw : ‖S.signAverage (2 ^ n) σ X - (A + (σ : ℂ) * B)‖ ≤
      2 * (eu + es) + 2 * S.relativeRootSum (2 ^ n) * (‖A‖ + ‖B‖) := by
    rw [S.signAverage_projection_real n hn σ hσ X]
    rcases hσ with rfl | rfl
    · have h := plus_density_error (SpectralFamily.average X)
        (SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ) * X f))
        A B (S.relativeRootSum (2 ^ n)) eu es hδ hU hS
      simpa only [Complex.ofReal_one, one_mul, abs_of_nonneg hδ0] using h
    · have h := minus_density_error (SpectralFamily.average X)
        (SpectralFamily.average (fun f => (S.rootNumber (2 ^ n) f : ℂ) * X f))
        A B (S.relativeRootSum (2 ^ n)) eu es hδ hU hS
      simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul,
        sub_eq_add_neg, abs_of_nonneg hδ0] using h
  have hprod := mul_le_mul_of_nonneg_right hδbound
    (show 0 ≤ ‖A‖ + ‖B‖ by positivity)
  have htail : 2 * S.relativeRootSum (2 ^ n) * (‖A‖ + ‖B‖) ≤
      16 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) * (‖A‖ + ‖B‖) := by
    calc
      _ = 2 * (S.relativeRootSum (2 ^ n) * (‖A‖ + ‖B‖)) := by ring
      _ ≤ 2 * ((8 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n))) *
          (‖A‖ + ‖B‖)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = _ := by ring
  exact hraw.trans (add_le_add (le_refl _) htail)

end DepthAspect.SignedSieve.SignedArithmeticData
