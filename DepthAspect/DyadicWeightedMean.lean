import DepthAspect.DyadicFourClassBridge
import DepthAspect.OddEulerAtOne
import DepthAspect.GlobalCoefficientTail

/-! The actual averaged L-values and the weighted identity (90). -/
noncomputable section
namespace DepthAspect.DyadicWeightedMean
open GlobalCoefficientTail GlobalResidueMean DyadicOddSeries
open FourDyadicTwists ArithmeticWeights

 theorem valueAtOne_eq_LSeries (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    valueAtOne t χ = LSeries (sequence t χ) 1 := by
  have hs := CoefficientHalfPlane.LSeriesSummable_average t χ (s := 1) (by norm_num)
  rw [LSeries, hs.tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add, LSeries.term_of_ne_zero (Nat.succ_ne_zero _),
    Complex.cpow_one]
  rfl

/-- The dyadic factor at one multiplies the literal arithmetic product. -/
theorem valueAtOne_factorization (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    valueAtOne t χ = dyadicSeries t χ (1 / 2) *
      ((Real.pi : ℂ) ^ 2 / 8 * (integerPrimeWeight 2 t : ℂ)) := by
  rw [valueAtOne_eq_LSeries,
    LSeries_factorization t χ (s := 1) (by norm_num), OddEulerAtOne.odd_series_at_one]
  norm_num [Complex.cpow_neg, Complex.cpow_one]

/-- The four actual averages at one, in the order used in (90). -/
theorem four_values {t : ℤ} (ht : 8 ∣ t) :
    valueAtOne t (character 0) = (4 / 3 : ℂ) *
      ((Real.pi : ℂ) ^ 2 / 8 * (integerPrimeWeight 2 t : ℂ)) ∧
    valueAtOne t (character 1) = (1 / 3 : ℂ) *
      ((Real.pi : ℂ) ^ 2 / 8 * (integerPrimeWeight 2 t : ℂ)) ∧
    valueAtOne t (character 2) = (1 / 6 : ℂ) *
      ((Real.pi : ℂ) ^ 2 / 8 * (integerPrimeWeight 2 t : ℂ)) ∧
    valueAtOne t (character 3) = (1 / 6 : ℂ) *
      ((Real.pi : ℂ) ^ 2 / 8 * (integerPrimeWeight 2 t : ℂ)) := by
  obtain ⟨h0, h1, h2, h3⟩ := DyadicFourClassBridge.dyadic_generating_functions ht
    (z := (1 / 2 : ℂ)) (by norm_num)
  simp only [valueAtOne_factorization, h0, h1, h2, h3]
  norm_num

/-- Equation (90) for the literal residue-average Dirichlet series; every
local mean and Euler-product factor has been derived internally. -/
theorem weighted_mean {t : ℤ} (ht : 8 ∣ t) :
    (13 / 32 : ℂ) * valueAtOne t (character 0) -
      (3 / 32 : ℂ) * valueAtOne t (character 1) -
      (1 / 32 : ℂ) * valueAtOne t (character 2) -
      (1 / 32 : ℂ) * valueAtOne t (character 3) =
        (1 / 2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 8 * (integerPrimeWeight 2 t : ℂ)) := by
  obtain ⟨h0, h1, h2, h3⟩ := four_values ht
  rw [h0, h1, h2, h3]
  ring

end DepthAspect.DyadicWeightedMean
