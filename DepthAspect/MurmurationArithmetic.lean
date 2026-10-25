import DepthAspect.MurmurationLattice
import DepthAspect.ArithmeticPrimeWeight

/-! The literal arithmetic density Mℓ in (106). -/
namespace DepthAspect.MurmurationArithmetic
open MurmurationLattice ArithmeticWeights

noncomputable def M (a ℓ : ℕ) (y : ℝ) : ℝ :=
  weightedDensity a ℓ (integerPrimeWeight ℓ) y

/-- The first assertion of Theorem 6.1 for the actual omitted-prime
arithmetic weight, including the support-boundary endpoint. -/
theorem M_small (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) {y : ℝ}
    (hy : 0 < y) (hymax : y ≤ 1 / (4 * (ℓ : ℝ) ^ 2)) :
    M a ℓ y = (2 * Real.pi / ((2 * a + 1 : ℕ) : ℝ)) * Real.sqrt y :=
  weightedDensity_small a hℓ.two_le (integerPrimeWeight ℓ)
    (integerPrimeWeight_zero ℓ) hy hymax

end DepthAspect.MurmurationArithmetic
