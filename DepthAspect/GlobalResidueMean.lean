import DepthAspect.GlobalResidueModulus
import DepthAspect.LocalCoefficientNorm
import DepthAspect.AffineResidueMean
import DepthAspect.OddMeanMajorant
import DepthAspect.CoefficientDecomposition

/-!
# The actual global mean and its squarefree bound

This module evaluates the principal Fourier coefficient of the literal
function (81) by its proved CRT coordinates. The dyadic factor remains its
actual finite average, even when its degree-zero mean is zero. It is never
treated as a multiplicative arithmetic function with value one at one.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.GlobalResidueMean
open GlobalResidueCoefficient GlobalResidueModulus FiniteCharacterFourier

 theorem eight_dvd_twoPower (m : ℕ) : 8 ∣ 2 ^ twoExponent m := by
  exact pow_dvd_pow 2 (le_max_left 3 (2 * m.factorization 2))

/-- The literal twisted dyadic integrand in the CRT product. -/
def dyadicFunction (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8)
    (x : (ZMod (2 ^ twoExponent m))ˣ) : ℂ :=
  χ (-1) * (χ.changeLevel (eight_dvd_twoPower m)) x *
    DyadicCoefficientFourier.localAtTwo (twoExponent m) (m.factorization 2)
      (le_max_right _ _) t x

def localFunction (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    (i : Index m) → (ZMod (localModulus m i))ˣ → ℂ
  | none => dyadicFunction m t χ
  | some p => OddCoefficientFourier.localOnUnits (p := p.val) (m.factorization p.val) t

/-- This is precisely the normalized mean defining ψ-tilde in (81). -/
def average (m : ℕ) [NeZero m] (t : ℤ) (χ : DirichletCharacter ℂ 8) : ℂ :=
  coefficient (twistedFunction m t χ) 1

/-- Equation (81) with its literal Euler-totient normalization written out. -/
theorem average_eq_unit_sum (m : ℕ) [NeZero m] (t : ℤ)
    (χ : DirichletCharacter ℂ 8) :
    average m t χ = (1 / ((modulus m).totient : ℂ)) *
      ∑ x : (ZMod (modulus m))ˣ, twistedFunction m t χ x := by
  rw [average, coefficient_principal, ZMod.card_units_eq_totient]
  ring

/-- The dyadic factor is retained as an actual finite mean. -/
def dyadicMean (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8) : ℂ :=
  coefficient (dyadicFunction m t χ) 1

 theorem twistedFunction_product (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    twistedFunction m t χ = fun x =>
      ∏ i : Index m, localFunction m t χ i
        (ZMod.unitsMap (localModulus_dvd m i) x) := by
  funext x
  rw [Fintype.prod_option]
  change χ (-1) * (χ.changeLevel (show 8 ∣ modulus m from Nat.dvd_lcm_left 8 (m ^ 2))) x *
      (twoFactor m t x * ∏ p : OddPrime m, oddFactor m t p x) =
    dyadicFunction m t χ (ZMod.unitsMap (twoPower_dvd m) x) *
      ∏ p : OddPrime m, oddFactor m t p x
  have hχ : (χ.changeLevel (eight_dvd_twoPower m))
      (ZMod.unitsMap (twoPower_dvd m) x) =
      (χ.changeLevel (show 8 ∣ modulus m from Nat.dvd_lcm_left 8 (m ^ 2))) x := by
    have h := congrArg (fun ν : DirichletCharacter ℂ (modulus m) => ν x)
      (χ.changeLevel_trans (eight_dvd_twoPower m) (twoPower_dvd m))
    simpa [DirichletCharacter.changeLevel_def] using h.symm
  simp only [dyadicFunction, hχ, twoFactor]
  ring

/-- Equation (81)'s literal mean is exactly its dyadic mean times the computed
odd-prime means. This is the required global arithmetic identification. -/
theorem average_factorization (m : ℕ) [NeZero m] (t : ℤ)
    (χ : DirichletCharacter ℂ 8) :
    average m t χ = dyadicMean m t χ * (OddMeanMajorant.oddMean m t : ℂ) := by
  rw [average, twistedFunction_product,
    FiniteResidueCRT.principal_product_at_modulus (localModulus m)
      (localModulus_pairwise m) (modulus m) (product_eq_modulus (NeZero.ne m))
      (localModulus_dvd m) (localFunction m t χ), Fintype.prod_option]
  change dyadicMean m t χ *
      (∏ p : OddPrime m, coefficient
        (OddCoefficientFourier.localOnUnits (p := p.val) (m.factorization p.val) t) 1) = _
  congr 1
  calc
    _ = ∏ p : OddPrime m,
        (LocalResidueAverages.unitMean (p := p.val) (m.factorization p.val)
          (t : ZMod p.val) : ℂ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact AffineResidueMean.principal_local_mean (oddPrime_ne_two m p) _ t
    _ = _ := by
      unfold OddMeanMajorant.oddMean
      push_cast
      rw [← prod_oddPrime m (fun p =>
        (OddMeanMajorant.primeMean p t (m.factorization p) : ℂ))]
      apply Finset.prod_congr rfl
      intro p hp
      rw [OddMeanMajorant.primeMean, dif_pos (Fact.out : p.val.Prime)]

 theorem norm_dyadicFunction_le (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8)
    (x : (ZMod (2 ^ twoExponent m))ˣ) : ‖dyadicFunction m t χ x‖ ≤ 1 := by
  have hχ : ‖χ (-1)‖ = 1 := by simpa using χ.unit_norm_eq_one (-1 : (ZMod 8)ˣ)
  rw [dyadicFunction, norm_mul, norm_mul, hχ,
    DirichletCharacter.unit_norm_eq_one, one_mul, one_mul]
  exact LocalCoefficientNorm.norm_localAtTwo_le _ _ _ _ _

 theorem norm_dyadicMean_le (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    ‖dyadicMean m t χ‖ ≤ 1 :=
  LocalCoefficientNorm.norm_principal_le_one _ (norm_dyadicFunction_le m t χ)

/-- The pointwise estimate (87) is now for the actual mean in (81), with no
local-average or multiplicativity hypothesis. -/
theorem norm_average_squarefree_le {u v : ℕ} (hu : Squarefree u) (huodd : Odd u)
    (hv : v ≠ 0) (b : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8)
    [NeZero (2 ^ b * u * v ^ 2)] :
    ‖average (2 ^ b * u * v ^ 2) t χ‖ ≤ 1 / (u.totient : ℝ) := by
  rw [average_factorization, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul (norm_dyadicMean_le _ t χ)
    (OddMeanMajorant.abs_oddMean_le hu huodd hv b t) (abs_nonneg _)
    zero_le_one).trans_eq (one_mul _)

/-- A total sequence for the Dirichlet series; the artificial index zero is
excluded from every series and never used as a positive-index coefficient. -/
def sequence (t : ℤ) (χ : DirichletCharacter ℂ 8) (m : ℕ) : ℂ :=
  if hm : m = 0 then 0 else @average m ⟨hm⟩ t χ

 theorem sequence_eq (m : ℕ) [NeZero m] (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    sequence t χ m = average m t χ := by
  simp only [sequence, dif_neg (NeZero.ne m)]

 theorem sequence_majorant (t : ℤ) (χ : DirichletCharacter ℂ 8)
    (b : ℕ) (u : CoefficientDecomposition.SquarefreeOdd) (v : ℕ)
    (hv : 0 < v) (_hvodd : Odd v) :
    ‖sequence t χ (2 ^ b * (u : ℕ) * v ^ 2)‖ ≤ 1 / ((u : ℕ).totient : ℝ) := by
  letI : NeZero (2 ^ b * (u : ℕ) * v ^ 2) := ⟨mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by omega)) u.property.1.ne_zero)
    (pow_ne_zero _ hv.ne')⟩
  rw [sequence_eq]
  exact norm_average_squarefree_le u.property.1 u.property.2 hv.ne' b t χ

end DepthAspect.GlobalResidueMean
