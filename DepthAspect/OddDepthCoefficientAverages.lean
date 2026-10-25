import DepthAspect.OddDepthResidueCoefficient
import DepthAspect.ResiduePrimeRestoration
import DepthAspect.CoefficientErrorMajorant
import DepthAspect.CoefficientTail

/-! Actual odd-depth coefficient identities, prime errors, and tail. -/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace DepthAspect.OddDepthCoefficientAverages
open OddDepthResidueCoefficient GlobalResidueCoefficient CharacterPrimeAverages
open QuadraticClassFormula QuadraticDiscriminantL

 theorem discriminant_negative {t : ℤ} {A B : ℝ} (hA : 0 ≤ A)
    (ht : (t : ℝ) ^ 2 ≤ 8 * A) {p : ℕ}
    (hp : p ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊) :
    IsNegativeDiscriminant (t ^ 2 - 8 * (p : ℤ)) := by
  have hlt : (t : ℝ) ^ 2 < 8 * p := by
    have := (CoefficientPrimeAverages.prime_mem_interval hA hp).1
    nlinarith
  have hltInt : t ^ 2 < 8 * (p : ℤ) := by exact_mod_cast hlt
  have h := elliptic_isNegativeDiscriminant t (2 * p) (by nlinarith [hltInt])
  convert h using 1 <;> ring

 theorem residue_eq_negative_psi {H : ℤ → ℝ} (G : GeneralFormula H)
    {m : ℕ} (hm : m ≠ 0) {t X : ℤ} (ht : 8 ∣ t) (hX : Odd X)
    (hD : IsNegativeDiscriminant (t ^ 2 - 8 * X))
    (x : (ZMod (modulus m))ˣ) (hx : (X : ZMod (modulus m)) = x) :
    residueFunction m t x = psi G (t ^ 2 - 8 * X) m := by
  rw [psi, dif_pos hD]
  exact residueFunction_eq_psi hm ht hX
    (datum _ hD).fundamental_shape
    (G.quadratic _ (datum _ hD).fundamental_shape (datum _ hD).fundamental_neg)
    (datum _ hD).conductor_pos.ne' (datum _ hD).factorization x hx

 theorem extend_good_prime {H : ℤ → ℝ} (G : GeneralFormula H)
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬p ∣ m)
    {t : ℤ} (ht : 8 ∣ t) (hD : IsNegativeDiscriminant (t ^ 2 - 8 * (p : ℤ))) :
    CharacterPrimeAverages.extend (residueFunction m t) (p : ZMod (modulus m)) =
      psi G (t ^ 2 - 8 * (p : ℤ)) m := by
  let x := ZMod.unitOfCoprime p (NegativeResidueBridge.prime_coprime_modulus m hp hp2 hpm)
  have hx : (x : ZMod (modulus m)) = p := by simp [x]
  rw [← hx]
  have he : CharacterPrimeAverages.extend (residueFunction m t)
      (x : ZMod (modulus m)) = residueFunction m t x := by
    unfold CharacterPrimeAverages.extend
    rw [dif_pos x.isUnit]
    congr 1
    exact Units.ext x.isUnit.unit_spec
  rw [he]
  exact residue_eq_negative_psi G (NeZero.ne m) ht
    (by exact_mod_cast hp.odd_of_ne_two hp2) hD x (by simpa using hx.symm)

/-- The actual coefficient-wise prime discrepancy for t²−8p. All local
identification, means, and Fourier norm bounds are discharged internally. -/
theorem coefficient_error_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    {m : ℕ} [NeZero m] {t : ℤ} (ht8 : 8 ∣ t)
    {A B M C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 2 ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 8 * A) (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hGRH : PrimitiveGRHTransport.PrimitiveVonMangoldtEstimate C)
    (Φ : ℝ → ℂ) (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    ‖ResiduePrimeRestoration.weightedOdd (fun p => psi G (t ^ 2 - 8 * (p : ℤ)) m) A B Φ -
      OddAverageEuler.coefficient t m * ∫ u in A..B, Φ u‖ ≤
      (2 * M + ∫ u in A..B, ‖deriv Φ u‖) * GlobalFourierBound.localProduct m *
        envelope (C + 3 / Real.log 4) B (modulus m) + M * OmittedPrimeCost.primeCost m := by
  have h := ResiduePrimeRestoration.coefficient_bound (m := m) (residueFunction m t)
    (fun p => psi G (t ^ 2 - 8 * (p : ℤ)) m) hA hAB hB hM0 hC hGRH Φ hΦ hdΦ hI hM
    (fun p _ _ _ => CoefficientPrimeAverages.norm_psi_le G _ m)
    (fun p hpS hp hp2 hpm => extend_good_prime (m := m) G hp hp2 hpm ht8
      (discriminant_negative hA ht hpS))
  rw [principal_mean] at h
  apply h.trans
  have hV : 0 ≤ ∫ u in A..B, ‖deriv Φ u‖ :=
    intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have hE : 0 ≤ envelope (C + 3 / Real.log 4) B (modulus m) := by
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    unfold envelope
    positivity
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (beta_residueFunction (m := m) t) (by linarith)) hE) (le_refl _)

/-- The odd-depth average is exactly the actual odd Euler series. -/
def valueAtOne (t : ℤ) : ℂ :=
  ∑' n : ℕ, OddAverageEuler.coefficient t (n + 1) / ((n + 1 : ℕ) : ℂ)

 theorem coefficient_tail (t : ℤ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖OddAverageEuler.coefficient t (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))) ∧
    (∑' n : ℕ, ‖OddAverageEuler.coefficient t (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))) ≤
        CoefficientTail.tailConstant / Real.sqrt x :=
  CoefficientTail.tail_summable_and_bound (OddAverageEuler.coefficient t)
    (OddAverageEuler.coefficient_majorant t) hx

 theorem absolute_coefficients (t : ℤ) :
    Summable (fun n : ℕ => ‖OddAverageEuler.coefficient t (n + 1)‖ / ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, ‖OddAverageEuler.coefficient t (n + 1)‖ / ((n + 1 : ℕ) : ℝ)) ≤
        CoefficientTail.tailConstant / (1 - Real.exp (-1)) :=
  CoefficientTail.absolute_series_summable_and_bound (OddAverageEuler.coefficient t)
    (OddAverageEuler.coefficient_majorant t)

end DepthAspect.OddDepthCoefficientAverages
