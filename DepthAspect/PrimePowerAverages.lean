import DepthAspect.PrimePowerTail
import DepthAspect.SatakeCoefficients
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped BigOperators FourierTransform

namespace DepthAspect.PrimePowerAverages

open PrimePowerTail

/-- The actual scalar prime-power weight is nonnegative on the paper's indices. -/
theorem higherPowerTerm_nonneg (p : OddPrime) (j : ℕ) :
    0 ≤ higherPowerTerm (p.val : ℝ) j := by
  unfold higherPowerTerm
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast
    (Nat.le_trans (by decide : 1 ≤ 3) p.property.2)))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

noncomputable def twistedTerm (w : OddPrime → ℕ → ℂ) (p : OddPrime) (j : ℕ) : ℂ :=
  higherPowerTerm (p.val : ℝ) j • w p j

theorem twistedTerm_norm_bound (w : OddPrime → ℕ → ℂ) (C : ℝ)
    (hw : ∀ p j, ‖w p j‖ ≤ C) (p : OddPrime) (j : ℕ) :
    ‖twistedTerm w p j‖ ≤ C * higherPowerTerm (p.val : ℝ) j := by
  unfold twistedTerm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (higherPowerTerm_nonneg p j)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hw p j) (higherPowerTerm_nonneg p j)

theorem twistedTerm_summable (w : OddPrime → ℕ → ℂ) (C : ℝ)
    (hw : ∀ p j, ‖w p j‖ ≤ C) (p : OddPrime) : Summable (twistedTerm w p) :=
  (((higherPowerTerm_hasSum (by exact_mod_cast p.property.2)).summable).mul_left C).of_norm_bounded
    (twistedTerm_norm_bound w C hw p)

theorem twisted_inner_norm_bound (w : OddPrime → ℕ → ℂ) (C : ℝ)
    (hw : ∀ p j, ‖w p j‖ ≤ C) (p : OddPrime) :
    ‖∑' j, twistedTerm w p j‖ ≤ C * ∑' j, higherPowerTerm (p.val : ℝ) j :=
  tsum_of_norm_bounded
    (((higherPowerTerm_hasSum (by exact_mod_cast p.property.2)).summable).hasSum.mul_left C)
    (twistedTerm_norm_bound w C hw p)

theorem twisted_outer_summable (w : OddPrime → ℕ → ℂ) (C : ℝ)
    (hw : ∀ p j, ‖w p j‖ ≤ C) :
    Summable (fun p : OddPrime => ∑' j : ℕ, twistedTerm w p j) :=
  (oddPrime_higherPower_summable.mul_left C).of_norm_bounded
    (twisted_inner_norm_bound w C hw)

/-- A bounded complex twist of the actual higher-prime-power weights has an
absolute majorant independent of the support cutoff. Both nested series converge. -/
theorem twisted_tail_norm_bound (w : OddPrime → ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ p j, ‖w p j‖ ≤ C) :
    ‖∑' p : OddPrime, ∑' j : ℕ, twistedTerm w p j‖ ≤ 48 * C := by
  have h := tsum_of_norm_bounded (oddPrime_higherPower_summable.hasSum.mul_left C)
    (twisted_inner_norm_bound w C hw)
  have hm := mul_le_mul_of_nonneg_left oddPrime_higherPower_tsum_le_forty_eight hC
  exact h.trans (by nlinarith)

/-- The coefficient hypotheses used for (117), applied to the actual values
of the test transform. The variable `j` represents the paper's exponent `j+3`. -/
theorem coefficient_test_tail_bound
    (ε : ℂ) (hε : ‖ε‖ ≤ 1) (a : OddPrime → ℕ → ℂ)
    (ha : ∀ p j, ‖a p j‖ ≤ 2) (h : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hh : ∀ x, ‖h x‖ ≤ M) (L : ℝ) :
    ‖∑' p : OddPrime, ∑' j : ℕ,
      higherPowerTerm (p.val : ℝ) j •
        (ε * a p j * h ((((j : ℝ) + 3) * Real.log (p.val : ℝ)) / L))‖ ≤ 96 * M := by
  have hw : ∀ p : OddPrime, ∀ j : ℕ,
      ‖ε * a p j * h ((((j : ℝ) + 3) * Real.log (p.val : ℝ)) / L)‖ ≤ 2 * M := by
    intro p j
    rw [norm_mul, norm_mul]
    have hfirst : ‖ε‖ * ‖a p j‖ ≤ 2 := by
      simpa only [one_mul] using mul_le_mul hε (ha p j) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact mul_le_mul hfirst (hh _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have hbound := twisted_tail_norm_bound
    (fun p j => ε * a p j * h ((((j : ℝ) + 3) * Real.log (p.val : ℝ)) / L))
    (2 * M) (by positivity) hw
  unfold twistedTerm at hbound
  linarith

/-- The exact constant in (117), for a finite nonempty averaging family. -/
theorem averaged_coefficient_test_tail_bound
    {ι : Type*} (F : Finset ι) (hF : 0 < F.card)
    (ε : ι → ℂ) (hε : ∀ f ∈ F, ‖ε f‖ ≤ 1)
    (a : ι → OddPrime → ℕ → ℂ) (ha : ∀ f ∈ F, ∀ p j, ‖a f p j‖ ≤ 2)
    (h : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hh : ∀ x, ‖h x‖ ≤ M)
    (L : ℝ) (hL : 0 < L) :
    ‖(2 / (L * F.card)) •
      ∑ f ∈ F, ∑' p : OddPrime, ∑' j : ℕ,
        higherPowerTerm (p.val : ℝ) j •
          (ε f * a f p j * h ((((j : ℝ) + 3) * Real.log (p.val : ℝ)) / L))‖ ≤
      192 * M / L := by
  have hc : (0 : ℝ) < F.card := by exact_mod_cast hF
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 / (L * F.card))]
  have hsum := norm_sum_le_of_le F (fun f hf =>
    coefficient_test_tail_bound (ε f) (hε f hf) (a f) (ha f hf) h M hM hh L)
  have hsum' : ‖∑ f ∈ F, ∑' p : OddPrime, ∑' j : ℕ,
        higherPowerTerm (p.val : ℝ) j •
          (ε f * a f p j * h ((((j : ℝ) + 3) * Real.log (p.val : ℝ)) / L))‖ ≤
      F.card * (96 * M) := by simpa using hsum
  calc
    _ ≤ (2 / (L * F.card)) * (F.card * (96 * M)) :=
      mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = _ := by field_simp [ne_of_gt hc, ne_of_gt hL]; ring


/-- The actual Fourier transform of a Schwartz function supplies its own
finite uniform bound, so the test-function estimate is not an assumption. -/
theorem averaged_schwartz_fourier_tail_bound
    {ι : Type*} (F : Finset ι) (hF : 0 < F.card)
    (ε : ι → ℂ) (hε : ∀ f ∈ F, ‖ε f‖ ≤ 1)
    (a : ι → OddPrime → ℕ → ℂ) (ha : ∀ f ∈ F, ∀ p j, ‖a f p j‖ ≤ 2)
    (φ : SchwartzMap ℝ ℂ) (L : ℝ) (hL : 0 < L) :
    ‖(2 / (L * F.card)) •
      ∑ f ∈ F, ∑' p : OddPrime, ∑' j : ℕ,
        higherPowerTerm (p.val : ℝ) j •
          (ε f * a f p j * (𝓕 φ) ((((j : ℝ) + 3) * Real.log (p.val : ℝ)) / L))‖ ≤
      192 * ‖(𝓕 φ).toBoundedContinuousFunction‖ / L := by
  apply averaged_coefficient_test_tail_bound F hF ε hε a ha (⇑(𝓕 φ : SchwartzMap ℝ ℂ))
    ‖(𝓕 φ : SchwartzMap ℝ ℂ).toBoundedContinuousFunction‖ (norm_nonneg _) _ L hL
  intro x
  exact BoundedContinuousFunction.norm_coe_le_norm (𝓕 φ : SchwartzMap ℝ ℂ).toBoundedContinuousFunction x


/-- Equation (117) for the literal Satake coefficients α^ν+β^ν and an actual
Schwartz Fourier transform. Unit Satake norms are precisely the paper's Deligne
input; the bound on the coefficient and both convergent series are consequences. -/
theorem averaged_satake_fourier_tail_bound
    {ι : Type*} (F : Finset ι) (hF : 0 < F.card)
    (ε : ι → ℂ) (hε : ∀ f ∈ F, ε f = 1 ∨ ε f = -1)
    (α β : ι → OddPrime → ℂ)
    (hα : ∀ f ∈ F, ∀ p, ‖α f p‖ = 1)
    (hβ : ∀ f ∈ F, ∀ p, ‖β f p‖ = 1)
    (φ : SchwartzMap ℝ ℂ) (L : ℝ) (hL : 0 < L) :
    ‖(2 / (L * F.card)) •
      ∑ f ∈ F, ∑' p : OddPrime, ∑' j : ℕ,
        higherPowerTerm (p.val : ℝ) j •
          (ε f * SatakeCoefficients.powerCoefficient (α f p) (β f p) (j + 3) *
            (𝓕 φ) ((((j : ℝ) + 3) * Real.log (p.val : ℝ)) / L))‖ ≤
      192 * ‖(𝓕 φ).toBoundedContinuousFunction‖ / L := by
  apply averaged_schwartz_fourier_tail_bound F hF ε _
    (fun f p j => SatakeCoefficients.powerCoefficient (α f p) (β f p) (j + 3)) _ φ L hL
  · intro f hf
    rcases hε f hf with h | h <;> simp [h]
  · intro f hf p j
    exact SatakeCoefficients.norm_powerCoefficient_le_two (α f p) (β f p)
      (hα f hf p) (hβ f hf p) (j + 3)

end DepthAspect.PrimePowerAverages
