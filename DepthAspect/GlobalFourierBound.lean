import DepthAspect.DivisorGrowth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.GCongr

/-!
# Combining the local Fourier constants

This is the numerical last step of (97): the literal product of the proved
local constants is bounded by 4 τ(m) sqrt(m), then by a uniform subpower
constant. Its CRT/Fourier interpretation is a separate step; no Fourier norm
estimate is assumed here.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.GlobalFourierBound

noncomputable def localProduct (m : ℕ) : ℝ :=
  4 * ((m.factorization 2 : ℝ) + 1) *
    ∏ p ∈ m.primeFactors.erase 2, ((m.factorization p : ℝ) + 1) * Real.sqrt p

private theorem tau_factorization (m : ℕ) (hm : m ≠ 0) :
    (m.divisors.card : ℝ) =
      ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) := by
  rw [Nat.card_divisors hm, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [Nat.cast_add, Nat.cast_one]

private theorem factorization_two_split (m : ℕ) :
    (((m.factorization 2 : ℝ) + 1) *
      ∏ p ∈ m.primeFactors.erase 2, ((m.factorization p : ℝ) + 1)) =
      ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) := by
  by_cases htwo : 2 ∈ m.primeFactors
  · exact Finset.mul_prod_erase m.primeFactors
      (fun p : ℕ => (m.factorization p : ℝ) + 1) htwo
  · have hf : m.factorization 2 = 0 := by
      by_contra h
      exact htwo (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
        Nat.dvd_of_factorization_pos h, by
          intro hm
          subst m
          simp at h⟩)
    simp only [hf, Nat.cast_zero, zero_add, one_mul, Finset.erase_eq_of_notMem htwo]

private theorem radical_odd_le (m : ℕ) (hm : 0 < m) :
    (∏ p ∈ m.primeFactors.erase 2, p) ≤ m := by
  apply Nat.le_of_dvd hm
  exact (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p)
    (Finset.erase_subset 2 m.primeFactors)).trans
    (Nat.prod_primeFactors_dvd m)

private theorem sqrt_prod_nat (s : Finset ℕ) :
    Real.sqrt ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, Real.sqrt p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p),
      Finset.prod_insert hp, ih]

/-- The literal product of the dyadic and odd local Fourier constants has
exactly the divisor-function majorant printed in (97). -/
theorem localProduct_le (m : ℕ) (hm : 0 < m) :
    localProduct m ≤ 4 * (m.divisors.card : ℝ) * Real.sqrt m := by
  have hsqrt : (∏ p ∈ m.primeFactors.erase 2, Real.sqrt p) ≤ Real.sqrt m := by
    rw [← sqrt_prod_nat]
    exact Real.sqrt_le_sqrt (by exact_mod_cast radical_odd_le m hm)
  unfold localProduct
  rw [Finset.prod_mul_distrib]
  calc
    _ = 4 * (((m.factorization 2 : ℝ) + 1) *
        ∏ p ∈ m.primeFactors.erase 2, ((m.factorization p : ℝ) + 1)) *
          ∏ p ∈ m.primeFactors.erase 2, Real.sqrt p := by ring
    _ = 4 * (m.divisors.card : ℝ) *
          ∏ p ∈ m.primeFactors.erase 2, Real.sqrt p := by
      rw [factorization_two_split, ← tau_factorization m hm.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt (by positivity)

/-- The constant depends only on δ; the modulus and trace index do not enter it. -/
theorem localProduct_subpower {δ : ℝ} (hδ : 0 < δ) (m : ℕ) (hm : 0 < m) :
    localProduct m ≤ (4 * DivisorGrowth.boundConstant δ) * (m : ℝ) ^ (1 / 2 + δ) := by
  apply (localProduct_le m hm).trans
  simpa only [Real.sqrt_eq_rpow] using DivisorGrowth.four_divisors_sqrt_le hδ hm

end DepthAspect.GlobalFourierBound
