import DepthAspect.ImprimitiveEuler
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The actual prime-factor decomposition of the imprimitive coefficient

This finite identity applies also to conductor one. It does not force the
coefficient at zero into an arithmetic-function type, and it does not assume
multiplicativity of the twisted reduced-residue average.
-/
open scoped BigOperators
namespace DepthAspect.PrimeCoefficientProduct
open ImprimitiveCharacter ImprimitiveEuler

 theorem psiNat_finset_prod {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ)
    {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (hs : (s : Set ι).Pairwise (fun i j => Nat.Coprime (g i) (g j))) :
    psiNat χ f (∏ i ∈ s, g i) = ∏ i ∈ s, psiNat χ f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpair : (s : Set ι).Pairwise (fun i j => Nat.Coprime (g i) (g j)) := by
      intro j hj k hk hjk
      exact hs (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk
    have hcop : Nat.Coprime (g i) (∏ j ∈ s, g j) := by
      apply Nat.Coprime.prod_right
      intro j hj
      exact hs (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj)
        (ne_of_mem_of_not_mem hj hi).symm
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      psiNat_mul_of_coprime χ f _ _ hcop, ih hpair]

/-- No local Euler identity is an input: the formula follows from the proved
coprime multiplication rule and the actual factorization of `m`. -/
theorem psiNat_primeFactorProduct {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) {m : ℕ} (hm : m ≠ 0) :
    psiNat χ f m = ∏ p ∈ m.primeFactors, psiNat χ f (p ^ m.factorization p) := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm]
  apply psiNat_finset_prod
  intro p hp r hr hpr
  exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hr)).mpr hpr).pow _ _

/-- Separate the dyadic factor while retaining its degree-zero value one
when `m` is odd. This is the product identity used before the CRT average. -/
theorem psiNat_two_mul_odd {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) {m : ℕ} (hm : m ≠ 0) :
    psiNat χ f m = psiNat χ f (2 ^ m.factorization 2) *
      ∏ p ∈ m.primeFactors.erase 2, psiNat χ f (p ^ m.factorization p) := by
  rw [psiNat_primeFactorProduct χ f hm]
  by_cases htwo : 2 ∈ m.primeFactors
  · exact (Finset.mul_prod_erase m.primeFactors
      (fun p : ℕ => psiNat χ f (p ^ m.factorization p)) htwo).symm
  · have hval : m.factorization 2 = 0 := by
      by_contra h
      exact htwo (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_two, Nat.dvd_of_factorization_pos h, hm⟩)
    simp only [hval, pow_zero, psiNat_one, one_mul, Finset.erase_eq_of_notMem htwo]

end DepthAspect.PrimeCoefficientProduct
