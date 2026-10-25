import DepthAspect.LocalResidueAverages
import DepthAspect.SquarefreeCoefficientProduct
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The squarefree majorant for the computed odd residue means

The local means here are the literal finite residue averages. Their product
is bounded using the parity of the actual prime factorization of 2^b*u*v²,
with u squarefree and odd. CRT is the separate proved identification with the
full reduced-residue average; no multiplicativity of a twisted mean is assumed.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.OddMeanMajorant
open Finset

/-- Total extension of the actual local mean to natural prime indices. -/
def primeMean (p : ℕ) (t : ℤ) (b : ℕ) : ℝ :=
  if hp : p.Prime then @LocalResidueAverages.unitMean p ⟨hp⟩ b (t : ZMod p) else 0

/-- The actual product of the odd local averages. -/
def oddMean (m : ℕ) (t : ℤ) : ℝ :=
  ∏ p ∈ m.primeFactors.erase 2, primeMean p t (m.factorization p)

theorem abs_primeMean_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (t : ℤ) (b : ℕ) :
    |primeMean p t b| ≤ if Even b then 1 else 1 / ((p : ℝ) - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [primeMean, dif_pos hp] using LocalResidueAverages.abs_unitMean_le hp2 b (t : ZMod p)

 theorem factorization_odd_prime {p u v : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hu : u ≠ 0) (hv : v ≠ 0) (b : ℕ) :
    (2 ^ b * u * v ^ 2).factorization p = u.factorization p + 2 * v.factorization p := by
  rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ (by omega)) hu) (pow_ne_zero _ hv),
    Nat.factorization_mul (pow_ne_zero _ (by omega)) hu,
    Nat.prime_two.factorization_pow, Nat.factorization_pow]
  simp [Finsupp.add_apply, Finsupp.single_apply, hp2, Ne.symm hp2, mul_comm]

 theorem even_factorization_iff {p u v : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hu : Squarefree u) (hv : v ≠ 0) (b : ℕ) :
    Even ((2 ^ b * u * v ^ 2).factorization p) ↔ ¬ p ∣ u := by
  rw [factorization_odd_prime hp hp2 hu.ne_zero hv, Nat.even_iff]
  by_cases hpu : p ∣ u
  · rw [Nat.factorization_eq_one_of_squarefree hu hp hpu]
    simp [hpu]
  · rw [Nat.factorization_eq_zero_of_not_dvd hpu]
    simp [hpu]

/-- The pointwise squarefree bound (87), for the computed local-average product. -/
theorem abs_oddMean_le {u v : ℕ} (hu : Squarefree u) (huodd : Odd u)
    (hv : v ≠ 0) (b : ℕ) (t : ℤ) :
    |oddMean (2 ^ b * u * v ^ 2) t| ≤ 1 / (u.totient : ℝ) := by
  let m := 2 ^ b * u * v ^ 2
  let S := m.primeFactors.erase 2
  have hm : m ≠ 0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by omega)) hu.ne_zero)
    (pow_ne_zero _ hv)
  have hsub : u.primeFactors ⊆ S := by
    intro p hp
    have hpu := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro heq
      exact huodd.not_two_dvd_nat (heq ▸ hpu)
    have hud : u ∣ m := dvd_mul_of_dvd_left (dvd_mul_left u (2 ^ b)) (v ^ 2)
    exact Finset.mem_erase.mpr ⟨hp2, Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp, hpu.trans hud, hm⟩⟩
  have hloc (p : ℕ) (hp : p ∈ S) :
      |primeMean p t (m.factorization p)| ≤
        if p ∈ u.primeFactors then 1 / ((p : ℝ) - 1) else 1 := by
    obtain ⟨hp2, hpm⟩ := Finset.mem_erase.mp hp
    have hprime := Nat.prime_of_mem_primeFactors hpm
    have h := abs_primeMean_le hprime hp2 t (m.factorization p)
    have hmem : p ∈ u.primeFactors ↔ p ∣ u := by
      exact ⟨fun h => (Nat.mem_primeFactors.mp h).2.1,
        fun h => Nat.mem_primeFactors.mpr ⟨hprime, h, hu.ne_zero⟩⟩
    simp only [show Even (m.factorization p) ↔ ¬p ∣ u from
      even_factorization_iff hprime hp2 hu hv b] at h
    by_cases hpu : p ∣ u <;> simpa only [hmem, hpu, not_true_eq_false, not_false_eq_true,
      ↓reduceIte] using h
  calc
    _ = ∏ p ∈ S, |primeMean p t (m.factorization p)| := by
      exact Finset.abs_prod _ _
    _ ≤ ∏ p ∈ S, if p ∈ u.primeFactors then 1 / ((p : ℝ) - 1) else 1 :=
      Finset.prod_le_prod (fun p hp => abs_nonneg _) hloc
    _ = ∏ p ∈ u.primeFactors, 1 / ((p : ℝ) - 1) := by
      rw [← Finset.prod_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp (fun hp => hsub hp)
    _ = 1 / (u.totient : ℝ) := by
      rw [SquarefreeCoefficientProduct.totient_squarefree hu, Nat.cast_prod]
      simp only [one_div, ← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

end DepthAspect.OddMeanMajorant
