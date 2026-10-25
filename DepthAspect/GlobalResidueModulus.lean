import DepthAspect.GlobalResidueCoefficient
import DepthAspect.FiniteResidueCRT

/-!
# The actual coprime factorization of lcm(8,m²)

The finite CRT coordinates are one dyadic coordinate and one coordinate for
each odd prime dividing m. Their product is proved equal to the modulus in
(81), rather than being supplied as a decomposition hypothesis.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.GlobalResidueModulus
open GlobalResidueCoefficient

abbrev Index (m : ℕ) := Option (OddPrime m)

def localModulus (m : ℕ) : Index m → ℕ
  | none => 2 ^ twoExponent m
  | some p => p.val ^ (2 * m.factorization p.val)

instance localModulus_neZero (m : ℕ) (i : Index m) : NeZero (localModulus m i) := by
  cases i with
  | none => exact ⟨pow_ne_zero _ (by omega)⟩
  | some p => exact ⟨pow_ne_zero _ (Fact.out : p.val.Prime).ne_zero⟩

instance product_neZero (m : ℕ) : NeZero (∏ i, localModulus m i) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne _)⟩

private theorem odd_product_factorization (m p : ℕ) :
    (∏ r ∈ m.primeFactors.erase 2, r ^ (2 * m.factorization r)).factorization p =
      if p = 2 then 0 else 2 * m.factorization p := by
  rw [Nat.factorization_prod_apply (fun r hr => pow_ne_zero _
    (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hr).2).ne_zero)]
  have hterms : ∀ r ∈ m.primeFactors.erase 2,
      (r ^ (2 * m.factorization r)).factorization p =
        if r = p then 2 * m.factorization p else 0 := by
    intro r hr
    rw [(Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hr).2).factorization_pow]
    simp only [Finsupp.single_apply]
    split_ifs with h <;> simp_all
  rw [Finset.sum_congr rfl hterms]
  by_cases hp2 : p = 2
  · subst p
    simp
  · rw [if_neg hp2]
    by_cases hpm : p ∈ m.primeFactors
    · simp [Finset.sum_ite_eq', hpm, hp2]
    · have hv : m.factorization p = 0 := by
        exact Finsupp.notMem_support_iff.mp (by simpa using hpm)
      simp [hv]

/-- The finite CRT coordinates have exactly the paper's common modulus. -/
theorem product_eq_modulus {m : ℕ} (hm : m ≠ 0) :
    (∏ i : Index m, localModulus m i) = modulus m := by
  rw [Fintype.prod_option]
  change 2 ^ twoExponent m *
    (∏ p : OddPrime m, p.val ^ (2 * m.factorization p.val)) = modulus m
  rw [prod_oddPrime m (fun p : ℕ => p ^ (2 * m.factorization p))]
  have hpnonzero : (∏ p ∈ m.primeFactors.erase 2, p ^ (2 * m.factorization p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _
      (Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp hp).2).ne_zero)
  apply Nat.eq_of_factorization_eq (mul_ne_zero (pow_ne_zero _ (by omega)) hpnonzero)
    (modulus_ne_zero hm)
  intro p
  rw [Nat.factorization_mul (pow_ne_zero _ (by omega)) hpnonzero,
    Nat.prime_two.factorization_pow, Finsupp.add_apply, Finsupp.single_apply,
    odd_product_factorization, modulus,
    Nat.factorization_lcm (by norm_num) (pow_ne_zero _ hm),
    Finsupp.sup_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have h8 : (8 : ℕ).factorization p = if 2 = p then 3 else 0 := by
    change (2 ^ 3 : ℕ).factorization p = _
    rw [Nat.prime_two.factorization_pow, Finsupp.single_apply]
  rw [h8]
  by_cases hp : p = 2
  · subst p
    simp [twoExponent]
  · simp [hp, Ne.symm hp]

/-- Pairwise coprimality is proved from the actual distinct prime indices. -/
theorem localModulus_pairwise (m : ℕ) :
    Pairwise fun i j : Index m => Nat.Coprime (localModulus m i) (localModulus m j) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact False.elim (hij rfl)
    | some p =>
      exact ((Nat.coprime_primes Nat.prime_two (Fact.out : p.val.Prime)).mpr
        (Ne.symm (oddPrime_ne_two m p))).pow _ _
  | some p =>
    cases j with
    | none =>
      exact ((Nat.coprime_primes (Fact.out : p.val.Prime) Nat.prime_two).mpr
        (oddPrime_ne_two m p)).pow _ _
    | some r =>
      have hpr : p.val ≠ r.val := by
        intro h
        exact hij (congrArg some (Subtype.ext h))
      exact ((Nat.coprime_primes (Fact.out : p.val.Prime)
        (Fact.out : r.val.Prime)).mpr hpr).pow _ _

 theorem localModulus_dvd (m : ℕ) (i : Index m) : localModulus m i ∣ modulus m := by
  cases i with
  | none => exact twoPower_dvd m
  | some p => exact primeSquare_dvd m p.val

end DepthAspect.GlobalResidueModulus
