import DepthAspect.CoefficientDecomposition

/-! The literal uniqueness assertion preceding (87). The tail proof needs
only a selected reconstruction injection; this module also proves that every
admissible odd-square/squarefree triple is that selected triple. -/
noncomputable section
namespace DepthAspect.CoefficientUniqueness
open CoefficientDecomposition

private theorem factorization_product (b : ℕ) {u v : ℕ}
    (hu : u ≠ 0) (hv : v ≠ 0) (p : ℕ) :
    (2 ^ b * u * v ^ 2).factorization p =
      (if 2 = p then b else 0) + u.factorization p + 2 * v.factorization p := by
  rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ (by omega)) hu)
      (pow_ne_zero _ hv), Nat.factorization_mul (pow_ne_zero _ (by omega)) hu,
    Nat.prime_two.factorization_pow, Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.smul_apply, smul_eq_mul]

/-- Equality of two admissible representations forces equality of all three
parameters. Squarefree factorization exponents are zero or one, so their
parity determines the squarefree part after removing the power of two. -/
theorem decomposition_unique {b b' u u' v v' : ℕ}
    (hu : Squarefree u) (hu' : Squarefree u') (huodd : Odd u) (huodd' : Odd u')
    (hv : v ≠ 0) (hv' : v' ≠ 0) (hvodd : Odd v) (hvodd' : Odd v')
    (h : 2 ^ b * u * v ^ 2 = 2 ^ b' * u' * v' ^ 2) :
    b = b' ∧ u = u' ∧ v = v' := by
  have hb := congrArg (fun n : ℕ => n.factorization 2) h
  rw [factorization_product b hu.ne_zero hv, factorization_product b' hu'.ne_zero hv',
    if_pos rfl, Nat.factorization_eq_zero_of_not_dvd huodd.not_two_dvd_nat,
    Nat.factorization_eq_zero_of_not_dvd huodd'.not_two_dvd_nat,
    Nat.factorization_eq_zero_of_not_dvd hvodd.not_two_dvd_nat,
    Nat.factorization_eq_zero_of_not_dvd hvodd'.not_two_dvd_nat] at hb
  simp only [↓reduceIte, add_zero, mul_zero] at hb
  have hparts (p : ℕ) : u.factorization p = u'.factorization p ∧
      v.factorization p = v'.factorization p := by
    have hp := congrArg (fun n : ℕ => n.factorization p) h
    rw [factorization_product b hu.ne_zero hv, factorization_product b' hu'.ne_zero hv',
      hb] at hp
    have hu1 := hu.natFactorization_le_one p
    have hu1' := hu'.natFactorization_le_one p
    omega
  exact ⟨hb, Nat.eq_of_factorization_eq hu.ne_zero hu'.ne_zero (fun p => (hparts p).1),
    Nat.eq_of_factorization_eq hv hv' (fun p => (hparts p).2)⟩

/-- Reconstruction is injective on the triples whose square part is odd. -/
theorem reconstruct_injective_on_odd {i j : Indices}
    (hi : Odd (i.2.2 + 1)) (hj : Odd (j.2.2 + 1))
    (h : reconstruct i = reconstruct j) : i = j := by
  obtain ⟨hb, hu, hv⟩ := decomposition_unique i.2.1.property.1 j.2.1.property.1
    i.2.1.property.2 j.2.1.property.2 (by omega) (by omega) hi hj h
  exact Prod.ext hb (Prod.ext (Subtype.ext hu) (Nat.add_right_cancel hv))

/-- The exact unique representation used before equation (87). -/
theorem exists_unique_decomposition (n : ℕ) :
    ∃! i : Indices, reconstruct i = n + 1 ∧ Odd (i.2.2 + 1) := by
  refine ⟨decompose n, ⟨reconstruct_decompose n, decompose_odd_square_part n⟩, ?_⟩
  intro i hi
  exact reconstruct_injective_on_odd hi.2 (decompose_odd_square_part n)
    (hi.1.trans (reconstruct_decompose n).symm)

/-- Every positive integer has the unique representation stated in the paper. -/
theorem exists_unique_positive_decomposition (m : ℕ) (hm : 0 < m) :
    ∃! i : Indices, reconstruct i = m ∧ Odd (i.2.2 + 1) := by
  simpa only [Nat.sub_add_cancel hm] using exists_unique_decomposition (m - 1)

end DepthAspect.CoefficientUniqueness
