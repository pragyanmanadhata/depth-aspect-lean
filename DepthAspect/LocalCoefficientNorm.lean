import DepthAspect.GlobalResidueCoefficient

/-!
# Pointwise bounds for the literal local residue functions

Every stratum takes a quadratic-symbol value of norm at most one, and the
strata are disjoint. These facts prove the bound on all residue representatives,
including positive and zero discriminants, without introducing an L-value.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.LocalCoefficientNorm
open FundamentalDiscriminant OddDiscriminantValues DyadicCoefficientFourier
open GlobalResidueCoefficient FiniteCharacterFourier

private theorem norm_sparse_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hbound : ∀ i ∈ s, ‖f i‖ ≤ 1)
    (hunique : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → i = j) :
    ‖∑ i ∈ s, f i‖ ≤ 1 := by
  by_cases hex : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := hex
    rw [Finset.sum_eq_single_of_mem i hi]
    · exact hbound i hi
    · intro j hj hji
      by_contra hfj
      exact hji (hunique j hj i hi hfj hfi)
  · have hz : ∀ i ∈ s, f i = 0 := by simpa using hex
    simp [Finset.sum_eq_zero hz]

 theorem norm_twoSymbol_pow_le (D : ℤ) (j : ℕ) : ‖(twoSymbol D : ℂ) ^ j‖ ≤ 1 := by
  rcases twoSymbol_cases D with h | h | h
  · simp only [h, Int.cast_zero]
    cases j <;> norm_num
  · simp [h]
  · simp [h]

 theorem norm_legendre_pow_le {p : ℕ} [Fact p.Prime] (D : ℤ) (j : ℕ) :
    ‖(legendreSym p D : ℂ) ^ j‖ ≤ 1 := by
  by_cases hz : (D : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p D).mpr hz]
    cases j <;> norm_num
  · rcases legendreSym.eq_one_or_neg_one p hz with h | h <;> simp [h]

 theorem norm_localCoefficient_le {p : ℕ} [Fact p.Prime] (D : ℤ) (j : ℕ) :
    ‖localCoefficient p D j‖ ≤ 1 := by
  by_cases hz : D = 0
  · simp [localCoefficient, hz]
  by_cases hj : j ≤ D.natAbs.factorization p / 2
  · simp [localCoefficient, hz, hj]
  by_cases hv : D.natAbs.factorization p % 2 = 0
  · simpa only [localCoefficient, if_neg hz, if_neg hj, if_pos hv] using
      norm_legendre_pow_le (p := p) (D / (p : ℤ) ^ (2 * (D.natAbs.factorization p / 2)))
        (j - D.natAbs.factorization p / 2)
  · simp [localCoefficient, hz, hj, hv]

private def terminalAndStrata (z : ℤ) (j : ℕ) : Option (Fin j) → ℂ
  | none => if (2 : ℤ) ^ (2 * j) ∣ z then 1 else 0
  | some a => if z.natAbs.factorization 2 = 2 * a.val ∧
      (z / (2 : ℤ) ^ (2 * a.val)) % 4 = 1 then
      (twoSymbol (z / (2 : ℤ) ^ (2 * a.val)) : ℂ) ^ (j - a.val - 1) else 0

private theorem terminalAndStrata_bound (z : ℤ) (j : ℕ) (i : Option (Fin j)) :
    ‖terminalAndStrata z j i‖ ≤ 1 := by
  cases i with
  | none => simp only [terminalAndStrata]; split_ifs <;> norm_num
  | some a =>
    simp only [terminalAndStrata]
    split_ifs <;> first | exact norm_twoSymbol_pow_le _ _ | norm_num

private theorem stratum_nonzero {z : ℤ} {j : ℕ} (a : Fin j)
    (h : terminalAndStrata z j (some a) ≠ 0) :
    z ≠ 0 ∧ z.natAbs.factorization 2 = 2 * a.val := by
  have hc : z.natAbs.factorization 2 = 2 * a.val ∧
      (z / (2 : ℤ) ^ (2 * a.val)) % 4 = 1 := by
    by_contra hn
    exact h (by simp [terminalAndStrata, hn])
  refine ⟨?_, hc.1⟩
  intro hz
  simp [hz] at hc

private theorem terminalAndStrata_unique (z : ℤ) (j : ℕ)
    (i k : Option (Fin j)) (hi : terminalAndStrata z j i ≠ 0)
    (hk : terminalAndStrata z j k ≠ 0) : i = k := by
  have hcross : ∀ a : Fin j, terminalAndStrata z j none ≠ 0 →
      terminalAndStrata z j (some a) ≠ 0 → False := by
    intro a hnone hsome
    obtain ⟨hz, hv⟩ := stratum_nonzero a hsome
    have hd : (2 : ℤ) ^ (2 * j) ∣ z := by
      by_contra hn
      exact hnone (by simp [terminalAndStrata, hn])
    have hdn : 2 ^ (2 * j) ∣ z.natAbs := by
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hd
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization
      (by simpa using hz : z.natAbs ≠ 0)).mp hdn
    have ha := a.isLt
    omega
  cases i with
  | none =>
    cases k with
    | none => rfl
    | some a => exact False.elim (hcross a hi hk)
  | some a =>
    cases k with
    | none => exact False.elim (hcross a hk hi)
    | some b =>
      apply congrArg some
      apply Fin.ext
      have ha := (stratum_nonzero a hi).2
      have hb := (stratum_nonzero b hk).2
      omega

/-- The terminal term and every finite valuation stratum are mutually exclusive. -/
theorem norm_localEven_le (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ)
    (x : (ZMod (2 ^ n))ˣ) : ‖localEven n j hn u x‖ ≤ 1 := by
  let X : ℤ := ((x : ZMod (2 ^ n)).val : ℕ)
  have hx : (X : ZMod (2 ^ n)) = x := by simp [X]
  have heq : localEven n j hn u x =
      ∑ i : Option (Fin j), terminalAndStrata (u ^ 2 - X) j i := by
    rw [Fintype.sum_option]
    unfold localEven
    rw [inflatedTerminal_eq n j hn u X x hx]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    exact inflatedStratum_eq n j hn u X a x hx
  rw [heq]
  exact norm_sparse_sum Finset.univ _ (fun i _ => terminalAndStrata_bound _ j i)
    (fun i _ k _ => terminalAndStrata_unique _ j i k)

 theorem norm_localAtTwo_le (n j : ℕ) (hn : 2 * j ≤ n) (t : ℤ)
    (x : (ZMod (2 ^ n))ˣ) : ‖localAtTwo n j hn t x‖ ≤ 1 := by
  unfold localAtTwo
  split_ifs
  · exact norm_localEven_le n j hn _ x
  · simp

/-- The actual global coefficient is bounded at every reduced residue class. -/
theorem norm_coefficientFunction_le (m : ℕ) (t : ℤ)
    (x : (ZMod (modulus m))ˣ) : ‖coefficientFunction m t x‖ ≤ 1 := by
  rw [coefficientFunction, norm_mul, norm_prod]
  have htwo : ‖twoFactor m t x‖ ≤ 1 := norm_localAtTwo_le _ _ _ _ _
  have hodd : ∀ p : OddPrime m, ‖oddFactor m t p x‖ ≤ 1 := by
    intro p
    exact norm_localCoefficient_le _ _
  exact (mul_le_mul htwo (Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun p _ => hodd p)) (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    zero_le_one).trans_eq (mul_one 1)

/-- A normalized principal coefficient of a bounded function is bounded. -/
theorem norm_principal_le_one {q : ℕ} [NeZero q] (g : (ZMod q)ˣ → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) : ‖coefficient g 1‖ ≤ 1 := by
  rw [coefficient_principal, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
    (0 : ℝ) < Fintype.card (ZMod q)ˣ)).mpr
  calc
    _ ≤ ∑ x : (ZMod q)ˣ, ‖g x‖ := norm_sum_le _ _
    _ ≤ ∑ x : (ZMod q)ˣ, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hg x)
    _ = _ := by simp

end DepthAspect.LocalCoefficientNorm
