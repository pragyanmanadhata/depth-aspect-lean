import DepthAspect.SignedIndexOne
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Reindexing the literal signed trace into its dyadic strata

The reindexing starts with the actual divisor and trace sets in the general
formula. A common finite integer set is obtained by writing t=v*u; the
squarefree-gcd restriction is kept until the proved coefficient table is used.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- The literal finite interval for the quotient trace u=t/v. -/
noncomputable def quotientTraces (v m : ℕ) : Finset ℤ :=
  (closedTraces 1 m).filter (fun u => (v : ℤ) * u ^ 2 ≤ 4 * m)

@[simp] theorem mem_quotientTraces (v m : ℕ) (hv : 0 < v) (hm : 0 < m) (u : ℤ) :
    u ∈ quotientTraces v m ↔ (v : ℤ) * u ^ 2 ≤ 4 * m := by
  rw [quotientTraces, Finset.mem_filter, mem_closedTraces 1 m (by decide) hm]
  simp only [Nat.cast_one, mul_one]
  constructor
  · exact fun h => h.2
  · intro h
    have hvZ : (1 : ℤ) ≤ v := by exact_mod_cast hv
    refine ⟨?_, h⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr hvZ) (sq_nonneg u)]

/-- Exact substitution t=v*u in the original admissible trace sum. -/
theorem sum_admissibleTraces_reindex (M v m : ℕ) (hv : 0 < v) (hm : 0 < m)
    (F : ℤ → ℂ) :
    (∑ t ∈ admissibleTraces M v m, F t) =
      ∑ u ∈ quotientTraces v m,
        if Squarefree (Nat.gcd (u.natAbs ^ 2) (M / v))
        then F ((v : ℤ) * u) else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun u _ => (v : ℤ) * u)
  · intro u hu
    obtain ⟨hu, hs⟩ := Finset.mem_filter.mp hu
    have hb := (mem_quotientTraces v m hv hm u).mp hu
    rw [mem_admissibleTraces M v m hv hm]
    have hvZ : (0 : ℤ) < v := by exact_mod_cast hv
    refine ⟨?_, dvd_mul_right _ _, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left hb hvZ.le]
    · simpa only [Int.mul_ediv_cancel_left _ (ne_of_gt hvZ)] using hs
  · intro u hu w hw heq
    exact mul_left_cancel₀ (by exact_mod_cast ne_of_gt hv) heq
  · intro t ht
    obtain ⟨hb, htdiv, hs⟩ := (mem_admissibleTraces M v m hv hm t).mp ht
    obtain ⟨u, rfl⟩ := htdiv
    have hvZ : (0 : ℤ) < v := by exact_mod_cast hv
    refine ⟨u, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · rw [mem_quotientTraces v m hv hm]
      apply (mul_le_mul_iff_right₀ hvZ).mp
      nlinarith [hb]
    · simpa only [Int.mul_ediv_cancel_left _ (ne_of_gt hvZ)] using hs
  · intro u hu
    rfl

/-- A divisor sum over a smaller level can be embedded in the larger level,
with only its literal divisibility condition added. -/
theorem sum_divisors_embed (N M : ℕ) (hN : N ≠ 0) (hM : M ∣ N) (F : ℕ → ℂ) :
    (∑ v ∈ M.divisors, F v) =
      ∑ v ∈ N.divisors, if v ∣ M then F v else 0 := by
  classical
  have hM0 : M ≠ 0 := ne_zero_of_dvd_ne_zero hN hM
  have hs : M.divisors = N.divisors.filter (fun v => v ∣ M) := by
    ext v
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hv, _⟩
      exact ⟨⟨dvd_trans hv hM, hN⟩, hv⟩
    · rintro ⟨_, hv⟩
      exact ⟨hv, hM0⟩
  rw [hs, Finset.sum_filter]

/-- Descending dyadic indexing of an actual divisor sum. -/
theorem sum_divisors_two_pow_desc (n : ℕ) (F : ℕ → ℂ) :
    (∑ v ∈ (2 ^ n).divisors, F v) =
      ∑ b ∈ Finset.range (n + 1), F (2 ^ (n - b)) := by
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  change (∑ b ∈ Finset.range (n + 1), F (2 ^ b)) = _
  rw [← Finset.sum_range_reflect (fun b => F (2 ^ b))]
  apply Finset.sum_congr rfl
  intro b hb
  congr 2

/-- The four full-level elliptic sums have exactly the coefficient given by
the literal squarefree-gcd condition. This is the finite-sum bridge to (72). -/
theorem signed_elliptic_stratum_reindex (n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m)
    (F : ℕ → ℤ → ℂ) :
    (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      ∑ v ∈ (2 ^ (n - j)).divisors,
        ∑ t ∈ admissibleTraces (2 ^ (n - j)) v m, F v t) =
    ∑ b ∈ Finset.range (n + 1), ∑ u ∈ quotientTraces (2 ^ (n - b)) m,
      (SignedAdmissibility.actualStratumCoefficient n b u : ℂ) *
        F (2 ^ (n - b)) (((2 ^ (n - b) : ℕ) : ℤ) * u) := by
  classical
  have hlevel (j : ℕ) (hj : j ∈ Finset.range 4) :
      (∑ v ∈ (2 ^ (n - j)).divisors,
        ∑ t ∈ admissibleTraces (2 ^ (n - j)) v m, F v t) =
      ∑ b ∈ Finset.range (n + 1), ∑ u ∈ quotientTraces (2 ^ (n - b)) m,
        if (2 : ℕ) ^ (n - b) ∣ 2 ^ (n - j) ∧
          Squarefree (Nat.gcd (u.natAbs ^ 2) ((2 : ℕ) ^ (n - j) / 2 ^ (n - b)))
        then F (2 ^ (n - b)) (((2 ^ (n - b) : ℕ) : ℤ) * u) else 0 := by
    rw [sum_divisors_embed (2 ^ n) (2 ^ (n - j)) (by positivity)
      (pow_dvd_pow 2 (by omega)), sum_divisors_two_pow_desc]
    apply Finset.sum_congr rfl
    intro b hb
    rw [sum_admissibleTraces_reindex _ _ _ (by positivity) hm]
    by_cases hdiv : (2 : ℕ) ^ (n - b) ∣ 2 ^ (n - j)
    · simp only [hdiv, if_true, true_and]
    · simp [hdiv]
  have heq := Finset.sum_congr rfl (fun j hj => congrArg
    (fun z : ℂ => (Dyadic.alpha j : ℂ) * z) (hlevel j hj))
  rw [heq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  unfold SignedAdmissibility.actualStratumCoefficient
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

/-- The actual coefficient table annihilates every unlisted divisor. This
finite identity keeps both parity classes at N/4 explicit. -/
theorem coefficient_sum_four_strata (n : ℕ) (hn : 4 ≤ n)
    (U : ℕ → Finset ℤ) (F : ℕ → ℤ → ℂ) :
    (∑ b ∈ Finset.range (n + 1), ∑ u ∈ U b,
      (SignedAdmissibility.actualStratumCoefficient n b u : ℂ) * F b u) =
    (∑ u ∈ U 0, F 0 u) +
      (∑ u ∈ U 2, (if Odd u then (-1 : ℂ) else -2) * F 2 u) +
      (∑ u ∈ U 4, if Even u then F 4 u else 0) := by
  classical
  have hsub : ({0, 2, 4} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hrestrict :
      (∑ b ∈ Finset.range (n + 1), ∑ u ∈ U b,
        (SignedAdmissibility.actualStratumCoefficient n b u : ℂ) * F b u) =
      ∑ b ∈ ({0, 2, 4} : Finset ℕ), ∑ u ∈ U b,
        (SignedAdmissibility.actualStratumCoefficient n b u : ℂ) * F b u := by
    symm
    apply Finset.sum_subset hsub
    intro b hb hnot
    apply Finset.sum_eq_zero
    intro u hu
    have hb' : b ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hb0 : b ≠ 0 := by intro h; subst b; simp at hnot
    have hb2 : b ≠ 2 := by intro h; subst b; simp at hnot
    have hb4 : b ≠ 4 := by intro h; subst b; simp at hnot
    rw [SignedAdmissibility.actual_stratum_table n b (by omega) hb']
    simp [hb0, hb2, hb4]
  rw [hrestrict]
  have hexpand (G : ℕ → ℂ) :
      (∑ b ∈ ({0, 2, 4} : Finset ℕ), G b) = G 0 + G 2 + G 4 := by
    simp [Finset.sum_insert, add_assoc]
  rw [hexpand]
  have h0 (u : ℤ) : SignedAdmissibility.actualStratumCoefficient n 0 u = 1 := by
    rw [SignedAdmissibility.actual_stratum_table n 0 (by omega) (by omega)]
    simp
  have h2 (u : ℤ) : SignedAdmissibility.actualStratumCoefficient n 2 u =
      if Odd u then -1 else -2 := by
    rw [SignedAdmissibility.actual_stratum_table n 2 (by omega) (by omega)]
    simp
  have h4 (u : ℤ) : SignedAdmissibility.actualStratumCoefficient n 4 u =
      if Even u then 1 else 0 := by
    rw [SignedAdmissibility.actual_stratum_table n 4 (by omega) (by omega)]
    simp
  simp only [h0, h2, h4, Int.cast_one, one_mul]
  simp only [Int.cast_ite, Int.cast_neg, Int.cast_one, Int.cast_ofNat, Int.cast_zero,
    ite_mul, one_mul, zero_mul]

end DepthAspect.SignedSieve
