import DepthAspect.SignedIndexOne
import DepthAspect.SignedAuxiliary
import DepthAspect.TraceTrigonometry

/-!
# Summing the literal index-one signed trace indices

This module passes from the proved admissible-pair classification to an
actual finite sum identity. In particular, zero-discriminant terms are
retained in the constant six-pair part until their sieve cancellation.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

noncomputable def admissiblePairs (M m : ℕ) : Finset (ℕ × ℤ) :=
  M.divisors.biUnion (fun v => (admissibleTraces M v m).image (fun t => (v, t)))

@[simp] theorem mem_admissiblePairs (M m v : ℕ) (t : ℤ) :
    (v, t) ∈ admissiblePairs M m ↔
      v ∈ M.divisors ∧ t ∈ admissibleTraces M v m := by
  classical
  simp [admissiblePairs]

/-- No duplicate pairs are introduced in combining the divisor sums. -/
theorem sum_admissiblePairs (M m : ℕ) (F : ℕ × ℤ → ℂ) :
    (∑ p ∈ admissiblePairs M m, F p) =
      ∑ v ∈ M.divisors, ∑ t ∈ admissibleTraces M v m, F (v, t) := by
  classical
  have hd : Set.PairwiseDisjoint (↑M.divisors)
      (fun v => (admissibleTraces M v m).image (fun t => (v, t))) := by
    intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hq
    exact hne (by simpa using (congrArg Prod.fst heq).symm)
  unfold admissiblePairs
  rw [Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_image]
  intro x hx y hy heq
  exact (Prod.mk.inj heq).2

/-- The exact six nonzero pairs, including the two zero-discriminant endpoints. -/
def indexOneNonzeroPairs : Finset (ℕ × ℤ) :=
  {(1, 1), (1, -1), (2, 2), (2, -2), (4, 4), (4, -4)}

@[simp] theorem mem_indexOneNonzeroPairs (v : ℕ) (t : ℤ) :
    (v, t) ∈ indexOneNonzeroPairs ↔
      (v = 1 ∧ (t = 1 ∨ t = -1)) ∨
      (v = 2 ∧ (t = 2 ∨ t = -2)) ∨
      (v = 4 ∧ (t = 4 ∨ t = -4)) := by
  simp only [indexOneNonzeroPairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  tauto

/-- The actual zero-trace pairs are precisely the two largest divisors. -/
theorem zero_index_one_pairs (h v : ℕ) (hh : 2 ≤ h) :
    (v, (0 : ℤ)) ∈ admissiblePairs (2 ^ h) 1 ↔
      v = 2 ^ h ∨ v = 2 ^ (h - 1) := by
  rw [mem_admissiblePairs]
  constructor
  · rintro ⟨hv, hadm⟩
    obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.mem_divisors.mp hv).1
    have hdiff := (zero_index_one_divisors h b hb).mp hadm
    have heq : b = h ∨ b = h - 1 := by omega
    rcases heq with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    all_goals
      constructor
      · exact Nat.mem_divisors.mpr ⟨pow_dvd_pow 2 (by omega), by positivity⟩
      · apply (zero_index_one_divisors h _ (by omega)).mpr
        omega

/-- Exact pair-set decomposition, proved from literal conditions. -/
theorem admissiblePairs_index_one (h : ℕ) (hh : 2 ≤ h) :
    admissiblePairs (2 ^ h) 1 =
      indexOneNonzeroPairs ∪ {(2 ^ h, 0), (2 ^ (h - 1), 0)} := by
  classical
  ext ⟨v, t⟩
  by_cases ht : t = 0
  · subst t
    rw [zero_index_one_pairs h v hh]
    simp [indexOneNonzeroPairs]
  · have hc := nonzero_index_one_pairs h v hh t ht
    rw [mem_admissiblePairs, hc, Finset.mem_union, mem_indexOneNonzeroPairs]
    simp [ht]

/-- The literal double sum splits into the fixed six-pair contribution and
the two zero-trace terms, without discarding H(0). -/
theorem index_one_sum (h : ℕ) (hh : 2 ≤ h) (F : ℕ × ℤ → ℂ) :
    (∑ v ∈ (2 ^ h).divisors, ∑ t ∈ admissibleTraces (2 ^ h) v 1, F (v, t)) =
      (∑ p ∈ indexOneNonzeroPairs, F p) + F (2 ^ h, 0) + F (2 ^ (h - 1), 0) := by
  classical
  rw [← sum_admissiblePairs, admissiblePairs_index_one h hh]
  have hd : Disjoint indexOneNonzeroPairs {(2 ^ h, (0 : ℤ)), (2 ^ (h - 1), 0)} := by
    apply Finset.disjoint_left.mpr
    rintro ⟨v, t⟩ hp hz
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hz
    rcases hz with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> norm_num [indexOneNonzeroPairs] at hp
  have hne : (2 ^ h, (0 : ℤ)) ≠ (2 ^ (h - 1), 0) := by
    intro heq
    have he := (Prod.mk.inj heq).1
    have hexp := (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))) he
    omega
  rw [Finset.sum_union hd, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  ring

end DepthAspect.SignedSieve
