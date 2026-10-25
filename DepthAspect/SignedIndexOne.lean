import DepthAspect.SignedSieve
import Mathlib.Tactic.IntervalCases

/-!
# Actual nonzero index-one terms in the signed trace

For M=2^h with h≥2 the literal divisibility, closed elliptic bound, and
squarefree-gcd condition admit exactly (v,t)=(1,±1),(2,±2),(4,±4).
The zero-discriminant endpoint (4,±4) is retained.
-/
namespace DepthAspect.SignedSieve

/-- Membership in the finite closed elliptic interval is the displayed
quadratic inequality at positive v*m. -/
theorem mem_closedTraces (v m : ℕ) (hv : 0 < v) (hm : 0 < m) (t : ℤ) :
    t ∈ closedTraces v m ↔ t ^ 2 ≤ 4 * (v : ℤ) * m := by
  simp only [closedTraces, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro ht
    have hvZ : (0 : ℤ) < v := by exact_mod_cast hv
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
    have hvm : (1 : ℤ) ≤ (v : ℤ) * m := by
      have hpos := mul_pos hvZ hmZ
      omega
    refine ⟨⟨?_, ?_⟩, ht⟩ <;> nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]

theorem mem_admissibleTraces (M v m : ℕ) (hv : 0 < v) (hm : 0 < m) (t : ℤ) :
    t ∈ admissibleTraces M v m ↔
      t ^ 2 ≤ 4 * (v : ℤ) * m ∧ (v : ℤ) ∣ t ∧
        Squarefree (Nat.gcd ((t / (v : ℤ)).natAbs ^ 2) (M / v)) := by
  simp only [admissibleTraces, Finset.mem_filter, mem_closedTraces v m hv hm]

/-- Exact classification of the nonzero admissible pairs at index one. -/
theorem nonzero_index_one_pairs (h v : ℕ) (hh : 2 ≤ h) (t : ℤ) (ht : t ≠ 0) :
    (v ∈ (2 ^ h).divisors ∧ t ∈ admissibleTraces (2 ^ h) v 1) ↔
      (v = 1 ∧ (t = 1 ∨ t = -1)) ∨
      (v = 2 ∧ (t = 2 ∨ t = -2)) ∨
      (v = 4 ∧ (t = 4 ∨ t = -4)) := by
  constructor
  · rintro ⟨hv, hadm⟩
    have hvdiv := (Nat.mem_divisors.mp hv).1
    obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hvdiv
    have hvpos : (0 : ℤ) < (2 ^ b : ℕ) := by positivity
    obtain ⟨hbound, hdiv, hs⟩ :=
      (mem_admissibleTraces (2 ^ h) (2 ^ b) 1 (by positivity) (by decide) t).mp hadm
    obtain ⟨u, hu⟩ := hdiv
    have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu; exact ht hu
    have hu1 : (1 : ℤ) ≤ u ^ 2 := by nlinarith [sq_pos_of_ne_zero hu0]
    have hsmall : ((2 ^ b : ℕ) : ℤ) * u ^ 2 ≤ 4 := by
      apply (mul_le_mul_iff_right₀ hvpos).mp
      rw [hu] at hbound
      norm_num only [Nat.cast_one] at hbound
      nlinarith [hbound]
    have hv4 : ((2 ^ b : ℕ) : ℤ) ≤ 4 := by
      nlinarith [mul_nonneg hvpos.le (sub_nonneg.mpr hu1)]
    have hb2 : b ≤ 2 := by
      have hp : (2 : ℕ) ^ b ≤ 2 ^ 2 := by norm_num; exact_mod_cast hv4
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hp
    interval_cases b
    · have hs' : Squarefree (Nat.gcd (t.natAbs ^ 2) (2 ^ h)) := by simpa using hs
      have hbound' : t ^ 2 ≤ 4 := by simpa using hbound
      have hodd : Odd t := by
        have hf := (SignedAdmissibility.squarefree_gcd_int_square_two_pow t h).mp hs'
        exact hf.resolve_right (by omega)
      have htl : -2 ≤ t := by nlinarith
      have htr : t ≤ 2 := by nlinarith
      refine Or.inl ⟨by norm_num, ?_⟩
      obtain ⟨z, hz⟩ := hodd
      have hzl : -1 ≤ z := by omega
      have hzr : z ≤ 0 := by omega
      interval_cases z
      · right; omega
      · left; omega
    · have hsmall' : (2 : ℤ) * u ^ 2 ≤ 4 := by simpa using hsmall
      have hu' : t = 2 * u := by simpa using hu
      have hul : -1 ≤ u := by nlinarith
      have hur : u ≤ 1 := by nlinarith
      interval_cases u <;> simp_all
    · have hsmall' : (4 : ℤ) * u ^ 2 ≤ 4 := by simpa using hsmall
      have hu' : t = 4 * u := by simpa using hu
      have hul : -1 ≤ u := by nlinarith
      have hur : u ≤ 1 := by nlinarith
      interval_cases u <;> simp_all
  · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩)
    all_goals
      constructor
      · apply Nat.mem_divisors.mpr
        refine ⟨?_, by positivity⟩
        first
        | exact one_dvd _
        | exact dvd_pow_self 2 (by omega : h ≠ 0)
        | have h4 : (2 : ℕ) ^ 2 ∣ 2 ^ h :=
            (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mpr hh
          norm_num only [show (2 : ℕ) ^ 2 = 4 by norm_num] at h4
          exact h4
      · rw [mem_admissibleTraces _ _ _ (by decide) (by decide)]
        norm_num

/-- At t=0 the literal gcd restriction leaves only the two top divisors. -/
theorem zero_index_one_divisors (h b : ℕ) (hb : b ≤ h) :
    (0 : ℤ) ∈ admissibleTraces (2 ^ h) (2 ^ b) 1 ↔ h - b ≤ 1 := by
  rw [mem_admissibleTraces _ _ _ (by positivity) (by decide)]
  have hquot : (2 ^ h : ℕ) / 2 ^ b = 2 ^ (h - b) := by
    calc
      (2 ^ h : ℕ) / 2 ^ b = (2 ^ b * 2 ^ (h - b)) / 2 ^ b := by
        congr 1
        rw [← pow_add, Nat.add_sub_of_le hb]
      _ = 2 ^ (h - b) := Nat.mul_div_cancel_left _ (by positivity)
  have hbound : (0 : ℤ) ^ 2 ≤ 4 * ((2 ^ b : ℕ) : ℤ) * 1 := by
    norm_num only [zero_pow (by decide : 2 ≠ 0), mul_one]
    positivity
  simp only [hbound, true_and, dvd_zero, zero_div, Int.natAbs_zero,
    zero_pow (by decide : 2 ≠ 0), Nat.gcd_zero_left, hquot]
  simpa using SignedAdmissibility.squarefree_gcd_square_two_pow 0 (h - b)

end DepthAspect.SignedSieve
