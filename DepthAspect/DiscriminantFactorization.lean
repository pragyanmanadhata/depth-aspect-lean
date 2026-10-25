import DepthAspect.FundamentalDiscriminant

/-!
# Actual fundamental-discriminant factorization

Every negative integer congruent to zero or one modulo four is factored
as a negative fundamental discriminant times a positive integral square.
This is derived from mathlib's squarefree decomposition of a positive
natural number; it is not an additional class-number assumption.
-/
namespace DepthAspect.FundamentalDiscriminant

/-- The general quadratic-discriminant classification, with an actual
positive natural conductor. -/
theorem exists_fundamental_factorization (D : ℤ) (hD : D < 0)
    (hmod : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ (d : ℤ) (f : ℕ), IsFundamental d ∧ d < 0 ∧ 0 < f ∧
      D = d * (f : ℤ) ^ 2 := by
  obtain ⟨a, b, ha, hb, hab, hsf⟩ :=
    Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr (ne_of_lt hD))
  have hcast : (b : ℤ) ^ 2 * a = -D := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hab
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, abs_of_neg hD] using h
  have heq : D = -(a : ℤ) * (b : ℤ) ^ 2 := by nlinarith
  have haneg : -(a : ℤ) < 0 := neg_neg_of_pos (by exact_mod_cast ha)
  have hsfa : Squarefree (-(a : ℤ)).natAbs := by simpa using hsf
  by_cases h1 : -(a : ℤ) % 4 = 1
  · exact ⟨-(a : ℤ), b, Or.inl ⟨h1, hsfa⟩, haneg, hb, heq⟩
  have h0 : -(a : ℤ) % 4 ≠ 0 := by
    intro hz
    have hzdiv : (4 : ℤ) ∣ -(a : ℤ) := (Int.dvd_iff_emod_eq_zero).mpr hz
    have hadiv : (4 : ℕ) ∣ a := by
      exact_mod_cast (dvd_neg.mp hzdiv)
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf) 2 Nat.prime_two hadiv
  have h23 : -(a : ℤ) % 4 = 2 ∨ -(a : ℤ) % 4 = 3 := by omega
  have hbeven : Even b := by
    rcases Nat.even_or_odd b with heven | hodd
    · exact heven
    · have hoddZ : Odd (b : ℤ) := by
        obtain ⟨z, hz⟩ := hodd
        exact ⟨(z : ℤ), by exact_mod_cast hz⟩
      have hs8 := odd_square_mod_eight hoddZ
      have hs4 : (b : ℤ) ^ 2 % 4 = 1 := by omega
      have hDmod : D % 4 = -(a : ℤ) % 4 := by
        rw [heq, Int.mul_emod, hs4, mul_one, Int.emod_emod]
      omega
  obtain ⟨f, hbf⟩ := hbeven
  refine ⟨4 * -(a : ℤ), f, Or.inr ⟨-(a : ℤ), rfl, hsfa, h23⟩,
    by linarith, by omega, ?_⟩
  rw [heq, hbf]
  push_cast
  ring

/-- Every strict elliptic discriminant of the paper has the standard
fundamental-conductor factorization. -/
theorem elliptic_fundamental_factorization (t m : ℤ) (ht : t ^ 2 < 4 * m) :
    ∃ (d : ℤ) (f : ℕ), IsFundamental d ∧ d < 0 ∧ 0 < f ∧
      t ^ 2 - 4 * m = d * (f : ℤ) ^ 2 := by
  apply exists_fundamental_factorization _ (by omega)
  have htmod : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases htmod with h | h | h | h <;>
    norm_num [pow_two, Int.sub_emod, Int.mul_emod, h]

/-- The positive-discriminant analogue, including square discriminants
whose fundamental part is one. -/
theorem exists_positive_fundamental_factorization (D : ℤ) (hD : 0 < D)
    (hmod : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ (d : ℤ) (f : ℕ), IsFundamental d ∧ 0 < d ∧ 0 < f ∧
      D = d * (f : ℤ) ^ 2 := by
  obtain ⟨a, b, ha, hb, hab, hsf⟩ :=
    Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr (ne_of_gt hD))
  have hcast : (b : ℤ) ^ 2 * a = D := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hab
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, abs_of_pos hD] using h
  have heq : D = (a : ℤ) * (b : ℤ) ^ 2 := by nlinarith
  have hapos : (0 : ℤ) < a := by exact_mod_cast ha
  have hsfa : Squarefree (a : ℤ).natAbs := by simpa using hsf
  by_cases h1 : (a : ℤ) % 4 = 1
  · exact ⟨(a : ℤ), b, Or.inl ⟨h1, hsfa⟩, hapos, hb, heq⟩
  have h0 : (a : ℤ) % 4 ≠ 0 := by
    intro hz
    have hadiv : (4 : ℕ) ∣ a := by exact_mod_cast ((Int.dvd_iff_emod_eq_zero).mpr hz)
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf) 2 Nat.prime_two hadiv
  have h23 : (a : ℤ) % 4 = 2 ∨ (a : ℤ) % 4 = 3 := by omega
  have hbeven : Even b := by
    rcases Nat.even_or_odd b with heven | hodd
    · exact heven
    · have hoddZ : Odd (b : ℤ) := by
        obtain ⟨z, hz⟩ := hodd
        exact ⟨(z : ℤ), by exact_mod_cast hz⟩
      have hs8 := odd_square_mod_eight hoddZ
      have hs4 : (b : ℤ) ^ 2 % 4 = 1 := by omega
      have hDmod : D % 4 = (a : ℤ) % 4 := by
        rw [heq, Int.mul_emod, hs4, mul_one, Int.emod_emod]
      omega
  obtain ⟨f, hbf⟩ := hbeven
  refine ⟨4 * (a : ℤ), f, Or.inr ⟨(a : ℤ), rfl, hsfa, h23⟩,
    by positivity, by omega, ?_⟩
  rw [heq, hbf]
  push_cast
  ring

/-- Sign-independent factorization for the residue calculations; zero
remains a separate explicit convention. -/
theorem exists_nonzero_fundamental_factorization (D : ℤ) (hD : D ≠ 0)
    (hmod : D % 4 = 0 ∨ D % 4 = 1) :
    ∃ (d : ℤ) (f : ℕ), IsFundamental d ∧ 0 < f ∧
      D = d * (f : ℤ) ^ 2 := by
  rcases lt_or_gt_of_ne hD with hn | hp
  · obtain ⟨d, f, hd, _, hf, heq⟩ := exists_fundamental_factorization D hn hmod
    exact ⟨d, f, hd, hf, heq⟩
  · obtain ⟨d, f, hd, _, hf, heq⟩ := exists_positive_fundamental_factorization D hp hmod
    exact ⟨d, f, hd, hf, heq⟩

end DepthAspect.FundamentalDiscriminant
