import DepthAspect.Dyadic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Ring.Int.Parity

/-!
# The literal squarefree-gcd restriction in the signed trace formula

The input predicate is the actual squarefreeness condition of (66), with
the integer quotient represented using its absolute value inside Nat.gcd.
The four surviving rows of (72) follow from that predicate, not from an
assumed parity table.
-/
namespace DepthAspect.SignedAdmissibility
open scoped BigOperators

/-- Squarefreeness of the actual dyadic gcd is exactly the parity restriction. -/
theorem squarefree_gcd_square_two_pow (u a : ℕ) :
    Squarefree (Nat.gcd (u ^ 2) (2 ^ a)) ↔ Odd u ∨ a ≤ 1 := by
  constructor
  · intro hs
    by_cases hu : Odd u
    · exact Or.inl hu
    · right
      by_contra ha
      have ha2 : 2 ≤ a := by omega
      have h2u : 2 ∣ u := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hu)
      have h4u : 2 * 2 ∣ u ^ 2 := by simpa only [pow_two] using mul_dvd_mul h2u h2u
      have h4a : 2 * 2 ∣ 2 ^ a := by simpa only [pow_two] using pow_dvd_pow 2 ha2
      exact (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two
        (Nat.dvd_gcd h4u h4a)
  · rintro (hu | ha)
    · have hc : Nat.Coprime (u ^ 2) (2 ^ a) := hu.coprime_two_right.pow 2 a
      rw [Nat.coprime_iff_gcd_eq_one.mp hc]
      exact squarefree_one
    · interval_cases a
      · simp
      · exact Nat.prime_two.squarefree.squarefree_of_dvd (by simpa using Nat.gcd_dvd_right (u ^ 2) 2)

/-- The same condition for the signed integer quotient t/v. -/
theorem squarefree_gcd_int_square_two_pow (u : ℤ) (a : ℕ) :
    Squarefree (Nat.gcd (u.natAbs ^ 2) (2 ^ a)) ↔ Odd u ∨ a ≤ 1 := by
  rw [squarefree_gcd_square_two_pow, Int.natAbs_odd]

theorem level_divisor_condition (n b j : ℕ) (hb : b ≤ n) (hj : j ≤ n) :
    (2 : ℕ) ^ (n - b) ∣ 2 ^ (n - j) ↔ j ≤ b := by
  rw [Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))]
  omega

theorem level_divisor_quotient (n b j : ℕ) (hb : b ≤ n) (hj : j ≤ b) :
    (2 : ℕ) ^ (n - j) / 2 ^ (n - b) = 2 ^ (b - j) := by
  rw [show n - j = (n - b) + (b - j) by omega, pow_add]
  exact Nat.mul_div_cancel_left _ (by positivity)

/-- An actual level-N/2^j summand at v=N/2^b has precisely the restriction
used in table (72), including the condition that v divide that level. -/
theorem actual_stratum_condition (n b j : ℕ) (hb : b ≤ n) (hj : j ≤ n) (u : ℤ) :
    ((2 : ℕ) ^ (n - b) ∣ 2 ^ (n - j) ∧
      Squarefree (Nat.gcd (u.natAbs ^ 2) ((2 : ℕ) ^ (n - j) / 2 ^ (n - b)))) ↔
      j ≤ b ∧ (Odd u ∨ b ≤ j + 1) := by
  rw [level_divisor_condition n b j hb hj]
  constructor
  · rintro ⟨hjb, hs⟩
    rw [level_divisor_quotient n b j hb hjb, squarefree_gcd_int_square_two_pow] at hs
    exact ⟨hjb, hs.imp_right (by omega)⟩
  · rintro ⟨hjb, hs⟩
    refine ⟨hjb, ?_⟩
    rw [level_divisor_quotient n b j hb hjb, squarefree_gcd_int_square_two_pow]
    exact hs.imp_right (by omega)

/-- The sieve coefficient before replacing the literal gcd by a parity table. -/
noncomputable def actualStratumCoefficient (n b : ℕ) (u : ℤ) : ℤ :=
  ∑ j ∈ Finset.range 4,
    if (2 : ℕ) ^ (n - b) ∣ 2 ^ (n - j) ∧
        Squarefree (Nat.gcd (u.natAbs ^ 2) ((2 : ℕ) ^ (n - j) / 2 ^ (n - b)))
    then Dyadic.alpha j else 0

theorem actualStratumCoefficient_eq (n b : ℕ) (hn : 3 ≤ n) (hb : b ≤ n) (u : ℤ) :
    actualStratumCoefficient n b u = Dyadic.stratumCoefficient b (decide (Odd u)) := by
  unfold actualStratumCoefficient Dyadic.stratumCoefficient
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  simp only [actual_stratum_condition n b j hb hjn, decide_eq_true_eq]

/-- All four nonzero rows and all zero rows of (72), for the actual predicate. -/
theorem actual_stratum_table (n b : ℕ) (hn : 3 ≤ n) (hb : b ≤ n) (u : ℤ) :
    actualStratumCoefficient n b u =
      if b = 0 then 1 else if b = 2 then (if Odd u then -1 else -2)
      else if b = 4 ∧ Even u then 1 else 0 := by
  rw [actualStratumCoefficient_eq n b hn hb u]
  by_cases hu : Odd u
  · simp only [hu, decide_true, Dyadic.stratum_odd, if_true]
    have hne : ¬ Even u := Int.not_even_iff_odd.mpr hu
    simp [hne]
  · have he : Even u := Int.not_odd_iff_even.mp hu
    simp [hu, he, Dyadic.stratum_even]

end DepthAspect.SignedAdmissibility
