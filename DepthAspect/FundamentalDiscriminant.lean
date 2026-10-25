import DepthAspect.LocalRoots
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Fundamental-discriminant arithmetic used in the signed trace

The predicate is the usual squarefree congruence definition. The symbol at
two is mathlib's actual quadratic residue character modulo eight. Local
valuation consequences are proved from the definition.
-/
namespace DepthAspect.FundamentalDiscriminant

/-- The standard congruence-and-squarefreeness definition. -/
def IsFundamental (d : ℤ) : Prop :=
  (d % 4 = 1 ∧ Squarefree d.natAbs) ∨
    ∃ d₀ : ℤ, d = 4 * d₀ ∧ Squarefree d₀.natAbs ∧ (d₀ % 4 = 2 ∨ d₀ % 4 = 3)

/-- The actual quadratic symbol (d/2), including zero at even d. -/
def twoSymbol (d : ℤ) : ℤ := ZMod.χ₈ (d : ZMod 8)

theorem twoSymbol_eq (d : ℤ) : twoSymbol d =
    if d % 2 = 0 then 0 else if d % 8 = 1 ∨ d % 8 = 7 then 1 else -1 :=
  ZMod.χ₈_int_eq_if_mod_eight d

theorem twoSymbol_cases (d : ℤ) :
    twoSymbol d = 0 ∨ twoSymbol d = 1 ∨ twoSymbol d = -1 := by
  rw [twoSymbol_eq]
  split_ifs <;> simp

theorem abs_twoSymbol_le_one (d : ℤ) : |twoSymbol d| ≤ 1 := by
  rcases twoSymbol_cases d with h | h | h <;> norm_num [h]

theorem twoSymbol_even {d : ℤ} (hd : Even d) : twoSymbol d = 0 := by
  rw [twoSymbol_eq, if_pos]
  exact Int.even_iff.mp hd

theorem twoSymbol_mod_one {d : ℤ} (hd : d % 8 = 1) : twoSymbol d = 1 := by
  rw [twoSymbol_eq]
  have hodd : d % 2 ≠ 0 := by omega
  simp [hd, hodd]

theorem twoSymbol_mod_five {d : ℤ} (hd : d % 8 = 5) : twoSymbol d = -1 := by
  rw [twoSymbol_eq]
  have hodd : d % 2 ≠ 0 := by omega
  simp [hd, hodd]

theorem IsFundamental.ne_zero {d : ℤ} (hd : IsFundamental d) : d ≠ 0 := by
  intro hz
  rcases hd with ⟨hmod, _⟩ | ⟨d₀, heq, _, hmod⟩
  · norm_num [hz] at hmod
  · have hzero : d₀ = 0 := by omega
    norm_num [hzero] at hmod

/-- A fundamental discriminant has no odd-prime square factor. -/
theorem IsFundamental.not_prime_square_dvd_natAbs {d : ℤ} (hd : IsFundamental d)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p * p ∣ d.natAbs := by
  intro hdiv
  rcases hd with ⟨_, hs⟩ | ⟨d₀, rfl, hs, _⟩
  · exact (Nat.squarefree_iff_prime_squarefree.mp hs) p hp hdiv
  · have hc : Nat.Coprime (p * p) 4 := by
      simpa only [pow_two, show (2 : ℕ) * 2 = 4 by norm_num] using
        (hp.odd_of_ne_two hp2).coprime_two_right.pow 2 2
    have hdiv' : p * p ∣ 4 * d₀.natAbs := by simpa only [Int.natAbs_mul, show (4 : ℤ).natAbs = 4 by norm_num] using hdiv
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) p hp (hc.dvd_of_dvd_mul_left hdiv')

theorem IsFundamental.not_prime_square_dvd {d : ℤ} (hd : IsFundamental d)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ^ 2 ∣ d := by
  intro hdiv
  apply hd.not_prime_square_dvd_natAbs hp hp2
  apply Int.natCast_dvd.mp
  simpa only [Nat.cast_mul, pow_two] using hdiv

/-- The exponent of every odd prime in a fundamental discriminant is at most one. -/
theorem IsFundamental.odd_prime_factorization_le_one {d : ℤ} (hd : IsFundamental d)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : d.natAbs.factorization p ≤ 1 := by
  by_contra hn
  have hdabs : d.natAbs ≠ 0 := by
    intro hzero
    exact hd.ne_zero (Int.natAbs_eq_zero.mp hzero)
  have hpow : p ^ 2 ∣ d.natAbs :=
    (hp.pow_dvd_iff_le_factorization hdabs).mpr (by omega)
  exact hd.not_prime_square_dvd_natAbs hp hp2 (by simpa only [pow_two] using hpow)

/-- Odd fundamental discriminants are one modulo four. -/
theorem IsFundamental.odd_mod_four {d : ℤ} (hd : IsFundamental d) (hodd : Odd d) : d % 4 = 1 := by
  rcases hd with ⟨hmod, _⟩ | ⟨d₀, rfl, _, _⟩
  · exact hmod
  · have heven : Even (4 * d₀) := ⟨2 * d₀, by ring⟩
    exact False.elim ((Int.not_even_iff_odd.mpr hodd) heven)

/-- Any odd square is one modulo eight, using the already checked local-root lemma. -/
theorem odd_square_mod_eight {f : ℤ} (hf : Odd f) : f ^ 2 % 8 = 1 := by
  have h := Int.emod_eq_zero_of_dvd (LocalRoots.eight_dvd_odd_square_sub_one hf)
  omega

/-- Multiplication by an odd square preserves the residue governing the
quadratic symbol at two. -/
theorem mul_odd_square_mod_eight (d f : ℤ) (hf : Odd f) :
    (d * f ^ 2) % 8 = d % 8 := by
  rw [Int.mul_emod, odd_square_mod_eight hf]
  simp

theorem twoSymbol_mul_odd_square (d f : ℤ) (hf : Odd f) :
    twoSymbol (d * f ^ 2) = twoSymbol d := by
  unfold twoSymbol
  rw [ZMod.χ₈_int_mod_eight (d * f ^ 2), ZMod.χ₈_int_mod_eight d,
    mul_odd_square_mod_eight d f hf]


end DepthAspect.FundamentalDiscriminant
