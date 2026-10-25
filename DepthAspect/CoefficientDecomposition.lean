import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The integer reindexing in the coefficient tail

Every positive integer is injected into triples (b,u,v) with u squarefree and
odd and v positive, through its genuine decomposition 2^b*u*v². Existence is
proved from Mathlib's squarefree decomposition; no counting identity is an input.
For the upper bound no uniqueness theorem is needed: reconstruction alone
proves that the selected decomposition is injective.
-/
noncomputable section
namespace DepthAspect.CoefficientDecomposition

abbrev SquarefreeOdd := {u : ℕ // Squarefree u ∧ Odd u}
abbrev Indices := ℕ × SquarefreeOdd × ℕ

/-- The last natural index represents the positive integer v=k+1. -/
def reconstruct (i : Indices) : ℕ := 2 ^ i.1 * i.2.1.val * (i.2.2 + 1) ^ 2

 theorem exists_decomposition (n : ℕ) :
    ∃ i : Indices, reconstruct i = n + 1 ∧ Odd (i.2.2 + 1) := by
  let o : ℕ := ordCompl[2] (n + 1)
  have ho : 0 < o := Nat.ordCompl_pos 2 (by omega)
  have hoodd : Odd o := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : n + 1 ≠ 0)
      (even_iff_two_dvd.mp he)
  obtain ⟨u, v, hu, hv, huv, hus⟩ := Nat.sq_mul_squarefree_of_pos ho
  have huodd : Odd u := (Nat.odd_mul.mp (huv.symm ▸ hoodd)).2
  have hvodd : Odd v :=
    (Nat.odd_pow_iff (by omega : (2 : ℕ) ≠ 0)).mp (Nat.odd_mul.mp (huv.symm ▸ hoodd)).1
  refine ⟨⟨(n + 1).factorization 2, ⟨u, hus, huodd⟩, v - 1⟩, ?_, ?_⟩
  swap
  · simpa only [Nat.sub_add_cancel hv] using hvodd
  unfold reconstruct
  simp only
  rw [Nat.sub_add_cancel hv]
  calc
    2 ^ (n + 1).factorization 2 * u * v ^ 2 =
        2 ^ (n + 1).factorization 2 * o := by rw [← huv]; ring
    _ = n + 1 := Nat.ordProj_mul_ordCompl_eq_self (n + 1) 2

/-- One actual decomposition for each positive integer. -/
def decompose (n : ℕ) : Indices := Classical.choose (exists_decomposition n)

 theorem reconstruct_decompose (n : ℕ) : reconstruct (decompose n) = n + 1 :=
  (Classical.choose_spec (exists_decomposition n)).1

 theorem decompose_odd_square_part (n : ℕ) : Odd ((decompose n).2.2 + 1) :=
  (Classical.choose_spec (exists_decomposition n)).2

 theorem decompose_injective : Function.Injective decompose := by
  intro n m h
  have h' := congrArg reconstruct h
  rw [reconstruct_decompose, reconstruct_decompose] at h'
  omega

 theorem reconstruct_pos (i : Indices) : 0 < reconstruct i := by
  unfold reconstruct
  exact Nat.mul_pos (Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero i.2.1.property.1.ne_zero)) (by positivity)

end DepthAspect.CoefficientDecomposition
