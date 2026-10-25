import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Actual imprimitive character periodicity

For an actual odd Dirichlet character χ modulo q, this module studies the
literal function χ(n/gcd(n,f)). Its complete-period mean and uniform partial
sum bound are proved from the character, rather than supplied as assumptions.
The arithmetic identification χ = χ_d for a negative fundamental discriminant
is a separate external interface. Sums start at 1, matching OrderedDirichlet.
-/

open scoped BigOperators
namespace DepthAspect.ImprimitiveCharacter

noncomputable def psiInt {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ) (n : ℤ) : ℂ :=
  χ ((n / (Int.gcd n (f : ℤ) : ℤ) : ℤ) : ZMod q)

noncomputable def psiNat {q : ℕ} (χ : DirichletCharacter ℂ q) (f n : ℕ) : ℂ :=
  psiInt χ f (n : ℤ)

/-- Agreement with the paper's literal natural-number quotient. -/
theorem psiNat_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (f n : ℕ) :
    psiNat χ f n = χ ((n / Nat.gcd n f : ℕ) : ZMod q) := by
  simp only [psiNat, psiInt, Int.gcd_natCast_natCast, ← Int.natCast_ediv,
    Int.cast_natCast]

@[simp] theorem psiNat_conductor_one {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    psiNat χ 1 n = χ (n : ZMod q) := by
  simp [psiNat_eq]

theorem psiInt_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ) (n : ℤ) :
    ‖psiInt χ f n‖ ≤ 1 := χ.norm_le_one _

theorem psiNat_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (f n : ℕ) :
    ‖psiNat χ f n‖ ≤ 1 := psiInt_norm_le_one χ f n

/-- The larger period q*f absorbs every possible content gcd. -/
theorem psiInt_periodic {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ) :
    Function.Periodic (psiInt χ f) ((q * f : ℕ) : ℤ) := by
  intro n
  unfold psiInt
  rw [Nat.cast_mul, Int.gcd_add_mul_right_left]
  have hd : (Int.gcd n (f : ℤ) : ℤ) ∣ (f : ℤ) := Int.gcd_dvd_right n (f : ℤ)
  rw [Int.add_ediv_of_dvd_right (dvd_mul_of_dvd_right hd (q : ℤ)),
    Int.mul_ediv_assoc (q : ℤ) hd]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero]

theorem psiNat_periodic {q : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ) :
    Function.Periodic (psiNat χ f) (q * f) := by
  intro n
  simpa only [psiNat, Nat.cast_add] using psiInt_periodic χ f (n : ℤ)

/-- Oddness is preserved even though the gcd varies with n. -/
theorem psiInt_odd {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (f : ℕ) :
    Function.Odd (psiInt χ f) := by
  intro n
  unfold psiInt
  rw [Int.neg_gcd, Int.neg_ediv_of_dvd (Int.gcd_dvd_left n (f : ℤ)), Int.cast_neg]
  exact DirichletCharacter.Odd.eval_neg χ _ hχ

/-- A complete period of an odd periodic integer function has zero sum.
The proof pairs n with T-n; no cancellation estimate is assumed. -/
theorem odd_periodic_sum_zero (g : ℤ → ℂ) (T : ℕ)
    (hp : Function.Periodic g (T : ℤ)) (ho : Function.Odd g) :
    (∑ i ∈ Finset.range T, g ((i + 1 : ℕ) : ℤ)) = 0 := by
  have hs : (∑ i ∈ Finset.range T, g ((i + 1 : ℕ) : ℤ)) =
      ∑ i ∈ Finset.range T, g (i : ℤ) := by
    have he := Finset.sum_range_succ' (fun i : ℕ => g (i : ℤ)) T
    rw [Finset.sum_range_succ] at he
    have hp0 : g (T : ℤ) = g 0 := by simpa using hp 0
    rw [hp0] at he
    exact add_right_cancel he.symm
  have hr := Finset.sum_range_reflect (fun i : ℕ => g ((i + 1 : ℕ) : ℤ)) T
  have he : (∑ i ∈ Finset.range T, g ((T - 1 - i + 1 : ℕ) : ℤ)) =
      -(∑ i ∈ Finset.range T, g (i : ℤ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hnat : T - 1 - i + 1 = T - i := by omega
    rw [hnat, Nat.cast_sub (by omega : i ≤ T), hp.sub_eq', ho]
  rw [he, hs] at hr
  rw [hs]
  linear_combination (-1 / 2 : ℂ) * hr

theorem psiNat_period_sum_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (f : ℕ) :
    (∑ i ∈ Finset.range (q * f), psiNat χ f (i + 1)) = 0 :=
  odd_periodic_sum_zero (psiInt χ f) (q * f) (psiInt_periodic χ f) (psiInt_odd χ hχ f)

/-- Removing a complete zero-sum period does not change an initial sum. -/
theorem periodic_sum_block (a : ℕ → ℂ) (T n : ℕ) (hp : Function.Periodic a T)
    (hz : (∑ i ∈ Finset.range T, a (i + 1)) = 0) :
    (∑ i ∈ Finset.range (T + n), a (i + 1)) = ∑ i ∈ Finset.range n, a (i + 1) := by
  rw [Finset.sum_range_add, hz, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Nat.add_assoc, Nat.add_comm T, Nat.add_left_comm] using hp (i + 1)

/-- The norm bound is a consequence of periodicity, zero mean and the literal
pointwise character bound. This theorem accepts no bounded-partial-sum premise. -/
theorem periodic_sum_norm_le (a : ℕ → ℂ) (T : ℕ) (hT : 0 < T)
    (hp : Function.Periodic a T)
    (hz : (∑ i ∈ Finset.range T, a (i + 1)) = 0)
    (ha : ∀ n, ‖a n‖ ≤ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, a (i + 1)‖ ≤ T := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < T
    · calc
        _ ≤ ∑ i ∈ Finset.range n, ‖a (i + 1)‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => ha (i + 1))
        _ = (n : ℝ) := by simp
        _ ≤ T := by exact_mod_cast hn.le
    · have hTn : T ≤ n := Nat.le_of_not_gt hn
      have he : n = T + (n - T) := by omega
      rw [he, periodic_sum_block a T (n - T) hp hz]
      exact ih (n - T) (by omega)

theorem psiNat_partial_sum_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, psiNat χ f (i + 1)‖ ≤ (q * f : ℕ) :=
  periodic_sum_norm_le (psiNat χ f) (q * f) (Nat.mul_pos hq hf)
    (psiNat_periodic χ f) (psiNat_period_sum_zero χ hχ f) (psiNat_norm_le_one χ f) n

end DepthAspect.ImprimitiveCharacter
