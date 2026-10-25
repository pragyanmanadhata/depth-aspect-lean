import DepthAspect.CuspReindex
import DepthAspect.SignedAdmissibility
import DepthAspect.TracePolynomial
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The general Skoruppa–Zagier trace and its four-level dyadic sieve

This module states the cited general trace formula as a finite arithmetic
expression and proves the dyadic truncation from the general multiplicative
α-function. The trace formula itself is an external input; no specialized
signed trace or signed trace estimate is built into its definition.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- The general multiplicative coefficient α of the cited formula (66). -/
noncomputable def alphaGeneral (N : ℕ) : ℤ :=
  N.factorization.prod (fun _ e => Dyadic.alpha e)

@[simp] theorem alphaGeneral_two_pow (n : ℕ) :
    alphaGeneral (2 ^ n) = Dyadic.alpha n := by
  unfold alphaGeneral
  rw [Nat.prime_two.factorization_pow,
    Finsupp.prod_single_index (by rfl : Dyadic.alpha 0 = 1)]

theorem alpha_ge_four (j : ℕ) (hj : 4 ≤ j) : Dyadic.alpha j = 0 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rfl

/-- The exact square-part function Q(M) from the general formula. -/
noncomputable def squarePart (M : ℕ) : ℕ :=
  M.factorization.prod (fun p e => p ^ (e / 2))

@[simp] theorem squarePart_two_pow (h : ℕ) : squarePart (2 ^ h) = 2 ^ (h / 2) := by
  unfold squarePart
  rw [Nat.prime_two.factorization_pow, Finsupp.prod_single_index (by simp)]

/-- All integral traces in the closed elliptic interval. The generous integer
bounds make the finite definition independent of rounding a square root. -/
noncomputable def closedTraces (v m : ℕ) : Finset ℤ :=
  (Finset.Icc (-4 * (v : ℤ) * m) (4 * (v : ℤ) * m)).filter
    (fun t => t ^ 2 ≤ 4 * (v : ℤ) * m)

/-- The literal (66) admissibility condition at a fixed positive divisor v. -/
noncomputable def admissibleTraces (M v m : ℕ) : Finset ℤ :=
  (closedTraces v m).filter (fun t => (v : ℤ) ∣ t ∧
    Squarefree (Nat.gcd ((t / (v : ℤ)).natAbs ^ 2) (M / v)))

/-- The full general s_{k,M}(m), with polynomial degree k−2 represented by r.
The value H(0) remains in the closed elliptic sum. -/
noncomputable def fullSignedExpression (r M m : ℕ) (H : ℤ → ℝ) : ℂ :=
  -(∑ v ∈ M.divisors, ∑ t ∈ admissibleTraces M v m,
      tracePolynomial (((t : ℝ) / Real.sqrt v : ℝ) : ℂ) (m : ℂ) r *
        (H (t ^ 2 - 4 * (v : ℤ) * m) : ℂ)) / 2 -
    ((∑ d ∈ m.divisors,
      ((min d (m / d) : ℕ) : ℝ) ^ (r + 1) *
        (Nat.gcd (squarePart M) (d + m / d) : ℝ)) : ℂ) / 2 +
    if r = 0 then ((M.divisors.card : ℕ) : ℂ) *
      ((∑ d ∈ m.divisors, d : ℕ) : ℂ) else 0

/-- The literal divisor convolution on the right side of the general signed
newspace trace formula; pair (M,L) has M*L=N. -/
noncomputable def newSignedExpression (r N m : ℕ) (H : ℤ → ℝ) : ℂ :=
  ∑ p ∈ N.divisorsAntidiagonal,
    (alphaGeneral p.2 : ℂ) * fullSignedExpression r p.1 m H

/-- The general multiplicative α convolution has exactly four dyadic levels.
This proves the first specialization of (66). -/
theorem alpha_convolution_two_pow (n : ℕ) (hn : 3 ≤ n) (s : ℕ → ℂ) :
    (∑ p ∈ (2 ^ n).divisorsAntidiagonal, (alphaGeneral p.2 : ℂ) * s p.1) =
      ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) * s (2 ^ (n - j)) := by
  rw [TraceBounds.sum_divisorsAntidiagonal_two_pow]
  simp only [alphaGeneral_two_pow]
  have hreflect :
      (∑ a ∈ Finset.range (n + 1), (Dyadic.alpha (n - a) : ℂ) * s (2 ^ a)) =
      ∑ j ∈ Finset.range (n + 1), (Dyadic.alpha j : ℂ) * s (2 ^ (n - j)) := by
    rw [← Finset.sum_range_reflect (fun j => (Dyadic.alpha j : ℂ) * s (2 ^ (n - j)))]
    apply Finset.sum_congr rfl
    intro a ha
    have han : a ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self han]
  rw [hreflect]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : 4 ≤ n + 1))
  intro j hj hnot
  have hj4 : 4 ≤ j := by simpa only [Finset.mem_range, not_lt] using hnot
  simp [alpha_ge_four j hj4]

/-- The actual full signed formula specializes to the four levels N/2^j. -/
theorem newSignedExpression_two_pow (r n m : ℕ) (hn : 3 ≤ n) (H : ℤ → ℝ) :
    newSignedExpression r (2 ^ n) m H =
      ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
        fullSignedExpression r (2 ^ (n - j)) m H :=
  alpha_convolution_two_pow n hn (fun M => fullSignedExpression r M m H)

end DepthAspect.SignedSieve
