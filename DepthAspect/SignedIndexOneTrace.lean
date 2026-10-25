import DepthAspect.SignedIndexOneSum
import DepthAspect.SignedTraceInterface
import Mathlib.Tactic.LinearCombination

/-!
# The index-one signed trace combination

The actual general signed trace is specialized at index one. The six
nonzero pairs, including H(0), cancel only after the four-level sieve;
the two zero-trace divisors give the explicit three-class-number expression.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

noncomputable def indexOneConstant (r : ℕ) (H : ℤ → ℝ) : ℂ :=
  ∑ p ∈ indexOneNonzeroPairs,
    tracePolynomial (((p.2 : ℝ) / Real.sqrt p.1 : ℝ) : ℂ) 1 (2 * r) *
      (H (p.2 ^ 2 - 4 * (p.1 : ℤ)) : ℂ)

/-- Each literal index-one expression consists of the same six-pair
constant, the two zero-trace terms, and its elementary auxiliary terms. -/
theorem fullSignedExpression_index_one (r h : ℕ) (hh : 2 ≤ h) (H : ℤ → ℝ) :
    fullSignedExpression (2 * r) (2 ^ h) 1 H =
      -(indexOneConstant r H + (-1 : ℂ) ^ r *
        ((H (-4 * (2 : ℤ) ^ h) : ℂ) + (H (-4 * (2 : ℤ) ^ (h - 1)) : ℂ))) / 2 - 1 +
      if 2 * r = 0 then ((h : ℕ) + 1 : ℂ) else 0 := by
  have hi := index_one_sum h hh (fun p : ℕ × ℤ =>
    tracePolynomial (((p.2 : ℝ) / Real.sqrt p.1 : ℝ) : ℂ) 1 (2 * r) *
      (H (p.2 ^ 2 - 4 * (p.1 : ℤ)) : ℂ))
  simp only [Int.cast_zero, zero_div, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
    zero_sub, Nat.cast_pow, Nat.cast_ofNat, TraceTrigonometry.tracePolynomial_even_zero] at hi
  have hhyp : (∑ d ∈ (1 : ℕ).divisors,
      (((min d (1 / d) : ℕ) : ℝ) : ℂ) ^ (2 * r + 1) *
        (((Nat.gcd (squarePart (2 ^ h)) (d + 1 / d) : ℕ) : ℝ) : ℂ)) = 2 := by
    exact_mod_cast hyperbolic_index_one (2 * r) h hh
  unfold fullSignedExpression
  simp only [Nat.cast_one, mul_one]
  rw [hi, hhyp, OldformTrace.two_pow_divisors_card]
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.cast_one, mul_one,
    Nat.cast_add, Complex.ofReal_ofNat, neg_mul]
  unfold indexOneConstant
  split_ifs <;> ring

/-- The four-level index-one expression, before applying the spectral sign
normalization. Every zero-discriminant and auxiliary contribution cancels. -/
theorem newSignedExpression_index_one (r n : ℕ) (hn : 5 ≤ n) (H : ℤ → ℝ) :
    newSignedExpression (2 * r) (2 ^ n) 1 H =
      -((-1 : ℂ) ^ r) *
        ((H (-(2 : ℤ) ^ (n + 2)) : ℂ) - 2 * (H (-(2 : ℤ) ^ n) : ℂ) +
          (H (-(2 : ℤ) ^ (n - 2)) : ℂ)) / 2 := by
  rw [newSignedExpression_two_pow (2 * r) n 1 (by omega)]
  have hexpr : (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      fullSignedExpression (2 * r) (2 ^ (n - j)) 1 H) =
      ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
        (-(indexOneConstant r H + (-1 : ℂ) ^ r *
          ((H (-4 * (2 : ℤ) ^ (n - j)) : ℂ) +
            (H (-4 * (2 : ℤ) ^ (n - j - 1)) : ℂ))) / 2 - 1 +
          if 2 * r = 0 then ((n - j : ℕ) + 1 : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [fullSignedExpression_index_one r (n - j)
      (by have := Finset.mem_range.mp hj; omega)]
  rw [hexpr]
  let G : ℕ → ℂ := fun h => (H (-4 * (2 : ℤ) ^ h) : ℂ)
  have ha := alpha_auxiliary_window_sieve n (by omega) (indexOneConstant r H)
    ((-1 : ℂ) ^ r) (if 2 * r = 0 then 1 else 0) G
  have hrepl : (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      (-(indexOneConstant r H + (-1 : ℂ) ^ r *
        ((H (-4 * (2 : ℤ) ^ (n - j)) : ℂ) +
          (H (-4 * (2 : ℤ) ^ (n - j - 1)) : ℂ))) / 2 - 1 +
        if 2 * r = 0 then ((n - j : ℕ) + 1 : ℂ) else 0)) =
      ∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
        (-(indexOneConstant r H + (-1 : ℂ) ^ r * (G (n - j) + G (n - j - 1))) / 2 - 1 +
          (if 2 * r = 0 then (1 : ℂ) else 0) * (((n - j : ℕ) : ℂ) + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp [G]
  rw [hrepl, ha]
  dsimp [G]
  have hn0 : -4 * (2 : ℤ) ^ n = -(2 : ℤ) ^ (n + 2) := by rw [pow_add]; ring
  have hn2 : -4 * (2 : ℤ) ^ (n - 2) = -(2 : ℤ) ^ n := by
    conv_rhs => rw [show n = (n - 2) + 2 by omega, pow_add]
    ring
  have hn4 : -4 * (2 : ℤ) ^ (n - 4) = -(2 : ℤ) ^ (n - 2) := by
    conv_rhs => rw [show n - 2 = (n - 4) + 2 by omega, pow_add]
    ring
  rw [hn0, hn2, hn4]
  ring

/-- The actual finite-family root-number sum in (68), from the general
Skoruppa–Zagier identity and the individual Fricke eigenvector normalization.
The identity operator at Hecke index one is the only Hecke input here. -/
theorem rootNumberSum_from_general_formula
    (Family V : ℕ → Type*) [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (V N)] [∀ N, Module ℂ (V N)]
    (r n : ℕ) (hn : 5 ≤ n) (H : ℤ → ℝ)
    (T : ∀ N, ℕ → V N →ₗ[ℂ] V N) (W : ∀ N, V N →ₗ[ℂ] V N)
    (hSZ : GeneralSignedTraceFormula r H V T W)
    (hT1 : ∀ N, 0 < N → T N 1 = LinearMap.id)
    (ε : Family (2 ^ n) → ℂ) (b : Module.Basis (Family (2 ^ n)) ℂ (V (2 ^ n)))
    (hW : ∀ f, W (2 ^ n) (b f) = ((-1 : ℂ) ^ (r + 1) * ε f) • b f) :
    (∑ f, ε f) =
      ((H (-(2 : ℤ) ^ (n + 2)) : ℂ) - 2 * (H (-(2 : ℤ) ^ n) : ℂ) +
        (H (-(2 : ℤ) ^ (n - 2)) : ℂ)) / 2 := by
  have htrace := hSZ.trace_formula (2 ^ n) 1 (by positivity) (by decide) (by simp)
  rw [hT1 (2 ^ n) (by positivity), LinearMap.id_comp,
    OldformTrace.trace_of_eigenbasis b (W (2 ^ n)) _ hW,
    ← Finset.mul_sum, newSignedExpression_index_one r n hn H, pow_succ] at htrace
  have hzero : (-1 : ℂ) ^ r * ((∑ f, ε f) -
      ((H (-(2 : ℤ) ^ (n + 2)) : ℂ) - 2 * (H (-(2 : ℤ) ^ n) : ℂ) +
        (H (-(2 : ℤ) ^ (n - 2)) : ℂ)) / 2) = 0 := by
    linear_combination -htrace
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by norm_num)))


end DepthAspect.SignedSieve
