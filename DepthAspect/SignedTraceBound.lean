import DepthAspect.SignedNumericBound
import DepthAspect.SignedTraceInterface

/-!
# The signed prime-square trace bound from the literal general expression

The auxiliary terms are cancelled as actual finite divisor sums, and the
elliptic part is bounded through its proved four strata. Only the reusable
arithmetic class-number growth input is present here; the final uniform
class-number composition supplies it from the cited general identity.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- At an odd prime-square index, the complete general expression reduces
exactly to its elliptic sieve. -/
theorem newSignedExpression_prime_square (r n p : ℕ) (hn : 7 ≤ n)
    (hp : p.Prime) (hodd : Odd p) (H : ℤ → ℝ) :
    newSignedExpression (2 * r) (2 ^ n) (p ^ 2) H =
      -(∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
        ∑ v ∈ (2 ^ (n - j)).divisors,
          ∑ t ∈ admissibleTraces (2 ^ (n - j)) v (p ^ 2),
            tracePolynomial (((t : ℝ) / Real.sqrt v : ℝ) : ℂ) ((p ^ 2 : ℕ) : ℂ) (2 * r) *
              (H (t ^ 2 - 4 * (v : ℤ) * (p ^ 2 : ℕ)) : ℂ)) / 2 := by
  rw [newSignedExpression_two_pow (2 * r) n (p ^ 2) (by omega)]
  have hH := hyperbolic_prime_square_sieve (2 * r) n p (by omega) hp hodd
  have hW := weight_two_sieve n (p ^ 2) (by omega)
  unfold fullSignedExpression
  push_cast at hH hW ⊢
  by_cases hr : 2 * r = 0
  · simp only [hr] at hH
    simp only [hr, if_true]
    simp only [mul_add, mul_sub, mul_div, mul_neg, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_div]
    rw [hH, hW]
    ring
  · simp only [hr, if_false, add_zero]
    simp only [mul_sub, mul_div, mul_neg, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.sum_div]
    rw [hH]
    ring

/-- The actual newspace signed arithmetic expression, including every
hyperbolic, weight-two and H(0) term in its source, obeys the bound used in (73). -/
theorem normalizedSignedExpression_square_bound (r n p : ℕ) (hn : 7 ≤ n)
    (hp : p.Prime) (hodd : Odd p) (H : ℤ → ℝ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hHnonneg : ∀ D : ℤ, D < 0 → 0 ≤ H D)
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ C * |(D : ℝ)| ^ (1 / 2 + δ)) :
    ‖newSignedExpression (2 * r) (2 ^ n) (p ^ 2) H /
        ((((p ^ 2 : ℕ) : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ)‖ ≤
      48 * ((2 * r + 1 : ℕ) : ℝ) * C * (4 : ℝ) ^ (1 / 2 + δ) *
        (((2 : ℝ) ^ n) ^ (1 / 2 + δ) * (p : ℝ) ^ (2 * δ) +
          ((2 : ℝ) ^ n) ^ δ * (p : ℝ) ^ (1 + 2 * δ)) := by
  have hp0 := hp.pos
  have hmR : (0 : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by positivity
  have hden : 0 < (((p ^ 2 : ℕ) : ℝ) ^ ((r : ℝ) + 1 / 2)) :=
    Real.rpow_pos_of_pos hmR _
  rw [newSignedExpression_prime_square r n p hn hp hodd H,
    norm_div, norm_div, norm_neg, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  have hE := signed_elliptic_square_bound r n p hn hp.pos hodd H C δ hC hδ
    hHnonneg hHgrowth
  have hb := signed_numeric_bound r ((2 : ℝ) ^ n) ((p ^ 2 : ℕ) : ℝ) C δ
    (by positivity) hmR hC
  have hsum : ‖∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      ∑ v ∈ (2 ^ (n - j)).divisors,
        ∑ t ∈ admissibleTraces (2 ^ (n - j)) v (p ^ 2),
          tracePolynomial (((t : ℝ) / Real.sqrt v : ℝ) : ℂ) ((p ^ 2 : ℕ) : ℂ) (2 * r) *
            (H (t ^ 2 - 4 * (v : ℤ) * (p ^ 2 : ℕ)) : ℂ)‖ / 2 /
      (((p ^ 2 : ℕ) : ℝ) ^ ((r : ℝ) + 1 / 2)) ≤
      48 * ((2 * r + 1 : ℕ) : ℝ) * C * (4 : ℝ) ^ (1 / 2 + δ) *
        (((2 : ℝ) ^ n) ^ (1 / 2 + δ) * ((p ^ 2 : ℕ) : ℝ) ^ δ +
          ((2 : ℝ) ^ n) ^ δ * ((p ^ 2 : ℕ) : ℝ) ^ (1 / 2 + δ)) := by
    exact (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hE (by norm_num)) hden.le).trans hb
  have hexp := square_rpow_exponents (p : ℝ) δ (by positivity)
  simpa only [Nat.cast_pow, hexp.1, hexp.2] using hsum

/-- The signed arithmetic estimate with its class-number size premise fully
discharged. The remaining arithmetic inputs are the cited general class
identity and the actual primitive nonnegative class weights. -/
theorem normalizedSignedExpression_square_bound_uniform (r n p : ℕ) (hn : 7 ≤ n)
    (hp : p.Prime) (hodd : Odd p) (h₀ H : ℤ → ℝ)
    (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 → H D =
      ∑ u ∈ TraceBounds.positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨
      Nonempty (ClassNumberGrowth.ClassFormulaData H D))
    (δ : ℝ) (hδ : 0 < δ) :
    ‖newSignedExpression (2 * r) (2 ^ n) (p ^ 2) H /
        ((((p ^ 2 : ℕ) : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ)‖ ≤
      48 * ((2 * r + 1 : ℕ) : ℝ) * TraceBounds.uniformClassConstant δ *
        (4 : ℝ) ^ (1 / 2 + δ) *
        (((2 : ℝ) ^ n) ^ (1 / 2 + δ) * (p : ℝ) ^ (2 * δ) +
          ((2 : ℝ) ^ n) ^ δ * (p : ℝ) ^ (1 + 2 * δ)) :=
  normalizedSignedExpression_square_bound r n p hn hp hodd H
    (TraceBounds.uniformClassConstant δ) δ (TraceBounds.uniformClassConstant_pos hδ).le hδ
    (TraceBounds.hurwitz_nonneg h₀ H h₀nonneg hidentity)
    (TraceBounds.uniform_class_growth H hformula hδ)

/-- Lemma 5.1 for the actual finite signed Hecke sum, conditional only on the
cited general SZ trace identity, its simultaneous eigenbasis normalization,
and the general arithmetic class identities. Every specialized bound in the
conclusion is supplied by the preceding proved chain. -/
theorem signedHeckeSum_prime_square_bound_from_general_inputs
    {ι : Type*} [Fintype ι] (V : ℕ → Type*)
    [∀ N, AddCommGroup (V N)] [∀ N, Module ℂ (V N)]
    (r n p : ℕ) (hn : 7 ≤ n) (hp : p.Prime) (hodd : Odd p)
    (T : ∀ N, ℕ → V N →ₗ[ℂ] V N) (W : ∀ N, V N →ₗ[ℂ] V N)
    (b : Module.Basis ι ℂ (V (2 ^ n))) (ε : ι → ℂ) (a : ι → ℕ → ℂ)
    (hT : ∀ f, T (2 ^ n) (p ^ 2) (b f) =
      (((((p ^ 2 : ℕ) : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * a f (p ^ 2)) • b f)
    (hW : ∀ f, W (2 ^ n) (b f) = ((-1 : ℂ) ^ (r + 1) * ε f) • b f)
    (h₀ H : ℤ → ℝ) (hSZ : GeneralSignedTraceFormula r H V T W)
    (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 → H D =
      ∑ u ∈ TraceBounds.positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hformula : ∀ D : ℤ, D < 0 → H D = 0 ∨
      Nonempty (ClassNumberGrowth.ClassFormulaData H D))
    (δ : ℝ) (hδ : 0 < δ) :
    ‖signedHeckeSum ε a (p ^ 2)‖ ≤
      48 * ((2 * r + 1 : ℕ) : ℝ) * TraceBounds.uniformClassConstant δ *
        (4 : ℝ) ^ (1 / 2 + δ) *
        (((2 : ℝ) ^ n) ^ (1 / 2 + δ) * (p : ℝ) ^ (2 * δ) +
          ((2 : ℝ) ^ n) ^ δ * (p : ℝ) ^ (1 + 2 * δ)) := by
  have hp0 := hp.pos
  have hcop : Nat.Coprime (p ^ 2) (2 ^ n) := hodd.coprime_two_right.pow 2 n
  have hs := signedHeckeSum_eq_trace r (p ^ 2) (by positivity) b
    (T (2 ^ n) (p ^ 2)) (W (2 ^ n)) ε a hT hW
  rw [hSZ.trace_formula (2 ^ n) (p ^ 2) (by positivity) (by positivity) hcop] at hs
  have hs' : signedHeckeSum ε a (p ^ 2) = (-1 : ℂ) ^ (r + 1) *
      (newSignedExpression (2 * r) (2 ^ n) (p ^ 2) H /
        ((((p ^ 2 : ℕ) : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ)) := by
    rw [hs]
    ring
  rw [hs', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact normalizedSignedExpression_square_bound_uniform r n p hn hp hodd h₀ H
    h₀nonneg hidentity hformula δ hδ

end DepthAspect.SignedSieve
