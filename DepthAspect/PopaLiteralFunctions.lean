import DepthAspect.PopaTrace
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The literal local functions in Popa's formula

These are the objects B_Q, C_Q, Xi_r, and K_n displayed in (2) and (12).
The local count uses canonical representatives of actual units modulo Q.
Its independence of the representative, in the stated domain, is proved
below. General Möbius inversion gives the C-to-B identity used before (9).
No dyadic trace estimate is an assumption in this module.
-/
namespace DepthAspect.PopaLiteralFunctions

open scoped BigOperators

def quadratic (t m x : ℤ) : ℤ := x ^ 2 - t * x + m

theorem derivative_divisible (Q v t m x : ℤ) (hv : v ∣ Q)
    (hD : v ^ 2 ∣ t ^ 2 - 4 * m) (hx : Q * v ∣ quadratic t m x) :
    v ∣ 2 * x - t := by
  have hvQ : v ^ 2 ∣ Q * v := by
    obtain ⟨a, rfl⟩ := hv
    refine ⟨a, ?_⟩
    ring
  have hf : v ^ 2 ∣ quadratic t m x := dvd_trans hvQ hx
  have hs : v ^ 2 ∣ (2 * x - t) ^ 2 := by
    have heq : (2 * x - t) ^ 2 = 4 * quadratic t m x + (t ^ 2 - 4 * m) := by
      unfold quadratic
      ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right hf 4) hD
  exact (Int.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hs

theorem quadratic_root_shift (Q v t m x a : ℤ) (hv : v ∣ Q)
    (hD : v ^ 2 ∣ t ^ 2 - 4 * m) (hx : Q * v ∣ quadratic t m x) :
    Q * v ∣ quadratic t m (x + Q * a) := by
  have hd := derivative_divisible Q v t m x hv hD hx
  obtain ⟨b, hb⟩ := hd
  obtain ⟨c, hc⟩ := hv
  obtain ⟨d, hd⟩ := hx
  refine ⟨d + a * b + c * a ^ 2, ?_⟩
  unfold quadratic at hd ⊢
  linear_combination hd + Q * a * hb + Q * a ^ 2 * hc

theorem quadratic_root_shift_iff (Q v t m x a : ℤ) (hv : v ∣ Q)
    (hD : v ^ 2 ∣ t ^ 2 - 4 * m) :
    Q * v ∣ quadratic t m (x + Q * a) ↔ Q * v ∣ quadratic t m x := by
  constructor
  · intro hx
    have hh := quadratic_root_shift Q v t m (x + Q * a) (-a) hv hD hx
    simpa only [mul_neg, add_neg_cancel_right] using hh
  · exact quadratic_root_shift Q v t m x a hv hD

noncomputable def B (Q : ℕ) (hQ : 0 < Q) (v : ℕ) (t m : ℤ) : ℝ := by
  letI : NeZero Q := ⟨ne_of_gt hQ⟩
  exact PopaTrace.indexPsi Q / PopaTrace.indexPsi (Q / v) *
    Fintype.card {a : (ZMod Q)ˣ //
      ((Q * v : ℕ) : ℤ) ∣ quadratic t m (((a : ZMod Q).val : ℕ) : ℤ)}

/-- The antidiagonal form makes the divisor convolution literal, including
the zero input convention for arithmetic functions. -/
noncomputable def C (Q : ℕ) (hQ : 0 < Q) (v : ℕ) (t m : ℤ) : ℝ :=
  ∑ a ∈ v.divisorsAntidiagonal, (ArithmeticFunction.moebius a.1 : ℝ) * B Q hQ a.2 t m

theorem C_eq_divisor_sum (Q : ℕ) (hQ : 0 < Q) (v : ℕ) (t m : ℤ) :
    C Q hQ v t m =
      ∑ a ∈ v.divisors, (ArithmeticFunction.moebius a : ℝ) * B Q hQ (v / a) t m := by
  exact Nat.sum_divisorsAntidiagonal (fun a b =>
    (ArithmeticFunction.moebius a : ℝ) * B Q hQ b t m)

theorem sum_C_eq_B (Q : ℕ) (hQ : 0 < Q) (v : ℕ) (hv : 0 < v) (t m : ℤ) :
    (∑ a ∈ v.divisors, C Q hQ a t m) = B Q hQ v t m := by
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun a => C Q hQ a t m) (g := fun a => B Q hQ a t m)).mpr
    (fun a _ => rfl) v hv

/-- General Hurwitz-class coefficient, with the square divisibility convention
made explicit rather than interpreting a nonintegral discriminant as an integer. -/
noncomputable def classCoefficient (Q : ℕ) (hQ : 0 < Q)
    (H : ℤ → ℝ) (t m : ℤ) : ℝ :=
  ∑ v ∈ Q.divisors,
    if (v : ℤ) ^ 2 ∣ t ^ 2 - 4 * m then
      H ((t ^ 2 - 4 * m) / (v : ℤ) ^ 2) * C Q hQ v t m else 0

noncomputable def Xi (h : ℕ) (H : ℤ → ℝ) (t m : ℤ) : ℝ :=
  classCoefficient (2 ^ h) (by positivity) H t m

theorem Xi_eq_sum (h : ℕ) (H : ℤ → ℝ) (t m : ℤ) :
    Xi h H t m = ∑ j ∈ Finset.range (h + 1),
      if (4 : ℤ) ^ j ∣ t ^ 2 - 4 * m then
        H ((t ^ 2 - 4 * m) / (4 : ℤ) ^ j) * C (2 ^ h) (by positivity) (2 ^ j) t m
      else 0 := by
  unfold Xi classCoefficient
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  apply Finset.sum_congr rfl
  intro j hj
  have hp : (((2 ^ j : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ j := by
    push_cast
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  simp only [hp]

noncomputable def K (n : ℕ) (H : ℤ → ℝ) (t m : ℤ) : ℝ :=
  Xi n H t m - 2 * Xi (n - 1) H t m + Xi (n - 2) H t m

end DepthAspect.PopaLiteralFunctions
