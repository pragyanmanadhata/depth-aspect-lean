import DepthAspect.TraceBounds
import Mathlib.NumberTheory.Divisors

/-!
# Prime and prime-square specializations of the concrete cusp trace

The divisor-pair sets are the actual natural-number divisor antidiagonals.
The estimates below derive (32) from the restricted-totient estimate (31).
As in `TraceBounds`, `k` is the polynomial degree (weight minus two).
-/
namespace DepthAspect.TraceBounds
open scoped BigOperators

/-- The two actual factor pairs of a prime. -/
theorem prime_divisorsAntidiagonal (p : ℕ) (hp : p.Prime) :
    p.divisorsAntidiagonal = {(1, p), (p, 1)} := by
  ext ⟨a, b⟩
  simp only [Nat.mem_divisorsAntidiagonal, hp.ne_zero, ne_eq, not_false_eq_true,
    and_true, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro hab
    rcases (Nat.dvd_prime hp).mp (show a ∣ p from ⟨b, hab.symm⟩) with ha | ha
    · left
      subst a
      exact ⟨rfl, by simpa using hab⟩
    · right
      subst a
      refine ⟨rfl, ?_⟩
      have h : p * b = p * 1 := by simpa using hab
      exact mul_left_cancel₀ hp.ne_zero h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The three actual factor pairs of a prime square. -/
theorem prime_square_divisorsAntidiagonal (p : ℕ) (hp : p.Prime) :
    (p ^ 2).divisorsAntidiagonal = {(1, p ^ 2), (p, p), (p ^ 2, 1)} := by
  ext ⟨a, b⟩
  simp only [Nat.mem_divisorsAntidiagonal, pow_ne_zero 2 hp.ne_zero, ne_eq,
    not_false_eq_true, and_true, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro hab
    by_cases ha : a = 1
    · left
      subst a
      exact ⟨rfl, by simpa using hab⟩
    by_cases hb : b = 1
    · right; right
      subst b
      exact ⟨by simpa using hab, rfl⟩
    · exact Or.inr (Or.inl ((hp.mul_eq_prime_sq_iff ha hb).mp hab))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [pow_two]

/-- Real-power form of the prime cusp weight. -/
theorem inverse_sqrt_pow (x : ℝ) (hx : 0 < x) (k : ℕ) :
    (1 / Real.sqrt x) ^ (k + 1) = x ^ (-((k : ℝ) + 1) / 2) := by
  rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (Real.sqrt_nonneg x),
    Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

/-- The prime estimate in (32), for the actual cusp term. -/
theorem normalizedCusp_prime_bound (k n p : ℕ) (hp : p.Prime) (d : ℝ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d) :
    |normalizedCusp k n d (p : ℝ) p.divisorsAntidiagonal| ≤
      (576 / ((k : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n)) *
        (p : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpair : (1, p) ≠ (p, 1) := by
    intro h
    have := congrArg Prod.fst h
    exact hp.ne_one this.symm
  have hs : (∑ q ∈ p.divisorsAntidiagonal,
      ((min q.1 q.2 : ℕ) / Real.sqrt (p : ℝ) : ℝ) ^ (k + 1)) =
      2 * (1 / Real.sqrt (p : ℝ)) ^ (k + 1) := by
    rw [prime_divisorsAntidiagonal p hp]
    simp [hpair, min_eq_left hpOne, min_eq_right hpOne, two_mul]
  have hb := normalizedCusp_bound k n d (p : ℝ) hpR hd p.divisorsAntidiagonal
  rw [hs, inverse_sqrt_pow (p : ℝ) hpR k] at hb
  apply hb.trans
  have hnonneg : 0 ≤ (p : ℝ) ^ (-((k : ℝ) + 1) / 2) := by positivity
  have hden : 0 ≤ 1 / ((k : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n) := by positivity
  calc
    _ = 384 * ((1 / ((k : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n)) *
        (p : ℝ) ^ (-((k : ℝ) + 1) / 2)) := by ring
    _ ≤ 576 * ((1 / ((k : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n)) *
        (p : ℝ) ^ (-((k : ℝ) + 1) / 2)) :=
      mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hden hnonneg)
    _ = _ := by ring

/-- A positive factor pair has minimum no larger than the square root of its product. -/
theorem divisor_pair_ratio_le_one (m : ℕ) (hm : 0 < m) (p : ℕ × ℕ)
    (hp : p ∈ m.divisorsAntidiagonal) :
    ((min p.1 p.2 : ℕ) : ℝ) / Real.sqrt (m : ℝ) ≤ 1 := by
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hprodR : (p.1 : ℝ) * (p.2 : ℝ) = m := by exact_mod_cast hprod
  have hmin0 : 0 ≤ ((min p.1 p.2 : ℕ) : ℝ) := by positivity
  have hmin : ((min p.1 p.2 : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := by
    apply (Real.le_sqrt hmin0 (by positivity)).mpr
    rcases le_total p.1 p.2 with h | h
    · rw [min_eq_left h]
      have hR : (p.1 : ℝ) ≤ p.2 := by exact_mod_cast h
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ p.1 by positivity) (sub_nonneg.mpr hR)]
    · rw [min_eq_right h]
      have hR : (p.2 : ℝ) ≤ p.1 := by exact_mod_cast h
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ p.2 by positivity) (sub_nonneg.mpr hR)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hm))).mpr
  simpa using hmin

/-- The prime-square estimate in (32), for the actual cusp term. -/
theorem normalizedCusp_prime_square_bound (k n p : ℕ) (hp : p.Prime) (d : ℝ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d) :
    |normalizedCusp k n d ((p ^ 2 : ℕ) : ℝ) (p ^ 2).divisorsAntidiagonal| ≤
      576 / ((k : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n) := by
  have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
  have hcard : ((p ^ 2).divisorsAntidiagonal.card : ℝ) ≤ 3 := by
    rw [prime_square_divisorsAntidiagonal p hp]
    exact_mod_cast (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (by simp : ({(p ^ 2, 1)} : Finset (ℕ × ℕ)).card ≤ 1) 1)) 1)
  have hsum : (∑ q ∈ (p ^ 2).divisorsAntidiagonal,
      ((min q.1 q.2 : ℕ) / Real.sqrt ((p ^ 2 : ℕ) : ℝ) : ℝ) ^ (k + 1)) ≤ 3 := by
    calc
      _ ≤ ∑ _q ∈ (p ^ 2).divisorsAntidiagonal, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact pow_le_one₀ (by positivity) (divisor_pair_ratio_le_one (p ^ 2) hp2 q hq)
      _ = ((p ^ 2).divisorsAntidiagonal.card : ℝ) := by simp
      _ ≤ 3 := hcard
  have hb := normalizedCusp_bound k n d ((p ^ 2 : ℕ) : ℝ)
    (by exact_mod_cast hp2) hd (p ^ 2).divisorsAntidiagonal
  apply hb.trans
  calc
    _ ≤ (192 / ((k : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n)) * 3 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- The prime specialization (37) for the concrete finite elliptic-plus-cusp
model. A spectral-family interpretation only has to supply the cited trace
identity equating its average to this expression. Both size estimates used
here are already proved from the matrix and totient definitions. -/
theorem normalizedPrimeTrace_bound (k n p : ℕ) (hn : 4 ≤ n) (hp : p.Prime)
    (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (T : Finset ℤ) (s : ℤ → Finset (ℕ × ℕ)) (F : ℤ → ℕ × ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * (p : ℤ))
    (hF : ∀ t ∈ T, ∀ q ∈ s t,
      IsContentDatum q (t ^ 2 - 4 * (p : ℤ)) Ccl δ (F t q)) :
    ‖normalizedElliptic k d (p : ℝ) T (fun t => contentTrace n (s t) (F t)) +
      (normalizedCusp k n d (p : ℝ) p.divisorsAntidiagonal : ℂ)‖ ≤
      (ellipticConstant Ccl δ + 576 / ((k : ℝ) + 1)) *
        ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
        ((p : ℝ) ^ δ *
          ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) (p : ℤ)).card : ℝ) +
          (p : ℝ) ^ (-((k : ℝ) + 1) / 2)) := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hE := normalizedElliptic_bound_surviving k n hn (p : ℤ) hpZ d Ccl δ hC hδ hd
    T s F hT hF
  simp only [Int.cast_natCast] at hE
  have hCusp := normalizedCusp_prime_bound k n p hp d hd
  have hNinv : 1 / Real.sqrt ((2 : ℝ) ^ n) = ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow, one_div]
  have hCusp' : |normalizedCusp k n d (p : ℝ) p.divisorsAntidiagonal| ≤
      (576 / ((k : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
        (p : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
    convert hCusp using 1
    rw [← hNinv]
    ring
  have hK := ellipticConstant_nonneg Ccl δ hC hδ
  have hCross1 : 0 ≤ ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
      (p : ℝ) ^ (-((k : ℝ) + 1) / 2) := by positivity
  have hCross2 : 0 ≤ (576 / ((k : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
      ((p : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) (p : ℤ)).card : ℝ)) := by
    positivity
  calc
    _ ≤ ‖normalizedElliptic k d (p : ℝ) T (fun t => contentTrace n (s t) (F t))‖ +
        |normalizedCusp k n d (p : ℝ) p.divisorsAntidiagonal| := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using norm_add_le
        (normalizedElliptic k d (p : ℝ) T (fun t => contentTrace n (s t) (F t)))
        (normalizedCusp k n d (p : ℝ) p.divisorsAntidiagonal : ℂ)
    _ ≤ _ := by nlinarith [hE, hCusp']

end DepthAspect.TraceBounds
