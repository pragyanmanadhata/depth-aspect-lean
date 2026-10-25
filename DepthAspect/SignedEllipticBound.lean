import DepthAspect.SignedSquareAuxiliary
import DepthAspect.SignedStratumBounds
import DepthAspect.UniformTraceBounds

/-!
# Quantitative bounds for the actual surviving signed strata

The finite coefficient weights, cardinalities, polynomial estimate, and
strict negativity are derived from the literal trace sets. The reusable
intermediate class-number bound is discharged by UniformTraceBounds in the
final arithmetic-family composition.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- The finite norm estimate with its constant majorant summed explicitly. -/
theorem norm_sum_le_card_mul (U : Finset ℤ) (F : ℤ → ℂ) (B : ℝ)
    (hF : ∀ u ∈ U, ‖F u‖ ≤ B) : ‖∑ u ∈ U, F u‖ ≤ (U.card : ℝ) * B := by
  simpa using norm_sum_le_of_le U hF

/-- The exact coefficient table has total absolute weight at most four,
when both parity classes at N/4 are counted in the same finite interval. -/
theorem norm_coefficient_sum_le (n : ℕ) (hn : 4 ≤ n)
    (U : ℕ → Finset ℤ) (F : ℕ → ℤ → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hcard : ∀ b ∈ ({0, 2, 4} : Finset ℕ), (U b).card ≤ C)
    (hF : ∀ b ∈ ({0, 2, 4} : Finset ℕ), ∀ u ∈ U b, ‖F b u‖ ≤ B) :
    ‖∑ b ∈ Finset.range (n + 1), ∑ u ∈ U b,
      (SignedAdmissibility.actualStratumCoefficient n b u : ℂ) * F b u‖ ≤ 4 * C * B := by
  classical
  rw [coefficient_sum_four_strata n hn]
  have h0 := norm_sum_le_card_mul (U 0) (F 0) B (hF 0 (by simp))
  have h2 : ‖∑ u ∈ U 2, (if Odd u then (-1 : ℂ) else -2) * F 2 u‖ ≤
      (U 2).card * (2 * B) := by
    apply norm_sum_le_card_mul
    intro u hu
    have hb := hF 2 (by simp) u hu
    by_cases ho : Odd u
    · simp only [ho, if_true, neg_one_mul, norm_neg]
      linarith
    · simp only [ho, if_false, norm_mul, norm_neg, Complex.norm_ofNat]
      linarith
  have h4 : ‖∑ u ∈ U 4, if Even u then F 4 u else 0‖ ≤ (U 4).card * B := by
    apply norm_sum_le_card_mul
    intro u hu
    split_ifs
    · exact hF 4 (by simp) u hu
    · simpa only [norm_zero] using hB
  have hc0 := mul_le_mul_of_nonneg_right (hcard 0 (by simp)) hB
  have hc2 := mul_le_mul_of_nonneg_right (hcard 2 (by simp)) (by positivity : 0 ≤ 2 * B)
  have hc4 := mul_le_mul_of_nonneg_right (hcard 4 (by simp)) hB
  have ht := norm_add_le
    ((∑ u ∈ U 0, F 0 u) + (∑ u ∈ U 2, (if Odd u then (-1 : ℂ) else -2) * F 2 u))
    (∑ u ∈ U 4, if Even u then F 4 u else 0)
  have ht' := norm_add_le (∑ u ∈ U 0, F 0 u)
    (∑ u ∈ U 2, (if Odd u then (-1 : ℂ) else -2) * F 2 u)
  nlinarith

/-- Each actual quotient-trace interval satisfies the common stratum bound. -/
theorem quotientTraces_card_bound (n b m : ℕ) (hb : b ≤ 4) (hn : 4 ≤ n) (hm : 0 < m) :
    ((quotientTraces (2 ^ (n - b)) m).card : ℝ) ≤
      1 + 16 * Real.sqrt m / Real.sqrt ((2 : ℝ) ^ n) := by
  have hsize : (2 : ℝ) ^ n ≤ 16 * 2 ^ (n - b) := by
    have hbn : b ≤ n := by omega
    have hp : (2 : ℝ) ^ b ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hb
    calc
      (2 : ℝ) ^ n = 2 ^ (n - b) * 2 ^ b := by
        rw [← pow_add, Nat.sub_add_cancel hbn]
      _ ≤ 16 * 2 ^ (n - b) := by
        norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at hp
        nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2 : ℝ) ^ (n - b))]
  apply card_surviving_stratum _ ((2 : ℝ) ^ (n - b)) ((2 : ℝ) ^ n) m
    (by positivity) (by positivity) (by positivity) hsize
  intro u hu
  have h := (mem_quotientTraces (2 ^ (n - b)) m (by positivity) hm u).mp hu
  exact_mod_cast h

/-- The polynomial and class-number bounds applied to an actual quotient
trace. Its discriminant is the literal v²u²−4vm. -/
theorem norm_stratum_term_le (r v m N : ℕ) (hv : 0 < v) (hm : 0 < m) (hvN : v ≤ N)
    (u : ℤ) (hu : u ∈ quotientTraces v m)
    (hD : ((v : ℤ) * u) ^ 2 - 4 * (v : ℤ) * m < 0)
    (H : ℤ → ℝ) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hHnonneg : ∀ D : ℤ, D < 0 → 0 ≤ H D)
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ C * |(D : ℝ)| ^ (1 / 2 + δ)) :
    ‖tracePolynomial ((((v : ℝ) * (u : ℝ)) / Real.sqrt v : ℝ) : ℂ)
        (m : ℂ) (2 * r) *
      (H (((v : ℤ) * u) ^ 2 - 4 * (v : ℤ) * m) : ℂ)‖ ≤
      ((2 * r + 1 : ℕ) : ℝ) * (m : ℝ) ^ r * C *
        (4 * (N : ℝ) * m) ^ (1 / 2 + δ) := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvs : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr hvR).ne'
  have hsquare : ((v : ℝ) * (u : ℝ) / Real.sqrt v) ^ 2 = (v : ℝ) * (u : ℝ) ^ 2 := by
    field_simp [hvs]
    rw [Real.sq_sqrt hvR.le]
    ring
  have hquad : (v : ℝ) * (u : ℝ) ^ 2 ≤ 4 * m := by
    exact_mod_cast (mem_quotientTraces v m hv hm u).mp hu
  have hp := norm_signedPolynomial_le r ((v : ℝ) * (u : ℝ) / Real.sqrt v)
    (m : ℝ) (by positivity) (by rw [hsquare]; exact hquad)
  let D : ℤ := ((v : ℤ) * u) ^ 2 - 4 * (v : ℤ) * m
  have hd : (D : ℝ) < 0 := by exact_mod_cast hD
  have habs : |(D : ℝ)| ≤ 4 * (N : ℝ) * m := by
    rw [abs_of_neg hd]
    have hvNR : (v : ℝ) ≤ N := by exact_mod_cast hvN
    dsimp [D]
    push_cast
    nlinarith [sq_nonneg ((v : ℝ) * u),
      mul_nonneg (sub_nonneg.mpr hvNR) (by positivity : (0 : ℝ) ≤ m)]
  have hrpow := Real.rpow_le_rpow (abs_nonneg (D : ℝ)) habs (by linarith : 0 ≤ 1 / 2 + δ)
  have hH : ‖(H D : ℂ)‖ ≤ C * (4 * (N : ℝ) * m) ^ (1 / 2 + δ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hHnonneg D hD)]
    exact (hHgrowth D hD).trans (mul_le_mul_of_nonneg_left hrpow hC)
  change ‖tracePolynomial _ _ _ * (H D : ℂ)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (((2 * r + 1 : ℕ) : ℝ) * (m : ℝ) ^ r) *
      (C * (4 * (N : ℝ) * m) ^ (1 / 2 + δ)) :=
      mul_le_mul hp hH (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The complete literal elliptic sieve at p² satisfies the bound obtained
from the actual four strata, with the internal local coefficient cancellation
and the actual finite cardinalities both discharged. -/
theorem signed_elliptic_square_bound (r n p : ℕ) (hn : 7 ≤ n)
    (hp : 0 < p) (hodd : Odd p) (H : ℤ → ℝ) (C δ : ℝ)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hHnonneg : ∀ D : ℤ, D < 0 → 0 ≤ H D)
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ C * |(D : ℝ)| ^ (1 / 2 + δ)) :
    ‖∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
      ∑ v ∈ (2 ^ (n - j)).divisors,
        ∑ t ∈ admissibleTraces (2 ^ (n - j)) v (p ^ 2),
          tracePolynomial (((t : ℝ) / Real.sqrt v : ℝ) : ℂ) ((p ^ 2 : ℕ) : ℂ) (2 * r) *
            (H (t ^ 2 - 4 * (v : ℤ) * (p ^ 2 : ℕ)) : ℂ)‖ ≤
      4 * (1 + 16 * Real.sqrt ((p ^ 2 : ℕ) : ℝ) / Real.sqrt ((2 : ℝ) ^ n)) *
        (((2 * r + 1 : ℕ) : ℝ) * ((p ^ 2 : ℕ) : ℝ) ^ r * C *
          (4 * (2 : ℝ) ^ n * ((p ^ 2 : ℕ) : ℝ)) ^ (1 / 2 + δ)) := by
  rw [signed_elliptic_stratum_reindex n (p ^ 2) (by omega) (by positivity)]
  apply norm_coefficient_sum_le n (by omega) _ _ _ _ (by positivity)
  · intro b hb
    have hb4 : b ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl <;> omega
    exact quotientTraces_card_bound n b (p ^ 2) hb4 (by omega) (by positivity)
  · intro b hb u hu
    have hb4 : b ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl <;> omega
    have hD := surviving_square_discriminant_neg n b p hn hb4 hp hodd u hu
    have hvN : (2 : ℕ) ^ (n - b) ≤ 2 ^ n :=
      pow_le_pow_right₀ (by decide) (Nat.sub_le n b)
    have h := norm_stratum_term_le r (2 ^ (n - b)) (p ^ 2) (2 ^ n)
      (by positivity) (by positivity) hvN u hu (by simpa only [Nat.cast_pow] using hD)
      H C δ hC hδ hHnonneg hHgrowth
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] using h

end DepthAspect.SignedSieve
