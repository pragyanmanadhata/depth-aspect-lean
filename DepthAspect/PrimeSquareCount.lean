import DepthAspect.SurvivingTraces
import DepthAspect.GeneralRoots

/-!
# Canonical prime-square trace-index counts

An actual residue/quotient injection bounds all roots in `(-P,P)` by four
residue classes times the number of possible quotient blocks. This proves
(39), without assuming a bound on `T_N(P²)` or a four-class interval count.
-/
namespace DepthAspect.PrimeSquareCount

open SurvivingTraces SquareDivisibility GeneralRoots

/-- Residue plus a shifted quotient uniquely specifies the original integer. -/
def intervalEncoding (q P r : ℤ) : ℤ × ℤ := (r % q, (r + P) / q)

theorem intervalEncoding_injective (q P : ℤ) : Function.Injective (intervalEncoding q P) := by
  intro r s heq
  have hrem := congrArg (fun z : ℤ × ℤ => z.1) heq
  have hquot := congrArg (fun z : ℤ × ℤ => z.2) heq
  change r % q = s % q at hrem
  change (r + P) / q = (s + P) / q at hquot
  have hshift : (r + P) % q = (s + P) % q := by
    rw [Int.add_emod r P q, Int.add_emod s P q, hrem]
  have hr := Int.emod_add_mul_ediv (r + P) q
  have hs := Int.emod_add_mul_ediv (s + P) q
  rw [hshift, hquot] at hr
  omega

/-- Every actual square-index root maps into a root residue and a bounded
quotient interval. -/
theorem intervalEncoding_mem (j : ℕ) {P r : ℤ} (hP : 0 < P)
    (hr : r ∈ halvedTraces ((2 : ℤ) ^ j) (P ^ 2)) :
    intervalEncoding ((2 : ℤ) ^ j) P r ∈
      squareRoots j (P ^ 2) ×ˢ Finset.Icc 0 (2 * P / (2 : ℤ) ^ j) := by
  obtain ⟨hrsq, hrdiv⟩ := (mem_halvedTraces _ _ _).mp hr
  have hq : 0 < (2 : ℤ) ^ j := by positivity
  obtain ⟨hrleft, hrright⟩ := abs_lt_of_sq_lt_sq' hrsq hP.le
  apply Finset.mem_product.mpr
  constructor
  · apply (mem_squareRoots j (P ^ 2) _).mpr
    refine ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq, ?_⟩
    apply (PeriodicCounting.square_periodic ((2 : ℤ) ^ j) (P ^ 2) r).mp
    simpa only [neg_sub] using dvd_neg.mpr hrdiv
  · apply Finset.mem_Icc.mpr
    exact ⟨Int.ediv_nonneg (by omega) hq.le, Int.ediv_le_ediv hq (by omega)⟩

/-- The exact natural-number interval bound before casting to real quotients. -/
theorem canonical_square_count_nat (j : ℕ) {P : ℤ} (hP : 0 < P) (hodd : Odd P) :
    (survivingTraces ((2 : ℤ) ^ j) (P ^ 2)).card ≤
      4 * (2 * P / (2 : ℤ) ^ j + 1).toNat := by
  rw [survivingTraces_card_eq]
  have hc := Finset.card_le_card_of_injOn (intervalEncoding ((2 : ℤ) ^ j) P)
    (fun r hr => intervalEncoding_mem j hP hr)
    (intervalEncoding_injective ((2 : ℤ) ^ j) P).injOn
  rw [Finset.card_product, Int.card_Icc, sub_zero] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (squareRoots_odd_card_le_four j hodd.pow))

/-- Equation (39), with the actual complete trace-index set. -/
theorem canonical_square_count (j : ℕ) {P : ℤ} (hP : 0 < P) (hodd : Odd P) :
    ((survivingTraces ((2 : ℤ) ^ j) (P ^ 2)).card : ℝ) ≤
      4 * (2 * (P : ℝ) / (((2 : ℤ) ^ j : ℤ) : ℝ) + 1) := by
  have hq : 0 < (2 : ℤ) ^ j := by positivity
  have hqR : 0 < (((2 : ℤ) ^ j : ℤ) : ℝ) := by exact_mod_cast hq
  have hz : 0 ≤ 2 * P / (2 : ℤ) ^ j := Int.ediv_nonneg (by omega) hq.le
  have hcast : (((2 * P / (2 : ℤ) ^ j + 1).toNat : ℕ) : ℝ) =
      ((2 * P / (2 : ℤ) ^ j : ℤ) : ℝ) + 1 := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ 2 * P / (2 : ℤ) ^ j + 1)
  have hc : ((survivingTraces ((2 : ℤ) ^ j) (P ^ 2)).card : ℝ) ≤
      4 * ((2 * P / (2 : ℤ) ^ j : ℤ) : ℝ) + 4 := by
    have hh := canonical_square_count_nat j hP hodd
    have hhR : ((survivingTraces ((2 : ℤ) ^ j) (P ^ 2)).card : ℝ) ≤
        4 * (((2 * P / (2 : ℤ) ^ j + 1).toNat : ℕ) : ℝ) := by exact_mod_cast hh
    rw [hcast] at hhR
    linarith
  have hdiv : ((2 * P / (2 : ℤ) ^ j : ℤ) : ℝ) ≤
      2 * (P : ℝ) / (((2 : ℤ) ^ j : ℤ) : ℝ) := by
    apply (le_div_iff₀ hqR).mpr
    exact_mod_cast Int.ediv_mul_le (2 * P) hq.ne'
  nlinarith

/-- The paper's `128P/N+4` form, for `N=16q`. -/
theorem canonical_square_count_level (j : ℕ) {P : ℤ} {N : ℝ}
    (hP : 0 < P) (hodd : Odd P) (hN : N = 16 * (((2 : ℤ) ^ j : ℤ) : ℝ)) :
    ((survivingTraces ((2 : ℤ) ^ j) (P ^ 2)).card : ℝ) ≤
      128 * (P : ℝ) / N + 4 := by
  have hc := canonical_square_count j hP hodd
  have heq : 4 * (2 * (P : ℝ) / (((2 : ℤ) ^ j : ℤ) : ℝ) + 1) = 128 * (P : ℝ) / N + 4 := by
    rw [hN]
    ring
  rwa [heq] at hc

/-- The exact complete trace-index set in Proposition 3.4 vanishes in the
small-prime range. The root-exclusion proof is already valid for every odd P. -/
theorem canonical_square_count_zero (j : ℕ) (hj : 2 ≤ j) {P : ℤ}
    (hP : 0 < P) (hodd : Odd P) (hsize : 2 * P < (2 : ℤ) ^ (j - 1)) :
    survivingTraces ((2 : ℤ) ^ j) (P ^ 2) = ∅ := by
  rw [survivingTraces_eq_image]
  have he : halvedTraces ((2 : ℤ) ^ j) (P ^ 2) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hrsq, hrdiv⟩ := (mem_halvedTraces _ _ _).mp hr
    obtain ⟨hrleft, hrright⟩ := abs_lt_of_sq_lt_sq' hrsq hP.le
    apply LocalArithmetic.no_interior_square_root (h := j - 2) hP hodd
      (by simpa only [show j - 2 + 1 = j - 1 by omega] using hsize) hrleft hrright
    rw [show j - 2 + 2 = j by omega]
    simpa only [neg_sub] using dvd_neg.mpr hrdiv
  rw [he, Finset.image_empty]

end DepthAspect.PrimeSquareCount
