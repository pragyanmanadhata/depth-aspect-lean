import DepthAspect.ContentReindex
import DepthAspect.PrimeSquareCount

/-!
# Actual elliptic prime-square trace estimates

The complete canonical trace-index count is proved in `PrimeSquareCount`.
Here it is composed with the literal class-number weighted matrix sum; the
pointwise prime-square estimate and its small-prime vanishing are conclusions.
-/
namespace DepthAspect.TraceBounds
open scoped BigOperators

/-- The literal normalized elliptic expression, with primitive class weights. -/
noncomputable def classElliptic (k n : ℕ) (d : ℝ) (m : ℤ) (H : ℤ → ℝ)
    (T : Finset ℤ) (F : ℤ → ℕ → ContentDatum) : ℂ :=
  normalizedElliptic k d (m : ℝ) T
    (fun t => literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
      (fun u => classWeightedDatum H (t ^ 2 - 4 * m) u (F t u)))

/-- Empty canonical support forces the literal elliptic expression to vanish.
This is a pure local-algebra conclusion and requires no class-number estimate
or dimension lower bound. -/
theorem classElliptic_zero_of_empty_surviving (k n : ℕ) (hn : 4 ≤ n)
    (d : ℝ) (m : ℤ) (H : ℤ → ℝ) (T : Finset ℤ) (F : ℤ → ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * m)
    (hF : ∀ t ∈ T, ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
      H ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 →
      IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (F t u))
    (he : SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m = ∅) :
    classElliptic k n d m H T F = 0 := by
  have hz : ∀ t ∈ T,
      literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
        (fun u => classWeightedDatum H (t ^ 2 - 4 * m) u (F t u)) = 0 := by
    intro t ht
    have hbad : ¬ (2 : ℤ) ^ (n - 2) ∣ t ^ 2 - 4 * m := by
      intro hdiv
      have hq : 4 * (2 : ℤ) ^ (n - 4) = 2 ^ (n - 2) := by
        rw [show n - 2 = (n - 4) + 2 by omega, pow_add]
        ring
      have hmem : t ∈ SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m := by
        apply (SurvivingTraces.mem_survivingTraces _ _ _).mpr
        refine ⟨hT t ht, ?_⟩
        rw [hq]
        simpa only [neg_sub] using dvd_neg.mpr hdiv
      rw [he] at hmem
      exact Finset.notMem_empty t hmem
    apply Finset.sum_eq_zero
    intro u hu
    change H ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) * matrixDifference n (F t u).matrix = 0
    by_cases hw : H ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) = 0
    · rw [hw, zero_mul]
    · have hM := matrixDifference_zero n (by omega) (F t u).matrix (hF t ht u hu hw).oddDet
        (by rwa [(hF t ht u hu hw).discriminant])
      rw [hM, mul_zero]
  unfold classElliptic
  rw [normalizedElliptic_filter k d (m : ℝ) T
    (fun t => literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * m))
      (fun u => classWeightedDatum H (t ^ 2 - 4 * m) u (F t u)))
    (fun _ => False) (fun t ht _ => hz t ht)]
  simp [normalizedElliptic]

/-- Equation (40), with the actual elliptic expression and complete trace count. -/
theorem classElliptic_prime_square_bound (k n : ℕ) (hn : 4 ≤ n) (P : ℤ)
    (hP : 0 < P) (hodd : Odd P) (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (H : ℤ → ℝ) (hH0 : ∀ D : ℤ, D < 0 → 0 ≤ H D)
    (hHgrowth : ∀ D : ℤ, D < 0 → H D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (T : Finset ℤ) (F : ℤ → ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * P ^ 2)
    (hF : ∀ t ∈ T, ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * P ^ 2),
      H ((t ^ 2 - 4 * P ^ 2) / (u : ℤ) ^ 2) ≠ 0 →
      IsPrimitiveContentMatrix u (t ^ 2 - 4 * P ^ 2) (F t u)) :
    ‖classElliptic k n d (P ^ 2) H T F‖ ≤
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (P : ℝ) ^ (2 * δ) *
        (128 * (P : ℝ) / (2 : ℝ) ^ n + 4) := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hN : (2 : ℝ) ^ n = 16 * (((2 : ℤ) ^ (n - 4) : ℤ) : ℝ) := by
    push_cast
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 4) + 4) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hcount := PrimeSquareCount.canonical_square_count_level (n - 4) hP hodd hN
  have hb := normalizedElliptic_class_number_bound k n hn (P ^ 2) (by positivity)
    d Ccl δ hC hδ hd H hH0 hHgrowth T F hT hF
  have hpower : (((P ^ 2 : ℤ) : ℝ)) ^ δ = (P : ℝ) ^ (2 * δ) := by
    push_cast
    simpa using (Real.rpow_natCast_mul hPR.le 2 δ).symm
  rw [hpower] at hb
  apply hb.trans
  have hK := ellipticConstant_nonneg Ccl δ hC hδ
  exact mul_le_mul_of_nonneg_left hcount (by positivity)

/-- The elliptic term of Proposition 3.4 is exactly zero in its stated range.
This uses the proved canonical empty-set result, with no assumed vanishing. -/
theorem classElliptic_prime_square_zero (k n : ℕ) (hn : 6 ≤ n) (P : ℤ)
    (hP : 0 < P) (hodd : Odd P) (hsize : (P : ℝ) < (2 : ℝ) ^ n / 64)
    (d : ℝ) (H : ℤ → ℝ) (T : Finset ℤ) (F : ℤ → ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * P ^ 2)
    (hF : ∀ t ∈ T, ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * P ^ 2),
      H ((t ^ 2 - 4 * P ^ 2) / (u : ℤ) ^ 2) ≠ 0 →
      IsPrimitiveContentMatrix u (t ^ 2 - 4 * P ^ 2) (F t u)) :
    classElliptic k n d (P ^ 2) H T F = 0 := by
  have hscale : (2 : ℝ) ^ n = 32 * (2 : ℝ) ^ (n - 5) := by
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 5) + 5) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hsizeR : 2 * (P : ℝ) < (2 : ℝ) ^ (n - 5) := by
    rw [hscale] at hsize
    linarith
  have hsizeZ : 2 * P < (2 : ℤ) ^ ((n - 4) - 1) := by
    rw [show (n - 4) - 1 = n - 5 by omega]
    exact_mod_cast hsizeR
  have he := PrimeSquareCount.canonical_square_count_zero (n - 4) (by omega) hP hodd hsizeZ
  exact classElliptic_zero_of_empty_surviving k n (by omega) d (P ^ 2) H T F hT hF he

end DepthAspect.TraceBounds
