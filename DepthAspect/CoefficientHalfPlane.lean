import DepthAspect.GlobalResidueMean
import DepthAspect.SquarefreeSigmaProduct
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# The actual coefficient series on Re(s)>1/2

The positive-index sequence is the literal residue average. The proof uses
its actual squarefree decomposition and the convergent squarefree Euler
product, and establishes the displayed absolute bound (87).
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.CoefficientHalfPlane
open CoefficientDecomposition GlobalResidueMean

noncomputable def dyadicRatio (σ : ℝ) : ℝ := (2 : ℝ) ^ (-σ)
noncomputable def squarefreeTerm (σ : ℝ) (u : SquarefreeOdd) : ℝ :=
  1 / (((u : ℕ) : ℝ) ^ σ * ((u : ℕ).totient : ℝ))
noncomputable def squareTerm (σ : ℝ) (n : ℕ) : ℝ :=
  1 / (((n + 1 : ℕ) : ℝ) ^ (2 * σ))
noncomputable def tripleTerm (σ : ℝ) (i : Indices) : ℝ :=
  dyadicRatio σ ^ i.1 * (squarefreeTerm σ i.2.1 * squareTerm σ i.2.2)
noncomputable def zetaSeries (σ : ℝ) : ℝ := ∑' n, squareTerm σ n

 theorem dyadicRatio_lt_one {σ : ℝ} (hσ : 0 < σ) : dyadicRatio σ < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
 theorem dyadicRatio_pos (σ : ℝ) : 0 < dyadicRatio σ := Real.rpow_pos_of_pos (by norm_num) _
 theorem squarefreeTerm_nonneg (σ : ℝ) (u : SquarefreeOdd) : 0 ≤ squarefreeTerm σ u := by
  unfold squarefreeTerm
  positivity
 theorem squareTerm_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ squareTerm σ n := by
  unfold squareTerm
  positivity
 theorem tripleTerm_nonneg (σ : ℝ) (i : Indices) : 0 ≤ tripleTerm σ i := by
  exact mul_nonneg (pow_nonneg (dyadicRatio_pos σ).le _)
    (mul_nonneg (squarefreeTerm_nonneg σ _) (squareTerm_nonneg σ _))

 theorem squareTerm_summable {σ : ℝ} (hσ : 1 / 2 < σ) : Summable (squareTerm σ) := by
  exact (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 2 * σ))

 theorem dyadic_summable {σ : ℝ} (hσ : 0 < σ) : Summable (fun b : ℕ => dyadicRatio σ ^ b) :=
  summable_geometric_of_lt_one (dyadicRatio_pos σ).le (dyadicRatio_lt_one hσ)

 theorem pair_summable {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun i : SquarefreeOdd × ℕ => squarefreeTerm σ i.1 * squareTerm σ i.2) :=
  (SquarefreeSigmaProduct.squarefree_weight_summable (by linarith : 0 < σ)).mul_of_nonneg
    (squareTerm_summable hσ) (squarefreeTerm_nonneg σ) (squareTerm_nonneg σ)

 theorem tripleTerm_summable {σ : ℝ} (hσ : 1 / 2 < σ) : Summable (tripleTerm σ) :=
  (dyadic_summable (by linarith : 0 < σ)).mul_of_nonneg (pair_summable hσ)
    (fun b => pow_nonneg (dyadicRatio_pos σ).le b)
    (fun i => mul_nonneg (squarefreeTerm_nonneg σ i.1) (squareTerm_nonneg σ i.2))

 theorem tripleTerm_sum_bound {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' i : Indices, tripleTerm σ i) ≤
      zetaSeries σ / (1 - dyadicRatio σ) * SquarefreeSigmaProduct.productConstant σ := by
  have hσ0 : 0 < σ := by linarith
  have hsum : (∑' i : Indices, tripleTerm σ i) =
      (∑' b : ℕ, dyadicRatio σ ^ b) *
        ((∑' u : SquarefreeOdd, squarefreeTerm σ u) * (∑' n, squareTerm σ n)) := by
    calc
      _ = (∑' b : ℕ, dyadicRatio σ ^ b) *
          (∑' j : SquarefreeOdd × ℕ, squarefreeTerm σ j.1 * squareTerm σ j.2) :=
        ((dyadic_summable hσ0).tsum_mul_tsum (pair_summable hσ)
          (tripleTerm_summable hσ)).symm
      _ = _ := by
        congr 1
        exact ((SquarefreeSigmaProduct.squarefree_weight_summable hσ0).tsum_mul_tsum
          (squareTerm_summable hσ) (pair_summable hσ)).symm
  rw [hsum, tsum_geometric_of_lt_one (dyadicRatio_pos σ).le (dyadicRatio_lt_one hσ0)]
  have hbound := SquarefreeSigmaProduct.squarefree_weight_sum_le hσ0
  have hz : 0 ≤ zetaSeries σ := tsum_nonneg (squareTerm_nonneg σ)
  have hd : 0 < 1 - dyadicRatio σ := sub_pos.mpr (dyadicRatio_lt_one hσ0)
  calc
    _ = zetaSeries σ / (1 - dyadicRatio σ) *
        (∑' u : SquarefreeOdd, squarefreeTerm σ u) := by unfold zetaSeries; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (div_nonneg hz hd.le)

private theorem reconstruct_weight (σ : ℝ) (i : Indices) :
    (1 / ((i.2.1 : ℕ).totient : ℝ)) / ((reconstruct i : ℕ) : ℝ) ^ σ = tripleTerm σ i := by
  have hu : (0 : ℝ) < (i.2.1 : ℕ) := by
    exact_mod_cast Nat.pos_of_ne_zero i.2.1.property.1.ne_zero
  have hv : (0 : ℝ) < (i.2.2 : ℝ) + 1 := by positivity
  have hφ : (0 : ℝ) < (i.2.1 : ℕ).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero i.2.1.property.1.ne_zero)
  unfold reconstruct tripleTerm dyadicRatio squarefreeTerm squareTerm
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) hu.le,
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) σ i.1,
    ← Real.rpow_natCast_mul hv.le 2 σ]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : (2 : ℝ) ^ σ ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) σ).ne'
  have huσ := (Real.rpow_pos_of_pos hu σ).ne'
  have hvσ := (Real.rpow_pos_of_pos hv (2 * σ)).ne'
  rw [inv_pow]
  field_simp [h2, huσ, hvσ, hφ.ne']

/-- The precise decomposition bound for a sequence with the proved local
squarefree majorant. The public actual-sequence theorem below discharges it. -/
theorem absolute_sum_of_majorant (a : ℕ → ℂ)
    (hmajor : ∀ b : ℕ, ∀ u : SquarefreeOdd, ∀ v : ℕ, 0 < v → Odd v →
      ‖a (2 ^ b * (u : ℕ) * v ^ 2)‖ ≤ 1 / ((u : ℕ).totient : ℝ))
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ σ) ∧
    (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ σ) ≤
      zetaSeries σ / (1 - dyadicRatio σ) * SquarefreeSigmaProduct.productConstant σ := by
  have hpoint (n : ℕ) : ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ σ ≤
      tripleTerm σ (decompose n) := by
    let i := decompose n
    have hm := hmajor i.1 i.2.1 (i.2.2 + 1) (by omega) (decompose_odd_square_part n)
    have hi := reconstruct_decompose n
    change reconstruct i = n + 1 at hi
    rw [← hi]
    exact (div_le_div_of_nonneg_right hm (Real.rpow_nonneg (Nat.cast_nonneg _) _)).trans_eq
      (reconstruct_weight σ i)
  have hs := (tripleTerm_summable hσ).comp_injective decompose_injective
  have ha := hs.of_nonneg_of_le (fun n => by positivity) hpoint
  refine ⟨ha, ?_⟩
  exact ((Summable.tsum_le_tsum hpoint ha hs).trans
    (tsum_comp_le_tsum_of_inj (tripleTerm_summable hσ) (tripleTerm_nonneg σ)
      decompose_injective)).trans (tripleTerm_sum_bound hσ)

/-- The actual absolute-convergence and bound (87). -/
theorem absolute_coefficient_series (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ σ) ∧
    (∑' n : ℕ, ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ σ) ≤
      zetaSeries σ / (1 - dyadicRatio σ) * SquarefreeSigmaProduct.productConstant σ :=
  absolute_sum_of_majorant (sequence t χ) (sequence_majorant t χ) hσ

/-- The actual averaged L-series is absolutely convergent throughout the
half-plane claimed in (84), not only at s=1. -/
theorem LSeriesSummable_average (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {s : ℂ} (hs : 1 / 2 < s.re) : LSeriesSummable (sequence t χ) s := by
  apply (summable_nat_add_iff 1).mp
  apply Summable.of_norm
  simpa only [LSeries.term_of_ne_zero (Nat.succ_ne_zero _), norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.succ_pos _) s] using
      (absolute_coefficient_series t χ hs).1

/-- The square-part series is the actual zeta value, not an unnamed constant. -/
theorem zetaSeries_eq (σ : ℝ) (hσ : 1 / 2 < σ) :
    (zetaSeries σ : ℂ) = riemannZeta ((2 * σ : ℝ) : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using
    (show (1 : ℝ) < 2 * σ by linarith)), zetaSeries, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [squareTerm, Complex.ofReal_div, Complex.ofReal_one]
  rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))]
  push_cast
  rfl

/-- The displayed (87) with its literal zeta and prime-product constants. -/
theorem displayed_absolute_bound (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' n : ℕ, ‖sequence t χ (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ σ) ≤
      (riemannZeta ((2 * σ : ℝ) : ℂ)).re / (1 - (2 : ℝ) ^ (-σ)) *
        SquarefreeSigmaProduct.productConstant σ := by
  have hz := congrArg Complex.re (zetaSeries_eq σ hσ)
  simpa only [Complex.ofReal_re, ← hz, dyadicRatio] using
    (absolute_coefficient_series t χ hσ).2

end DepthAspect.CoefficientHalfPlane
