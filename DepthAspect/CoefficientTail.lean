import DepthAspect.CoefficientDecomposition
import DepthAspect.SquarefreeCoefficientProduct
import DepthAspect.SmoothingKernel
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The triple-sum estimate behind the literal coefficient tail

The natural numbers are injected into the actual decompositions `2^b*u*v²`.
The squarefree weight and the exponential cutoff are literal. This module
proves the numerical consequence of the pointwise squarefree majorant; the
arithmetic identification of that majorant is a separate CRT/local-mean step.
-/

noncomputable section
open scoped BigOperators
namespace DepthAspect.CoefficientTail
open CoefficientDecomposition

noncomputable def squarefreeWeight (u : SquarefreeOdd) : ℝ :=
  1 / (Real.sqrt (u : ℕ) * ((u : ℕ).totient : ℝ))
noncomputable def ratio : ℝ := (Real.sqrt 2)⁻¹
noncomputable def tailConstant : ℝ :=
  4 / (1 - ratio) * SquarefreeCoefficientProduct.productConstant

noncomputable def tripleTerm (x : ℝ) (i : Indices) : ℝ :=
  (1 / ((2 : ℝ) ^ i.1 * (i.2.1 : ℕ) * ((i.2.1 : ℕ).totient : ℝ))) *
    SmoothingKernel.term (x / ((2 : ℝ) ^ i.1 * (i.2.1 : ℕ))) i.2.2

private theorem u_pos (u : SquarefreeOdd) : (0 : ℝ) < (u : ℕ) := by
  exact_mod_cast Nat.pos_of_ne_zero u.property.1.ne_zero
private theorem phi_pos (u : SquarefreeOdd) : (0 : ℝ) < (u : ℕ).totient := by
  exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero u.property.1.ne_zero)

theorem squarefreeWeight_nonneg (u : SquarefreeOdd) : 0 ≤ squarefreeWeight u := by
  unfold squarefreeWeight
  positivity

theorem ratio_nonneg : 0 ≤ ratio := inv_nonneg.mpr (Real.sqrt_nonneg _)
theorem ratio_lt_one : ratio < 1 := by
  have hsq : 1 < Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have h0 := Real.sqrt_nonneg 2
    nlinarith
  exact (inv_lt_one₀ (Real.sqrt_pos.mpr (by norm_num))).mpr hsq

theorem ratio_summable : Summable (fun b : ℕ => ratio ^ b) :=
  summable_geometric_of_abs_lt_one (by rw [abs_of_nonneg ratio_nonneg]; exact ratio_lt_one)

theorem ratio_sum : (∑' b : ℕ, ratio ^ b) = 1 / (1 - ratio) := by
  simpa only [one_div] using
    (tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg ratio_nonneg]; exact ratio_lt_one))

private theorem sqrt_two_pow (b : ℕ) : Real.sqrt ((2 : ℝ) ^ b) = Real.sqrt 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

theorem tripleTerm_nonneg {x : ℝ} (hx : 0 < x) (i : Indices) : 0 ≤ tripleTerm x i := by
  unfold tripleTerm
  exact mul_nonneg (by positivity)
    (SmoothingKernel.term_nonneg (div_pos hx (mul_pos (by positivity) (u_pos _))) _)

theorem tripleTerm_inner_summable {x : ℝ} (hx : 0 < x) (b : ℕ) (u : SquarefreeOdd) :
    Summable (fun v : ℕ => tripleTerm x (b, u, v)) := by
  change Summable (fun v : ℕ =>
    (1 / ((2 : ℝ) ^ b * (u : ℕ) * ((u : ℕ).totient : ℝ))) *
      SmoothingKernel.term (x / ((2 : ℝ) ^ b * (u : ℕ))) v)
  exact (SmoothingKernel.term_summable
    (div_pos hx (mul_pos (by positivity) (u_pos u)))).mul_left _

/-- Summing the square part gives the factor 4/sqrt(x), with the exact
squarefree and dyadic factors displayed. -/
theorem tripleTerm_inner_bound {x : ℝ} (hx : 0 < x) (b : ℕ) (u : SquarefreeOdd) :
    (∑' v : ℕ, tripleTerm x (b, u, v)) ≤
      (4 / Real.sqrt x) * ratio ^ b * squarefreeWeight u := by
  have hT : 0 < x / ((2 : ℝ) ^ b * (u : ℕ)) :=
    div_pos hx (mul_pos (by positivity) (u_pos u))
  simp only [tripleTerm, Prod.fst, Prod.snd]
  rw [tsum_mul_left]
  calc
    _ ≤ (1 / ((2 : ℝ) ^ b * (u : ℕ) * ((u : ℕ).totient : ℝ))) *
        (4 / Real.sqrt (x / ((2 : ℝ) ^ b * (u : ℕ)))) :=
      mul_le_mul_of_nonneg_left (SmoothingKernel.tsum_term_le hT) (by positivity)
    _ = _ := by
      have hA : 0 < (2 : ℝ) ^ b * (u : ℕ) := mul_pos (by positivity) (u_pos u)
      have hxS : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
      have hAS : Real.sqrt ((2 : ℝ) ^ b * (u : ℕ)) ≠ 0 :=
        (Real.sqrt_pos.mpr hA).ne'
      have hphi : ((u : ℕ).totient : ℝ) ≠ 0 := (phi_pos u).ne'
      calc
        _ = (4 / Real.sqrt x) *
            (Real.sqrt ((2 : ℝ) ^ b * (u : ℕ)) / ((2 : ℝ) ^ b * (u : ℕ))) /
              ((u : ℕ).totient : ℝ) := by
          rw [Real.sqrt_div hx.le]
          field_simp [hxS, hAS, hA.ne', hphi] <;> ring
        _ = _ := by
          rw [Real.sqrt_div_self, Real.sqrt_mul (by positivity), sqrt_two_pow,
            mul_inv_rev, ← inv_pow]
          unfold ratio squarefreeWeight
          ring

private theorem squarefree_sum_summable : Summable squarefreeWeight :=
  SquarefreeCoefficientProduct.squarefree_weight_summable

private theorem squarefree_sum_nonneg : 0 ≤ ∑' u : SquarefreeOdd, squarefreeWeight u :=
  tsum_nonneg squarefreeWeight_nonneg

private theorem pair_summable {x : ℝ} (hx : 0 < x) (b : ℕ) :
    Summable (fun uv : SquarefreeOdd × ℕ => tripleTerm x (b, uv)) := by
  apply (summable_prod_of_nonneg (fun i => tripleTerm_nonneg hx (b, i))).mpr
  refine ⟨tripleTerm_inner_summable hx b, ?_⟩
  apply (squarefree_sum_summable.mul_left ((4 / Real.sqrt x) * ratio ^ b)).of_nonneg_of_le
  · intro u
    exact tsum_nonneg (fun v => tripleTerm_nonneg hx (b, u, v))
  · exact tripleTerm_inner_bound hx b

private theorem pair_sum_bound {x : ℝ} (hx : 0 < x) (b : ℕ) :
    (∑' uv : SquarefreeOdd × ℕ, tripleTerm x (b, uv)) ≤
      ((4 / Real.sqrt x) * ratio ^ b) * (∑' u : SquarefreeOdd, squarefreeWeight u) := by
  rw [(pair_summable hx b).tsum_prod]
  calc
    _ ≤ ∑' u : SquarefreeOdd, ((4 / Real.sqrt x) * ratio ^ b) * squarefreeWeight u := by
      apply Summable.tsum_le_tsum (tripleTerm_inner_bound hx b)
      · exact ((summable_prod_of_nonneg (fun i => tripleTerm_nonneg hx (b, i))).mp
          (pair_summable hx b)).2
      · exact squarefree_sum_summable.mul_left _
    _ = _ := tsum_mul_left

/-- Absolute convergence of the literal positive triple majorant. -/
theorem tripleTerm_summable {x : ℝ} (hx : 0 < x) : Summable (tripleTerm x) := by
  apply (summable_prod_of_nonneg (tripleTerm_nonneg hx)).mpr
  refine ⟨pair_summable hx, ?_⟩
  apply ((ratio_summable.mul_left (4 / Real.sqrt x)).mul_right
    (∑' u : SquarefreeOdd, squarefreeWeight u)).of_nonneg_of_le
  · intro b
    exact tsum_nonneg (fun uv => tripleTerm_nonneg hx (b, uv))
  · exact pair_sum_bound hx

/-- The numerical constant is precisely the convergent prime product in
(85), after summing the actual dyadic geometric series. -/
theorem tripleTerm_sum_bound {x : ℝ} (hx : 0 < x) :
    (∑' i : Indices, tripleTerm x i) ≤ tailConstant / Real.sqrt x := by
  rw [(tripleTerm_summable hx).tsum_prod]
  calc
    _ ≤ ∑' b : ℕ, ((4 / Real.sqrt x) * ratio ^ b) *
        (∑' u : SquarefreeOdd, squarefreeWeight u) := by
      apply Summable.tsum_le_tsum (pair_sum_bound hx)
      · exact ((summable_prod_of_nonneg (tripleTerm_nonneg hx)).mp (tripleTerm_summable hx)).2
      · exact (ratio_summable.mul_left _).mul_right _
    _ = (4 / Real.sqrt x) * (1 / (1 - ratio)) *
        (∑' u : SquarefreeOdd, squarefreeWeight u) := by
      rw [tsum_mul_right, tsum_mul_left, ratio_sum]
    _ ≤ (4 / Real.sqrt x) * (1 / (1 - ratio)) *
        SquarefreeCoefficientProduct.productConstant := by
      apply mul_le_mul_of_nonneg_left SquarefreeCoefficientProduct.squarefree_weight_sum_le
      have hr : 0 < 1 - ratio := sub_pos.mpr ratio_lt_one
      positivity
    _ = _ := by unfold tailConstant; ring

/-- The arithmetic pointwise majorant implies the coefficient tail through
the actual natural-number decomposition injection. This is an intermediate
lemma; its majorant must be supplied by the proved CRT/local-average chain. -/
theorem tail_summable_and_bound (a : ℕ → ℂ)
    (hmajor : ∀ b : ℕ, ∀ u : SquarefreeOdd, ∀ v : ℕ, 0 < v → Odd v →
      ‖a (2 ^ b * (u : ℕ) * v ^ 2)‖ ≤ 1 / ((u : ℕ).totient : ℝ))
    {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))) ∧
    (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))) ≤ tailConstant / Real.sqrt x := by
  let f : ℕ → ℝ := fun n => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))
  have hnonneg (n : ℕ) : 0 ≤ f n := by
    have h := (SmoothingKernel.one_sub_exp_neg_le_min
      (y := ((n + 1 : ℕ) : ℝ) / x) (by positivity)).1
    dsimp [f]
    rw [← neg_div] at h
    exact mul_nonneg (by positivity) h
  have hpoint (n : ℕ) : f n ≤ tripleTerm x (decompose n) := by
    let i := decompose n
    have hi := reconstruct_decompose n
    have hv := decompose_odd_square_part n
    have hma := hmajor i.1 i.2.1 (i.2.2 + 1) (by omega) hv
    have hrec : 2 ^ i.1 * (i.2.1 : ℕ) * (i.2.2 + 1) ^ 2 = n + 1 := hi
    have huR : (0 : ℝ) < (i.2.1 : ℕ) := u_pos _
    have hphiR : (0 : ℝ) < (i.2.1 : ℕ).totient := phi_pos _
    have hvR : (0 : ℝ) < (i.2.2 : ℝ) + 1 := by positivity
    rw [hrec] at hma
    have hy : 0 ≤ ((n + 1 : ℕ) : ℝ) / x := by positivity
    have hexp := (SmoothingKernel.one_sub_exp_neg_le_min hy).2
    rw [← neg_div] at hexp
    dsimp [f]
    calc
      _ ≤ (1 / ((i.2.1 : ℕ).totient : ℝ)) / ((n + 1 : ℕ) : ℝ) *
          min 1 (((n + 1 : ℕ) : ℝ) / x) :=
        mul_le_mul (div_le_div_of_nonneg_right hma (by positivity)) hexp
          (by simpa only [neg_div] using (SmoothingKernel.one_sub_exp_neg_le_min hy).1)
          (by positivity)
      _ = _ := by
        change _ = tripleTerm x i
        unfold tripleTerm SmoothingKernel.term DigammaBound.inverseSquare
        rw [← hrec]
        push_cast
        have hcut : ((i.2.2 : ℝ) + 1) ^ 2 /
            (x / ((2 : ℝ) ^ i.1 * (i.2.1 : ℕ))) =
            ((2 : ℝ) ^ i.1 * (i.2.1 : ℕ) * ((i.2.2 : ℝ) + 1) ^ 2) / x := by
          field_simp
          <;> ring
        rw [hcut]
        field_simp
        <;> ring
  have hs := (tripleTerm_summable hx).comp_injective decompose_injective
  have hf : Summable f := hs.of_nonneg_of_le hnonneg hpoint
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, tripleTerm x (decompose n) := Summable.tsum_le_tsum hpoint hf hs
    _ ≤ ∑' i : Indices, tripleTerm x i :=
      tsum_comp_le_tsum_of_inj (tripleTerm_summable hx) (tripleTerm_nonneg hx) decompose_injective
    _ ≤ _ := tripleTerm_sum_bound hx

/-- The first estimate in (85), together with the separate convergence
statement above, for any coefficient sequence with the proved local majorant. -/
theorem tail_of_decomposition_majorant (a : ℕ → ℂ)
    (hmajor : ∀ b : ℕ, ∀ u : SquarefreeOdd, ∀ v : ℕ, 0 < v → Odd v →
      ‖a (2 ^ b * (u : ℕ) * v ^ 2)‖ ≤ 1 / ((u : ℕ).totient : ℝ))
    {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-((n + 1 : ℕ) : ℝ) / x))) ≤ tailConstant / Real.sqrt x :=
  (tail_summable_and_bound a hmajor hx).2

/-- The unsmoothed coefficient series converges absolutely, with exactly
the final constant in (85). This avoids relying on a default `tsum` value. -/
theorem absolute_series_summable_and_bound (a : ℕ → ℂ)
    (hmajor : ∀ b : ℕ, ∀ u : SquarefreeOdd, ∀ v : ℕ, 0 < v → Odd v →
      ‖a (2 ^ b * (u : ℕ) * v ^ 2)‖ ≤ 1 / ((u : ℕ).totient : ℝ)) :
    Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ)) ∧
    (∑' n : ℕ, ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ)) ≤
      tailConstant / (1 - Real.exp (-1)) := by
  let g : ℕ → ℝ := fun n => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) *
    (1 - Real.exp (-((n + 1 : ℕ) : ℝ)))
  have hpos : 0 < 1 - Real.exp (-1) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0)
    linarith
  obtain ⟨hgs, hgb⟩ := tail_summable_and_bound a hmajor (x := 1) (by norm_num)
  simp only [div_one, Real.sqrt_one] at hgs hgb
  have hpoint (n : ℕ) : ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ≤
      (1 - Real.exp (-1))⁻¹ * g n := by
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    have he : Real.exp (-((n + 1 : ℕ) : ℝ)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.mpr (by linarith)
    have he' : 1 - Real.exp (-1) ≤ 1 - Real.exp (-((n + 1 : ℕ) : ℝ)) := by linarith
    have hm := mul_le_mul_of_nonneg_left he'
      (show 0 ≤ ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) by positivity)
    calc
      _ ≤ g n / (1 - Real.exp (-1)) := (le_div_iff₀ hpos).mpr hm
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have hs : Summable (fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ)) :=
    (hgs.mul_left (1 - Real.exp (-1))⁻¹).of_nonneg_of_le (fun n => by positivity) hpoint
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (1 - Real.exp (-1))⁻¹ * g n :=
      Summable.tsum_le_tsum hpoint hs (hgs.mul_left _)
    _ = (1 - Real.exp (-1))⁻¹ * ∑' n : ℕ, g n := tsum_mul_left
    _ ≤ (1 - Real.exp (-1))⁻¹ * tailConstant :=
      mul_le_mul_of_nonneg_left hgb (inv_nonneg.mpr hpos.le)
    _ = _ := by ring

end DepthAspect.CoefficientTail
