import DepthAspect.OrderedDirichlet
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp

/-!
# The ordered value at one and the analytic boundary value

The uniform tail estimate is proved by finite Abel summation. This separates
the ordered Dirichlet value at one from Mathlib's unordered LSeries there.
-/

open Filter
open scoped BigOperators Topology
namespace DepthAspect.OrderedAbel

open OrderedDirichlet

noncomputable def weightedPartial (a w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range n, w (i + 1) * a (i + 1)

noncomputable def powerPartial (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  weightedPartial a (fun j => ((j : ℝ) ^ (-σ) : ℝ)) n

@[simp] theorem weightedPartial_succ (a w : ℕ → ℂ) (n : ℕ) :
    weightedPartial a w (n + 1) = weightedPartial a w n + w (n + 1) * a (n + 1) := by
  simp only [weightedPartial, Finset.sum_range_succ]

/-- Finite Abel summation for arbitrary complex weights. -/
theorem weightedPartial_sub_eq (a w : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) :
    weightedPartial a w M - weightedPartial a w N =
      w M * partialSum a M - w N * partialSum a N +
        ∑ i ∈ Finset.Ico N M, (w i - w (i + 1)) * partialSum a i := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [weightedPartial_succ, partialSum_succ, Finset.sum_Ico_succ_top hNM]
    linear_combination ih

theorem sum_Ico_weight_difference (w : ℕ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    (∑ i ∈ Finset.Ico N M, (w i - w (i + 1))) = w N - w M := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    rw [Finset.sum_Ico_succ_top hNM, ih]
    ring

private theorem norm_real_mul_partialSum_le (a : ℕ → ℂ) {B r : ℝ}
    (hB : ∀ n, ‖partialSum a n‖ ≤ B) (hr : 0 ≤ r) (n : ℕ) :
    ‖(r : ℂ) * partialSum a n‖ ≤ r * B := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left (hB n) hr

/-- The crucial tail estimate is uniform for every real exponent σ ≥ 1. -/
theorem finite_power_tail_bound (a : ℕ → ℂ) {B : ℝ}
    (hB : ∀ n, ‖partialSum a n‖ ≤ B) {σ : ℝ} (hσ : 1 ≤ σ)
    {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) :
    ‖powerPartial a σ M - powerPartial a σ N‖ ≤ 2 * B / N := by
  let w : ℕ → ℝ := fun j => (j : ℝ) ^ (-σ)
  have hB0 : 0 ≤ B := by simpa [partialSum] using hB 0
  have hw0 : ∀ j, 0 ≤ w j := fun j => Real.rpow_nonneg (Nat.cast_nonneg j) _
  have hmono : ∀ i ∈ Finset.Ico N M, 0 ≤ w i - w (i + 1) := by
    intro i hi
    have hiN := (Finset.mem_Ico.mp hi).1
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast hN.trans_le hiN
    · exact_mod_cast Nat.le_succ i
    · linarith
  have hfinite : ‖powerPartial a σ M - powerPartial a σ N‖ ≤
      w M * B + w N * B + ∑ i ∈ Finset.Ico N M, (w i - w (i + 1)) * B := by
    unfold powerPartial
    rw [weightedPartial_sub_eq a (fun j => (w j : ℂ)) hNM]
    calc
      _ ≤ ‖(w M : ℂ) * partialSum a M‖ + ‖(w N : ℂ) * partialSum a N‖ +
          ∑ i ∈ Finset.Ico N M, ‖((w i : ℂ) - (w (i + 1) : ℂ)) * partialSum a i‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_sum_le _ _))
      _ ≤ _ := by
        apply add_le_add
        · exact add_le_add (norm_real_mul_partialSum_le a hB (hw0 M) M)
            (norm_real_mul_partialSum_le a hB (hw0 N) N)
        · apply Finset.sum_le_sum
          intro i hi
          rw [← Complex.ofReal_sub]
          exact norm_real_mul_partialSum_le a hB (hmono i hi) i
  have heq : w M * B + w N * B +
      (∑ i ∈ Finset.Ico N M, (w i - w (i + 1)) * B) = 2 * B * w N := by
    rw [← Finset.sum_mul, sum_Ico_weight_difference w hNM]
    ring
  rw [heq] at hfinite
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from hN)
  have hwN : w N ≤ (N : ℝ)⁻¹ := by
    unfold w
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
  calc
    _ ≤ 2 * B * w N := hfinite
    _ ≤ 2 * B * (N : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hwN (by positivity)
    _ = _ := by rw [div_eq_mul_inv]

/-- The σ=1 member is exactly the ordered partial sum used elsewhere. -/
theorem powerPartial_one (a : ℕ → ℂ) (n : ℕ) :
    powerPartial a 1 n = partialL a n := by
  unfold powerPartial weightedPartial partialL
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Real.rpow_neg_one, Complex.ofReal_inv, Complex.ofReal_natCast,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_one, div_eq_mul_inv]
  ring


/-- For σ>1, the finite power sums converge to Mathlib's actual (absolutely
convergent) L-series. This statement is deliberately not asserted at σ=1. -/
theorem powerPartial_tendsto_LSeries (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (powerPartial a σ) atTop (𝓝 (LSeries a (σ : ℂ))) := by
  have hsum := (LSeriesSummable_of_bounded_of_one_lt_real (fun n _ => ha n) hσ).hasSum
  rw [← hasSum_nat_add_iff' 1] at hsum
  simp only [Finset.sum_range_one, LSeries.term_zero, sub_zero] at hsum
  have heq (j : ℕ) : ((((j + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * a (j + 1) =
      LSeries.term a (σ : ℂ) (j + 1) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (j + 1)) (-σ), Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.cpow_neg,
      LSeries.term_of_ne_zero (Nat.succ_ne_zero j)]
    simp only [div_eq_mul_inv, mul_comm]
  have heqfun : powerPartial a σ =
      (fun n => ∑ i ∈ Finset.range n, LSeries.term a (σ : ℂ) (i + 1)) := by
    funext n
    unfold powerPartial weightedPartial
    apply Finset.sum_congr rfl
    intro j hj
    exact heq j
  rw [heqfun]
  exact hsum.tendsto_sum_nat

theorem LSeries_tail_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {B : ℝ}
    (hB : ∀ n, ‖partialSum a n‖ ≤ B) {σ : ℝ} (hσ : 1 < σ)
    {N : ℕ} (hN : 0 < N) :
    ‖LSeries a (σ : ℂ) - powerPartial a σ N‖ ≤ 2 * B / N := by
  apply le_of_tendsto ((powerPartial_tendsto_LSeries a ha hσ).sub_const
    (powerPartial a σ N)).norm
  filter_upwards [eventually_ge_atTop N] with M hNM
  exact finite_power_tail_bound a hB hσ.le hN hNM

theorem ordered_tail_bound (a : ℕ → ℂ) {B : ℝ}
    (hB : ∀ n, ‖partialSum a n‖ ≤ B) {L : ℂ}
    (hL : Tendsto (partialL a) atTop (𝓝 L)) {N : ℕ} (hN : 0 < N) :
    ‖L - powerPartial a 1 N‖ ≤ 2 * B / N := by
  have hlim : Tendsto (powerPartial a 1) atTop (𝓝 L) := by
    have heq : powerPartial a 1 = partialL a := funext (powerPartial_one a)
    rw [heq]
    exact hL
  apply le_of_tendsto (hlim.sub_const (powerPartial a 1 N)).norm
  filter_upwards [eventually_ge_atTop N] with M hNM
  exact finite_power_tail_bound a hB (by norm_num) hN hNM

theorem powerPartial_continuous (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun σ : ℝ => powerPartial a σ N) := by
  unfold powerPartial weightedPartial
  apply continuous_finsetSum
  intro j hj
  have hjpos : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hw : Continuous (fun σ : ℝ => ((j + 1 : ℕ) : ℝ) ^ (-σ)) :=
    (Real.continuous_const_rpow hjpos.ne').comp continuous_neg
  exact (Complex.continuous_ofReal.comp hw).mul continuous_const


/-- Abelian boundary convergence at 1. Only the values with σ>1 use `LSeries`;
the limiting value is supplied by an actual ordered-partial-sum limit. -/
theorem LSeries_tendsto_ordered_value (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {B : ℝ} (hB : ∀ n, ‖partialSum a n‖ ≤ B) {L : ℂ}
    (hL : Tendsto (partialL a) atTop (𝓝 L)) :
    Tendsto (fun σ : ℝ => LSeries a (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 L) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (6 * B / ε))
  have hNR : (0 : ℝ) < N := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hN)
  have hNnat : 0 < N := by exact_mod_cast hNR
  have hlarge : 6 * B < (N : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hN)
  have hsmall : 2 * B / N < ε / 3 := by
    apply (div_lt_iff₀ hNR).mpr
    nlinarith
  have hcont : Tendsto (fun σ : ℝ => powerPartial a σ N)
      (𝓝[>] (1 : ℝ)) (𝓝 (powerPartial a 1 N)) :=
    (powerPartial_continuous a N).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hclose := Metric.tendsto_nhds.mp hcont (ε / 3) (by positivity)
  filter_upwards [hclose, show ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), 1 < σ from
    self_mem_nhdsWithin] with σ hclose hσ
  have hfirst := LSeries_tail_bound a ha hB hσ hNnat
  have hlast : ‖powerPartial a 1 N - L‖ ≤ 2 * B / N := by
    rw [norm_sub_rev]
    exact ordered_tail_bound a hB hL hNnat
  have ht := dist_triangle (LSeries a (σ : ℂ)) (powerPartial a σ N) L
  have hm := dist_triangle (powerPartial a σ N) (powerPartial a 1 N) L
  simp only [dist_eq_norm] at ht hm hclose ⊢
  linarith

/-- Any continuous continuation agreeing with the defining series to the
right of 1 has exactly the ordered value at 1. This is the precise bridge
needed by the class-number formula and avoids an unordered endpoint `tsum`. -/
theorem continuation_value_eq_ordered (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {B : ℝ} (hB : ∀ n, ‖partialSum a n‖ ≤ B) {L : ℂ}
    (hL : Tendsto (partialL a) atTop (𝓝 L))
    (G : ℂ → ℂ) (hG : ContinuousAt G 1)
    (hseries : ∀ σ : ℝ, 1 < σ → G (σ : ℂ) = LSeries a (σ : ℂ)) :
    G 1 = L := by
  have hlimG : Tendsto (fun σ : ℝ => G (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (G 1)) := by
    have hcast : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact hG.tendsto.comp hcast
  have heq : (fun σ : ℝ => G (σ : ℂ)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun σ : ℝ => LSeries a (σ : ℂ)) := by
    filter_upwards [show ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), 1 < σ from
      self_mem_nhdsWithin] with σ hσ
    exact hseries σ hσ
  exact tendsto_nhds_unique hlimG ((LSeries_tendsto_ordered_value a ha hB hL).congr' heq.symm)

end DepthAspect.OrderedAbel
