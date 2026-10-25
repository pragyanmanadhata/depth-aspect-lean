import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The archimedean digamma estimate

The series in DLMF (5.7.6) is defined term by term. Its summability and the
bound in Lemma 4.6 are proved here, rather than supplied as hypotheses.
The only explicit external interface is the cited identification of that
series with the actual logarithmic derivative of Gamma. The positive-integer
value is proved for Mathlib's actual digamma directly from its recurrence.
-/

open scoped BigOperators

namespace DepthAspect.DigammaBound

/-- A summable numerical majorant for the concrete series terms. -/
noncomputable def inverseSquare (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ 2

theorem inverse_square_le_telescoping {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  calc
    1 / (x + 1) ^ 2 ≤ 1 / (x * (x + 1)) :=
      one_div_le_one_div_of_le (mul_pos hx hx1) (by nlinarith)
    _ = 1 / x - 1 / (x + 1) := by
      field_simp [ne_of_gt hx, ne_of_gt hx1]
      ring

/-- Integral comparison is replaced by an explicit telescoping majorant. -/
theorem inverseSquare_partial_bound (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), inverseSquare n) ≤ 2 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num [inverseSquare]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := inverse_square_le_telescoping (x := (N : ℝ) + 1) (by positivity)
    simp only [inverseSquare, Nat.cast_add, Nat.cast_one] at *
    linarith

theorem inverseSquare_sum_range_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, inverseSquare n) ≤ 2 := by
  cases N with
  | zero => simp
  | succ N =>
    have h := inverseSquare_partial_bound N
    have hp : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    linarith

theorem inverseSquare_summable : Summable inverseSquare :=
  summable_of_sum_range_le (fun n => by unfold inverseSquare; positivity)
    inverseSquare_sum_range_le_two

theorem inverseSquare_tsum_le_two : (∑' n, inverseSquare n) ≤ 2 :=
  Real.tsum_le_of_sum_range_le (fun n => by unfold inverseSquare; positivity)
    inverseSquare_sum_range_le_two

/-- The exact term of the series cited as DLMF (5.7.6). -/
noncomputable def seriesTerm (z : ℂ) (n : ℕ) : ℂ :=
  ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + z)⁻¹

/-- The concrete series expression for the logarithmic derivative of Gamma. -/
noncomputable def seriesDigamma (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) + ∑' n : ℕ, seriesTerm z n

theorem nat_add_norm_lower {z : ℂ} (hz : 1 ≤ z.re) (n : ℕ) :
    (n : ℝ) + 1 ≤ ‖(n : ℂ) + z‖ := by
  calc
    (n : ℝ) + 1 ≤ ((n : ℂ) + z).re := by simp only [Complex.add_re, Complex.natCast_re]; linarith
    _ ≤ ‖(n : ℂ) + z‖ := Complex.re_le_norm _

theorem nat_add_ne_zero {z : ℂ} (hz : 1 ≤ z.re) (n : ℕ) :
    (n : ℂ) + z ≠ 0 := by
  have hp : 0 < (n : ℝ) + 1 := by positivity
  exact norm_pos_iff.mp (hp.trans_le (nat_add_norm_lower hz n))

theorem seriesTerm_sub (z w : ℂ) (n : ℕ)
    (hz : (n : ℂ) + z ≠ 0) (hw : (n : ℂ) + w ≠ 0) :
    seriesTerm z n - seriesTerm w n =
      (z - w) / (((n : ℂ) + w) * ((n : ℂ) + z)) := by
  have heq : seriesTerm z n - seriesTerm w n =
      ((n : ℂ) + w)⁻¹ - ((n : ℂ) + z)⁻¹ := by unfold seriesTerm; ring
  rw [heq]
  field_simp [hz, hw]
  ring

/-- Every actual difference term is controlled by an inverse square. -/
theorem seriesTerm_sub_norm_le {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re)
    (n : ℕ) :
    ‖seriesTerm z n - seriesTerm w n‖ ≤ ‖z - w‖ * inverseSquare n := by
  rw [seriesTerm_sub z w n (nat_add_ne_zero hz n) (nat_add_ne_zero hw n),
    norm_div, norm_mul]
  have hbase : 0 < (n : ℝ) + 1 := by positivity
  have hz' := nat_add_norm_lower hz n
  have hw' := nat_add_norm_lower hw n
  have hprod : ((n : ℝ) + 1) ^ 2 ≤ ‖(n : ℂ) + w‖ * ‖(n : ℂ) + z‖ := by
    nlinarith [norm_nonneg ((n : ℂ) + w), norm_nonneg ((n : ℂ) + z)]
  calc
    ‖z - w‖ / (‖(n : ℂ) + w‖ * ‖(n : ℂ) + z‖) ≤
        ‖z - w‖ / ((n : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hbase) hprod
    _ = ‖z - w‖ * inverseSquare n := by unfold inverseSquare; ring

theorem seriesTerm_norm_le {z : ℂ} (hz : 1 ≤ z.re) (n : ℕ) :
    ‖seriesTerm z n‖ ≤ ‖z - 1‖ * inverseSquare n := by
  simpa only [seriesTerm, sub_self, sub_zero] using
    seriesTerm_sub_norm_le hz (show 1 ≤ (1 : ℂ).re by norm_num) n

/-- Absolute convergence of the series on the closed half plane Re z ≥ 1. -/
theorem seriesTerm_norm_summable {z : ℂ} (hz : 1 ≤ z.re) :
    Summable (fun n => ‖seriesTerm z n‖) :=
  (inverseSquare_summable.mul_left ‖z - 1‖).of_nonneg_of_le
    (fun _ => norm_nonneg _) (seriesTerm_norm_le hz)

theorem seriesTerm_summable {z : ℂ} (hz : 1 ≤ z.re) :
    Summable (seriesTerm z) :=
  (inverseSquare_summable.mul_left ‖z - 1‖).of_norm_bounded (seriesTerm_norm_le hz)

/-- A half-plane Lipschitz bound obtained from the concrete series. -/
theorem seriesDigamma_norm_sub_le {z w : ℂ} (hz : 1 ≤ z.re) (hw : 1 ≤ w.re) :
    ‖seriesDigamma z - seriesDigamma w‖ ≤ 2 * ‖z - w‖ := by
  have heq : seriesDigamma z - seriesDigamma w =
      ∑' n : ℕ, (seriesTerm z n - seriesTerm w n) := by
    rw [(seriesTerm_summable hz).tsum_sub (seriesTerm_summable hw)]
    unfold seriesDigamma
    ring
  rw [heq]
  have hb := tsum_of_norm_bounded
    (inverseSquare_summable.hasSum.mul_left ‖z - w‖) (seriesTerm_sub_norm_le hz hw)
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left inverseSquare_tsum_le_two (norm_nonneg (z - w))])

/-- Lemma 4.6 for the explicitly convergent series. -/
theorem seriesDigamma_vertical_bound (a t : ℝ) (ha : 1 ≤ a) :
    ‖seriesDigamma ((a : ℂ) + (t : ℂ) * Complex.I) - seriesDigamma (a : ℂ)‖ ≤
      2 * |t| := by
  have hz : 1 ≤ ((a : ℂ) + (t : ℂ) * Complex.I).re := by simpa using ha
  have hw : 1 ≤ (a : ℂ).re := ha
  have h := seriesDigamma_norm_sub_le hz hw
  simpa only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one] using h

/-- The legitimate external input (58): DLMF's series identity for the actual
digamma. It contains no bound, convergence premise, or conclusion of this paper. -/
def DLMFSeriesIdentity : Prop :=
  ∀ z : ℂ, 1 ≤ z.re → Complex.digamma z = seriesDigamma z

/-- The actual Gamma logarithmic derivative satisfies (57), conditional only
on the cited DLMF identity. The estimate itself has been proved above. -/
theorem digamma_vertical_bound_of_dlmf (hDLMF : DLMFSeriesIdentity)
    (a t : ℝ) (ha : 1 ≤ a) :
    ‖Complex.digamma ((a : ℂ) + (t : ℂ) * Complex.I) - Complex.digamma (a : ℂ)‖ ≤
      2 * |t| := by
  rw [hDLMF _ (by simpa using ha), hDLMF _ ha]
  exact seriesDigamma_vertical_bound a t ha

/-- Equation (57) with the Gamma derivative quotient written explicitly. -/
theorem gamma_derivative_quotient_bound_of_dlmf (hDLMF : DLMFSeriesIdentity)
    (a t : ℝ) (ha : 1 ≤ a) :
    ‖deriv Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) /
        Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I) -
      deriv Complex.Gamma (a : ℂ) / Complex.Gamma (a : ℂ)‖ ≤ 2 * |t| := by
  simpa only [Complex.digamma_def, logDeriv_apply] using
    digamma_vertical_bound_of_dlmf hDLMF a t ha

/-- Telescoping the actual digamma recurrence gives the positive-integer value.
Mathlib's `harmonic n` is the actual finite sum of reciprocals. -/
theorem digamma_nat_add_one (n : ℕ) :
    Complex.digamma ((n : ℂ) + 1) =
      (harmonic n : ℂ) - (Real.eulerMascheroniConstant : ℂ) := by
  induction n with
  | zero => simpa using Complex.digamma_one
  | succ n ih =>
    have havoid : ∀ m : ℕ, (n : ℂ) + 1 ≠ -(m : ℂ) := by
      intro m heq
      have hreal := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
        Complex.neg_re] at hreal
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      linarith
    rw [Nat.cast_succ, Complex.digamma_apply_add_one _ havoid, ih, harmonic_succ]
    push_cast
    ring

theorem digamma_positive_integer (a : ℕ) (ha : 1 ≤ a) :
    Complex.digamma (a : ℂ) =
      (harmonic (a - 1) : ℂ) - (Real.eulerMascheroniConstant : ℂ) := by
  have h := digamma_nat_add_one (a - 1)
  have heq : ((a - 1 : ℕ) : ℂ) + 1 = (a : ℂ) := by
    exact_mod_cast (Nat.sub_add_cancel ha)
  rwa [heq] at h

end DepthAspect.DigammaBound
