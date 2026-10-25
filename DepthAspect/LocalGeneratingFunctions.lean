import DepthAspect.LocalResidueAverages
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.LinearCombination

/-!
# Generating functions of the computed local residue averages

The recurrence used here is the finite residue identity proved in
LocalResidueAverages. The resulting rational functions are the two branches
of (83). The analytic sums are actual absolutely convergent power series.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.LocalGeneratingFunctions
open LocalResidueAverages

variable {p : ℕ} [Fact p.Prime]

private theorem norm_lt_one_ne_one {w : ℂ} (hw : ‖w‖ < 1) : w ≠ 1 := by
  intro h
  rw [h, norm_one] at hw
  exact (lt_irrefl 1) hw

set_option maxHeartbeats 600000 in
/-- The actual parity series, including its degree-zero term. -/
theorem parity_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun b : ℕ => if Even b then z ^ b else 0) ((1 - z ^ 2)⁻¹) := by
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have he : HasSum (fun b : ℕ => if Even (2 * b) then z ^ (2 * b) else 0)
      ((1 - z ^ 2)⁻¹) := by
    simpa only [even_two_mul, ↓reduceIte, pow_mul] using
      hasSum_geometric_of_norm_lt_one hz2
  have ho : HasSum (fun b : ℕ => if Even (2 * b + 1) then z ^ (2 * b + 1) else 0) 0 := by
    simp only [Nat.not_even_bit1, ↓reduceIte]
    exact hasSum_zero
  simpa only [add_zero] using
    HasSum.even_add_odd (f := fun b : ℕ => if Even b then z ^ b else 0) he ho

def meanSeries (z : ℂ) : ℂ := ∑' b : ℕ, (mean (p := p) b : ℂ) * z ^ b

theorem meanSeries_summable (hp2 : p ≠ 2) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun b : ℕ => (mean (p := p) b : ℂ) * z ^ b) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz)
  intro b
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mean_bounds hp2 b).1]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) _) (mean_bounds hp2 b).2

/-- The recurrence gives this exact algebraic equation for the convergent series. -/
theorem meanSeries_equation (hp2 : p ≠ 2) {z : ℂ} (hz : ‖z‖ < 1) :
    meanSeries (p := p) z - 1 =
      (1 - 1 / (p : ℂ)) * ((1 - z ^ 2)⁻¹ - 1) +
        (z / (p : ℂ) ^ 2) * meanSeries (p := p) z := by
  have hpz : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs := (meanSeries_summable hp2 hz).hasSum
  change HasSum _ (meanSeries (p := p) z) at hs
  have hs' : HasSum (fun b : ℕ => (mean (p := p) (b + 1) : ℂ) * z ^ (b + 1))
      (meanSeries (p := p) z - 1) := by
    simpa only [Finset.sum_range_one, mean_zero, Complex.ofReal_one, pow_zero, mul_one] using
      (hasSum_nat_add_iff' 1).mpr hs
  have he : HasSum (fun b : ℕ => if Even (b + 1) then z ^ (b + 1) else 0)
      ((1 - z ^ 2)⁻¹ - 1) := by
    simpa only [Finset.sum_range_one, Even.zero, ↓reduceIte, pow_zero] using
      (hasSum_nat_add_iff' 1).mpr (parity_hasSum hz)
  have ht := (he.mul_left (1 - 1 / (p : ℂ))).add (hs.mul_left (z / (p : ℂ) ^ 2))
  apply hs'.unique
  apply ht.congr_fun
  intro b
  rw [mean_succ hp2]
  push_cast
  split_ifs <;> push_cast <;> simp only [pow_succ] <;> field_simp [hpz] <;> ring

/-- The rational unrestricted generating function displayed before (83). -/
theorem meanSeries_eq (hp2 : p ≠ 2) {z : ℂ} (hz : ‖z‖ < 1) :
    meanSeries (p := p) z =
      (1 - z ^ 2 / (p : ℂ)) / ((1 - z ^ 2) * (1 - z / (p : ℂ) ^ 2)) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hd1 : 1 - z ^ 2 ≠ 0 := sub_ne_zero.mpr (norm_lt_one_ne_one hz2).symm
  have hzp : ‖z / (p : ℂ) ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, Complex.norm_natCast]
    apply (div_lt_iff₀ (by positivity : 0 < (p : ℝ) ^ 2)).mpr
    nlinarith
  have hd2 : 1 - z / (p : ℂ) ^ 2 ≠ 0 := sub_ne_zero.mpr (norm_lt_one_ne_one hzp).symm
  have h := meanSeries_equation hp2 hz
  apply (eq_div_iff (mul_ne_zero hd1 hd2)).mpr
  field_simp [hp0, hd1] at h ⊢
  linear_combination h

/-- Excluding the nonzero square class gives this identity in every degree,
including zero; it is the finite mean computed in (86). -/
theorem unitMean_affine (hp2 : p ≠ 2) {t : ZMod p} (ht : t ≠ 0) (b : ℕ) :
    unitMean (p := p) b t = ((p : ℝ) * mean (p := p) b - 1) / ((p : ℝ) - 1) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    linarith
  cases b with
  | zero => simp [unitMean, mean_zero, hp1]
  | succ b =>
    rw [unitMean_nonzero hp2 b ht, mean_succ hp2]
    split_ifs <;> field_simp <;> ring

/-- The first branch of (83), for a parameter divisible by p. -/
theorem unitMean_zero_hasSum (hp2 : p ≠ 2) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun b : ℕ => (unitMean (p := p) b 0 : ℂ) * z ^ b) ((1 - z ^ 2)⁻¹) := by
  simpa only [unitMean_zero hp2, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero, ite_mul, one_mul, zero_mul] using parity_hasSum hz

/-- The second branch of (83), for a parameter prime to p. -/
theorem unitMean_nonzero_hasSum (hp2 : p ≠ 2) {t : ZMod p} (ht : t ≠ 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun b : ℕ => (unitMean (p := p) b t : ℂ) * z ^ b)
      (((p : ℂ) ^ 2 - ((p : ℂ) + 1) * z - ((p : ℂ) + 1) * z ^ 2) /
        ((1 - z ^ 2) * ((p : ℂ) ^ 2 - z))) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (Fact.out : p.Prime).ne_one
  have h := (((meanSeries_summable hp2 hz).hasSum.mul_left (p : ℂ)).sub
    (hasSum_geometric_of_norm_lt_one hz)).div_const ((p : ℂ) - 1)
  have hvalue : ((p : ℂ) * meanSeries (p := p) z - (1 - z)⁻¹) / ((p : ℂ) - 1) =
      (((p : ℂ) ^ 2 - ((p : ℂ) + 1) * z - ((p : ℂ) + 1) * z ^ 2) /
        ((1 - z ^ 2) * ((p : ℂ) ^ 2 - z))) := by
    rw [meanSeries_eq hp2 hz]
    have hz1 : 1 - z ≠ 0 := sub_ne_zero.mpr (norm_lt_one_ne_one hz).symm
    have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
    have hd1 : 1 - z ^ 2 ≠ 0 := sub_ne_zero.mpr (norm_lt_one_ne_one hz2).symm
    have hpz : (p : ℂ) ^ 2 - z ≠ 0 := by
      intro he
      have hz' : z = (p : ℂ) ^ 2 := (sub_eq_zero.mp he).symm
      rw [hz', norm_pow, Complex.norm_natCast] at hz
      have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
      nlinarith
    field_simp [hp0, hp1, hz1, hd1, hpz]
    ring
  rw [← hvalue]
  apply h.congr_fun
  intro b
  rw [unitMean_affine hp2 ht]
  push_cast
  ring

end DepthAspect.LocalGeneratingFunctions
