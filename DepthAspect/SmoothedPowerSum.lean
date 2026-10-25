import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Actual exponentially smoothed power sums

These are the positive Dirichlet-series majorants that occur when the
character errors are summed in (103). Their convergence and quantitative
bounds follow from the integral test and the actual Gamma integral.
-/
open MeasureTheory Set
open scoped BigOperators
namespace DepthAspect.SmoothedPowerSum

noncomputable def term (a x : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (a - 1) * Real.exp (-((n + 1 : ℕ) : ℝ) / x)

private theorem weight_integrable {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t / x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (by linarith : -1 < a - 1) (le_refl (1 : ℝ)) (inv_pos.mpr hx)
  have he (t : ℝ) : -x⁻¹ * t = -t / x := by ring
  simpa only [Real.rpow_one, he] using h

private theorem weight_antitone {a x : ℝ} (ha : a ≤ 1) (hx : 0 < x) :
    AntitoneOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t / x)) (Ici 1) := by
  intro u hu v hv huv
  change 1 ≤ u at hu
  change 1 ≤ v at hv
  have hu0 : 0 < u := by linarith [hu]
  have hv0 : 0 < v := by linarith [hv]
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos hu0 huv (by linarith)
  · exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg huv) hx.le)
  · exact (Real.exp_pos _).le
  · exact Real.rpow_nonneg hu0.le _

theorem term_nonneg (a x : ℝ) (n : ℕ) : 0 ≤ term a x n := by
  unfold term
  positivity

theorem term_summable {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) :
    Summable (term a x) := by
  have h := AntitoneOn.summable_of_integrableOn_Ioi (N := 1)
    (f := fun t : ℝ => t ^ (a - 1) * Real.exp (-t / x))
    (by simpa only [Nat.cast_one] using weight_antitone ha1 hx)
    ((weight_integrable ha hx).mono_set (Ioi_subset_Ioi (by norm_num)))
    (by
      intro t ht
      simp only [Nat.cast_one, mem_Ioi] at ht
      exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le)
  exact (summable_nat_add_iff
    (f := fun n : ℕ => (n : ℝ) ^ (a - 1) * Real.exp (-(n : ℝ) / x)) 1).mpr h

/-- A concrete Gamma constant, uniform over the smoothing length x≥1. -/
theorem term_sum_bound {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 1 ≤ x) :
    (∑' n : ℕ, term a x n) ≤ (1 + Real.Gamma a) * x ^ a := by
  have hx0 : 0 < x := by linarith
  let f : ℝ → ℝ := fun t => t ^ (a - 1) * Real.exp (-t / x)
  have hfint : IntegrableOn f (Ioi 0) := weight_integrable ha hx0
  have hfpos : ∀ t ∈ Ioi 0, 0 ≤ f t := fun t ht =>
    mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  have hfanti : AntitoneOn f (Ici (1 : ℝ)) := weight_antitone ha1 hx0
  have htail : (∑' n : ℕ, f (n + 1 + 1 : ℕ)) ≤ ∫ t : ℝ in Ioi 1, f t := by
    have h := AntitoneOn.tsum_comp_add_le_integral (f := f) 1
      (by simpa only [Nat.cast_one] using hfanti)
      (hfint.mono_set (Ioi_subset_Ioi (by norm_num)))
      (by
        intro t ht
        simp only [Nat.cast_one, mem_Ioi] at ht
        exact hfpos t (lt_trans zero_lt_one ht))
    simpa only [Nat.cast_one] using h
  have hmono : (∫ t : ℝ in Ioi 1, f t) ≤ ∫ t : ℝ in Ioi 0, f t := by
    apply setIntegral_mono_set hfint
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hfpos t ht
    · exact Filter.Eventually.of_forall (fun t ht => lt_trans zero_lt_one ht)
  have heval : (∫ t : ℝ in Ioi 0, f t) = x ^ a * Real.Gamma a := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha (inv_pos.mpr hx0)
    have he (t : ℝ) : -(x⁻¹ * t) = -t / x := by ring
    simpa only [f, he, one_div, inv_inv] using h
  have hfirst : f 1 ≤ 1 := by
    simp only [f, Real.one_rpow, one_mul]
    exact Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (by norm_num : -(1 : ℝ) ≤ 0) hx0.le)
  have htermzero : term a x 0 = f 1 := by
    simp only [term, Nat.zero_add, Nat.cast_one, f]
  rw [(term_summable ha ha1 hx0).tsum_eq_zero_add, htermzero]
  change f 1 + (∑' n : ℕ, f (n + 1 + 1 : ℕ)) ≤ _
  calc
    _ ≤ 1 + x ^ a * Real.Gamma a := add_le_add hfirst (htail.trans (hmono.trans heval.le))
    _ ≤ (1 + Real.Gamma a) * x ^ a := by
      have hxa := Real.one_le_rpow hx ha.le
      nlinarith

/-- Absorbing a squared logarithm uses the exact positive-power bound,
with a uniform explicit constant. -/
theorem log_sq_le {u δ : ℝ} (hu : 1 ≤ u) (hδ : 0 < δ) :
    Real.log u ^ 2 ≤ (4 / δ ^ 2) * u ^ δ := by
  have hu0 : 0 < u := by linarith
  have hlog := Real.log_le_rpow_div hu0.le (show 0 < δ / 2 by linarith)
  have hlog0 := Real.log_nonneg hu
  have hp0 : 0 ≤ u ^ (δ / 2) / (δ / 2) := by positivity
  have hs := pow_le_pow_left₀ hlog0 hlog 2
  calc
    _ ≤ (u ^ (δ / 2) / (δ / 2)) ^ 2 := hs
    _ = _ := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]
      have he : δ / 2 * (2 : ℕ) = δ := by norm_num <;> ring
      rw [he]
      field_simp <;> ring

/-- The explicit pointwise logarithmic absorption used in the series bound. -/
theorem log_weighted_term_le {a δ B x : ℝ} (hδ : 0 < δ) (hB : 1 ≤ B) (n : ℕ) :
    term a x n * Real.log (2 * B * (n + 1 : ℕ)) ^ 2 ≤
      ((4 / δ ^ 2) * (2 * B) ^ δ) * term (a + δ) x n := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hu : 1 ≤ 2 * B * (n + 1 : ℕ) := by
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    nlinarith
  apply (mul_le_mul_of_nonneg_left (log_sq_le hu hδ) (term_nonneg _ _ _)).trans_eq
  unfold term
  rw [Real.mul_rpow (by positivity : 0 ≤ 2 * B) hn.le]
  have he : ((n + 1 : ℕ) : ℝ) ^ (a - 1) * ((n + 1 : ℕ) : ℝ) ^ δ =
      ((n + 1 : ℕ) : ℝ) ^ (a + δ - 1) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ = ((4 / δ ^ 2) * (2 * B) ^ δ) *
        ((((n + 1 : ℕ) : ℝ) ^ (a - 1) * ((n + 1 : ℕ) : ℝ) ^ δ) *
          Real.exp (-((n + 1 : ℕ) : ℝ) / x)) := by ring
    _ = _ := by rw [he]

/-- The literal log-weighted series needed after (98) converges absolutely. -/
theorem log_weighted_summable {a δ B x : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (haδ : a + δ ≤ 1) (hB : 1 ≤ B) (hx : 0 < x) :
    Summable (fun n : ℕ => term a x n * Real.log (2 * B * (n + 1 : ℕ)) ^ 2) := by
  exact ((term_summable (by linarith) haδ hx).mul_left _).of_nonneg_of_le
    (fun n => mul_nonneg (term_nonneg _ _ _) (sq_nonneg _)) (log_weighted_term_le hδ hB)

/-- Its explicit quantitative bound gives the `x^(1/2+η)` term after
summing the actual Fourier/GRH errors. -/
theorem log_weighted_sum_bound {a δ B x : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (haδ : a + δ ≤ 1) (hB : 1 ≤ B) (hx : 1 ≤ x) :
    (∑' n : ℕ, term a x n * Real.log (2 * B * (n + 1 : ℕ)) ^ 2) ≤
      ((4 / δ ^ 2) * 2 ^ δ * (1 + Real.Gamma (a + δ))) * B ^ δ * x ^ (a + δ) := by
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ ∑' n : ℕ, ((4 / δ ^ 2) * (2 * B) ^ δ) * term (a + δ) x n :=
      Summable.tsum_le_tsum (log_weighted_term_le hδ hB)
        (log_weighted_summable ha hδ haδ hB hx0)
        ((term_summable (by linarith) haδ hx0).mul_left _)
    _ = ((4 / δ ^ 2) * (2 * B) ^ δ) * (∑' n : ℕ, term (a + δ) x n) := tsum_mul_left
    _ ≤ ((4 / δ ^ 2) * (2 * B) ^ δ) * ((1 + Real.Gamma (a + δ)) * x ^ (a + δ)) :=
      mul_le_mul_of_nonneg_left (term_sum_bound (by linarith) haδ hx) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ B)]; ring

end DepthAspect.SmoothedPowerSum
