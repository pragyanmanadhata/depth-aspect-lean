import DepthAspect.BesselFirstKind
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The square-root substitution used to integrate each actual Bessel term
in (129). Monotone change of variables handles the endpoint at zero. -/
open MeasureTheory Set
namespace DepthAspect.BesselSqrtIntegral
open BesselFirstKind

/-- The transformed integrand has its correct value at the origin, since
the Bessel order is positive. -/
theorem transformed_integrand {m : ℕ} (hm : 0 < m) (α : ℝ) {x : ℝ}
    (hx : 0 ≤ x) :
    (J m (α * Real.sqrt (x ^ 2)) / Real.sqrt (x ^ 2)) * (2 * x) =
      2 * J m (α * x) := by
  rw [Real.sqrt_sq hx]
  by_cases hx0 : x = 0
  · subst x
    simp [J_zero_of_pos hm]
  · field_simp
    <;> ring

/-- The individual square-root Bessel term is integrable, with its
normalization derived by two actual changes of variables. -/
theorem integral_bessel_sqrt (hDLMF : DLMFIdentities) {m : ℕ}
    (hm : 0 < m) {α Z : ℝ} (hα : 0 < α) (hZ : 0 ≤ Z) :
    (∫ y : ℝ in (0)..Z, J m (α * Real.sqrt y) / Real.sqrt y) =
      (2 / α) * ∫ t : ℝ in (0)..(α * Real.sqrt Z), J m t := by
  let f : ℝ → ℝ := fun x => x ^ 2
  let f' : ℝ → ℝ := fun x => 2 * x
  let q : ℝ → ℝ := fun y => J m (α * Real.sqrt y) / Real.sqrt y
  have hs := Real.sqrt_nonneg Z
  have hderiv (x : ℝ) : HasDerivAt f (f' x) x := by
    simpa [f, f'] using (hasDerivAt_pow 2 x)
  have hdpos : ∀ x ∈ Ioo (min 0 (Real.sqrt Z)) (max 0 (Real.sqrt Z)), 0 ≤ f' x := by
    intro x hx
    rw [min_eq_left hs, max_eq_right hs] at hx
    dsimp [f']
    exact mul_nonneg (by norm_num) hx.1.le
  have hcv := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := f) (f' := f') (g := q) (a := 0) (b := Real.sqrt Z)
    (by fun_prop) (fun x _ => hderiv x) hdpos
  have he : (∫ x : ℝ in (0)..Real.sqrt Z, (q ∘ f) x * f' x) =
      ∫ x : ℝ in (0)..Real.sqrt Z, 2 * J m (α * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hs] at hx
    exact transformed_integrand hm α hx.1
  simp only [f, zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt hZ] at hcv
  rw [he] at hcv
  rw [← hcv, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t => J m t) (ne_of_gt hα)]
  simp only [mul_zero, smul_eq_mul]
  ring

/-- The same substitution proves integrability before any infinite sum is
interchanged with this integral. -/
theorem intervalIntegrable_bessel_sqrt (hDLMF : DLMFIdentities) {m : ℕ}
    (hm : 0 < m) (α : ℝ) {Z : ℝ} (hZ : 0 ≤ Z) :
    IntervalIntegrable (fun y => J m (α * Real.sqrt y) / Real.sqrt y) volume 0 Z := by
  let f : ℝ → ℝ := fun x => x ^ 2
  let f' : ℝ → ℝ := fun x => 2 * x
  let q : ℝ → ℝ := fun y => J m (α * Real.sqrt y) / Real.sqrt y
  have hs := Real.sqrt_nonneg Z
  have hd (x : ℝ) : HasDerivAt f (f' x) x := by
    simpa [f, f'] using (hasDerivAt_pow 2 x)
  have hp : ∀ x ∈ Ioo (min 0 (Real.sqrt Z)) (max 0 (Real.sqrt Z)), 0 ≤ f' x := by
    intro x hx
    rw [min_eq_left hs, max_eq_right hs] at hx
    dsimp [f']
    exact mul_nonneg (by norm_num) hx.1.le
  have he := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (f := f) (f' := f') (g := q) (a := 0) (b := Real.sqrt Z)
    (by fun_prop) (fun x _ => hd x) hp
  have hcont : Continuous (fun x : ℝ => 2 * J m (α * x)) :=
    continuous_const.mul ((hDLMF.continuous m).comp (continuous_const.mul continuous_id))
  have hi : IntervalIntegrable (fun x => (q ∘ f) x * f' x) volume 0 (Real.sqrt Z) := by
    have heq : EqOn (fun x => (q ∘ f) x * f' x)
        (fun x => 2 * J m (α * x)) (uIoc 0 (Real.sqrt Z)) := by
      intro x hx
      have hx' := uIoc_subset_uIcc hx
      rw [uIcc_of_le hs] at hx'
      exact transformed_integrand hm α hx'.1
    exact (intervalIntegrable_congr heq).mpr (hcont.intervalIntegrable 0 (Real.sqrt Z))
  have hresult := he.mp hi
  simpa only [f, zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt hZ] using hresult

end DepthAspect.BesselSqrtIntegral
