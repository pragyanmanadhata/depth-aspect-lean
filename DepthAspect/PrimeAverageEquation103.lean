import DepthAspect.TheoremFiveFive

/-!
# The literal two-term estimate (103)

The proof below records (103) with its exact displayed exponents and the
paper's odd-prime convention (Section 1.3). It
uses the fully assembled prime-average theorem (104), whose proof
already derives and optimizes the literal three-error smoothing estimate.
Thus there is no analytic estimate assumed here and no cyclic dependency:
(104) depends on `PrimeAverageSmoothing`, not on this presentation wrapper.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DepthAspect.PrimeAverageEquation103
open DirichletRH GRHConsequences QuadraticClassFormula
open PrimeAverageSmoothing GlobalCoefficientTail SmoothingLossAbsorption

/-- The geometric-mean scale never exceeds the sum of the two unbalanced
leading terms, for every positive smoothing parameter. -/
theorem scale_le_leading {M V B x : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hB : 0 < B) (hx : 0 < x) :
    Real.sqrt M * Real.sqrt (M + V) * B ^ (3 / 4 : ℝ) ≤ leading M V B x := by
  let a : ℝ := M * B / Real.sqrt x
  let b : ℝ := (M + V) * Real.sqrt B * Real.sqrt x
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hab : a * b = (M * (M + V)) * (B * Real.sqrt B) := by
    dsimp [a, b]
    field_simp
    <;> ring
  have hscale : Real.sqrt (a * b) =
      Real.sqrt M * Real.sqrt (M + V) * B ^ (3 / 4 : ℝ) := by
    rw [hab, Real.sqrt_mul (mul_nonneg hM (add_nonneg hM hV)),
      Real.sqrt_mul hM, Smoothing.sqrt_scale B hB]
  have hsq : a * b ≤ (a + b) ^ 2 := by
    nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ha hb]
  have hroot : Real.sqrt (a * b) ≤ a + b := by
    exact (Real.sqrt_le_iff).mpr ⟨add_nonneg ha hb, hsq⟩
  rw [hscale] at hroot
  exact hroot

/-- After multiplication by B^η, the leading sum is at most the exact
right-hand side printed in (103), since x≥1. -/
theorem leading_le_displayed {M V B x η : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hB : 0 < B) (hx : 1 ≤ x) (hη : 0 ≤ η) :
    B ^ η * leading M V B x ≤
      M * B ^ (1 + η) * x ^ (-1 / 2 : ℝ) +
      (M + V) * B ^ (1 / 2 + η) * x ^ (1 / 2 + η) := by
  have hx0 : 0 < x := by linarith
  have hpow : Real.sqrt x ≤ x ^ (1 / 2 + η) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hfirst : B ^ η * (M * B / Real.sqrt x) =
      M * B ^ (1 + η) * x ^ (-1 / 2 : ℝ) := by
    rw [Real.rpow_add hB, Real.rpow_one,
      show (-1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
    ring
  have hsecond : B ^ η * ((M + V) * Real.sqrt B * Real.sqrt x) =
      (M + V) * B ^ (1 / 2 + η) * Real.sqrt x := by
    rw [Real.rpow_add hB, ← Real.sqrt_eq_rpow]
    ring
  rw [leading, mul_add, hfirst, hsecond]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- Equation (103) for exactly the paper's odd-prime convention, uniformly in
all discriminants, characters, intervals and weights. Its only analytic inputs
are primitive Dirichlet RH and the cited general implications. -/
theorem prime_average_smoothing_bound (hRH : PrimitiveDirichletRH)
    (cited : CitedGeneralTheorems) {η : ℝ} (hη : 0 < η) :
    ∃ Cη : ℝ, 0 < Cη ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (t : ℤ) (χ : DirichletCharacter ℂ 8) (A B M x : ℝ) (Φ : ℝ → ℂ),
      0 ≤ A → A ≤ B → 3 ≤ B → (t : ℝ) ^ 2 ≤ 4 * A → 0 ≤ M →
      1 ≤ x → x ≤ Real.sqrt B →
      ContinuousOn Φ (Set.Icc A B) →
      (∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u) →
      IntegrableOn (deriv Φ) (Set.Icc A B) →
      (∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) →
      ‖primeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u‖ ≤
        Cη * (M * B ^ (1 + η) * x ^ (-1 / 2 : ℝ) +
          (M + ∫ u in A..B, ‖deriv Φ u‖) * B ^ (1 / 2 + η) * x ^ (1 / 2 + η)) := by
  obtain ⟨C, hC, hb⟩ := TheoremFiveFive.prime_average_bound hRH cited hη
  refine ⟨C, hC, ?_⟩
  intro H G t χ A B M x Φ hA hAB hB ht hM hx hxB hΦ hdΦ hI hMb
  have hB0 : 0 < B := by linarith
  have hx0 : 0 < x := by linarith
  have hV : 0 ≤ ∫ u in A..B, ‖deriv Φ u‖ :=
    intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have h := hb G t χ A B M Φ hA hAB hB ht hM hΦ hdΦ hI hMb
  calc
    _ ≤ C * Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
        B ^ (3 / 4 + η) := h
    _ = C * B ^ η * (Real.sqrt M * Real.sqrt (M + ∫ u in A..B, ‖deriv Φ u‖) *
        B ^ (3 / 4 : ℝ)) := by rw [Real.rpow_add hB0]; ring
    _ ≤ C * B ^ η * leading M (∫ u in A..B, ‖deriv Φ u‖) B x :=
      mul_le_mul_of_nonneg_left (scale_le_leading hM hV hB0 hx0) (by positivity)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (leading_le_displayed hM hV hB0 hx hη.le) hC.le



end DepthAspect.PrimeAverageEquation103
