import DepthAspect.FiniteCharacterFourier
import DepthAspect.EndpointAbel
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp

/-!
# Weighted prime averages from the general GRH character estimate

The arithmetic input is exactly the general cumulative character estimate
(92), for every Dirichlet character. The weight, Fourier expansion, principal
coefficient, and partial-summation error are constructed and proved here.
Neither (98) nor any local residue mean or coefficient bound is assumed.
-/

noncomputable section
open Finset MeasureTheory
open scoped BigOperators Classical
namespace DepthAspect.CharacterPrimeAverages

variable {q : ℕ} [NeZero q]

/-- The actual logarithmic prime coefficient of a character. -/
def primeCoeff (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n.Prime then χ (n : ZMod q) * (Real.log n : ℂ) else 0

/-- Its actual cumulative prime sum. -/
def theta (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊u⌋₊, primeCoeff χ n

/-- Principal-character indicator. -/
def principal (χ : DirichletCharacter ℂ q) : ℂ := if χ = 1 then 1 else 0

/-- The input supplied by the cited general GRH theorem, equation (92).
This concerns all characters, before choosing any discriminant residue function. -/
def GRHCharacterEstimate (C : ℝ) : Prop :=
  ∀ χ : DirichletCharacter ℂ q, ∀ u : ℝ, 2 ≤ u →
    ‖theta χ u - principal χ * (u : ℂ)‖ ≤
      C * Real.sqrt u * Real.log (2 * (q : ℝ) * u) ^ 2

/-- The actual finite weighted prime sum in (A,B]. -/
def weighted (χ : DirichletCharacter ℂ q) (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, Φ n * primeCoeff χ n

 theorem theta_of_lt_two (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : u < 2) :
    theta χ u = 0 := by
  unfold theta
  apply Finset.sum_eq_zero
  intro n hn
  have hn2 : n < 2 := (Finset.mem_Icc.mp hn).2.trans_lt
    ((Nat.floor_lt' (by norm_num : (2 : ℕ) ≠ 0)).mpr hu)
  have hp : ¬ n.Prime := fun hp => (not_lt_of_ge hp.two_le) hn2
  simp [primeCoeff, hp]

 theorem principal_norm_le (χ : DirichletCharacter ℂ q) : ‖principal χ‖ ≤ 1 := by
  classical
  unfold principal
  split_ifs <;> norm_num

/-- A single monotone envelope also covers points below the first prime. -/
def envelope (C B : ℝ) (q : ℕ) : ℝ :=
  C * Real.sqrt B * Real.log (2 * (q : ℝ) * B) ^ 2 + 2

 theorem cumulative_error_bound {C B u : ℝ} (hC : 0 ≤ C)
    (hGRH : GRHCharacterEstimate (q := q) C) (hB : 2 ≤ B)
    (hu0 : 0 ≤ u) (huB : u ≤ B) (χ : DirichletCharacter ℂ q) :
    ‖theta χ u - principal χ * (u : ℂ)‖ ≤ envelope C B q := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hmain0 : 0 ≤ C * Real.sqrt B * Real.log (2 * (q : ℝ) * B) ^ 2 := by positivity
  by_cases hu : 2 ≤ u
  · have hlu : 0 ≤ Real.log (2 * (q : ℝ) * u) :=
      Real.log_nonneg (by nlinarith)
    have hmono : C * Real.sqrt u * Real.log (2 * (q : ℝ) * u) ^ 2 ≤
        C * Real.sqrt B * Real.log (2 * (q : ℝ) * B) ^ 2 := by
      gcongr
    exact (hGRH χ u hu).trans (hmono.trans (by unfold envelope; linarith))
  · rw [theta_of_lt_two χ (lt_of_not_ge hu), zero_sub, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    calc
      _ ≤ u := by simpa using mul_le_mul_of_nonneg_right (principal_norm_le χ) hu0
      _ ≤ envelope C B q := by unfold envelope; linarith

/-- Exact weighted partial summation, allowing only interior differentiability
and continuity at the two endpoints. -/
theorem weighted_abel {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (χ : DirichletCharacter ℂ q) (Φ : ℝ → ℂ)
    (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ x ∈ Set.Ioo A B, DifferentiableAt ℝ Φ x)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B)) :
    weighted χ A B Φ = Φ B * theta χ B - Φ A * theta χ A -
      ∫ x in A..B, deriv Φ x * theta χ x := by
  have h := EndpointAbel.sum_mul_eq_sub_sub_integral_mul_endpoint
    (primeCoeff χ) hA hAB hΦ hdΦ hI
  rw [← intervalIntegral.integral_of_le hAB] at h
  exact h

/-- Subtracting the principal main integral gives exactly the cumulative-error
pairing. This is the analytic step in (98), not an estimate premise. -/
theorem weighted_error_identity {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (χ : DirichletCharacter ℂ q) (Φ : ℝ → ℂ)
    (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ x ∈ Set.Ioo A B, DifferentiableAt ℝ Φ x)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B)) :
    weighted χ A B Φ - principal χ * ∫ x in A..B, Φ x =
      Φ B * (theta χ B - principal χ * (B : ℂ)) -
      Φ A * (theta χ A - principal χ * (A : ℂ)) -
      ∫ x in A..B, deriv Φ x * (theta χ x - principal χ * (x : ℂ)) := by
  have hdI : IntervalIntegrable (deriv Φ) volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hI
  have hΦu : ContinuousOn Φ (Set.uIcc A B) := by simpa [Set.uIcc_of_le hAB] using hΦ
  have hXu : ContinuousOn (fun x : ℝ => (x : ℂ)) (Set.uIcc A B) :=
    Complex.continuous_ofReal.continuousOn
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := Φ) (u' := deriv Φ) (v := fun x : ℝ => (x : ℂ)) (v' := fun _ => (1 : ℂ))
    hΦu hXu
    (fun x hx => (hdΦ x (by simpa [min_eq_left hAB, max_eq_right hAB] using hx)).hasDerivAt)
    (fun x hx => (hasDerivAt_id x).ofReal_comp) hdI intervalIntegrable_const
  simp only [mul_one] at hp
  have hiTheta : IntervalIntegrable (fun x => deriv Φ x * theta χ x) volume A B := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr
    exact integrableOn_mul_sum_Icc (primeCoeff χ) hA hI
  have hiX : IntervalIntegrable
      (fun x => deriv Φ x * (principal χ * (x : ℂ))) volume A B :=
    hdI.mul_continuousOn (continuous_const.mul Complex.continuous_ofReal).continuousOn
  have hiSub : (∫ x in A..B, deriv Φ x * (theta χ x - principal χ * (x : ℂ))) =
      (∫ x in A..B, deriv Φ x * theta χ x) -
      principal χ * ∫ x in A..B, deriv Φ x * (x : ℂ) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hiTheta hiX]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [weighted_abel hA hAB χ Φ hΦ hdΦ hI, hp, hiSub]
  ring

/-- The actual weighted error follows from a uniform cumulative error on the
interval. Both endpoint contributions and the variation are retained. -/
theorem weighted_error_of_cumulative {A B M R : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (χ : DirichletCharacter ℂ q) (Φ : ℝ → ℂ)
    (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ x ∈ Set.Ioo A B, DifferentiableAt ℝ Φ x)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ x ∈ Set.Icc A B, ‖Φ x‖ ≤ M)
    (hR : ∀ x ∈ Set.Icc A B, ‖theta χ x - principal χ * (x : ℂ)‖ ≤ R) :
    ‖weighted χ A B Φ - principal χ * ∫ x in A..B, Φ x‖ ≤
      (2 * M + ∫ x in A..B, ‖deriv Φ x‖) * R := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR A ⟨le_rfl, hAB⟩)
  have hdI : IntervalIntegrable (deriv Φ) volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hI
  have hInt : ‖∫ x in A..B, deriv Φ x * (theta χ x - principal χ * (x : ℂ))‖ ≤
      (∫ x in A..B, ‖deriv Φ x‖) * R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x => deriv Φ x * (theta χ x - principal χ * (x : ℂ)))
      (g := fun x => ‖deriv Φ x‖ * R) hAB
      (Filter.Eventually.of_forall (fun x hx => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hR x ⟨hx.1.le, hx.2⟩) (norm_nonneg _)))
      (hdI.norm.mul_const R)
    simpa only [intervalIntegral.integral_mul_const] using h
  have hEnd (x : ℝ) (hx : x ∈ Set.Icc A B) :
      ‖Φ x * (theta χ x - principal χ * (x : ℂ))‖ ≤ M * R := by
    rw [norm_mul]
    exact mul_le_mul (hM x hx) (hR x hx) (norm_nonneg _) ((norm_nonneg _).trans (hM x hx))
  rw [weighted_error_identity hA hAB χ Φ hΦ hdΦ hI]
  calc
    _ ≤ ‖Φ B * (theta χ B - principal χ * (B : ℂ))‖ +
        ‖Φ A * (theta χ A - principal χ * (A : ℂ))‖ +
        ‖∫ x in A..B, deriv Φ x * (theta χ x - principal χ * (x : ℂ))‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
    _ ≤ M * R + M * R + (∫ x in A..B, ‖deriv Φ x‖) * R := by
      exact add_le_add (add_le_add (hEnd B ⟨hAB, le_rfl⟩) (hEnd A ⟨le_rfl, hAB⟩)) hInt
    _ = _ := by ring

/-- Weighted character estimate derived from (92), with an explicit envelope
which also covers the short part of the interval below two. -/
theorem weighted_error_GRH {A B M C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : 2 ≤ B) (hC : 0 ≤ C) (hGRH : GRHCharacterEstimate (q := q) C)
    (χ : DirichletCharacter ℂ q) (Φ : ℝ → ℂ)
    (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ x ∈ Set.Ioo A B, DifferentiableAt ℝ Φ x)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ x ∈ Set.Icc A B, ‖Φ x‖ ≤ M) :
    ‖weighted χ A B Φ - principal χ * ∫ x in A..B, Φ x‖ ≤
      (2 * M + ∫ x in A..B, ‖deriv Φ x‖) * envelope C B q := by
  apply weighted_error_of_cumulative hA hAB χ Φ hΦ hdΦ hI hM
  intro x hx
  exact cumulative_error_bound hC hGRH hB (hA.trans hx.1) hx.2 χ

/-- Zero extension from units to all residue classes. -/
def extend (g : (ZMod q)ˣ → ℂ) (a : ZMod q) : ℂ :=
  if h : IsUnit a then g h.unit else 0

 theorem extend_fourier (g : (ZMod q)ˣ → ℂ) (a : ZMod q) :
    extend g a = ∑ χ : DirichletCharacter ℂ q,
      FiniteCharacterFourier.coefficient g χ * χ a := by
  classical
  by_cases ha : IsUnit a
  · rw [extend, dif_pos ha]
    have h := FiniteCharacterFourier.inversion g ha.unit
    simpa only [ha.unit_spec] using h.symm
  · simp [extend, ha, MulChar.map_nonunit _ ha]

/-- Literal prime sum with the omitted nonunit primes set to zero. -/
def residueWeighted (g : (ZMod q)ˣ → ℂ) (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
    if n.Prime then Φ n * extend g (n : ZMod q) * (Real.log n : ℂ) else 0

 theorem residueWeighted_fourier (g : (ZMod q)ˣ → ℂ) (A B : ℝ) (Φ : ℝ → ℂ) :
    residueWeighted g A B Φ = ∑ χ : DirichletCharacter ℂ q,
      FiniteCharacterFourier.coefficient g χ * weighted χ A B Φ := by
  classical
  unfold residueWeighted weighted primeCoeff
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [hp, ↓reduceIte, extend_fourier, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  · simp [hp]

/-- The principal Fourier term is exactly the finite residue average. -/
theorem residueWeighted_error_identity (g : (ZMod q)ˣ → ℂ) (A B : ℝ) (Φ : ℝ → ℂ) :
    residueWeighted g A B Φ - FiniteCharacterFourier.coefficient g 1 * ∫ x in A..B, Φ x =
      ∑ χ : DirichletCharacter ℂ q, FiniteCharacterFourier.coefficient g χ *
        (weighted χ A B Φ - principal χ * ∫ x in A..B, Φ x) := by
  classical
  rw [residueWeighted_fourier]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  simp [principal]

/-- The Fourier form of (98), derived from (92) and the actual expansion.
Its principal coefficient is the literal finite average from (93). -/
theorem residueWeighted_error_GRH {A B M C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hB : 2 ≤ B) (hC : 0 ≤ C) (hGRH : GRHCharacterEstimate (q := q) C)
    (g : (ZMod q)ˣ → ℂ) (Φ : ℝ → ℂ)
    (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ x ∈ Set.Ioo A B, DifferentiableAt ℝ Φ x)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ x ∈ Set.Icc A B, ‖Φ x‖ ≤ M) :
    ‖residueWeighted g A B Φ - FiniteCharacterFourier.coefficient g 1 *
      ∫ x in A..B, Φ x‖ ≤
      (2 * M + ∫ x in A..B, ‖deriv Φ x‖) *
        FiniteCharacterFourier.beta g * envelope C B q := by
  rw [residueWeighted_error_identity]
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖FiniteCharacterFourier.coefficient g χ *
        (weighted χ A B Φ - principal χ * ∫ x in A..B, Φ x)‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ‖FiniteCharacterFourier.coefficient g χ‖ *
        ((2 * M + ∫ x in A..B, ‖deriv Φ x‖) * envelope C B q) := by
      apply Finset.sum_le_sum
      intro χ hχ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (weighted_error_GRH hA hAB hB hC hGRH χ Φ hΦ hdΦ hI hM) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold FiniteCharacterFourier.beta; ring

end DepthAspect.CharacterPrimeAverages
