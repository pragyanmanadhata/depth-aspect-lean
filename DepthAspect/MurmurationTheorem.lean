import DepthAspect.MurmurationMean
import DepthAspect.MurmurationOscillation
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Theorem 6.1, assembled for every even weight k=2a+2 and every prime ℓ.
Its only analytic background parameter is the cited general Bessel identities. -/
open Filter MeasureTheory
open scoped BigOperators Topology
namespace DepthAspect.MurmurationTheorem
open ArithmeticWeights BesselFirstKind MurmurationArithmetic MurmurationMean MurmurationOscillationSeries
  MurmurationBohrCoefficient MurmurationExpansion MurmurationOscillation OscillatoryMean
open MurmurationBesselSeries MurmurationDivisorExpansion MurmurationPointwiseBounds
  MurmurationIntegralSeries MurmurationIntegralLimit MurmurationIntegralError MurmurationIntegralSmall

theorem zetaThreeHalves_eq :
    (zetaThreeHalves : ℂ) = riemannZeta (3 / 2) := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by norm_num : 1 < (3 / 2 : ℂ).re)]
  rw [← tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ => 1 / (n : ℂ) ^ (3 / 2 : ℂ))
    (by rw [Nat.cast_zero, Complex.zero_cpow (by norm_num), div_zero])]
  unfold zetaThreeHalves
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro ν
  have hv : (0 : ℝ) ≤ ν := by positivity
  rw [Real.rpow_neg hv, Complex.ofReal_inv, Complex.ofReal_cpow hv]
  push_cast
  simp only [one_div]

/-- The magnitude q has the exact normalization printed in (134). -/
theorem q_normalization {ℓ : ℕ} (hℓ : ℓ.Prime) :
    q ℓ = B ℓ * S ℓ / (Real.sqrt 2 * (1 - (ℓ : ℝ)⁻¹)) := by
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hz : 1 - (ℓ : ℝ)⁻¹ ≠ 0 := by linarith [inv_lt_one_of_one_lt₀ hl]
  have hs : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  unfold q K
  generalize hden : 1 - (ℓ : ℝ)⁻¹ = z at hz ⊢
  calc
    _ = (Real.sqrt 2 * B ℓ / z * S ℓ) /
        (Real.sqrt 2 * Real.sqrt 2) := by rw [hs]
    _ = _ := by field_simp [hz, ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))] <;> ring

theorem coefficient_literal {ℓ : ℕ} (hℓ : ℓ.Prime) (a : ℕ) :
    (q ℓ : ℂ) * wave (-(phase a)) 1 =
      ((B ℓ : ℂ) * Complex.exp (-(phase a : ℂ) * Complex.I) /
        ((Real.sqrt 2 : ℂ) * (1 - (ℓ : ℂ)⁻¹))) * (S ℓ : ℂ) := by
  rw [q_normalization hℓ]
  unfold wave
  push_cast
  simp only [mul_one]
  ring

theorem coefficient_nonzero {ℓ : ℕ} (hℓ : ℓ.Prime) (a : ℕ) :
    (q ℓ : ℂ) * wave (-(phase a)) 1 ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (q_pos hℓ))) (Complex.exp_ne_zero _)

/-- Equation (134), with the printed complex normalization as the actual
limiting Fourier coefficient of (131). -/
theorem coefficient_limit_literal {ℓ : ℕ} (hℓ : ℓ.Prime) (a : ℕ) :
    Tendsto (average (fun x => (A a ℓ x : ℂ) * wave (-(4 * Real.pi)) x))
      atTop (𝓝 (((B ℓ : ℂ) * Complex.exp (-(phase a : ℂ) * Complex.I) /
        ((Real.sqrt 2 : ℂ) * (1 - (ℓ : ℂ)⁻¹))) * (S ℓ : ℂ))) := by
  rw [← coefficient_literal hℓ a]
  exact A_coefficient a hℓ

/-- Lemma 6.4 for the literal g and M, including absolute convergence of
the arithmetic divisor expansion and a single constant for both regimes. -/
theorem lemma_6_4 (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (∀ y : ℝ, 0 < y →
      g a ℓ y = (2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹)) *
        ∑' ν : ℕ+, (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
          J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν))) ∧
    (∀ y : ℝ, 0 < y →
      Summable (fun d : ℕ => c ℓ d * g a ℓ (y / (d : ℝ) ^ 2)) ∧
      M a ℓ y = B ℓ * ∑' d : ℕ, c ℓ d * g a ℓ (y / (d : ℝ) ^ 2)) ∧
    (∃ C > 0,
      (∀ y : ℝ, 1 ≤ y → |g a ℓ y| ≤ C * y ^ (1 / 4 : ℝ)) ∧
      (∀ y : ℝ, 0 < y → y ≤ 1 → |g a ℓ y| ≤ C * Real.sqrt y)) := by
  refine ⟨fun y hy => g_eq_bessel hDLMF a hℓ.two_le hy,
    fun y hy => M_divisor_sum a hℓ hy, ?_⟩
  obtain ⟨Cs, hCs, hs⟩ := g_small_bound a hℓ.two_le
  obtain ⟨Cq, hCq, hq⟩ := g_quarter_bound hDLMF a hℓ.two_le
  refine ⟨Cs + Cq, by positivity, ?_, ?_⟩
  · intro y hy
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    exact (hq y hy0).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hCs.le) (Real.rpow_nonneg hy0.le _))
  · intro y hy hy1
    exact (hs y hy hy1).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hCq.le) (Real.sqrt_nonneg y))

/-- Lemma 6.5 as an assertion about the actual integral G, with the exact
zeta normalization, its limit, and one constant for the two error bounds. -/
theorem lemma_6_5 (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (∀ Z : ℝ, 0 ≤ Z →
      G a ℓ Z = (1 / (1 - (ℓ : ℝ)⁻¹)) * ∑' ν : ℕ+, ((ν : ℝ) ^ 2)⁻¹ *
        (I a (4 * Real.pi * ν * Real.sqrt Z) -
          ((ℓ : ℝ) ^ 2)⁻¹ * I a (4 * Real.pi * ℓ * ν * Real.sqrt Z))) ∧
    ((limitValue ℓ : ℂ) = (1 + (ℓ : ℂ)⁻¹) * riemannZeta 2) ∧
    Tendsto (G a ℓ) atTop (𝓝 (limitValue ℓ)) ∧
    (∃ C > 0,
      (∀ Z : ℝ, 1 ≤ Z → |G a ℓ Z - limitValue ℓ| ≤ C * Z ^ (-(1 / 4 : ℝ))) ∧
      (∀ Z : ℝ, 0 < Z → Z ≤ 1 → |G a ℓ Z| ≤ C * Real.sqrt Z)) := by
  refine ⟨fun Z hZ => G_eq_series hDLMF a hℓ.two_le hZ,
    limitValue_eq_zeta ℓ, G_tendsto hDLMF a hℓ.two_le, ?_⟩
  obtain ⟨Cs, hCs, hs⟩ := G_small_bound hDLMF a hℓ.two_le
  obtain ⟨Ce, hCe, he⟩ := G_large_error hDLMF a hℓ.two_le
  refine ⟨Cs + Ce, by positivity, ?_, ?_⟩
  · intro Z hZ
    exact (he Z hZ).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hCs.le) (Real.rpow_nonneg (zero_le_one.trans hZ) _))
  · intro Z hZ hZ1
    exact (hs Z hZ hZ1).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hCe.le) (Real.sqrt_nonneg Z))

/-- The three assertions displayed together in (120), for the literal
arithmetic density and literal trigonometric series. -/
theorem theorem_6_1 (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (∀ y : ℝ, 0 < y → y ≤ 1 / (4 * (ℓ : ℝ) ^ 2) →
      M a ℓ y = (2 * Real.pi / ((2 * a + 1 : ℕ) : ℝ)) * Real.sqrt y) ∧
    (∃ C > 0, ∀ Y : ℝ, 1 ≤ Y →
      |(∫ y : ℝ in (1)..Y, M a ℓ y / y) - (1 / 2 : ℝ) * Real.log Y| ≤ C) ∧
    (∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |(M a ℓ y - 1 / 2) - y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y)| ≤ C) ∧
    (∀ L : ℝ, ¬ Tendsto (M a ℓ) atTop (𝓝 L)) := by
  exact ⟨fun y hy hys => M_small a hℓ hy hys,
    M_logarithmic_mean hDLMF a hℓ, M_oscillatory_expansion hDLMF a hℓ,
    M_no_limit hDLMF a hℓ⟩


/-- The regularity and unboundedness assertions accompanying (120). These
are included explicitly alongside the three displayed formulas: absolute
uniform convergence of (131), bounded continuity of its sum, and the
quantitative sequences (135) tending in both signs to infinity. -/
theorem theorem_6_1_shape (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (∀ x : ℝ, Summable (fun i : ℕ+ × ℕ+ => ‖oscillationTerm a ℓ i x‖)) ∧
    TendstoUniformly
      (fun s : Finset (ℕ+ × ℕ+) => fun x => ∑ i ∈ s, ‖oscillationTerm a ℓ i x‖)
      (fun x => ∑' i : ℕ+ × ℕ+, ‖oscillationTerm a ℓ i x‖) atTop ∧
    TendstoUniformly (fun s : Finset (ℕ+ × ℕ+) => fun x => ∑ i ∈ s, oscillationTerm a ℓ i x)
      (A a ℓ) atTop ∧
    Continuous (A a ℓ) ∧
    (∀ x : ℝ, |A a ℓ x| ≤ Q ℓ) ∧
    (∃ C > 0, ∀ y : ℝ, 1 ≤ y → |M a ℓ y| ≤ C * y ^ (1 / 4 : ℝ)) ∧
    0 < oscillationConstant ℓ ∧
    (∃ yPos yNeg : ℕ → ℝ,
      Tendsto yPos atTop atTop ∧ Tendsto yNeg atTop atTop ∧
      (∀ j, 1 ≤ yPos j ∧ oscillationConstant ℓ * (yPos j) ^ (1 / 4 : ℝ) ≤ M a ℓ (yPos j)) ∧
      (∀ j, 1 ≤ yNeg j ∧ M a ℓ (yNeg j) ≤ -oscillationConstant ℓ * (yNeg j) ^ (1 / 4 : ℝ))) ∧
    (∃ yPos yNeg : ℕ → ℝ,
      Tendsto yPos atTop atTop ∧ Tendsto yNeg atTop atTop ∧
      Tendsto (fun j => M a ℓ (yPos j)) atTop atTop ∧
      Tendsto (fun j => M a ℓ (yNeg j)) atTop atBot) := by
  exact ⟨A_absolute a hℓ, A_absolute_uniform a hℓ, A_uniform a hℓ, A_continuous a hℓ,
    A_bounded a hℓ, M_quarter_bound hDLMF a hℓ, oscillationConstant_pos hℓ,
    oscillating_sequences hDLMF a hℓ, unbounded_both_signs hDLMF a hℓ⟩

end DepthAspect.MurmurationTheorem
