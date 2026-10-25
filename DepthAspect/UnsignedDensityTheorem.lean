import DepthAspect.UniformSpectralPrimeBounds
import DepthAspect.UnsignedAnalyticReduction
import DepthAspect.UnsignedConstantBounds
import DepthAspect.SupportEndpoint

/-!
# The unsigned density theorem from general cited inputs

ArithmeticSpectralData carries the general arithmetic identities. The
analytic data below carry the unit Satake roots, their Hecke coefficients,
and the general local-integral explicit formula. Internal equations
(35), (40), (45)--(50), (52), (56), and (59)--(64) are not assumptions.
-/
namespace DepthAspect.UnsignedDensity

open SpectralFamily TraceBounds PrimePowerApplications UnsignedExponents
open scoped BigOperators FourierTransform SchwartzMap

structure AnalyticSpectralData {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) where
  weight_relation : k + 2 = 2 * a
  zeroIndex : ∀ n, Family (2 ^ n) → Type
  zeroOrdinate : ∀ n f, zeroIndex n f → ℂ
  alpha : ∀ n, Family (2 ^ n) → ℕ → ℂ
  beta : ∀ n, Family (2 ^ n) → ℕ → ℂ
  alpha_norm : ∀ n, 8 ≤ n → ∀ f p, p.Prime → p ≠ 2 → ‖alpha n f p‖ = 1
  beta_norm : ∀ n, 8 ≤ n → ∀ f p, p.Prime → p ≠ 2 → ‖beta n f p‖ = 1
  first_coefficient : ∀ n, 8 ≤ n → ∀ f p, p.Prime → p ≠ 2 →
    alpha n f p + beta n f p = D.eigenvalues (2 ^ n) f p
  product : ∀ n, 8 ≤ n → ∀ f p, p.Prime → p ≠ 2 → alpha n f p * beta n f p = 1
  general_explicit_formula : ∀ n, 8 ≤ n → ∀ f,
    ExplicitFormula.ShinTemplierFormula ((2 : ℝ) ^ n) (zeroOrdinate n f)
      (GammaLocal.gammaFactor (2 * (a : ℝ)))
      (ExplicitFormula.finiteEulerFactor (alpha n f) (beta n f))

/-- The square coefficient needed in (55) follows internally from the cited
general Hecke recurrence and the first Satake coefficient. -/
theorem AnalyticSpectralData.square_coefficient {k a : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    {D : ArithmeticSpectralData k Family V} (Z : AnalyticSpectralData D a)
    (n : ℕ) (hn : 8 ≤ n) (f : Family (2 ^ n)) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    tracePolynomial (Z.alpha n f p + Z.beta n f p) 1 2 =
      D.eigenvalues (2 ^ n) f (p ^ 2) := by
  rw [Z.first_coefficient n hn f p hp hp2]
  exact D.square_coefficient (2 ^ n) f p hp ((hp.odd_of_ne_two hp2).coprime_two_right.pow_right n)

noncomputable def primeConstant (s δ : ℝ) : ℝ :=
  96 * s * uniformEllipticConstant δ * Real.sqrt 2 / (1 - (2 : ℝ) ^ (-1 - δ))

noncomputable def cuspSumConstant (k : ℕ) (s H : ℝ) : ℝ :=
  2 * (576 / ((k : ℝ) + 1)) * H * Real.log 4 * ((1 + s) + (1 + s / 2))

/-- This constant depends only on the fixed test, weight, support endpoint,
small exponent, and the constant in the cited Mertens theorem. -/
noncomputable def fiveTermConstant (k a : ℕ) (s δ C : ℝ) (φ : 𝓢(ℝ, ℂ)) : ℝ :=
  let H := ‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖
  (analyticConstant a φ C + 8 * H * Real.log 4) + cuspSumConstant k s H +
    primeConstant s δ * H + squareConstant (uniformEllipticConstant δ) δ * H

theorem primeConstant_nonneg {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) :
    0 ≤ primeConstant s δ := by
  have hq : (2 : ℝ) ^ (-1 - δ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK := (uniformEllipticConstant_pos hδ).le
  unfold primeConstant
  positivity

theorem analyticConstant_nonneg (a : ℕ) (ha : 1 ≤ a) (φ : 𝓢(ℝ, ℂ))
    {C : ℝ} (hC : 0 ≤ C) : 0 ≤ analyticConstant a φ C := by
  have hA := archimedeanConstant_nonneg a ha φ
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hI : 0 ≤ ∫ u : ℝ, ‖deriv (𝓕 φ : 𝓢(ℝ, ℂ)) u‖ :=
    MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  unfold analyticConstant
  positivity

theorem fiveTermConstant_nonneg (k a : ℕ) (ha : 1 ≤ a) (φ : 𝓢(ℝ, ℂ))
    {s δ C : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) (hC : 0 ≤ C) :
    0 ≤ fiveTermConstant k a s δ C φ := by
  have hA := analyticConstant_nonneg a ha φ hC
  have hP := primeConstant_nonneg hs hδ
  have hK := (uniformEllipticConstant_pos hδ).le
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold fiveTermConstant cuspSumConstant squareConstant
  positivity

/-- Equation (62) for the literal finite average of the literal zero sums.
All internal arithmetic and analytic estimates have been composed here. -/
theorem unsigned_five_term {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) (ha : 1 ≤ a)
    (Z : AnalyticSpectralData D a) (hDLMF : DigammaBound.DLMFSeriesIdentity)
    (n : ℕ) (hn : 8 ≤ n) {s δ C : ℝ}
    (hs : 0 ≤ s) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) :
    let N := (2 : ℝ) ^ n
    let L := Real.log ((2 * (a : ℝ)) ^ 2 * N)
    ‖meanDensity s L φ (Z.zeroOrdinate n) -
      ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤
      fiveTermConstant k a s δ C φ *
        (1 / L + N ^ (-(1 / 2 : ℝ)) +
          N ^ (-(3 / 2 : ℝ)) * ((2 * (a : ℝ)) ^ 2 * N) ^ (s * (1 + δ)) +
          (1 / L) * (N ^ (-(3 / 2 : ℝ)) *
            ((2 * (a : ℝ)) ^ 2 * N) ^ (s * (1 / 2 + δ))) +
          (1 / L) * (N ^ (-(1 / 2 : ℝ)) *
            ((2 * (a : ℝ)) ^ 2 * N) ^ (s * δ))) := by
  letI : Nonempty (Family (2 ^ n)) :=
    MartinDimension.family_nonempty Family (k + 2) n (by omega) hn D.dimension_formula
  let N := (2 : ℝ) ^ n
  let L := Real.log ((2 * (a : ℝ)) ^ 2 * N)
  let H := ‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hweight : 2 ≤ 2 * (a : ℝ) := by linarith
  have hL : 1 ≤ L := conductor_log_ge_one (2 * (a : ℝ)) hweight n hn
  have hL0 : 0 < L := by linarith
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hh (x : ℝ) : ‖(𝓕 φ : 𝓢(ℝ, ℂ)) x‖ ≤ H :=
    (𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction.norm_coe_le_norm x
  have hp := D.prime_sum n hn hL hs hδ (norm_nonneg _) _ hh
  have hq := D.square_sum n hn hL hs hδ hδhalf (norm_nonneg _) _ hsupp hh
  have hb := density_error_from_general_explicit_formula hDLMF N hN a ha hs hC hL hM
    φ heven hsupp (Z.zeroOrdinate n) (Z.alpha n) (Z.beta n)
    (D.eigenvalues (2 ^ n)) (Z.alpha_norm n hn) (Z.beta_norm n hn) (Z.first_coefficient n hn)
    (Z.product n hn) (Z.square_coefficient n hn)
    (Z.general_explicit_formula n hn)
    hp hq
  let A := analyticConstant a φ C + 8 * H * Real.log 4
  let B := cuspSumConstant k s H
  let P := primeConstant s δ * H
  let Q := squareConstant (uniformEllipticConstant δ) δ * H
  have hA : 0 ≤ A := by
    have := analyticConstant_nonneg a ha φ hC
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [A, H]
    positivity
  have hB : 0 ≤ B := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [B, cuspSumConstant, H]
    positivity
  have hP : 0 ≤ P := mul_nonneg (primeConstant_nonneg hs hδ) (norm_nonneg _)
  have hQ : 0 ≤ Q := by
    have := (uniformEllipticConstant_pos hδ).le
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp [Q, squareConstant, H]
    positivity
  have he : ‖meanDensity s L φ (Z.zeroOrdinate n) -
      ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤
      A / L + B * N ^ (-(1 / 2 : ℝ)) +
      P * N ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 + δ) +
      Q / L * (N ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 / 2 + δ) +
        N ^ (-(1 / 2 : ℝ)) * (Real.exp (s * L)) ^ δ) := by
    convert hb using 1 <;> dsimp [A, B, P, Q, cuspSumConstant, primeConstant, H, L, N] <;> ring
  have ht := weighted_error_to_five_terms (by linarith : 0 < 2 * (a : ℝ))
    (by positivity : 0 < N) hL0 hA hB hP hQ rfl he
  simpa only [A, B, P, Q, H, fiveTermConstant, L, N] using ht

noncomputable def threeTermConstant (k a : ℕ) (s η C : ℝ) (φ : 𝓢(ℝ, ℂ)) : ℝ :=
  let δ := η / (2 * (1 + s))
  fiveTermConstant k a s δ C φ *
    (2 + ((2 * (a : ℝ)) ^ 2) ^ (s * (1 + δ)) +
      ((2 * (a : ℝ)) ^ 2) ^ (s * (1 / 2 + δ)) + ((2 * (a : ℝ)) ^ 2) ^ (s * δ))

theorem threeTermConstant_nonneg (k a : ℕ) (ha : 1 ≤ a) (φ : 𝓢(ℝ, ℂ))
    {s η C : ℝ} (hs : 0 < s) (hη : 0 < η) (hC : 0 ≤ C) :
    0 ≤ threeTermConstant k a s η C φ := by
  have hδ : 0 < η / (2 * (1 + s)) := by positivity
  have hF := fiveTermConstant_nonneg k a ha φ hs.le hδ hC
  unfold threeTermConstant
  positivity

/-- Equation (42), for every depth in the stated range and the actual
finite zero average. The constant is displayed independently of n. -/
theorem unsigned_density_quantitative {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) (ha : 1 ≤ a)
    (Z : AnalyticSpectralData D a) (hDLMF : DigammaBound.DLMFSeriesIdentity)
    (n : ℕ) (hn : 8 ≤ n) {s η C : ℝ}
    (hs : 0 < s) (hs' : s < 3 / 2) (hη : 0 < η) (hηhalf : η < 1 / 2) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) :
    let N := (2 : ℝ) ^ n
    let L := Real.log ((2 * (a : ℝ)) ^ 2 * N)
    ‖meanDensity s L φ (Z.zeroOrdinate n) -
      ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤
      threeTermConstant k a s η C φ *
        (1 / L + N ^ (s - 3 / 2 + η) + N ^ (-(1 / 2 : ℝ) + η)) := by
  let δ := η / (2 * (1 + s))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ < 1 / 2 := (unsigned_parameter_choice hs hs' hη hηhalf).2.1
  have he := unsigned_five_term D a ha Z hDLMF n hn hs.le hδ hδhalf hC hM φ heven hsupp
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hN : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hL := conductor_log_ge_one (2 * (a : ℝ)) (by linarith) n hn
  have ht := five_term_to_three_term (by linarith : 0 < 2 * (a : ℝ)) hN hL
    hs hs' hη hηhalf (fiveTermConstant_nonneg k a ha φ hs.le hδ hC) he
  simpa only [threeTermConstant, δ] using ht

/-- Theorem 4.1's uniform error (41). The constant is independent of depth;
there is no assumed internal trace, Mertens-weighting, or explicit-formula
specialization in the hypotheses. -/
theorem unsigned_density_uniform {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) (ha : 1 ≤ a)
    (Z : AnalyticSpectralData D a) (hDLMF : DigammaBound.DLMFSeriesIdentity)
    {s C : ℝ} (hs : 0 < s) (hs' : s < 3 / 2) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 8 ≤ n →
      ‖meanDensity s (Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n)) φ
        (Z.zeroOrdinate n) - ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤
        K / Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n) := by
  obtain ⟨η, hη, hηmax⟩ := unsigned_parameter_exists hs'
  have hηhalf := hηmax.trans_le (min_le_left _ _)
  let K₃ := threeTermConstant k a s η C φ
  let K := K₃ * (1 + 2 * Real.log ((2 * (a : ℝ)) ^ 2) +
    1 / (-(s - 3 / 2 + η)) + 1 / (-(-(1 / 2 : ℝ) + η)))
  refine ⟨|K|, abs_nonneg K, ?_⟩
  intro n hn
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hk : 1 ≤ (2 * (a : ℝ)) ^ 2 := by nlinarith
  have he := unsigned_density_quantitative D a ha Z hDLMF n hn hs hs' hη hηhalf
    hC hM φ heven hsupp
  have ht := three_term_to_inverse_log hk (dyadic_level_gt_one n hn)
    (threeTermConstant_nonneg k a ha φ hs hη hC) hηmax he
  have hL : 0 < Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n) := by
    have := conductor_log_ge_one (2 * (a : ℝ)) (by linarith) n hn
    linarith
  exact ht.trans (div_le_div_of_nonneg_right (le_abs_self K) hL.le)

/-- The actual finite zero average is independent of the valid auxiliary
support endpoint used to construct its entire test function. -/
theorem meanDensity_support_independent {ι : Type*} [Fintype ι] {κ : ι → Type*}
    (φ : 𝓢(ℝ, ℂ)) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hss : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (hts : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-t) t)
    (L : ℝ) (γ : ∀ f, κ f → ℂ) : meanDensity s L φ γ = meanDensity t L φ γ := by
  unfold meanDensity
  congr 1
  funext f
  exact ExplicitFormula.density_support_independent φ hs ht hss hts L (γ f)

/-- Theorem 1.1's unsigned conclusion for its stated closed Fourier support.
No separate compactness premise is added, and the final density uses the
fixed support endpoint 3/2 rather than a choice depending on the proof. -/
theorem unsigned_density_theorem_1_1 {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (a : ℕ) (ha : 1 ≤ a)
    (Z : AnalyticSpectralData D a) (hDLMF : DigammaBound.DLMFSeriesIdentity)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Ioo (-(3 / 2 : ℝ)) (3 / 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 8 ≤ n →
      ‖meanDensity (3 / 2) (Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n)) φ
        (Z.zeroOrdinate n) - ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤
        K / Real.log ((2 * (a : ℝ)) ^ 2 * (2 : ℝ) ^ n) := by
  obtain ⟨s, hs0, hsb, hs⟩ := SupportEndpoint.support_endpoint_of_tsupport_subset
    (𝓕 φ : 𝓢(ℝ, ℂ)) (by norm_num : (0 : ℝ) < 3 / 2) hsupp
  obtain ⟨K, hK0, hK⟩ := unsigned_density_uniform D a ha Z hDLMF hs0 hsb hC hM φ heven hs
  refine ⟨K, hK0, ?_⟩
  intro n hn
  have hbig : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-(3 / 2 : ℝ)) (3 / 2) :=
    subset_closure.trans (hsupp.trans Set.Ioo_subset_Icc_self)
  rw [← meanDensity_support_independent φ hs0.le (by norm_num : (0 : ℝ) ≤ 3 / 2)
    hs hbig]
  exact hK n hn

end DepthAspect.UnsignedDensity
