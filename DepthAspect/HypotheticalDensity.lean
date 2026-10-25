import DepthAspect.HypotheticalPrimeDensity

/-!
# The hypothetical signed support range below two

The only additional premise is the precise arithmetic strengthening in
`StrengthenedPrimeAverages`. The literal zero average, specialized
explicit formula, finite initial depths, square and higher prime powers,
and actual step-subtracted main integral are handled internally.
This formalizes the conditional statement following equation (141).
-/
namespace DepthAspect.HypotheticalSignedDensity
open MeasureTheory Set SignedDensity SignedSieve UnsignedDensity SpectralFamily
open scoped BigOperators FourierTransform SchwartzMap

variable {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

theorem improved_loss_parameters {s : ℝ} (hs : 0 < s) (hs' : s < 2) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ δ < 1 / 2 ∧
      -(1 / 2 : ℝ) + s * ε ≤ 0 ∧
      -1 + s * (1 / 2 + ε) ≤ 0 ∧
      -1 + δ + s * (1 / 2 + δ) ≤ 0 ∧
      -(1 / 2 : ℝ) + δ + s * δ ≤ 0 := by
  let ε := min (1 / (4 * s)) ((2 - s) / (4 * s))
  let δ := (2 - s) / (4 * (1 + s))
  have hε : 0 < ε := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hε₁ : s * ε ≤ 1 / 4 := by
    have he := mul_le_mul_of_nonneg_left (min_le_left (1 / (4 * s)) ((2 - s) / (4 * s))) hs.le
    have hid : s * (1 / (4 * s)) = 1 / 4 := by field_simp [hs.ne']
    rwa [hid] at he
  have hε₂ : s * ε ≤ (2 - s) / 4 := by
    have he := mul_le_mul_of_nonneg_left (min_le_right (1 / (4 * s)) ((2 - s) / (4 * s))) hs.le
    have hid : s * ((2 - s) / (4 * s)) = (2 - s) / 4 := by field_simp [hs.ne']
    rwa [hid] at he
  have hδhalf : δ < 1 / 2 := by
    dsimp [δ]
    apply (div_lt_iff₀ (by positivity : 0 < 4 * (1 + s))).mpr
    linarith
  have hd : δ * (1 + s) = (2 - s) / 4 := by
    dsimp [δ]
    field_simp [show 1 + s ≠ 0 by linarith] <;> ring
  refine ⟨ε, δ, hε, hδ, hδhalf, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem signed_density_quantitative (r : ℕ)
    (improved : StrengthenedPrimeAverages)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    {s : ℝ} (hs : 0 < s) (hs' : s < 2)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
      (n : ℕ), 8 ≤ n → 2 ≤ Real.exp (s * conductorLog r n) →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
        (conductorLog r n) φ (Z.zeroOrdinate n) +
          (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2‖ ≤
        K / conductorLog r n := by
  obtain ⟨ε, δ, hε, hδ, hδhalf, he₁, he₂, hq₁, hq₂⟩ := improved_loss_parameters hs hs'
  let h : 𝓢(ℝ, ℂ) := 𝓕 φ
  obtain ⟨Kp, hKp, hp⟩ := signed_prime_inverse_log
    (Family := Family) (Full := Full) (New := New) r h improved hBessel hs.le hε he₁ he₂ hsupp
  obtain ⟨Kq, hKq, hq⟩ := signed_square_inverse_log
    (Family := Family) (Full := Full) (New := New) r h hs.le hδ hδhalf hq₁ hq₂ hsupp
  let w : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  let H : ℝ := ‖h.toBoundedContinuousFunction‖
  let Ca : ℝ := 8 / ((2 * r + 1 : ℕ) : ℝ) *
    (‖h 0‖ + archimedeanConstant (r + 1) φ)
  let Ka : ℝ := Ca * (Real.log (w ^ 2) + 2)
  have hw : 2 ≤ w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) r; push_cast; linarith
  have hCa : 0 ≤ Ca := by
    have hconst := archimedeanConstant_nonneg (r + 1) (by omega) φ
    dsimp [Ca]
    positivity
  have hKa : 0 ≤ Ka := by
    have := Real.log_nonneg (show 1 ≤ w ^ 2 by nlinarith)
    dsimp [Ka]
    positivity
  refine ⟨Ka + Kp + Kq + 192 * H, by positivity, ?_⟩
  intro S Z n hn hcut
  letI : Nonempty (Family (2 ^ n)) := MartinDimension.family_nonempty Family
    (2 * r + 2) n (by omega) hn S.unsigned.dimension_formula
  have hL := conductorLog_pos r n
  have hN := UnsignedExponents.dyadic_level_gt_one n hn
  have hR := negative_power_le_inverse_conductor_log hN
    (show 1 ≤ w ^ 2 by nlinarith) (by norm_num : -(1 / 2 : ℝ) < 0)
  norm_num only [neg_neg, one_div_div, one_div_one] at hR
  have hArch : ‖average (fun f => (S.rootNumber (2 ^ n) f : ℂ)) *
      ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) w (r + 1) φ (h 0)‖ ≤ Ka / conductorLog r n := by
    have hb := signed_archimedean_bound S hDLMF n hn φ
    exact hb.trans ((mul_le_mul_of_nonneg_left hR hCa).trans_eq (by dsimp [Ka, conductorLog, w]; ring))
  have hPrime := hp S n hn hcut
  have hSquare := hq S n hn
  have hsign : ∀ f : Family (2 ^ n), ‖(S.rootNumber (2 ^ n) f : ℂ)‖ ≤ 1 := by
    intro f
    rcases S.rootNumber_sign (2 ^ n) f with he | he <;> simp [he]
  have hfirst : ∀ p ∈ primeBases (conductorLog r n) s, ∀ f,
      Z.alpha n f p + Z.beta n f p = S.unsigned.eigenvalues (2 ^ n) f p := by
    intro p hp f
    have hc := (Finset.mem_filter.mp hp).2
    exact Z.first_coefficient n (by omega) f p hc.1 hc.2
  have hprod : ∀ p ∈ primeBases (conductorLog r n) s, ∀ f,
      Z.alpha n f p * Z.beta n f p = 1 := by
    intro p hp f
    have hc := (Finset.mem_filter.mp hp).2
    exact Z.product n (by omega) f p hc.1 hc.2
  have hsquare : ∀ p ∈ primeBases (conductorLog r n) s, ∀ f,
      tracePolynomial (Z.alpha n f p + Z.beta n f p) 1 2 =
        S.unsigned.eigenvalues (2 ^ n) f (p ^ 2) := by
    intro p hp f
    have hc := (Finset.mem_filter.mp hp).2
    exact Z.square_coefficient n (by omega) f p hc.1 hc.2
  have hα : ∀ p ∈ primeBases (conductorLog r n) s, ∀ f, ‖Z.alpha n f p‖ = 1 := by
    intro p hp f
    have hc := (Finset.mem_filter.mp hp).2
    exact Z.alpha_norm n (by omega) f p hc.1 hc.2
  have hβ : ∀ p ∈ primeBases (conductorLog r n) s, ∀ f, ‖Z.beta n f p‖ = 1 := by
    intro p hp f
    have hc := (Finset.mem_filter.mp hp).2
    exact Z.beta_norm n (by omega) f p hc.1 hc.2
  have h56 := Z.explicit_formula hDLMF n (by omega) hs.le φ heven hsupp
  have hbound := signed_density_error_of_terms hL (norm_nonneg _)
    (fun f => (S.rootNumber (2 ^ n) f : ℂ)) hsign φ hsupp (Z.zeroOrdinate n)
    (Z.alpha n) (Z.beta n) (S.unsigned.eigenvalues (2 ^ n))
    (ArchimedeanBound.archimedeanTerm ((2 : ℝ) ^ n) w (r + 1) φ (h 0))
    (∫ u in Ioi (1 : ℝ), h u) hfirst hprod hsquare hα hβ
    (fun x => h.toBoundedContinuousFunction.norm_coe_le_norm x)
    hArch hPrime hSquare h56
  rw [even_outside_integral h (EntireExtension.schwartz_fourier_even φ heven)] at hbound
  exact hbound.trans_eq (by ring)

/-- The quantitative conclusion is uniform in all spectral and zero data,
including the finite initial depths and arbitrarily small support radius. -/
theorem signed_density_uniform (r : ℕ)
    (improved : StrengthenedPrimeAverages)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    {s : ℝ} (hs : 0 < s) (hs' : s < 2)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
      (n : ℕ), 7 ≤ n →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
        (conductorLog r n) φ (Z.zeroOrdinate n) +
          (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2‖ ≤
        K / conductorLog r n := by
  obtain ⟨K, hK, hb⟩ := signed_density_quantitative
    (Family := Family) (Full := Full) (New := New) r improved hDLMF hBessel hs hs' φ heven hsupp
  have hw : (0 : ℝ) < 2 * ((r + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨n₀, hn₀⟩ := support_endpoint_eventually_large hw hs
  let J : ℂ := (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2
  let C := K + ∑ j ∈ Finset.range (max 8 n₀),
    max 0 (conductorLog r j) * (initialEnvelope r s φ j + ‖J‖)
  have hC : 0 ≤ C := add_nonneg hK (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (le_max_left _ _) (add_nonneg (initialEnvelope_nonneg r s φ j) (norm_nonneg _))))
  refine ⟨C, hC, ?_⟩
  intro S Z n hn
  have he := signed_density_finite_prefix S Z hDLMF hs.le φ heven hsupp
    J (max 8 n₀) K hK (fun m hm hcut =>
      hb S Z m ((le_max_left _ _).trans hcut) (hn₀ m ((le_max_right _ _).trans hcut)))
  exact he.2 n hn

theorem conditional_signed_density_support_two {r : ℕ}
    (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
    (improved : StrengthenedPrimeAverages)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Ioo (-(2 : ℝ)) (2)) :
    ∃ K ≥ 0, ∀ n : ℕ, 7 ≤ n →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (2)
        (conductorLog r n) φ (Z.zeroOrdinate n) +
          (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2‖ ≤
        K / conductorLog r n := by
  obtain ⟨s, hs, hsb, hsupport⟩ := SupportEndpoint.support_endpoint_of_tsupport_subset
    (𝓕 φ : 𝓢(ℝ, ℂ)) (by norm_num : (0 : ℝ) < 2) hsupp
  obtain ⟨K, hK, hb⟩ := signed_density_uniform
    (Family := Family) (Full := Full) (New := New) r improved hDLMF hBessel hs hsb φ heven hsupport
  refine ⟨K, hK, ?_⟩
  intro n hn
  have hbig : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-(2 : ℝ)) (2) :=
    subset_closure.trans (hsupp.trans Set.Ioo_subset_Icc_self)
  rw [← signedMeanDensity_support_independent _ φ hs.le (by norm_num : (0 : ℝ) ≤ 2)
    hsupport hbig]
  exact hb S Z n hn

theorem conditional_signed_density_limit {r : ℕ}
    (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
    (improved : StrengthenedPrimeAverages)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Ioo (-(2 : ℝ)) (2)) :
    Filter.Tendsto (fun n : ℕ => signedMeanDensity
      (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (2)
      (conductorLog r n) φ (Z.zeroOrdinate n)) Filter.atTop
      (nhds (-(∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2)) := by
  obtain ⟨K, _, hb⟩ := conditional_signed_density_support_two S Z improved hDLMF hBessel φ heven hsupp
  have hlevel : Filter.Tendsto (fun n : ℕ =>
      (2 * ((r + 1 : ℕ) : ℝ)) ^ 2 * (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hlog := Real.tendsto_log_atTop.comp hlevel
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (by
      filter_upwards [Filter.eventually_ge_atTop (7 : ℕ)] with n hn
      simpa only [neg_div, sub_neg_eq_add] using hb n hn)
  exact hlog.const_div_atTop K

end DepthAspect.HypotheticalSignedDensity
