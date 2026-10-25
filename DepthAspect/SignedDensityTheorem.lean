import DepthAspect.SignedDensityRates
import DepthAspect.SignedArchimedean
import DepthAspect.SignedInitialBound
import DepthAspect.SupportEndpoint
import DepthAspect.RandomMatrixMainTerms

/-!
# Theorem 5.8 and Theorem 1.2 for the actual signed zero average

The final theorem retains actual primitive Dirichlet RH and the cited
uniform implications of that hypothesis. Internal prime averages, trace
bounds, variation, bounded primitives, sign balance and the specialized
explicit formula are derived. The finite initial-depth constant uses a
universal Satake envelope, independently of auxiliary spectral data.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set SpectralFamily SignedSieve UnsignedDensity
open DirichletRH GRHConsequences
open scoped BigOperators FourierTransform SchwartzMap

/-- An even integrable test has equal tails on the two components of the
complement of [-1,1]. This is the literal main term in (118). -/
theorem even_outside_integral (h : 𝓢(ℝ, ℂ)) (heven : Function.Even h) :
    (∫ u in Ioi (1 : ℝ), h u) = (∫ u in (Icc (-1) 1)ᶜ, h u) / 2 := by
  have hset : (Icc (-1 : ℝ) 1)ᶜ = Iio (-1) ∪ Ioi 1 := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
    constructor
    · intro hx
      by_cases hlo : x < -1
      · exact Or.inl hlo
      · exact Or.inr (lt_of_not_ge (fun hhi => hx ⟨le_of_not_gt hlo, hhi⟩))
    · rintro (hx | hx) hmem <;> linarith [hmem.1, hmem.2]
  have hd : Disjoint (Iio (-1 : ℝ)) (Ioi 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hx'
    simp only [mem_Iio, mem_Ioi] at hx hx'
    linarith
  have hleft : (∫ u in Iio (-1 : ℝ), h u) = ∫ u in Ioi (1 : ℝ), h u := by
    rw [← integral_Iic_eq_integral_Iio]
    calc
      _ = ∫ u in Iic (-1 : ℝ), h (-u) :=
        setIntegral_congr_fun measurableSet_Iic (fun u _ => (heven u).symm)
      _ = _ := by simpa using integral_comp_neg_Iic (-1) h
  rw [hset, setIntegral_union hd measurableSet_Ioi h.integrable.integrableOn h.integrable.integrableOn,
    hleft]
  ring

variable {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- The combined signed-density estimate, followed by the strict support savings,
on the dyadic-block range. Its constant is uniform in the spectral data. -/
theorem signed_density_quantitative (r : ℕ)
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    {s : ℝ} (hs : 0 < s) (hs' : s < 4 / 3)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
      (n : ℕ), 8 ≤ n → 2 ≤ Real.exp (s * conductorLog r n) →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
        (conductorLog r n) φ (Z.zeroOrdinate n) +
          (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2‖ ≤
        K / conductorLog r n := by
  obtain ⟨ε, δ, hε, hδ, hδhalf, he₁, he₂, hq₁, hq₂⟩ := signed_loss_parameters hs hs'
  let h : 𝓢(ℝ, ℂ) := 𝓕 φ
  obtain ⟨Kp, hKp, hp⟩ := signed_prime_inverse_log
    (Family := Family) (Full := Full) (New := New) r h hRH cited hBessel hs.le hε he₁ he₂ hsupp
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
    exact hb.trans ((mul_le_mul_of_nonneg_left hR hCa).trans_eq
      (by dsimp [Ka, conductorLog, w]; ring))
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
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    {s : ℝ} (hs : 0 < s) (hs' : s < 4 / 3)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
      (n : ℕ), 7 ≤ n →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
        (conductorLog r n) φ (Z.zeroOrdinate n) +
          (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2‖ ≤
        K / conductorLog r n := by
  obtain ⟨K, hK, hb⟩ := signed_density_quantitative
    (Family := Family) (Full := Full) (New := New) r hRH cited hDLMF hBessel hs hs' φ heven hsupp
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

/-- Theorem 5.8, literally displayed as (118). The already proved stronger
inverse-log bound implies this quantitative four-power bound; no occurrence
of (118) is used as an input in the preceding derivation. -/
theorem signed_density_theorem_5_8 (r : ℕ)
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    {s η : ℝ} (hs : 0 < s) (hs' : s < 4 / 3) (_hη : 0 < η)
    (_hη₁ : η < 1 - 3 * s / 4) (_hη₂ : η < 1 / 2 - s / 4)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
      (n : ℕ), 7 ≤ n →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) s
        (conductorLog r n) φ (Z.zeroOrdinate n) +
          (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2‖ ≤
        K * (1 / conductorLog r n +
          ((2 : ℝ) ^ n) ^ (-1 + 3 * s / 4 + η) +
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + s / 4 + η) +
          ((2 : ℝ) ^ n) ^ (-1 + s / 2 + η) +
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + η)) := by
  obtain ⟨K, hK, hb⟩ := signed_density_uniform
    (Family := Family) (Full := Full) (New := New) r hRH cited hDLMF hBessel hs hs' φ heven hsupp
  refine ⟨K, hK, ?_⟩
  intro S Z n hn
  apply (hb S Z n hn).trans
  have hpow : 0 ≤ ((2 : ℝ) ^ n) ^ (-1 + 3 * s / 4 + η) +
      ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + s / 4 + η) +
      ((2 : ℝ) ^ n) ^ (-1 + s / 2 + η) +
      ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + η) := by positivity
  have hm := mul_nonneg hK hpow
  calc
    K / conductorLog r n ≤ K / conductorLog r n +
        K * (((2 : ℝ) ^ n) ^ (-1 + 3 * s / 4 + η) +
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + s / 4 + η) +
          ((2 : ℝ) ^ n) ^ (-1 + s / 2 + η) +
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + η)) := le_add_of_nonneg_right hm
    _ = _ := by ring

/-- Changing the support endpoint does not change any actual signed zero
average, since the entire Schwartz extension is independent of it. -/
theorem signedMeanDensity_support_independent {ι : Type*} [Fintype ι]
    {κ : ι → Type*} (ε : ι → ℂ) (φ : 𝓢(ℝ, ℂ)) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hss : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-s) s)
    (hts : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-t) t)
    (L : ℝ) (γ : ∀ f, κ f → ℂ) :
    signedMeanDensity ε s L φ γ = signedMeanDensity ε t L φ γ := by
  unfold signedMeanDensity
  congr 1
  funext f
  rw [ExplicitFormula.density_support_independent φ hs ht hss hts]

/-- Theorem 1.2, with the exact finite root-number average and actual zero
ordinates. Only the cited general assumptions remain at the boundary. -/
theorem signed_density_theorem_1_2 {r : ℕ}
    (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Ioo (-(4 / 3 : ℝ)) (4 / 3)) :
    ∃ K ≥ 0, ∀ n : ℕ, 7 ≤ n →
      ‖signedMeanDensity (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (4 / 3)
        (conductorLog r n) φ (Z.zeroOrdinate n) +
          (∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2‖ ≤
        K / conductorLog r n := by
  obtain ⟨s, hs, hsb, hsupport⟩ := SupportEndpoint.support_endpoint_of_tsupport_subset
    (𝓕 φ : 𝓢(ℝ, ℂ)) (by norm_num : (0 : ℝ) < 4 / 3) hsupp
  obtain ⟨K, hK, hb⟩ := signed_density_uniform
    (Family := Family) (Full := Full) (New := New) r hRH cited hDLMF hBessel hs hsb φ heven hsupport
  refine ⟨K, hK, ?_⟩
  intro n hn
  have hbig : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Icc (-(4 / 3 : ℝ)) (4 / 3) :=
    subset_closure.trans (hsupp.trans Set.Ioo_subset_Icc_self)
  rw [← signedMeanDensity_support_independent _ φ hs.le (by norm_num : (0 : ℝ) ≤ 4 / 3)
    hsupport hbig]
  exact hb S Z n hn

/-- The actual signed zero averages have the limit asserted in Theorem 1.2. -/
theorem signed_density_limit {r : ℕ}
    (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    (hDLMF : DigammaBound.DLMFSeriesIdentity) (hBessel : BesselFirstKind.DLMFIdentities)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Ioo (-(4 / 3 : ℝ)) (4 / 3)) :
    Filter.Tendsto (fun n : ℕ => signedMeanDensity
      (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (4 / 3)
      (conductorLog r n) φ (Z.zeroOrdinate n)) Filter.atTop
      (nhds (-(∫ u in (Icc (-1) 1)ᶜ, (𝓕 φ : 𝓢(ℝ, ℂ)) u) / 2)) := by
  obtain ⟨K, _, hb⟩ := signed_density_theorem_1_2 S Z hRH cited hDLMF hBessel φ heven hsupp
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

/-- Absolute convergence of every zero observation used by the signed
endpoint follows from the actual zero-counting data, including depth seven. -/
theorem signed_zero_sum_absolutely_convergent {r : ℕ}
    (S : SignedArithmeticData r Family Full New) (Z : AnalyticData S)
    (ZC : ZeroCountingData Z) (n : ℕ) (hn : 7 ≤ n)
    (φ : 𝓢(ℝ, ℂ))
    (hsupp : tsupport (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Ioo (-(4 / 3 : ℝ)) (4 / 3))
    (f : Family (2 ^ n)) :
    Summable (fun i => ‖EntireExtension.extension (4 / 3) (𝓕 φ : 𝓢(ℝ, ℂ))
      (((conductorLog r n / (2 * Real.pi) : ℝ) : ℂ) * Z.zeroOrdinate n f i)‖) := by
  exact ZC.zero_sum_absolutely_convergent n hn (by norm_num) φ
    (subset_closure.trans (hsupp.trans Set.Ioo_subset_Icc_self)) f

end DepthAspect.SignedDensity
