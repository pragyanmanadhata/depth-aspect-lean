import DepthAspect.HypotheticalPrimeAverages

/-! Consequences of the explicitly hypothetical arithmetic estimates for
actual individual trace weights and the full spectral block. -/
namespace DepthAspect.HypotheticalSignedDensity
open MeasureTheory Set SignedDensity SignedSieve QuadraticClassFormula
open QuadraticDiscriminantL TraceWeightVariation SignedVariationAssembly
open scoped BigOperators SchwartzMap

theorem even_traceIndexError_bound (improved : StrengthenedPrimeAverages) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (k a : ℕ), 2 ≤ a → ∀ X Y L s : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 3 ≤ Y → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ∀ h : 𝓢(ℝ, ℂ), ∀ j ∈ activeIndices ((2 : ℝ) ^ (2 * a + 4)) Y,
      ‖traceIndexError k ((2 : ℝ) ^ (2 * a + 4)) L X Y h
        (UnsignedDensity.primeBases L s) (evenLValue G a) j‖ ≤
        C * Real.sqrt
          ((‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))) *
            (‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ)) +
              weightVariation (2 * (k : ℝ) + 1) L X Y
                ((2 : ℝ) ^ (2 * a + 4)) h j)) * X ^ (1 / 2 + ε) := by
  obtain ⟨Cε, hCε, hb⟩ := even_weighted_prime_average_bound improved hε
  refine ⟨Cε * (2 : ℝ) ^ (1 / 2 + ε), by positivity, ?_⟩
  intro H G k a ha X Y L s hX hXY hY hY3 hL hYs h j hj
  let N : ℝ := (2 : ℝ) ^ (2 * a + 4)
  let t : ℤ := (2 : ℤ) ^ (a + 1) * j
  let c : ℝ := traceParameter N j
  let A : ℝ := max X (N * (j : ℝ) ^ 2 / 16)
  let M₀ : ℝ := ‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))
  let Φ : ℝ → ℂ := traceWeight (2 * (k : ℝ) + 1) c L h
  have hN : 0 < N := by dsimp [N]; positivity
  have hX0 : 0 < X := by linarith
  have hA0 : 0 < A := hX0.trans_le (le_max_left _ _)
  have hAY : A ≤ Y := max_le hXY
    ((mem_activeIndices hN (hX0.trans_le hXY) j).mp hj).le
  have hcA : c ^ 2 ≤ A := by
    dsimp [c]
    rw [traceParameter_sq hN.le]
    exact le_max_right _ _
  have htA : (t : ℝ) ^ 2 ≤ 4 * A := by
    have ht := even_traceParameter_square a j
    change (t : ℝ) ^ 2 = 4 * c ^ 2 at ht
    nlinarith
  have ht8 : 8 ∣ t := even_trace_eight_dvd a ha j
  obtain ⟨hI, hbound, hvariation⟩ := schwartz_traceWeight_variation h
    (by positivity : 0 ≤ 2 * (k : ℝ) + 1) hL hX0 (le_max_left _ _)
    hAY hY hcA
  have hreg : ContinuousOn Φ (Icc A Y) := traceWeight_continuousOn _ _ _ h hA0
  have hdreg : ∀ u ∈ Ioo A Y, DifferentiableAt ℝ Φ u := by
    intro u hu
    exact traceWeight_differentiableAt _ _ _ h (hcA.trans_lt hu.1)
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  have he := hb G t A Y M₀ Φ ht8 hA0.le hAY hY3 htA hM₀ hreg hdreg hI hbound
  have hmean := even_meanLValueCoefficient a j
  have hset := primeBases_interval_eq (L := L) (s := s) hA0.le hYs
  have heq : traceIndexError k N L X Y h (UnsignedDensity.primeBases L s) (evenLValue G a) j =
      (∑ P ∈ PrimeAverageSmoothing.primeSet A Y, (Real.log (P : ℝ) : ℂ) *
        ((2 : ℂ) * (primeWeight (P : ℤ) : ℂ) * LAtOne G (t ^ 2 - 4 * (P : ℤ)) * Φ P)) -
        ((Real.pi : ℂ) ^ 2 / 8 * (ArithmeticWeights.integerPrimeWeight 2 t : ℂ)) *
          (∫ u in A..Y, Φ u) := by
    unfold traceIndexError
    rw [hset, hmean]
    simp only [Complex.real_smul, evenLValue, Φ, c, traceParameter]
    rfl
  rw [heq]
  have hVeq : (∫ u in A..Y, ‖deriv Φ u‖) =
      weightVariation (2 * (k : ℝ) + 1) L X Y N h j := by
    unfold weightVariation lowerEndpoint
    rw [traceParameter_sq hN.le] <;> rfl
  rw [hVeq] at he
  have hsqrt : Cε * Real.sqrt M₀ *
      Real.sqrt (M₀ + weightVariation (2 * (k : ℝ) + 1) L X Y N h j) =
      Cε * Real.sqrt (M₀ * (M₀ + weightVariation (2 * (k : ℝ) + 1) L X Y N h j)) := by
    rw [Real.sqrt_mul hM₀]
    ring
  rw [hsqrt] at he
  have hpow : Y ^ (1 / 2 + ε) ≤ (2 : ℝ) ^ (1 / 2 + ε) * X ^ (1 / 2 + ε) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0.le]
    exact Real.rpow_le_rpow (by linarith) hY (by linarith)
  exact he.trans (by
    have hm := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg hCε.le (Real.sqrt_nonneg (M₀ * (M₀ + weightVariation
        (2 * (k : ℝ) + 1) L X Y N h j))))
    convert hm using 1 <;> ring)

/-- The actual unnormalized even-depth block estimate (112), with all
individual arithmetic and variation estimates discharged. The remaining
dimension inequality is supplied by Martin's general formula at the
spectral-family endpoint. -/
theorem even_trace_block_bound (improved : StrengthenedPrimeAverages) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (k a : ℕ), 2 ≤ a → ∀ X Y L s d : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 3 ≤ Y → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ((2 : ℝ) ^ (2 * a + 4)) / 64 ≤ d → ∀ h : 𝓢(ℝ, ℂ),
      ‖primeTraceBlock k ((2 : ℝ) ^ (2 * a + 4)) d L X Y h
          (UnsignedDensity.primeBases L s) (evenLValue G a) -
        (∫ u in X..Y, (traceDimensionScale k ((2 : ℝ) ^ (2 * a + 4)) d *
          MurmurationArithmetic.M k 2 (u / ((2 : ℝ) ^ (2 * a + 4))) / u) •
            h (Real.log u / L))‖ ≤
        C * ((2 + (2 * (k : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h) *
          ((((2 : ℝ) ^ (2 * a + 4)) ^ (-(1 / 2 : ℝ))) * X ^ (ε) +
            (((2 : ℝ) ^ (2 * a + 4)) ^ (-1 : ℝ)) * X ^ (1 / 2 + ε)) := by
  obtain ⟨C, hC, hb⟩ := even_traceIndexError_bound improved hε
  refine ⟨256 * Real.sqrt 2 * C / Real.pi, by positivity, ?_⟩
  intro H G k a ha X Y L s d hX hXY hY hY3 hL hYs hdim h
  have he := trace_block_bound k (ε := ε - 1 / 4) (by positivity : 0 < (2 : ℝ) ^ (2 * a + 4))
    hdim (by linarith : 0 < X) hXY hY hL hC.le h
    (UnsignedDensity.primeBases L s) (evenLValue G a)
    (by
      simpa only [show (3 / 4 : ℝ) + (ε - 1 / 4) = 1 / 2 + ε by ring] using
        hb G k a ha X Y L s hX hXY hY hY3 hL hYs h)
  simp only [show (1 / 4 : ℝ) + (ε - 1 / 4) = ε by ring,
    show (3 / 4 : ℝ) + (ε - 1 / 4) = 1 / 2 + ε by ring] at he
  convert he using 1 <;> ring

theorem odd_traceIndexError_bound (improved : StrengthenedPrimeAverages) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (k a : ℕ), 1 ≤ a → ∀ X Y L s : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 3 ≤ Y → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ∀ h : 𝓢(ℝ, ℂ), ∀ j ∈ activeIndices ((2 : ℝ) ^ (2 * a + 5)) Y,
      ‖traceIndexError k ((2 : ℝ) ^ (2 * a + 5)) L X Y h
        (UnsignedDensity.primeBases L s) (oddLValue G a) j‖ ≤
        C * Real.sqrt
          ((‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))) *
            (‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ)) +
              weightVariation (2 * (k : ℝ) + 1) L X Y
                ((2 : ℝ) ^ (2 * a + 5)) h j)) * X ^ (1 / 2 + ε) := by
  obtain ⟨Cε, hCε, hb⟩ := improved.odd ε hε
  refine ⟨Cε * (2 : ℝ) ^ (1 / 2 + ε), by positivity, ?_⟩
  intro H G k a ha X Y L s hX hXY hY hY3 hL hYs h j hj
  let N : ℝ := (2 : ℝ) ^ (2 * a + 5)
  let t : ℤ := (2 : ℤ) ^ (a + 2) * j
  let c : ℝ := traceParameter N j
  let A : ℝ := max X (N * (j : ℝ) ^ 2 / 16)
  let M₀ : ℝ := ‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))
  let Φ : ℝ → ℂ := traceWeight (2 * (k : ℝ) + 1) c L h
  have hN : 0 < N := by dsimp [N]; positivity
  have hX0 : 0 < X := by linarith
  have hA0 : 0 < A := hX0.trans_le (le_max_left _ _)
  have hAY : A ≤ Y := max_le hXY
    ((mem_activeIndices hN (hX0.trans_le hXY) j).mp hj).le
  have hcA : c ^ 2 ≤ A := by
    dsimp [c]
    rw [traceParameter_sq hN.le]
    exact le_max_right _ _
  have htA : (t : ℝ) ^ 2 ≤ 8 * A := by
    have ht := odd_traceParameter_square a j
    change (t : ℝ) ^ 2 = 8 * c ^ 2 at ht
    nlinarith
  have ht8 : 8 ∣ t := odd_trace_eight_dvd a ha j
  obtain ⟨hI, hbound, hvariation⟩ := schwartz_traceWeight_variation h
    (by positivity : 0 ≤ 2 * (k : ℝ) + 1) hL hX0 (le_max_left _ _)
    hAY hY hcA
  have hreg : ContinuousOn Φ (Icc A Y) := traceWeight_continuousOn _ _ _ h hA0
  have hdreg : ∀ u ∈ Ioo A Y, DifferentiableAt ℝ Φ u := by
    intro u hu
    exact traceWeight_differentiableAt _ _ _ h (hcA.trans_lt hu.1)
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  have hA2 : 2 ≤ A := hX.trans (le_max_left _ _)
  have he := hb G t A Y M₀ Φ ht8 hA2 hAY hY3 htA hM₀ hreg hdreg hI hbound
  have hmean := odd_meanLValueCoefficient a j
  have hset := primeBases_interval_eq (L := L) (s := s) hA0.le hYs
  have heq : traceIndexError k N L X Y h (UnsignedDensity.primeBases L s) (oddLValue G a) j =
      (∑ P ∈ PrimeAverageSmoothing.primeSet A Y, (Real.log (P : ℝ) : ℂ) *
        (LAtOne G (t ^ 2 - 8 * (P : ℤ)) * Φ P)) -
        ((Real.pi : ℂ) ^ 2 / 8 * (ArithmeticWeights.integerPrimeWeight 2 t : ℂ)) *
          (∫ u in A..Y, Φ u) := by
    unfold traceIndexError
    rw [hset, hmean]
    simp only [Complex.real_smul, oddLValue, Φ, c, traceParameter] <;> rfl
  rw [heq]
  have hVeq : (∫ u in A..Y, ‖deriv Φ u‖) =
      weightVariation (2 * (k : ℝ) + 1) L X Y N h j := by
    unfold weightVariation lowerEndpoint
    rw [traceParameter_sq hN.le] <;> rfl
  rw [hVeq] at he
  have hsqrt : Cε * Real.sqrt M₀ *
      Real.sqrt (M₀ + weightVariation (2 * (k : ℝ) + 1) L X Y N h j) =
      Cε * Real.sqrt (M₀ * (M₀ + weightVariation (2 * (k : ℝ) + 1) L X Y N h j)) := by
    rw [Real.sqrt_mul hM₀]
    ring
  rw [hsqrt] at he
  have hpow : Y ^ (1 / 2 + ε) ≤ (2 : ℝ) ^ (1 / 2 + ε) * X ^ (1 / 2 + ε) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hX0.le]
    exact Real.rpow_le_rpow (by linarith) hY (by linarith)
  exact he.trans (by
    have hm := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg hCε.le (Real.sqrt_nonneg (M₀ * (M₀ + weightVariation
        (2 * (k : ℝ) + 1) L X Y N h j))))
    convert hm using 1 <;> ring)

/-- The actual unnormalized odd-depth block estimate (112), with all
individual arithmetic and variation estimates discharged. The remaining
dimension inequality is supplied by Martin's general formula at the
spectral-family endpoint. -/
theorem odd_trace_block_bound (improved : StrengthenedPrimeAverages) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : ℤ → ℝ} (G : GeneralFormula H)
      (k a : ℕ), 1 ≤ a → ∀ X Y L s d : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 3 ≤ Y → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ((2 : ℝ) ^ (2 * a + 5)) / 64 ≤ d → ∀ h : 𝓢(ℝ, ℂ),
      ‖primeTraceBlock k ((2 : ℝ) ^ (2 * a + 5)) d L X Y h
          (UnsignedDensity.primeBases L s) (oddLValue G a) -
        (∫ u in X..Y, (traceDimensionScale k ((2 : ℝ) ^ (2 * a + 5)) d *
          MurmurationArithmetic.M k 2 (u / ((2 : ℝ) ^ (2 * a + 5))) / u) •
            h (Real.log u / L))‖ ≤
        C * ((2 + (2 * (k : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h) *
          ((((2 : ℝ) ^ (2 * a + 5)) ^ (-(1 / 2 : ℝ))) * X ^ (ε) +
            (((2 : ℝ) ^ (2 * a + 5)) ^ (-1 : ℝ)) * X ^ (1 / 2 + ε)) := by
  obtain ⟨C, hC, hb⟩ := odd_traceIndexError_bound improved hε
  refine ⟨256 * Real.sqrt 2 * C / Real.pi, by positivity, ?_⟩
  intro H G k a ha X Y L s d hX hXY hY hY3 hL hYs hdim h
  have he := trace_block_bound k (ε := ε - 1 / 4) (by positivity : 0 < (2 : ℝ) ^ (2 * a + 5))
    hdim (by linarith : 0 < X) hXY hY hL hC.le h
    (UnsignedDensity.primeBases L s) (oddLValue G a)
    (by
      simpa only [show (3 / 4 : ℝ) + (ε - 1 / 4) = 1 / 2 + ε by ring] using
        hb G k a ha X Y L s hX hXY hY hY3 hL hYs h)
  simp only [show (1 / 4 : ℝ) + (ε - 1 / 4) = ε by ring,
    show (3 / 4 : ℝ) + (ε - 1 / 4) = 1 / 2 + ε by ring] at he
  convert he using 1 <;> ring

variable {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

theorem signed_prime_elliptic_block_bound (k : ℕ) (h : 𝓢(ℝ, ℂ))
    (improved : StrengthenedPrimeAverages)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SignedArithmeticData k Family Full New)
      (n : ℕ), 7 ≤ n → ∀ X Y L s : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 3 ≤ Y → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ‖ellipticPrimeBlock S n L s X Y h -
        (∫ u in X..Y, (traceDimensionScale k ((2 : ℝ) ^ n)
          (Fintype.card (Family (2 ^ n)) : ℝ) *
          MurmurationArithmetic.M k 2 (u / ((2 : ℝ) ^ n)) / u) •
            h (Real.log u / L))‖ ≤
        C * ((((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * X ^ (ε) +
          (((2 : ℝ) ^ n) ^ (-1 : ℝ)) * X ^ (1 / 2 + ε)) := by
  obtain ⟨Ce, hCe, hbe⟩ := even_trace_block_bound improved hε
  obtain ⟨Co, hCo, hbo⟩ := odd_trace_block_bound improved hε
  let A := (2 + (2 * (k : ℝ) + 1) * (Real.pi / 2)) * schwartzSize h
  have hA : 0 ≤ A := by dsimp [A, schwartzSize]; positivity
  refine ⟨(Ce + Co) * (A + 1), by positivity, ?_⟩
  intro S n hn X Y L s hX hXY hY hY3 hL hYs
  have hdim := signed_dimension_lower_weak S n hn
  have hE : 0 ≤ (((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * X ^ (ε) +
      (((2 : ℝ) ^ n) ^ (-1 : ℝ)) * X ^ (1 / 2 + ε) := by positivity
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨b, hb⟩ := heven
    let a := b - 2
    have heq : n = 2 * a + 4 := by dsimp [a]; omega
    have ha : 2 ≤ a := by omega
    rw [heq] at hdim hE ⊢
    rw [ellipticPrimeBlock_even S a ha]
    have hbound := hbe S.quadratic_class_formula k a ha X Y L s _
      hX hXY hY hY3 hL hYs hdim h
    refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hE)
    change Ce * A ≤ (Ce + Co) * (A + 1)
    nlinarith
  · obtain ⟨b, hb⟩ := hodd
    let a := b - 2
    have heq : n = 2 * a + 5 := by dsimp [a]; omega
    have ha : 1 ≤ a := by omega
    rw [heq] at hdim hE ⊢
    rw [ellipticPrimeBlock_odd S a ha]
    have hbound := hbo S.quadratic_class_formula k a ha X Y L s _
      hX hXY hY hY3 hL hYs hdim h
    refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hE)
    change Co * A ≤ (Ce + Co) * (A + 1)
    nlinarith

end DepthAspect.HypotheticalSignedDensity
