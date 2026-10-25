import DepthAspect.EvenPrimeAverage
import DepthAspect.SignedBlockIdentity
import DepthAspect.SignedTraceIndices
import DepthAspect.UnsignedDensity

/-!
# Discharging the individual arithmetic errors at even depth

This applies the actual prime-average theorem to the actual trace weight,
including its endpoint derivative and canonical finite prime set. The
constant is chosen before depth, weight, class data, and Schwartz test.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set DirichletRH GRHConsequences QuadraticClassFormula
open QuadraticDiscriminantL TraceWeightVariation SignedVariationAssembly
open scoped BigOperators SchwartzMap

/-- A canonical prime-box subinterval equals the literal prime set in
Theorem 5.5. The floor endpoints and odd-prime restrictions are retained. -/
theorem primeBases_interval_eq {L s A B : ℝ} (hA : 0 ≤ A)
    (hB : B ≤ Real.exp (s * L)) :
    (UnsignedDensity.primeBases L s).filter
      (fun (P : ℕ) => A < (P : ℝ) ∧ (P : ℝ) ≤ B) = PrimeAverageSmoothing.primeSet A B := by
  classical
  ext P
  simp only [UnsignedDensity.primeBases, PrimeAverageSmoothing.primeSet,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hP2, hPX⟩, hprime, hodd⟩, hAP, hPB⟩
    exact ⟨⟨(Nat.floor_lt hA).mpr hAP, Nat.le_floor hPB⟩, hprime, hodd⟩
  · rintro ⟨⟨hAP, hPB⟩, hprime, hodd⟩
    have hPB' : (P : ℝ) ≤ B := (Nat.le_floor_iff' hprime.ne_zero).mp hPB
    exact ⟨⟨⟨hprime.two_le, Nat.le_floor (hPB'.trans hB)⟩, hprime, hodd⟩,
      (Nat.floor_lt hA).mp hAP, hPB'⟩

noncomputable def evenLValue {H : ℤ → ℝ} (G : GeneralFormula H)
    (a : ℕ) (j : ℤ) (P : ℕ) : ℂ :=
  (2 : ℂ) * (primeWeight (P : ℤ) : ℂ) *
    LAtOne G (((2 : ℤ) ^ (a + 1) * j) ^ 2 - 4 * (P : ℤ))

/-- The exact square scale of the even-depth trace parameter. -/
theorem even_traceParameter_square (a : ℕ) (j : ℤ) :
    (((2 : ℤ) ^ (a + 1) * j : ℤ) : ℝ) ^ 2 =
      4 * (traceParameter ((2 : ℝ) ^ (2 * a + 4)) j) ^ 2 := by
  rw [traceParameter_sq (by positivity)]
  push_cast
  rw [mul_pow, ← pow_mul,
    show (a + 1) * 2 = 2 * a + 2 by omega,
    show 2 * a + 4 = (2 * a + 2) + 2 by omega, pow_add]
  norm_num
  ring

/-- The arithmetic mean is unchanged by the actual power-of-two trace
scale, including j=0 and negative trace indices. -/
theorem even_meanLValueCoefficient (a : ℕ) (j : ℤ) :
    (Real.pi : ℂ) ^ 2 / 8 *
      (ArithmeticWeights.integerPrimeWeight 2 ((2 : ℤ) ^ (a + 1) * j) : ℂ) =
        (meanLValueCoefficient j : ℂ) := by
  have hweight : ArithmeticWeights.integerPrimeWeight 2 ((2 : ℤ) ^ (a + 1) * j) =
      ArithmeticWeights.integerPrimeWeight 2 j := by
    simpa only [Nat.cast_ofNat] using
      ArithmeticWeights.integerPrimeWeight_omitted_pow_mul 2 (a + 1) j
  rw [hweight]
  simp only [meanLValueCoefficient, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- The actual individual bound needed by the even-depth application of
(112). Endpoint regularity, the complete prime set, and the main
coefficient are all proved; only the cited general RH input is external. -/
theorem even_traceIndexError_bound (hRH : PrimitiveDirichletRH)
    (cited : CitedGeneralTheorems) {ε : ℝ} (hε : 0 < ε) :
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
                ((2 : ℝ) ^ (2 * a + 4)) h j)) * X ^ (3 / 4 + ε) := by
  obtain ⟨Cε, hCε, hb⟩ := EvenPrimeAverage.even_weighted_prime_average_bound hRH cited hε
  refine ⟨Cε * (2 : ℝ) ^ (3 / 4 + ε), by positivity, ?_⟩
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
    rw [traceParameter_sq hN.le]
  rw [hVeq] at he
  have hsqrt : Cε * Real.sqrt M₀ *
      Real.sqrt (M₀ + weightVariation (2 * (k : ℝ) + 1) L X Y N h j) =
      Cε * Real.sqrt (M₀ * (M₀ + weightVariation (2 * (k : ℝ) + 1) L X Y N h j)) := by
    rw [Real.sqrt_mul hM₀]
    ring
  rw [hsqrt] at he
  have hpow : Y ^ (3 / 4 + ε) ≤ (2 : ℝ) ^ (3 / 4 + ε) * X ^ (3 / 4 + ε) := by
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
theorem even_trace_block_bound (hRH : PrimitiveDirichletRH)
    (cited : CitedGeneralTheorems) {ε : ℝ} (hε : 0 < ε) :
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
          ((((2 : ℝ) ^ (2 * a + 4)) ^ (-(1 / 2 : ℝ))) * X ^ (1 / 4 + ε) +
            (((2 : ℝ) ^ (2 * a + 4)) ^ (-1 : ℝ)) * X ^ (3 / 4 + ε)) := by
  obtain ⟨C, hC, hb⟩ := even_traceIndexError_bound hRH cited hε
  refine ⟨256 * Real.sqrt 2 * C / Real.pi, by positivity, ?_⟩
  intro H G k a ha X Y L s d hX hXY hY hY3 hL hYs hdim h
  have he := trace_block_bound k (by positivity : 0 < (2 : ℝ) ^ (2 * a + 4))
    hdim (by linarith : 0 < X) hXY hY hL hC.le h
    (UnsignedDensity.primeBases L s) (evenLValue G a)
    (hb G k a ha X Y L s hX hXY hY hY3 hL hYs h)
  convert he using 1 <;> ring

end DepthAspect.SignedDensity
