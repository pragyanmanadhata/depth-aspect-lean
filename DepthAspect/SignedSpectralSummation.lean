import DepthAspect.SignedSpectralBlock
import DepthAspect.SignedBlockSummation
import DepthAspect.SignedSmallBlock
import DepthAspect.MurmurationPrimeIntegral

/-!
# Equation (113) for the literal spectral trace

The finite dyadic partition is bounded by the actual Fourier-support
cutoff. Its final block below three is treated by the absence of odd
primes and the proved small-density bound. Thus neither a missing final
block nor a prime-average premise remains in the summation theorem.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set SignedSieve MurmurationArithmetic DirichletRH GRHConsequences
open scoped BigOperators SchwartzMap

variable {k : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

theorem signed_traceDimensionScale_bounds (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (hn : 7 ≤ n) :
    0 ≤ traceDimensionScale k ((2 : ℝ) ^ n)
      (Fintype.card (Family (2 ^ n)) : ℝ) ∧
    traceDimensionScale k ((2 : ℝ) ^ n)
      (Fintype.card (Family (2 ^ n)) : ℝ) ≤ 2 := by
  have hb := signed_dimension_lower S n hn
  have hd := signed_dimension_lower_weak S n hn
  have hd0 : (0 : ℝ) < Fintype.card (Family (2 ^ n)) :=
    lt_of_lt_of_le (by positivity) hd
  unfold traceDimensionScale
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) <
        32 * (Fintype.card (Family (2 ^ n)) : ℝ))).mpr
    push_cast
    linarith

/-- The finite spectral sum partitions exactly over adjacent real intervals. -/
theorem ellipticPrimeBlock_add (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (L s A B C : ℝ) (hAB : A ≤ B) (hBC : B ≤ C)
    (h : 𝓢(ℝ, ℂ)) :
    ellipticPrimeBlock S n L s A C h =
      ellipticPrimeBlock S n L s A B h + ellipticPrimeBlock S n L s B C h := by
  classical
  unfold ellipticPrimeBlock
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hPA : A < (P : ℝ)
  · by_cases hPB : (P : ℝ) ≤ B
    · have hPC := hPB.trans hBC
      simp [hPA, hPB, hPC, not_lt.mpr hPB]
    · have hBP : B < (P : ℝ) := lt_of_not_ge hPB
      by_cases hPC : (P : ℝ) ≤ C <;> simp [hPA, hPB, hBP, hPC]
  · have hBP : ¬ B < (P : ℝ) := by linarith
    simp [hPA, hBP]

noncomputable def ellipticDiscrepancyPrefix (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (L s : ℝ) (h : 𝓢(ℝ, ℂ)) (X : ℝ) : ℂ :=
  ellipticPrimeBlock S n L s 2 X h -
    (∫ u in (2 : ℝ)..X, (traceDimensionScale k ((2 : ℝ) ^ n)
      (Fintype.card (Family (2 ^ n)) : ℝ) * M k 2 (u / ((2 : ℝ) ^ n)) / u) •
        h (Real.log u / L))

@[simp] theorem ellipticDiscrepancyPrefix_two
    (S : SignedArithmeticData k Family Full New) (n : ℕ) (L s : ℝ)
    (h : 𝓢(ℝ, ℂ)) : ellipticDiscrepancyPrefix S n L s h 2 = 0 := by
  classical
  simp only [ellipticDiscrepancyPrefix, intervalIntegral.integral_same, sub_zero]
  unfold ellipticPrimeBlock
  have hempty : (UnsignedDensity.primeBases L s).filter
      (fun P : ℕ => (2 : ℝ) < P ∧ (P : ℝ) ≤ 2) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro P hP hbad
    exact (not_lt.mpr hbad.2) hbad.1
  rw [hempty, Finset.sum_empty]

theorem ellipticDiscrepancyPrefix_sub
    (S : SignedArithmeticData k Family Full New) (n : ℕ) (L s A B : ℝ)
    (hA : 2 ≤ A) (hAB : A ≤ B) (h : 𝓢(ℝ, ℂ)) :
    ellipticDiscrepancyPrefix S n L s h B - ellipticDiscrepancyPrefix S n L s h A =
      ellipticPrimeBlock S n L s A B h -
        (∫ u in A..B, (traceDimensionScale k ((2 : ℝ) ^ n)
          (Fintype.card (Family (2 ^ n)) : ℝ) * M k 2 (u / ((2 : ℝ) ^ n)) / u) •
            h (Real.log u / L)) := by
  have hi := trace_main_intervalIntegrable k (by positivity : 0 < (2 : ℝ) ^ n)
    (Fintype.card (Family (2 ^ n)) : ℝ) L B (hA.trans hAB) h
  have hiA := hi.mono_set (c := (2 : ℝ)) (d := A) (by
    rw [Set.uIcc_of_le hA, Set.uIcc_of_le (hA.trans hAB)]
    exact Set.Icc_subset_Icc le_rfl hAB)
  have hiAB := hi.mono_set (c := A) (d := B) (by
    rw [Set.uIcc_of_le hAB, Set.uIcc_of_le (hA.trans hAB)]
    exact Set.Icc_subset_Icc hA le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hiA hiAB
  unfold ellipticDiscrepancyPrefix
  rw [ellipticPrimeBlock_add S n L s 2 A B hA hAB h, ← hadd]
  abel

/-- The actual block estimate remains valid below three; its constant is
uniform in the family and no arithmetic character estimate is used there. -/
theorem signed_prime_elliptic_block_bound_all (k : ℕ) (h : 𝓢(ℝ, ℂ))
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SignedArithmeticData k Family Full New)
      (n : ℕ), 7 ≤ n → ∀ X Y L s : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ‖ellipticPrimeBlock S n L s X Y h -
        (∫ u in X..Y, (traceDimensionScale k ((2 : ℝ) ^ n)
          (Fintype.card (Family (2 ^ n)) : ℝ) * M k 2 (u / ((2 : ℝ) ^ n)) / u) •
            h (Real.log u / L))‖ ≤
        C * ((((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * X ^ (1 / 4 + ε) +
          (((2 : ℝ) ^ n) ^ (-1 : ℝ)) * X ^ (3 / 4 + ε)) := by
  obtain ⟨C, hC, hb⟩ := signed_prime_elliptic_block_bound
    (Family := Family) (Full := Full) (New := New) k h hRH cited hε
  obtain ⟨Cs, hCs, hs⟩ := SignedSmallBlock.main_integral_small_block k Nat.prime_two
  let E := 2 * (Cs * Real.sqrt 3 * ‖h.toBoundedContinuousFunction‖)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨C + E, by positivity, ?_⟩
  intro S n hn X Y L s hX hXY hY hL hYs
  let N : ℝ := (2 : ℝ) ^ n
  let d : ℝ := Fintype.card (Family (2 ^ n))
  have hN : 0 < N := by dsimp [N]; positivity
  have hN3 : 3 ≤ N := by
    have he := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    norm_num at he
    dsimp [N]
    linarith
  have hmain := signed_traceDimensionScale_bounds S n hn
  have herror : 0 ≤ N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) +
      N ^ (-1 : ℝ) * X ^ (3 / 4 + ε) := by positivity
  by_cases hY3 : 3 ≤ Y
  · exact (hb S n hn X Y L s hX hXY hY hY3 hL hYs).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + E) herror)
  · have hYsmall : Y < 3 := lt_of_not_ge hY3
    have hzero : ellipticPrimeBlock S n L s X Y h = 0 := by
      unfold ellipticPrimeBlock
      rw [SignedSmallBlock.prime_interval_empty L s hX hYsmall, Finset.sum_empty]
    rw [hzero, zero_sub, norm_neg]
    have hscalar : (∫ u in X..Y, (traceDimensionScale k N d * M k 2 (u / N) / u) •
        h (Real.log u / L)) = traceDimensionScale k N d •
        (∫ v in (X / N)..(Y / N), MurmurationPrimeIntegral.weightedIntegrand k 2 N L h v) := by
      rw [← MurmurationPrimeIntegral.change_variable k 2 hN L X Y h,
        ← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      rw [smul_smul]
      congr 1
      ring
    change ‖∫ u in X..Y, (traceDimensionScale k N d * M k 2 (u / N) / u) •
      h (Real.log u / L)‖ ≤ _
    rw [hscalar, norm_smul, Real.norm_eq_abs, abs_of_nonneg hmain.1]
    have his := hs X Y N L hX hXY hYsmall hN3 h
    have hsmall : traceDimensionScale k N d *
        ‖∫ v in (X / N)..(Y / N), MurmurationPrimeIntegral.weightedIntegrand k 2 N L h v‖ ≤
        E * N ^ (-(1 / 2 : ℝ)) := by
      calc
        _ ≤ 2 * ((Cs * Real.sqrt 3 * ‖h.toBoundedContinuousFunction‖) *
            N ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hmain.2 his (norm_nonneg _) (by norm_num)
        _ = _ := by dsimp [E]; ring
    have hXpow : 1 ≤ X ^ (1 / 4 + ε) :=
      Real.one_le_rpow (by linarith) (by linarith)
    have hEsum : E * N ^ (-(1 / 2 : ℝ)) ≤
        (C + E) * (N ^ (-(1 / 2 : ℝ)) * X ^ (1 / 4 + ε) +
          N ^ (-1 : ℝ) * X ^ (3 / 4 + ε)) := by
      have hfirst := mul_le_mul_of_nonneg_left hXpow
        (show 0 ≤ N ^ (-(1 / 2 : ℝ)) by positivity)
      have hsecond : 0 ≤ N ^ (-1 : ℝ) * X ^ (3 / 4 + ε) := by positivity
      nlinarith
    exact hsmall.trans hEsum

/-- The literal finite spectral sum satisfies (113), with its two exact
geometric constants and the actual support endpoint exp(sL). -/
theorem signed_prime_elliptic_sum_bound (k : ℕ) (h : 𝓢(ℝ, ℂ))
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SignedArithmeticData k Family Full New)
      (n : ℕ), 7 ≤ n → ∀ L s : ℝ, 1 ≤ L → 2 ≤ Real.exp (s * L) →
      ‖ellipticDiscrepancyPrefix S n L s h (Real.exp (s * L))‖ ≤
        C * (((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (s * L)) ^ (1 / 4 + ε) / (1 - (2 : ℝ) ^ (-(1 / 4 + ε))) +
          ((2 : ℝ) ^ n) ^ (-1 : ℝ) *
          (Real.exp (s * L)) ^ (3 / 4 + ε) / (1 - (2 : ℝ) ^ (-(3 / 4 + ε)))) := by
  obtain ⟨C, hC, hb⟩ := signed_prime_elliptic_block_bound_all
    (Family := Family) (Full := Full) (New := New) k h hRH cited hε
  refine ⟨C, hC, ?_⟩
  intro S n hn L s hL hX
  have he := SignedDyadicSummation.two_power_sum_bound_bounded hX
    (by linarith : 0 < 1 / 4 + ε) (by linarith : 0 < 3 / 4 + ε)
    (by positivity : 0 ≤ C * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)))
    (by positivity : 0 ≤ C * ((2 : ℝ) ^ n) ^ (-1 : ℝ))
    (ellipticDiscrepancyPrefix S n L s h) (fun A B hA hAB hB hBX => by
      rw [ellipticDiscrepancyPrefix_sub S n L s A B hA hAB h]
      have he := hb S n hn A B L s hA hAB hB hL hBX
      exact he.trans_eq (by ring))
  rw [ellipticDiscrepancyPrefix_two, sub_zero] at he
  exact he.trans_eq (by ring)

end DepthAspect.SignedDensity
