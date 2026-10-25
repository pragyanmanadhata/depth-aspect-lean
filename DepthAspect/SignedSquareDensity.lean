import DepthAspect.SignedBalance
import DepthAspect.SignedDensityModel
import DepthAspect.UnsignedErrorAssembly
import DepthAspect.UnsignedPrimeSums

/-!
# The actual signed square contribution in (116)

Lemma 5.1 and Martin's general dimension identity are composed for the
literal signed Hecke average. The two Chebyshev estimates are then applied
to the actual finite prime set. No signed trace-size premise is retained.
-/
namespace DepthAspect.SignedDensity
open SpectralFamily UnsignedDensity PrimePowerApplications ChebyshevWeights
open scoped BigOperators

noncomputable def squareTraceConstant (δ : ℝ) : ℝ :=
  3072 * TraceBounds.uniformClassConstant δ * (4 : ℝ) ^ (1 / 2 + δ)

theorem squareTraceConstant_nonneg {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ squareTraceConstant δ := by
  have hC := (TraceBounds.uniformClassConstant_pos hδ).le
  unfold squareTraceConstant
  positivity

variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- The dimension-normalized form of Lemma 5.1, for the actual shared
spectral family. Depth seven is included by the final finite-prefix lemma. -/
theorem signed_square_average_bound (S : SignedSieve.SignedArithmeticData r Family Full New)
    (n p : ℕ) (hn : 8 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖signedHeckeAverage (fun f => (S.rootNumber (2 ^ n) f : ℂ))
      (S.unsigned.eigenvalues (2 ^ n)) (p ^ 2)‖ ≤
      squareTraceConstant δ *
        (((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + δ) * (p : ℝ) ^ (2 * δ) +
          ((2 : ℝ) ^ n) ^ (-1 + δ) * (p : ℝ) ^ (1 + 2 * δ)) := by
  let N : ℝ := (2 : ℝ) ^ n
  let d : ℝ := Fintype.card (Family (2 ^ n))
  have hN : 0 < N := by dsimp [N]; positivity
  have hr : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) := by positivity
  have hd : ((2 * r + 1 : ℕ) : ℝ) * N / 64 ≤ d := by
    have hb := MartinDimension.polynomial_degree_dimension_lower (2 * r) n hn
      (fun Q => (Fintype.card (Family Q) : ℝ)) S.unsigned.dimension_formula
    convert hb using 1
    dsimp [N, d]
    push_cast
    ring
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hb := S.signed_square_bound n p (by omega) hp (hp.odd_of_ne_two hp2) δ hδ
  change ‖SignedSieve.signedHeckeSum (fun f => (S.rootNumber (2 ^ n) f : ℂ))
    (S.unsigned.eigenvalues (2 ^ n)) (p ^ 2) / (Fintype.card (Family (2 ^ n)) : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hd0).mpr
  have hfirst : N ^ (1 / 2 + δ) = N ^ (-(1 / 2 : ℝ) + δ) * N := by
    rw [show (1 / 2 : ℝ) + δ = (-(1 / 2 : ℝ) + δ) + 1 by ring,
      Real.rpow_add hN, Real.rpow_one]
  have hsecond : N ^ δ = N ^ (-1 + δ) * N := by
    calc
      N ^ δ = N ^ ((-1 + δ) + 1) := by congr 1; ring
      _ = N ^ (-1 + δ) * N := by rw [Real.rpow_add hN, Real.rpow_one]
  have heq : 48 * ((2 * r + 1 : ℕ) : ℝ) * TraceBounds.uniformClassConstant δ *
      (4 : ℝ) ^ (1 / 2 + δ) *
      (N ^ (1 / 2 + δ) * (p : ℝ) ^ (2 * δ) + N ^ δ * (p : ℝ) ^ (1 + 2 * δ)) =
      (squareTraceConstant δ *
        (N ^ (-(1 / 2 : ℝ) + δ) * (p : ℝ) ^ (2 * δ) +
          N ^ (-1 + δ) * (p : ℝ) ^ (1 + 2 * δ))) *
        (((2 * r + 1 : ℕ) : ℝ) * N / 64) := by
    rw [hfirst, hsecond]
    unfold squareTraceConstant
    ring
  have hcoef : 0 ≤ squareTraceConstant δ *
      (N ^ (-(1 / 2 : ℝ) + δ) * (p : ℝ) ^ (2 * δ) +
        N ^ (-1 + δ) * (p : ℝ) ^ (1 + 2 * δ)) := by
    exact mul_nonneg (squareTraceConstant_nonneg hδ) (by positivity)
  exact hb.trans (heq.le.trans (mul_le_mul_of_nonneg_left hd hcoef))

/-- The actual finite two-power prime sum which appears in (116), before
substituting the support endpoint and selecting the small parameter δ. -/
theorem signed_square_hecke_sum_bound_Z
    (S : SignedSieve.SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 8 ≤ n) {Z L H δ : ℝ}
    (hZ : 1 ≤ Z) (hL : 0 < L) (hH : 0 ≤ H) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (hodd : ∀ p ∈ M, p ≠ 2)
    (w : ℕ → ℂ) (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1)
      (fun p => signedHeckeAverage (fun f => (S.rootNumber (2 ^ n) f : ℂ))
        (S.unsigned.eigenvalues (2 ^ n)) (p ^ 2)) w ≤
      (2 * squareTraceConstant δ * H * Real.log 4 / L) *
        (((2 : ℝ) ^ n) ^ (-1 + δ) * Z ^ (1 + 2 * δ) +
          (1 + 1 / (2 * δ)) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + δ) * Z ^ (2 * δ)) := by
  let K := squareTraceConstant δ
  let N : ℝ := (2 : ℝ) ^ n
  have hK := squareTraceConstant_nonneg hδ
  have hN : 0 < N := by dsimp [N]; positivity
  have hC : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ K * N ^ (-1 + δ) := by dsimp [K]; positivity
  have hB : 0 ≤ K * N ^ (-(1 / 2 : ℝ) + δ) := by dsimp [K]; positivity
  have hE : ∀ p ∈ M,
      ‖signedHeckeAverage (fun f => (S.rootNumber (2 ^ n) f : ℂ))
        (S.unsigned.eigenvalues (2 ^ n)) (p ^ 2)‖ ≤
      (K * N ^ (-1 + δ)) * (p : ℝ) ^ (1 + 2 * δ) +
        (K * N ^ (-(1 / 2 : ℝ) + δ)) * (p : ℝ) ^ (2 * δ) := by
    intro p hp
    have ht := signed_square_average_bound S n p hn (Nat.mem_primesLE.mp (hM hp)).2
      (hodd p hp) δ hδ
    convert ht using 1
    dsimp [N, K]
    ring
  have hb := weightedSum_two_power_bound (v := -1) hA hB hH M hM _ w hE hw
  rw [show (1 + 2 * δ) + (-1) = 2 * δ by ring,
    show 2 * δ + (-1) = 2 * δ - 1 by ring] at hb
  have hp := primePowerSum_nonnegative_exponent hZ (by linarith : 0 ≤ 2 * δ)
  have hm := primePowerSum_negative_exponent_all hZ (by linarith : 0 < 2 * δ)
    (by linarith : 2 * δ < 1)
  have ht := mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hp hA) (mul_le_mul_of_nonneg_left hm hB)) hH))
    (by positivity : 0 ≤ 2 / L)
  exact ht.trans_eq (by simp only [K, N]; ring)

/-- The actual `-average ε` part of the signed square coefficient is
controlled by sign balance and the Chebyshev harmonic prime weight. -/
theorem signed_square_constant_bound_Z
    (S : SignedSieve.SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 7 ≤ n) {Z L H : ℝ}
    (hZ : 1 ≤ Z) (hL : 0 < L) (hH : 0 ≤ H)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊)
    (w : ℕ → ℂ) (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1)
      (fun _ => average (fun f => (S.rootNumber (2 ^ n) f : ℂ))) w ≤
      (16 * H * Real.log 4 * (1 + Real.log Z)) /
        (L * ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) := by
  obtain ⟨hR0, _, hRb⟩ := S.relativeRootSum_bounds n hn
  have havg : average (fun f => (S.rootNumber (2 ^ n) f : ℂ)) =
      (S.relativeRootSum (2 ^ n) : ℂ) := by
    unfold average SignedSieve.SignedArithmeticData.relativeRootSum
    push_cast
    rfl
  have hbound : ∀ p ∈ M,
      ‖average (fun f => (S.rootNumber (2 ^ n) f : ℂ))‖ ≤
      (8 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n))) * (p : ℝ) ^ (0 : ℝ) := by
    intro p hp
    rw [havg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0, Real.rpow_zero, mul_one]
    exact hRb
  have hb := weightedSum_power_bound (v := -1) (by positivity) hH M hM _ w hbound hw
  rw [zero_add] at hb
  have hh := primePowerSum_harmonic hZ
  have ht := mul_le_mul_of_nonneg_left (hb.trans
    (mul_le_mul_of_nonneg_left hh (by positivity))) (by positivity : 0 ≤ 2 / L)
  exact ht.trans_eq (by ring)

/-- Equation (116)'s literal signed square sum, including the exact
subtraction of the mean root sign. This estimate is valid on every prime
subset, including an empty set at very small support. -/
theorem signedSquareContribution_bound_Z
    (S : SignedSieve.SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 8 ≤ n) {Z L H δ : ℝ}
    (hZ : 1 ≤ Z) (hL : 0 < L) (hH : 0 ≤ H) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (hodd : ∀ p ∈ M, p ≠ 2)
    (h : ℝ → ℂ) (hh : ∀ x, ‖h x‖ ≤ H) :
    ‖((2 / L : ℝ) : ℂ) * signedSquareContribution
      (fun f => (S.rootNumber (2 ^ n) f : ℂ)) L h
      (S.unsigned.eigenvalues (2 ^ n)) M‖ ≤
      (2 * squareTraceConstant δ * H * Real.log 4 / L) *
        (((2 : ℝ) ^ n) ^ (-1 + δ) * Z ^ (1 + 2 * δ) +
          (1 + 1 / (2 * δ)) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + δ) * Z ^ (2 * δ)) +
      (16 * H * Real.log 4 * (1 + Real.log Z)) /
        (L * ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) := by
  let ε := fun f => (S.rootNumber (2 ^ n) f : ℂ)
  let E := fun p => signedHeckeAverage ε (S.unsigned.eigenvalues (2 ^ n)) (p ^ 2)
  let w := fun p : ℕ => h (2 * Real.log p / L)
  have hP : ∀ p ∈ M, 1 ≤ p := fun p hp => (Nat.mem_primesLE.mp (hM hp)).2.one_le
  have hnorm : ‖signedSquareContribution ε L h (S.unsigned.eigenvalues (2 ^ n)) M‖ ≤
      weightedSum M (-1) (fun p => E p - average ε) w := by
    rw [weightedSum_neg_one]
    unfold signedSquareContribution
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hP p hp))
        (Nat.cast_nonneg _))]
  have hsplit := weightedSum_decomposition M (-1) (fun p => E p - average ε)
    E (fun _ => -average ε) w hP (fun _ _ => sub_eq_add_neg _ _)
  have hneg : weightedSum M (-1) (fun _ => -average ε) w =
      weightedSum M (-1) (fun _ => average ε) w := by
    simp only [weightedSum, norm_neg]
  rw [hneg] at hsplit
  have hfirst := signed_square_hecke_sum_bound_Z S n hn hZ hL hH hδ hδhalf
    M hM hodd w (fun p _ => hh _)
  have hsecond := signed_square_constant_bound_Z S n (by omega) hZ hL hH
    M hM w (fun p _ => hh _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
  calc
    _ ≤ (2 / L) * (weightedSum M (-1) E w +
        weightedSum M (-1) (fun _ => average ε) w) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hsplit) (by positivity)
    _ = (2 / L) * weightedSum M (-1) E w +
        (2 / L) * weightedSum M (-1) (fun _ => average ε) w := by ring
    _ ≤ _ := add_le_add hfirst hsecond

/-- The actual signed square sum has the same square-root support cutoff
as the unsigned term; the mean root sign does not affect this exact identity. -/
theorem signedSquareContribution_eq_squareBases {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) {L s : ℝ} (hL : 0 < L) (h : ℝ → ℂ)
    (hsupp : Function.support h ⊆ Set.Icc (-s) s) (a : ι → ℕ → ℂ) :
    signedSquareContribution ε L h a (primeBases L s) =
      signedSquareContribution ε L h a (squareBases L s) := by
  unfold signedSquareContribution squareBases
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hsq : (p : ℝ) ^ 2 ≤ Real.exp (s * L)
  · simp only [hsq, if_true]
  · have hz : h (2 * Real.log p / L) = 0 := by
      by_contra hn
      have hprime := (Finset.mem_filter.mp hp).2.1
      exact hsq (PrimePowerSupport.supported_prime_power_le hL hsupp
        hprime.pos (j := 2) (by simpa only [Nat.cast_ofNat] using hn))
    simp only [hsq, if_false, hz, mul_zero]

/-- Equation (116) for the literal full prime box and the actual Schwartz
test, with its cutoff and all test-value bounds derived internally. -/
theorem signedSquareContribution_bound_support
    (S : SignedSieve.SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 8 ≤ n) {L s δ : ℝ}
    (hL : 0 < L) (hs : 0 ≤ s) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (h : SchwartzMap ℝ ℂ) (hsupp : Function.support h ⊆ Set.Icc (-s) s) :
    ‖((2 / L : ℝ) : ℂ) * signedSquareContribution
      (fun f => (S.rootNumber (2 ^ n) f : ℂ)) L h
      (S.unsigned.eigenvalues (2 ^ n)) (primeBases L s)‖ ≤
      (2 * squareTraceConstant δ * ‖h.toBoundedContinuousFunction‖ * Real.log 4 / L) *
        (((2 : ℝ) ^ n) ^ (-1 + δ) *
            (Real.sqrt (Real.exp (s * L))) ^ (1 + 2 * δ) +
          (1 + 1 / (2 * δ)) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ) + δ) *
            (Real.sqrt (Real.exp (s * L))) ^ (2 * δ)) +
      (16 * ‖h.toBoundedContinuousFunction‖ * Real.log 4 *
          (1 + Real.log (Real.sqrt (Real.exp (s * L))))) /
        (L * ((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) := by
  rw [signedSquareContribution_eq_squareBases _ hL h hsupp]
  have hZ : 1 ≤ Real.sqrt (Real.exp (s * L)) := by
    apply Real.one_le_sqrt.mpr
    exact Real.one_le_exp_iff.mpr (mul_nonneg hs hL.le)
  exact signedSquareContribution_bound_Z S n hn hZ hL (norm_nonneg _) hδ hδhalf
    (squareBases L s) (squareBases_subset_primesLE L s)
    (fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2)
    h (fun x => h.toBoundedContinuousFunction.norm_coe_le_norm x)

end DepthAspect.SignedDensity
