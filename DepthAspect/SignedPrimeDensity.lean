import DepthAspect.SignedHyperbolicDensity
import DepthAspect.SignedInitialBound
import DepthAspect.BoundedPrimitiveWeight

/-!
# The prime contribution to the signed density

Equations (113)--(115) are assembled with the actual spectral prime sum.
The constants are chosen before the spectral family. The retained bounds
separate the arithmetic block powers, the small lower integral and
hyperbolic terms, and the bounded-primitive inverse logarithm.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set SignedSieve DirichletRH GRHConsequences BesselFirstKind
open MurmurationArithmetic UnsignedDensity
open scoped BigOperators SchwartzMap

variable {k : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

theorem traceDimensionScale_eq_scalar (S : SignedArithmeticData k Family Full New)
    (n : ℕ) :
    traceDimensionScale k ((2 : ℝ) ^ n) (Fintype.card (Family (2 ^ n)) : ℝ) =
      MartinDimension.scalarCoefficient (2 * k + 2) n
        (fun N => (Fintype.card (Family N) : ℝ)) := by
  unfold traceDimensionScale MartinDimension.scalarCoefficient
  push_cast
  ring

/-- The actual prime-density main term, with uniform constants. This is
(113)--(115) after proving the literal finite spectral decomposition. -/
theorem signed_prime_density_bound (k : ℕ) (h : 𝓢(ℝ, ℂ))
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    (hBessel : DLMFIdentities) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hsupp : Function.support h ⊆ Icc (-s) s) :
    ∃ Cb Cn Cl : ℝ, 0 ≤ Cb ∧ 0 ≤ Cn ∧ 0 ≤ Cl ∧
      ∀ (S : SignedArithmeticData k Family Full New) (n : ℕ), 8 ≤ n →
      2 ≤ Real.exp (s * conductorLog k n) →
      ‖((2 / conductorLog k n : ℝ) : ℂ) * signedPrimeContribution
        (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (conductorLog k n) h
        (S.unsigned.eigenvalues (2 ^ n)) (primeBases (conductorLog k n) s) -
          ∫ u in Ioi (1 : ℝ), h u‖ ≤
      (Cb / conductorLog k n) *
        (((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) *
            (Real.exp (s * conductorLog k n)) ^ (1 / 4 + ε) +
          ((2 : ℝ) ^ n) ^ (-1 : ℝ) *
            (Real.exp (s * conductorLog k n)) ^ (3 / 4 + ε)) +
        Cn * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) + Cl / conductorLog k n := by
  obtain ⟨Cb₀, hCb₀, hb⟩ := signed_prime_elliptic_sum_bound
    (Family := Family) (Full := Full) (New := New) k h hRH cited hε
  obtain ⟨Ci, hCi, hi⟩ := MurmurationPrimeIntegral.prime_range_integral_error
    hBessel k Nat.prime_two
  obtain ⟨Cp, hCp, hp⟩ := BoundedPrimitiveWeight.scaled_main_term hBessel k Nat.prime_two
  let w : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  let H : ℝ := ‖h.toBoundedContinuousFunction‖
  let J : ℂ := ∫ u in Ioi (1 : ℝ), h u
  let A : ℝ := 1 - (2 : ℝ) ^ (-(1 / 4 + ε))
  let B : ℝ := 1 - (2 : ℝ) ^ (-(3 / 4 + ε))
  let E : ℝ := 2 * Cp * (∫ u : ℝ, ‖deriv h u‖) + 2 * Real.log w * H
  let CH : ℝ := 2 * (256 / (2 * (k : ℝ) + 1)) * H * Real.log 4 * (1 + s)
  have hw : 2 ≤ w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith
  have hH : 0 ≤ H := norm_nonneg _
  have hA : 0 < A := by
    dsimp [A]
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hB : 0 < B := by
    dsimp [B]
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hE : 0 ≤ E := by
    have hlog : 0 ≤ Real.log w := Real.log_nonneg (by linarith)
    have hI : 0 ≤ ∫ u : ℝ, ‖deriv h u‖ := integral_nonneg (fun _ => norm_nonneg _)
    dsimp [E]
    positivity
  have hCH : 0 ≤ CH := by dsimp [CH]; positivity
  let Cb : ℝ := 2 * Cb₀ * (1 / A + 1 / B)
  let Cn : ℝ := CH + 4 * Ci * H + (8 / (2 * (k : ℝ) + 1)) * ‖J‖
  refine ⟨Cb, Cn, 2 * E, by dsimp [Cb]; positivity,
    by dsimp [Cn]; positivity, by positivity, ?_⟩
  intro S n hn hcut
  let N : ℝ := (2 : ℝ) ^ n
  let L : ℝ := conductorLog k n
  let X : ℝ := Real.exp (s * L)
  let d : ℝ := Fintype.card (Family (2 ^ n))
  let c : ℝ := traceDimensionScale k N d
  let Q : ℂ := ∫ u in (2 : ℝ)..X, (M k 2 (u / N) / u) • h (Real.log u / L)
  let I : ℂ := ∫ v in Ioi (0 : ℝ), MurmurationPrimeIntegral.weightedIntegrand k 2 N L h v
  let R : ℝ := N ^ (-(1 / 2 : ℝ))
  let U : ℝ := R * X ^ (1 / 4 + ε)
  let V : ℝ := N ^ (-1 : ℝ) * X ^ (3 / 4 + ε)
  have hN : 0 < N := by dsimp [N]; positivity
  have hN2 : 2 ≤ N := by
    dsimp [N]
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ n by omega)
  have hL : 1 ≤ L := UnsignedExponents.conductor_log_ge_one w hw n hn
  have hL0 : 0 < L := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hc := signed_traceDimensionScale_bounds S n (by omega)
  change 0 ≤ c ∧ c ≤ 2 at hc
  have hce : |c - 1| ≤ (8 / (2 * (k : ℝ) + 1)) * R := by
    have he := MartinDimension.scalarCoefficient_error (2 * k + 2) n
      (by omega) hn (fun N => (Fintype.card (Family N) : ℝ)) S.unsigned.dimension_formula
    rw [← traceDimensionScale_eq_scalar S n] at he
    convert he using 1 <;> dsimp [R, N] <;> push_cast <;> ring
  have hQ : ‖Q - I‖ ≤ Ci * H * R := hi N L s hN2 hL0 hcut h hsupp
  have hI : ‖(2 / L : ℝ) • I - J‖ ≤ E / L := by
    have he := hp w N s (by linarith) hN hL0 h hsupp
    exact he
  have hEL : ‖ellipticPrimeBlock S n L s 2 X h - c • Q‖ ≤ Cb₀ * (U / A + V / B) := by
    have he := hb S n (by omega) L s hL hcut
    have heq : (∫ u in (2 : ℝ)..X, (c * M k 2 (u / N) / u) • h (Real.log u / L)) = c • Q := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro u hu
      change (c * M k 2 (u / N) / u) • h (Real.log u / L) =
        c • ((M k 2 (u / N) / u) • h (Real.log u / L))
      rw [smul_smul]
      congr 1
      ring
    change ‖ellipticPrimeBlock S n L s 2 X h -
      (∫ u in (2 : ℝ)..X, (c * M k 2 (u / N) / u) • h (Real.log u / L))‖ ≤ _ at he
    rw [heq] at he
    exact he
  have hHB := hyperbolicPrimeSum_bound S n (by omega) hL hs h
  have hid : ((2 / L : ℝ) : ℂ) * signedPrimeContribution
      (fun f => (S.rootNumber (2 ^ n) f : ℂ)) L h
      (S.unsigned.eigenvalues (2 ^ n)) (primeBases L s) - J =
      (2 / L : ℝ) • (ellipticPrimeBlock S n L s 2 X h - c • Q) +
      ((2 / L : ℝ) : ℂ) * hyperbolicPrimeSum S n L s h +
      ((2 / L) * c : ℝ) • (Q - I) +
      c • ((2 / L : ℝ) • I - J) + (c - 1) • J := by
    rw [signedPrimeContribution_eq_elliptic_add_hyperbolic S n L s h]
    simp only [Complex.real_smul]
    push_cast
    ring
  have hb1 : ‖(2 / L : ℝ) • (ellipticPrimeBlock S n L s 2 X h - c • Q)‖ ≤
      (Cb / L) * (U + V) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
    apply (mul_le_mul_of_nonneg_left hEL (by positivity)).trans
    have hm : U / A + V / B ≤ (1 / A + 1 / B) * (U + V) := by
      have hcross : 0 ≤ U / B + V / A := by positivity
      have hid : (1 / A + 1 / B) * (U + V) - (U / A + V / B) = U / B + V / A := by ring
      linarith
    have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (2 / L) * Cb₀)
    calc
      (2 / L) * (Cb₀ * (U / A + V / B)) =
          ((2 / L) * Cb₀) * (U / A + V / B) := by ring
      _ ≤ ((2 / L) * Cb₀) * ((1 / A + 1 / B) * (U + V)) := hh
      _ = (Cb / L) * (U + V) := by dsimp [Cb]; ring
  have hb2 : ‖((2 / L : ℝ) : ℂ) * hyperbolicPrimeSum S n L s h‖ ≤ CH * R := hHB
  have hb3 : ‖((2 / L) * c : ℝ) • (Q - I)‖ ≤ (4 * Ci * H) * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity : 0 ≤ 2 / L) hc.1)]
    have hf : 2 / L * c ≤ 4 := by
      have ht : 2 / L ≤ 2 := (div_le_iff₀ hL0).mpr (by linarith)
      nlinarith
    exact (mul_le_mul hf hQ (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hb4 : ‖c • ((2 / L : ℝ) • I - J)‖ ≤ 2 * E / L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1]
    exact (mul_le_mul hc.2 hI (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hb5 : ‖(c - 1) • J‖ ≤ ((8 / (2 * (k : ℝ) + 1)) * ‖J‖) * R := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hce (norm_nonneg _)).trans_eq (by ring)
  rw [hid]
  have hnorm := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hb3)) hb4)) hb5)
  exact hnorm.trans_eq (by dsimp [Cn, U, V, R, N, X, L]; ring)

end DepthAspect.SignedDensity
