import DepthAspect.SignedPrimeDensity
import DepthAspect.SignedSquareDensity

/-!
# Uniform inverse-logarithm bounds for the signed prime terms

All Fourier endpoint powers are rewritten exactly before applying the
negative level exponents. Constants depend on the fixed weight, test and
chosen support/loss parameters, and precede every spectral datum.
-/
namespace DepthAspect.SignedDensity
open MeasureTheory Set SignedSieve DirichletRH GRHConsequences BesselFirstKind
open UnsignedDensity
open scoped BigOperators SchwartzMap

/-- Exact conductor/level separation of a Fourier endpoint power. -/
theorem endpoint_product_identity {w N : ℝ} (hw : 0 < w) (hN : 0 < N)
    (s u v : ℝ) :
    N ^ u * (Real.exp (s * Real.log (w ^ 2 * N))) ^ v =
      (w ^ 2) ^ (s * v) * N ^ (u + s * v) := by
  have he : (Real.exp (s * Real.log (w ^ 2 * N))) ^ v = (w ^ 2 * N) ^ (s * v) := by
    rw [← Real.exp_mul, Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  rw [he, UnsignedExponents.level_endpoint_identity hw hN]

theorem endpoint_product_bound {w N : ℝ} (hw : 0 < w) (hN : 1 ≤ N)
    (s u v : ℝ) (he : u + s * v ≤ 0) :
    N ^ u * (Real.exp (s * Real.log (w ^ 2 * N))) ^ v ≤ (w ^ 2) ^ (s * v) := by
  rw [endpoint_product_identity hw (by linarith) s u v]
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_one_of_one_le_of_nonpos hN he) (by positivity)).trans_eq (by ring)

variable {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

theorem signed_prime_inverse_log (k : ℕ) (h : 𝓢(ℝ, ℂ))
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    (hBessel : DLMFIdentities) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (he₁ : -(1 / 2 : ℝ) + s * (1 / 4 + ε) ≤ 0)
    (he₂ : -1 + s * (3 / 4 + ε) ≤ 0)
    (hsupp : Function.support h ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (S : SignedArithmeticData k Family Full New) (n : ℕ), 8 ≤ n →
      2 ≤ Real.exp (s * conductorLog k n) →
      ‖((2 / conductorLog k n : ℝ) : ℂ) * signedPrimeContribution
        (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (conductorLog k n) h
        (S.unsigned.eigenvalues (2 ^ n)) (primeBases (conductorLog k n) s) -
          ∫ u in Ioi (1 : ℝ), h u‖ ≤ K / conductorLog k n := by
  obtain ⟨Cb, Cn, Cl, hCb, hCn, hCl, hb⟩ :=
    signed_prime_density_bound
    (Family := Family) (Full := Full) (New := New) k h hRH cited hBessel hs hε hsupp
  let w : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  have hw : 2 ≤ w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith
  let W : ℝ := (w ^ 2) ^ (s * (1 / 4 + ε)) + (w ^ 2) ^ (s * (3 / 4 + ε))
  let R : ℝ := Real.log (w ^ 2) + 2
  have hR : 0 ≤ R := by
    have := Real.log_nonneg (show 1 ≤ w ^ 2 by nlinarith)
    dsimp [R]
    linarith
  refine ⟨Cb * W + Cn * R + Cl, by dsimp [W]; positivity, ?_⟩
  intro S n hn hcut
  have hN := UnsignedExponents.dyadic_level_gt_one n hn
  have hL := conductorLog_pos k n
  have he₁' := endpoint_product_bound (by linarith : 0 < w) hN.le
    s (-(1 / 2 : ℝ)) (1 / 4 + ε) he₁
  have he₂' := endpoint_product_bound (by linarith : 0 < w) hN.le
    s (-1) (3 / 4 + ε) he₂
  have hR' := negative_power_le_inverse_conductor_log hN
    (show 1 ≤ w ^ 2 by nlinarith) (by norm_num : -(1 / 2 : ℝ) < 0)
  norm_num only [neg_neg, one_div_div, one_div_one] at hR'
  have ht := hb S n hn hcut
  apply ht.trans
  calc
    _ ≤ (Cb / conductorLog k n) * W + Cn * (R / conductorLog k n) + Cl / conductorLog k n := by
      refine add_le_add ?_ le_rfl
      exact add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add he₁' he₂') (by positivity))
        (mul_le_mul_of_nonneg_left hR' hCn)
    _ = _ := by ring

theorem signed_square_inverse_log (k : ℕ) (h : 𝓢(ℝ, ℂ))
    {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (he₁ : -1 + δ + s * (1 / 2 + δ) ≤ 0)
    (he₂ : -(1 / 2 : ℝ) + δ + s * δ ≤ 0)
    (hsupp : Function.support h ⊆ Icc (-s) s) :
    ∃ K ≥ 0, ∀ (S : SignedArithmeticData k Family Full New) (n : ℕ), 8 ≤ n →
      ‖((2 / conductorLog k n : ℝ) : ℂ) * signedSquareContribution
        (fun f => (S.rootNumber (2 ^ n) f : ℂ)) (conductorLog k n) h
        (S.unsigned.eigenvalues (2 ^ n)) (primeBases (conductorLog k n) s)‖ ≤
        K / conductorLog k n := by
  let w : ℝ := 2 * ((k + 1 : ℕ) : ℝ)
  let H : ℝ := ‖h.toBoundedContinuousFunction‖
  let A : ℝ := 2 * squareTraceConstant δ * H * Real.log 4
  let B : ℝ := 16 * H * Real.log 4 / (2 * (k : ℝ) + 1)
  let W : ℝ := (w ^ 2) ^ (s * (1 / 2 + δ)) +
    (1 + 1 / (2 * δ)) * (w ^ 2) ^ (s * δ)
  let R : ℝ := Real.log (w ^ 2) + 2
  have hw : 2 ≤ w := by dsimp [w]; have := Nat.cast_nonneg (α := ℝ) k; push_cast; linarith
  have hH : 0 ≤ H := norm_nonneg _
  have hA : 0 ≤ A := by have := squareTraceConstant_nonneg hδ; dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := by
    have := Real.log_nonneg (show 1 ≤ w ^ 2 by nlinarith)
    dsimp [R]
    linarith
  refine ⟨A * W + B * (1 + s / 2) * R, by dsimp [W]; positivity, ?_⟩
  intro S n hn
  let N : ℝ := (2 : ℝ) ^ n
  let L : ℝ := conductorLog k n
  let X : ℝ := Real.exp (s * L)
  have hN := UnsignedExponents.dyadic_level_gt_one n hn
  have hL : 1 ≤ L := UnsignedExponents.conductor_log_ge_one w hw n hn
  have hL0 : 0 < L := by linarith
  have hfirst : N ^ (-1 + δ) * (Real.sqrt X) ^ (1 + 2 * δ) ≤
      (w ^ 2) ^ (s * (1 / 2 + δ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Real.exp_pos _).le]
    have he : (1 / 2 : ℝ) * (1 + 2 * δ) = 1 / 2 + δ := by ring
    rw [he]
    exact endpoint_product_bound (by linarith) hN.le s (-1 + δ) (1 / 2 + δ) he₁
  have hsecond : N ^ (-(1 / 2 : ℝ) + δ) * (Real.sqrt X) ^ (2 * δ) ≤
      (w ^ 2) ^ (s * δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Real.exp_pos _).le]
    have he : (1 / 2 : ℝ) * (2 * δ) = δ := by ring
    rw [he]
    exact endpoint_product_bound (by linarith) hN.le s (-(1 / 2 : ℝ) + δ) δ he₂
  have hR' : N ^ (-(1 / 2 : ℝ)) ≤ R / L := by
    have ht := negative_power_le_inverse_conductor_log hN
      (show 1 ≤ w ^ 2 by nlinarith) (by norm_num : -(1 / 2 : ℝ) < 0)
    norm_num only [neg_neg, one_div_div, one_div_one] at ht
    exact ht
  have hlog : Real.log (Real.sqrt X) = (s / 2) * L := square_endpoint_log L s
  have hsmall : (16 * H * Real.log 4 * (1 + Real.log (Real.sqrt X))) /
      (L * ((2 * k + 1 : ℕ) : ℝ) * Real.sqrt N) ≤
        (B * (1 + s / 2) * R) / L := by
    rw [hlog]
    have hfrac : (1 + (s / 2) * L) / L ≤ 1 + s / 2 := by
      apply (div_le_iff₀ hL0).mpr
      nlinarith
    have hid : (16 * H * Real.log 4 * (1 + s / 2 * L)) /
        (L * ((2 * k + 1 : ℕ) : ℝ) * Real.sqrt N) =
        B * ((1 + s / 2 * L) / L) * N ^ (-(1 / 2 : ℝ)) := by
      dsimp [B]
      rw [Real.rpow_neg (by positivity : 0 ≤ N), ← Real.sqrt_eq_rpow]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hid]
    calc
      _ ≤ (B * (1 + s / 2)) * (R / L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hfrac hB) hR'
          (by positivity) (by positivity)
      _ = _ := by ring
  have ht := signedSquareContribution_bound_support S n hn hL0 hs hδ hδhalf h hsupp
  apply ht.trans
  have hm := add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ 1 + 1 / (2 * δ) by positivity))
  have hm' : N ^ (-1 + δ) * (Real.sqrt X) ^ (1 + 2 * δ) +
      (1 + 1 / (2 * δ)) * N ^ (-(1 / 2 : ℝ) + δ) * (Real.sqrt X) ^ (2 * δ) ≤ W := by
    simpa only [mul_assoc] using hm
  have ht' := add_le_add (mul_le_mul_of_nonneg_left hm' (by positivity : 0 ≤ A / L)) hsmall
  exact ht'.trans_eq (by ring)

/-- Explicit positive choices of both arithmetic losses for every support
strictly below 4/3. The parameters are fixed before depth and family data. -/
theorem signed_loss_parameters {s : ℝ} (hs : 0 < s) (hs' : s < 4 / 3) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧ δ < 1 / 2 ∧
      -(1 / 2 : ℝ) + s * (1 / 4 + ε) ≤ 0 ∧
      -1 + s * (3 / 4 + ε) ≤ 0 ∧
      -1 + δ + s * (1 / 2 + δ) ≤ 0 ∧
      -(1 / 2 : ℝ) + δ + s * δ ≤ 0 := by
  let ε := (4 - 3 * s) / (8 * s)
  let δ := (2 - s) / (4 * (1 + s))
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hδhalf : δ < 1 / 2 := by
    dsimp [δ]
    apply (div_lt_iff₀ (by positivity : 0 < 4 * (1 + s))).mpr
    linarith
  have he : s * ε = (4 - 3 * s) / 8 := by dsimp [ε]; field_simp [hs.ne'] <;> ring
  have hd : δ * (1 + s) = (2 - s) / 4 := by
    dsimp [δ]
    field_simp [show 1 + s ≠ 0 by linarith] <;> ring
  refine ⟨ε, δ, hε, hδ, hδhalf, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end DepthAspect.SignedDensity
