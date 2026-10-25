import DepthAspect.CoefficientPrimeAverages
import DepthAspect.SmoothedPowerSum
import DepthAspect.FiniteSmoothedAssembly

/-!
# Summing the actual coefficient-wise prime errors

The modulus in (81) is bounded by 8m². Its logarithm and the actual Fourier
norm are bounded before summing. This supplies the smoothed x-power in (103)
from the real coefficient-wise GRH error, rather than taking that summed
estimate as an input.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.CoefficientErrorMajorant
open GlobalResidueCoefficient CharacterPrimeAverages

 theorem modulus_le (m : ℕ) (hm : 0 < m) : modulus m ≤ 8 * m ^ 2 := by
  exact Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul 8 (m ^ 2))

 theorem log_modulus_le {m : ℕ} (hm : 0 < m) {B : ℝ} (hB : 2 ≤ B) :
    Real.log (2 * (modulus m : ℝ) * B) ≤ 4 * Real.log (2 * B * m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq0 : 0 < modulus m := Nat.pos_of_ne_zero (by
    unfold modulus
    exact Nat.lcm_ne_zero (by norm_num) (pow_ne_zero _ hm.ne'))
  have hq : (modulus m : ℝ) ≤ 8 * (m : ℝ) ^ 2 := by exact_mod_cast modulus_le m hm
  have harg : 2 * (modulus m : ℝ) * B ≤ (2 * B * m) ^ 4 := by
    have hB2 : 1 ≤ B ^ 2 := by nlinarith
    have hm2 : 1 ≤ (m : ℝ) ^ 2 := by nlinarith
    have hBm : 1 ≤ B ^ 2 * (m : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hB2 hm2
    have hB3 : B ≤ B ^ 4 := by
      calc B ≤ B ^ 2 := by nlinarith
           _ ≤ (B ^ 2) ^ 2 := by nlinarith
           _ = B ^ 4 := by ring
    have hm4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by nlinarith
    have hprod := mul_le_mul hB3 hm4 (by positivity) (by positivity)
    have hqB := mul_le_mul_of_nonneg_right hq (by linarith : 0 ≤ B)
    nlinarith
  calc
    _ ≤ Real.log ((2 * B * m) ^ 4) := Real.log_le_log (by positivity) harg
    _ = _ := by rw [Real.log_pow]; norm_num

/-- A uniform coefficient independent of m, B and the test function. -/
def envelopeConstant (C : ℝ) : ℝ :=
  16 * (C + 3 / Real.log 4) + 2 / Real.log 4 ^ 2

 theorem envelopeConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ envelopeConstant C := by
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold envelopeConstant
  positivity

 theorem envelope_le {m : ℕ} (hm : 0 < m) {B C : ℝ} (hB : 2 ≤ B) (hC : 0 ≤ C) :
    envelope (C + 3 / Real.log 4) B (modulus m) ≤
      envelopeConstant C * Real.sqrt B * Real.log (2 * B * m) ^ 2 := by
  have hq1 : (1 : ℝ) ≤ modulus m := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.lcm_ne_zero (by norm_num) (pow_ne_zero _ hm.ne'))
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogq0 : 0 ≤ Real.log (2 * (modulus m : ℝ) * B) :=
    Real.log_nonneg (by nlinarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog : Real.log 4 ≤ Real.log (2 * B * m) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hsqrt : 1 ≤ Real.sqrt B := (Real.le_sqrt (by norm_num) (by linarith : 0 ≤ B)).mpr (by nlinarith)
  have hC' : 0 ≤ C + 3 / Real.log 4 := by positivity
  have hsq : Real.log (2 * (modulus m : ℝ) * B) ^ 2 ≤
      16 * Real.log (2 * B * m) ^ 2 := by
    have h := pow_le_pow_left₀ hlogq0 (log_modulus_le hm hB) 2
    nlinarith
  have hsmall : 2 ≤ (2 / Real.log 4 ^ 2) * Real.sqrt B * Real.log (2 * B * m) ^ 2 := by
    have hs : Real.log 4 ^ 2 ≤ Real.log (2 * B * m) ^ 2 := by nlinarith
    have hs' : Real.log 4 ^ 2 ≤ Real.sqrt B * Real.log (2 * B * m) ^ 2 :=
      hs.trans (le_mul_of_one_le_left (sq_nonneg _) hsqrt)
    have h := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ 2 / Real.log 4 ^ 2)
    have heq : 2 / Real.log 4 ^ 2 * Real.log 4 ^ 2 = 2 := by field_simp
    rw [heq] at h
    simpa only [mul_assoc] using h
  have hlarge := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg hC' (Real.sqrt_nonneg B))
  unfold envelope envelopeConstant
  nlinarith

/-- The summed coefficient error constant; δ is the divisor-function loss. -/
def constant (δ C : ℝ) : ℝ :=
  8 * DivisorGrowth.boundConstant δ * envelopeConstant C

 theorem constant_nonneg {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) : 0 ≤ constant δ C := by
  unfold constant
  exact mul_nonneg (by have := DivisorGrowth.boundConstant_pos hδ; positivity)
    (envelopeConstant_nonneg hC)

/-- A coefficient-wise numerical majorant with all modulus/Fourier factors
eliminated. Its only variable m dependence is the printed power/logarithm. -/
theorem coefficient_majorant {m : ℕ} (hm : 0 < m)
    {δ C B M V : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hB : 2 ≤ B)
    (hM : 0 ≤ M) (hV : 0 ≤ V) :
    (2 * M + V) * GlobalFourierBound.localProduct m *
      envelope (C + 3 / Real.log 4) B (modulus m) ≤
        constant δ C * (M + V) * Real.sqrt B *
          (m : ℝ) ^ (1 / 2 + δ) * Real.log (2 * B * m) ^ 2 := by
  have hlocal : 0 ≤ GlobalFourierBound.localProduct m := by
    unfold GlobalFourierBound.localProduct
    positivity
  calc
    _ ≤ (2 * (M + V)) *
      ((4 * DivisorGrowth.boundConstant δ) * (m : ℝ) ^ (1 / 2 + δ)) *
        (envelopeConstant C * Real.sqrt B * Real.log (2 * B * m) ^ 2) := by
      have henv : 0 ≤ envelope (C + 3 / Real.log 4) B (modulus m) := by
        have : 0 < Real.log 4 := Real.log_pos (by norm_num)
        unfold envelope
        positivity
      have hupper : 0 ≤ 2 * (M + V) := by positivity
      have hlocalbound := GlobalFourierBound.localProduct_subpower hδ m hm
      have hproduct := mul_le_mul
        (show 2 * M + V ≤ 2 * (M + V) by linarith)
        hlocalbound hlocal hupper
      exact mul_le_mul hproduct (envelope_le hm hB hC) henv
        (mul_nonneg hupper (hlocal.trans hlocalbound))
    _ = _ := by unfold constant; ring

/-- The exact exponentially damped coefficient-error majorant. -/
def term (δ C B M V x : ℝ) (n : ℕ) : ℝ :=
  FiniteSmoothedAssembly.weight x n *
    (constant δ C * (M + V) * Real.sqrt B *
      ((n + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) * Real.log (2 * B * (n + 1 : ℕ)) ^ 2)

 theorem term_eq (δ C B M V x : ℝ) (n : ℕ) : term δ C B M V x n =
    (constant δ C * (M + V) * Real.sqrt B) *
      (SmoothedPowerSum.term (1 / 2 + δ) x n * Real.log (2 * B * (n + 1 : ℕ)) ^ 2) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  unfold term FiniteSmoothedAssembly.weight SmoothedPowerSum.term
  rw [Real.rpow_sub hn, Real.rpow_one]
  ring

 theorem term_summable {δ C B M V x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hB : 2 ≤ B) (hx : 0 < x) : Summable (term δ C B M V x) := by
  have hs := (SmoothedPowerSum.log_weighted_summable
    (a := 1 / 2 + δ) (δ := δ) (B := B) (x := x)
    (by linarith : 0 < 1 / 2 + δ) hδ (by linarith) (by linarith) hx).mul_left
      (constant δ C * (M + V) * Real.sqrt B)
  exact hs.congr (fun n => (term_eq δ C B M V x n).symm)

/-- The middle error in (103), with its actual x^(1/2+2δ) and B^δ factors.
Taking δ=η/2 gives the exponents printed in the paper. -/
theorem term_sum_bound {δ C B M V x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4)
    (hC : 0 ≤ C) (hB : 2 ≤ B) (hM : 0 ≤ M) (hV : 0 ≤ V) (hx : 1 ≤ x) :
    (∑' n : ℕ, term δ C B M V x n) ≤
      (constant δ C * ((4 / δ ^ 2) * 2 ^ δ *
        (1 + Real.Gamma (1 / 2 + δ + δ)))) *
          (M + V) * Real.sqrt B * B ^ δ * x ^ (1 / 2 + δ + δ) := by
  simp_rw [term_eq]
  rw [tsum_mul_left]
  have h := mul_le_mul_of_nonneg_left
    (SmoothedPowerSum.log_weighted_sum_bound
      (a := 1 / 2 + δ) (δ := δ) (B := B) (x := x)
      (by linarith : 0 < 1 / 2 + δ) hδ (by linarith) (by linarith) hx)
    (by have := constant_nonneg hδ hC; positivity :
      0 ≤ constant δ C * (M + V) * Real.sqrt B)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end DepthAspect.CoefficientErrorMajorant
