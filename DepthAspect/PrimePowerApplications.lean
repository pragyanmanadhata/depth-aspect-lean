import DepthAspect.ChebyshevWeights
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Assembly of the cusp and square-index prime estimates

The pointwise trace bounds remain explicit inputs. All summation, power,
normalization, and logarithmic estimates use the actual finite prime sets
and the proved Chebyshev weights in `ChebyshevWeights`.
-/
namespace DepthAspect.PrimePowerApplications

open ChebyshevWeights
open scoped BigOperators

/-- A prime sum with a real power weight. The bounded factor `w p` may be
`h(log p/L)` or `h(2 log p/L)`. -/
noncomputable def weightedSum (M : Finset ℕ) (v : ℝ) (E w : ℕ → ℂ) : ℝ :=
  ∑ p ∈ M, Real.log p * (p : ℝ) ^ v * ‖E p‖ * ‖w p‖

/-- The square-index weight is exactly `log p / p`, as displayed in (48)--(49). -/
theorem weightedSum_neg_one (M : Finset ℕ) (E w : ℕ → ℂ) :
    weightedSum M (-1) E w =
      ∑ p ∈ M, Real.log p / (p : ℝ) * ‖E p‖ * ‖w p‖ := by
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- The prime-index weight is exactly `log p / √p`, as displayed in (46). -/
theorem weightedSum_neg_half (M : Finset ℕ) (E w : ℕ → ℂ) :
    weightedSum M (-(1 / 2 : ℝ)) E w =
      ∑ p ∈ M, Real.log p / Real.sqrt (p : ℝ) * ‖E p‖ * ‖w p‖ := by
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p), ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- Sum a pointwise two-power trace majorant over an actual prime subset. -/
theorem weightedSum_two_power_bound {Z A B H a b v : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (E w : ℕ → ℂ)
    (hE : ∀ p ∈ M, ‖E p‖ ≤ A * (p : ℝ) ^ a + B * (p : ℝ) ^ b)
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    weightedSum M v E w ≤
      H * (A * primePowerSum Z (a + v) + B * primePowerSum Z (b + v)) := by
  have hterm : ∀ p ∈ M,
      Real.log p * (p : ℝ) ^ v * ‖E p‖ * ‖w p‖ ≤
      H * (A * ((p : ℝ) ^ (a + v) * Real.log p) +
        B * ((p : ℝ) ^ (b + v) * Real.log p)) := by
    intro p hp
    have hpprime := (Nat.mem_primesLE.mp (hM hp)).2
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpprime.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    calc
      _ ≤ (Real.log p * (p : ℝ) ^ v) *
          (A * (p : ℝ) ^ a + B * (p : ℝ) ^ b) * H := by
        apply mul_le_mul
          (mul_le_mul_of_nonneg_left (hE p hp) (mul_nonneg hlog (Real.rpow_nonneg hp0.le v)))
          (hw p hp) (norm_nonneg _) (by positivity)
      _ = _ := by rw [Real.rpow_add hp0, Real.rpow_add hp0]; ring
  have hs : weightedSum M v E w ≤
      H * (A * (∑ p ∈ M, (p : ℝ) ^ (a + v) * Real.log p) +
        B * (∑ p ∈ M, (p : ℝ) ^ (b + v) * Real.log p)) := by
    unfold weightedSum
    calc
      _ ≤ ∑ p ∈ M, H * (A * ((p : ℝ) ^ (a + v) * Real.log p) +
          B * ((p : ℝ) ^ (b + v) * Real.log p)) := Finset.sum_le_sum hterm
      _ = _ := by simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  exact hs.trans (mul_le_mul_of_nonneg_left
    (add_le_add
      (mul_le_mul_of_nonneg_left (primePowerSum_subset Z (a + v) M hM) hA)
      (mul_le_mul_of_nonneg_left (primePowerSum_subset Z (b + v) M hM) hB)) hH)

/-- The single-power version. -/
theorem weightedSum_power_bound {Z A H a v : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (E w : ℕ → ℂ)
    (hE : ∀ p ∈ M, ‖E p‖ ≤ A * (p : ℝ) ^ a)
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    weightedSum M v E w ≤ H * A * primePowerSum Z (a + v) := by
  have h := weightedSum_two_power_bound (B := 0) (b := 0) (v := v) hA (by norm_num) hH
    M hM E w (by simpa using hE) hw
  simpa only [zero_mul, add_zero, mul_assoc] using h

/-- Cusp estimate (46). The real parameter `k≥2` includes every allowed
integral weight. The conclusion has an explicit constant independent of X. -/
theorem cusp_prime_sum_bound {X N L k K H s : ℝ}
    (hX : 1 ≤ X) (hN : 0 < N) (hL : 1 ≤ L) (hk : 2 ≤ k)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (_hs : 0 ≤ s) (hlog : Real.log X ≤ s * L)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊X⌋₊) (E w : ℕ → ℂ)
    (hE : ∀ p ∈ M, ‖E p‖ ≤ K * N ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-(k - 1) / 2))
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-(1 / 2 : ℝ)) E w ≤
      2 * K * H * Real.log 4 * (1 + s) * N ^ (-(1 / 2 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hA : 0 ≤ K * N ^ (-(1 / 2 : ℝ)) := mul_nonneg hK (Real.rpow_nonneg hN.le _)
  have hb := weightedSum_power_bound (v := -(1 / 2 : ℝ)) hA hH M hM E w hE hw
  have he : -(k - 1) / 2 + -(1 / 2 : ℝ) = -k / 2 := by ring
  rw [he] at hb
  have hsum : primePowerSum X (-k / 2) ≤ Real.log 4 * (1 + Real.log X) :=
    (primePowerSum_mono_exponent X (by linarith : -k / 2 ≤ -1)).trans
      (primePowerSum_harmonic hX)
  have ht := mul_le_mul_of_nonneg_left
    (hb.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hH hA)))
    (by positivity : 0 ≤ 2 / L)
  have hl : (1 + Real.log X) / L ≤ 1 + s := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  have hc : 0 ≤ 2 * K * H * Real.log 4 * N ^ (-(1 / 2 : ℝ)) := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  calc
    _ ≤ (2 * K * H * Real.log 4 * N ^ (-(1 / 2 : ℝ))) *
        ((1 + Real.log X) / L) := by
      calc
        _ ≤ (2 / L) * (H * (K * N ^ (-(1 / 2 : ℝ))) *
            (Real.log 4 * (1 + Real.log X))) := ht
        _ = _ := by ring
    _ ≤ (2 * K * H * Real.log 4 * N ^ (-(1 / 2 : ℝ))) * (1 + s) :=
      mul_le_mul_of_nonneg_left hl hc
    _ = _ := by ring

/-- The cusp-square estimate in (49), from the pointwise constant bound (32). -/
theorem cusp_square_sum_bound {Z N L K H s : ℝ}
    (hZ : 1 ≤ Z) (hN : 0 < N) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (_hs : 0 ≤ s) (hlog : Real.log Z ≤ s * L)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (E w : ℕ → ℂ)
    (hE : ∀ p ∈ M, ‖E p‖ ≤ K * N ^ (-(1 / 2 : ℝ)))
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1) E w ≤
      2 * K * H * Real.log 4 * (1 + s) * N ^ (-(1 / 2 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hA : 0 ≤ K * N ^ (-(1 / 2 : ℝ)) := mul_nonneg hK (Real.rpow_nonneg hN.le _)
  have hb := weightedSum_power_bound (a := 0) (v := -1) hA hH M hM E w
    (by simpa using hE) hw
  simp only [zero_add] at hb
  have ht := mul_le_mul_of_nonneg_left
    (hb.trans (mul_le_mul_of_nonneg_left (primePowerSum_harmonic hZ) (mul_nonneg hH hA)))
    (by positivity : 0 ≤ 2 / L)
  have hl : (1 + Real.log Z) / L ≤ 1 + s := by
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  have hc : 0 ≤ 2 * K * H * Real.log 4 * N ^ (-(1 / 2 : ℝ)) := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  calc
    _ ≤ (2 * K * H * Real.log 4 * N ^ (-(1 / 2 : ℝ))) *
        ((1 + Real.log Z) / L) := by
      calc
        _ ≤ (2 / L) * (H * (K * N ^ (-(1 / 2 : ℝ))) *
            (Real.log 4 * (1 + Real.log Z))) := ht
        _ = _ := by ring
    _ ≤ (2 * K * H * Real.log 4 * N ^ (-(1 / 2 : ℝ))) * (1 + s) :=
      mul_le_mul_of_nonneg_left hl hc
    _ = _ := by ring

/-- The scalar-square estimate in (49). Taking `E p=cN/p`, with `|cN|≤2`,
supplies the displayed pointwise hypothesis. -/
theorem scalar_square_sum_bound {Z L H : ℝ} (hZ : 1 ≤ Z) (hL : 0 < L) (hH : 0 ≤ H)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (E w : ℕ → ℂ)
    (hE : ∀ p ∈ M, ‖E p‖ ≤ 2 * (p : ℝ) ^ (-1 : ℝ))
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1) E w ≤ 8 * H * Real.log 4 / L := by
  have hb := weightedSum_power_bound (a := -1) (v := -1) (by norm_num : (0 : ℝ) ≤ 2)
    hH M hM E w hE hw
  norm_num only [show (-1 : ℝ) + -1 = -2 by norm_num] at hb
  have ht := mul_le_mul_of_nonneg_left
    (hb.trans (mul_le_mul_of_nonneg_left (primePowerSum_square_denominator hZ) (by positivity)))
    (by positivity : 0 ≤ 2 / L)
  calc
    _ ≤ (2 / L) * (H * 2 * (2 * Real.log 4)) := ht
    _ = _ := by ring

/-- The explicit constant stated after equation (50). -/
noncomputable def squareConstant (K δ : ℝ) : ℝ :=
  256 * K * Real.log 4 + 8 * K * Real.log 4 * (1 + 1 / (2 * δ))

/-- Assemble (40) and the two proved Chebyshev weights into (48), initially
using the prime endpoint `Z`. -/
theorem elliptic_square_sum_bound_Z {Z N L K H δ : ℝ}
    (hZ : 1 ≤ Z) (hN : 0 < N) (hL : 0 < L)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Z⌋₊) (E w : ℕ → ℂ)
    (hE : ∀ p ∈ M, ‖E p‖ ≤ K * N ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (2 * δ) *
      (128 * (p : ℝ) / N + 4))
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1) E w ≤ squareConstant K δ * H / L *
      (N ^ (-(3 / 2 : ℝ)) * Z ^ (1 + 2 * δ) +
        N ^ (-(1 / 2 : ℝ)) * Z ^ (2 * δ)) := by
  let A := 128 * K * N ^ (-(1 / 2 : ℝ)) / N
  let B := 4 * K * N ^ (-(1 / 2 : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hE' : ∀ p ∈ M, ‖E p‖ ≤
      A * (p : ℝ) ^ (2 * δ + 1) + B * (p : ℝ) ^ (2 * δ) := by
    intro p hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp (hM hp)).2.pos
    calc
      _ ≤ K * N ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (2 * δ) *
          (128 * (p : ℝ) / N + 4) := hE p hp
      _ = _ := by
        rw [Real.rpow_add hp0, Real.rpow_one]
        dsimp [A, B]
        ring
  have hb := weightedSum_two_power_bound (v := -1) hA hB hH M hM E w hE' hw
  rw [show (2 * δ + 1) + (-1) = 2 * δ by ring,
    show 2 * δ + (-1) = 2 * δ - 1 by ring] at hb
  have hp := primePowerSum_nonnegative_exponent hZ (by linarith : 0 ≤ 2 * δ)
  have hm := primePowerSum_negative_exponent_all hZ (by linarith : 0 < 2 * δ)
    (by linarith : 2 * δ < 1)
  have ht := mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hp hA) (mul_le_mul_of_nonneg_left hm hB)) hH))
    (by positivity : 0 ≤ 2 / L)
  have hn : N ^ (-(1 / 2 : ℝ)) / N = N ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN]
    norm_num
  have heq : (2 / L) * (H * (A * (Real.log 4 * Z ^ (1 + 2 * δ)) +
      B * (Real.log 4 * (1 + 1 / (2 * δ)) * Z ^ (2 * δ)))) =
      H / L * ((256 * K * Real.log 4) *
        ((N ^ (-(1 / 2 : ℝ)) / N) * Z ^ (1 + 2 * δ)) +
      (8 * K * Real.log 4 * (1 + 1 / (2 * δ))) *
        (N ^ (-(1 / 2 : ℝ)) * Z ^ (2 * δ))) := by
    dsimp [A, B]
    ring
  rw [heq, hn] at ht
  have hfirst : 0 ≤ 256 * K * Real.log 4 := by positivity
  have hsecond : 0 ≤ 8 * K * Real.log 4 * (1 + 1 / (2 * δ)) := by positivity
  have hu : 0 ≤ N ^ (-(3 / 2 : ℝ)) * Z ^ (1 + 2 * δ) := by positivity
  have hv : 0 ≤ N ^ (-(1 / 2 : ℝ)) * Z ^ (2 * δ) := by positivity
  have hcombine :
      (256 * K * Real.log 4) * (N ^ (-(3 / 2 : ℝ)) * Z ^ (1 + 2 * δ)) +
      (8 * K * Real.log 4 * (1 + 1 / (2 * δ))) * (N ^ (-(1 / 2 : ℝ)) * Z ^ (2 * δ)) ≤
      squareConstant K δ * (N ^ (-(3 / 2 : ℝ)) * Z ^ (1 + 2 * δ) +
        N ^ (-(1 / 2 : ℝ)) * Z ^ (2 * δ)) := by
    dsimp [squareConstant]
    nlinarith [mul_nonneg hfirst hv, mul_nonneg hsecond hu]
  calc
    _ ≤ _ := ht
    _ ≤ H / L * (squareConstant K δ *
        (N ^ (-(3 / 2 : ℝ)) * Z ^ (1 + 2 * δ) +
          N ^ (-(1 / 2 : ℝ)) * Z ^ (2 * δ))) :=
      mul_le_mul_of_nonneg_left hcombine (by positivity)
    _ = _ := by ring

/-- Equation (48) in the paper's endpoint `X`, with `Z=√X`. -/
theorem elliptic_square_sum_bound {X N L K H δ : ℝ}
    (hX : 1 ≤ X) (hN : 0 < N) (hL : 0 < L)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (M : Finset ℕ) (hM : M ⊆ Nat.primesLE ⌊Real.sqrt X⌋₊) (E w : ℕ → ℂ)
    (hE : ∀ p ∈ M, ‖E p‖ ≤ K * N ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (2 * δ) *
      (128 * (p : ℝ) / N + 4))
    (hw : ∀ p ∈ M, ‖w p‖ ≤ H) :
    (2 / L) * weightedSum M (-1) E w ≤ squareConstant K δ * H / L *
      (N ^ (-(3 / 2 : ℝ)) * X ^ (1 / 2 + δ) +
        N ^ (-(1 / 2 : ℝ)) * X ^ δ) := by
  have hX0 : 0 ≤ X := by linarith
  have hb := elliptic_square_sum_bound_Z (Real.one_le_sqrt.mpr hX) hN hL hK hH hδ hδhalf
    M hM E w hE hw
  have hp : Real.sqrt X ^ (1 + 2 * δ) = X ^ (1 / 2 + δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0]
    congr 1
    ring
  have hq : Real.sqrt X ^ (2 * δ) = X ^ δ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0]
    congr 1
    ring
  simpa only [hp, hq] using hb

end DepthAspect.PrimePowerApplications
