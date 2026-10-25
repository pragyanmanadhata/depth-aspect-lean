import DepthAspect.PrimePairBound
import Mathlib.Analysis.Complex.Basic

/-!
# The finite trace-index assembly in equations (112) and (141)

The pointwise arithmetic prime-average theorem remains an explicit input.
This module proves the actual finite index count, the use of the variation
bound, and all powers and constants in passing to the complete block error.
In particular, neither (111)'s cardinal estimate nor (141) is a premise.
-/
namespace DepthAspect.SignedBlockAssembly

open scoped BigOperators

/-- Every finite set of the actual eligible integer indices has the bound
in the second line of (111). -/
theorem trace_index_card_bound {B N : ℝ} (hB : 0 < B) (hN : 0 < N)
    (S : Finset ℤ) (hS : ∀ r ∈ S, N * (r : ℝ) ^ 2 / 16 < 2 * B) :
    (S.card : ℝ) ≤ 1 + 8 * Real.sqrt (2 * B / N) := by
  let R : ℕ := ⌊4 * Real.sqrt (2 * B / N)⌋₊
  have hsub : S ⊆ Finset.Icc (-(R : ℤ)) (R : ℤ) := by
    intro r hr
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * B / N)
    have hroot : |(r : ℝ)| ≤ 4 * Real.sqrt (2 * B / N) := by
      have hr' := hS r hr
      have hrdiv : (r : ℝ) ^ 2 ≤ 32 * B / N :=
        (le_div_iff₀ hN).mpr (by nlinarith)
      rw [show 32 * B / N = 16 * (2 * B / N) by ring] at hrdiv
      have hrsq : (r : ℝ) ^ 2 ≤ (4 * Real.sqrt (2 * B / N)) ^ 2 := by
        nlinarith
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hrsq)
    have hnat : r.natAbs ≤ R := by
      apply Nat.le_floor
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hroot
    have hint : (r.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hnat
    rw [Int.natCast_natAbs] at hint
    exact Finset.mem_Icc.mpr (abs_le.mp hint)
  have hc : S.card ≤ 2 * R + 1 := by
    have hh := Finset.card_le_card hsub
    rw [Int.card_Icc] at hh
    have he : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
    rwa [he] at hh
  have hcR : (S.card : ℝ) ≤ 2 * (R : ℝ) + 1 := by exact_mod_cast hc
  have hR : (R : ℝ) ≤ 4 * Real.sqrt (2 * B / N) := Nat.floor_le (by positivity)
  linarith

/-- The geometric mean in the prime-averaging estimate is controlled by
the proved/available variation majorant `M+V`. -/
theorem geometric_variation_bound {M V H B : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hH : 0 ≤ H) (hB : 0 < B) (hvar : M + V ≤ H * B ^ (-(1 / 2 : ℝ))) :
    Real.sqrt (M * (M + V)) ≤ H * B ^ (-(1 / 2 : ℝ)) := by
  have hMV : 0 ≤ M + V := by linarith
  calc
    _ ≤ Real.sqrt ((M + V) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = M + V := Real.sqrt_sq hMV
    _ ≤ _ := hvar

/-- Finite sum form of the conditional block bound, with a general
per-index exponent. This also exposes the effect of improving that exponent. -/
theorem finite_block_bound {B N L C H β : ℝ}
    (hB : 0 < B) (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (S : Finset ℤ) (E : ℤ → ℂ) (M V : ℤ → ℝ)
    (hS : ∀ r ∈ S, N * (r : ℝ) ^ 2 / 16 < 2 * B)
    (hM : ∀ r ∈ S, 0 ≤ M r) (hV : ∀ r ∈ S, 0 ≤ V r)
    (hvar : ∀ r ∈ S, M r + V r ≤ H * B ^ (-(1 / 2 : ℝ)))
    (hE : ∀ r ∈ S, ‖E r‖ ≤ C * Real.sqrt (M r * (M r + V r)) * B ^ β) :
    ‖((1 / L) * N ^ (-(1 / 2 : ℝ))) • (∑ r ∈ S, E r)‖ ≤
      (C * H / L) * N ^ (-(1 / 2 : ℝ)) * B ^ (β - 1 / 2) *
        (1 + 8 * Real.sqrt (2 * B / N)) := by
  have hpoint : ∀ r ∈ S, ‖E r‖ ≤ C * H * B ^ (β - 1 / 2) := by
    intro r hr
    have hv := geometric_variation_bound (hM r hr) (hV r hr) hH hB (hvar r hr)
    calc
      _ ≤ C * Real.sqrt (M r * (M r + V r)) * B ^ β := hE r hr
      _ ≤ C * (H * B ^ (-(1 / 2 : ℝ))) * B ^ β :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hC) (by positivity)
      _ = C * H * (B ^ (-(1 / 2 : ℝ)) * B ^ β) := by ring
      _ = C * H * B ^ (β - 1 / 2) := by
        rw [← Real.rpow_add hB]
        congr 2
        ring
  have hsum : ‖∑ r ∈ S, E r‖ ≤ (S.card : ℝ) * (C * H * B ^ (β - 1 / 2)) := by
    calc
      _ ≤ ∑ r ∈ S, ‖E r‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ S, C * H * B ^ (β - 1 / 2) := Finset.sum_le_sum hpoint
      _ = _ := by simp
  have hcard := trace_index_card_bound hB hN S hS
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 / L) * N ^ (-(1 / 2 : ℝ)))]
  calc
    _ ≤ ((1 / L) * N ^ (-(1 / 2 : ℝ))) *
        ((1 + 8 * Real.sqrt (2 * B / N)) * (C * H * B ^ (β - 1 / 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = _ := by ring

/-- The product of the index radius and the outside level normalization. -/
theorem root_scale_identity {B N : ℝ} (hB : 0 < B) (hN : 0 < N) (γ : ℝ) :
    N ^ (-(1 / 2 : ℝ)) * B ^ γ * Real.sqrt (2 * B / N) =
      Real.sqrt 2 * N ^ (-1 : ℝ) * B ^ (γ + 1 / 2) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_add hB, ← Real.sqrt_eq_rpow, Real.rpow_neg_one,
    Real.rpow_neg hN.le, ← Real.sqrt_eq_rpow]
  have hn := Real.sq_sqrt hN.le
  have hn0 : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  field_simp [hn0, hN.ne']
  nlinarith [congrArg (fun x : ℝ => Real.sqrt 2 * B ^ γ * Real.sqrt B * x) hn]

/-- Equation (141), conditional only on the individual prime-average
bound and the weight-variation estimate. The full index sum is actual. -/
theorem three_quarter_block_bound {B N L C H ε : ℝ}
    (hB : 0 < B) (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (S : Finset ℤ) (E : ℤ → ℂ) (M V : ℤ → ℝ)
    (hS : ∀ r ∈ S, N * (r : ℝ) ^ 2 / 16 < 2 * B)
    (hM : ∀ r ∈ S, 0 ≤ M r) (hV : ∀ r ∈ S, 0 ≤ V r)
    (hvar : ∀ r ∈ S, M r + V r ≤ H * B ^ (-(1 / 2 : ℝ)))
    (hE : ∀ r ∈ S, ‖E r‖ ≤ C * Real.sqrt (M r * (M r + V r)) *
      B ^ (3 / 4 + ε)) :
    ‖((1 / L) * N ^ (-(1 / 2 : ℝ))) • (∑ r ∈ S, E r)‖ ≤
      (8 * Real.sqrt 2 * C * H / L) *
        (N ^ (-(1 / 2 : ℝ)) * B ^ (1 / 4 + ε) +
          N ^ (-1 : ℝ) * B ^ (3 / 4 + ε)) := by
  have hb := finite_block_bound hB hN hL hC hH S E M V hS hM hV hvar hE
  have he : (3 / 4 + ε) - 1 / 2 = 1 / 4 + ε := by ring
  rw [he] at hb
  have hid := root_scale_identity hB hN (1 / 4 + ε)
  rw [show (1 / 4 + ε) + 1 / 2 = 3 / 4 + ε by ring] at hid
  have hsqrt : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hA : 0 ≤ N ^ (-(1 / 2 : ℝ)) * B ^ (1 / 4 + ε) := by positivity
  have hCH : 0 ≤ C * H / L := by positivity
  have hcoef : C * H / L ≤ (8 * Real.sqrt 2) * (C * H / L) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show 1 ≤ 8 * Real.sqrt 2 by linarith) hCH
  apply hb.trans
  calc
    _ = (C * H / L) * (N ^ (-(1 / 2 : ℝ)) * B ^ (1 / 4 + ε)) +
        8 * (C * H / L) *
          (N ^ (-(1 / 2 : ℝ)) * B ^ (1 / 4 + ε) * Real.sqrt (2 * B / N)) := by ring
    _ = ((C * H / L) * (N ^ (-(1 / 2 : ℝ)) * B ^ (1 / 4 + ε))) +
        ((8 * Real.sqrt 2) * (C * H / L)) *
          (N ^ (-1 : ℝ) * B ^ (3 / 4 + ε)) := by rw [hid]; ring
    _ ≤ ((8 * Real.sqrt 2) * (C * H / L)) *
          (N ^ (-(1 / 2 : ℝ)) * B ^ (1 / 4 + ε)) +
        ((8 * Real.sqrt 2) * (C * H / L)) *
          (N ^ (-1 : ℝ) * B ^ (3 / 4 + ε)) := by
      simpa only [mul_assoc] using
        add_le_add (mul_le_mul_of_nonneg_right hcoef hA)
          (le_refl (((8 * Real.sqrt 2) * (C * H / L)) *
            (N ^ (-1 : ℝ) * B ^ (3 / 4 + ε))))
    _ = _ := by ring

/-- The hypothetical improved prime-average exponent mentioned after
(141) has exactly the stated effect on the complete finite block. -/
theorem improved_half_block_bound {B N L C H ε : ℝ}
    (hB : 0 < B) (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (S : Finset ℤ) (E : ℤ → ℂ) (M V : ℤ → ℝ)
    (hS : ∀ r ∈ S, N * (r : ℝ) ^ 2 / 16 < 2 * B)
    (hM : ∀ r ∈ S, 0 ≤ M r) (hV : ∀ r ∈ S, 0 ≤ V r)
    (hvar : ∀ r ∈ S, M r + V r ≤ H * B ^ (-(1 / 2 : ℝ)))
    (hE : ∀ r ∈ S, ‖E r‖ ≤ C * Real.sqrt (M r * (M r + V r)) *
      B ^ (1 / 2 + ε)) :
    ‖((1 / L) * N ^ (-(1 / 2 : ℝ))) • (∑ r ∈ S, E r)‖ ≤
      (8 * Real.sqrt 2 * C * H / L) *
        (N ^ (-(1 / 2 : ℝ)) * B ^ ε +
          N ^ (-1 : ℝ) * B ^ (1 / 2 + ε)) := by
  have hb := finite_block_bound hB hN hL hC hH S E M V hS hM hV hvar hE
  rw [show (1 / 2 + ε) - 1 / 2 = ε by ring] at hb
  have hid := root_scale_identity hB hN ε
  rw [show ε + 1 / 2 = 1 / 2 + ε by ring] at hid
  have hsqrt : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hA : 0 ≤ N ^ (-(1 / 2 : ℝ)) * B ^ ε := by positivity
  have hCH : 0 ≤ C * H / L := by positivity
  have hcoef : C * H / L ≤ (8 * Real.sqrt 2) * (C * H / L) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show 1 ≤ 8 * Real.sqrt 2 by linarith) hCH
  apply hb.trans
  calc
    _ = (C * H / L) * (N ^ (-(1 / 2 : ℝ)) * B ^ (ε)) +
        8 * (C * H / L) *
          (N ^ (-(1 / 2 : ℝ)) * B ^ (ε) * Real.sqrt (2 * B / N)) := by ring
    _ = ((C * H / L) * (N ^ (-(1 / 2 : ℝ)) * B ^ (ε))) +
        ((8 * Real.sqrt 2) * (C * H / L)) *
          (N ^ (-1 : ℝ) * B ^ (1 / 2 + ε)) := by rw [hid]; ring
    _ ≤ ((8 * Real.sqrt 2) * (C * H / L)) *
          (N ^ (-(1 / 2 : ℝ)) * B ^ (ε)) +
        ((8 * Real.sqrt 2) * (C * H / L)) *
          (N ^ (-1 : ℝ) * B ^ (1 / 2 + ε)) := by
      simpa only [mul_assoc] using
        add_le_add (mul_le_mul_of_nonneg_right hcoef hA)
          (le_refl (((8 * Real.sqrt 2) * (C * H / L)) *
            (N ^ (-1 : ℝ) * B ^ (1 / 2 + ε))))
    _ = _ := by ring

/-- The support restrictions in the final paragraph of Section 7 are
exactly the signs of the two level exponents. -/
theorem three_quarter_exponent_negative {a ε : ℝ} (ha : 0 < a)
    (hε : ε < (1 - 3 * a / 4) / a) : -1 + a * (3 / 4 + ε) < 0 := by
  have := (lt_div_iff₀ ha).mp hε
  nlinarith

theorem improved_exponent_negative {a ε : ℝ} (ha : 0 < a)
    (hε : ε < (1 - a / 2) / a) : -1 + a * (1 / 2 + ε) < 0 := by
  have := (lt_div_iff₀ ha).mp hε
  nlinarith

end DepthAspect.SignedBlockAssembly
