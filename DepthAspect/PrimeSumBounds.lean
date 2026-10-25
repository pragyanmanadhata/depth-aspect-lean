import DepthAspect.PrimePairBound
import DepthAspect.DyadicSummation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Weighted prime and trace sums in Lemma 4.3

The finite sets below contain actual integer trace indices. The sole analytic
input is the individual elliptic trace estimate (35); neither the pair bound
nor the weighted block estimate (47) is assumed. Primality is unnecessary for
these stronger bounds over arbitrary finite integer subsets.
-/
namespace DepthAspect.PrimeSumBounds

open scoped BigOperators

/-- The nonnegative weight in the prime contribution to the explicit formula. -/
noncomputable def weightedTerm (L : ℝ) (E : ℤ → ℂ) (h : ℝ → ℂ) (m : ℤ) : ℝ :=
  Real.log (m : ℝ) / Real.sqrt (m : ℝ) * ‖E m‖ * ‖h (Real.log (m : ℝ) / L)‖

/-- Square-root denominator bound on a dyadic interval. -/
theorem inverse_sqrt_dyadic {B x : ℝ} (hB : 0 < B) (hx : B / 2 < x) :
    1 / Real.sqrt x ≤ Real.sqrt 2 / Real.sqrt B := by
  have hx0 : 0 < x := by linarith
  have hroot : Real.sqrt B ≤ Real.sqrt 2 * Real.sqrt x := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt (by linarith)
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr hx0) (Real.sqrt_pos.mpr hB)).mpr
    (by simpa only [one_mul] using hroot)

/-- Each weighted summand is bounded by a constant times the actual number
of surviving trace indices. -/
theorem weightedTerm_bound {B L δ A H : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hA : 0 ≤ A) (_hH : 0 ≤ H) (E : ℤ → ℂ) (h : ℝ → ℂ)
    (T : ℤ → Finset ℤ) (m : ℤ) (hm1 : 1 ≤ (m : ℝ))
    (hmlo : B / 2 < (m : ℝ)) (hmhi : (m : ℝ) ≤ B)
    (htrace : ‖E m‖ ≤ A * (m : ℝ) ^ δ * ((T m).card : ℝ))
    (hh : ‖h (Real.log (m : ℝ) / L)‖ ≤ H) :
    weightedTerm L E h m ≤
      (Real.log B * (Real.sqrt 2 / Real.sqrt B) * A * B ^ δ * H) *
        ((T m).card : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by linarith
  have hB0 : 0 < B := by linarith
  have hlog : Real.log (m : ℝ) ≤ Real.log B := Real.log_le_log hm0 hmhi
  have hlog0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB
  have hsqrt := inverse_sqrt_dyadic hB0 hmlo
  have hweight : Real.log (m : ℝ) / Real.sqrt (m : ℝ) ≤
      Real.log B * (Real.sqrt 2 / Real.sqrt B) := by
    simpa only [mul_one_div] using
      mul_le_mul hlog hsqrt (by positivity) hlogB0
  have hpower : (m : ℝ) ^ δ ≤ B ^ δ := Real.rpow_le_rpow hm0.le hmhi hδ
  have htrace' : ‖E m‖ ≤ A * B ^ δ * ((T m).card : ℝ) :=
    htrace.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower hA) (by positivity))
  unfold weightedTerm
  calc
    _ ≤ (Real.log B * (Real.sqrt 2 / Real.sqrt B)) *
        (A * B ^ δ * ((T m).card : ℝ)) * H := by
      apply mul_le_mul (mul_le_mul hweight htrace' (norm_nonneg _) (by positivity)) hh
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Equation (47), retaining a general coefficient `A` in the pointwise
trace estimate `‖E m‖ ≤ A m^δ T(m)`. -/
theorem dyadic_block_bound {B N L δ A H : ℝ} {q : ℤ}
    (hB : 1 ≤ B) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (M : Finset ℤ) (T : ℤ → Finset ℤ) (E : ℤ → ℂ) (h : ℝ → ℂ)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ B / 2 < (m : ℝ) ∧ (m : ℝ) ≤ B)
    (hT : ∀ m ∈ M, ∀ t ∈ T m, t ^ 2 < 4 * m ∧ 4 * q ∣ 4 * m - t ^ 2)
    (htrace : ∀ m ∈ M, ‖E m‖ ≤ A * (m : ℝ) ^ δ * ((T m).card : ℝ))
    (hh : ∀ m ∈ M, ‖h (Real.log (m : ℝ) / L)‖ ≤ H) :
    (2 / L) * (∑ m ∈ M, weightedTerm L E h m) ≤
      96 * A * Real.sqrt 2 * H * (B ^ (1 + δ) / N) * (Real.log B / L) := by
  have hB0 : 0 < B := by linarith
  have hN0 : 0 < N := by rw [hN]; positivity
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hB
  let C := Real.log B * (Real.sqrt 2 / Real.sqrt B) * A * B ^ δ * H
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterms : (∑ m ∈ M, weightedTerm L E h m) ≤
      C * (∑ m ∈ M, ((T m).card : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    exact weightedTerm_bound hB hδ hA hH E h T m (hM m hm).1
      (hM m hm).2.1 (hM m hm).2.2 (htrace m hm) (hh m hm)
  have hcount := PrimePairBound.original_trace_sum_bound hB hq hN M T
    (fun m hm t ht => ⟨(hT m hm t ht).1, (hM m hm).2.2, (hT m hm t ht).2⟩)
  have hcount' : (∑ m ∈ M, ((T m).card : ℝ)) ≤ 48 * B ^ (3 / 2 : ℝ) / N := by
    exact_mod_cast hcount
  have htotal := mul_le_mul_of_nonneg_left
    (hterms.trans (mul_le_mul_of_nonneg_left hcount' hC)) (by positivity : 0 ≤ 2 / L)
  have hpow : B ^ (3 / 2 : ℝ) = B * Real.sqrt B := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hB0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hpow' : B ^ (1 + δ) = B * B ^ δ := by
    rw [Real.rpow_add hB0, Real.rpow_one]
  have heq : (2 / L) * (C * (48 * B ^ (3 / 2 : ℝ) / N)) =
      96 * A * Real.sqrt 2 * H * (B ^ (1 + δ) / N) * (Real.log B / L) := by
    rw [hpow, hpow']
    dsimp [C]
    field_simp
    ring
  rwa [heq] at htotal

/-- The exact powers of the level in the paper's equation (47). -/
theorem dyadic_block_bound_level {B N L δ K H : ℝ} {q : ℤ}
    (hB : 1 ≤ B) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (M : Finset ℤ) (T : ℤ → Finset ℤ) (E : ℤ → ℂ) (h : ℝ → ℂ)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ B / 2 < (m : ℝ) ∧ (m : ℝ) ≤ B)
    (hT : ∀ m ∈ M, ∀ t ∈ T m, t ^ 2 < 4 * m ∧ 4 * q ∣ 4 * m - t ^ 2)
    (htrace : ∀ m ∈ M, ‖E m‖ ≤ K * N ^ (-(1 / 2 : ℝ)) *
      (m : ℝ) ^ δ * ((T m).card : ℝ))
    (hh : ∀ m ∈ M, ‖h (Real.log (m : ℝ) / L)‖ ≤ H) :
    (2 / L) * (∑ m ∈ M, weightedTerm L E h m) ≤
      96 * K * Real.sqrt 2 * H * N ^ (-(3 / 2 : ℝ)) *
        B ^ (1 + δ) * (Real.log B / L) := by
  have hN0 : 0 < N := by rw [hN]; positivity
  have hb := dyadic_block_bound hB hL hδ (mul_nonneg hK (Real.rpow_nonneg hN0.le _))
    hH hq hN M T E h hM hT htrace hh
  have hn : N ^ (-(1 / 2 : ℝ)) / N = N ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    norm_num
  have heq : 96 * (K * N ^ (-(1 / 2 : ℝ))) * Real.sqrt 2 * H *
      (B ^ (1 + δ) / N) * (Real.log B / L) =
      96 * K * Real.sqrt 2 * H * N ^ (-(3 / 2 : ℝ)) *
        B ^ (1 + δ) * (Real.log B / L) := by
    calc
      _ = 96 * K * Real.sqrt 2 * H * (N ^ (-(1 / 2 : ℝ)) / N) *
          B ^ (1 + δ) * (Real.log B / L) := by ring
      _ = _ := by rw [hn]
  rwa [heq] at hb

/-- Equation (45), including the actual finite dyadic partition. The bound
applies to any finite integer subset of `[1,X]`; taking odd primes gives the
paper's sum. Its only trace input is the pointwise estimate (35). -/
theorem prime_sum_bound {X N L δ K H s : ℝ} {q : ℤ}
    (hX : 1 ≤ X) (hL : 0 < L) (hδ : 0 ≤ δ) (hs : 0 ≤ s)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (hlogX : Real.log X ≤ s * L)
    (M : Finset ℤ) (T : ℤ → Finset ℤ) (E : ℤ → ℂ) (h : ℝ → ℂ)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (hT : ∀ m ∈ M, ∀ t ∈ T m, t ^ 2 < 4 * m ∧ 4 * q ∣ 4 * m - t ^ 2)
    (htrace : ∀ m ∈ M, ‖E m‖ ≤ K * N ^ (-(1 / 2 : ℝ)) *
      (m : ℝ) ^ δ * ((T m).card : ℝ))
    (hh : ∀ m ∈ M, ‖h (Real.log (m : ℝ) / L)‖ ≤ H) :
    (2 / L) * (∑ m ∈ M, weightedTerm L E h m) ≤
      (96 * s * K * Real.sqrt 2 / (1 - (2 : ℝ) ^ (-1 - δ))) *
        H * N ^ (-(3 / 2 : ℝ)) * X ^ (1 + δ) := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by rw [hN]; positivity
  let C := 96 * K * Real.sqrt 2 * H * N ^ (-(3 / 2 : ℝ)) * s
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hblocks : ∀ j : ℕ,
      (∑ m ∈ DyadicSummation.block X j M, (2 / L) * weightedTerm L E h m) ≤
        C * DyadicSummation.endpoint X j ^ (1 + δ) := by
    intro j
    let S := DyadicSummation.block X j M
    let B := DyadicSummation.endpoint X j
    have hB0 : 0 < B := DyadicSummation.endpoint_pos hX0 j
    have hsub : S ⊆ M := Finset.filter_subset _ _
    by_cases hempty : S = ∅
    · change (∑ m ∈ S, (2 / L) * weightedTerm L E h m) ≤ C * B ^ (1 + δ)
      rw [hempty, Finset.sum_empty]
      positivity
    · obtain ⟨m, hm⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hB : 1 ≤ B := (hM m (hsub hm)).1.trans (Finset.mem_filter.mp hm).2.2
      have hSM : ∀ m ∈ S, 1 ≤ (m : ℝ) ∧ B / 2 < (m : ℝ) ∧ (m : ℝ) ≤ B := by
        intro m hm
        obtain ⟨hmM, hmlow, hmhigh⟩ := Finset.mem_filter.mp hm
        refine ⟨(hM m hmM).1, ?_, hmhigh⟩
        simpa only [DyadicSummation.endpoint_succ] using hmlow
      have hb := dyadic_block_bound_level hB hL hδ hK hH hq hN S T E h hSM
        (fun m hm => hT m (hsub hm)) (fun m hm => htrace m (hsub hm))
        (fun m hm => hh m (hsub hm))
      have hlog : Real.log B / L ≤ s := by
        apply (div_le_iff₀ hL).mpr
        exact (Real.log_le_log hB0 (DyadicSummation.endpoint_le hX0.le j)).trans hlogX
      rw [Finset.mul_sum] at hb
      calc
        _ ≤ 96 * K * Real.sqrt 2 * H * N ^ (-(3 / 2 : ℝ)) *
            B ^ (1 + δ) * (Real.log B / L) := hb
        _ ≤ 96 * K * Real.sqrt 2 * H * N ^ (-(3 / 2 : ℝ)) *
            B ^ (1 + δ) * s := mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = C * B ^ (1 + δ) := by dsimp [C]; ring
  have hsum := DyadicSummation.sum_bound hX0.le (by linarith : 0 < 1 + δ)
    hC M (fun m => (2 / L) * weightedTerm L E h m) hM hblocks
  rw [← Finset.mul_sum] at hsum
  have heq : C * X ^ (1 + δ) / (1 - (2 : ℝ) ^ (-(1 + δ))) =
      (96 * s * K * Real.sqrt 2 / (1 - (2 : ℝ) ^ (-1 - δ))) *
        H * N ^ (-(3 / 2 : ℝ)) * X ^ (1 + δ) := by
    rw [show -(1 + δ) = -1 - δ by ring]
    dsimp [C]
    ring
  rwa [heq] at hsum

/-- For the paper's `X=(k²N)^s` and `L=log(k²N)`, the logarithm endpoint
condition in `prime_sum_bound` is an identity. -/
theorem logarithmic_endpoint (Y s : ℝ) (hY : 0 < Y) :
    Real.log (Y ^ s) = s * Real.log Y := Real.log_rpow hY s

end DepthAspect.PrimeSumBounds
