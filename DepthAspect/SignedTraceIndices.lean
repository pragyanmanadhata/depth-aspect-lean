import DepthAspect.SignedPrimeFormula
import DepthAspect.ActiveTraceIndices
import Mathlib.Data.Finset.Preimage

/-!
# Exact reindexing of the surviving Ramanujan traces

The same index condition N*r²/16<P is obtained at both depth parities.
The change is a literal finite-sum bijection; no root or trace count is an
input. `ramanujanTwoPow b` has modulus 2^(b+1), so its support scale is 2^b.
-/
namespace DepthAspect.SignedDensity
open SignedSieve DyadicRamanujan
open scoped BigOperators

noncomputable def scaledPrimeTraces (b c P : ℕ) : Finset ℤ :=
  (strictPrimeTraces c P).preimage (fun r : ℤ => (2 : ℤ) ^ b * r)
    (by intro x _ y _ hxy; exact mul_left_cancel₀ (by positivity : (2 : ℤ) ^ b ≠ 0) hxy)

theorem mem_scaledPrimeTraces (b c P : ℕ) (hc : 0 < c) (hP : 0 < P) (r : ℤ) :
    r ∈ scaledPrimeTraces b c P ↔ ((2 : ℤ) ^ b * r) ^ 2 < 4 * (c : ℤ) * P := by
  rw [scaledPrimeTraces, Finset.mem_preimage, mem_strictPrimeTraces c P hc hP]

theorem ramanujan_zero_outside_scale (b : ℕ) (t : ℤ) (ht : ¬ (2 : ℤ) ^ b ∣ t) :
    ramanujanTwoPow b t = 0 := by
  have ht' : ¬ (2 : ℤ) ^ (b + 1) ∣ t := by
    intro h
    exact ht (dvd_trans (pow_dvd_pow 2 (by omega : b ≤ b + 1)) h)
  simp only [ramanujanTwoPow_formula, if_neg ht, if_neg ht', sub_self]

/-- The exact finite change from t to its half-modulus multiple. -/
theorem ramanujan_trace_reindex (b c P : ℕ) (F : ℤ → ℂ) :
    (∑ t ∈ strictPrimeTraces c P, ramanujanTwoPow b t * F t) =
      (2 : ℂ) ^ b * ∑ r ∈ scaledPrimeTraces b c P,
        (-1 : ℂ) ^ r * F ((2 : ℤ) ^ b * r) := by
  classical
  have hf : (∑ t ∈ strictPrimeTraces c P, ramanujanTwoPow b t * F t) =
      ∑ t ∈ (strictPrimeTraces c P).filter (fun t : ℤ => (2 : ℤ) ^ b ∣ t),
        ramanujanTwoPow b t * F t := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hd : (2 : ℤ) ^ b ∣ t
    · simp only [if_pos hd]
    · simp only [if_neg hd, ramanujan_zero_outside_scale b t hd, zero_mul]
  rw [hf, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun r _ => (2 : ℤ) ^ b * r)
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_preimage.mp hr, dvd_mul_right _ _⟩
  · intro x hx y hy hxy
    exact mul_left_cancel₀ (by positivity : (2 : ℤ) ^ b ≠ 0) hxy
  · intro t ht
    obtain ⟨ht, r, rfl⟩ := Finset.mem_filter.mp ht
    exact ⟨r, Finset.mem_preimage.mpr ht, rfl⟩
  · intro r hr
    rw [ramanujanTwoPow_scaled]
    ring

/-- At even depth, the canonical negative-discriminant set is exactly the
half-modulus quotient of the literal t interval. -/
theorem scaledPrimeTraces_even (a P : ℕ) (hP : 0 < P) :
    scaledPrimeTraces (a + 1) 1 P = activeIndices ((2 : ℝ) ^ (2 * a + 4)) P := by
  ext r
  rw [mem_scaledPrimeTraces _ _ _ (by decide) hP,
    mem_activeIndices (by positivity) (by exact_mod_cast hP)]
  have he : (2 : ℝ) ^ (2 * a + 4) = 4 * ((2 : ℝ) ^ (a + 1)) ^ 2 := by
    rw [← pow_mul, show (a + 1) * 2 = 2 * a + 2 by omega,
      show 2 * a + 4 = (2 * a + 2) + 2 by omega, pow_add]
    norm_num
    ring
  have hcast : (((2 : ℤ) ^ (a + 1) * r) ^ 2 < 4 * (1 : ℤ) * P) ↔
      ((2 : ℝ) ^ (a + 1) * r) ^ 2 < 4 * (P : ℝ) := by
    constructor <;> intro h <;> exact_mod_cast h
  simp only [Nat.cast_one, Nat.cast_ofNat]
  rw [hcast, he]
  constructor <;> intro h <;> nlinarith

/-- The odd-depth half-modulus has one additional factor two, while its
base discriminant has the compensating factor two. -/
theorem scaledPrimeTraces_odd (a P : ℕ) (hP : 0 < P) :
    scaledPrimeTraces (a + 2) 2 P = activeIndices ((2 : ℝ) ^ (2 * a + 5)) P := by
  ext r
  rw [mem_scaledPrimeTraces _ _ _ (by decide) hP,
    mem_activeIndices (by positivity) (by exact_mod_cast hP)]
  have he : (2 : ℝ) ^ (2 * a + 5) = 2 * ((2 : ℝ) ^ (a + 2)) ^ 2 := by
    rw [← pow_mul, show (a + 2) * 2 = 2 * a + 4 by omega,
      show 2 * a + 5 = (2 * a + 4) + 1 by omega, pow_add]
    norm_num
    ring
  have hcast : (((2 : ℤ) ^ (a + 2) * r) ^ 2 < 4 * (2 : ℤ) * P) ↔
      ((2 : ℝ) ^ (a + 2) * r) ^ 2 < 8 * (P : ℝ) := by
    constructor <;> intro h <;> exact_mod_cast h
  simp only [Nat.cast_one, Nat.cast_ofNat]
  rw [hcast, he]
  constructor <;> intro h <;> nlinarith

/-- The same real inverse-sine argument at both parity normalizations. -/
theorem trace_argument_scale {N c q P : ℝ} (hN : 0 < N) (hc : 0 < c)
    (hq : 0 < q) (hP : 0 < P) (hscale : N * c = 4 * q ^ 2) (r : ℝ) :
    (q * r) / (2 * Real.sqrt (c * P)) = r / (4 * Real.sqrt (P / N)) := by
  have hroot : Real.sqrt N * Real.sqrt c = 2 * q := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hc.le]
    nlinarith
  have hqeq : q = Real.sqrt N * Real.sqrt c / 2 := by linarith
  rw [hqeq, Real.sqrt_mul hc.le, Real.sqrt_div hP.le]
  field_simp [(Real.sqrt_pos.mpr hN).ne', (Real.sqrt_pos.mpr hc).ne',
    (Real.sqrt_pos.mpr hP).ne']
  ring

theorem primeCosine_even_scaled (k a P : ℕ) (hP : 0 < P) (r : ℤ) :
    primeCosine k 1 P ((2 : ℤ) ^ (a + 1) * r) =
      Real.cos ((2 * (k : ℝ) + 1) *
        Real.arcsin ((r : ℝ) / (4 * Real.sqrt ((P : ℝ) / (2 : ℝ) ^ (2 * a + 4))))) := by
  have he : (2 : ℝ) ^ (2 * a + 4) * 1 = 4 * ((2 : ℝ) ^ (a + 1)) ^ 2 := by
    rw [← pow_mul, show (a + 1) * 2 = 2 * a + 2 by omega,
      show 2 * a + 4 = (2 * a + 2) + 2 by omega, pow_add]
    norm_num
    ring
  unfold primeCosine
  push_cast
  rw [trace_argument_scale (by positivity) (by norm_num) (by positivity)
    (by exact_mod_cast hP) he]

theorem primeCosine_odd_scaled (k a P : ℕ) (hP : 0 < P) (r : ℤ) :
    primeCosine k 2 P ((2 : ℤ) ^ (a + 2) * r) =
      Real.cos ((2 * (k : ℝ) + 1) *
        Real.arcsin ((r : ℝ) / (4 * Real.sqrt ((P : ℝ) / (2 : ℝ) ^ (2 * a + 5))))) := by
  have he : (2 : ℝ) ^ (2 * a + 5) * 2 = 4 * ((2 : ℝ) ^ (a + 2)) ^ 2 := by
    rw [← pow_mul, show (a + 2) * 2 = 2 * a + 4 by omega,
      show 2 * a + 5 = (2 * a + 4) + 1 by omega, pow_add]
    norm_num
    ring
  unfold primeCosine
  push_cast
  rw [trace_argument_scale (by positivity) (by norm_num) (by positivity)
    (by exact_mod_cast hP) he]

/-- Both supports meet the divisibility hypothesis in (104)/(105). -/
theorem even_trace_eight_dvd (a : ℕ) (ha : 2 ≤ a) (r : ℤ) :
    (8 : ℤ) ∣ (2 : ℤ) ^ (a + 1) * r := by
  exact dvd_mul_of_dvd_left
    (by simpa using (pow_dvd_pow (2 : ℤ) (by omega : 3 ≤ a + 1))) r

theorem odd_trace_eight_dvd (a : ℕ) (ha : 1 ≤ a) (r : ℤ) :
    (8 : ℤ) ∣ (2 : ℤ) ^ (a + 2) * r := by
  exact dvd_mul_of_dvd_left
    (by simpa using (pow_dvd_pow (2 : ℤ) (by omega : 3 ≤ a + 2))) r

end DepthAspect.SignedDensity
