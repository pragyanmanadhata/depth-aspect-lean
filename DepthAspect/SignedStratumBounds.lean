import DepthAspect.SignedSieve
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Counting the actual integer variables in a signed trace stratum

The finite cardinality estimate is proved from the quadratic trace range.
It is not supplied as an assumption in the signed trace bound.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- The first assertion of (73), including repeated-root endpoints. -/
theorem norm_signedPolynomial_le (r : ℕ) (x m : ℝ) (hm : 0 ≤ m)
    (hx : x ^ 2 ≤ 4 * m) :
    ‖tracePolynomial (x : ℂ) (m : ℂ) (2 * r)‖ ≤
      ((2 * r + 1 : ℕ) : ℝ) * m ^ r := by
  simpa only [pow_mul, Real.sq_sqrt hm, Nat.cast_add, Nat.cast_one] using norm_tracePolynomial_le x m (2 * r) hx

/-- A finite set of integers in a real symmetric interval has at most
its length plus one elements. -/
theorem card_integer_symmetric_interval (U : Finset ℤ) (X : ℝ) (hX : 0 ≤ X)
    (hU : ∀ u ∈ U, |(u : ℝ)| ≤ X) : (U.card : ℝ) ≤ 2 * X + 1 := by
  have hf : (0 : ℤ) ≤ ⌊X⌋ := Int.floor_nonneg.mpr hX
  have hsub : U ⊆ Finset.Icc (-⌊X⌋) ⌊X⌋ := by
    intro u hu
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp (hU u hu)
    have hupper : u ≤ ⌊X⌋ := Int.le_floor.mpr hh.2
    have hlower : -u ≤ ⌊X⌋ := Int.le_floor.mpr (by push_cast; linarith [hh.1])
    constructor <;> omega
  have hc : (U.card : ℤ) ≤ ((Finset.Icc (-⌊X⌋) ⌊X⌋).card : ℤ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [Int.card_Icc_of_le (a := -⌊X⌋) (b := ⌊X⌋) (by omega)] at hc
  have hcR : (U.card : ℝ) ≤ (⌊X⌋ : ℝ) + 1 - (- (⌊X⌋ : ℝ)) := by exact_mod_cast hc
  nlinarith [Int.floor_le X]

/-- The quadratic range v*u²≤4m yields the interval-length bound on the
actual set of possible integer u, with no parity restriction needed. -/
theorem card_quadratic_stratum (U : Finset ℤ) (v m : ℝ) (hv : 0 < v) (hm : 0 ≤ m)
    (hU : ∀ u ∈ U, v * (u : ℝ) ^ 2 ≤ 4 * m) :
    (U.card : ℝ) ≤ 1 + 4 * Real.sqrt m / Real.sqrt v := by
  have hvroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hX : 0 ≤ 2 * Real.sqrt m / Real.sqrt v := by positivity
  have hb := card_integer_symmetric_interval U (2 * Real.sqrt m / Real.sqrt v) hX (by
    intro u hu
    apply (le_div_iff₀ hvroot).mpr
    have hmul : 0 ≤ |(u : ℝ)| * Real.sqrt v := by positivity
    have hright : 0 ≤ 2 * Real.sqrt m := by positivity
    apply (sq_le_sq₀ hmul hright).mp
    simp only [mul_pow, sq_abs, Real.sq_sqrt hv.le, Real.sq_sqrt hm]
    nlinarith [hU u hu])
  calc
    (U.card : ℝ) ≤ 2 * (2 * Real.sqrt m / Real.sqrt v) + 1 := hb
    _ = _ := by ring

/-- The smallest surviving divisor is N/16. This derives the literal
1+16√(m/N) estimate used after table (72). -/
theorem card_surviving_stratum (U : Finset ℤ) (v N m : ℝ)
    (hv : 0 < v) (hN : 0 < N) (hm : 0 ≤ m) (hsize : N ≤ 16 * v)
    (hU : ∀ u ∈ U, v * (u : ℝ) ^ 2 ≤ 4 * m) :
    (U.card : ℝ) ≤ 1 + 16 * Real.sqrt m / Real.sqrt N := by
  have hvroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hNroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsqrt : Real.sqrt N ≤ 4 * Real.sqrt v := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg N) (by positivity : 0 ≤ 4 * Real.sqrt v)).mp
    simp only [mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hv.le]
    nlinarith [hsize]
  calc
    (U.card : ℝ) ≤ 1 + 4 * Real.sqrt m / Real.sqrt v := card_quadratic_stratum U v m hv hm hU
    _ ≤ 1 + 16 * Real.sqrt m / Real.sqrt N := by
      have hfrac : 4 * Real.sqrt m / Real.sqrt v ≤ 16 * Real.sqrt m / Real.sqrt N := by
        apply (div_le_div_iff₀ hvroot hNroot).mpr
        nlinarith [mul_nonneg (Real.sqrt_nonneg m) (sub_nonneg.mpr hsqrt)]
      linarith

end DepthAspect.SignedSieve
