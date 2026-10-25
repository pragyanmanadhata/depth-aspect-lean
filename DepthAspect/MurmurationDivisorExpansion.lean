import DepthAspect.MurmurationArithmetic
import DepthAspect.MurmurationBesselSeries
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Coprime.Lemmas

/-! The second identity in (128), including absolute convergence of the
actual arithmetic divisor expansion. Spatial compact support reduces the
interchange to finitely many convergent divisor sums, including the sum at
zero; no formal interchange of two divergent series is used. -/
open scoped BigOperators
namespace DepthAspect.MurmurationDivisorExpansion
open MurmurationKernel MurmurationLattice MurmurationBesselSeries
open MurmurationArithmetic ArithmeticWeights

/-- Every fixed positive lattice scale has finite spatial support. -/
theorem finite_lattice_support (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ S : Finset ℤ, ∀ r : ℤ, r ∉ S → kernel k ((r : ℝ) / R) = 0 := by
  obtain ⟨K, hK⟩ := exists_nat_gt R
  refine ⟨Finset.Icc (-(K : ℤ)) (K : ℤ), ?_⟩
  intro r hr
  have hri : (K : ℤ) ≤ |r| := by
    simp only [Finset.mem_Icc, not_and_or] at hr
    rcases hr with h | h
    · exact (by omega : (K : ℤ) ≤ -r).trans (neg_le_abs r)
    · exact (by omega : (K : ℤ) ≤ r).trans (le_abs_self r)
  have hrr : (K : ℝ) ≤ |(r : ℝ)| := by exact_mod_cast hri
  apply kernel_zero_of_one_le_abs
  rw [abs_div, abs_of_pos hR]
  exact (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hK.le.trans hrr)

/-- Multiplication by an integer coprime to ℓ preserves its residue weight. -/
theorem residueWeight_mul {ℓ d : ℕ} (hcop : d.Coprime ℓ) (r : ℤ) :
    residueWeight ℓ ((d : ℤ) * r) = residueWeight ℓ r := by
  have hi : IsCoprime (ℓ : ℤ) (d : ℤ) := hcop.symm.isCoprime
  have hd : (ℓ : ℤ) ∣ (d : ℤ) * r ↔ (ℓ : ℤ) ∣ r :=
    ⟨hi.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h _⟩
  simp only [residueWeight, hd]

/-- The positive square-root scale agrees exactly with the divided lattice. -/
theorem sqrt_div_nat_sq {y : ℝ} (hy : 0 ≤ y) (d : ℕ) :
    Real.sqrt (y / (d : ℝ) ^ 2) = Real.sqrt y / (d : ℝ) := by
  rw [Real.sqrt_div hy, Real.sqrt_sq (Nat.cast_nonneg d)]

/-- Reindexing a divisible real-valued lattice needs no convergence premise:
its support lies in the range of an injective multiplication map. -/
theorem divisible_real_lattice (f : ℤ → ℝ) {d : ℤ} (hd : d ≠ 0) :
    (∑' r : ℤ, if d ∣ r then f r else 0) = ∑' r : ℤ, f (d * r) := by
  have hi : Function.Injective (fun r : ℤ => d * r) := by
    intro r s h
    exact mul_left_cancel₀ hd h
  have hs : Function.support (fun r : ℤ => if d ∣ r then f r else 0) ⊆
      Set.range (fun r : ℤ => d * r) := by
    intro r hr
    by_cases h : d ∣ r
    · obtain ⟨s, rfl⟩ := h
      exact ⟨s, rfl⟩
    · exact (hr (if_neg h)).elim
  simpa using (hi.tsum_eq hs).symm

/-- One divisor contributes exactly c(d)g(y/d²). The coefficient is zero
at d=0 and at non-coprime d, so every case is covered. -/
theorem scaled_divisor_term (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {y : ℝ} (hy : 0 < y) (d : ℕ) :
    (((-1 : ℝ) ^ a * (2 * Real.pi * Real.sqrt y) /
      ((((2 * a + 1 : ℕ) : ℝ)) * (1 - (ℓ : ℝ)⁻¹))) *
      ∑' r : ℤ, residueWeight ℓ r * divisorCoefficient ℓ r d *
        kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))) =
      c ℓ d * g a ℓ (y / (d : ℝ) ^ 2) := by
  by_cases hd : d = 0
  · subst d
    simp [divisorCoefficient]
  by_cases hb : b ℓ d = 0
  · simp [divisorCoefficient, hb, c_apply]
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.pos
  have hcop := b_ne_zero_coprime hℓ hb
  have hsum : (∑' r : ℤ, residueWeight ℓ r * divisorCoefficient ℓ r d *
      kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))) =
      b ℓ d * ∑' r : ℤ, residueWeight ℓ r *
        kernel (2 * a + 2) ((r : ℝ) /
          (2 * (ℓ : ℝ) * Real.sqrt (y / (d : ℝ) ^ 2))) := by
    calc
      _ = b ℓ d * ∑' r : ℤ, if (d : ℤ) ∣ r then
          residueWeight ℓ r * kernel (2 * a + 2)
            ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y)) else 0 := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro r
        simp only [divisorCoefficient, hd0, true_and]
        split_ifs <;> ring
      _ = b ℓ d * ∑' r : ℤ, residueWeight ℓ ((d : ℤ) * r) *
          kernel (2 * a + 2)
            ((((d : ℤ) * r : ℤ) : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y)) := by
        rw [divisible_real_lattice _ (by exact_mod_cast hd)]
      _ = _ := by
        congr 1
        apply tsum_congr
        intro r
        rw [residueWeight_mul hcop, sqrt_div_nat_sq hy.le]
        congr 2
        push_cast
        field_simp
        <;> ring
  rw [hsum]
  unfold g weightedDensity
  simp only [mul_one, sqrt_div_nat_sq hy.le, c_apply]
  generalize hseries : (∑' r : ℤ, residueWeight ℓ r *
    kernel (2 * a + 2) ((r : ℝ) /
      (2 * (ℓ : ℝ) * (Real.sqrt y / (d : ℝ))))) = S
  generalize hden : 1 - (ℓ : ℝ)⁻¹ = z
  field_simp [ne_of_gt hdR]
  <;> ring

/-- The actual arithmetic expansion is absolutely summable and has the
literal density as its value. This includes the infinitely many positive
divisors at the zero lattice point. -/
theorem M_divisor_sum (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    {y : ℝ} (hy : 0 < y) :
    Summable (fun d : ℕ => c ℓ d * g a ℓ (y / (d : ℝ) ^ 2)) ∧
      M a ℓ y = B ℓ * ∑' d : ℕ, c ℓ d * g a ℓ (y / (d : ℝ) ^ 2) := by
  classical
  let R : ℝ := 2 * (ℓ : ℝ) * Real.sqrt y
  have hR : 0 < R := by have := hℓ.pos; dsimp [R]; positivity
  let P : ℝ := (-1 : ℝ) ^ a * (2 * Real.pi * Real.sqrt y) /
    ((((2 * a + 1 : ℕ) : ℝ)) * (1 - (ℓ : ℝ)⁻¹))
  obtain ⟨S, hS⟩ := finite_lattice_support (2 * a + 2) hR
  let t : ℤ → ℕ → ℝ := fun r d =>
    residueWeight ℓ r * divisorCoefficient ℓ r d *
      kernel (2 * a + 2) ((r : ℝ) / R)
  have ht (r : ℤ) : Summable (t r) :=
    ((divisorCoefficient_summable ℓ r).mul_left _).mul_right _
  have hfinite (d : ℕ) : (∑' r : ℤ, t r d) = ∑ r ∈ S, t r d := by
    apply tsum_eq_sum
    intro r hr
    simp only [t, hS r hr, mul_zero]
  have hterm (d : ℕ) : P * ∑ r ∈ S, t r d =
      c ℓ d * g a ℓ (y / (d : ℝ) ^ 2) := by
    rw [← hfinite]
    exact scaled_divisor_term a hℓ hy d
  have hsum : Summable (fun d : ℕ => ∑ r ∈ S, t r d) :=
    summable_sum (fun r _ => ht r)
  have hseries : Summable (fun d : ℕ => c ℓ d * g a ℓ (y / (d : ℝ) ^ 2)) :=
    (hsum.mul_left P).congr hterm
  refine ⟨hseries, ?_⟩
  have hM : M a ℓ y = P * ∑ r ∈ S,
      residueWeight ℓ r * integerPrimeWeight ℓ r *
        kernel (2 * a + 2) ((r : ℝ) / R) := by
    unfold M weightedDensity
    congr 1
    apply tsum_eq_sum
    intro r hr
    simp only [show (2 * (ℓ : ℝ) * Real.sqrt y) = R from rfl, hS r hr, mul_zero]
  have hr (r : ℤ) : residueWeight ℓ r * integerPrimeWeight ℓ r *
      kernel (2 * a + 2) ((r : ℝ) / R) = B ℓ * ∑' d : ℕ, t r d := by
    rw [integerPrimeWeight_divisor_sum hℓ]
    dsimp [t]
    rw [tsum_mul_right, tsum_mul_left]
    ring
  rw [hM]
  simp_rw [hr]
  rw [← Finset.mul_sum]
  rw [← Summable.tsum_finsetSum (fun r _ => ht r)]
  calc
    P * (B ℓ * ∑' d : ℕ, ∑ r ∈ S, t r d) =
        B ℓ * ∑' d : ℕ, P * ∑ r ∈ S, t r d := by
      rw [tsum_mul_left]
      ring
    _ = _ := by simp_rw [hterm]

end DepthAspect.MurmurationDivisorExpansion
