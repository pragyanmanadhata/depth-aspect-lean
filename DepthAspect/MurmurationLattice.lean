import DepthAspect.MurmurationKernel
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-! The literal weighted lattice in (106) and its small-argument value. -/
open scoped BigOperators
namespace DepthAspect.MurmurationLattice
open MurmurationKernel

noncomputable def residueWeight (ℓ : ℕ) (r : ℤ) : ℝ :=
  (if (ℓ : ℤ) ∣ r then 1 else 0) - (ℓ : ℝ)⁻¹

noncomputable def weightedDensity (a ℓ : ℕ) (w : ℤ → ℝ) (y : ℝ) : ℝ :=
  ((-1 : ℝ) ^ a * (2 * Real.pi * Real.sqrt y) /
    ((((2 * a + 1 : ℕ) : ℝ)) * (1 - (ℓ : ℝ)⁻¹))) *
      ∑' r : ℤ, residueWeight ℓ r * w r *
        kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))

/-- A nonzero integer is outside the kernel whenever the lattice radius
is at most one. Equality at the support boundary is included. -/
theorem lattice_kernel_zero {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (k : ℕ) {r : ℤ} (hr : r ≠ 0) : kernel k ((r : ℝ) / R) = 0 := by
  have hr1 : (1 : ℤ) ≤ |r| := by
    have habs : 0 < |r| := abs_pos.mpr hr
    omega
  have hrR : (1 : ℝ) ≤ |(r : ℝ)| := by exact_mod_cast hr1
  apply kernel_zero_of_one_le_abs
  rw [abs_div, abs_of_pos hR]
  exact (le_div_iff₀ hR).mpr (by linarith)

/-- The small-argument range in (120) makes the lattice radius at most one. -/
theorem small_radius {ℓ : ℕ} (hℓ : 0 < ℓ) {y : ℝ}
    (hy : y ≤ 1 / (4 * (ℓ : ℝ) ^ 2)) :
    2 * (ℓ : ℝ) * Real.sqrt y ≤ 1 := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hs : Real.sqrt y ≤ 1 / (2 * (ℓ : ℝ)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    convert hy using 1 <;> field_simp <;> ring
  have ht := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * (ℓ : ℝ))
  simpa only [mul_one_div_cancel (by positivity : 2 * (ℓ : ℝ) ≠ 0)] using ht

/-- The first line of Theorem 6.1 uses only the actual origin weight w(0)=1.
It therefore applies to both the arithmetic density and the unweighted g. -/
theorem weightedDensity_small (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (w : ℤ → ℝ) (hw : w 0 = 1) {y : ℝ} (hy : 0 < y)
    (hymax : y ≤ 1 / (4 * (ℓ : ℝ) ^ 2)) :
    weightedDensity a ℓ w y =
      (2 * Real.pi / ((2 * a + 1 : ℕ) : ℝ)) * Real.sqrt y := by
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hR : 0 < 2 * (ℓ : ℝ) * Real.sqrt y := by positivity
  have hR1 := small_radius (by omega : 0 < ℓ) hymax
  have hs : (∑' r : ℤ, residueWeight ℓ r * w r *
      kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))) =
      (1 - (ℓ : ℝ)⁻¹) * (-1 : ℝ) ^ a := by
    rw [tsum_eq_single 0]
    · simp [residueWeight, hw, kernel_zero]
    · intro r hr
      rw [lattice_kernel_zero hR hR1 _ hr, mul_zero]
  have hz : 1 - (ℓ : ℝ)⁻¹ ≠ 0 := by
    have : (ℓ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hℓR
    linarith
  have hm : (((2 * a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hsign : ((-1 : ℝ) ^ a) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm a 2, pow_mul]
    norm_num
  unfold weightedDensity
  rw [hs]
  calc
    _ = (2 * Real.pi / ((2 * a + 1 : ℕ) : ℝ)) * Real.sqrt y *
        ((-1 : ℝ) ^ a) ^ 2 := by
          generalize hzv : 1 - (ℓ : ℝ)⁻¹ = z at hz ⊢
          field_simp [hz, hm]
          <;> ring
    _ = _ := by rw [hsign, mul_one]

end DepthAspect.MurmurationLattice
