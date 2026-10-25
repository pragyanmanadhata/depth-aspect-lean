import DepthAspect.MurmurationArithmetic
import DepthAspect.TraceTrigonometry
import DepthAspect.SignedBlockAssembly
import DepthAspect.ActiveTraceIndices

/-!
# The exact main-term identity (108)

This identifies the literal alternating cosine lattice, with the actual
omitted-prime product coefficient π²p₂(r)/8, with the actual density M₂.
The identification of this product with the character-averaged L-value is
made separately in the arithmetic prime-average theorem.
-/
namespace DepthAspect.SignedDensity
open MurmurationKernel MurmurationLattice MurmurationArithmetic ArithmeticWeights
open scoped BigOperators

noncomputable def meanLValueCoefficient (r : ℤ) : ℝ :=
  (Real.pi ^ 2 / 8) * integerPrimeWeight 2 r

theorem kernel_zero_outside_active (a : ℕ) {N u : ℝ} (hN : 0 < N) (hu : 0 < u)
    (r : ℤ) (hr : r ∉ activeIndices N u) :
    kernel (2 * a + 2) ((r : ℝ) / (4 * Real.sqrt (u / N))) = 0 := by
  have ht : u ≤ N * (r : ℝ) ^ 2 / 16 := by
    exact le_of_not_gt (by intro h; exact hr ((mem_activeIndices hN hu r).mpr h))
  have hs := Real.sq_sqrt (by positivity : 0 ≤ u / N)
  have hR : 0 < 4 * Real.sqrt (u / N) := by positivity
  apply kernel_zero_of_one_le_abs
  rw [abs_div, abs_of_pos hR]
  apply (le_div_iff₀ hR).mpr
  have hdiv : 16 * u / N ≤ (r : ℝ) ^ 2 :=
    (div_le_iff₀ hN).mpr (by nlinarith)
  have hsq : (4 * Real.sqrt (u / N)) ^ 2 ≤ |(r : ℝ)| ^ 2 := by
    calc
      _ = 16 * (u / N) := by rw [mul_pow, hs]; norm_num
      _ = 16 * u / N := by ring
      _ ≤ (r : ℝ) ^ 2 := hdiv
      _ = |(r : ℝ)| ^ 2 := by rw [sq_abs]
  simpa only [one_mul] using (sq_le_sq₀ hR.le (abs_nonneg (r : ℝ))).mp hsq

/-- The alternating lattice sign is twice the exact residue weight at two. -/
theorem alternating_residueWeight (r : ℤ) :
    (-1 : ℝ) ^ r = 2 * residueWeight 2 r := by
  rw [neg_one_zpow_eq_ite]
  simp only [residueWeight, Nat.cast_ofNat]
  by_cases he : Even r
  · have hd : (2 : ℤ) ∣ r := even_iff_two_dvd.mp he
    norm_num [he, hd]
  · have hd : ¬ (2 : ℤ) ∣ r := by simpa only [← even_iff_two_dvd] using he
    simp [he, hd]

theorem cosine_eq_kernel (a : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    Real.cos ((2 * (a : ℝ) + 1) * Real.arcsin x) =
      (-1 : ℝ) ^ a * kernel (2 * a + 2) x := by
  rw [TraceTrigonometry.kernel_even_arcsin a x hx]
  have hs : ((-1 : ℝ) ^ a) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm a 2, pow_mul]
    norm_num
  rw [← mul_assoc, ← pow_two, hs, one_mul]

/-- The actual M₂ is a finite sum on precisely the negative-discriminant
index set, including the convention that boundary kernels vanish. -/
theorem M_two_eq_active_sum (a : ℕ) {N u : ℝ} (hN : 0 < N) (hu : 0 < u) :
    M a 2 (u / N) =
      ((-1 : ℝ) ^ a * (4 * Real.pi * Real.sqrt (u / N)) / ((2 * a + 1 : ℕ) : ℝ)) *
        ∑ r ∈ activeIndices N u, residueWeight 2 r * integerPrimeWeight 2 r *
          kernel (2 * a + 2) ((r : ℝ) / (4 * Real.sqrt (u / N))) := by
  have hs : (∑' r : ℤ, residueWeight 2 r * integerPrimeWeight 2 r *
      kernel (2 * a + 2) ((r : ℝ) / (4 * Real.sqrt (u / N)))) =
      ∑ r ∈ activeIndices N u, residueWeight 2 r * integerPrimeWeight 2 r *
        kernel (2 * a + 2) ((r : ℝ) / (4 * Real.sqrt (u / N))) := by
    apply tsum_eq_sum
    intro r hr
    rw [kernel_zero_outside_active a hN hu r hr, mul_zero]
  unfold M weightedDensity
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 2 = 4 by norm_num]
  rw [hs]
  ring

/-- Equation (108), with literal finite lattice and literal p₂ product.
The scalar c_N is exactly (k−1)N/(32d) for k=2a+2. -/
theorem prime_main_term_eq_M (a : ℕ) {N u d : ℝ}
    (hN : 0 < N) (hu : 0 < u) (hd : 0 < d) :
    Real.sqrt (N * u) / (2 * Real.pi * d) *
      (∑ r ∈ activeIndices N u, (-1 : ℝ) ^ r *
        Real.cos ((2 * (a : ℝ) + 1) *
          Real.arcsin ((r : ℝ) / (4 * Real.sqrt (u / N)))) * meanLValueCoefficient r) =
      (((2 * a + 1 : ℕ) : ℝ) * N / (32 * d)) * M a 2 (u / N) := by
  have hsum : (∑ r ∈ activeIndices N u, (-1 : ℝ) ^ r *
      Real.cos ((2 * (a : ℝ) + 1) *
        Real.arcsin ((r : ℝ) / (4 * Real.sqrt (u / N)))) * meanLValueCoefficient r) =
      ((-1 : ℝ) ^ a * (Real.pi ^ 2 / 4)) *
        ∑ r ∈ activeIndices N u, residueWeight 2 r * integerPrimeWeight 2 r *
          kernel (2 * a + 2) ((r : ℝ) / (4 * Real.sqrt (u / N))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [alternating_residueWeight, cosine_eq_kernel a _ (active_argument_bound hN hu hr).le]
    unfold meanLValueCoefficient
    ring
  have hscale : Real.sqrt (N * u) = N * Real.sqrt (u / N) := by
    rw [Real.sqrt_mul hN.le, Real.sqrt_div hu.le]
    have hs := Real.sq_sqrt hN.le
    have hn : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hN)
    field_simp [hn]
    nlinarith [congrArg (fun z : ℝ => z * Real.sqrt u) hs]
  rw [hsum, M_two_eq_active_sum a hN hu, hscale]
  have hm : (((2 * a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hm, Real.pi_ne_zero, hd.ne']
  ring

end DepthAspect.SignedDensity
