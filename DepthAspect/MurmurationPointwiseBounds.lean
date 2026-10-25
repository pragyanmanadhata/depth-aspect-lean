import DepthAspect.MurmurationBesselSeries
import DepthAspect.BesselBounds
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.Interval

/-! The two bounds for the actual unweighted density in Lemma 6.4. -/
open scoped BigOperators
namespace DepthAspect.MurmurationPointwiseBounds
open MurmurationKernel MurmurationLattice MurmurationBesselSeries BesselFirstKind

/-- The coefficient of each residue is at most one in absolute value. -/
theorem residueWeight_abs_le_one {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (r : ℤ) :
    |residueWeight ℓ r| ≤ 1 := by
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hi : 0 ≤ (ℓ : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hi1 : (ℓ : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓR
  unfold residueWeight
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- A single finite set contains all nonzero lattice terms throughout
0 < y ≤ 1. Its endpoint terms vanish as well. -/
theorem small_lattice_support (a : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) {r : ℤ}
    (hr : r ∉ Finset.Icc (-2 * (ℓ : ℤ)) (2 * (ℓ : ℤ))) :
    kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y)) = 0 := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hs1 : Real.sqrt y ≤ 1 := by simpa using Real.sqrt_le_sqrt hy1
  have hri : 2 * (ℓ : ℤ) ≤ |r| := by
    simp only [Finset.mem_Icc, not_and_or] at hr
    rcases hr with h | h
    · exact (by omega : 2 * (ℓ : ℤ) ≤ -r).trans (neg_le_abs r)
    · exact (by omega : 2 * (ℓ : ℤ) ≤ r).trans (le_abs_self r)
  have hrr : 2 * (ℓ : ℝ) ≤ |(r : ℝ)| := by exact_mod_cast hri
  apply kernel_zero_of_one_le_abs
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * (ℓ : ℝ) * Real.sqrt y)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (ℓ : ℝ) * Real.sqrt y)).mpr
  nlinarith

/-- This direct finite-lattice bound supplies the stronger small-y estimate,
which is needed for the arithmetic divisor tails. -/
theorem g_small_bound (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, ∀ y : ℝ, 0 < y → y ≤ 1 → |g a ℓ y| ≤ C * Real.sqrt y := by
  let S := Finset.Icc (-2 * (ℓ : ℤ)) (2 * (ℓ : ℤ))
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  let C : ℝ := 2 * Real.pi * (S.card + 1) /
    (((2 * a + 1 : ℕ) : ℝ) * (1 - (ℓ : ℝ)⁻¹))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro y hy hy1
  have he : (∑' r : ℤ, residueWeight ℓ r *
      kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))) =
      ∑ r ∈ S, residueWeight ℓ r *
        kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y)) := by
    apply tsum_eq_sum
    intro r hr
    rw [small_lattice_support a (by omega : 0 < ℓ) hy hy1 hr, mul_zero]
  have hb : |∑ r ∈ S, residueWeight ℓ r *
      kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))| ≤ S.card := by
    calc
      _ ≤ ∑ r ∈ S, |residueWeight ℓ r *
          kernel (2 * a + 2) ((r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r _
        rw [abs_mul]
        exact mul_le_one₀ (residueWeight_abs_le_one (by omega) r) (abs_nonneg _)
          (kernel_abs_le_one _ _)
      _ = _ := by simp
  have hsign : |(-1 : ℝ) ^ a| = 1 := by simp
  unfold g weightedDensity
  simp only [mul_one, he, abs_mul, abs_div, hsign, one_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * Real.sqrt y),
    abs_of_pos (by positivity : 0 < (((2 * a + 1 : ℕ) : ℝ) *
      (1 - (ℓ : ℝ)⁻¹)))]
  calc
    _ ≤ (2 * Real.pi * Real.sqrt y /
        ((((2 * a + 1 : ℕ) : ℝ)) * (1 - (ℓ : ℝ)⁻¹))) * S.card :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2 * Real.pi * S.card /
        ((((2 * a + 1 : ℕ) : ℝ)) * (1 - (ℓ : ℝ)⁻¹))) * Real.sqrt y := by ring
    _ ≤ C * Real.sqrt y := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg y)
      dsimp [C]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [Real.pi_pos]

/-- The Bessel half-power bound can be extended to every positive argument:
for arguments below one its right side only gets larger. -/
theorem J_global_half_bound (hDLMF : DLMFIdentities) (m : ℕ) :
    ∃ C > 0, ∀ t : ℝ, 0 < t → |J m t| ≤ C * t ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb, hd⟩ := BesselBounds.J_bounded_and_decay hDLMF m
  refine ⟨C, hC, ?_⟩
  intro t ht
  by_cases ht1 : 1 ≤ t
  · exact hd t ht1
  · have hp : 1 ≤ t ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht (le_of_not_ge ht1) (by norm_num)
    exact (hb t ht.le).trans ((le_mul_iff_one_le_right hC).mpr hp)

/-- Scaling the actual Bessel bound isolates the summable ν^{-3/2}
majorant needed for all subsequent series and integral interchanges. -/
theorem J_scaled_div_bound {m : ℕ} {C β x v : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, 0 < t → |J m t| ≤ C * t ^ (-(1 / 2 : ℝ)))
    (hβ : 1 ≤ β) (hx : 0 < x) (hv : 0 < v) :
    |J m (β * v * x) / v| ≤
      C * x ^ (-(1 / 2 : ℝ)) * v ^ (-(3 / 2 : ℝ)) := by
  have harg : 0 < β * v * x := by positivity
  have hcomp : v * x ≤ β * v * x := by nlinarith
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < v * x) hcomp
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  calc
    _ = |J m (β * v * x)| / v := by rw [abs_div, abs_of_pos hv]
    _ ≤ (C * (β * v * x) ^ (-(1 / 2 : ℝ))) / v :=
      div_le_div_of_nonneg_right (hb _ harg) hv.le
    _ ≤ (C * (v * x) ^ (-(1 / 2 : ℝ))) / v :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hv.le
    _ = _ := by
      rw [Real.mul_rpow hv.le hx.le]
      have he : v ^ (-(1 / 2 : ℝ)) / v = v ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_sub_one (ne_of_gt hv)]
        norm_num
      calc
        _ = C * x ^ (-(1 / 2 : ℝ)) * (v ^ (-(1 / 2 : ℝ)) / v) := by ring
        _ = _ := by rw [he]

/-- This is an absolutely summable positive-index p-series. -/
theorem pnat_three_halves_summable :
    Summable (fun ν : ℕ+ => (ν : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have h := (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
  exact h.comp_injective Subtype.val_injective

/-- A reusable absolute majorant for each difference in (128). -/
theorem bessel_difference_bound (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    {K : ℝ} (hK : 0 < K)
    (hb : ∀ t : ℝ, 0 < t → |J (2 * a + 1) t| ≤ K * t ^ (-(1 / 2 : ℝ)))
    {y : ℝ} (hy : 0 < y) (ν : ℕ+) :
    |J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
      J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)| ≤
      2 * K * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) * (ν : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hv : (0 : ℝ) < ν := by exact_mod_cast ν.pos
  have hπ : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.two_le_pi]
  have h1 := J_scaled_div_bound hK.le hb hπ hs hv
  have h2 := J_scaled_div_bound hK.le hb
    (by nlinarith : (1 : ℝ) ≤ 4 * Real.pi * ℓ) hs hv
  have h2' : |J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) /
      ((ℓ : ℝ) * ν)| ≤
      K * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) * (ν : ℝ) ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = |J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / (ν : ℝ)| /
          (ℓ : ℝ) := by
        simp only [abs_div, abs_mul, abs_of_pos hv,
          abs_of_pos (lt_trans zero_lt_one hℓR)]
        ring
      _ ≤ |J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / (ν : ℝ)| :=
        div_le_self (abs_nonneg _) hℓR.le
      _ ≤ _ := h2
  exact (abs_sub _ _).trans (by linarith)

/-- The quarter-power bound in Lemma 6.4 holds globally; the stronger
square-root bound above is used when y is small. -/
theorem g_quarter_bound (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, ∀ y : ℝ, 0 < y → |g a ℓ y| ≤ C * y ^ (1 / 4 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := J_global_half_bound hDLMF (2 * a + 1)
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  let S : ℝ := ∑' ν : ℕ+, (ν : ℝ) ^ (-(3 / 2 : ℝ))
  have hS : 0 ≤ S := tsum_nonneg (fun ν => Real.rpow_nonneg (by positivity) _)
  let C : ℝ := 4 * Real.pi * K * (S + 1) / (1 - (ℓ : ℝ)⁻¹)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  let q : ℕ+ → ℝ := fun ν =>
    J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
      J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)
  have hq := g_bessel_series_summable hDLMF a (by omega : 0 < ℓ) hy
  have hmajor (ν : ℕ+) : |q ν| ≤
      2 * K * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) * (ν : ℝ) ^ (-(3 / 2 : ℝ)) :=
    bessel_difference_bound a hℓ hK hb hy ν
  have hbSum : |∑' ν : ℕ+, q ν| ≤
      2 * K * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) * S := by
    calc
      _ ≤ ∑' ν : ℕ+, |q ν| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hq.norm
      _ ≤ ∑' ν : ℕ+, 2 * K * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) *
          (ν : ℝ) ^ (-(3 / 2 : ℝ)) :=
        Summable.tsum_le_tsum hmajor hq.abs
          (pnat_three_halves_summable.mul_left _)
      _ = _ := tsum_mul_left
  have hp : Real.sqrt y * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) = y ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy.le, ← Real.rpow_add hy]
    norm_num
  rw [g_eq_bessel hDLMF a hℓ hy, abs_mul, abs_of_pos (by positivity :
    0 < 2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹))]
  calc
    _ ≤ (2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹)) *
        (2 * K * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) * S) :=
      mul_le_mul_of_nonneg_left hbSum (by positivity)
    _ = (4 * Real.pi * K * S / (1 - (ℓ : ℝ)⁻¹)) * y ^ (1 / 4 : ℝ) := by
      rw [← hp]
      ring
    _ ≤ C * y ^ (1 / 4 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy.le _)
      dsimp [C]
      apply div_le_div_of_nonneg_right _ hz.le
      nlinarith [Real.pi_pos]

end DepthAspect.MurmurationPointwiseBounds
