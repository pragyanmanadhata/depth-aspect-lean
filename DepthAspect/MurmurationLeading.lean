import DepthAspect.MurmurationOscillationSeries
import DepthAspect.BesselRemainder

/-! Exact normalization of the leading Bessel terms in (131), followed by
their absolutely summable bounds and the actual large-y remainder for g. -/
open scoped BigOperators
namespace DepthAspect.MurmurationLeading
open BesselFirstKind BesselRemainder MurmurationBesselSeries
  MurmurationPointwiseBounds MurmurationOscillationSeries

noncomputable def leadingTerm (a ℓ : ℕ) (y : ℝ) (ν : ℕ+) : ℝ :=
  (2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹)) *
    (leading (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
      leading (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν))

noncomputable def gLeading (a ℓ : ℕ) (y : ℝ) : ℝ := ∑' ν : ℕ+, leadingTerm a ℓ y ν

theorem sqrt_sqrt_eq_quarter {y : ℝ} (hy : 0 ≤ y) :
    Real.sqrt (Real.sqrt y) = y ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
  norm_num

/-- The factor √2 comes from the actual Bessel amplitude and the 2πx
prefactor. It is not inserted as a normalization assumption. -/
theorem leading_amplitude {x v : ℝ} (hx : 0 < x) (hv : 0 < v) :
    2 * Real.pi * x * Real.sqrt (2 / (Real.pi * (4 * Real.pi * v * x))) / v =
      Real.sqrt 2 * Real.sqrt x * v ^ (-(3 / 2 : ℝ)) := by
  have he : Real.pi * (4 * Real.pi * v * x) = ((2 * Real.pi) ^ 2 * v) * x := by ring
  have hs : Real.sqrt (2 / (Real.pi * (4 * Real.pi * v * x))) =
      Real.sqrt 2 / (2 * Real.pi * Real.sqrt v * Real.sqrt x) := by
    rw [he, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by positivity : 0 ≤ (2 * Real.pi) ^ 2 * v),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hvpow : v ^ (-(3 / 2 : ℝ)) = (v * Real.sqrt v)⁻¹ := by
    rw [Real.rpow_neg hv.le, Real.sqrt_eq_rpow]
    congr 1
    calc
      v ^ (3 / 2 : ℝ) = v ^ (1 + 1 / 2 : ℝ) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hv, Real.rpow_one]
  rw [hs, hvpow]
  calc
    _ = Real.sqrt 2 * (x / Real.sqrt x) / (v * Real.sqrt v) := by
      field_simp [Real.pi_ne_zero, ne_of_gt hv, ne_of_gt (Real.sqrt_pos.mpr hx),
        ne_of_gt (Real.sqrt_pos.mpr hv)]
      <;> ring
    _ = _ := by rw [Real.div_sqrt]; ring

theorem leading_scaled {x v : ℝ} (hx : 0 < x) (hv : 0 < v) (a : ℕ) :
    2 * Real.pi * x * (leading (2 * a + 1) (4 * Real.pi * v * x) / v) =
      Real.sqrt 2 * Real.sqrt x * v ^ (-(3 / 2 : ℝ)) *
        Real.cos (4 * Real.pi * v * x - phase a) := by
  have hp : ((2 * ((2 * a + 1 : ℕ) : ℝ) + 1) * Real.pi / 4) = phase a := by
    unfold phase
    push_cast
    ring
  unfold leading
  rw [hp]
  calc
    _ = (2 * Real.pi * x * Real.sqrt (2 / (Real.pi * (4 * Real.pi * v * x))) / v) *
        Real.cos (4 * Real.pi * v * x - phase a) := by ring
    _ = _ := by rw [leading_amplitude hx hv]

theorem leadingTerm_cos (a : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) {y : ℝ} (hy : 0 < y)
    (ν : ℕ+) : leadingTerm a ℓ y ν =
      (Real.sqrt 2 / (1 - (ℓ : ℝ)⁻¹)) * y ^ (1 / 4 : ℝ) *
        (ν : ℝ) ^ (-(3 / 2 : ℝ)) *
          (Real.cos (4 * Real.pi * ν * Real.sqrt y - phase a) -
            (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) *
              Real.cos (4 * Real.pi * ℓ * ν * Real.sqrt y - phase a)) := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hv : (0 : ℝ) < ν := by positivity
  have hl : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h₁ := leading_scaled hs hv a
  have h₂ := leading_scaled hs (mul_pos hl hv) a
  have harg : 4 * Real.pi * ((ℓ : ℝ) * ν) * Real.sqrt y =
      4 * Real.pi * ℓ * ν * Real.sqrt y := by ring
  rw [harg, Real.mul_rpow hl.le hv.le, sqrt_sqrt_eq_quarter hy.le] at h₂
  rw [sqrt_sqrt_eq_quarter hy.le] at h₁
  unfold leadingTerm
  calc
    _ = ((2 * Real.pi * Real.sqrt y *
          (leading (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ))) -
        (2 * Real.pi * Real.sqrt y *
          (leading (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)))) /
            (1 - (ℓ : ℝ)⁻¹) := by ring
    _ = _ := by rw [h₁, h₂]; ring

theorem leadingTerm_bound (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {y : ℝ} (hy : 0 < y)
    (ν : ℕ+) : ‖leadingTerm a ℓ y ν‖ ≤
      (Real.sqrt 2 / (1 - (ℓ : ℝ)⁻¹) * (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ)))) *
        y ^ (1 / 4 : ℝ) * (ν : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by linarith [inv_lt_one_of_one_lt₀ hl]
  have he : 0 ≤ (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [leadingTerm_cos a (by omega) hy, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt 2 / (1 - (ℓ : ℝ)⁻¹)) *
      y ^ (1 / 4 : ℝ) * (ν : ℝ) ^ (-(3 / 2 : ℝ)))]
  have hc : |Real.cos (4 * Real.pi * ν * Real.sqrt y - phase a) -
      (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) *
        Real.cos (4 * Real.pi * ℓ * ν * Real.sqrt y - phase a)| ≤
      1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) := by
    apply (abs_sub _ _).trans
    apply add_le_add (Real.abs_cos_le_one _)
    rw [abs_mul, abs_of_nonneg he]
    exact mul_le_of_le_one_right he (Real.abs_cos_le_one _)
  calc
    _ ≤ ((Real.sqrt 2 / (1 - (ℓ : ℝ)⁻¹)) * y ^ (1 / 4 : ℝ) *
        (ν : ℝ) ^ (-(3 / 2 : ℝ))) * (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

theorem leading_summable (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {y : ℝ} (hy : 0 < y) :
    Summable (leadingTerm a ℓ y) :=
  (pnat_three_halves_summable.mul_left _).of_norm_bounded (leadingTerm_bound a hℓ hy)

theorem gLeading_bound (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, ∀ y : ℝ, 0 < y → |gLeading a ℓ y| ≤ C * y ^ (1 / 4 : ℝ) := by
  let C := Real.sqrt 2 / (1 - (ℓ : ℝ)⁻¹) *
    (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ))) * zetaThreeHalves
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by linarith [inv_lt_one_of_one_lt₀ hl]
  have hζ : 0 < zetaThreeHalves := zero_lt_one.trans_le zetaThreeHalves_ge_one
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro y hy
  calc
    _ ≤ ∑' ν : ℕ+, ‖leadingTerm a ℓ y ν‖ :=
      norm_tsum_le_tsum_norm (leading_summable a hℓ hy).norm
    _ ≤ ∑' ν : ℕ+, (Real.sqrt 2 / (1 - (ℓ : ℝ)⁻¹) *
        (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ)))) * y ^ (1 / 4 : ℝ) *
          (ν : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Summable.tsum_le_tsum (leadingTerm_bound a hℓ hy) (leading_summable a hℓ hy).norm
        (pnat_three_halves_summable.mul_left _)
    _ = _ := by rw [tsum_mul_left]; dsimp [C, zetaThreeHalves]; ring

/-- The large Bessel remainder after division by the actual frequency.
The weaker ν^-3/2 majorant is already summable and sufficient here. -/
theorem scaled_remainder_bound {m : ℕ} {C β x v : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t : ℝ, 1 ≤ t → |J m t - leading m t| ≤ C * t ^ (-(3 / 2 : ℝ)))
    (hβ : 1 ≤ β) (hx : 1 ≤ x) (hv : 1 ≤ v) :
    |(J m (β * v * x) - leading m (β * v * x)) / v| ≤
      C * x ^ (-(3 / 2 : ℝ)) * v ^ (-(3 / 2 : ℝ)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hv0 : 0 < v := zero_lt_one.trans_le hv
  have harg : 1 ≤ β * v * x :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hβ hv) hx
  have hcomp : v * x ≤ β * v * x := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ hv0.le) hx0.le
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hv0 hx0) hcomp
    (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  calc
    _ = |J m (β * v * x) - leading m (β * v * x)| / v := by
      rw [abs_div, abs_of_pos hv0]
    _ ≤ |J m (β * v * x) - leading m (β * v * x)| := div_le_self (abs_nonneg _) hv
    _ ≤ C * (β * v * x) ^ (-(3 / 2 : ℝ)) := hb _ harg
    _ ≤ C * (v * x) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hp hC
    _ = _ := by rw [Real.mul_rpow hv0.le hx0.le]; ring

/-- Summing the actual Bessel remainders gives the local asymptotic needed
before the arithmetic d-cutoff in (132). -/
theorem g_leading_remainder (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |g a ℓ y - gLeading a ℓ y| ≤ C * y ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨D, hD, hb⟩ := large_remainder_bound hDLMF (2 * a + 1)
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by linarith [inv_lt_one_of_one_lt₀ hl]
  have hζ : 0 < zetaThreeHalves := zero_lt_one.trans_le zetaThreeHalves_ge_one
  let C := 4 * Real.pi * D * zetaThreeHalves / (1 - (ℓ : ℝ)⁻¹)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro y hy
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hs : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  let P := 2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹)
  have hP : 0 < P := by dsimp [P]; positivity
  let j : ℕ+ → ℝ := fun ν => P *
    (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
      J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν))
  have hj : Summable j := (g_bessel_series_summable hDLMF a (by omega) hy0).mul_left P
  have he : Summable (fun ν => j ν - leadingTerm a ℓ y ν) :=
    hj.sub (leading_summable a hℓ hy0)
  have hpower : Real.sqrt y * (Real.sqrt y) ^ (-(3 / 2 : ℝ)) =
      y ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]
    norm_num
  have hterm (ν : ℕ+) : ‖j ν - leadingTerm a ℓ y ν‖ ≤
      (4 * Real.pi * D / (1 - (ℓ : ℝ)⁻¹)) * y ^ (-(1 / 4 : ℝ)) *
        (ν : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hv : (1 : ℝ) ≤ ν := by exact_mod_cast ν.pos
    have hπ : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.two_le_pi]
    have h₁ := scaled_remainder_bound hD.le hb hπ hs hv
    have h₂ := scaled_remainder_bound hD.le hb
      (by nlinarith : (1 : ℝ) ≤ 4 * Real.pi * ℓ) hs hv
    have h₂' : |(J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) -
        leading (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y)) / ((ℓ : ℝ) * ν)| ≤
        D * (Real.sqrt y) ^ (-(3 / 2 : ℝ)) * (ν : ℝ) ^ (-(3 / 2 : ℝ)) := by
      calc
        _ = |(J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) -
          leading (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y)) / (ν : ℝ)| / (ℓ : ℝ) := by
            simp only [abs_div, abs_mul, abs_of_pos (zero_lt_one.trans_le hv),
              abs_of_pos (zero_lt_one.trans hl)]
            ring
        _ ≤ |(J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) -
          leading (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y)) / (ν : ℝ)| :=
            div_le_self (abs_nonneg _) hl.le
        _ ≤ _ := h₂
    have halg : j ν - leadingTerm a ℓ y ν = P *
        ((J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) -
          leading (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y)) / (ν : ℝ) -
        (J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) -
          leading (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y)) / ((ℓ : ℝ) * ν)) := by
      dsimp [j, leadingTerm, P]
      ring
    rw [halg, Real.norm_eq_abs, abs_mul, abs_of_pos hP]
    calc
      _ ≤ P * (2 * D * (Real.sqrt y) ^ (-(3 / 2 : ℝ)) *
          (ν : ℝ) ^ (-(3 / 2 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hP.le
        exact (abs_sub _ _).trans (by linarith)
      _ = _ := by
        dsimp [P]
        calc
          _ = (4 * Real.pi * D / (1 - (ℓ : ℝ)⁻¹)) *
              (Real.sqrt y * (Real.sqrt y) ^ (-(3 / 2 : ℝ))) *
                (ν : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
          _ = _ := by rw [hpower]
  have heq : g a ℓ y - gLeading a ℓ y = ∑' ν : ℕ+, (j ν - leadingTerm a ℓ y ν) := by
    rw [hj.tsum_sub (leading_summable a hℓ hy0)]
    unfold gLeading j
    rw [tsum_mul_left, g_eq_bessel hDLMF a hℓ hy0]
  rw [heq]
  calc
    _ ≤ ∑' ν : ℕ+, ‖j ν - leadingTerm a ℓ y ν‖ := norm_tsum_le_tsum_norm he.norm
    _ ≤ ∑' ν : ℕ+, (4 * Real.pi * D / (1 - (ℓ : ℝ)⁻¹)) *
        y ^ (-(1 / 4 : ℝ)) * (ν : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Summable.tsum_le_tsum hterm he.norm (pnat_three_halves_summable.mul_left _)
    _ = _ := by rw [tsum_mul_left]; dsimp [C, zetaThreeHalves]; ring

end DepthAspect.MurmurationLeading
