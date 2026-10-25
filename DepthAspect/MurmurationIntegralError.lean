import DepthAspect.MurmurationIntegralLimit

/-! The quantitative large-argument error in (129). -/
open MeasureTheory Set
open scoped BigOperators
namespace DepthAspect.MurmurationIntegralError
open BesselFirstKind BesselBounds MurmurationIntegralSeries MurmurationIntegralLimit

/-- Every Bessel argument in (129) is at least sqrt Z. This yields the
uniform quarter-power remainder before the summation over ν. -/
theorem I_scaled_error {a : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hI : ∀ T : ℝ, 1 ≤ T → |I a T - 1| ≤ K * T ^ (-(1 / 2 : ℝ)))
    {β Z : ℝ} (hβ : 1 ≤ β) (hZ : 1 ≤ Z) :
    |I a (β * Real.sqrt Z) - 1| ≤ K * Z ^ (-(1 / 4 : ℝ)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hs : 0 < Real.sqrt Z := Real.sqrt_pos.2 hZ0
  have hs1 : 1 ≤ Real.sqrt Z := by simpa using Real.sqrt_le_sqrt hZ
  have harg : Real.sqrt Z ≤ β * Real.sqrt Z := by nlinarith
  calc
    _ ≤ K * (β * Real.sqrt Z) ^ (-(1 / 2 : ℝ)) := hI _ (hs1.trans harg)
    _ ≤ K * (Real.sqrt Z) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs harg (by norm_num)) hK
    _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ0.le]; norm_num

/-- The difference from the limiting integrated term has a summable
inverse-square majorant with a common Z^{-1/4} factor. -/
theorem integrated_error_bound {a : ℕ} {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    {K : ℝ} (hK : 0 ≤ K)
    (hI : ∀ T : ℝ, 1 ≤ T → |I a T - 1| ≤ K * T ^ (-(1 / 2 : ℝ)))
    {Z : ℝ} (hZ : 1 ≤ Z) (ν : ℕ+) :
    ‖integratedTerm a ℓ Z ν - ((ν : ℝ) ^ 2)⁻¹ * (1 - ((ℓ : ℝ) ^ 2)⁻¹)‖ ≤
      (K * (1 + ((ℓ : ℝ) ^ 2)⁻¹) * Z ^ (-(1 / 4 : ℝ))) * ((ν : ℝ) ^ 2)⁻¹ := by
  have hν : (1 : ℝ) ≤ ν := by exact_mod_cast ν.pos
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast (by omega : 1 ≤ ℓ)
  have hπ : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.two_le_pi]
  have h1 := I_scaled_error hK hI (show 1 ≤ 4 * Real.pi * ν by nlinarith) hZ
  have h2 := I_scaled_error hK hI (show 1 ≤ 4 * Real.pi * ℓ * ν by
    have hprod : 1 ≤ 4 * Real.pi * ℓ := by nlinarith
    nlinarith) hZ
  have he : integratedTerm a ℓ Z ν - ((ν : ℝ) ^ 2)⁻¹ * (1 - ((ℓ : ℝ) ^ 2)⁻¹) =
      ((ν : ℝ) ^ 2)⁻¹ * ((I a (4 * Real.pi * ν * Real.sqrt Z) - 1) -
        ((ℓ : ℝ) ^ 2)⁻¹ * (I a (4 * Real.pi * ℓ * ν * Real.sqrt Z) - 1)) := by
    unfold integratedTerm
    ring
  rw [he, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((ν : ℝ) ^ 2)⁻¹)]
  have h2' : |((ℓ : ℝ) ^ 2)⁻¹ * (I a (4 * Real.pi * ℓ * ν * Real.sqrt Z) - 1)| ≤
      ((ℓ : ℝ) ^ 2)⁻¹ * (K * Z ^ (-(1 / 4 : ℝ))) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((ℓ : ℝ) ^ 2)⁻¹)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc
    _ ≤ ((ν : ℝ) ^ 2)⁻¹ *
        (K * Z ^ (-(1 / 4 : ℝ)) + ((ℓ : ℝ) ^ 2)⁻¹ * (K * Z ^ (-(1 / 4 : ℝ)))) :=
      mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2')) (by positivity)
    _ = _ := by ring

/-- The actual G has the quantitative error stated in (129). -/
theorem G_large_error (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∃ C > 0, ∀ Z : ℝ, 1 ≤ Z →
      |G a ℓ Z - limitValue ℓ| ≤ C * Z ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨K, hK, _, hI⟩ := odd_integral_bounds hDLMF a
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  let C : ℝ := (1 / (1 - (ℓ : ℝ)⁻¹)) *
    (K * (1 + ((ℓ : ℝ) ^ 2)⁻¹)) * (Real.pi ^ 2 / 6)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ
  let e : ℕ+ → ℝ := fun ν => integratedTerm a ℓ Z ν -
    ((ν : ℝ) ^ 2)⁻¹ * (1 - ((ℓ : ℝ) ^ 2)⁻¹)
  have hs1 := integratedTerm_summable hDLMF a (by omega : 0 < ℓ)
    (zero_le_one.trans hZ)
  have hs2 := inverse_squares_summable.mul_right (1 - ((ℓ : ℝ) ^ 2)⁻¹)
  have he : G a ℓ Z - limitValue ℓ =
      (1 / (1 - (ℓ : ℝ)⁻¹)) * ∑' ν : ℕ+, e ν := by
    rw [G_eq_series hDLMF a hℓ (zero_le_one.trans hZ),
      ← limiting_constant_algebra hℓ]
    rw [show (∑' ν : ℕ+, e ν) =
        (∑' ν : ℕ+, integratedTerm a ℓ Z ν) -
          (1 - ((ℓ : ℝ) ^ 2)⁻¹) * (Real.pi ^ 2 / 6) by
      rw [show (∑' ν : ℕ+, e ν) = _ from hs1.tsum_sub hs2,
        tsum_mul_right, inverse_squares_tsum]
      ring]
    change _ = _
    unfold integratedTerm
    ring
  have hs : Summable e := hs1.sub hs2
  have hbound (ν : ℕ+) := integrated_error_bound hℓ hK.le hI hZ ν
  have hsum : |∑' ν : ℕ+, e ν| ≤
      (K * (1 + ((ℓ : ℝ) ^ 2)⁻¹) * Z ^ (-(1 / 4 : ℝ))) * (Real.pi ^ 2 / 6) := by
    calc
      _ ≤ ∑' ν : ℕ+, ‖e ν‖ := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' ν : ℕ+, (K * (1 + ((ℓ : ℝ) ^ 2)⁻¹) *
          Z ^ (-(1 / 4 : ℝ))) * ((ν : ℝ) ^ 2)⁻¹ :=
        Summable.tsum_le_tsum hbound hs.norm (inverse_squares_summable.mul_left _)
      _ = _ := by rw [tsum_mul_left, inverse_squares_tsum]
  rw [he, abs_mul, abs_of_pos (one_div_pos.mpr hz)]
  exact (mul_le_mul_of_nonneg_left hsum (one_div_pos.mpr hz).le).trans_eq (by dsimp [C]; ring)

end DepthAspect.MurmurationIntegralError
