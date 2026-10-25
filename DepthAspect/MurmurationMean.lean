import DepthAspect.MurmurationArithmeticIntegral
import DepthAspect.MurmurationScaledPrimitive
import DepthAspect.ArithmeticResidue

/-! The actual logarithmic mean (130), from the proved arithmetic masses
and the computed Bessel primitive. -/
open MeasureTheory
open scoped BigOperators
namespace DepthAspect.MurmurationMean
open BesselFirstKind MurmurationArithmetic MurmurationBesselSeries
open MurmurationIntegralSeries MurmurationIntegralLimit MurmurationIntegralError
open MurmurationArithmeticIntegral MurmurationScaledPrimitive ArithmeticWeights

/-- The large-argument error scales with the half moment in (125). -/
theorem scaled_large_error_power {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 0 < d) :
    (x ^ 2 / (d : ℝ) ^ 2) ^ (-(1 / 4 : ℝ)) =
      x ^ (-(1 / 2 : ℝ)) * Real.sqrt d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.div_rpow (sq_nonneg _) (sq_nonneg _),
    ← Real.rpow_natCast_mul hx.le 2 (-(1 / 4 : ℝ)),
    ← Real.rpow_natCast_mul hdR.le 2 (-(1 / 4 : ℝ))]
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (-(1 / 4)) = -(1 / 2) by norm_num]
  rw [div_eq_mul_inv, ← Real.rpow_neg hdR.le]
  norm_num only [neg_neg]
  rw [← Real.sqrt_eq_rpow]

/-- Replacing G(x²/d²) by its limit for d≤x costs a bounded total, and the
remaining d>x tail costs a bounded total. Both estimates use literal
arithmetic coefficients and the actual real cutoff. -/
theorem primitive_sum_cutoff_bound (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ K > 0, ∀ x : ℝ, 1 ≤ x →
      |(∑' d : ℕ, c ℓ d * G a ℓ (x ^ 2 / (d : ℝ) ^ 2)) -
        limitValue ℓ * partialC ℓ x| ≤ K := by
  obtain ⟨A, hA, hlarge⟩ := G_large_error hDLMF a hℓ.two_le
  obtain ⟨D, hD, hsmall⟩ := G_global_sqrt_bound hDLMF a hℓ.two_le
  let q : ℝ := 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hq : 0 < q := by
    dsimp [q]
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by norm_num : -(1 / 2 : ℝ) < 0)
    linarith
  let K : ℝ := A * dyadicMassConstant ℓ / q + 2 * D * dyadicMassConstant ℓ
  have hmass : 0 < dyadicMassConstant ℓ := zero_lt_one.trans_le (dyadicMassConstant_ge_one ℓ)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro x hx
  classical
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let S := Finset.Ioc 0 ⌊x⌋₊
  let e : ℕ → ℝ := fun d => c ℓ d * G a ℓ (x ^ 2 / (d : ℝ) ^ 2) -
    if d ∈ S then limitValue ℓ * c ℓ d else 0
  let head : ℕ → ℝ := fun d =>
    if d ∈ S then A * x ^ (-(1 / 2 : ℝ)) * (c ℓ d * Real.sqrt d) else 0
  let tail : ℕ → ℝ := fun d => D * x * tailWeight ℓ 1 x d
  have hfinite : Summable (fun d : ℕ => if d ∈ S then limitValue ℓ * c ℓ d else 0) :=
    summable_of_ne_finset_zero (s := S) (fun d hd => if_neg hd)
  have he : Summable e :=
    (scaled_primitive_summable hDLMF a hℓ.two_le (sq_pos_of_pos hx0)).sub hfinite
  have hh : Summable head := summable_of_ne_finset_zero (s := S) (fun d hd => if_neg hd)
  have ht : Summable tail := (tail_moment ℓ hx0 (by norm_num : (0 : ℝ) < 1)).1.mul_left _
  have hb (d : ℕ) : ‖e d‖ ≤ head d + tail d := by
    by_cases hdS : d ∈ S
    · have hd0 : 0 < d := (Finset.mem_Ioc.mp hdS).1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
      have hdx : (d : ℝ) ≤ x :=
        (by exact_mod_cast (Finset.mem_Ioc.mp hdS).2 : (d : ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx0.le)
      have hz : 1 ≤ x ^ 2 / (d : ℝ) ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hdR)).mpr (by nlinarith)
      have htail : tail d = 0 := by simp [tail, tailWeight, not_lt.mpr hdx]
      rw [htail, add_zero]
      dsimp [e, head]
      rw [if_pos hdS, if_pos hdS]
      have he : c ℓ d * G a ℓ (x ^ 2 / (d : ℝ) ^ 2) - limitValue ℓ * c ℓ d =
          c ℓ d * (G a ℓ (x ^ 2 / (d : ℝ) ^ 2) - limitValue ℓ) := by ring
      rw [he, abs_mul, abs_of_nonneg (c_nonneg ℓ d)]
      calc
        _ ≤ c ℓ d * (A * (x ^ 2 / (d : ℝ) ^ 2) ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hlarge _ hz) (c_nonneg ℓ d)
        _ = _ := by rw [scaled_large_error_power hx0 hd0]; ring
    · have hhead : head d = 0 := by simp [head, hdS]
      rw [hhead, zero_add]
      by_cases hd0 : d = 0
      · subst d
        simp [e, tail, tailWeight, S]
      have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
      have hdx : x < (d : ℝ) := by
        apply (Nat.floor_lt hx0.le).mp
        have : ¬ d ≤ ⌊x⌋₊ := fun hd => hdS (Finset.mem_Ioc.mpr ⟨hdpos, hd⟩)
        omega
      have hweight : tailWeight ℓ 1 x d = b ℓ d := by
        rw [tailWeight, if_pos hdx, Real.rpow_neg_one, c_apply]
        field_simp [ne_of_gt hdR]
        <;> ring
      dsimp [e]
      rw [if_neg hdS, sub_zero]
      have hd := scaled_primitive_bound a ℓ hD.le hsmall (sq_pos_of_pos hx0) d
      simpa only [Real.norm_eq_abs, Real.sqrt_sq hx0.le, tail, hweight] using hd
  have heq : (∑' d : ℕ, e d) =
      (∑' d : ℕ, c ℓ d * G a ℓ (x ^ 2 / (d : ℝ) ^ 2)) -
        limitValue ℓ * partialC ℓ x := by
    dsimp only [e]
    rw [(scaled_primitive_summable hDLMF a hℓ.two_le (sq_pos_of_pos hx0)).tsum_sub hfinite]
    have hfinite_tsum : (∑' d : ℕ, if d ∈ S then limitValue ℓ * c ℓ d else 0) =
        limitValue ℓ * partialC ℓ x := by
      rw [tsum_eq_sum (s := S) (fun d hd => if_neg hd)]
      simp only [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum]
      rfl
    rw [hfinite_tsum]
  have hheadsum : (∑' d : ℕ, head d) =
      A * x ^ (-(1 / 2 : ℝ)) * ∑ d ∈ S, c ℓ d * Real.sqrt d := by
    rw [tsum_eq_sum (s := S) (fun d hd => if_neg hd)]
    simp only [head, Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum]
  have htailsum : (∑' d : ℕ, tail d) = D * x * ∑' d : ℕ, tailWeight ℓ 1 x d :=
    by dsimp only [tail]; rw [tsum_mul_left]
  have hcancel : x ^ (-(1 / 2 : ℝ)) * Real.sqrt x = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    norm_num
  have hheadbound : (∑' d : ℕ, head d) ≤ A * dyadicMassConstant ℓ / q := by
    rw [hheadsum]
    calc
      _ ≤ A * x ^ (-(1 / 2 : ℝ)) *
          (dyadicMassConstant ℓ * Real.sqrt x / q) :=
        mul_le_mul_of_nonneg_left (prefix_half_moment ℓ hx) (by positivity)
      _ = _ := by
        calc
          _ = (A * dyadicMassConstant ℓ / q) *
              (x ^ (-(1 / 2 : ℝ)) * Real.sqrt x) := by ring
          _ = _ := by rw [hcancel, mul_one]
  have htailbound : (∑' d : ℕ, tail d) ≤ 2 * D * dyadicMassConstant ℓ := by
    rw [htailsum]
    calc
      _ ≤ D * x * (2 * dyadicMassConstant ℓ / x) :=
        mul_le_mul_of_nonneg_left (tail_inverse_moment ℓ hx) (by positivity)
      _ = _ := by field_simp
  rw [← heq]
  calc
    |∑' d : ℕ, e d| ≤ ∑' d : ℕ, ‖e d‖ := norm_tsum_le_tsum_norm he.norm
    _ ≤ ∑' d : ℕ, (head d + tail d) :=
      Summable.tsum_le_tsum hb he.norm (hh.add ht)
    _ = (∑' d : ℕ, head d) + ∑' d : ℕ, tail d := hh.tsum_add ht
    _ ≤ K := add_le_add hheadbound htailbound

/-- The residue and Bessel constants multiply to exactly one. -/
theorem mean_normalization {ℓ : ℕ} (hℓ : ℓ.Prime) :
    B ℓ * R ℓ * limitValue ℓ = 1 := by
  rw [B_mul_R hℓ]
  unfold limitValue
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hℓ1 : (ℓ : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hℓ0, hℓ1, Real.pi_ne_zero]
  <;> ring

/-- Equation (130), with the integral of the literal arithmetic density
and a constant uniform in its upper endpoint. -/
theorem M_logarithmic_mean (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ Y : ℝ, 1 ≤ Y →
      |(∫ y : ℝ in (1)..Y, M a ℓ y / y) - (1 / 2 : ℝ) * Real.log Y| ≤ C := by
  obtain ⟨K, hK, hk⟩ := primitive_sum_cutoff_bound hDLMF a hℓ
  obtain ⟨D, hD, hd⟩ := lower_endpoint_bound hDLMF a hℓ.two_le
  let E : ℝ := ((14 / 3 : ℝ) + |Real.eulerMascheroniConstant|) * coefficientMoment ℓ
  have hE : 0 ≤ E := by dsimp [E, coefficientMoment]; positivity
  let C : ℝ := B ℓ * K + |B ℓ * limitValue ℓ| * (E + |constantTerm ℓ|) + D
  have hB := B_pos ℓ
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro Y hY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  let x := Real.sqrt Y
  have hx : 1 ≤ x := by simpa [x] using Real.sqrt_le_sqrt hY
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hx2 : x ^ 2 = Y := Real.sq_sqrt hY0.le
  have hlog : Real.log x = (1 / 2 : ℝ) * Real.log Y := by
    dsimp [x]
    rw [Real.log_sqrt hY0.le]
    ring
  have hs := summatory_asymptotic ℓ hx
  have hp : x ^ (-1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hpartial : |partialC ℓ x - R ℓ * Real.log x| ≤ E + |constantTerm ℓ| := by
    calc
      _ ≤ |partialC ℓ x - (R ℓ * Real.log x + constantTerm ℓ)| + |constantTerm ℓ| := by
        calc
          _ = |(partialC ℓ x - (R ℓ * Real.log x + constantTerm ℓ)) + constantTerm ℓ| := by
            congr 1; ring
          _ ≤ _ := abs_add_le _ _
      _ ≤ E + |constantTerm ℓ| := add_le_add (hs.trans (mul_le_of_le_one_right hE hp)) (le_refl _)
  have hupper := hk x hx
  rw [hx2] at hupper
  have hseries := (M_log_integral_eq_series hDLMF a hℓ hY).2
  have hsY := scaled_primitive_summable hDLMF a hℓ.two_le hY0
  have hs1 := scaled_primitive_summable hDLMF a hℓ.two_le (by norm_num : (0 : ℝ) < 1)
  simp_rw [mul_sub] at hseries
  rw [hsY.tsum_sub hs1] at hseries
  have he : (∫ y : ℝ in (1)..Y, M a ℓ y / y) - (1 / 2 : ℝ) * Real.log Y =
      B ℓ * ((∑' d : ℕ, c ℓ d * G a ℓ (Y / (d : ℝ) ^ 2)) - limitValue ℓ * partialC ℓ x) +
      (B ℓ * limitValue ℓ) * (partialC ℓ x - R ℓ * Real.log x) -
      B ℓ * ∑' d : ℕ, c ℓ d * G a ℓ (1 / (d : ℝ) ^ 2) := by
    rw [hseries, ← hlog]
    have hn := mean_normalization hℓ
    have hnlog := congrArg (fun z : ℝ => z * Real.log x) hn
    nlinarith [hnlog]
  rw [he]
  calc
    _ ≤ |B ℓ * ((∑' d : ℕ, c ℓ d * G a ℓ (Y / (d : ℝ) ^ 2)) - limitValue ℓ * partialC ℓ x)| +
        |(B ℓ * limitValue ℓ) * (partialC ℓ x - R ℓ * Real.log x)| +
        |B ℓ * ∑' d : ℕ, c ℓ d * G a ℓ (1 / (d : ℝ) ^ 2)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ C := by
      rw [abs_mul, abs_of_pos (B_pos ℓ), abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hupper (B_pos ℓ).le)
        (mul_le_mul_of_nonneg_left hpartial (abs_nonneg _))) hd

end DepthAspect.MurmurationMean
