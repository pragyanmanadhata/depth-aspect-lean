import DepthAspect.MurmurationLeadingDivisors

/-! The three actual cutoff errors (132), the expansion (120), and (133). -/
open scoped BigOperators
namespace DepthAspect.MurmurationExpansion
open ArithmeticWeights BesselFirstKind MurmurationArithmetic MurmurationBesselSeries
  MurmurationPointwiseBounds MurmurationDivisorExpansion MurmurationLeading
  MurmurationLeadingDivisors MurmurationOscillationSeries

/-- All three errors are estimated on the literal real cutoff d≤sqrt(y).
The sums and their summability are supplied by the preceding proved identities. -/
theorem M_leading_error (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |M a ℓ y - y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y)| ≤ C := by
  obtain ⟨D, hD, hrem⟩ := g_leading_remainder hDLMF a hℓ.two_le
  obtain ⟨E, hE, hsmall⟩ := g_small_bound a hℓ.two_le
  obtain ⟨F, hF, hlead⟩ := gLeading_bound a hℓ.two_le
  let ρ := 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by norm_num : -(1 / 2 : ℝ) < 0)
    linarith
  let C := B ℓ * (D * dyadicMassConstant ℓ / ρ +
    2 * E * dyadicMassConstant ℓ + F * dyadicMassConstant ℓ / ρ)
  have hmass : 0 < dyadicMassConstant ℓ := zero_lt_one.trans_le (dyadicMassConstant_ge_one ℓ)
  refine ⟨C, by have := B_pos ℓ; dsimp [C]; positivity, ?_⟩
  intro y hy
  classical
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hx : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy
  have hx0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  let S := Finset.Ioc 0 ⌊Real.sqrt y⌋₊
  let e : ℕ → ℝ := fun d => c ℓ d *
    (g a ℓ (y / (d : ℝ) ^ 2) - gLeading a ℓ (y / (d : ℝ) ^ 2))
  let head : ℕ → ℝ := fun d => if d ∈ S then
    D * y ^ (-(1 / 4 : ℝ)) * (c ℓ d * Real.sqrt d) else 0
  let tail₁ : ℕ → ℝ := fun d => E * Real.sqrt y * tailWeight ℓ 1 (Real.sqrt y) d
  let tail₂ : ℕ → ℝ := fun d => F * y ^ (1 / 4 : ℝ) *
    tailWeight ℓ (1 / 2) (Real.sqrt y) d
  have hg := (M_divisor_sum a hℓ hy0).1
  have hl := scaled_leading_summable a hℓ.two_le hy0
  have he : Summable e := (hg.sub hl).congr (fun d => by dsimp [e] <;> ring)
  have hh : Summable head := summable_of_ne_finset_zero (s := S) (fun d hd => if_neg hd)
  have ht₁ : Summable tail₁ := (tail_moment ℓ hx0 (by norm_num : (0 : ℝ) < 1)).1.mul_left _
  have ht₂ : Summable tail₂ := (tail_moment ℓ hx0 (by norm_num : (0 : ℝ) < 1 / 2)).1.mul_left _
  have hb (d : ℕ) : ‖e d‖ ≤ head d + tail₁ d + tail₂ d := by
    by_cases hd0 : d = 0
    · subst d
      simp [e, head, tail₁, tail₂, tailWeight, S, not_lt.mpr hx0.le]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hydiv : 0 < y / (d : ℝ) ^ 2 := div_pos hy0 (sq_pos_of_pos hdR)
    by_cases hdS : d ∈ S
    · have hdx : (d : ℝ) ≤ Real.sqrt y :=
        (by exact_mod_cast (Finset.mem_Ioc.mp hdS).2 : (d : ℝ) ≤ ⌊Real.sqrt y⌋₊).trans
          (Nat.floor_le hx0.le)
      have hz : 1 ≤ y / (d : ℝ) ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hdR)).mpr
        nlinarith [Real.sq_sqrt hy0.le]
      simp only [head, if_pos hdS, tail₁, tail₂, tailWeight,
        if_neg (not_lt.mpr hdx), mul_zero, add_zero]
      dsimp [e]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (c_nonneg ℓ d)]
      calc
        _ ≤ c ℓ d * (D * (y / (d : ℝ) ^ 2) ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hrem _ hz) (c_nonneg ℓ d)
        _ = _ := by rw [scaled_negative_quarter hy0 hdpos] <;> ring
    · have hdx : Real.sqrt y < (d : ℝ) := by
        apply (Nat.floor_lt hx0.le).mp
        have : ¬ d ≤ ⌊Real.sqrt y⌋₊ := fun hd => hdS (Finset.mem_Ioc.mpr ⟨hdpos, hd⟩)
        omega
      have hz : y / (d : ℝ) ^ 2 ≤ 1 := by
        apply (div_le_iff₀ (sq_pos_of_pos hdR)).mpr
        nlinarith [Real.sq_sqrt hy0.le]
      have h₁ : c ℓ d * |g a ℓ (y / (d : ℝ) ^ 2)| ≤ tail₁ d := by
        calc
          _ ≤ c ℓ d * (E * Real.sqrt (y / (d : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hsmall _ hydiv hz) (c_nonneg ℓ d)
          _ = _ := by
            rw [sqrt_div_nat_sq hy0.le d]
            simp only [tail₁, tailWeight, if_pos hdx, Real.rpow_neg_one]
            ring
      have h₂ : c ℓ d * |gLeading a ℓ (y / (d : ℝ) ^ 2)| ≤ tail₂ d := by
        calc
          _ ≤ c ℓ d * (F * (y / (d : ℝ) ^ 2) ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (hlead _ hydiv) (c_nonneg ℓ d)
          _ = _ := by
            rw [scaled_quarter hy0 hdpos]
            simp only [tail₂, tailWeight, if_pos hdx]
            ring
      simp only [head, if_neg hdS, zero_add]
      dsimp [e]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (c_nonneg ℓ d)]
      exact (mul_le_mul_of_nonneg_left (abs_sub _ _) (c_nonneg ℓ d)).trans
        (by linarith)
  have hheadsum : (∑' d : ℕ, head d) = D * y ^ (-(1 / 4 : ℝ)) *
      ∑ d ∈ S, c ℓ d * Real.sqrt d := by
    rw [tsum_eq_sum (s := S) (fun d hd => if_neg hd)]
    simp only [head, Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum]
  have hcancel₁ : y ^ (-(1 / 4 : ℝ)) * Real.sqrt (Real.sqrt y) = 1 := by
    rw [sqrt_sqrt_eq_quarter hy0.le, ← Real.rpow_add hy0]
    norm_num
  have hcancel₂ : y ^ (1 / 4 : ℝ) * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy0.le, ← Real.rpow_add hy0]
    norm_num
  have hheadbound : (∑' d : ℕ, head d) ≤ D * dyadicMassConstant ℓ / ρ := by
    rw [hheadsum]
    calc
      _ ≤ D * y ^ (-(1 / 4 : ℝ)) *
          (dyadicMassConstant ℓ * Real.sqrt (Real.sqrt y) / ρ) :=
        mul_le_mul_of_nonneg_left (prefix_half_moment ℓ hx) (by positivity)
      _ = _ := by
        calc
          _ = (D * dyadicMassConstant ℓ / ρ) *
              (y ^ (-(1 / 4 : ℝ)) * Real.sqrt (Real.sqrt y)) := by ring
          _ = _ := by rw [hcancel₁, mul_one]
  have htail₁bound : (∑' d : ℕ, tail₁ d) ≤ 2 * E * dyadicMassConstant ℓ := by
    dsimp only [tail₁]
    rw [tsum_mul_left]
    calc
      _ ≤ E * Real.sqrt y * (2 * dyadicMassConstant ℓ / Real.sqrt y) :=
        mul_le_mul_of_nonneg_left (tail_inverse_moment ℓ hx) (by positivity)
      _ = _ := by field_simp <;> ring
  have htail₂bound : (∑' d : ℕ, tail₂ d) ≤ F * dyadicMassConstant ℓ / ρ := by
    dsimp only [tail₂]
    rw [tsum_mul_left]
    calc
      _ ≤ F * y ^ (1 / 4 : ℝ) *
          (dyadicMassConstant ℓ * (Real.sqrt y) ^ (-(1 / 2 : ℝ)) / ρ) :=
        mul_le_mul_of_nonneg_left (tail_half_moment ℓ hx) (by positivity)
      _ = _ := by
        calc
          _ = (F * dyadicMassConstant ℓ / ρ) *
              (y ^ (1 / 4 : ℝ) * (Real.sqrt y) ^ (-(1 / 2 : ℝ))) := by ring
          _ = _ := by rw [hcancel₂, mul_one]
  have heq : M a ℓ y - y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y) = B ℓ * ∑' d : ℕ, e d := by
    rw [(M_divisor_sum a hℓ hy0).2, ← leading_divisor_series_eq a hℓ hy0, ← mul_sub]
    rw [← hg.tsum_sub hl]
    congr 1
    apply tsum_congr
    intro d
    dsimp [e]
    ring
  have hsbound : |∑' d : ℕ, e d| ≤ D * dyadicMassConstant ℓ / ρ +
      2 * E * dyadicMassConstant ℓ + F * dyadicMassConstant ℓ / ρ := by
    calc
      _ ≤ ∑' d : ℕ, ‖e d‖ := norm_tsum_le_tsum_norm he.norm
      _ ≤ ∑' d : ℕ, (head d + tail₁ d + tail₂ d) :=
        Summable.tsum_le_tsum hb he.norm ((hh.add ht₁).add ht₂)
      _ = (∑' d : ℕ, head d) + (∑' d : ℕ, tail₁ d) + ∑' d : ℕ, tail₂ d := by
        rw [(hh.add ht₁).tsum_add ht₂, hh.tsum_add ht₁]
      _ ≤ _ := add_le_add (add_le_add hheadbound htail₁bound) htail₂bound
  rw [heq, abs_mul, abs_of_pos (B_pos ℓ)]
  exact mul_le_mul_of_nonneg_left hsbound (B_pos ℓ).le

/-- The literal last assertion of (120), with the half-unit subtraction
absorbed into an explicitly bounded remainder. -/
theorem M_oscillatory_expansion (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |(M a ℓ y - 1 / 2) - y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y)| ≤ C := by
  obtain ⟨C, hC, hb⟩ := M_leading_error hDLMF a hℓ
  refine ⟨C + 1 / 2, by linarith, ?_⟩
  intro y hy
  have ht := abs_sub (M a ℓ y - y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y)) (1 / 2 : ℝ)
  have he : (M a ℓ y - 1 / 2) - y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y) =
      (M a ℓ y - y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y)) - 1 / 2 := by ring
  rw [he]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at ht
  exact ht.trans (by linarith [hb y hy])

theorem M_quarter_bound (hDLMF : DLMFIdentities) (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y → |M a ℓ y| ≤ C * y ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := M_leading_error hDLMF a hℓ
  have hQ : 0 < Q ℓ := by linarith [q_pos hℓ, two_q_le_Q hℓ]
  refine ⟨C + Q ℓ, by positivity, ?_⟩
  intro y hy
  have hp : 1 ≤ y ^ (1 / 4 : ℝ) := Real.one_le_rpow hy (by norm_num)
  have ht := abs_sub_le (M a ℓ y) (y ^ (1 / 4 : ℝ) * A a ℓ (Real.sqrt y)) 0
  have hp0 : 0 ≤ y ^ (1 / 4 : ℝ) := zero_le_one.trans hp
  simp only [sub_zero, abs_mul, abs_of_nonneg hp0] at ht
  have ha := mul_le_mul_of_nonneg_left (A_bounded a hℓ (Real.sqrt y)) hp0
  have hCscale : C ≤ C * y ^ (1 / 4 : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hC.le
  nlinarith [hb y hy]

end DepthAspect.MurmurationExpansion
