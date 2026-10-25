import DepthAspect.SignedArithmeticData

/-!
# Quantitative sign balance for the actual finite family

The estimates in (71) are derived from the exact general-formula sign
counts and Martin dimensions, with the depth-seven boundary included.
The denominators are the cardinalities of the literal sign filters.
-/
open scoped BigOperators
namespace DepthAspect.SignedSieve

theorem even_ratio_bounds (k q : ℝ) (hk : 2 ≤ k) (hq : 16 ≤ q) :
    0 ≤ evenImbalance q / evenDimension k q ∧
      evenImbalance q / evenDimension k q ≤ 1 / 2 ∧
      evenImbalance q / evenDimension k q ≤ 8 / ((k - 1) * q) := by
  have hd := even_dimension_pos k q hk hq
  have hq0 : 0 < q := by linarith
  have hk0 : 0 < k - 1 := by linarith
  have hden : 0 < (k - 1) * q := by positivity
  have hhalf := even_imbalance_le_half k q hk hq
  refine ⟨div_nonneg (by unfold evenImbalance; positivity) hd.le, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith
  · apply (div_le_div_iff₀ hd hden).mpr
    have hb := (even_dimension_bounds k q hk hq).1
    unfold evenImbalance
    nlinarith

theorem odd_ratio_bounds (k q : ℝ) (hk : 2 ≤ k) (hq : 8 ≤ q) :
    0 ≤ oddImbalance q / oddDimension k q ∧
      oddImbalance q / oddDimension k q ≤ 1 / 2 ∧
      oddImbalance q / oddDimension k q = 4 / ((k - 1) * q) := by
  have hq0 : 0 < q := by linarith
  have hd := odd_dimension_pos k q hk hq0
  have hk0 : k - 1 ≠ 0 := by linarith
  have hhalf := odd_imbalance_le_half k q hk hq
  refine ⟨div_nonneg (by unfold oddImbalance; positivity) hd.le, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith
  · unfold oddImbalance oddDimension
    field_simp [hk0, ne_of_gt hq0]
    ring

theorem sqrt_two_even_power (a : ℕ) : Real.sqrt ((2 : ℝ) ^ (2 * a)) = (2 : ℝ) ^ a := by
  rw [mul_comm 2 a, pow_mul, Real.sqrt_sq (by positivity)]

theorem sqrt_two_odd_power (a : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * a + 1)) = Real.sqrt 2 * (2 : ℝ) ^ a := by
  rw [pow_add, pow_one, Real.sqrt_mul (by positivity), sqrt_two_even_power]
  ring

namespace SignedArithmeticData

variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

noncomputable def relativeRootSum (S : SignedArithmeticData r Family Full New) (N : ℕ) : ℝ :=
  (∑ f, S.rootNumber N f) / (Fintype.card (Family N) : ℝ)

theorem relativeRootSum_even_bounds (S : SignedArithmeticData r Family Full New)
    (a : ℕ) (ha : 4 ≤ a) :
    0 ≤ S.relativeRootSum (2 ^ (2 * a)) ∧
      S.relativeRootSum (2 ^ (2 * a)) ≤ 1 / 2 ∧
      S.relativeRootSum (2 ^ (2 * a)) ≤
        8 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ (2 * a))) := by
  have hq : (16 : ℝ) ≤ 2 ^ a := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at h
    exact h
  have hk : (2 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * r + 2)
  have hR : (2 : ℝ) ^ (a - 3) = evenImbalance ((2 : ℝ) ^ a) := by
    unfold evenImbalance
    conv_rhs => rw [show a = (a - 3) + 3 by omega, pow_add]
    norm_num
  unfold relativeRootSum
  rw [S.rootNumber_sum_even a (by omega), hR,
    MartinDimension.dimension_even (2 * r + 2) a (by omega) _ S.unsigned.dimension_formula,
    sqrt_two_even_power]
  have h := even_ratio_bounds ((2 * r + 2 : ℕ) : ℝ) ((2 : ℝ) ^ a) hk hq
  convert h using 1 <;> push_cast <;> ring

theorem relativeRootSum_odd_bounds (S : SignedArithmeticData r Family Full New)
    (a : ℕ) (ha : 3 ≤ a) :
    0 ≤ S.relativeRootSum (2 ^ (2 * a + 1)) ∧
      S.relativeRootSum (2 ^ (2 * a + 1)) ≤ 1 / 2 ∧
      S.relativeRootSum (2 ^ (2 * a + 1)) ≤
        8 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ (2 * a + 1))) := by
  have hq : (8 : ℝ) ≤ 2 ^ a := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
    norm_num at h
    exact h
  have hk : (2 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * r + 2)
  have hR : (2 : ℝ) ^ (a - 2) = oddImbalance ((2 : ℝ) ^ a) := by
    unfold oddImbalance
    conv_rhs => rw [show a = (a - 2) + 2 by omega, pow_add]
    norm_num
  have heq : S.relativeRootSum (2 ^ (2 * a + 1)) =
      oddImbalance ((2 : ℝ) ^ a) / oddDimension ((2 * r + 2 : ℕ) : ℝ) ((2 : ℝ) ^ a) := by
    unfold relativeRootSum
    rw [S.rootNumber_sum_odd a (by omega), hR,
      MartinDimension.dimension_odd (2 * r + 2) a (by omega) _ S.unsigned.dimension_formula]
  rw [heq, sqrt_two_odd_power]
  obtain ⟨hnonneg, hhalf, hvalue⟩ := odd_ratio_bounds ((2 * r + 2 : ℕ) : ℝ) ((2 : ℝ) ^ a) hk hq
  refine ⟨hnonneg, hhalf, ?_⟩
  rw [hvalue]
  have hcoef : (((2 * r + 2 : ℕ) : ℝ) - 1) = ((2 * r + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcoef]
  have hspos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hprod : (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) * 2 ^ a := by positivity
  apply (div_le_div_iff₀ hprod (by positivity)).mpr
  nlinarith [mul_nonneg hprod.le (sub_nonneg.mpr hs2)]

/-- The first quantitative bound in (71), together with the sharper
one-half bound needed for both actual sign classes. -/
theorem relativeRootSum_bounds (S : SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 7 ≤ n) :
    0 ≤ S.relativeRootSum (2 ^ n) ∧ S.relativeRootSum (2 ^ n) ≤ 1 / 2 ∧
      S.relativeRootSum (2 ^ n) ≤
        8 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) := by
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨a, ha⟩ := heven
    have heq : n = 2 * a := by omega
    rw [heq] at hn ⊢
    exact S.relativeRootSum_even_bounds a (by omega)
  · obtain ⟨a, ha⟩ := hodd
    have heq : n = 2 * a + 1 := by omega
    rw [heq] at hn ⊢
    exact S.relativeRootSum_odd_bounds a (by omega)

/-- The actual sign-filter cardinality ratio in the second line of (71). -/
theorem signClass_card_ratio_error (S : SignedArithmeticData r Family Full New)
    (n : ℕ) (hn : 7 ≤ n) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    |(Fintype.card (Family (2 ^ n)) : ℝ) /
      (2 * ((S.signClass (2 ^ n) σ).card : ℝ)) - 1| ≤
      16 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n)) := by
  have hcount := S.signClass_card (2 ^ n) σ hσ
  have hnonempty := S.signClass_nonempty n hn σ hσ
  have hsign : (0 : ℝ) < (S.signClass (2 ^ n) σ).card := by
    exact_mod_cast Finset.card_pos.mpr hnonempty
  have hall : (Finset.univ : Finset (Family (2 ^ n))).Nonempty :=
    hnonempty.mono (Finset.filter_subset _ _)
  have hd : (0 : ℝ) < Fintype.card (Family (2 ^ n)) := by
    have hdn : 0 < Fintype.card (Family (2 ^ n)) := by
      simpa only [Finset.card_univ] using Finset.card_pos.mpr hall
    exact_mod_cast hdn
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨hR0, hRhalf, hRbound⟩ := S.relativeRootSum_bounds n hn
  have hxabs : |σ * S.relativeRootSum (2 ^ n)| = S.relativeRootSum (2 ^ n) := by
    rw [abs_mul, hσabs, one_mul, abs_of_nonneg hR0]
  have hden : 1 + σ * S.relativeRootSum (2 ^ n) ≠ 0 := by
    have h := abs_le.mp (show |σ * S.relativeRootSum (2 ^ n)| ≤ (1 / 2 : ℝ) by
      rw [hxabs]; exact hRhalf)
    linarith
  have heq : (Fintype.card (Family (2 ^ n)) : ℝ) /
      (2 * ((S.signClass (2 ^ n) σ).card : ℝ)) =
      (1 + σ * S.relativeRootSum (2 ^ n))⁻¹ := by
    have hsum0 : (Fintype.card (Family (2 ^ n)) : ℝ) +
        σ * (∑ f, S.rootNumber (2 ^ n) f) ≠ 0 := by
      rw [← hcount]
      positivity
    unfold relativeRootSum
    rw [hcount]
    field_simp [ne_of_gt hd, hsum0]
  rw [heq]
  calc
    _ ≤ 2 * |σ * S.relativeRootSum (2 ^ n)| :=
      inverse_one_add_error _ (by rw [hxabs]; exact hRhalf)
    _ = 2 * S.relativeRootSum (2 ^ n) := by rw [hxabs]
    _ ≤ 2 * (8 / (((2 * r + 1 : ℕ) : ℝ) * Real.sqrt ((2 : ℝ) ^ n))) :=
      mul_le_mul_of_nonneg_left hRbound (by norm_num)
    _ = _ := by ring

end SignedArithmeticData
end DepthAspect.SignedSieve
