import DepthAspect.MurmurationPointwiseBounds
import DepthAspect.ArithmeticWeightedTails
import DepthAspect.ArithmeticPrimeWeight
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! The literal oscillation series (131), its absolute uniform convergence,
and the positive constants used for (135). -/
open Filter
open scoped BigOperators Topology
namespace DepthAspect.MurmurationOscillationSeries
open ArithmeticWeights MurmurationPointwiseBounds

noncomputable def phase (a : ℕ) : ℝ := ((4 * a + 3 : ℕ) : ℝ) * Real.pi / 4
noncomputable def K (ℓ : ℕ) : ℝ := Real.sqrt 2 * B ℓ / (1 - (ℓ : ℝ)⁻¹)
noncomputable def T (ℓ : ℕ) : ℝ := ∑' d : ℕ+, b ℓ d * Real.sqrt d
noncomputable def S (ℓ : ℕ) : ℝ := ∑' d : ℕ+, b ℓ d / (d : ℝ)
noncomputable def zetaThreeHalves : ℝ := ∑' ν : ℕ+, (ν : ℝ) ^ (-(3 / 2 : ℝ))
noncomputable def q (ℓ : ℕ) : ℝ := K ℓ * S ℓ / 2
noncomputable def Q (ℓ : ℕ) : ℝ :=
  K ℓ * (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ))) * zetaThreeHalves * T ℓ

noncomputable def oscillationTerm (a ℓ : ℕ) (i : ℕ+ × ℕ+) (x : ℝ) : ℝ :=
  K ℓ * (b ℓ i.1 * Real.sqrt i.1) * (i.2 : ℝ) ^ (-(3 / 2 : ℝ)) *
    (Real.cos (4 * Real.pi * i.2 * x / i.1 - phase a) -
      (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) * Real.cos (4 * Real.pi * ℓ * i.2 * x / i.1 - phase a))

noncomputable def A (a ℓ : ℕ) (x : ℝ) : ℝ :=
  ∑' i : ℕ+ × ℕ+, oscillationTerm a ℓ i x

noncomputable def majorant (ℓ : ℕ) (i : ℕ+ × ℕ+) : ℝ :=
  (K ℓ * (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ)))) *
    ((b ℓ i.1 * Real.sqrt i.1) * (i.2 : ℝ) ^ (-(3 / 2 : ℝ)))

theorem K_pos {ℓ : ℕ} (hℓ : ℓ.Prime) : 0 < K ℓ := by
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  have hz : 0 < 1 - (ℓ : ℝ)⁻¹ := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  dsimp [K]
  exact div_pos (mul_pos (by positivity) (B_pos ℓ)) hz

theorem T_summable (ℓ : ℕ) : Summable (fun d : ℕ+ => b ℓ d * Real.sqrt d) :=
  (b_sqrt_summable_and_bound ℓ).1.comp_injective Subtype.val_injective

theorem S_term_le_T_term (ℓ : ℕ) (d : ℕ+) : b ℓ d / (d : ℝ) ≤ b ℓ d * Real.sqrt d := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast d.pos
  have hs : 1 ≤ Real.sqrt d := by simpa using Real.sqrt_le_sqrt hd
  calc
    _ ≤ b ℓ d := div_le_self (b_nonneg ℓ d) hd
    _ ≤ _ := le_mul_of_one_le_right (b_nonneg ℓ d) hs

theorem S_summable (ℓ : ℕ) : Summable (fun d : ℕ+ => b ℓ d / (d : ℝ)) :=
  Summable.of_nonneg_of_le (fun d : ℕ+ => div_nonneg (b_nonneg ℓ d) (by positivity))
    (S_term_le_T_term ℓ) (T_summable ℓ)

theorem S_ge_one (ℓ : ℕ) : 1 ≤ S ℓ := by
  have h := (S_summable ℓ).le_tsum (i := (1 : ℕ+))
    (fun (d : ℕ+) _ => div_nonneg (b_nonneg ℓ d) (by positivity))
  simpa [S, b_one] using h

theorem S_le_T (ℓ : ℕ) : S ℓ ≤ T ℓ :=
  Summable.tsum_le_tsum (S_term_le_T_term ℓ) (S_summable ℓ) (T_summable ℓ)

theorem zetaThreeHalves_ge_one : 1 ≤ zetaThreeHalves := by
  have h := pnat_three_halves_summable.le_tsum (i := (1 : ℕ+))
    (fun d _ => Real.rpow_nonneg (by positivity) _)
  simpa [zetaThreeHalves] using h

theorem q_pos {ℓ : ℕ} (hℓ : ℓ.Prime) : 0 < q ℓ := by
  dsimp [q]
  exact div_pos (mul_pos (K_pos hℓ) (zero_lt_one.trans_le (S_ge_one ℓ))) (by norm_num)

theorem two_q_le_Q {ℓ : ℕ} (hℓ : ℓ.Prime) : 2 * q ℓ ≤ Q ℓ := by
  have hK := K_pos hℓ
  have hS := S_ge_one ℓ
  have hST := S_le_T ℓ
  have hz := zetaThreeHalves_ge_one
  have he : 0 ≤ (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hT : 0 ≤ T ℓ := by linarith
  have h1 : K ℓ * S ℓ ≤ K ℓ * T ℓ := mul_le_mul_of_nonneg_left hST hK.le
  have h2 : K ℓ * T ℓ ≤ K ℓ * (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ))) * T ℓ := by
    have hnonneg : 0 ≤ K ℓ * T ℓ * (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith only [hnonneg]
  have h3 := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ K ℓ * (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ))) * T ℓ by positivity)
  dsimp [q, Q]
  nlinarith [h1, h2, h3]

/-- The uniform absolute bound on every actual term of (131). -/
theorem oscillationTerm_bound (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (i : ℕ+ × ℕ+) (x : ℝ) : ‖oscillationTerm a ℓ i x‖ ≤ majorant ℓ i := by
  have hc : 0 ≤ K ℓ * (b ℓ i.1 * Real.sqrt i.1) * (i.2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have := (K_pos hℓ).le
    have := b_nonneg ℓ i.1
    positivity
  have he : 0 ≤ (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold oscillationTerm
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc]
  calc
    _ ≤ (K ℓ * (b ℓ i.1 * Real.sqrt i.1) * (i.2 : ℝ) ^ (-(3 / 2 : ℝ))) *
        (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact (abs_sub _ _).trans (add_le_add (Real.abs_cos_le_one _)
        (by rw [abs_mul, abs_of_nonneg he]; exact mul_le_of_le_one_right he (Real.abs_cos_le_one _)))
    _ = _ := by dsimp [majorant]; ring

theorem majorant_summable (ℓ : ℕ) : Summable (majorant ℓ) :=
  (summable_mul_of_summable_norm (T_summable ℓ).norm
    pnat_three_halves_summable.norm).mul_left _

/-- Absolute convergence at every x; the majorant does not depend on x. -/
theorem A_absolute (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (x : ℝ) :
    Summable (fun i : ℕ+ × ℕ+ => ‖oscillationTerm a ℓ i x‖) :=
  (majorant_summable ℓ).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun i => oscillationTerm_bound a hℓ i x)

/-- The product-index definition equals the nested trigonometric series
printed in (131); the interchange is justified by its absolute convergence. -/
theorem A_eq_nested (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (x : ℝ) :
    A a ℓ x = K ℓ * ∑' d : ℕ+, (b ℓ d * Real.sqrt d) *
      ∑' ν : ℕ+, (ν : ℝ) ^ (-(3 / 2 : ℝ)) *
        (Real.cos (4 * Real.pi * ν * x / d - phase a) -
          (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) *
            Real.cos (4 * Real.pi * ℓ * ν * x / d - phase a)) := by
  rw [A, (Summable.of_norm (A_absolute a hℓ x)).tsum_prod]
  simp only [oscillationTerm, mul_assoc, tsum_mul_left]

/-- Uniform convergence also holds for the series of absolute values. -/
theorem A_absolute_uniform (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    TendstoUniformly
      (fun s : Finset (ℕ+ × ℕ+) => fun x => ∑ i ∈ s, ‖oscillationTerm a ℓ i x‖)
      (fun x => ∑' i : ℕ+ × ℕ+, ‖oscillationTerm a ℓ i x‖) atTop := by
  apply tendstoUniformly_tsum (majorant_summable ℓ)
  intro i x
  simpa only [norm_norm] using oscillationTerm_bound a hℓ i x

/-- Uniform convergence of the actual trigonometric series. -/
theorem A_uniform (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    TendstoUniformly (fun s : Finset (ℕ+ × ℕ+) => fun x => ∑ i ∈ s, oscillationTerm a ℓ i x)
      (A a ℓ) atTop :=
  tendstoUniformly_tsum (majorant_summable ℓ) (oscillationTerm_bound a hℓ)

theorem A_continuous (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) : Continuous (A a ℓ) :=
  continuous_tsum (fun i => by unfold oscillationTerm; fun_prop)
    (majorant_summable ℓ) (oscillationTerm_bound a hℓ)

/-- The displayed upper bound Q is the sum of the actual positive majorant. -/
theorem majorant_tsum (ℓ : ℕ) : (∑' i : ℕ+ × ℕ+, majorant ℓ i) = Q ℓ := by
  unfold majorant
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm
    (T_summable ℓ).norm pnat_three_halves_summable.norm]
  change (K ℓ * (1 + (ℓ : ℝ) ^ (-(3 / 2 : ℝ)))) *
    (T ℓ * zetaThreeHalves) = Q ℓ
  unfold Q
  ring

theorem A_bounded (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (x : ℝ) : |A a ℓ x| ≤ Q ℓ := by
  calc
    _ ≤ ∑' i : ℕ+ × ℕ+, ‖oscillationTerm a ℓ i x‖ := norm_tsum_le_tsum_norm (A_absolute a hℓ x)
    _ ≤ ∑' i : ℕ+ × ℕ+, majorant ℓ i := Summable.tsum_le_tsum
      (fun i => oscillationTerm_bound a hℓ i x) (A_absolute a hℓ x) (majorant_summable ℓ)
    _ = _ := majorant_tsum ℓ

end DepthAspect.MurmurationOscillationSeries
