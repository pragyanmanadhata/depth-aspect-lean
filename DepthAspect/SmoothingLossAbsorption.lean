import DepthAspect.Smoothing
import DepthAspect.SmoothedPowerSum

/-! Absorbing the explicit losses in (103) on 1≤x≤√B. -/
noncomputable section
namespace DepthAspect.SmoothingLossAbsorption

def leading (M V B x : ℝ) : ℝ :=
  M * B / Real.sqrt x + (M + V) * Real.sqrt B * Real.sqrt x

def logarithmConstant (η : ℝ) : ℝ := (4 / η ^ 2) * 2 ^ η + 1

 theorem leading_nonneg {M V B x : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hB : 0 ≤ B) :
    0 ≤ leading M V B x := by unfold leading; positivity

 theorem x_le_B {B x : ℝ} (hB : 1 ≤ B) (hxB : x ≤ Real.sqrt B) : x ≤ B :=
  hxB.trans (Real.sqrt_le_self_iff.mpr (Or.inr hB))

 theorem power_loss_le {B x α ε : ℝ} (hB : 1 ≤ B) (hx : 1 ≤ x)
    (hxB : x ≤ Real.sqrt B) (hα : 0 ≤ α) (hαε : α ≤ ε) : x ^ α ≤ B ^ ε := by
  exact (Real.rpow_le_rpow (by linarith) (x_le_B hB hxB) hα).trans
    (Real.rpow_le_rpow_of_exponent_le hB hαε)

 theorem first_term_factor {B x η : ℝ} (hB : 0 < B) (hx : 0 < x) (M : ℝ) :
    M * B ^ (1 + η) * x ^ (-1 / 2 + η) =
      (M * B / Real.sqrt x) * (B ^ η * x ^ η) := by
  rw [Real.rpow_add hB, Real.rpow_one,
    show (-1 : ℝ) / 2 + η = η - 1 / 2 by ring,
    Real.rpow_sub hx, ← Real.sqrt_eq_rpow]
  ring

 theorem middle_term_factor {B x δ : ℝ} (hx : 0 < x) (M V : ℝ) :
    (M + V) * Real.sqrt B * B ^ δ * x ^ (1 / 2 + δ + δ) =
      ((M + V) * Real.sqrt B * Real.sqrt x) * (B ^ δ * x ^ (2 * δ)) := by
  rw [show (1 / 2 : ℝ) + δ + δ = 1 / 2 + 2 * δ by ring,
    Real.rpow_add hx, ← Real.sqrt_eq_rpow]
  ring

 theorem first_loss_le {B x η ε : ℝ} (hB : 1 ≤ B) (hx : 1 ≤ x)
    (hxB : x ≤ Real.sqrt B) (hη : 0 ≤ η) (hloss : 2 * η ≤ ε) :
    B ^ η * x ^ η ≤ B ^ ε := by
  have hB0 : 0 < B := by linarith
  calc
    _ ≤ B ^ η * B ^ η := mul_le_mul_of_nonneg_left
      (power_loss_le hB hx hxB hη le_rfl) (by positivity)
    _ = B ^ (2 * η) := by rw [← Real.rpow_add hB0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB hloss

 theorem middle_loss_le {B x δ ε : ℝ} (hB : 1 ≤ B) (hx : 1 ≤ x)
    (hxB : x ≤ Real.sqrt B) (hδ : 0 ≤ δ) (hloss : 3 * δ ≤ ε) :
    B ^ δ * x ^ (2 * δ) ≤ B ^ ε := by
  have hB0 : 0 < B := by linarith
  calc
    _ ≤ B ^ δ * B ^ (2 * δ) := mul_le_mul_of_nonneg_left
      (power_loss_le hB hx hxB (by positivity) le_rfl) (by positivity)
    _ = B ^ (3 * δ) := by rw [← Real.rpow_add hB0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB hloss

 theorem logarithm_loss_le {B x η ε : ℝ} (hB : 1 ≤ B) (hx : 1 ≤ x)
    (hxB : x ≤ Real.sqrt B) (hη : 0 < η) (hηε : η ≤ ε) :
    Real.log (2 * x) ^ 2 + 1 ≤ logarithmConstant η * B ^ ε := by
  have hB0 : 0 < B := by linarith
  have hx0 : 0 < x := by linarith
  have hp : (2 * x) ^ η ≤ 2 ^ η * B ^ ε := by
    rw [Real.mul_rpow (by norm_num) hx0.le]
    exact mul_le_mul_of_nonneg_left (power_loss_le hB hx hxB hη.le hηε) (by positivity)
  have hlog := SmoothedPowerSum.log_sq_le (by linarith : 1 ≤ 2 * x) hη
  have h1 : 1 ≤ B ^ ε := Real.one_le_rpow hB (hη.le.trans hηε)
  have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 / η ^ 2)
  unfold logarithmConstant
  nlinarith

 theorem M_le_first {M B x : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B)
    (hx : 1 ≤ x) (hxB : x ≤ Real.sqrt B) : M ≤ M * B / Real.sqrt x := by
  have hroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  apply (le_div_iff₀ hroot).mpr
  exact mul_le_mul_of_nonneg_left ((Real.sqrt_le_self_iff.mpr (Or.inr hx)).trans (x_le_B hB hxB)) hM

/-- All losses in the literal three-error estimate are bounded by one
common B^ε factor on the range used by the balancing argument. -/
theorem raw_le_leading {M V B x η δ ε a b d : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hB : 1 ≤ B) (hx : 1 ≤ x)
    (hxB : x ≤ Real.sqrt B) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hηε : 2 * η ≤ ε) (hδε : 3 * δ ≤ ε)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    a * M * B ^ (1 + η) * x ^ (-1 / 2 + η) +
      b * (M + V) * Real.sqrt B * B ^ δ * x ^ (1 / 2 + δ + δ) +
      M * (Real.log (2 * x) ^ 2 + 1) + d / Real.sqrt x * (M * B) ≤
        (a + b + logarithmConstant η + d) * B ^ ε * leading M V B x := by
  have hx0 : 0 < x := by linarith
  have hB0 : 0 < B := by linarith
  have hε : 0 ≤ ε := by linarith
  have hpow : 1 ≤ B ^ ε := Real.one_le_rpow hB hε
  have hL := leading_nonneg (x := x) hM hV hB0.le
  have hfirst0 : 0 ≤ M * B / Real.sqrt x := by positivity
  have hmid0 : 0 ≤ (M + V) * Real.sqrt B * Real.sqrt x := by positivity
  have hfirst : M * B / Real.sqrt x ≤ leading M V B x := by unfold leading; linarith
  have hmid : (M + V) * Real.sqrt B * Real.sqrt x ≤ leading M V B x := by unfold leading; linarith
  have hA : a * M * B ^ (1 + η) * x ^ (-1 / 2 + η) ≤
      a * B ^ ε * leading M V B x := by
    calc
      _ = a * ((M * B / Real.sqrt x) * (B ^ η * x ^ η)) := by
        rw [← first_term_factor hB0 hx0 M]; ring
      _ ≤ a * (leading M V B x * B ^ ε) := by
        gcongr
        exact first_loss_le hB hx hxB hη.le hηε
      _ = _ := by ring
  have hD : b * (M + V) * Real.sqrt B * B ^ δ * x ^ (1 / 2 + δ + δ) ≤
      b * B ^ ε * leading M V B x := by
    calc
      _ = b * (((M + V) * Real.sqrt B * Real.sqrt x) * (B ^ δ * x ^ (2 * δ))) := by
        rw [← middle_term_factor hx0 M V]; ring
      _ ≤ b * (leading M V B x * B ^ ε) := by
        gcongr
        exact middle_loss_le hB hx hxB hδ hδε
      _ = _ := by ring
  have hlog0 : 0 ≤ logarithmConstant η := by unfold logarithmConstant; positivity
  have hlog := logarithm_loss_le hB hx hxB hη (by linarith : η ≤ ε)
  have hsmall : M * (Real.log (2 * x) ^ 2 + 1) ≤
      logarithmConstant η * B ^ ε * leading M V B x := by
    calc
      _ ≤ leading M V B x * (logarithmConstant η * B ^ ε) :=
        mul_le_mul ((M_le_first hM hB hx hxB).trans hfirst) hlog (by positivity) hL
      _ = _ := by ring
  have htail : d / Real.sqrt x * (M * B) ≤ d * B ^ ε * leading M V B x := by
    calc
      _ = d * (M * B / Real.sqrt x) := by ring
      _ ≤ d * leading M V B x := mul_le_mul_of_nonneg_left hfirst hd
      _ ≤ d * B ^ ε * leading M V B x := by
        simpa only [one_mul, mul_assoc] using
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hL) hd)
  nlinarith

end DepthAspect.SmoothingLossAbsorption
