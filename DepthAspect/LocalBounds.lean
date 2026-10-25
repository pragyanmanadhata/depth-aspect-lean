import DepthAspect.LocalCancellation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Quantitative bounds for actual dyadic projective charts

The bounds in (23) are proved for the concrete two-chart count. Integer bounds
use floor exponents and imply the paper's real half-exponent bounds.
Identification with trace-formula local weights remains separate.
-/
namespace DepthAspect.LocalBounds
open ContentReduction LocalCancellation GeneralRoots

/-- The odd-middle case has at most three projective roots. -/
theorem rho_odd_middle_bound (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    rho j A B C ≤ 3 := by
  have hfirst : firstChart j A B C = OddMiddleRoots.roots j A B C := rfl
  have hsecond : secondChart j A B C = OddMiddleRoots.evenRoots j C B A := by
    ext x
    simp only [secondChart, OddMiddleRoots.evenRoots, OddMiddleRoots.evenRootsMod,
      OddMiddleRoots.rootsMod, OddMiddleRoots.quadratic, Finset.mem_filter]
    have heq : A + B * x + C * x ^ 2 = C * x ^ 2 + B * x + A := by ring
    rw [heq]
    tauto
  simpa only [rho, hfirst, hsecond] using
    OddMiddleRoots.projective_chart_bound j A B C hj hB

/-- A primitive form has at most `4 * 2^floor(j/2)` roots at positive depth. -/
theorem rho_primitive_bound (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j)
    (hprim : Odd A ∨ Odd B ∨ Odd C) : rho j A B C ≤ 4 * 2 ^ (j / 2) := by
  rcases Int.even_or_odd B with hBe | hBo
  · obtain ⟨b, hb⟩ := hBe
    have hB : B = 2 * b := by omega
    have hnB : ¬ Odd B := by rw [hB, Int.odd_iff]; omega
    have hAC : Odd A ∨ Odd C := by tauto
    rw [hB, rho_even_middle_eq_squareRoots A b C hAC j hj]
    exact squareRoots_card_bound j _
  · have hb := rho_odd_middle_bound j A B C hj hBo
    have hp : 1 ≤ (2 : ℕ) ^ (j / 2) := Nat.one_le_pow _ _ (by decide)
    omega

/-- The quantitative content bound, with natural-number floor in the exponent. -/
theorem rho_scaled_bound (h e : ℕ) (A B C : ℤ) (hh : 1 ≤ h)
    (hprim : Odd A ∨ Odd B ∨ Odd C) :
    rho h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) ≤ 4 * 2 ^ ((h + e) / 2) := by
  by_cases he : h ≤ e
  · rw [rho_all_scalar h e A B C hh he]
    have hp : (2 : ℕ) ^ (h - 1) ≤ 2 ^ ((h + e) / 2) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hej : e + (h - e) = h := by omega
    rw [← hej, rho_content_reduction e (h - e) A B C (by omega)]
    have hb := rho_primitive_bound (h - e) A B C (by omega) hprim
    calc
      2 ^ e * rho (h - e) A B C ≤ 2 ^ e * (4 * 2 ^ ((h - e) / 2)) :=
        Nat.mul_le_mul_left _ hb
      _ = 4 * 2 ^ ((e + (h - e) + e) / 2) := by
        rw [show (e + (h - e) + e) / 2 = e + (h - e) / 2 by omega, pow_add]
        ring

/-- The formal level-zero charts have two representatives; no abstract
projective-line interpretation at level zero is asserted. -/
theorem rho_zero (A B C : ℤ) : rho 0 A B C = 2 := by
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by decide
  have hE : Even (0 : ℤ) := ⟨0, rfl⟩
  simp [rho, firstChart, secondChart, hI, Finset.filter_singleton, hE]

/-- The numerical bound also holds for the formal level-zero convention. -/
theorem rho_scaled_bound_all (h e : ℕ) (A B C : ℤ)
    (hprim : Odd A ∨ Odd B ∨ Odd C) :
    rho h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) ≤ 4 * 2 ^ ((h + e) / 2) := by
  by_cases hh : h = 0
  · rw [hh, rho_zero]
    have hp : 1 ≤ (2 : ℕ) ^ ((0 + e) / 2) := Nat.one_le_pow _ _ (by decide)
    omega
  · exact rho_scaled_bound h e A B C (by omega) hprim

/-- The second-difference bound in the stronger floor-exponent integer form. -/
theorem second_difference_bound (n e : ℕ) (A B C : ℤ)
    (hprim : Odd A ∨ Odd B ∨ Odd C) :
    |(rho n (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) -
      2 * (rho (n - 1) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) +
      (rho (n - 2) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ)| ≤
      16 * (2 : ℤ) ^ ((n + e) / 2) := by
  have h0 := rho_scaled_bound_all n e A B C hprim
  have h1 := rho_scaled_bound_all (n - 1) e A B C hprim
  have h2 := rho_scaled_bound_all (n - 2) e A B C hprim
  have hp1 : (2 : ℕ) ^ ((n - 1 + e) / 2) ≤ 2 ^ ((n + e) / 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hp2 : (2 : ℕ) ^ ((n - 2 + e) / 2) ≤ 2 ^ ((n + e) / 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have h0' : (rho n (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) ≤
      4 * (2 : ℤ) ^ ((n + e) / 2) := by exact_mod_cast h0
  have h1' : (rho (n - 1) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) ≤
      4 * (2 : ℤ) ^ ((n + e) / 2) := by
    exact_mod_cast h1.trans (Nat.mul_le_mul_left 4 hp1)
  have h2' : (rho (n - 2) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) ≤
      4 * (2 : ℤ) ^ ((n + e) / 2) := by
    exact_mod_cast h2.trans (Nat.mul_le_mul_left 4 hp2)
  rw [abs_le]
  constructor <;> omega

/-- The floor exponent is bounded by the real half exponent. -/
theorem floor_power_le_half_power (a : ℕ) :
    (2 : ℝ) ^ (a / 2) ≤ (2 : ℝ) ^ ((a : ℝ) / 2) := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : a / 2 * 2 ≤ a := Nat.div_mul_le_self a 2
  have h' : (a / 2 : ℕ) * (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast h
  linarith

/-- The first estimate in (23), with the paper's real exponent. -/
theorem rho_scaled_bound_real (h e : ℕ) (A B C : ℤ) (hh : 1 ≤ h)
    (hprim : Odd A ∨ Odd B ∨ Odd C) :
    (rho h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ) ≤
      4 * (2 : ℝ) ^ (((h : ℝ) + e) / 2) := by
  have hb : (rho h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ) ≤
      4 * (2 : ℝ) ^ ((h + e) / 2) := by
    exact_mod_cast rho_scaled_bound h e A B C hh hprim
  have hp := floor_power_le_half_power (h + e)
  push_cast at hp
  exact hb.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

/-- The second estimate in (23), with the paper's real exponent. -/
theorem second_difference_bound_real (n e : ℕ) (A B C : ℤ)
    (hprim : Odd A ∨ Odd B ∨ Odd C) :
    |(rho n (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ) -
      2 * (rho (n - 1) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ) +
      (rho (n - 2) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ)| ≤
      16 * (2 : ℝ) ^ (((n : ℝ) + e) / 2) := by
  have hb : |(rho n (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ) -
      2 * (rho (n - 1) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ) +
      (rho (n - 2) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℝ)| ≤
      16 * (2 : ℝ) ^ ((n + e) / 2) := by
    exact_mod_cast second_difference_bound n e A B C hprim
  have hp := floor_power_le_half_power (n + e)
  push_cast at hp
  exact hb.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

end DepthAspect.LocalBounds
