import DepthAspect.DyadicFourClassBridge

/-! The sharper four-unit-class Fourier bound stated before (96). -/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.DyadicSpecialFourier
open DyadicCoefficientFourier DyadicFourClassBridge FiniteCharacterFourier

 theorem norm_residueCoefficient_le (j : ℕ) (K : ZMod 8) :
    ‖DyadicLocalMeans.residueCoefficient j K‖ ≤ 1 := by
  unfold DyadicLocalMeans.residueCoefficient
  split_ifs
  · norm_num
  · rw [norm_pow]
    have h := DirichletCharacter.norm_le_one
      (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 8) K
    exact pow_le_one₀ (norm_nonneg _) h
  · norm_num

/-- When four divides t the actual coefficient is inflated from modulus
eight, with a possible translation by (t/2)^2 retained in the argument. -/
theorem localAtTwo_four_dvd (n j : ℕ) (hn : 2 * j ≤ n) (hn3 : 3 ≤ n)
    {t : ℤ} (ht : 4 ∣ t) :
    localAtTwo n j hn t = fun x => DyadicLocalMeans.residueCoefficient j
      (((t / 2 : ℤ) : ZMod 8) ^ 2 -
        (ZMod.unitsMap (pow_dvd_pow 2 hn3) x : (ZMod 8)ˣ)) := by
  funext x
  let X : ℤ := (x : ZMod (2 ^ n)).val
  have hx : (X : ZMod (2 ^ n)) = x := by simp [X]
  have hX : Odd X := units_odd_representative (by omega) x
  obtain ⟨r, hr⟩ := ht
  have htEven : Even t := ⟨2 * r, by omega⟩
  have hu : t / 2 = 2 * r := by omega
  have huEven : Even (t / 2) := ⟨r, by omega⟩
  have hK : Odd ((t / 2) ^ 2 - X) := (huEven.pow_of_ne_zero (by omega : (2 : ℕ) ≠ 0)).sub_odd hX
  rw [localAtTwo, if_pos htEven, localEven_odd_quotient n j hn (t / 2) X hK x hx]
  congr 1
  rw [Int.cast_sub, Int.cast_pow]
  congr 1
  have hred := congrArg (ZMod.castHom (pow_dvd_pow 2 hn3) (ZMod 8)) hx
  simpa only [map_intCast, ZMod.unitsMap_val, ZMod.castHom_apply] using hred

/-- The exact uniform bound beta<=2 for 4|t, at the modulus used by q_m. -/
theorem beta_localAtTwo_le_two (n j : ℕ) (hn : 2 * j ≤ n) (hn3 : 3 ≤ n)
    {t : ℤ} (ht : 4 ∣ t) : beta (localAtTwo n j hn t) ≤ 2 := by
  let g : (ZMod 8)ˣ → ℂ := fun x =>
    DyadicLocalMeans.residueCoefficient j (((t / 2 : ℤ) : ZMod 8) ^ 2 - x)
  rw [localAtTwo_four_dvd n j hn hn3 ht]
  change beta (fun x : (ZMod (2 ^ n))ˣ =>
    g (ZMod.unitsMap (pow_dvd_pow 2 hn3) x)) ≤ 2
  rw [beta_inflation (pow_dvd_pow 2 hn3) g]
  apply (beta_le_sqrt_support g (fun _ => norm_residueCoefficient_le _ _)).trans
  have hc : (Finset.univ.filter (fun x : (ZMod 8)ˣ => g x ≠ 0)).card ≤ 4 := by
    exact (Finset.card_filter_le _ _).trans_eq (by simpa using DyadicLocalMeans.card_units_eight)
  calc
    _ ≤ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hc)
    _ = 2 := by simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2))

end DepthAspect.DyadicSpecialFourier
