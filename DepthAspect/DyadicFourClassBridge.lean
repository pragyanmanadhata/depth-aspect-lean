import DepthAspect.FourDyadicTwists
import DepthAspect.DyadicOddSeries

/-!
# Connecting the global dyadic factor to the four-class calculation

The hypothesis is exactly 8∣t. The actual stratum function then depends only
on the four odd residue classes modulo eight. Inflation invariance of the
principal Fourier coefficient proves equality with the literal finite average
used in Lemma 5.4.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.DyadicFourClassBridge
open DyadicCoefficientFourier FundamentalDiscriminant
open GlobalResidueCoefficient GlobalResidueMean DyadicOddSeries

 theorem localEven_odd_quotient (n j : ℕ) (hn : 2 * j ≤ n) (u X : ℤ)
    (hK : Odd (u ^ 2 - X)) (x : (ZMod (2 ^ n))ˣ)
    (hx : (X : ZMod (2 ^ n)) = x) :
    localEven n j hn u x = DyadicLocalMeans.residueCoefficient j ((u ^ 2 - X : ℤ) : ZMod 8) := by
  have hv : (u ^ 2 - X).natAbs.factorization 2 = 0 :=
    DyadicDiscriminantValues.factorization_two_of_odd hK
  have hmod : ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4)
      ((u ^ 2 - X : ℤ) : ZMod 8) = 1 ↔ (u ^ 2 - X) % 4 = 1 := by
    rw [map_intCast]
    change ((u ^ 2 - X : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) ↔ _
    rw [ZMod.intCast_eq_intCast_iff]
    norm_num [Int.ModEq]
  cases j with
  | zero =>
    rw [localEven, inflatedTerminal_eq n 0 hn u X x hx]
    simp [DyadicLocalMeans.residueCoefficient]
  | succ j =>
    have hterminal : ¬ (2 : ℤ) ^ (2 * (j + 1)) ∣ u ^ 2 - X := by
      intro h
      have hpow : (2 : ℤ) ∣ (2 : ℤ) ^ (2 * (j + 1)) := by
        simpa only [pow_one] using
          (pow_dvd_pow (2 : ℤ) (by omega : 1 ≤ 2 * (j + 1)))
      have hd : (2 : ℤ) ∣ u ^ 2 - X := hpow.trans h
      have hzero := Int.dvd_iff_emod_eq_zero.mp hd
      have hone := Int.odd_iff.mp hK
      omega
    rw [localEven, inflatedTerminal_eq n (j + 1) hn u X x hx, if_neg hterminal, zero_add]
    rw [Finset.sum_eq_single (0 : Fin (j + 1))]
    · rw [inflatedStratum_eq n (j + 1) hn u X (0 : Fin (j + 1)) x hx]
      simp only [Fin.val_zero, mul_zero, pow_zero, Int.ediv_one, hv, true_and,
        Nat.add_sub_cancel, DyadicLocalMeans.residueCoefficient, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, ↓reduceIte, hmod]
      rfl
    · intro a _ ha
      rw [inflatedStratum_eq n (j + 1) hn u X a x hx]
      have hane : a.val ≠ 0 := fun h => ha (Fin.ext h)
      simp [hv, hane]
    · simp

 theorem units_odd_representative {n : ℕ} (hn : 1 ≤ n) (x : (ZMod (2 ^ n))ˣ) :
    Odd ((x : ZMod (2 ^ n)).val : ℤ) := by
  have hc := ZMod.val_coe_unit_coprime x
  have hc2 : (x : ZMod (2 ^ n)).val.Coprime 2 :=
    (Nat.coprime_pow_right_iff (by omega : 0 < n)
      (x : ZMod (2 ^ n)).val 2).mp hc
  exact_mod_cast Nat.coprime_two_right.mp hc2

/-- The actual dyadic coefficient is inflated from the four classes modulo
8 when the trace index satisfies the paper's exact divisibility hypothesis. -/
theorem localAtTwo_eight_dvd (n j : ℕ) (hn : 2 * j ≤ n) (hn3 : 3 ≤ n)
    {t : ℤ} (ht : 8 ∣ t) (x : (ZMod (2 ^ n))ˣ) :
    localAtTwo n j hn t x =
      DyadicLocalMeans.residueCoefficient j
        (-(ZMod.unitsMap (pow_dvd_pow 2 hn3) x : (ZMod 8)ˣ) : ZMod 8) := by
  let X : ℤ := (x : ZMod (2 ^ n)).val
  have hX : Odd X := units_odd_representative (by omega) x
  have hx : (X : ZMod (2 ^ n)) = x := by simp [X]
  obtain ⟨r, hr⟩ := ht
  have hu : t / 2 = 4 * r := by omega
  have htEven : Even t := ⟨4 * r, by omega⟩
  have hK : Odd ((t / 2) ^ 2 - X) := by
    rw [hu]
    exact (((by decide : Even (4 : ℤ)).mul_right r).pow_of_ne_zero
      (by omega : (2 : ℕ) ≠ 0)).sub_odd hX
  rw [localAtTwo, if_pos htEven, localEven_odd_quotient n j hn (t / 2) X hK x hx]
  congr 1
  have hu8 : (((t / 2) ^ 2 : ℤ) : ZMod 8) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr
    rw [hu]
    exact ⟨2 * r ^ 2, by ring⟩
  rw [Int.cast_sub, hu8, zero_sub]
  congr 1
  have hred := congrArg (ZMod.castHom (pow_dvd_pow 2 hn3) (ZMod 8)) hx
  simpa only [map_intCast, ZMod.unitsMap_val, ZMod.castHom_apply] using hred

/-- The high-modulus dyadic integrand is the actual inflated four-class
function, including the character at −x. -/
theorem dyadicFunction_inflation (m : ℕ) {t : ℤ} (ht : 8 ∣ t) (i : Fin 4) :
    dyadicFunction m t (FourDyadicTwists.character i) = fun x =>
      (DyadicLocalMeans.twistValue i
        (-(ZMod.unitsMap (eight_dvd_twoPower m) x : (ZMod 8)ˣ) : ZMod 8) : ℂ) *
      DyadicLocalMeans.residueCoefficient (m.factorization 2)
        (-(ZMod.unitsMap (eight_dvd_twoPower m) x : (ZMod 8)ˣ) : ZMod 8) := by
  funext x
  have hj : 2 * m.factorization 2 ≤ twoExponent m := le_max_right _ _
  have hn3 : 3 ≤ twoExponent m := le_max_left _ _
  have hlocal := localAtTwo_eight_dvd (twoExponent m) (m.factorization 2) hj hn3 ht x
  have hchar : (FourDyadicTwists.character i) (-1) *
      ((FourDyadicTwists.character i).changeLevel (eight_dvd_twoPower m)) x =
      (DyadicLocalMeans.twistValue i
        (-(ZMod.unitsMap (eight_dvd_twoPower m) x : (ZMod 8)ˣ) : ZMod 8) : ℂ) := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    have hc := FourDyadicTwists.character_apply_unit i
      (-ZMod.unitsMap (eight_dvd_twoPower m) x)
    simp only [Units.val_neg] at hc
    calc
      _ = (FourDyadicTwists.character i)
          (-(ZMod.unitsMap (eight_dvd_twoPower m) x : ZMod 8)) := by
        simpa only [neg_one_mul, ZMod.unitsMap_val] using
          (map_mul (FourDyadicTwists.character i) (-1)
            (ZMod.unitsMap (eight_dvd_twoPower m) x : ZMod 8)).symm
      _ = _ := hc
  exact congrArg₂ (fun a b : ℂ => a * b) hchar hlocal

 theorem dyadicMean_eq_four_class (m : ℕ) {t : ℤ} (ht : 8 ∣ t) (i : Fin 4) :
    dyadicMean m t (FourDyadicTwists.character i) =
      DyadicLocalMeans.average i (m.factorization 2) := by
  let g : (ZMod 8)ˣ → ℂ := fun x =>
    (DyadicLocalMeans.twistValue i (-(x : ZMod 8)) : ℂ) *
      DyadicLocalMeans.residueCoefficient (m.factorization 2) (-(x : ZMod 8))
  rw [dyadicMean, dyadicFunction_inflation m ht i]
  change FiniteCharacterFourier.coefficient
    (fun x => g (ZMod.unitsMap (eight_dvd_twoPower m) x)) 1 =
      DyadicLocalMeans.average i (m.factorization 2)
  rw [FiniteCharacterFourier.coefficient_principal_inflation (eight_dvd_twoPower m) g,
    FiniteCharacterFourier.coefficient_principal, DyadicLocalMeans.card_units_eight]
  exact DyadicLocalMeans.average_negated_classes i _

 theorem dyadicValue_eq_four_class {t : ℤ} (ht : 8 ∣ t) (i : Fin 4) (b : ℕ) :
    dyadicValue t (FourDyadicTwists.character i) b = DyadicLocalMeans.average i b := by
  rw [dyadicValue_eq_mean, dyadicMean_eq_four_class _ ht i,
    Nat.factorization_pow_self Nat.prime_two]

/-- The actual four series in (89), after identification with the original
global mean rather than an independently defined residue table. -/
theorem dyadic_generating_functions {t : ℤ} (ht : 8 ∣ t)
    {z : ℂ} (hz : ‖z‖ < 1) :
    dyadicSeries t (FourDyadicTwists.character 0) z = (2 + z - 2 * z ^ 2) / (2 * (1 - z ^ 2)) ∧
    dyadicSeries t (FourDyadicTwists.character 1) z = z / (2 * (1 - z ^ 2)) ∧
    dyadicSeries t (FourDyadicTwists.character 2) z = z ^ 2 / (2 * (1 - z ^ 2)) ∧
    dyadicSeries t (FourDyadicTwists.character 3) z = z ^ 2 / (2 * (1 - z ^ 2)) := by
  obtain ⟨h0, h1, h2, h3⟩ := DyadicLocalMeans.generating_functions hz
  simp_rw [dyadicSeries, dyadicValue_eq_four_class ht]
  exact ⟨h0.tsum_eq, h1.tsum_eq, h2.tsum_eq, h3.tsum_eq⟩

end DepthAspect.DyadicFourClassBridge
