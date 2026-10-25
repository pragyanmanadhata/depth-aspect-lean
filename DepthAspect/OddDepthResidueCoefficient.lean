import DepthAspect.GlobalResidueMean
import DepthAspect.FiniteCharacterTranslation
import DepthAspect.OddAverageEuler
import DepthAspect.NegativeResidueBridge

/-!
# The actual odd-depth coefficient and its mean

For 8∣t, t²−8X has valuation exactly three at two for odd X. Hence every even
coefficient vanishes. For odd m, the odd coordinates are translated by the
unit represented by 2+7m². Its congruence to two modulo m² makes the literal
polynomial t²−8X agree with the already constructed odd local functions.
Translation preserves the actual principal coefficient and Fourier norm.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.OddDepthResidueCoefficient
open GlobalResidueCoefficient GlobalResidueMean FiniteCharacterFourier
open FundamentalDiscriminant OddDiscriminantValues ImprimitiveCharacter

/-- An explicit unit which doubles all odd residue coordinates. -/
def multiplier (m : ℕ) : ℕ := 2 + 7 * m ^ 2

 theorem multiplier_odd {m : ℕ} (hm : Odd m) : Odd (multiplier m) := by
  unfold multiplier
  exact (by decide : Even 2).add_odd ((by decide : Odd 7).mul (hm.pow (n := 2)))

 theorem multiplier_coprime {m : ℕ} (hm : Odd m) : (multiplier m).Coprime (modulus m) := by
  by_contra h
  obtain ⟨p, hp, hpU, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  rcases (NegativeResidueBridge.prime_dvd_modulus_iff m hp).mp hpq with hp2 | hpm
  · subst p
    exact (multiplier_odd hm).not_two_dvd_nat hpU
  · have hpd : p ∣ 7 * m ^ 2 := dvd_mul_of_dvd_right (dvd_pow hpm (by omega)) 7
    have hp2 : p ∣ 2 := (Nat.dvd_add_iff_left hpd).mpr hpU
    have heq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    exact hm.not_two_dvd_nat (heq ▸ hpm)

 def translatingUnit (m : ℕ) (hm : Odd m) : (ZMod (modulus m))ˣ :=
  ZMod.unitOfCoprime (multiplier m) (multiplier_coprime hm)

 theorem translatingUnit_odd_coordinate {m : ℕ} (hm : Odd m) (p : OddPrime m) :
    ((multiplier m : ℕ) : ZMod (p.val ^ (2 * m.factorization p.val))) = 2 := by
  have hdiv : p.val ^ (2 * m.factorization p.val) ∣ m ^ 2 := by
    have h := pow_dvd_pow_of_dvd (Nat.ordProj_dvd m p.val) 2
    simpa only [← pow_mul, mul_comm] using h
  have hz : ((m ^ 2 : ℕ) : ZMod (p.val ^ (2 * m.factorization p.val))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  simp only [multiplier, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hz, mul_zero, add_zero]

/-- The literal function used for the odd-depth coefficient average. -/
def residueFunction (m : ℕ) (t : ℤ) (x : (ZMod (modulus m))ˣ) : ℂ :=
  if hm : Odd m then coefficientFunction m t (translatingUnit m hm * x) else 0

 theorem localAtTwo_zero_degree (n : ℕ) (t : ℤ) (x : (ZMod (2 ^ n))ˣ) :
    DyadicCoefficientFourier.localAtTwo n 0 (by omega) t x = 1 := by
  unfold DyadicCoefficientFourier.localAtTwo
  split_ifs
  · simp [DyadicCoefficientFourier.localEven, DyadicCoefficientFourier.inflatedTerminal,
      DyadicResidueFourier.divisibleTerm, DyadicResidueFourier.residual] <;>
      exact Subsingleton.elim _ _
  · simp

private theorem localAtTwo_of_degree_zero (n j : ℕ) (hn : 2 * j ≤ n)
    (hj : j = 0) (t : ℤ) (x : (ZMod (2 ^ n))ˣ) :
    DyadicCoefficientFourier.localAtTwo n j hn t x = 1 := by
  subst j
  exact localAtTwo_zero_degree n t x

private theorem residueFunction_of_odd {m : ℕ} (hm : Odd m) (t : ℤ) :
    residueFunction m t = fun x => coefficientFunction m t (translatingUnit m hm * x) := by
  funext x
  exact dif_pos hm

private theorem residueFunction_of_not_odd {m : ℕ} (hm : ¬ Odd m) (t : ℤ) :
    residueFunction m t = fun _ => 0 := by
  funext x
  exact dif_neg hm

 theorem coefficient_principal_untwisted {m : ℕ} [NeZero m] (t : ℤ) :
    coefficient (coefficientFunction m t) 1 = average m t 1 := by
  have hneg : (1 : DirichletCharacter ℂ 8) (-1) = 1 :=
    MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod 8))
  have hfun : twistedFunction m t 1 = coefficientFunction m t := by
    funext x
    simp only [twistedFunction, hneg, DirichletCharacter.changeLevel_one,
      MulChar.one_apply_coe, one_mul]
  rw [average, hfun]

 theorem dyadicMean_odd {m : ℕ} (hm : Odd m) (t : ℤ) : dyadicMean m t 1 = 1 := by
  have hv : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat
  rw [dyadicMean]
  have hneg : (1 : DirichletCharacter ℂ 8) (-1) = 1 :=
    MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod 8))
  have heq : dyadicFunction m t 1 = fun _ => (1 : ℂ) := by
    funext x
    have hlocal := localAtTwo_of_degree_zero (twoExponent m) (m.factorization 2)
      (le_max_right _ _) hv t x
    simp only [dyadicFunction, hneg, DirichletCharacter.changeLevel_one,
      MulChar.one_apply_coe, one_mul, hlocal]
  rw [heq, coefficient_principal]
  simp

/-- The principal coefficient is exactly the previously proved odd Euler
sequence, including zero at every positive even index. -/
theorem principal_mean {m : ℕ} [NeZero m] (t : ℤ) :
    coefficient (residueFunction m t) 1 = OddAverageEuler.coefficient t m := by
  by_cases hm : Odd m
  · rw [residueFunction_of_odd hm t, FiniteCharacterTranslation.principal_translate,
      coefficient_principal_untwisted, average_factorization, dyadicMean_odd hm,
      one_mul, OddAverageEuler.coefficient_odd t hm]
  · rw [residueFunction_of_not_odd hm t,
      OddAverageEuler.coefficient_even t (Nat.not_odd_iff_even.mp hm)]
    simp [coefficient]

 theorem norm_residueFunction_le (m : ℕ) (t : ℤ) (x : (ZMod (modulus m))ˣ) :
    ‖residueFunction m t x‖ ≤ 1 := by
  unfold residueFunction
  split_ifs
  · exact LocalCoefficientNorm.norm_coefficientFunction_le _ _ _
  · norm_num

 theorem beta_residueFunction {m : ℕ} [NeZero m] (t : ℤ) :
    beta (residueFunction m t) ≤ GlobalFourierBound.localProduct m := by
  by_cases hm : Odd m
  · rw [residueFunction_of_odd hm t, FiniteCharacterTranslation.beta_translate]
    exact beta_coefficientFunction (NeZero.ne m) t
  · rw [residueFunction_of_not_odd hm t]
    have : 0 ≤ GlobalFourierBound.localProduct m := by
      unfold GlobalFourierBound.localProduct
      positivity
    simpa [beta, coefficient] using this

/-- The valuation-three row gives ψ_D(2^b)=0 for every positive b. -/
theorem psi_two_odd_depth {t X d : ℤ} (ht : 8 ∣ t) (hX : Odd X)
    (hd : IsFundamental d) (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : t ^ 2 - 8 * X = d * (f : ℤ) ^ 2) (b : ℕ) :
    psiNat χ.character f (2 ^ b) = if b = 0 then 1 else 0 := by
  obtain ⟨r, hr⟩ := ht
  let K : ℤ := 8 * r ^ 2 - X
  have hK : Odd K := ((by decide : Even (8 : ℤ)).mul_right _).sub_odd hX
  have hfactor : 4 * (2 : ℤ) ^ (2 * 0 + 1) * K = d * (f : ℤ) ^ 2 := by
    rw [← hD, hr]
    dsimp [K]
    ring
  simpa using DyadicDiscriminantValues.psi_two_odd_row hd hK χ hf 0 b hfactor

 theorem psi_even_odd_depth {t X d : ℤ} (ht : 8 ∣ t) (hX : Odd X)
    (hd : IsFundamental d) (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : t ^ 2 - 8 * X = d * (f : ℤ) ^ 2) {m : ℕ} (hm0 : m ≠ 0) (hm : Even m) :
    psiNat χ.character f m = 0 := by
  have hv : m.factorization 2 ≠ 0 := by
    exact (Nat.prime_two.factorization_pos_of_dvd hm0 hm.two_dvd).ne'
  rw [PrimeCoefficientProduct.psiNat_two_mul_odd χ.character f hm0,
    psi_two_odd_depth ht hX hd χ hf hD, if_neg hv, zero_mul]

/-- Actual coefficient identification at every fundamental factorization,
without any sign condition or local-value premise. -/
theorem residueFunction_eq_psi {m : ℕ} (hm0 : m ≠ 0) {t X d : ℤ}
    (ht : 8 ∣ t) (hX : Odd X) (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : t ^ 2 - 8 * X = d * (f : ℤ) ^ 2)
    (x : (ZMod (modulus m))ˣ) (hx : (X : ZMod (modulus m)) = x) :
    residueFunction m t x = psiNat χ.character f m := by
  by_cases hm : Odd m
  · have hv : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hm.not_two_dvd_nat
    have htwo : twoFactor m t (translatingUnit m hm * x) = 1 :=
      localAtTwo_of_degree_zero (twoExponent m) (m.factorization 2) (le_max_right _ _)
        hv t (ZMod.unitsMap (twoPower_dvd m) (translatingUnit m hm * x))
    rw [residueFunction, dif_pos hm, coefficientFunction, htwo,
      one_mul, PrimeCoefficientProduct.psiNat_two_mul_odd χ.character f hm0,
      hv, pow_zero, ImprimitiveEuler.psiNat_one, one_mul]
    rw [← prod_oddPrime m (fun p : ℕ => psiNat χ.character f (p ^ m.factorization p))]
    apply Finset.prod_congr rfl
    intro p hp
    let r := m.factorization p.val
    let y := ZMod.unitsMap (primeSquare_dvd m p.val) (translatingUnit m hm * x)
    have hy : (2 * X : ZMod (p.val ^ (2 * r))) = y := by
      have hred := congrArg (ZMod.castHom (primeSquare_dvd m p.val)
        (ZMod (p.val ^ (2 * r)))) hx
      have hU := translatingUnit_odd_coordinate hm p
      have hcast : (ZMod.cast ((multiplier m : ℕ) : ZMod (modulus m)) :
          ZMod (p.val ^ (2 * r))) = 2 :=
        (ZMod.cast_natCast (primeSquare_dvd m p.val) (multiplier m)).trans hU
      simp only [map_intCast, ZMod.unitsMap_val, ZMod.castHom_apply] at hred
      simp only [y, map_mul, Units.val_mul, translatingUnit, ZMod.coe_unitOfCoprime,
        ZMod.unitsMap_val, hcast, ← hred] <;> push_cast <;> rfl
    have hcong : (((y : ZMod (p.val ^ (2 * r))).val : ℕ) : ℤ) ≡ 2 * X
        [ZMOD (p.val : ℤ) ^ (2 * r)] := by
      rw [← hy]
      simpa only [Nat.cast_pow, Int.cast_mul, Int.cast_ofNat] using
        ResidueNormalization.val_modEq (p.val ^ (2 * r)) (2 * X)
    have hdisc := (Int.ModEq.refl (t ^ 2)).sub (hcong.mul_left 4)
    change localCoefficient p.val (t ^ 2 - 4 * (((y : ZMod (p.val ^ (2 * r))).val : ℕ) : ℤ)) r = _
    rw [OddCoefficientPeriodicity.localCoefficient_eq_of_modEq r hdisc,
      show t ^ 2 - 4 * (2 * X) = t ^ 2 - 8 * X by ring, hD]
    exact (psiNat_eq_localCoefficient hd χ (Fact.out : p.val.Prime)
      (oddPrime_ne_two m p) hf r).symm
  · rw [residueFunction, dif_neg hm,
      psi_even_odd_depth ht hX hd χ hf hD hm0 (Nat.not_odd_iff_even.mp hm)]

end DepthAspect.OddDepthResidueCoefficient
