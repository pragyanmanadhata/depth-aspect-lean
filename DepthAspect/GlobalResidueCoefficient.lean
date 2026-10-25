import DepthAspect.PrimeCoefficientProduct
import DepthAspect.OddCoefficientPeriodicity
import DepthAspect.OddCoefficientFourier
import DepthAspect.DyadicCoefficientFourier
import DepthAspect.GlobalFourierBound

/-!
# The literal global residue function in (81)

The modulus is exactly lcm(8,m²). Every local factor is the already defined
valuation-and-quadratic-symbol coefficient, pulled back by reduction. At any
integer representative with a fundamental factorization, the product equals
the original gcd-based ψ, regardless of the sign of the discriminant. Thus
positive representatives require only the algebraic quadratic character data,
not a positive-discriminant L-value or class-number assumption. At zero the
same formula gives one, exactly the explicit convention following (81).
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.GlobalResidueCoefficient
open FundamentalDiscriminant OddDiscriminantValues ImprimitiveCharacter
open FiniteCharacterFourier

/-- The exact common modulus printed in (81). -/
def modulus (m : ℕ) : ℕ := Nat.lcm 8 (m ^ 2)

/-- Its dyadic factor retains all three character digits at degree zero. -/
def twoExponent (m : ℕ) : ℕ := max 3 (2 * m.factorization 2)

abbrev OddPrime (m : ℕ) := {p : ℕ // p ∈ m.primeFactors.erase 2}

/-- Product conversion valid for the inferred finite subtype instance. -/
theorem prod_oddPrime {M : Type*} [CommMonoid M] (m : ℕ) (f : ℕ → M) :
    (∏ p : OddPrime m, f p.val) = ∏ p ∈ m.primeFactors.erase 2, f p :=
  (Finset.prod_subtype (p := fun p => p ∈ m.primeFactors.erase 2)
    (m.primeFactors.erase 2) (fun _ => Iff.rfl) f).symm

instance oddPrime_fact (m : ℕ) (p : OddPrime m) : Fact p.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp p.property).2⟩

 theorem oddPrime_ne_two (m : ℕ) (p : OddPrime m) : p.val ≠ 2 :=
  (Finset.mem_erase.mp p.property).1

 theorem modulus_ne_zero {m : ℕ} (hm : m ≠ 0) : modulus m ≠ 0 := by
  exact Nat.lcm_ne_zero (by norm_num) (pow_ne_zero 2 hm)

instance modulus_neZero (m : ℕ) [NeZero m] : NeZero (modulus m) :=
  ⟨modulus_ne_zero (NeZero.ne m)⟩

 theorem primeSquare_dvd (m p : ℕ) : p ^ (2 * m.factorization p) ∣ modulus m := by
  apply dvd_trans _ (Nat.dvd_lcm_right 8 (m ^ 2))
  have h := pow_dvd_pow_of_dvd (Nat.ordProj_dvd m p) 2
  simpa only [← pow_mul, mul_comm (m.factorization p) 2] using h

 theorem twoPower_dvd (m : ℕ) : 2 ^ twoExponent m ∣ modulus m := by
  unfold twoExponent
  rcases le_total 3 (2 * m.factorization 2) with h | h
  · rw [max_eq_right h]
    exact primeSquare_dvd m 2
  · rw [max_eq_left h]
    exact Nat.dvd_lcm_left 8 (m ^ 2)

/-- Each odd local factor is literally evaluated on the reduction of a unit. -/
def oddFactor (m : ℕ) (t : ℤ) (p : OddPrime m)
    (x : (ZMod (modulus m))ˣ) : ℂ :=
  OddCoefficientFourier.localOnUnits (p := p.val) (m.factorization p.val) t
    (ZMod.unitsMap (primeSquare_dvd m p.val) x)

/-- The literal dyadic coefficient, including its degree-zero value. -/
def twoFactor (m : ℕ) (t : ℤ) (x : (ZMod (modulus m))ˣ) : ℂ :=
  DyadicCoefficientFourier.localAtTwo (twoExponent m) (m.factorization 2)
    (le_max_right _ _) t (ZMod.unitsMap (twoPower_dvd m) x)

/-- The un-twisted ψ coefficient on the actual reduced residue classes. -/
def coefficientFunction (m : ℕ) (t : ℤ) (x : (ZMod (modulus m))ˣ) : ℂ :=
  twoFactor m t x * ∏ p : OddPrime m, oddFactor m t p x

/-- The character in (81) is inflated from its actual modulus eight, with
its value at minus x represented by the constant χ(-1). -/
def twistedFunction (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8)
    (x : (ZMod (modulus m))ˣ) : ℂ :=
  χ (-1) * (χ.changeLevel (show 8 ∣ modulus m from Nat.dvd_lcm_left 8 (m ^ 2))) x *
    coefficientFunction m t x

private theorem intCast_reduction {a Q : ℕ} (h : a ∣ Q) (X : ℤ)
    (x : (ZMod Q)ˣ) (hx : (X : ZMod Q) = x) :
    (X : ZMod a) = (ZMod.unitsMap h x : ZMod a) := by
  have heq := congrArg (ZMod.castHom h (ZMod a)) hx
  simpa only [map_intCast, ZMod.unitsMap_val, ZMod.castHom_apply] using heq

/-- The representative used in the odd factor is congruent to the actual X,
so the integer stratum formula identifies it with the original ψ coefficient. -/
theorem oddFactor_eq_psi {m : ℕ} (t X : ℤ) (p : OddPrime m)
    (x : (ZMod (modulus m))ˣ) (hx : (X : ZMod (modulus m)) = x)
    {d : ℤ} (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : t ^ 2 - 4 * X = d * (f : ℤ) ^ 2) :
    oddFactor m t p x = psiNat χ.character f (p.val ^ m.factorization p.val) := by
  let r := m.factorization p.val
  let y := ZMod.unitsMap (primeSquare_dvd m p.val) x
  have hy : (X : ZMod (p.val ^ (2 * r))) = y :=
    intCast_reduction (primeSquare_dvd m p.val) X x hx
  have hmod : (((y : ZMod (p.val ^ (2 * r))).val : ℕ) : ℤ) ≡
      X [ZMOD (p.val : ℤ) ^ (2 * r)] := by
    rw [← hy]
    simpa only [Nat.cast_pow] using ResidueNormalization.val_modEq (p.val ^ (2 * r)) X
  have hdisc : t ^ 2 - 4 * (((y : ZMod (p.val ^ (2 * r))).val : ℕ) : ℤ) ≡
      t ^ 2 - 4 * X [ZMOD (p.val : ℤ) ^ (2 * r)] :=
    (Int.ModEq.refl _).sub (hmod.mul_left 4)
  change localCoefficient p.val
    (t ^ 2 - 4 * (((y : ZMod (p.val ^ (2 * r))).val : ℕ) : ℤ)) r = _
  rw [OddCoefficientPeriodicity.localCoefficient_eq_of_modEq r hdisc, hD]
  exact (psiNat_eq_localCoefficient hd χ (Fact.out : p.val.Prime)
    (oddPrime_ne_two m p) hf r).symm

/-- The dyadic factor agrees with ψ on every fundamental factorization. The
sign of D is immaterial to this purely algebraic identity. -/
theorem twoFactor_eq_psi {m : ℕ} (t X : ℤ) (hX : Odd X)
    (x : (ZMod (modulus m))ˣ) (hx : (X : ZMod (modulus m)) = x)
    {d : ℤ} (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : t ^ 2 - 4 * X = d * (f : ℤ) ^ 2) :
    twoFactor m t x = psiNat χ.character f (2 ^ m.factorization 2) := by
  exact DyadicCoefficientFourier.localAtTwo_eq_psi _ _ _ t X hX _
    (intCast_reduction (twoPower_dvd m) X x hx) hd χ hf hD

/-- The actual periodic product equals the actual gcd-based ψ. In particular
this applies to every negative discriminant in the prime sum. It also proves
the algebraic extension on positive and nonzero-square representatives without
any assertion about their L-values. -/
theorem coefficientFunction_eq_psi {m : ℕ} (hm : m ≠ 0) (t X : ℤ) (hX : Odd X)
    (x : (ZMod (modulus m))ˣ) (hx : (X : ZMod (modulus m)) = x)
    {d : ℤ} (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : t ^ 2 - 4 * X = d * (f : ℤ) ^ 2) :
    coefficientFunction m t x = psiNat χ.character f m := by
  rw [coefficientFunction, twoFactor_eq_psi t X hX x hx hd χ hf hD,
    PrimeCoefficientProduct.psiNat_two_mul_odd χ.character f hm]
  congr 1
  calc
    _ = ∏ p : OddPrime m, psiNat χ.character f (p.val ^ m.factorization p.val) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact oddFactor_eq_psi t X p x hx hd χ hf hD
    _ = _ := prod_oddPrime m (fun p : ℕ =>
      psiNat χ.character f (p ^ m.factorization p))

/-- The zero discriminant is realized by the same local expressions, not by
an independently chosen function designed to change an average. -/
theorem coefficientFunction_zero {m : ℕ} (t X : ℤ)
    (x : (ZMod (modulus m))ˣ) (hx : (X : ZMod (modulus m)) = x)
    (hD : t ^ 2 - 4 * X = 0) : coefficientFunction m t x = 1 := by
  have ht : Even t := by
    by_contra hn
    have hodd := odd_square_mod_eight (Int.not_even_iff_odd.mp hn)
    omega
  obtain ⟨u, hu⟩ := ht
  have hX : X = u ^ 2 := by rw [hu] at hD; nlinarith [sq_nonneg u]
  have htwo : twoFactor m t x = 1 := by
    unfold twoFactor DyadicCoefficientFourier.localAtTwo
    rw [if_pos ⟨u, hu⟩]
    have htu : t / 2 = u := by omega
    rw [htu]
    apply DyadicCoefficientFourier.localEven_zero_discriminant
    simpa only [hX] using intCast_reduction (twoPower_dvd m) X x hx
  have hodd : ∀ p : OddPrime m, oddFactor m t p x = 1 := by
    intro p
    let r := m.factorization p.val
    let y := ZMod.unitsMap (primeSquare_dvd m p.val) x
    have hy := intCast_reduction (primeSquare_dvd m p.val) X x hx
    have hmod : (((y : ZMod (p.val ^ (2 * r))).val : ℕ) : ℤ) ≡
        X [ZMOD (p.val : ℤ) ^ (2 * r)] := by
      rw [← hy]
      simpa only [Nat.cast_pow] using ResidueNormalization.val_modEq (p.val ^ (2 * r)) X
    have hdmod := (Int.ModEq.refl (t ^ 2)).sub (hmod.mul_left 4)
    change localCoefficient p.val
      (t ^ 2 - 4 * (((y : ZMod (p.val ^ (2 * r))).val : ℕ) : ℤ)) r = 1
    rw [OddCoefficientPeriodicity.localCoefficient_eq_of_modEq r hdmod, hD,
      localCoefficient_zero]
  simp only [coefficientFunction, htwo, hodd, Finset.prod_const_one, mul_one]

/-- The norm estimate (97) for this actual global coefficient function. -/
theorem beta_coefficientFunction {m : ℕ} [NeZero m] (hm : m ≠ 0) (t : ℤ) :
    beta (coefficientFunction m t) ≤ GlobalFourierBound.localProduct m := by
  letI : NeZero (modulus m) := ⟨modulus_ne_zero hm⟩
  have htwo : beta (twoFactor m t) ≤ 4 * ((m.factorization 2 : ℝ) + 1) := by
    unfold twoFactor
    rw [beta_inflation]
    exact DyadicCoefficientFourier.beta_localAtTwo _ _ _ t
  have hodd : ∀ p : OddPrime m,
      beta (oddFactor m t p) ≤ ((m.factorization p.val : ℝ) + 1) * Real.sqrt p.val := by
    intro p
    unfold oddFactor
    rw [beta_inflation]
    exact OddCoefficientFourier.beta_localOnUnits_le (oddPrime_ne_two m p) _ t
  calc
    _ ≤ beta (twoFactor m t) * beta (fun x => ∏ p : OddPrime m, oddFactor m t p x) :=
      beta_mul _ _
    _ ≤ beta (twoFactor m t) * ∏ p : OddPrime m, beta (oddFactor m t p) :=
      mul_le_mul_of_nonneg_left (beta_prod Finset.univ _) (beta_nonneg _)
    _ ≤ (4 * ((m.factorization 2 : ℝ) + 1)) *
        ∏ p : OddPrime m, ((m.factorization p.val : ℝ) + 1) * Real.sqrt p.val := by
      apply mul_le_mul htwo _ (Finset.prod_nonneg (fun _ _ => beta_nonneg _))
        (by positivity)
      exact Finset.prod_le_prod (fun _ _ => beta_nonneg _) (fun p _ => hodd p)
    _ = _ := by
      rw [prod_oddPrime m (fun p : ℕ =>
        ((m.factorization p : ℝ) + 1) * Real.sqrt p)]
      rfl

/-- Twisting by χ(-x) retains the same norm bound; χ(-1) has norm one. -/
theorem beta_twistedFunction {m : ℕ} [NeZero m] (hm : m ≠ 0) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) :
    beta (twistedFunction m t χ) ≤ GlobalFourierBound.localProduct m := by
  letI : NeZero (modulus m) := ⟨modulus_ne_zero hm⟩
  have hn : ‖χ (-1)‖ = 1 := by simpa using χ.unit_norm_eq_one (-1 : (ZMod 8)ˣ)
  have hfun : twistedFunction m t χ = fun x : (ZMod (modulus m))ˣ => χ (-1) *
      ((χ.changeLevel (show 8 ∣ modulus m from Nat.dvd_lcm_left 8 (m ^ 2))) x * coefficientFunction m t x) := by
    funext x
    exact mul_assoc _ _ _
  rw [hfun, beta_const_mul, hn, one_mul, beta_twist]
  exact beta_coefficientFunction hm t

end DepthAspect.GlobalResidueCoefficient
