import DepthAspect.DyadicResidueFourier
import DepthAspect.DyadicDiscriminantValues

/-!
# Fourier bound for the literal dyadic discriminant coefficient

The actual strata of (96) are inflated from their minimal moduli. The last
stratum uses two remaining digits, and the earlier strata use three. Their
support bounds give (97) for every even trace index, including zero.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.DyadicCoefficientFourier
open DyadicResidueFourier FiniteCharacterFourier
open FundamentalDiscriminant OddDiscriminantValues ImprimitiveCharacter

private def extraDigits (j : ℕ) (a : Fin j) : ℕ := if a.val + 1 = j then 2 else 3

private theorem stratum_modulus_dvd (n j : ℕ) (hn : 2 * j ≤ n) (a : Fin j) :
    2 ^ (2 * a.val + extraDigits j a) ∣ 2 ^ n := by
  apply pow_dvd_pow
  have ha := a.isLt
  unfold extraDigits
  split_ifs <;> omega

/-- An individual normalized stratum pulled back to the common modulus. -/
def inflatedStratum (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ) (a : Fin j)
    (x : (ZMod (2 ^ n))ˣ) : ℂ :=
  stratum a.val (extraDigits j a) (j - a.val - 1) u
    (ZMod.unitsMap (stratum_modulus_dvd n j hn a) x)

/-- The terminal divisibility indicator pulled back to the common modulus. -/
def inflatedTerminal (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ)
    (x : (ZMod (2 ^ n))ˣ) : ℂ :=
  divisibleTerm j u (ZMod.unitsMap (pow_dvd_pow 2 hn) x)

/-- The actual finite stratum expression for ψ of 4(u²−x). -/
def localEven (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ)
    (x : (ZMod (2 ^ n))ˣ) : ℂ :=
  inflatedTerminal n j hn u x + ∑ a : Fin j, inflatedStratum n j hn u a x

private theorem val_pow_dvd_iff {z : ℤ} (hz : z ≠ 0) (r : ℕ) :
    (2 : ℤ) ^ r ∣ z ↔ r ≤ z.natAbs.factorization 2 := by
  change (((2 : ℕ) ^ r : ℕ) : ℤ) ∣ z ↔ r ≤ z.natAbs.factorization 2
  rw [Int.natCast_dvd,
    Nat.prime_two.pow_dvd_iff_le_factorization (by simpa using hz)]

/-- The residue-one condition already enforces exact valuation. Thus the
support-friendly formulation used in the Fourier estimate is exactly (96). -/
theorem exact_stratum_iff (z : ℤ) (a : ℕ) :
    ((2 : ℤ) ^ (2 * a) ∣ z ∧ (z / (2 : ℤ) ^ (2 * a)) % 4 = 1) ↔
      (z.natAbs.factorization 2 = 2 * a ∧ (z / (2 : ℤ) ^ (2 * a)) % 4 = 1) := by
  by_cases hz : z = 0
  · simp [hz]
  constructor
  · rintro ⟨hd, hmod⟩
    have hlo := (val_pow_dvd_iff hz (2 * a)).mp hd
    have hhi : ¬ (2 : ℤ) ^ (2 * a + 1) ∣ z := by
      intro hlarge
      obtain ⟨k, hk⟩ := hlarge
      have hq : z / (2 : ℤ) ^ (2 * a) = 2 * k := by
        rw [hk, pow_succ, mul_assoc,
          Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0))]
      rw [hq] at hmod
      omega
    have hhi' := mt (val_pow_dvd_iff hz (2 * a + 1)).mpr hhi
    exact ⟨by omega, hmod⟩
  · rintro ⟨hv, hmod⟩
    exact ⟨(val_pow_dvd_iff hz (2 * a)).mpr hv.ge, hmod⟩

 theorem inflatedStratum_eq (n j : ℕ) (hn : 2 * j ≤ n) (u X : ℤ)
    (a : Fin j) (x : (ZMod (2 ^ n))ˣ) (hx : (X : ZMod (2 ^ n)) = x) :
    inflatedStratum n j hn u a x =
      if (u ^ 2 - X).natAbs.factorization 2 = 2 * a.val ∧
          ((u ^ 2 - X) / (2 : ℤ) ^ (2 * a.val)) % 4 = 1 then
        (twoSymbol ((u ^ 2 - X) / (2 : ℤ) ^ (2 * a.val)) : ℂ) ^ (j - a.val - 1)
      else 0 := by
  unfold inflatedStratum
  rw [stratum_eq_of_intCast a.val (extraDigits j a) (j - a.val - 1)
    (by unfold extraDigits; split_ifs <;> omega)
    (by unfold extraDigits; split_ifs <;> omega) u X _ (by
      have h := congrArg (ZMod.castHom (stratum_modulus_dvd n j hn a)
        (ZMod (2 ^ (2 * a.val + extraDigits j a)))) hx
      simpa only [map_intCast, ZMod.unitsMap_val, ZMod.castHom_apply] using h)]
  simp only [exact_stratum_iff]

 theorem inflatedTerminal_eq (n j : ℕ) (hn : 2 * j ≤ n) (u X : ℤ)
    (x : (ZMod (2 ^ n))ˣ) (hx : (X : ZMod (2 ^ n)) = x) :
    inflatedTerminal n j hn u x = if (2 : ℤ) ^ (2 * j) ∣ u ^ 2 - X then 1 else 0 := by
  have hx' : (X : ZMod (2 ^ (2 * j))) =
      (ZMod.unitsMap (pow_dvd_pow 2 hn) x : ZMod (2 ^ (2 * j))) := by
    have h := congrArg (ZMod.castHom (pow_dvd_pow 2 hn) (ZMod (2 ^ (2 * j)))) hx
    simpa only [map_intCast, ZMod.unitsMap_val, ZMod.castHom_apply] using h
  unfold inflatedTerminal divisibleTerm DyadicResidueFourier.residual
  simp only [← hx', ← Int.cast_pow, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow, Nat.cast_ofNat]

/-- The finite function being bounded is the literal imprimitive coefficient
whenever the discriminant is given in its defining fundamental factorization. -/
theorem localEven_eq_psi (n j : ℕ) (hn : 2 * j ≤ n) (u X : ℤ)
    (x : (ZMod (2 ^ n))ˣ) (hx : (X : ZMod (2 ^ n)) = x)
    {d : ℤ} (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : 4 * (u ^ 2 - X) = d * (f : ℤ) ^ 2) :
    localEven n j hn u x = psiNat χ.character f (2 ^ j) := by
  rw [localEven, DyadicDiscriminantValues.psi_two_strata hd χ hf hD j,
    inflatedTerminal_eq n j hn u X x hx]
  congr 1
  simp_rw [inflatedStratum_eq n j hn u X _ x hx]
  symm
  exact Finset.sum_range _

/-- The convention ψ₀=1 is realized by the same literal residue function. -/
theorem localEven_zero_discriminant (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ)
    (x : (ZMod (2 ^ n))ˣ) (hx : ((u ^ 2 : ℤ) : ZMod (2 ^ n)) = x) :
    localEven n j hn u x = 1 := by
  unfold localEven
  rw [inflatedTerminal_eq n j hn u (u ^ 2) x hx]
  simp only [sub_self, dvd_zero, ↓reduceIte]
  have hsum : (∑ a : Fin j, inflatedStratum n j hn u a x) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [inflatedStratum_eq n j hn u (u ^ 2) a x hx]
    simp
  rw [hsum, add_zero]

 theorem beta_inflatedStratum (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ) (a : Fin j) :
    beta (inflatedStratum n j hn u a) ≤ Real.sqrt 8 := by
  unfold inflatedStratum
  rw [beta_inflation]
  apply beta_stratum_le_sqrt_eight
  unfold extraDigits
  split_ifs <;> omega

 theorem beta_inflatedTerminal (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ) :
    beta (inflatedTerminal n j hn u) ≤ 1 := by
  unfold inflatedTerminal
  rw [beta_inflation]
  exact beta_divisibleTerm j u

/-- The precise dyadic bound in (97), for the actual coefficient expression. -/
theorem beta_localEven (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ) :
    beta (localEven n j hn u) ≤ 1 + j * Real.sqrt 8 := by
  unfold localEven
  calc
    _ ≤ beta (inflatedTerminal n j hn u) +
        beta (fun x => ∑ a : Fin j, inflatedStratum n j hn u a x) := beta_add _ _
    _ ≤ 1 + ∑ a : Fin j, beta (inflatedStratum n j hn u a) :=
      add_le_add (beta_inflatedTerminal n j hn u) (beta_sum Finset.univ _)
    _ ≤ 1 + ∑ a : Fin j, Real.sqrt 8 := by
      gcongr with a
      exact beta_inflatedStratum n j hn u a
    _ = _ := by simp

 theorem beta_localEven_le (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ) :
    beta (localEven n j hn u) ≤ 4 * (j + 1) := by
  have hs : Real.sqrt 8 ≤ 4 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  exact (beta_localEven n j hn u).trans (by nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j])

/-- Multiplication by any character, including the character modulo eight in
(81), leaves the Fourier norm unchanged. -/
theorem beta_twisted_localEven (n j : ℕ) (hn : 2 * j ≤ n) (u : ℤ)
    (χ : DirichletCharacter ℂ (2 ^ n)) :
    beta (fun x => χ x * localEven n j hn u x) ≤ 4 * (j + 1) := by
  rw [beta_twist]
  exact beta_localEven_le n j hn u

/-- Odd trace indices have discriminant five modulo eight at every odd x.
The conductor is odd, so the actual coefficient is the constant (-1)^j. -/
theorem psi_odd_trace {t X : ℤ} (ht : Odd t) (hX : Odd X)
    {d : ℤ} (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : t ^ 2 - 4 * X = d * (f : ℤ) ^ 2) (j : ℕ) :
    psiNat χ.character f (2 ^ j) = (-1 : ℂ) ^ j := by
  have ht8 := odd_square_mod_eight ht
  have hX2 := Int.odd_iff.mp hX
  have hD8 : (t ^ 2 - 4 * X) % 8 = 5 := by omega
  have hDodd : Odd (d * (f : ℤ) ^ 2) := by
    rw [← hD]
    exact Int.odd_iff.mpr (by omega)
  have hfodd : Odd (f : ℤ) :=
    (Int.odd_pow' (by omega : (2 : ℕ) ≠ 0)).mp (Int.odd_mul.mp hDodd).2
  have hfv : f.factorization 2 = 0 := by
    simpa using DyadicDiscriminantValues.factorization_two_of_odd hfodd
  have hsym : twoSymbol d = -1 := by
    rw [← twoSymbol_mul_odd_square d (f : ℤ) hfodd, ← hD]
    exact twoSymbol_mod_five hD8
  rw [ImprimitiveEuler.psiNat_prime_power χ.character Nat.prime_two hf, hfv]
  simp only [Nat.sub_zero, Nat.cast_ofNat, χ.two_value, hsym, Int.cast_neg, Int.cast_one]

/-- All dyadic coefficient functions, with the actual odd/even trace split. -/
def localAtTwo (n j : ℕ) (hn : 2 * j ≤ n) (t : ℤ)
    (x : (ZMod (2 ^ n))ˣ) : ℂ :=
  if Even t then localEven n j hn (t / 2) x else (-1 : ℂ) ^ j

 theorem localAtTwo_eq_psi (n j : ℕ) (hn : 2 * j ≤ n) (t X : ℤ)
    (hX : Odd X) (x : (ZMod (2 ^ n))ˣ) (hx : (X : ZMod (2 ^ n)) = x)
    {d : ℤ} (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : t ^ 2 - 4 * X = d * (f : ℤ) ^ 2) :
    localAtTwo n j hn t x = psiNat χ.character f (2 ^ j) := by
  unfold localAtTwo
  split_ifs with ht
  · apply localEven_eq_psi n j hn (t / 2) X x hx hd χ hf
    obtain ⟨u, hu⟩ := ht
    have htu : t / 2 = u := by omega
    rw [htu]
    calc
      4 * (u ^ 2 - X) = t ^ 2 - 4 * X := by rw [hu]; ring
      _ = _ := hD
  · exact (psi_odd_trace (Int.not_even_iff_odd.mp ht) hX χ hf hD j).symm

 theorem beta_constant_sign (n j : ℕ) :
    beta (fun _ : (ZMod (2 ^ n))ˣ => (-1 : ℂ) ^ j) = 1 := by
  calc
    _ = beta (fun x : (ZMod (2 ^ n))ˣ =>
        (-1 : ℂ) ^ j * (1 : DirichletCharacter ℂ (2 ^ n)) x) := by
      congr 1
      funext x
      simp
    _ = ‖(-1 : ℂ) ^ j‖ * beta (fun x : (ZMod (2 ^ n))ˣ =>
        (1 : DirichletCharacter ℂ (2 ^ n)) x) := beta_const_mul _ _
    _ = 1 := by rw [beta_character]; simp

/-- Uniform dyadic Fourier bound, with both parity cases now derived. -/
theorem beta_localAtTwo (n j : ℕ) (hn : 2 * j ≤ n) (t : ℤ) :
    beta (localAtTwo n j hn t) ≤ 4 * (j + 1) := by
  by_cases ht : Even t
  · have he : localAtTwo n j hn t = localEven n j hn (t / 2) := by
      funext x
      simp only [localAtTwo, if_pos ht]
    rw [he]
    exact beta_localEven_le n j hn (t / 2)
  · have he : localAtTwo n j hn t = fun _ : (ZMod (2 ^ n))ˣ => (-1 : ℂ) ^ j := by
      funext x
      simp only [localAtTwo, if_neg ht]
    rw [he, beta_constant_sign]
    nlinarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]

end DepthAspect.DyadicCoefficientFourier
