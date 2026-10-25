import DepthAspect.DyadicDiscriminantValues
import DepthAspect.DyadicClassScaling

/-!
# The actual three-valued prime weight in Proposition 5.2

The conductor exponent and quadratic character at two are derived from the
fundamental-discriminant factorization. The piecewise weight is not assumed.
-/
namespace DepthAspect.PrimeTraceWeights
open FundamentalDiscriminant OddDiscriminantValues DyadicDiscriminantValues
open DyadicClassScaling

noncomputable def localPrimeWeight (e : ℕ) (α : ℝ) : ℝ :=
  (2 - α) * (2 : ℝ) ^ e / (4 * localClassFactor α e)

@[simp] theorem localPrimeWeight_zero : localPrimeWeight 0 0 = 1 / 2 := by
  norm_num [localPrimeWeight, localClassFactor]

@[simp] theorem localPrimeWeight_one_neg : localPrimeWeight 1 (-1) = 3 / 8 := by
  norm_num [localPrimeWeight, localClassFactor]

@[simp] theorem localPrimeWeight_one_pos : localPrimeWeight 1 1 = 1 / 4 := by
  norm_num [localPrimeWeight, localClassFactor]

/-- The residue of K after the actual divisibility 8|t is imposed. -/
theorem even_prime_normalized_residue (t P : ℤ) (ht : 8 ∣ t) :
    ((t / 2) ^ 2 - P) % 8 = (-P) % 8 := by
  obtain ⟨z, rfl⟩ := ht
  have hq : (8 * z) / 2 = 4 * z := by omega
  rw [hq, Int.sub_emod]
  have hs : (4 * z) ^ 2 % 8 = 0 := by
    apply Int.emod_eq_zero_of_dvd
    exact ⟨2 * z ^ 2, by ring⟩
  rw [hs]
  omega

/-- The weight is constant on each odd residue class modulo eight. -/
theorem localPrimeWeight_even_discriminant {K d : ℤ} (hK : Odd K)
    (hd : IsFundamental d) (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : 4 * K = d * (f : ℤ) ^ 2) :
    localPrimeWeight (f.factorization 2) (twoSymbol d : ℝ) =
      if K % 4 = 3 then 1 / 2 else if K % 8 = 5 then 3 / 8 else 1 / 4 := by
  have hD' : 4 * (2 : ℤ) ^ (2 * 0) * K = d * (f : ℤ) ^ 2 := by simpa using hD
  rcases table_even_rows hd hK χ hf 0 hD' with h | h
  · obtain ⟨hK4, he, hc⟩ := h
    have hsym : twoSymbol d = twoSymbol K := by
      rw [χ.two_value] at hc
      exact_mod_cast hc
    have hK8 : K % 8 = 1 ∨ K % 8 = 5 := by omega
    rw [he, hsym]
    rcases hK8 with hK8 | hK8
    · rw [twoSymbol_mod_one hK8]
      norm_num [hK4, hK8]
    · rw [twoSymbol_mod_five hK8]
      norm_num [hK4, hK8]
  · obtain ⟨hK4, he, hc⟩ := h
    have hsym : twoSymbol d = 0 := by
      rw [χ.two_value] at hc
      exact_mod_cast hc
    rw [he, hsym]
    norm_num [hK4]

/-- Literal table w(P) in (75), for every actual fundamental factorization
of t²−4P on the support 8|t. -/
theorem localPrimeWeight_prime_table (t P : ℤ) (ht : 8 ∣ t) (hP : Odd P)
    {d : ℤ} (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : t ^ 2 - 4 * P = d * (f : ℤ) ^ 2) :
    localPrimeWeight (f.factorization 2) (twoSymbol d : ℝ) =
      if P % 4 = 1 then 1 / 2 else if P % 8 = 3 then 3 / 8 else 1 / 4 := by
  have ht2 : 2 ∣ t := dvd_trans (by norm_num : (2 : ℤ) ∣ 8) ht
  have hteq : t = 2 * (t / 2) := (Int.mul_ediv_cancel' ht2).symm
  have hfac : 4 * ((t / 2) ^ 2 - P) = d * (f : ℤ) ^ 2 := by
    calc
      _ = t ^ 2 - 4 * P := by nlinarith [congrArg (fun x : ℤ => x ^ 2) hteq]
      _ = _ := hD
  have hres := even_prime_normalized_residue t P ht
  have hP8 : P % 8 = 1 ∨ P % 8 = 3 ∨ P % 8 = 5 ∨ P % 8 = 7 := by
    have := Int.odd_iff.mp hP
    omega
  have hK : Odd ((t / 2) ^ 2 - P) := Int.odd_iff.mpr (by omega)
  rw [localPrimeWeight_even_discriminant hK hd χ hf hfac]
  have hK8 : ((t / 2) ^ 2 - P) % 8 = (8 - P % 8) % 8 := by omega
  rcases hP8 with h | h | h | h
  all_goals
    have hP4 : P % 4 = (P % 8) % 4 := by omega
    have hK4 : ((t / 2) ^ 2 - P) % 4 =
        (((t / 2) ^ 2 - P) % 8) % 4 := by omega
    simp [hP4, hK4, hK8, h]

/-- At odd depth the actual discriminant t²−8P has conductor exponent zero
and ramified character at two, giving H(4D)−H(D)=2H(D). -/
theorem odd_prime_conductor_zero (t P : ℤ) (ht : 8 ∣ t) (hP : Odd P)
    {d : ℤ} (hd : IsFundamental d) (χ : QuadraticCharacterData d)
    {f : ℕ} (hf : f ≠ 0) (hD : t ^ 2 - 8 * P = d * (f : ℤ) ^ 2) :
    f.factorization 2 = 0 ∧ twoSymbol d = 0 := by
  obtain ⟨z, rfl⟩ := ht
  have hK : Odd (8 * z ^ 2 - P) := by
    apply Int.odd_iff.mpr
    have := Int.odd_iff.mp hP
    omega
  have hfac : 4 * (2 : ℤ) ^ (2 * 0 + 1) * (8 * z ^ 2 - P) =
      d * (f : ℤ) ^ 2 := by
    norm_num only [mul_zero, zero_add, pow_one]
    calc
      _ = (8 * z) ^ 2 - 8 * P := by ring
      _ = _ := hD
  obtain ⟨_, he, hc⟩ := table_odd_row hd hK χ hf 0 hfac
  refine ⟨he, ?_⟩
  rw [χ.two_value] at hc
  exact_mod_cast hc

end DepthAspect.PrimeTraceWeights
