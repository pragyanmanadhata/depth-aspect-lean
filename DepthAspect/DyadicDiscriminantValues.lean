import DepthAspect.OddDiscriminantValues
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Dyadic valuations of actual fundamental-discriminant factorizations

The possible valuations 0, 2 and 3 at two are derived from the standard
squarefree congruence definition. This is arithmetic input to table (82),
not a premise asserting that table or the local Fourier bound.
-/
open scoped BigOperators

namespace DepthAspect.DyadicDiscriminantValues
open FundamentalDiscriminant OddDiscriminantValues ImprimitiveCharacter ImprimitiveEuler

 theorem factorization_two_of_odd {u : ℤ} (hu : Odd u) :
    u.natAbs.factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro h
  have hz : (2 : ℤ) ∣ u := Int.natCast_dvd.mpr h
  exact (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr hz)

 theorem odd_ne_zero {u : ℤ} (hu : Odd u) : u ≠ 0 := by
  intro h
  subst u
  norm_num at hu

private theorem odd_of_mod_four_three {u : ℤ} (hu : u % 4 = 3) : Odd u := by
  apply Int.odd_iff.mpr
  omega

private theorem factorization_two_of_mod_four_two {u : ℤ} (hu : u % 4 = 2) :
    u.natAbs.factorization 2 = 1 := by
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at hu
  have hua : u.natAbs ≠ 0 := by simpa using hu0
  have h2 : (2 : ℤ) ∣ u := Int.dvd_iff_emod_eq_zero.mpr (by omega)
  have h4 : ¬ (4 : ℤ) ∣ u := by
    intro h
    have := Int.emod_eq_zero_of_dvd h
    omega
  have hlo : 1 ≤ u.natAbs.factorization 2 :=
    (Nat.prime_two.dvd_iff_one_le_factorization hua).mp (Int.natCast_dvd.mp h2)
  have hhi : ¬ 2 ≤ u.natAbs.factorization 2 := by
    intro h
    have hpow := (Nat.prime_two.pow_dvd_iff_le_factorization hua).mpr h
    apply h4
    have := Int.natCast_dvd.mpr hpow
    norm_num at this ⊢
    exact this
  omega

private theorem factorization_four : (4 : ℕ).factorization 2 = 2 := by
  exact Nat.factorization_pow_self (n := 2) Nat.prime_two

/-- All three branches retain the corresponding actual congruence data. -/
theorem fundamental_two_cases {d : ℤ} (hd : IsFundamental d) :
    (d.natAbs.factorization 2 = 0 ∧ d % 4 = 1) ∨
    (d.natAbs.factorization 2 = 2 ∧ ∃ d₀ : ℤ, d = 4 * d₀ ∧ d₀ % 4 = 3) ∨
    (d.natAbs.factorization 2 = 3 ∧ ∃ d₀ : ℤ, d = 4 * d₀ ∧ d₀ % 4 = 2) := by
  rcases hd with ⟨hm, hs⟩ | ⟨d₀, rfl, hs, hm⟩
  · have ho : Odd d := Int.odd_iff.mpr (by omega)
    exact Or.inl ⟨factorization_two_of_odd ho, hm⟩
  · have hd0 : d₀ ≠ 0 := by
      intro h
      rcases hm with hm | hm <;> norm_num [h] at hm
    have hda : d₀.natAbs ≠ 0 := by simpa using hd0
    have hv : (4 * d₀).natAbs.factorization 2 = 2 + d₀.natAbs.factorization 2 := by
      simp only [Int.natAbs_mul]
      rw [Nat.factorization_mul (by norm_num) hda, Finsupp.add_apply]
      norm_num [factorization_four]
    rcases hm with hm | hm
    · right; right
      refine ⟨?_, d₀, rfl, hm⟩
      rw [hv, factorization_two_of_mod_four_two hm]
    · right; left
      refine ⟨?_, d₀, rfl, hm⟩
      rw [hv, factorization_two_of_odd (odd_of_mod_four_three hm)]

/-- The fundamental character vanishes at two in both even-discriminant cases. -/
theorem character_two_eq_zero_of_even {d : ℤ} (χ : QuadraticCharacterData d)
    (hd : Even d) : χ.character (2 : ZMod d.natAbs) = 0 := by
  rw [χ.two_value, twoSymbol_even hd, Int.cast_zero]

/-- Every even fundamental discriminant belongs to one of the ramified cases. -/
theorem fundamental_two_ramified {d : ℤ} (hd : IsFundamental d)
    (hv : d.natAbs.factorization 2 ≠ 0) :
    Even d ∧ (d.natAbs.factorization 2 = 2 ∨ d.natAbs.factorization 2 = 3) := by
  rcases fundamental_two_cases hd with h | h | h
  · exact (hv h.1).elim
  · obtain ⟨d₀, rfl, hm⟩ := h.2
    exact ⟨⟨2 * d₀, by ring⟩, Or.inl h.1⟩
  · obtain ⟨d₀, rfl, hm⟩ := h.2
    exact ⟨⟨2 * d₀, by ring⟩, Or.inr h.1⟩

/-- The exact exponent relation underlying all rows of (82). -/
theorem table_exponent_relation {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    {f : ℕ} (hf : f ≠ 0) (j : ℕ)
    (hD : 4 * (2 : ℤ) ^ j * u = d * (f : ℤ) ^ 2) :
    j + 2 = d.natAbs.factorization 2 + 2 * f.factorization 2 := by
  have hu0 : u.natAbs ≠ 0 := by simpa using odd_ne_zero hu
  have hl : (4 * (2 : ℤ) ^ j * u).natAbs.factorization 2 = j + 2 := by
    simp only [Int.natAbs_mul, Int.natAbs_pow]
    rw [Nat.factorization_mul (by positivity) hu0,
      Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Finsupp.add_apply]
    simp [Nat.prime_two.factorization_pow, factorization_two_of_odd hu, factorization_four]
    omega
  rw [hD, discriminant_factorization hd.ne_zero hf] at hl
  exact hl.symm

/-- The odd conductor complement, viewed as an integer, is odd. -/
theorem conductor_odd_complement {f : ℕ} (hf : f ≠ 0) :
    Odd ((ordCompl[2] f : ℕ) : ℤ) := by
  have hg : Odd (ordCompl[2] f : ℕ) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact Nat.not_dvd_ordCompl Nat.prime_two hf (even_iff_two_dvd.mp he)
  obtain ⟨k, hk⟩ := hg
  refine ⟨(k : ℤ), ?_⟩
  exact_mod_cast hk

private theorem odd_square_mod_four {g : ℤ} (hg : Odd g) : g ^ 2 % 4 = 1 := by
  have h := FundamentalDiscriminant.odd_square_mod_eight hg
  omega

/-- Exact cancellation of the common dyadic scale in a discriminant
factorization. The resulting odd factor is an equality of integers. -/
theorem normalized_odd_factor {d d₀ u : ℤ} {f : ℕ} (hf : f ≠ 0)
    (j v : ℕ) (hd : d = (2 : ℤ) ^ v * d₀)
    (hv : j + 2 = v + 2 * f.factorization 2)
    (hD : 4 * (2 : ℤ) ^ j * u = d * (f : ℤ) ^ 2) :
    u = d₀ * ((ordCompl[2] f : ℕ) : ℤ) ^ 2 := by
  have hfcast : (f : ℤ) = (2 : ℤ) ^ f.factorization 2 * ((ordCompl[2] f : ℕ) : ℤ) := by
    exact_mod_cast (conductor_decomposition Nat.prime_two hf).1
  have hscaled : (2 : ℤ) ^ (j + 2) * u =
      (2 : ℤ) ^ (v + 2 * f.factorization 2) *
        (d₀ * ((ordCompl[2] f : ℕ) : ℤ) ^ 2) := by
    calc
      _ = 4 * (2 : ℤ) ^ j * u := by rw [pow_add]; ring
      _ = d * (f : ℤ) ^ 2 := hD
      _ = _ := by
        rw [hd, hfcast, pow_add, mul_comm 2 (f.factorization 2), pow_mul]
        ring
  rw [← hv] at hscaled
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)) hscaled

/-- Even valuation of K leaves exactly the two even rows of (82), with their
residue classes and the character value at two derived from the factorization. -/
theorem table_even_rows {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0) (a : ℕ)
    (hD : 4 * (2 : ℤ) ^ (2 * a) * u = d * (f : ℤ) ^ 2) :
    (u % 4 = 1 ∧ f.factorization 2 = a + 1 ∧
      χ.character (2 : ZMod d.natAbs) = (twoSymbol u : ℂ)) ∨
    (u % 4 = 3 ∧ f.factorization 2 = a ∧
      χ.character (2 : ZMod d.natAbs) = 0) := by
  have hrel := table_exponent_relation hd hu hf (2 * a) hD
  have hg := conductor_odd_complement hf
  have hg4 := odd_square_mod_four hg
  rcases fundamental_two_cases hd with h | h | h
  · have he : f.factorization 2 = a + 1 := by omega
    have hn := normalized_odd_factor hf (2 * a) 0
      (show d = (2 : ℤ) ^ 0 * d by simp) (by omega) hD
    left
    refine ⟨?_, he, ?_⟩
    · rw [hn, Int.mul_emod, hg4, h.2]
      norm_num
    · rw [χ.two_value, hn, FundamentalDiscriminant.twoSymbol_mul_odd_square d _ hg]
  · have he : f.factorization 2 = a := by omega
    obtain ⟨d₀, hd₀, hm⟩ := h.2
    have hn := normalized_odd_factor hf (2 * a) 2
      (show d = (2 : ℤ) ^ 2 * d₀ by simpa only [show (2 : ℤ) ^ 2 = 4 by norm_num] using hd₀) (by omega) hD
    right
    refine ⟨?_, he, character_two_eq_zero_of_even χ ?_⟩
    · rw [hn, Int.mul_emod, hg4, hm]
      norm_num
    · rw [hd₀]
      exact ⟨2 * d₀, by ring⟩
  · omega

/-- The first row of table (82), selected by the actual residue of the odd
normalized discriminant. -/
theorem table_even_one {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0) (a : ℕ)
    (hD : 4 * (2 : ℤ) ^ (2 * a) * u = d * (f : ℤ) ^ 2) (hu4 : u % 4 = 1) :
    f.factorization 2 = a + 1 ∧
      χ.character (2 : ZMod d.natAbs) = (twoSymbol u : ℂ) := by
  rcases table_even_rows hd hu χ hf a hD with h | h
  · exact h.2
  · omega

/-- The second row of table (82), with its vanishing fundamental character. -/
theorem table_even_three {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0) (a : ℕ)
    (hD : 4 * (2 : ℤ) ^ (2 * a) * u = d * (f : ℤ) ^ 2) (hu4 : u % 4 = 3) :
    f.factorization 2 = a ∧ χ.character (2 : ZMod d.natAbs) = 0 := by
  rcases table_even_rows hd hu χ hf a hD with h | h
  · omega
  · exact h.2

/-- The actual coefficient in the unramified dyadic row. -/
theorem psi_two_even_one {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0) (a b : ℕ)
    (hD : 4 * (2 : ℤ) ^ (2 * a) * u = d * (f : ℤ) ^ 2) (hu4 : u % 4 = 1) :
    psiNat χ.character f (2 ^ b) = (twoSymbol u : ℂ) ^ (b - a - 1) := by
  obtain ⟨he, hc⟩ := table_even_one hd hu χ hf a hD hu4
  rw [psiNat_prime_power χ.character Nat.prime_two hf, he]
  simp only [Nat.cast_ofNat]
  rw [hc]
  congr 1

/-- The actual coefficient in the ramified even-valuation row. -/
theorem psi_two_even_three {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0) (a b : ℕ)
    (hD : 4 * (2 : ℤ) ^ (2 * a) * u = d * (f : ℤ) ^ 2) (hu4 : u % 4 = 3) :
    psiNat χ.character f (2 ^ b) = if b ≤ a then 1 else 0 := by
  obtain ⟨he, hc⟩ := table_even_three hd hu χ hf a hD hu4
  rw [psiNat_prime_power χ.character Nat.prime_two hf, he]
  simp only [Nat.cast_ofNat]
  rw [hc]
  by_cases hb : b ≤ a
  · simp [hb, Nat.sub_eq_zero_of_le hb]
  · simp [hb, Nat.sub_ne_zero_of_lt (by omega : a < b)]

/-- Odd valuation of K forces valuation three of d and the corresponding
conductor exponent. This is the third row of (82), derived arithmetically. -/
theorem table_odd_row {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0) (a : ℕ)
    (hD : 4 * (2 : ℤ) ^ (2 * a + 1) * u = d * (f : ℤ) ^ 2) :
    d.natAbs.factorization 2 = 3 ∧ f.factorization 2 = a ∧
      χ.character (2 : ZMod d.natAbs) = 0 := by
  have hrel := table_exponent_relation hd hu hf (2 * a + 1) hD
  have hv : d.natAbs.factorization 2 = 3 := by
    rcases fundamental_two_cases hd with h | h | h <;> omega
  have he : f.factorization 2 = a := by omega
  refine ⟨hv, he, character_two_eq_zero_of_even χ ?_⟩
  exact (fundamental_two_ramified hd (by omega)).1

/-- The actual ψ coefficients in the odd-valuation row, including the zero
exponent convention 0^0=1. -/
theorem psi_two_odd_row {d u : ℤ} (hd : IsFundamental d) (hu : Odd u)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0) (a b : ℕ)
    (hD : 4 * (2 : ℤ) ^ (2 * a + 1) * u = d * (f : ℤ) ^ 2) :
    psiNat χ.character f (2 ^ b) = if b ≤ a then 1 else 0 := by
  obtain ⟨hv, he, hc⟩ := table_odd_row hd hu χ hf a hD
  rw [psiNat_prime_power χ.character Nat.prime_two hf, he]
  simp only [Nat.cast_ofNat]
  rw [hc]
  by_cases hb : b ≤ a
  · simp [hb, Nat.sub_eq_zero_of_le hb]
  · simp [hb, Nat.sub_ne_zero_of_lt (by omega : a < b)]

/-- Removing the full actual power of two from a nonzero integer leaves an odd
integer, including for negative discriminants. -/
theorem normalized_odd_quotient {z : ℤ} (hz : z ≠ 0) :
    z = (2 : ℤ) ^ z.natAbs.factorization 2 *
      (z / (2 : ℤ) ^ z.natAbs.factorization 2) ∧
    Odd (z / (2 : ℤ) ^ z.natAbs.factorization 2) := by
  have hza : z.natAbs ≠ 0 := by simpa using hz
  have hpow : (2 : ℤ) ^ z.natAbs.factorization 2 ∣ z := by
    have h := (Nat.prime_two.pow_dvd_iff_le_factorization hza).mpr (le_refl _)
    exact_mod_cast Int.natCast_dvd.mpr h
  have heq := Int.mul_ediv_cancel' hpow
  refine ⟨heq.symm, Int.not_even_iff_odd.mp ?_⟩
  intro heven
  have hdiv : (2 : ℤ) ∣ z / (2 : ℤ) ^ z.natAbs.factorization 2 :=
    even_iff_two_dvd.mp heven
  have hlarge : (2 : ℤ) ^ (z.natAbs.factorization 2 + 1) ∣ z := by
    simpa only [pow_succ, heq] using mul_dvd_mul_left ((2 : ℤ) ^ z.natAbs.factorization 2) hdiv
  have hlargeN : 2 ^ (z.natAbs.factorization 2 + 1) ∣ z.natAbs := by
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hlarge
  have hcontra := (Nat.prime_two.pow_dvd_iff_le_factorization hza).mp hlargeN
  omega

/-- Equation (96) for the literal imprimitive character, with no local
valuation rule supplied as an input. -/
theorem psi_two_strata {d z : ℤ} (hd : IsFundamental d)
    (χ : QuadraticCharacterData d) {f : ℕ} (hf : f ≠ 0)
    (hD : 4 * z = d * (f : ℤ) ^ 2) (j : ℕ) :
    psiNat χ.character f (2 ^ j) =
      (if (2 : ℤ) ^ (2 * j) ∣ z then 1 else 0) +
      ∑ a ∈ Finset.range j,
        if z.natAbs.factorization 2 = 2 * a ∧
            (z / (2 : ℤ) ^ (2 * a)) % 4 = 1 then
          (twoSymbol (z / (2 : ℤ) ^ (2 * a)) : ℂ) ^ (j - a - 1)
        else 0 := by
  classical
  have hz : z ≠ 0 := by
    intro h
    have hfz : (f : ℤ) ≠ 0 := by exact_mod_cast hf
    have hn := mul_ne_zero hd.ne_zero (pow_ne_zero 2 hfz)
    exact hn (by simpa [h] using hD.symm)
  have hza : z.natAbs ≠ 0 := by simpa using hz
  let v := z.natAbs.factorization 2
  let u := z / (2 : ℤ) ^ v
  obtain ⟨hzfac, hu⟩ := normalized_odd_quotient hz
  change z = (2 : ℤ) ^ v * u at hzfac
  change Odd u at hu
  have hscaled : 4 * (2 : ℤ) ^ v * u = d * (f : ℤ) ^ 2 := by
    rw [mul_assoc, ← hzfac]
    exact hD
  have hrel := table_exponent_relation hd hu hf v hscaled
  have hvalD : (2 : ℤ) ^ (2 * j) ∣ z ↔ 2 * j ≤ v := by
    change (((2 : ℕ) ^ (2 * j) : ℕ) : ℤ) ∣ z ↔ 2 * j ≤ v
    rw [Int.natCast_dvd, Nat.prime_two.pow_dvd_iff_le_factorization hza]
  simp only [hvalD]
  by_cases hj : 2 * j ≤ v
  · rw [if_pos hj]
    have hved : d.natAbs.factorization 2 ≤ 3 := by
      rcases fundamental_two_cases hd with h | h | h <;> omega
    have hej : j ≤ f.factorization 2 := by omega
    rw [psiNat_prime_power χ.character Nat.prime_two hf]
    rw [Nat.sub_eq_zero_of_le hej, pow_zero]
    have hsum : (∑ a ∈ Finset.range j,
        if z.natAbs.factorization 2 = 2 * a ∧
            (z / (2 : ℤ) ^ (2 * a)) % 4 = 1 then
          (twoSymbol (z / (2 : ℤ) ^ (2 * a)) : ℂ) ^ (j - a - 1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have haj := Finset.mem_range.mp ha
      rw [if_neg (by dsimp [v] at hj; omega)]
    rw [hsum, add_zero]
  · rw [if_neg hj, zero_add]
    rcases Nat.even_or_odd v with hv | hv
    · obtain ⟨a, ha⟩ := hv
      have hva : v = 2 * a := by omega
      have haj : a < j := by omega
      have hscaled' : 4 * (2 : ℤ) ^ (2 * a) * u = d * (f : ℤ) ^ 2 := by
        simpa only [hva] using hscaled
      have huquot : z / (2 : ℤ) ^ (2 * a) = u := by rw [← hva]
      rw [Finset.sum_eq_single a]
      · have hcases := table_even_rows hd hu χ hf a hscaled'
        rcases hcases with h | h
        · rw [if_pos ⟨hva, by simpa only [huquot] using h.1⟩, huquot]
          exact psi_two_even_one hd hu χ hf a j hscaled' h.1
        · rw [if_neg (by rw [huquot]; omega)]
          rw [psi_two_even_three hd hu χ hf a j hscaled' h.1, if_neg (by omega)]
      · intro b hb hba
        rw [if_neg (by dsimp [v] at hva; omega)]
      · intro haout
        exact (haout (Finset.mem_range.mpr haj)).elim
    · obtain ⟨a, ha⟩ := hv
      have hva : v = 2 * a + 1 := by omega
      have haj : a < j := by omega
      have hscaled' : 4 * (2 : ℤ) ^ (2 * a + 1) * u = d * (f : ℤ) ^ 2 := by
        simpa only [hva] using hscaled
      rw [psi_two_odd_row hd hu χ hf a j hscaled', if_neg (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg (by dsimp [v] at hva; omega)]

end DepthAspect.DyadicDiscriminantValues
