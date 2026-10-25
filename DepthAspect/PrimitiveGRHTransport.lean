import DepthAspect.PrimePowerRemoval
import DepthAspect.CharacterPrimeAverages
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.GCongr

/-!
# From the cited primitive GRH input to all character prime sums

The only GRH input is the primitive-character von-Mangoldt estimate, including
its principal conductor-one case. Prime-power removal, conductor-prime removal,
principal indicators and the modulus comparison are derived here. Consequently
(92) is not an additional analytic premise of the final prime-average argument.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.PrimitiveGRHTransport
open Finset PrimePowerRemoval

/-- The general primitive degree-one GRH theorem cited as IK Theorem 5.15.
This is an external theorem interface, before any discriminant or local mean
is selected. It includes the primitive principal character at conductor one. -/
def PrimitiveVonMangoldtEstimate (C : ℝ) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ∀ u : ℝ, 2 ≤ u →
      ‖vonMangoldtSum (fun n => χ (n : ZMod q)) u -
        (if χ = 1 then 1 else 0) * (u : ℂ)‖ ≤
          C * Real.sqrt u * Real.log (2 * (q : ℝ) * u) ^ 2

variable {q : ℕ} [NeZero q]

private theorem primeFactors_log_le :
    (∑ p ∈ q.primeFactors, Real.log p) ≤ Real.log q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hprod : 0 < ∏ p ∈ q.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hle := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  rw [← Real.log_prod (fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero), ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hprod) (by exact_mod_cast hle)

theorem primitive_eq_on_good_prime (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : p.Prime) (hpq : ¬p ∣ q) :
    χ.primitiveCharacter (p : ZMod χ.conductor) = χ (p : ZMod q) := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (hp.coprime_iff_not_dvd.mpr hpq)
  simpa only [Int.cast_natCast] using χ.primitiveCharacter_apply_of_isCoprime hc

theorem character_zero_on_bad_prime (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ q) : χ (p : ZMod q) = 0 := by
  have hc : ¬IsCoprime (p : ℤ) (q : ℤ) := by
    intro hc
    exact (hp.coprime_iff_not_dvd.mp (Nat.isCoprime_iff_coprime.mp hc)) hpq
  simpa only [Int.cast_natCast] using (χ.apply_eq_zero_iff (p : ℤ)).mpr hc

/-- Removing exactly the primes at which induction changes the character costs
at most logq, uniformly in the prime cutoff. -/
theorem conductor_prime_cost (χ : DirichletCharacter ℂ q) (u : ℝ) :
    ‖primeSum (fun n => χ (n : ZMod q)) u -
      primeSum (fun n => χ.primitiveCharacter (n : ZMod χ.conductor)) u‖ ≤ Real.log q := by
  rw [primeSum, primeSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊u⌋₊,
        ‖(if n.Prime then χ (n : ZMod q) * (Real.log n : ℂ) else 0) -
          (if n.Prime then χ.primitiveCharacter (n : ZMod χ.conductor) *
            (Real.log n : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 0 ⌊u⌋₊, if n.Prime ∧ n ∣ q then Real.log n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hp : n.Prime
      · by_cases hd : n ∣ q
        · have hlog : 0 ≤ Real.log (n : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
          simp only [hp, hd, true_and, ↓reduceIte, character_zero_on_bad_prime χ hp hd,
            zero_mul, zero_sub, norm_neg, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hlog]
          exact mul_le_of_le_one_left hlog (χ.primitiveCharacter.norm_le_one _)
        · simp [hp, hd, primitive_eq_on_good_prime χ hp hd]
      · simp [hp]
    _ = ∑ n ∈ (Icc 0 ⌊u⌋₊).filter (fun n => n.Prime ∧ n ∣ q), Real.log n :=
      by rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hn
        exact Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne q⟩
      · intro p hp hnot
        exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    _ ≤ _ := primeFactors_log_le

theorem primitive_principal_iff (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  have h := DirichletCharacter.changeLevel_eq_one_iff
    (χ := χ.primitiveCharacter) χ.conductor_dvd_level
  rw [χ.changeLevel_primitiveCharacter] at h
  exact h.symm

/-- All-character prime-sum bound before consolidating the elementary errors. -/
theorem prime_error_raw {C : ℝ} (hC : 0 ≤ C) (hGRH : PrimitiveVonMangoldtEstimate C)
    (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 2 ≤ u) :
    ‖primeSum (fun n => χ (n : ZMod q)) u -
      (if χ = 1 then 1 else 0) * (u : ℂ)‖ ≤
      C * Real.sqrt u * Real.log (2 * (q : ℝ) * u) ^ 2 +
        2 * Real.sqrt u * Real.log u + Real.log q := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hcpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcq : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hmain := hGRH χ.conductor hcpos χ.primitiveCharacter χ.primitiveCharacter_isPrimitive u hu
  simp only [primitive_principal_iff χ] at hmain
  have hmain' : ‖vonMangoldtSum (fun n => χ.primitiveCharacter (n : ZMod χ.conductor)) u -
      (if χ = 1 then 1 else 0) * (u : ℂ)‖ ≤
        C * Real.sqrt u * Real.log (2 * (q : ℝ) * u) ^ 2 := by
    apply hmain.trans
    have hcp : (1 : ℝ) ≤ χ.conductor := by exact_mod_cast hcpos
    have hqp : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    have hcqr : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hcq
    have hlogc : 0 ≤ Real.log (2 * (χ.conductor : ℝ) * u) :=
      Real.log_nonneg (by nlinarith)
    gcongr
  have hremove := character_norm_difference_le χ.primitiveCharacter (by linarith : 1 ≤ u)
  have hconductor := conductor_prime_cost χ u
  calc
    _ ≤ ‖primeSum (fun n => χ (n : ZMod q)) u -
          primeSum (fun n => χ.primitiveCharacter (n : ZMod χ.conductor)) u‖ +
        (‖primeSum (fun n => χ.primitiveCharacter (n : ZMod χ.conductor)) u -
          vonMangoldtSum (fun n => χ.primitiveCharacter (n : ZMod χ.conductor)) u‖ +
          ‖vonMangoldtSum (fun n => χ.primitiveCharacter (n : ZMod χ.conductor)) u -
            (if χ = 1 then 1 else 0) * (u : ℂ)‖) := by
      apply (norm_sub_le_norm_sub_add_norm_sub
        (primeSum (fun n => χ (n : ZMod q)) u)
        (primeSum (fun n => χ.primitiveCharacter (n : ZMod χ.conductor)) u)
        ((if χ = 1 then 1 else 0) * (u : ℂ))).trans
      exact add_le_add (le_refl _) (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ _ := by rw [norm_sub_rev] at hremove; linarith

/-- The elementary logarithms in the two removal errors fit the common GRH
envelope, with an absolute coefficient. -/
theorem error_absorption {u : ℝ} (hu : 2 ≤ u) :
    2 * Real.sqrt u * Real.log u + Real.log q ≤
      (3 / Real.log 4) * Real.sqrt u * Real.log (2 * (q : ℝ) * u) ^ 2 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hU : 1 ≤ Real.sqrt u := (Real.le_sqrt (by norm_num) (by linarith : 0 ≤ u)).mpr (by nlinarith)
  have hL : Real.log 4 ≤ Real.log (2 * (q : ℝ) * u) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hL0 : 0 ≤ Real.log (2 * (q : ℝ) * u) := h4.le.trans hL
  have hlogu : Real.log u ≤ Real.log (2 * (q : ℝ) * u) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlogq : Real.log q ≤ Real.log (2 * (q : ℝ) * u) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hratio : Real.log (2 * (q : ℝ) * u) ≤
      Real.log (2 * (q : ℝ) * u) ^ 2 / Real.log 4 := by
    apply (le_div_iff₀ h4).mpr
    nlinarith
  calc
    _ ≤ 3 * Real.sqrt u * Real.log (2 * (q : ℝ) * u) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogu (by positivity : 0 ≤ 2 * Real.sqrt u),
        mul_le_mul_of_nonneg_right hU hL0]
    _ ≤ 3 * Real.sqrt u * (Real.log (2 * (q : ℝ) * u) ^ 2 / Real.log 4) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- Equation (92) is now a consequence of the primitive external input. -/
theorem all_characters_estimate {C : ℝ} (hC : 0 ≤ C)
    (hGRH : PrimitiveVonMangoldtEstimate C) :
    CharacterPrimeAverages.GRHCharacterEstimate (q := q) (C + 3 / Real.log 4) := by
  intro χ u hu
  have h := prime_error_raw hC hGRH χ hu
  have he := error_absorption (q := q) hu
  change ‖primeSum (fun n => χ (n : ZMod q)) u -
    (if χ = 1 then 1 else 0) * (u : ℂ)‖ ≤ _
  nlinarith

end DepthAspect.PrimitiveGRHTransport
