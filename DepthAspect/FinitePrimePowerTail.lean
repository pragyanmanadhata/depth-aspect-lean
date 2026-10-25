import DepthAspect.PrimePowerAverages
import DepthAspect.PrimePowerSupport
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

namespace DepthAspect.FinitePrimePowerTail

open PrimePowerTail PrimePowerAverages

/-- The nonnegative majorant is genuinely summable over pairs, not only as
an iterated conditionally convergent sum. -/
theorem higherPower_prod_summable :
    Summable (fun pj : OddPrime × ℕ => higherPowerTerm (pj.1.val : ℝ) pj.2) := by
  apply (summable_prod_of_nonneg
    (f := fun pj : OddPrime × ℕ => higherPowerTerm (pj.1.val : ℝ) pj.2)
    (fun pj => higherPowerTerm_nonneg pj.1 pj.2)).2
  constructor
  · intro p
    have hp : (3 : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast p.property.2
    exact (higherPowerTerm_hasSum (p := (p.val : ℝ)) hp).summable
  · exact oddPrime_higherPower_summable

theorem higherPower_prod_tsum_le :
    (∑' pj : OddPrime × ℕ, higherPowerTerm (pj.1.val : ℝ) pj.2) ≤ 48 := by
  rw [higherPower_prod_summable.tsum_prod]
  exact oddPrime_higherPower_tsum_le_forty_eight

/-- Every finite box of actual prime/exponent weights is controlled by the
same convergent positive series, after the exact shift j ↦ j-3. -/
theorem finite_weight_sum_le (S : Finset (ℕ × ℕ))
    (hS : ∀ pj ∈ S, pj.1.Prime ∧ 3 ≤ pj.1 ∧ 3 ≤ pj.2) :
    (∑ pj ∈ S, Real.log (pj.1 : ℝ) / (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2)) ≤ 48 := by
  classical
  let e : S → OddPrime × ℕ := fun pj =>
    (⟨pj.val.1, (hS pj.val pj.property).1, (hS pj.val pj.property).2.1⟩,
      pj.val.2 - 3)
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : OddPrime × ℕ => z.1.val) hxy
    · have h := congrArg Prod.snd hxy
      have hx := (hS x.val x.property).2.2
      have hy := (hS y.val y.property).2.2
      change x.val.2 - 3 = y.val.2 - 3 at h
      omega
  have hw (pj : S) : higherPowerTerm ((e pj).1.val : ℝ) (e pj).2 =
      Real.log (pj.val.1 : ℝ) / (pj.val.1 : ℝ) ^ ((pj.val.2 : ℝ) / 2) := by
    dsimp [e, higherPowerTerm]
    rw [Nat.cast_sub (hS pj.val pj.property).2.2]
    norm_num
  have hid : (∑ pj ∈ S, Real.log (pj.1 : ℝ) / (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2)) =
      ∑ pj ∈ S.attach.image e, higherPowerTerm (pj.1.val : ℝ) pj.2 := by
    rw [Finset.sum_image he.injOn]
    simp_rw [hw]
    exact (Finset.sum_attach S _).symm
  rw [hid]
  exact (higherPower_prod_summable.sum_le_tsum _
    (fun pj _ => higherPowerTerm_nonneg pj.1 pj.2)).trans higherPower_prod_tsum_le

/-- Uniform finite-box version of the tail estimate, with bounds required
only at the actual summation indices. -/
theorem finite_twisted_tail_bound (S : Finset (ℕ × ℕ))
    (hS : ∀ pj ∈ S, pj.1.Prime ∧ 3 ≤ pj.1 ∧ 3 ≤ pj.2)
    (w : ℕ → ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ pj ∈ S, ‖w pj.1 pj.2‖ ≤ C) :
    ‖∑ pj ∈ S, (Real.log (pj.1 : ℝ) / (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2)) •
      w pj.1 pj.2‖ ≤ 48 * C := by
  have hnonneg (pj : ℕ × ℕ) (hpj : pj ∈ S) :
      0 ≤ Real.log (pj.1 : ℝ) / (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2) := by
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (by have := (hS pj hpj).2.1; omega : 1 ≤ pj.1)
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ ∑ pj ∈ S, ‖(Real.log (pj.1 : ℝ) /
        (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2)) • w pj.1 pj.2‖ := norm_sum_le _ _
    _ ≤ ∑ pj ∈ S, (Real.log (pj.1 : ℝ) /
        (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2)) * C := by
      apply Finset.sum_le_sum
      intro pj hpj
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg pj hpj)]
      exact mul_le_mul_of_nonneg_left (hw pj hpj) (hnonneg pj hpj)
    _ = (∑ pj ∈ S, Real.log (pj.1 : ℝ) /
        (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2)) * C := (Finset.sum_mul ..).symm
    _ ≤ 48 * C := mul_le_mul_of_nonneg_right (finite_weight_sum_le S hS) hC

/-- The literal higher-power part in the explicit formula, including its
support indicator, has norm at most 96 H before the factor 2/L. -/
theorem finite_primePowerTerm_tail_bound (S : Finset (ℕ × ℕ))
    (hS : ∀ pj ∈ S, pj.1.Prime ∧ 3 ≤ pj.1 ∧ 3 ≤ pj.2)
    (a : ℕ → ℕ → ℂ) (ha : ∀ pj ∈ S, ‖a pj.1 pj.2‖ ≤ 2)
    (h : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H) (hh : ∀ x, ‖h x‖ ≤ H) (L : ℝ) :
    ‖∑ pj ∈ S, PrimePowerSupport.primePowerTerm L h
      (fun p j => (Real.log (p : ℝ) : ℂ) /
        (((p : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * a p j) pj‖ ≤ 96 * H := by
  have heq : (∑ pj ∈ S, PrimePowerSupport.primePowerTerm L h
      (fun p j => (Real.log (p : ℝ) : ℂ) /
        (((p : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * a p j) pj) =
      ∑ pj ∈ S, (Real.log (pj.1 : ℝ) / (pj.1 : ℝ) ^ ((pj.2 : ℝ) / 2)) •
        (a pj.1 pj.2 * h ((pj.2 : ℝ) * Real.log (pj.1 : ℝ) / L)) := by
    apply Finset.sum_congr rfl
    intro pj hpj
    have hc := hS pj hpj
    have hcond : pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2 :=
      ⟨hc.1, by omega, by omega⟩
    simp only [PrimePowerSupport.primePowerTerm, if_pos hcond,
      Complex.real_smul, Complex.ofReal_div, mul_assoc]
  rw [heq]
  have hb := finite_twisted_tail_bound S hS
    (fun p j => a p j * h ((j : ℝ) * Real.log (p : ℝ) / L)) (2 * H)
    (by positivity) (by
      intro pj hpj
      rw [norm_mul]
      exact mul_le_mul (ha pj hpj) (hh _) (norm_nonneg _) (by norm_num))
  linarith

/-- A version for a rectangular truncation, where nonprimes and the bad prime
2 are present in the finite set but vanish by the actual support indicator. -/
theorem finite_primePowerTerm_tail_bound_of_ge_three (S : Finset (ℕ × ℕ))
    (hS : ∀ pj ∈ S, 3 ≤ pj.2)
    (a : ℕ → ℕ → ℂ)
    (ha : ∀ pj ∈ S, pj.1.Prime → pj.1 ≠ 2 → ‖a pj.1 pj.2‖ ≤ 2)
    (h : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H) (hh : ∀ x, ‖h x‖ ≤ H) (L : ℝ) :
    ‖∑ pj ∈ S, PrimePowerSupport.primePowerTerm L h
      (fun p j => (Real.log (p : ℝ) : ℂ) /
        (((p : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * a p j) pj‖ ≤ 96 * H := by
  classical
  let T := S.filter (fun pj => pj.1.Prime ∧ pj.1 ≠ 2)
  have hsubset : T ⊆ S := Finset.filter_subset _ _
  have heq : (∑ pj ∈ T, PrimePowerSupport.primePowerTerm L h
      (fun p j => (Real.log (p : ℝ) : ℂ) /
        (((p : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * a p j) pj) =
      ∑ pj ∈ S, PrimePowerSupport.primePowerTerm L h
      (fun p j => (Real.log (p : ℝ) : ℂ) /
        (((p : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * a p j) pj := by
    apply Finset.sum_subset hsubset
    intro pj hpj hnot
    have hc : ¬ (pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2) := by
      intro hc
      exact hnot (Finset.mem_filter.mpr ⟨hpj, hc.1, hc.2.1⟩)
    simp only [PrimePowerSupport.primePowerTerm, if_neg hc]
  rw [← heq]
  apply finite_primePowerTerm_tail_bound T _ a _ h H hH hh L
  · intro pj hpj
    obtain ⟨hpjS, hp, hp2⟩ := Finset.mem_filter.mp hpj
    exact ⟨hp, by have := hp.two_le; omega, hS pj hpjS⟩
  · intro pj hpj
    obtain ⟨hpjS, hp, hp2⟩ := Finset.mem_filter.mp hpj
    exact ha pj hpjS hp hp2

end DepthAspect.FinitePrimePowerTail
