import DepthAspect.SquarefreeCoefficientProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The literal variable-exponent squarefree Euler product in (87)

The convergence argument works for every positive sigma. Together with the
square-part p-series, this gives the half-plane sigma>1/2 in Lemma 5.3.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.SquarefreeSigmaProduct

abbrev SquarefreeOdd := {u : ℕ // Squarefree u ∧ Odd u}

def primeWeight (σ : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ p ≠ 2 then 1 / ((p : ℝ) ^ σ * ((p : ℝ) - 1)) else 0

def productConstant (σ : ℝ) : ℝ := ∏' p : ℕ, (1 + primeWeight σ p)

 theorem primeWeight_nonneg (σ : ℝ) (p : ℕ) : 0 ≤ primeWeight σ p := by
  unfold primeWeight
  split_ifs with hp
  · have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
    have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  · rfl

 theorem primeWeight_le (σ : ℝ) (p : ℕ) :
    primeWeight σ p ≤ 2 * (p : ℝ) ^ (-(σ + 1)) := by
  unfold primeWeight
  split_ifs with hp
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.1.two_le
    have hpow : (p : ℝ) ^ (σ + 1) = (p : ℝ) ^ σ * p := by
      rw [Real.rpow_add hp0, Real.rpow_one]
    rw [Real.rpow_neg hp0.le, hpow]
    apply (div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hp0 _) (by linarith))).mpr
    have heq : 2 * ((p : ℝ) ^ σ * p)⁻¹ * ((p : ℝ) ^ σ * ((p : ℝ) - 1)) =
        2 * ((p : ℝ) - 1) / p := by
      field_simp [(Real.rpow_pos_of_pos hp0 σ).ne'] <;> ring
    rw [heq]
    apply (le_div_iff₀ hp0).mpr
    nlinarith
  · positivity

 theorem primeWeight_summable {σ : ℝ} (hσ : 0 < σ) : Summable (primeWeight σ) := by
  exact ((Real.summable_nat_rpow.mpr (by linarith : -(σ + 1) < -1)).mul_left 2).of_nonneg_of_le (primeWeight_nonneg σ) (primeWeight_le σ)

 theorem finite_products_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun s : Finset ℕ => ∏ p ∈ s, primeWeight σ p) :=
  summable_finsetProd_of_summable_nonneg (primeWeight_nonneg σ) (primeWeight_summable hσ)

 theorem product_multipliable {σ : ℝ} (hσ : 0 < σ) :
    Multipliable (fun p : ℕ => 1 + primeWeight σ p) :=
  multipliable_one_add_of_summable_prod (finite_products_summable hσ)

 theorem productConstant_eq_sum {σ : ℝ} (hσ : 0 < σ) : productConstant σ =
    ∑' s : Finset ℕ, ∏ p ∈ s, primeWeight σ p :=
  tprod_one_add (finite_products_summable hσ)

private theorem rpow_prod (s : Finset ℕ) (σ : ℝ) :
    ((∏ p ∈ s, p : ℕ) : ℝ) ^ σ = ∏ p ∈ s, (p : ℝ) ^ σ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg p)
      (by positivity), Finset.prod_insert hp, ih]

 theorem squarefree_weight_eq_product (σ : ℝ) (u : SquarefreeOdd) :
    1 / (((u : ℕ) : ℝ) ^ σ * ((u : ℕ).totient : ℝ)) =
      ∏ p ∈ (u : ℕ).primeFactors, primeWeight σ p := by
  have hprime (p : ℕ) (hp : p ∈ (u : ℕ).primeFactors) : p.Prime ∧ p ≠ 2 := by
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    intro heq
    exact u.property.2.not_two_dvd_nat (heq ▸ Nat.dvd_of_mem_primeFactors hp)
  calc
    _ = 1 / ((∏ p ∈ (u : ℕ).primeFactors, (p : ℝ) ^ σ) *
        ∏ p ∈ (u : ℕ).primeFactors, ((p : ℝ) - 1)) := by
      congr 2
      · rw [← rpow_prod, Nat.prod_primeFactors_of_squarefree u.property.1]
      · rw [SquarefreeCoefficientProduct.totient_squarefree u.property.1, Nat.cast_prod]
        apply Finset.prod_congr rfl
        intro p hp
        simpa only [Nat.cast_one] using
          (Nat.cast_sub (R := ℝ) (hprime p hp).1.one_le)
    _ = ∏ p ∈ (u : ℕ).primeFactors,
        1 / ((p : ℝ) ^ σ * ((p : ℝ) - 1)) := by
      rw [← Finset.prod_mul_distrib]
      simp only [one_div, Finset.prod_inv_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [primeWeight, if_pos (hprime p hp)]

 theorem squarefree_weight_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun u : SquarefreeOdd =>
      1 / (((u : ℕ) : ℝ) ^ σ * ((u : ℕ).totient : ℝ))) := by
  have h := (finite_products_summable hσ).comp_injective
    SquarefreeCoefficientProduct.primeFactors_injective
  simpa only [Function.comp_def, squarefree_weight_eq_product] using h

 theorem squarefree_weight_sum_le {σ : ℝ} (hσ : 0 < σ) :
    (∑' u : SquarefreeOdd, 1 / (((u : ℕ) : ℝ) ^ σ * ((u : ℕ).totient : ℝ))) ≤
      productConstant σ := by
  rw [productConstant_eq_sum hσ]
  have h := tsum_comp_le_tsum_of_inj (finite_products_summable hσ)
    (fun s => Finset.prod_nonneg fun p _ => primeWeight_nonneg σ p)
    SquarefreeCoefficientProduct.primeFactors_injective
  simpa only [Function.comp_def, squarefree_weight_eq_product] using h

/-- The total-index product is exactly the product over odd primes in (87). -/
theorem productConstant_eq_odd_primes (σ : ℝ) : productConstant σ =
    ∏' p : {p : ℕ // p.Prime ∧ p ≠ 2},
      (1 + 1 / (((p : ℕ) : ℝ) ^ σ * (((p : ℕ) : ℝ) - 1))) := by
  rw [productConstant, ← tprod_subtype_eq_of_mulSupport_subset
    (s := {p : ℕ | p.Prime ∧ p ≠ 2})]
  · apply tprod_congr
    intro p
    have hp : (p : ℕ).Prime ∧ (p : ℕ) ≠ 2 := p.property
    simp only [primeWeight, if_pos hp]
  · intro p hp
    by_contra hn
    have hnot : ¬ (p.Prime ∧ p ≠ 2) := hn
    exact hp (by simp only [primeWeight, if_neg hnot, add_zero])

end DepthAspect.SquarefreeSigmaProduct
