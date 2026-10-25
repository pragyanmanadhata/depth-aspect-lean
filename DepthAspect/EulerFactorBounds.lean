import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The explicit finite-factor constants in Lemma 2.2

These are the literal finite geometric corrections and the paper's threshold
and small-prime product. The inequalities are proved independently of any
L-series size bound. Identification with the Euler correction is separate.
-/

open scoped BigOperators
namespace DepthAspect.EulerFactorBounds

noncomputable def threshold (δ : ℝ) : ℝ := max 3 (4 / δ)
noncomputable def smallPrimes (δ : ℝ) : Finset ℕ := ⌈threshold δ⌉₊.primesBelow
noncomputable def A (δ : ℝ) : ℝ :=
  ∏ p ∈ smallPrimes δ, (1 + 2 / ((p : ℝ) - 1))
noncomputable def correction (c : ℂ) (p : ℝ) (e : ℕ) : ℂ :=
  1 + (1 - c) * ∑ j ∈ Finset.range e, ((p : ℂ)⁻¹) ^ (j + 1)

theorem mem_smallPrimes_iff (δ : ℝ) (p : ℕ) :
    p ∈ smallPrimes δ ↔ p.Prime ∧ (p : ℝ) < threshold δ := by
  simp only [smallPrimes, Nat.mem_primesBelow, Nat.lt_ceil, and_comm]

theorem factor_one_le {p : ℝ} (hp : 1 < p) : 1 ≤ 1 + 2 / (p - 1) := by
  have : 0 ≤ 2 / (p - 1) := by positivity
  linarith

theorem A_one_le (δ : ℝ) : 1 ≤ A δ := by
  apply Finset.one_le_prod
  intro p hp
  exact factor_one_le (by exact_mod_cast ((mem_smallPrimes_iff δ p).mp hp).1.one_lt)

theorem A_pos (δ : ℝ) : 0 < A δ := lt_of_lt_of_le zero_lt_one (A_one_le δ)

/-- The prime 2 is always included in the paper's small-prime product. -/
theorem A_three_le (δ : ℝ) : 3 ≤ A δ := by
  have htwo : 2 ∈ smallPrimes δ := by
    apply (mem_smallPrimes_iff δ 2).mpr
    exact ⟨by decide, lt_of_lt_of_le (by norm_num) (le_max_left _ _)⟩
  have h := Finset.prod_le_prod_of_subset_of_one_le
    (Finset.singleton_subset_iff.mpr htwo)
    (f := fun p : ℕ => 1 + 2 / ((p : ℝ) - 1))
    (by intro p hp; simp only [Finset.mem_singleton] at hp; subst p; norm_num)
    (by
      intro p hp _
      exact factor_one_le (by exact_mod_cast ((mem_smallPrimes_iff δ p).mp hp).1.one_lt))
  norm_num [A] at h
  exact h

/-- The finite geometric sum, uniformly in the conductor exponent. -/
theorem inverse_power_sum_le {p : ℝ} (hp : 1 < p) (e : ℕ) :
    (∑ j ∈ Finset.range e, p⁻¹ ^ (j + 1)) ≤ 1 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp0)
  have hr1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  have hsum := (hasSum_geometric_of_lt_one hr0 hr1).mul_left p⁻¹
  have hb := hsum.summable.sum_le_tsum (Finset.range e)
    (fun j _ => mul_nonneg hr0 (pow_nonneg hr0 j))
  rw [hsum.tsum_eq] at hb
  have heq : p⁻¹ * (1 - p⁻¹)⁻¹ = 1 / (p - 1) := by
    field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp)]
  simpa only [← pow_succ', heq] using hb

/-- The actual finite polynomial has the stated primewise upper bound. -/
theorem norm_correction_le (c : ℂ) (hc : ‖c‖ ≤ 1) {p : ℝ} (hp : 1 < p) (e : ℕ) :
    ‖correction c p e‖ ≤ 1 + 2 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hn : ‖∑ j ∈ Finset.range e, ((p : ℂ)⁻¹) ^ (j + 1)‖ ≤ 1 / (p - 1) := by
    calc
      _ ≤ ∑ j ∈ Finset.range e, ‖((p : ℂ)⁻¹) ^ (j + 1)‖ := norm_sum_le _ _
      _ = ∑ j ∈ Finset.range e, p⁻¹ ^ (j + 1) := by
        simp only [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hp0]
      _ ≤ _ := inverse_power_sum_le hp e
  have hsub : ‖1 - c‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num only [norm_one]; linarith
  unfold correction
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(1 - c) * ∑ j ∈ Finset.range e, ((p : ℂ)⁻¹) ^ (j + 1)‖ :=
      norm_add_le _ _
    _ ≤ 1 + 2 * (1 / (p - 1)) := by
      rw [norm_one, norm_mul]
      exact add_le_add le_rfl (mul_le_mul hsub hn (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- The explicit logarithmic comparison for every p beyond Tδ. -/
theorem log_factor_le {δ p : ℝ} (hδ : 0 < δ) (hp : threshold δ ≤ p) :
    Real.log (1 + 2 / (p - 1)) ≤ δ * Real.log p := by
  have hp3 : 3 ≤ p := (le_max_left _ _).trans hp
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hlog : 1 ≤ Real.log p := by
    apply (Real.le_log_iff_exp_le hp0).mpr
    exact Real.exp_one_lt_three.le.trans hp3
  have hfrac : 2 / (p - 1) ≤ 4 / p := by
    apply (div_le_div_iff₀ hpm hp0).mpr
    linarith
  have hδp : 4 / p ≤ δ := by
    apply (div_le_iff₀ hp0).mpr
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hp)
    nlinarith
  calc
    _ ≤ (1 + 2 / (p - 1)) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 2 / (p - 1) := by ring
    _ ≤ 4 / p := hfrac
    _ ≤ δ := hδp
    _ ≤ δ * Real.log p := by nlinarith

theorem factor_le_rpow {δ p : ℝ} (hδ : 0 < δ) (hp : threshold δ ≤ p) :
    1 + 2 / (p - 1) ≤ p ^ δ := by
  have hp3 : 3 ≤ p := (le_max_left _ _).trans hp
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hb : 0 < 1 + 2 / (p - 1) := by positivity
  rw [Real.rpow_def_of_pos hp0]
  apply (Real.log_le_iff_le_exp hb).mp
  simpa only [mul_comm] using log_factor_le hδ hp

/-- The product of the actual finite local corrections is bounded by the
paper's Aδ f^δ. This includes f=1 and arbitrary zero-valued local characters. -/
theorem finite_correction_product_bound (δ : ℝ) (hδ : 0 < δ) (f : ℕ) (hf : 0 < f)
    (c : ℕ → ℂ) (hc : ∀ p ∈ f.primeFactors, ‖c p‖ ≤ 1) :
    ‖∏ p ∈ f.primeFactors, correction (c p) (p : ℝ) (f.factorization p)‖ ≤
      A δ * (f : ℝ) ^ δ := by
  classical
  let S := f.primeFactors.filter (fun p : ℕ => (p : ℝ) < threshold δ)
  let b : ℕ → ℝ := fun p => 1 + 2 / ((p : ℝ) - 1)
  have hprime (p : ℕ) (hp : p ∈ f.primeFactors) : (1 : ℝ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hloc (p : ℕ) (hp : p ∈ f.primeFactors) :
      ‖correction (c p) (p : ℝ) (f.factorization p)‖ ≤
        (if (p : ℝ) < threshold δ then b p else 1) * (p : ℝ) ^ δ := by
    have hb := norm_correction_le (c p) (hc p hp) (hprime p hp) (f.factorization p)
    split_ifs with hs
    · exact hb.trans (le_mul_of_one_le_right
        (le_trans zero_le_one (factor_one_le (hprime p hp)))
        (Real.one_le_rpow (hprime p hp).le hδ.le))
    · simpa only [one_mul] using hb.trans (factor_le_rpow hδ (le_of_not_gt hs))
  have hS : S ⊆ smallPrimes δ := by
    intro p hp
    obtain ⟨hpf, hpt⟩ := Finset.mem_filter.mp hp
    exact (mem_smallPrimes_iff δ p).mpr ⟨Nat.prime_of_mem_primeFactors hpf, hpt⟩
  have hbA : (∏ p ∈ S, b p) ≤ A δ := by
    apply Finset.prod_le_prod_of_subset_of_one_le hS
    · intro p hp
      exact (factor_one_le (hprime p (Finset.mem_filter.mp hp).1)).trans' zero_le_one
    · intro p hp _
      exact factor_one_le (by exact_mod_cast ((mem_smallPrimes_iff δ p).mp hp).1.one_lt)
  have hrad : (∏ p ∈ f.primeFactors, (p : ℝ)) ≤ (f : ℝ) := by
    have hnat := Nat.le_of_dvd hf (Nat.prod_primeFactors_dvd f)
    have hcast : ((∏ p ∈ f.primeFactors, p : ℕ) : ℝ) ≤ (f : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_prod] using hcast
  have hrpow : (∏ p ∈ f.primeFactors, (p : ℝ) ^ δ) ≤ (f : ℝ) ^ δ := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    exact Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) hrad hδ.le
  calc
    _ = ∏ p ∈ f.primeFactors, ‖correction (c p) (p : ℝ) (f.factorization p)‖ := norm_prod _ _
    _ ≤ ∏ p ∈ f.primeFactors,
        (if (p : ℝ) < threshold δ then b p else 1) * (p : ℝ) ^ δ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) hloc
    _ = (∏ p ∈ S, b p) * (∏ p ∈ f.primeFactors, (p : ℝ) ^ δ) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
    _ ≤ A δ * (f : ℝ) ^ δ := mul_le_mul hbA hrpow
      (Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) δ))
      (A_pos δ).le

/-- The exact elementary logarithm constant appearing in the paper. -/
theorem log_le_exp_constant {δ x : ℝ} (hδ : 0 < δ) (hx : 0 < x) :
    Real.log x ≤ (2 / (Real.exp 1 * δ)) * x ^ (δ / 2) := by
  have h := Real.add_one_le_exp ((δ / 2) * Real.log x - 1)
  have heq : Real.exp ((δ / 2) * Real.log x - 1) =
      x ^ (δ / 2) / Real.exp 1 := by
    rw [Real.exp_sub, Real.rpow_def_of_pos hx]
    congr 2
    ring
  rw [heq] at h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hm := (le_div_iff₀ he).mp (by linarith :
    δ / 2 * Real.log x ≤ x ^ (δ / 2) / Real.exp 1)
  calc
    Real.log x ≤ (2 * x ^ (δ / 2)) / (Real.exp 1 * δ) :=
      (le_div_iff₀ (mul_pos he hδ)).mpr (by nlinarith)
    _ = _ := by ring

theorem two_add_log_le_exp_constant {δ D d : ℝ} (hδ : 0 < δ)
    (hD : 1 ≤ D) (hd : 0 < d) (hdD : d ≤ D) :
    2 + Real.log d ≤ (2 + 2 / (Real.exp 1 * δ)) * D ^ (δ / 2) := by
  have hlog : Real.log d ≤ Real.log D := Real.log_le_log hd hdD
  have hpow : 1 ≤ D ^ (δ / 2) := Real.one_le_rpow hD (by positivity)
  have hb := log_le_exp_constant hδ (lt_of_lt_of_le zero_lt_one hD)
  nlinarith

noncomputable def explicitConstant (δ : ℝ) : ℝ := A δ * (2 + 2 / (Real.exp 1 * δ))

theorem explicitConstant_pos {δ : ℝ} (hδ : 0 < δ) : 0 < explicitConstant δ := by
  unfold explicitConstant
  have hA := A_pos δ
  have he := Real.exp_pos 1
  positivity

/-- The simpler ordered-period constant is already at most the exact
constant printed in the paper. This comparison needs no Euler identity. -/
theorem ordered_constant_le_explicit {δ : ℝ} (hδ : 0 < δ) :
    2 + δ⁻¹ ≤ explicitConstant δ := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hc : 1 ≤ 6 / Real.exp 1 := (le_div_iff₀ he).mpr
    (by linarith [Real.exp_one_lt_three])
  have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hbound : 2 + δ⁻¹ ≤ 3 * (2 + 2 / (Real.exp 1 * δ)) := by
    have hmul := mul_le_mul_of_nonneg_right hc hδi
    have heq : 3 * (2 + 2 / (Real.exp 1 * δ)) =
        6 + (6 / Real.exp 1) * δ⁻¹ := by ring
    rw [heq]
    nlinarith
  exact hbound.trans (mul_le_mul_of_nonneg_right (A_three_le δ) (by positivity))

/-- The exact algebra assembling the paper's displayed constant. The only
L-value input here is the primitive-character logarithmic bound (8); no
imprimitive L-value or class-number power bound is assumed. -/
theorem norm_value_times_correction_bound {δ d D : ℝ} (hδ : 0 < δ) (hd : 1 ≤ d)
    (f : ℕ) (hf : 0 < f) (hD : D = d * (f : ℝ) ^ 2)
    (z : ℂ) (hz : ‖z‖ ≤ 2 + Real.log d)
    (c : ℕ → ℂ) (hc : ∀ p ∈ f.primeFactors, ‖c p‖ ≤ 1) :
    ‖z * ∏ p ∈ f.primeFactors, correction (c p) (p : ℝ) (f.factorization p)‖ ≤
      explicitConstant δ * D ^ δ := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hf2 : 1 ≤ (f : ℝ) ^ 2 := by nlinarith
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hdD : d ≤ D := by rw [hD]; nlinarith
  have hfD : (f : ℝ) ^ 2 ≤ D := by rw [hD]; nlinarith
  have hfpower : (f : ℝ) ^ δ ≤ D ^ (δ / 2) := by
    calc
      (f : ℝ) ^ δ = ((f : ℝ) ^ 2) ^ (δ / 2) := by
        rw [← Real.rpow_natCast_mul hf0.le 2 (δ / 2)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) hfD (by positivity)
  have hzpower : ‖z‖ ≤ (2 + 2 / (Real.exp 1 * δ)) * D ^ (δ / 2) :=
    hz.trans (two_add_log_le_exp_constant hδ hD1 hd0 hdD)
  have hprod := (finite_correction_product_bound δ hδ f hf c hc).trans
    (mul_le_mul_of_nonneg_left hfpower (A_pos δ).le)
  calc
    _ = ‖z‖ * ‖∏ p ∈ f.primeFactors,
        correction (c p) (p : ℝ) (f.factorization p)‖ := norm_mul _ _
    _ ≤ ((2 + 2 / (Real.exp 1 * δ)) * D ^ (δ / 2)) *
        (A δ * D ^ (δ / 2)) :=
      mul_le_mul hzpower hprod (norm_nonneg _) (by positivity)
    _ = explicitConstant δ * D ^ δ := by
      unfold explicitConstant
      have hpow : D ^ (δ / 2) * D ^ (δ / 2) = D ^ δ := by
        rw [← Real.rpow_add hD0]
        congr 1
        ring
      calc
        _ = (A δ * (2 + 2 / (Real.exp 1 * δ))) *
            (D ^ (δ / 2) * D ^ (δ / 2)) := by ring
        _ = _ := by rw [hpow]

end DepthAspect.EulerFactorBounds
