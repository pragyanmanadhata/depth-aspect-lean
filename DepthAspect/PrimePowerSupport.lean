import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compact Fourier support makes the prime-power sum finite

The support rectangle is constructed from the actual conductor logarithm
and Fourier-support endpoint. No convergence or finite-support assertion
about the prime-power expression is assumed.
-/
open scoped BigOperators
namespace DepthAspect.PrimePowerSupport

noncomputable def indexBox (L s : ℝ) : Finset (ℕ × ℕ) :=
  Finset.Icc 2 ⌊Real.exp (s * L)⌋₊ ×ˢ Finset.Icc 1 ⌊s * L / Real.log 2⌋₊

/-- A nonzero supported test value bounds both the base and exponent. -/
theorem supported_index_mem {L s : ℝ} (hL : 0 < L) {h : ℝ → ℂ}
    (hsupp : Function.support h ⊆ Set.Icc (-s) s) {p j : ℕ}
    (hp : 2 ≤ p) (hj : 1 ≤ j)
    (hh : h ((j : ℝ) * Real.log (p : ℝ) / L) ≠ 0) :
    (p, j) ∈ indexBox L s := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hpR
  have hfreq : (j : ℝ) * Real.log (p : ℝ) ≤ s * L :=
    (div_le_iff₀ hL).mp (hsupp hh).2
  have hpbound : (p : ℝ) ≤ Real.exp (s * L) := by
    apply (Real.log_le_iff_le_exp hp0).mp
    calc
      Real.log (p : ℝ) ≤ (j : ℝ) * Real.log (p : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hjR) (hlog2.le.trans hlogp)]
      _ ≤ _ := hfreq
  have hjbound : (j : ℝ) ≤ s * L / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    exact (mul_le_mul_of_nonneg_left hlogp (Nat.cast_nonneg _)).trans hfreq
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp, Nat.le_floor hpbound⟩,
    Finset.mem_Icc.mpr ⟨hj, Nat.le_floor hjbound⟩⟩

/-- The sharper support condition used to truncate each prime-power sum:
a nonzero test value forces p^j ≤ exp(sL). -/
theorem supported_prime_power_le {L s : ℝ} (hL : 0 < L) {h : ℝ → ℂ}
    (hsupp : Function.support h ⊆ Set.Icc (-s) s) {p j : ℕ}
    (hp : 0 < p) (hh : h ((j : ℝ) * Real.log (p : ℝ) / L) ≠ 0) :
    (p : ℝ) ^ j ≤ Real.exp (s * L) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hfreq := (div_le_iff₀ hL).mp (hsupp hh).2
  apply (Real.log_le_iff_le_exp (pow_pos hpR j)).mp
  simpa only [Real.log_pow] using hfreq

/-- The actual coefficient-weighted odd-prime expression, extended by zero
outside positive exponents and odd prime bases. -/
noncomputable def primePowerTerm (L : ℝ) (h : ℝ → ℂ)
    (weight : ℕ → ℕ → ℂ) (pj : ℕ × ℕ) : ℂ :=
  if pj.1.Prime ∧ pj.1 ≠ 2 ∧ 1 ≤ pj.2 then
    weight pj.1 pj.2 * h ((pj.2 : ℝ) * Real.log (pj.1 : ℝ) / L)
  else 0

/-- The support is a subset of the constructed finite rectangle. -/
theorem primePowerTerm_support_subset {L s : ℝ} (hL : 0 < L) {h : ℝ → ℂ}
    (hsupp : Function.support h ⊆ Set.Icc (-s) s) (weight : ℕ → ℕ → ℂ) :
    Function.support (primePowerTerm L h weight) ⊆ (indexBox L s : Set (ℕ × ℕ)) := by
  intro pj hpj
  have hpj' : primePowerTerm L h weight pj ≠ 0 := hpj
  unfold primePowerTerm at hpj'
  split_ifs at hpj' with hc
  · have hh : h ((pj.2 : ℝ) * Real.log (pj.1 : ℝ) / L) ≠ 0 := by
      intro hz
      exact hpj' (by rw [hz, mul_zero])
    exact supported_index_mem hL hsupp hc.1.two_le hc.2.2 hh
  · exact (hpj' rfl).elim

/-- Compact support yields genuine finite support for arbitrary coefficients. -/
theorem primePowerTerm_finite_support {L s : ℝ} (hL : 0 < L) {h : ℝ → ℂ}
    (hsupp : Function.support h ⊆ Set.Icc (-s) s) (weight : ℕ → ℕ → ℂ) :
    (Function.support (primePowerTerm L h weight)).Finite :=
  (indexBox L s).finite_toSet.subset (primePowerTerm_support_subset hL hsupp weight)

/-- The series converges because its support is finite. -/
theorem primePowerTerm_summable {L s : ℝ} (hL : 0 < L) {h : ℝ → ℂ}
    (hsupp : Function.support h ⊆ Set.Icc (-s) s) (weight : ℕ → ℕ → ℂ) :
    Summable (primePowerTerm L h weight) :=
  summable_of_hasFiniteSupport (primePowerTerm_finite_support hL hsupp weight)

/-- The prime-power double series is exactly a finite sum, so every finite
spectral average may be interchanged with this expression. -/
theorem primePowerTerm_tsum_eq {L s : ℝ} (hL : 0 < L) {h : ℝ → ℂ}
    (hsupp : Function.support h ⊆ Set.Icc (-s) s) (weight : ℕ → ℕ → ℂ) :
    (∑' pj : ℕ × ℕ, primePowerTerm L h weight pj) =
      ∑ pj ∈ indexBox L s, primePowerTerm L h weight pj := by
  apply tsum_eq_sum
  intro pj hpj
  by_contra hn
  exact hpj (primePowerTerm_support_subset hL hsupp weight hn)

end DepthAspect.PrimePowerSupport
