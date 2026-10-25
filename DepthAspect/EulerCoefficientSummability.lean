import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Absolute convergence from summable local Euler-factor excess

This supplies the convergence step needed in Lemma 6.2. It starts from
actual local prime-power sums, not from a global convergence assumption.
-/
namespace DepthAspect.EulerCoefficientSummability

open Nat
open scoped BigOperators Topology

/-- A nonnegative multiplicative function is summable if the excess of
its local prime-power sum over one admits a nonnegative summable majorant.
The proof bounds every finite partial sum by the same convergent Euler
product majorant, using actual smooth-number coefficient sums. -/
theorem summable_of_local_majorant {f g : ℕ → ℝ}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hfn : ∀ n, 0 ≤ f n)
    (hfm : ∀ {m n}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖f (p ^ j)‖))
    (hgn : ∀ n, 0 ≤ g n) (hgs : Summable g)
    (hbound : ∀ p : ℕ, p.Prime → (∑' j : ℕ, f (p ^ j)) ≤ 1 + g p) :
    Summable f := by
  apply summable_of_sum_range_le hfn (c := Real.exp (∑' n : ℕ, g n))
  intro N
  let S := Finset.range N
  let A := Nat.factoredNumbers S
  have heuler := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hf1 hfm hlocal S
  have hind : HasSum (A.indicator f)
      (∏ p ∈ S with p.Prime, ∑' j : ℕ, f (p ^ j)) :=
    hasSum_subtype_iff_indicator.mp heuler.2
  have hterm : ∀ n ∈ Finset.range N, f n = A.indicator f n := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [hf0, Set.indicator]
    · have hmem : n ∈ A := by
        apply Nat.mem_factoredNumbers_iff_forall_le.mpr
        refine ⟨hn0, ?_⟩
        intro p hpn _ _
        exact Finset.mem_range.mpr (hpn.trans_lt (Finset.mem_range.mp hn))
      exact (Set.indicator_of_mem hmem f).symm
  calc
    (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range N, A.indicator f n :=
      Finset.sum_congr rfl hterm
    _ ≤ ∑' n : ℕ, A.indicator f n :=
      hind.summable.sum_le_tsum _ (fun n _ => Set.indicator_nonneg (fun i _ => hfn i) n)
    _ = ∏ p ∈ S with p.Prime, ∑' j : ℕ, f (p ^ j) := hind.tsum_eq
    _ ≤ ∏ p ∈ S with p.Prime, (1 + g p) := by
      apply Finset.prod_le_prod
      · intro p _
        exact tsum_nonneg (fun j => hfn _)
      · intro p hp
        exact hbound p (Finset.mem_filter.mp hp).2
    _ ≤ Real.exp (∑ p ∈ S with p.Prime, g p) :=
      Real.prod_one_add_le_exp_sum _ hgn
    _ ≤ Real.exp (∑' n : ℕ, g n) :=
      Real.exp_le_exp.mpr (hgs.sum_le_tsum _ (fun n _ => hgn n))

/-- The same proof supplies a concrete global bound, not only convergence. -/
theorem tsum_le_exp_tsum_of_local_majorant {f g : ℕ → ℝ}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hfn : ∀ n, 0 ≤ f n)
    (hfm : ∀ {m n}, m.Coprime n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖f (p ^ j)‖))
    (hgn : ∀ n, 0 ≤ g n) (hgs : Summable g)
    (hbound : ∀ p : ℕ, p.Prime → (∑' j : ℕ, f (p ^ j)) ≤ 1 + g p) :
    ∑' n : ℕ, f n ≤ Real.exp (∑' n : ℕ, g n) := by
  have hsum := summable_of_local_majorant hf0 hf1 hfn hfm hlocal hgn hgs hbound
  have hnorm : (fun n : ℕ => ‖f n‖) = f := by
    funext n
    exact Real.norm_of_nonneg (hfn n)
  have hsumNorm : Summable (fun n : ℕ => ‖f n‖) := by
    rw [hnorm]
    exact hsum
  have heuler := EulerProduct.eulerProduct hf1 hfm hsumNorm hf0
  have hle : ∀ N : ℕ, (∏ p ∈ Finset.range N with p.Prime, ∑' j : ℕ, f (p ^ j)) ≤
      Real.exp (∑' n : ℕ, g n) := by
    intro N
    calc
      _ ≤ ∏ p ∈ Finset.range N with p.Prime, (1 + g p) := by
        apply Finset.prod_le_prod
        · intro p _
          exact tsum_nonneg (fun j => hfn _)
        · intro p hp
          exact hbound p (Finset.mem_filter.mp hp).2
      _ ≤ Real.exp (∑ p ∈ Finset.range N with p.Prime, g p) :=
        Real.prod_one_add_le_exp_sum _ hgn
      _ ≤ _ := Real.exp_le_exp.mpr (hgs.sum_le_tsum _ (fun n _ => hgn n))
  apply le_of_tendsto heuler
  filter_upwards [] with N
  simpa only [Nat.primesBelow] using hle N

end DepthAspect.EulerCoefficientSummability
