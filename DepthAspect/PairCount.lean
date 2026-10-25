import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Counting surviving integer pairs

This is the injection behind Lemma 4.2. Counting all positive integer indices
also bounds any subset consisting of primes or a dyadic interval. The radius
is an integer parameter; this file does not silently assume the subsequent
real square-root estimate.
-/

namespace DepthAspect.PairCount

open Finset

/-- Actual pairs `(m,r)` satisfying `r² < m ≤ B` and `q ∣ m-r²`, in an
integer radius `R`. -/
def pairs (q B : ℤ) (R : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc 1 B) ×ˢ (Icc (-(R : ℤ)) R)).filter
    (fun p => p.2 ^ 2 < p.1 ∧ q ∣ p.1 - p.2 ^ 2)

/-- The positive multiple of q uniquely encodes m once r is fixed. -/
def encoding (q : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.2, (p.1 - p.2 ^ 2) / q)

theorem encoding_injective (q B : ℤ) (R : ℕ) :
    Set.InjOn (encoding q) (pairs q B R) := by
  intro p hp s hs heq
  have hp' := (mem_filter.mp hp).2.2
  have hs' := (mem_filter.mp hs).2.2
  have hr : p.2 = s.2 := congrArg Prod.fst heq
  have hv : (p.1 - p.2 ^ 2) / q = (s.1 - s.2 ^ 2) / q :=
    congrArg Prod.snd heq
  have hpm := Int.ediv_mul_cancel hp'
  have hsm := Int.ediv_mul_cancel hs'
  apply Prod.ext
  · rw [hv, hr] at hpm
    linarith
  · exact hr

theorem encoding_mem {q B : ℤ} {R : ℕ} (hq : 0 < q)
    {p : ℤ × ℤ} (hp : p ∈ pairs q B R) :
    encoding q p ∈ (Icc (-(R : ℤ)) R) ×ˢ (Icc 1 (B / q)) := by
  obtain ⟨hpbox, hlt, hdiv⟩ := mem_filter.mp hp
  obtain ⟨hm, hr⟩ := mem_product.mp hpbox
  obtain ⟨hm0, hmB⟩ := mem_Icc.mp hm
  have heq := Int.ediv_mul_cancel hdiv
  apply mem_product.mpr
  refine ⟨hr, mem_Icc.mpr ⟨?_, ?_⟩⟩
  · change 1 ≤ (p.1 - p.2 ^ 2) / q
    by_contra h
    have hv : (p.1 - p.2 ^ 2) / q ≤ 0 := by omega
    have hmul := mul_nonpos_of_nonpos_of_nonneg hv hq.le
    nlinarith
  · change (p.1 - p.2 ^ 2) / q ≤ B / q
    apply (Int.le_ediv_iff_mul_le hq).2
    rw [heq]
    nlinarith [sq_nonneg p.2]

/-- Exact integer bound with floor division; no primality assumptions. -/
theorem cardinal_bound {q B : ℤ} (R : ℕ) (hq : 0 < q) :
    (pairs q B R).card ≤ (2 * R + 1) * (B / q).toNat := by
  have h := Finset.card_le_card_of_injOn (encoding q)
    (fun _ hp => encoding_mem hq hp) (encoding_injective q B R)
  have hcard : ((Icc (-(R : ℤ)) (R : ℤ)) ×ˢ (Icc 1 (B / q))).card =
      (2 * R + 1) * (B / q).toNat := by
    rw [card_product, Int.card_Icc, Int.card_Icc]
    congr 1
    · omega
    · congr 1; omega
  exact h.trans_eq hcard

/-- The same bound holds after restricting m to any chosen finite subset,
in particular to primes in a dyadic interval. -/
theorem restricted_cardinal_bound {q B : ℤ} (R : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ pairs q B R) :
    S.card ≤ (2 * R + 1) * (B / q).toNat :=
  (Finset.card_le_card hS).trans (cardinal_bound R hq)

end DepthAspect.PairCount
