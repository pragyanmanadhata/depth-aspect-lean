import DepthAspect.PairCount
import DepthAspect.LocalArithmetic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Quantitative pair bound in Lemma 4.2

The finite set may be any set of integer pairs `(m,r)` satisfying the
surviving-index conditions. Restricting `m` to primes in a dyadic interval
only makes the set smaller. The real upper bound `B` need not be an integer.
-/
namespace DepthAspect.PrimePairBound

/-- The trace coordinate lies in the integer floor of the real square-root
radius. -/
theorem radius_bound {B : ℝ} {m r : ℤ} (hr : r ^ 2 < m) (hm : (m : ℝ) ≤ B) :
    -(⌊Real.sqrt B⌋₊ : ℤ) ≤ r ∧ r ≤ (⌊Real.sqrt B⌋₊ : ℤ) := by
  have hrsq : (r : ℝ) ^ 2 ≤ B := by
    have hr' : (r : ℝ) ^ 2 < (m : ℝ) := by exact_mod_cast hr
    exact hr'.le.trans hm
  have habs : (r.natAbs : ℝ) ≤ Real.sqrt B := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using Real.abs_le_sqrt hrsq
  have hrnat : r.natAbs ≤ ⌊Real.sqrt B⌋₊ := Nat.le_floor habs
  have hrint : (r.natAbs : ℤ) ≤ (⌊Real.sqrt B⌋₊ : ℤ) := by exact_mod_cast hrnat
  rw [Int.natCast_natAbs] at hrint
  exact abs_le.mp hrint

/-- Integer floor division is bounded above by the corresponding real quotient. -/
theorem floor_quotient_bound {B : ℝ} {q : ℤ} (hB : 0 ≤ B) (hq : 0 < q) :
    (((⌊B⌋ : ℤ) / q).toNat : ℝ) ≤ B / (q : ℝ) := by
  have hfloor : 0 ≤ (⌊B⌋ : ℤ) := Int.floor_nonneg.mpr hB
  have hz : 0 ≤ (⌊B⌋ : ℤ) / q := Int.ediv_nonneg hfloor hq.le
  have hcast : (((⌊B⌋ : ℤ) / q).toNat : ℝ) = (((⌊B⌋ : ℤ) / q : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  rw [hcast]
  apply (le_div_iff₀ (show (0 : ℝ) < q by exact_mod_cast hq)).mpr
  calc
    _ ≤ ((⌊B⌋ : ℤ) : ℝ) := by exact_mod_cast Int.ediv_mul_le (⌊B⌋ : ℤ) (ne_of_gt hq)
    _ ≤ B := Int.floor_le B

/-- Quantitative form of (44), before substituting `q=N/16`.
The bound counts all integer pairs, and so applies to prime-index subsets. -/
theorem integer_pairs_bound {B : ℝ} {q : ℤ} (hB : 1 ≤ B) (hq : 0 < q)
    (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, p.2 ^ 2 < p.1 ∧ (p.1 : ℝ) ≤ B ∧ q ∣ p.1 - p.2 ^ 2) :
    (s.card : ℝ) ≤ 3 * Real.sqrt B * B / (q : ℝ) := by
  let R : ℕ := ⌊Real.sqrt B⌋₊
  have hsubset : s ⊆ PairCount.pairs q (⌊B⌋ : ℤ) R := by
    intro p hp
    obtain ⟨hr, hm, hdiv⟩ := hs p hp
    have hm0 : 1 ≤ p.1 := by nlinarith [sq_nonneg p.2]
    have hmB : p.1 ≤ (⌊B⌋ : ℤ) := Int.le_floor.mpr hm
    have hrad := radius_bound hr hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hm0, hmB⟩, Finset.mem_Icc.mpr hrad⟩, hr, hdiv⟩
  have hcNat := PairCount.restricted_cardinal_bound R hq s hsubset
  have hc : (s.card : ℝ) ≤ (2 * (R : ℝ) + 1) * (((⌊B⌋ : ℤ) / q).toNat : ℝ) := by
    exact_mod_cast hcNat
  have hR : (R : ℝ) ≤ Real.sqrt B := Nat.floor_le (Real.sqrt_nonneg B)
  have hone : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hfactor : 2 * (R : ℝ) + 1 ≤ 3 * Real.sqrt B := by linarith
  have hquot := floor_quotient_bound (show 0 ≤ B by linarith) hq
  calc
    (s.card : ℝ) ≤ (2 * (R : ℝ) + 1) * (((⌊B⌋ : ℤ) / q).toNat : ℝ) := hc
    _ ≤ (3 * Real.sqrt B) * (B / (q : ℝ)) :=
      mul_le_mul hfactor hquot (by positivity) (by positivity)
    _ = 3 * Real.sqrt B * B / (q : ℝ) := by ring

/-- The paper's constant 48 after `q=N/16`, in square-root notation. -/
theorem integer_pairs_bound_level {B N : ℝ} {q : ℤ}
    (hB : 1 ≤ B) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, p.2 ^ 2 < p.1 ∧ (p.1 : ℝ) ≤ B ∧ q ∣ p.1 - p.2 ^ 2) :
    (s.card : ℝ) ≤ 48 * B * Real.sqrt B / N := by
  have h := integer_pairs_bound hB hq s hs
  have heq : 3 * Real.sqrt B * B / (q : ℝ) = 48 * B * Real.sqrt B / N := by
    rw [hN]
    ring
  rwa [heq] at h

/-- Exactly the `48 B^(3/2)/N` form in (44), with a real endpoint `B`. -/
theorem integer_pairs_bound_rpow {B N : ℝ} {q : ℤ}
    (hB : 1 ≤ B) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, p.2 ^ 2 < p.1 ∧ (p.1 : ℝ) ≤ B ∧ q ∣ p.1 - p.2 ^ 2) :
    (s.card : ℝ) ≤ 48 * B ^ (3 / 2 : ℝ) / N := by
  have hpow : B ^ (3 / 2 : ℝ) = B * Real.sqrt B := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (show 0 < B by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpow]
  simpa only [mul_assoc] using integer_pairs_bound_level hB hq hN s hs

/-- Summation form of the pair estimate. Each finite set `T m` consists of
surviving trace indices; `M` can be the primes in a dyadic interval. -/
theorem sum_trace_counts_bound {B : ℝ} {q : ℤ} (hB : 1 ≤ B) (hq : 0 < q)
    (M : Finset ℤ) (T : ℤ → Finset ℤ)
    (hT : ∀ m ∈ M, ∀ r ∈ T m,
      r ^ 2 < m ∧ (m : ℝ) ≤ B ∧ q ∣ m - r ^ 2) :
    ((∑ m ∈ M, (T m).card : ℕ) : ℝ) ≤ 3 * Real.sqrt B * B / (q : ℝ) := by
  let f : (Σ _ : ℤ, ℤ) → ℤ × ℤ := fun p => (p.1, p.2)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ heq
    have h1 : a = c := congrArg Prod.fst heq
    have h2 : b = d := congrArg Prod.snd heq
    subst c
    subst d
    rfl
  let s := (M.sigma T).image f
  have hs : ∀ p ∈ s, p.2 ^ 2 < p.1 ∧ (p.1 : ℝ) ≤ B ∧ q ∣ p.1 - p.2 ^ 2 := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm, hr⟩ := Finset.mem_sigma.mp hz
    exact hT z.1 hm z.2 hr
  have hc : s.card = ∑ m ∈ M, (T m).card := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf, Finset.card_sigma]
  rw [← hc]
  exact integer_pairs_bound hB hq s hs

/-- Equation (44) in its prime-sum shape, for arbitrary chosen integer-index
subfamilies and their actual surviving trace sets. -/
theorem sum_trace_counts_bound_rpow {B N : ℝ} {q : ℤ}
    (hB : 1 ≤ B) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (M : Finset ℤ) (T : ℤ → Finset ℤ)
    (hT : ∀ m ∈ M, ∀ r ∈ T m,
      r ^ 2 < m ∧ (m : ℝ) ≤ B ∧ q ∣ m - r ^ 2) :
    ((∑ m ∈ M, (T m).card : ℕ) : ℝ) ≤ 48 * B ^ (3 / 2 : ℝ) / N := by
  have h := sum_trace_counts_bound hB hq M T hT
  have hpow : B ^ (3 / 2 : ℝ) = B * Real.sqrt B := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (show 0 < B by linarith), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have heq : 3 * Real.sqrt B * B / (q : ℝ) = 48 * B ^ (3 / 2 : ℝ) / N := by
    rw [hN, hpow]
    ring
  rwa [heq] at h

/-- The same bound for the paper's original trace variable `t`. The map
`(m,t) ↦ (m,t/2)` is proved injective on the actual surviving pairs. -/
theorem original_trace_pairs_bound {B N : ℝ} {q : ℤ}
    (hB : 1 ≤ B) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (s : Finset (ℤ × ℤ))
    (hs : ∀ p ∈ s, p.2 ^ 2 < 4 * p.1 ∧ (p.1 : ℝ) ≤ B ∧
      4 * q ∣ 4 * p.1 - p.2 ^ 2) :
    (s.card : ℝ) ≤ 48 * B ^ (3 / 2 : ℝ) / N := by
  let f : ℤ × ℤ → ℤ × ℤ := fun p => (p.1, p.2 / 2)
  have hf : Set.InjOn f s := by
    intro p hp r hr heq
    change (p.1, p.2 / 2) = (r.1, r.2 / 2) at heq
    obtain ⟨hp2, _, hpd⟩ := hs p hp
    obtain ⟨hr2, _, hrd⟩ := hs r hr
    obtain ⟨a, ha, _, _⟩ := (LocalArithmetic.surviving_trace_iff q p.1 p.2).mp ⟨hp2, hpd⟩
    obtain ⟨b, hb, _, _⟩ := (LocalArithmetic.surviving_trace_iff q r.1 r.2).mp ⟨hr2, hrd⟩
    have hm := congrArg (fun z : ℤ × ℤ => z.1) heq
    have ht := congrArg (fun z : ℤ × ℤ => z.2) heq
    dsimp only at hm ht
    apply Prod.ext hm
    omega
  have himage : ∀ p ∈ s.image f,
      p.2 ^ 2 < p.1 ∧ (p.1 : ℝ) ≤ B ∧ q ∣ p.1 - p.2 ^ 2 := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hz2, hzm, hzd⟩ := hs z hz
    obtain ⟨r, hr, hrl, hrd⟩ :=
      (LocalArithmetic.surviving_trace_iff q z.1 z.2).mp ⟨hz2, hzd⟩
    have hre : z.2 / 2 = r := by omega
    simpa only [f, hre] using And.intro hrl (And.intro hzm hrd)
  have hbound := integer_pairs_bound_rpow hB hq hN (s.image f) himage
  rwa [Finset.card_image_of_injOn hf] at hbound

/-- Equation (44) directly for finite sets of the original trace indices `t`.
Taking `M` to be odd primes in `(B/2,B]` recovers the paper's sum without
assuming any prime-counting estimate. -/
theorem original_trace_sum_bound {B N : ℝ} {q : ℤ}
    (hB : 1 ≤ B) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (M : Finset ℤ) (T : ℤ → Finset ℤ)
    (hT : ∀ m ∈ M, ∀ t ∈ T m,
      t ^ 2 < 4 * m ∧ (m : ℝ) ≤ B ∧ 4 * q ∣ 4 * m - t ^ 2) :
    ((∑ m ∈ M, (T m).card : ℕ) : ℝ) ≤ 48 * B ^ (3 / 2 : ℝ) / N := by
  let f : (Σ _ : ℤ, ℤ) → ℤ × ℤ := fun p => (p.1, p.2)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ heq
    have h1 : a = c := congrArg Prod.fst heq
    have h2 : b = d := congrArg Prod.snd heq
    subst c
    subst d
    rfl
  let s := (M.sigma T).image f
  have hs : ∀ p ∈ s, p.2 ^ 2 < 4 * p.1 ∧ (p.1 : ℝ) ≤ B ∧
      4 * q ∣ 4 * p.1 - p.2 ^ 2 := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm, hr⟩ := Finset.mem_sigma.mp hz
    exact hT z.1 hm z.2 hr
  have hc : s.card = ∑ m ∈ M, (T m).card := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf, Finset.card_sigma]
  rw [← hc]
  exact original_trace_pairs_bound hB hq hN s hs

end DepthAspect.PrimePairBound
