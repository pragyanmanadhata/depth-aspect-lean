import DepthAspect.LocalRoots
import Mathlib.Data.Finset.Prod

/-! Exact counting of periodic integer predicates in complete periods. -/
namespace DepthAspect.PeriodicCounting

/-- Mixed-radix representation with a prescribed positive radix is unique. -/
theorem digit_injective {q a b r s : ℤ} (hq : 0 < q)
    (hr0 : 0 ≤ r) (hrq : r < q) (hs0 : 0 ≤ s) (hsq : s < q)
    (heq : q * a + r = q * b + s) : a = b ∧ r = s := by
  have hab : a = b := by
    by_contra h
    rcases lt_or_gt_of_ne h with hab | hba
    · have : a + 1 ≤ b := by omega
      nlinarith
    · have : b + 1 ≤ a := by omega
      nlinarith
  subst b
  constructor
  · rfl
  · omega

/-- A periodic predicate has equally many solutions in each complete period. -/
theorem periodic_count (A q : ℤ) (hq : 0 < q) (p : ℤ → Prop) [DecidablePred p]
    (hper : ∀ x, p x ↔ p (x % q)) :
    ((Finset.Ico 0 (A * q)).filter p).card =
      A.toNat * ((Finset.Ico 0 q).filter p).card := by
  let s := (Finset.Ico 0 A) ×ˢ ((Finset.Ico 0 q).filter p)
  let t := (Finset.Ico 0 (A * q)).filter p
  have hcount : s.card = t.card := by
    apply Finset.card_bij (fun z _ => q * z.1 + z.2)
    · intro z hz
      obtain ⟨hzA, hzp⟩ := Finset.mem_product.mp hz
      obtain ⟨ha0, haA⟩ := Finset.mem_Ico.mp hzA
      obtain ⟨hzq, hp⟩ := Finset.mem_filter.mp hzp
      obtain ⟨hr0, hrq⟩ := Finset.mem_Ico.mp hzq
      have hmod : (q * z.1 + z.2) % q = z.2 := by
        simp [Int.add_emod, Int.emod_eq_of_lt hr0 hrq]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, (hper _).mpr ?_⟩
      · nlinarith
      · have : z.1 + 1 ≤ A := by omega
        nlinarith
      · rwa [hmod]
    · intro a ha b hb hab
      obtain ⟨_, har⟩ := Finset.mem_product.mp ha
      obtain ⟨_, hbr⟩ := Finset.mem_product.mp hb
      obtain ⟨ha0, haq⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp har).1
      obtain ⟨hb0, hbq⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hbr).1
      obtain ⟨h1, h2⟩ := digit_injective hq ha0 haq hb0 hbq hab
      exact Prod.ext h1 h2
    · intro x hx
      obtain ⟨hxI, hxp⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx0, hxA⟩ := Finset.mem_Ico.mp hxI
      refine ⟨(x / q, x % q), ?_, ?_⟩
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_Ico.mpr
          constructor
          · exact Int.ediv_nonneg hx0 hq.le
          · apply (Int.ediv_lt_iff_lt_mul hq).mpr
            nlinarith
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
            ⟨Int.emod_nonneg x (ne_of_gt hq), Int.emod_lt_of_pos x hq⟩,
            (hper x).mp hxp⟩
      · have hh := Int.emod_add_mul_ediv x q
        dsimp
        omega
  have hs : s.card = A.toNat * ((Finset.Ico 0 q).filter p).card := by
    simp [s, Int.card_Ico]
  exact hcount.symm.trans hs

/-- Square congruences are periodic in their modulus. -/
theorem square_periodic (q d x : ℤ) :
    (q ∣ x ^ 2 - d) ↔ q ∣ (x % q) ^ 2 - d := by
  have heq := (Int.mod_modEq x q).pow 2
  have heq' := heq.sub (Int.ModEq.refl d)
  exact heq'.dvd_iff.symm

/-- Exact repeated-period count for square roots. -/
theorem repeated_roots_count (A q d : ℤ) (hq : 0 < q) :
    ((Finset.Ico 0 (A * q)).filter (fun x => q ∣ x ^ 2 - d)).card =
      A.toNat * ((Finset.Ico 0 q).filter (fun x => q ∣ x ^ 2 - d)).card :=
  periodic_count A q hq _ (square_periodic q d)

end DepthAspect.PeriodicCounting
