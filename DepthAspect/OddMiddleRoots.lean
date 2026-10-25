import DepthAspect.LocalRoots
import Mathlib.Data.Finset.Card

/-!
# Simple lifting for a quadratic with odd middle coefficient

The finite sets here are actual integer representatives in `[0,2^j)`.
An odd middle coefficient makes the derivative odd at every residue; each
root has exactly one of its two possible lifts at the next dyadic level.
-/

namespace DepthAspect.OddMiddleRoots

/-- The affine-chart quadratic. -/
def quadratic (A B C x : ℤ) : ℤ := A * x ^ 2 + B * x + C

/-- Actual canonical roots at an arbitrary integer modulus. -/
def rootsMod (q A B C : ℤ) : Finset ℤ :=
  (Finset.Ico 0 q).filter (fun x => q ∣ quadratic A B C x)

@[simp] theorem mem_rootsMod (q A B C x : ℤ) :
    x ∈ rootsMod q A B C ↔ 0 ≤ x ∧ x < q ∧ q ∣ quadratic A B C x := by
  simp only [rootsMod, Finset.mem_filter, Finset.mem_Ico]
  tauto

/-- Expanding a shift by the modulus isolates the derivative term. -/
theorem quadratic_shift (q A B C x : ℤ) :
    quadratic A B C (x + q) = quadratic A B C x + q * (2 * A * x + B + A * q) := by
  unfold quadratic
  ring

/-- The shift multiplier is odd when the modulus is even and `B` is odd. -/
theorem shift_multiplier_odd (q A B x : ℤ) (hq : Even q) (hB : Odd B) :
    Odd (2 * A * x + B + A * q) := by
  have h1 : Even (2 * A * x) := ⟨A * x, by ring⟩
  have h2 : Even (A * q) := hq.mul_left A
  exact (h1.add_odd hB).add_even h2

/-- Of the two possible lifts, at least one is a root. -/
theorem lift_exists (q A B C x : ℤ) (hq : Even q) (hB : Odd B)
    (hx : q ∣ quadratic A B C x) :
    2 * q ∣ quadratic A B C x ∨ 2 * q ∣ quadratic A B C (x + q) := by
  obtain ⟨c, hc⟩ := hx
  have hodd := shift_multiplier_odd q A B x hq hB
  rcases Int.even_or_odd c with he | ho
  · obtain ⟨v, hv⟩ := he
    left
    refine ⟨v, ?_⟩
    rw [hc, hv]
    ring
  · have he := ho.add_odd hodd
    obtain ⟨v, hv⟩ := he
    right
    refine ⟨v, ?_⟩
    rw [quadratic_shift, hc]
    calc
      q * c + q * (2 * A * x + B + A * q) =
          q * (c + (2 * A * x + B + A * q)) := by ring
      _ = _ := by rw [hv]; ring

/-- The two possible lifts cannot both be roots. -/
theorem lifts_not_both (q A B C x : ℤ) (hq0 : q ≠ 0) (hq : Even q) (hB : Odd B) :
    ¬ (2 * q ∣ quadratic A B C x ∧ 2 * q ∣ quadratic A B C (x + q)) := by
  rintro ⟨h0, h1⟩
  have hdiff := dvd_sub h1 h0
  rw [quadratic_shift, add_sub_cancel_left] at hdiff
  have hdiv : (2 : ℤ) ∣ 2 * A * x + B + A * q := by
    rw [mul_comm 2 q, mul_dvd_mul_iff_left hq0] at hdiff
    exact hdiff
  exact (Int.not_even_iff_odd.mpr (shift_multiplier_odd q A B x hq hB))
    (even_iff_two_dvd.mpr hdiv)

/-- An exact uniqueness formulation of the simple Hensel step. -/
theorem unique_lift (q A B C x : ℤ) (hq0 : 0 < q) (hq : Even q) (hB : Odd B)
    (hx : q ∣ quadratic A B C x) :
    ∃! y : ℤ, (y = x ∨ y = x + q) ∧ 2 * q ∣ quadratic A B C y := by
  have hn := lifts_not_both q A B C x (ne_of_gt hq0) hq hB
  rcases lift_exists q A B C x hq hB hx with h0 | h1
  · refine ⟨x, ⟨Or.inl rfl, h0⟩, ?_⟩
    rintro y ⟨hy | hy, hd⟩
    · exact hy
    · subst y
      exact False.elim (hn ⟨h0, hd⟩)
  · refine ⟨x + q, ⟨Or.inr rfl, h1⟩, ?_⟩
    rintro y ⟨hy | hy, hd⟩
    · subst y
      exact False.elim (hn ⟨hd, h1⟩)
    · exact hy

/-- Quadratic congruences are periodic in the modulus. -/
theorem quadratic_periodic (q A B C x : ℤ) :
    (q ∣ quadratic A B C x) ↔ q ∣ quadratic A B C (x % q) := by
  have h := Int.mod_modEq x q
  have heq := (((h.pow 2).mul_left A).add (h.mul_left B)).add_right C
  exact heq.dvd_iff.symm

/-- At an even positive modulus, reduction gives a bijection between roots
at the doubled modulus and roots at the original modulus. -/
theorem rootsMod_double_card (q A B C : ℤ) (hq0 : 0 < q) (hq : Even q) (hB : Odd B) :
    (rootsMod (2 * q) A B C).card = (rootsMod q A B C).card := by
  apply Finset.card_bij (fun x _ => x % q)
  · intro x hx
    obtain ⟨_, _, hd⟩ := (mem_rootsMod _ _ _ _ _).mp hx
    apply (mem_rootsMod _ _ _ _ _).mpr
    refine ⟨Int.emod_nonneg x (ne_of_gt hq0), Int.emod_lt_of_pos x hq0, ?_⟩
    exact (quadratic_periodic q A B C x).mp ((dvd_mul_left q 2).trans hd)
  · intro x hx y hy hmod
    obtain ⟨hx0, hxq, hxd⟩ := (mem_rootsMod _ _ _ _ _).mp hx
    obtain ⟨hy0, hyq, hyd⟩ := (mem_rootsMod _ _ _ _ _).mp hy
    have hr0 : 0 ≤ x % q := Int.emod_nonneg x (ne_of_gt hq0)
    have hrq : x % q < q := Int.emod_lt_of_pos x hq0
    have hxrep := LocalRoots.two_representatives hq0 hr0 hrq hx0 hxq
      (Int.modEq_iff_dvd.mp (Int.mod_modEq x q))
    have hydiv : q ∣ y - x % q := by
      rw [hmod]
      exact Int.modEq_iff_dvd.mp (Int.mod_modEq y q)
    have hyrep := LocalRoots.two_representatives hq0 hr0 hrq hy0 hyq hydiv
    have hn := lifts_not_both q A B C (x % q) (ne_of_gt hq0) hq hB
    rcases hxrep with hxr | hxr <;> rcases hyrep with hyr | hyr
    · omega
    · exact False.elim (hn ⟨by rw [← hxr]; exact hxd, by rw [← hyr]; exact hyd⟩)
    · exact False.elim (hn ⟨by rw [← hyr]; exact hyd, by rw [← hxr]; exact hxd⟩)
    · omega
  · intro r hr
    obtain ⟨hr0, hrq, hrd⟩ := (mem_rootsMod _ _ _ _ _).mp hr
    rcases lift_exists q A B C r hq hB hrd with h0 | h1
    · refine ⟨r, (mem_rootsMod _ _ _ _ _).mpr ⟨hr0, by omega, h0⟩, ?_⟩
      exact Int.emod_eq_of_lt hr0 hrq
    · refine ⟨r + q, (mem_rootsMod _ _ _ _ _).mpr ⟨by omega, by omega, h1⟩, ?_⟩
      simp [Int.emod_eq_of_lt hr0 hrq]

/-- The actual dyadic root set. The parameter is the exponent itself. -/
def roots (j : ℕ) (A B C : ℤ) : Finset ℤ := rootsMod ((2 : ℤ) ^ j) A B C

/-- Cardinality is unchanged by every lift above modulus two. -/
theorem roots_succ_card (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    (roots (j + 1) A B C).card = (roots j A B C).card := by
  unfold roots
  have hq : Even ((2 : ℤ) ^ j) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  rw [pow_succ, mul_comm ((2 : ℤ) ^ j) 2]
  exact rootsMod_double_card _ A B C (by positivity) hq hB

/-- All positive dyadic levels have the same affine root count. -/
theorem roots_card_eq_level_one (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    (roots j A B C).card = (roots 1 A B C).card := by
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [roots_succ_card (a + 1) A B C (by omega) hB]
    exact ih (by omega)

/-- Equality of actual affine root counts at any two positive levels. -/
theorem roots_stable (j l : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hl : 1 ≤ l) (hB : Odd B) :
    (roots j A B C).card = (roots l A B C).card := by
  rw [roots_card_eq_level_one j A B C hj hB, roots_card_eq_level_one l A B C hl hB]

/-- There are at most two affine roots, since the count equals the count modulo two. -/
theorem roots_card_le_two (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    (roots j A B C).card ≤ 2 := by
  rw [roots_card_eq_level_one j A B C hj hB]
  have h := Finset.card_filter_le (Finset.Ico (0 : ℤ) 2) (fun x => 2 ∣ quadratic A B C x)
  simpa [roots, rootsMod, Int.card_Ico] using h

/-- Reducing modulo an even modulus preserves parity. -/
theorem even_periodic (q x : ℤ) (hq : Even q) : Even x ↔ Even (x % q) := by
  have hm := (Int.mod_modEq x q).of_dvd (even_iff_two_dvd.mp hq)
  change (x % q) % 2 = x % 2 at hm
  rw [Int.even_iff, Int.even_iff, hm]

/-- The even-coordinate portion of the second projective chart. -/
def evenRootsMod (q A B C : ℤ) : Finset ℤ := (rootsMod q A B C).filter Even

@[simp] theorem mem_evenRootsMod (q A B C x : ℤ) :
    x ∈ evenRootsMod q A B C ↔
      0 ≤ x ∧ x < q ∧ q ∣ quadratic A B C x ∧ Even x := by
  simp only [evenRootsMod, Finset.mem_filter, mem_rootsMod]
  tauto

/-- The root-reduction bijection also preserves the even-coordinate subchart. -/
theorem evenRootsMod_double_card (q A B C : ℤ)
    (hq0 : 0 < q) (hq : Even q) (hB : Odd B) :
    (evenRootsMod (2 * q) A B C).card = (evenRootsMod q A B C).card := by
  apply Finset.card_bij (fun x _ => x % q)
  · intro x hx
    obtain ⟨_, _, hd, he⟩ := (mem_evenRootsMod _ _ _ _ _).mp hx
    apply (mem_evenRootsMod _ _ _ _ _).mpr
    refine ⟨Int.emod_nonneg x (ne_of_gt hq0), Int.emod_lt_of_pos x hq0, ?_, ?_⟩
    · exact (quadratic_periodic q A B C x).mp ((dvd_mul_left q 2).trans hd)
    · exact (even_periodic q x hq).mp he
  · intro x hx y hy hmod
    obtain ⟨hx0, hxq, hxd, _⟩ := (mem_evenRootsMod _ _ _ _ _).mp hx
    obtain ⟨hy0, hyq, hyd, _⟩ := (mem_evenRootsMod _ _ _ _ _).mp hy
    have hr0 : 0 ≤ x % q := Int.emod_nonneg x (ne_of_gt hq0)
    have hrq : x % q < q := Int.emod_lt_of_pos x hq0
    have hxrep := LocalRoots.two_representatives hq0 hr0 hrq hx0 hxq
      (Int.modEq_iff_dvd.mp (Int.mod_modEq x q))
    have hydiv : q ∣ y - x % q := by
      rw [hmod]
      exact Int.modEq_iff_dvd.mp (Int.mod_modEq y q)
    have hyrep := LocalRoots.two_representatives hq0 hr0 hrq hy0 hyq hydiv
    have hn := lifts_not_both q A B C (x % q) (ne_of_gt hq0) hq hB
    rcases hxrep with hxr | hxr <;> rcases hyrep with hyr | hyr
    · omega
    · exact False.elim (hn ⟨by rw [← hxr]; exact hxd, by rw [← hyr]; exact hyd⟩)
    · exact False.elim (hn ⟨by rw [← hyr]; exact hyd, by rw [← hxr]; exact hxd⟩)
    · omega
  · intro r hr
    obtain ⟨hr0, hrq, hrd, hre⟩ := (mem_evenRootsMod _ _ _ _ _).mp hr
    rcases lift_exists q A B C r hq hB hrd with h0 | h1
    · refine ⟨r, (mem_evenRootsMod _ _ _ _ _).mpr ⟨hr0, by omega, h0, hre⟩, ?_⟩
      exact Int.emod_eq_of_lt hr0 hrq
    · refine ⟨r + q, (mem_evenRootsMod _ _ _ _ _).mpr
        ⟨by omega, by omega, h1, hre.add hq⟩, ?_⟩
      simp [Int.emod_eq_of_lt hr0 hrq]

/-- Actual even canonical roots at dyadic level `j`. -/
def evenRoots (j : ℕ) (A B C : ℤ) : Finset ℤ := evenRootsMod ((2 : ℤ) ^ j) A B C

/-- The even-coordinate root count is unchanged at each positive level. -/
theorem evenRoots_succ_card (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    (evenRoots (j + 1) A B C).card = (evenRoots j A B C).card := by
  unfold evenRoots
  have hq : Even ((2 : ℤ) ^ j) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
  rw [pow_succ, mul_comm ((2 : ℤ) ^ j) 2]
  exact evenRootsMod_double_card _ A B C (by positivity) hq hB

/-- The even-coordinate count equals its count modulo two. -/
theorem evenRoots_card_eq_level_one (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    (evenRoots j A B C).card = (evenRoots 1 A B C).card := by
  obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [evenRoots_succ_card (a + 1) A B C (by omega) hB]
    exact ih (by omega)

/-- Stability of the even-coordinate subchart, used for the projective count. -/
theorem evenRoots_stable (j l : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hl : 1 ≤ l) (hB : Odd B) :
    (evenRoots j A B C).card = (evenRoots l A B C).card := by
  rw [evenRoots_card_eq_level_one j A B C hj hB,
    evenRoots_card_eq_level_one l A B C hl hB]

/-- At most one root belongs to the even-coordinate subchart. -/
theorem evenRoots_card_le_one (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    (evenRoots j A B C).card ≤ 1 := by
  rw [evenRoots_card_eq_level_one j A B C hj hB]
  have hsubset : evenRoots 1 A B C ⊆ ({0} : Finset ℤ) := by
    intro x hx
    have hx' := (mem_evenRootsMod 2 A B C x).mp (by simpa [evenRoots] using hx)
    obtain ⟨hx0, hx2, _, he⟩ := hx'
    rw [Int.even_iff] at he
    have hxzero : x = 0 := by omega
    simp [hxzero]
  simpa using Finset.card_le_card hsubset

/-- The two disjoint projective charts together have at most three roots
when the middle coefficient is odd. -/
theorem projective_chart_bound (j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) (hB : Odd B) :
    (roots j A B C).card + (evenRoots j C B A).card ≤ 3 := by
  have h1 := roots_card_le_two j A B C hj hB
  have h2 := evenRoots_card_le_one j C B A hj hB
  omega

end DepthAspect.OddMiddleRoots
