import DepthAspect.LocalArithmetic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Card

/-!
# Actual square roots of odd units modulo powers of two

`unitRoots h d` is the finite set of integer representatives of square roots
of `d` modulo `2^(h+3)`. The exponents guarantee the stable range `b ≥ 3`.
-/

namespace DepthAspect.LocalRoots
open DepthAspect.LocalArithmetic

/-- Canonical integer representatives of roots modulo `2^(h+3)`. -/
def unitRoots (h : ℕ) (d : ℤ) : Finset ℤ :=
  (Finset.Ico 0 ((2 : ℤ) ^ (h + 3))).filter (fun x => (2 : ℤ) ^ (h + 3) ∣ x ^ 2 - d)

@[simp] theorem mem_unitRoots (h : ℕ) (d x : ℤ) :
    x ∈ unitRoots h d ↔ 0 ≤ x ∧ x < (2 : ℤ) ^ (h + 3) ∧ (2 : ℤ) ^ (h + 3) ∣ x ^ 2 - d := by
  simp only [unitRoots, Finset.mem_filter, Finset.mem_Ico]
  tauto

/-- Exactly two representatives of a congruence class modulo `Q` lie in a
half-open interval of length `2Q`. -/
theorem two_representatives {Q r x : ℤ} (hQ : 0 < Q) (hr0 : 0 ≤ r) (hrQ : r < Q)
    (hx0 : 0 ≤ x) (hxQ : x < 2 * Q) (hdiv : Q ∣ x - r) : x = r ∨ x = r + Q := by
  obtain ⟨c, hc⟩ := hdiv
  have hc0 : 0 ≤ c := by
    by_contra h
    have hc' : c ≤ -1 := by omega
    nlinarith
  have hc2 : c < 2 := by
    by_contra h
    have hc' : 2 ≤ c := by omega
    nlinarith
  have : c = 0 ∨ c = 1 := by omega
  rcases this with rfl | rfl <;> simp_all <;> omega

/-- Cancellation of oddness through an even square congruence. -/
theorem root_odd {q x d : ℤ} (hq : 2 ∣ q) (hd : Odd d) (hx : q ∣ x ^ 2 - d) : Odd x := by
  have he : Even (x ^ 2 - d) := even_iff_two_dvd.mpr (hq.trans hx)
  have hxsq : Odd (x ^ 2) := by
    have := hd.add_even he
    convert this using 1
    ring
  rcases Int.even_or_odd x with hx | hx
  · exact False.elim ((Int.not_even_iff_odd.mpr hxsq) (hx.pow_of_ne_zero (by decide : 2 ≠ 0)))
  · exact hx

/-- Modulo an even `Q`, agreeing up to sign modulo `Q` suffices for squares to
agree modulo `2Q`. -/
theorem square_congruence_of_half {Q x y : ℤ} (hQ : Even Q) (h : Q ∣ x - y) :
    2 * Q ∣ x ^ 2 - y ^ 2 := by
  obtain ⟨e, he⟩ := hQ
  obtain ⟨c, hc⟩ := h
  refine ⟨c * (y + e * c), ?_⟩
  have hxy : x = y + Q * c := by omega
  rw [hxy, he]
  ring

/-- If an odd unit has a root, every other root belongs to one of four
explicit residue classes. -/
theorem root_classification {h : ℕ} {d x y : ℤ} (hd : Odd d)
    (hx : x ∈ unitRoots h d) (hy : y ∈ unitRoots h d) :
    x ∈ ({y % (2 ^ (h + 2)), y % (2 ^ (h + 2)) + 2 ^ (h + 2),
      (-y) % (2 ^ (h + 2)), (-y) % (2 ^ (h + 2)) + 2 ^ (h + 2)} : Finset ℤ) := by
  obtain ⟨hx0, hxq, hxdiv⟩ := (mem_unitRoots h d x).mp hx
  obtain ⟨_, _, hydiv⟩ := (mem_unitRoots h d y).mp hy
  have htwo : (2 : ℤ) ∣ 2 ^ (h + 3) := dvd_pow_self 2 (by omega)
  have hxo := root_odd htwo hd hxdiv
  have hyo := root_odd htwo hd hydiv
  have hdiff : (2 : ℤ) ^ (h + 3) ∣ x ^ 2 - y ^ 2 := by
    have hh := dvd_sub hxdiv hydiv
    simpa only [sub_sub_sub_cancel_right] using hh
  have hdiff' : (2 : ℤ) ^ ((h + 1) + 2) ∣ x ^ 2 - y ^ 2 := by
    simpa [Nat.add_assoc] using hdiff
  have hpm := odd_square_congruence hxo hyo hdiff'
  have hQpos : (0 : ℤ) < 2 ^ (h + 2) := by positivity
  have hxQ : x < 2 * (2 : ℤ) ^ (h + 2) := by
    have hp : (2 : ℤ) ^ (h + 3) = 2 * 2 ^ (h + 2) := by
      rw [show h + 3 = (h + 2) + 1 by omega, pow_succ]
      ring
    rwa [hp] at hxq
  rcases hpm with hminus | hplus
  · have hmod : (2 : ℤ) ^ (h + 2) ∣ x - y % (2 ^ (h + 2)) := by
      apply Int.modEq_iff_dvd.mp
      apply (Int.mod_modEq y _).trans
      exact Int.modEq_iff_dvd.mpr (by simpa [Nat.add_assoc] using hminus)
    have heq := two_representatives hQpos (Int.emod_nonneg y (ne_of_gt hQpos))
      (Int.emod_lt_of_pos y hQpos) hx0 hxQ hmod
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · have hmod : (2 : ℤ) ^ (h + 2) ∣ x - (-y) % (2 ^ (h + 2)) := by
      apply Int.modEq_iff_dvd.mp
      apply (Int.mod_modEq (-y) _).trans
      exact Int.modEq_iff_dvd.mpr (by simpa [Nat.add_assoc] using hplus)
    have heq := two_representatives hQpos (Int.emod_nonneg (-y) (ne_of_gt hQpos))
      (Int.emod_lt_of_pos (-y) hQpos) hx0 hxQ hmod
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- The cardinal bound in the odd-unit case of (22), proved for the actual
finite set of square roots. -/
theorem unitRoots_card_le_four (h : ℕ) {d : ℤ} (hd : Odd d) : (unitRoots h d).card ≤ 4 := by
  by_cases hs : (unitRoots h d).Nonempty
  · obtain ⟨y, hy⟩ := hs
    exact (Finset.card_le_card (fun _ hx => root_classification hd hx hy)).trans Finset.card_le_four
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- The elementary obstruction: every odd square is one modulo eight. -/
theorem eight_dvd_odd_square_sub_one {x : ℤ} (hx : Odd x) : 8 ∣ x ^ 2 - 1 := by
  obtain ⟨a, ha⟩ := hx
  have h : (2 : ℤ) ∣ a * (a + 1) := Int.two_dvd_mul_add_one a
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  rw [ha]
  nlinarith [hb]

/-- A necessary condition for an odd unit to have a root in the stable range. -/
theorem eight_dvd_of_root {h : ℕ} {d x : ℤ} (hd : Odd d)
    (hx : (2 : ℤ) ^ (h + 3) ∣ x ^ 2 - d) : 8 ∣ d - 1 := by
  have htwo : (2 : ℤ) ∣ 2 ^ (h + 3) := dvd_pow_self 2 (by omega)
  have h8 : (8 : ℤ) ∣ 2 ^ (h + 3) := by
    have hh := pow_dvd_pow (2 : ℤ) (show 3 ≤ h + 3 by omega)
    norm_num at hh
    exact hh
  have h1 := eight_dvd_odd_square_sub_one (root_odd htwo hd hx)
  have hh := dvd_sub h1 (h8.trans hx)
  have heq : x ^ 2 - 1 - (x ^ 2 - d) = d - 1 := by ring
  rwa [heq] at hh

/-- Constructive lifting of an odd square root: existence modulo eight implies
existence modulo every higher power of two. -/
theorem exists_odd_root (h : ℕ) {d : ℤ} (hd : 8 ∣ d - 1) :
    ∃ x : ℤ, Odd x ∧ (2 : ℤ) ^ (h + 3) ∣ x ^ 2 - d := by
  induction h with
  | zero =>
    refine ⟨1, by decide, ?_⟩
    norm_num
    simpa only [neg_sub] using dvd_neg.mpr hd
  | succ h ih =>
    obtain ⟨x, hxodd, c, hc⟩ := ih
    have hp : (2 : ℤ) ^ (h + 3) = 8 * 2 ^ h := by rw [pow_add]; ring
    have hp' : (2 : ℤ) ^ (h + 1 + 3) = 16 * 2 ^ h := by
      rw [show h + 1 + 3 = h + 4 by omega, pow_add]
      ring
    rw [hp] at hc
    rcases Int.even_or_odd c with heven | hodd
    · obtain ⟨a, ha⟩ := heven
      refine ⟨x, hxodd, a, ?_⟩
      rw [hp']
      rw [ha] at hc
      nlinarith [hc]
    · have heven : Even (c + x + 2 * (2 : ℤ) ^ h) := by
        rw [Int.even_iff]
        have hcmod := Int.odd_iff.mp hodd
        have hxmod := Int.odd_iff.mp hxodd
        omega
      obtain ⟨a, ha⟩ := heven
      refine ⟨x + 4 * 2 ^ h, hxodd.add_even ⟨2 * 2 ^ h, by ring⟩, a, ?_⟩
      rw [hp']
      have hce : c = 2 * a - x - 2 * (2 : ℤ) ^ h := by omega
      rw [hce] at hc
      nlinarith [hc]

/-- Canonical reduction of an integer root remains a root. -/
theorem canonical_root {h : ℕ} {d x : ℤ}
    (hx : (2 : ℤ) ^ (h + 3) ∣ x ^ 2 - d) :
    x % (2 ^ (h + 3)) ∈ unitRoots h d := by
  have hq : (0 : ℤ) < 2 ^ (h + 3) := by positivity
  refine (mem_unitRoots _ _ _).mpr ⟨Int.emod_nonneg _ (ne_of_gt hq),
    Int.emod_lt_of_pos _ hq, ?_⟩
  have heq := ((Int.mod_modEq x ((2 : ℤ) ^ (h + 3))).symm).pow 2
  have hdiff := Int.modEq_iff_dvd.mp heq
  have hh := dvd_add hdiff hx
  have heq : (x % 2 ^ (h + 3)) ^ 2 - x ^ 2 + (x ^ 2 - d) = (x % 2 ^ (h + 3)) ^ 2 - d := by ring
  rwa [heq] at hh

/-- The precise existence criterion for roots of an odd unit modulo `2^b`,
for every `b ≥ 3`. -/
theorem unitRoots_nonempty_iff (h : ℕ) {d : ℤ} (hd : Odd d) :
    (unitRoots h d).Nonempty ↔ 8 ∣ d - 1 := by
  constructor
  · rintro ⟨x, hx⟩
    exact eight_dvd_of_root hd ((mem_unitRoots h d x).mp hx).2.2
  · intro h8
    obtain ⟨x, _, hx⟩ := exists_odd_root h h8
    exact ⟨_, canonical_root hx⟩

/-- Both lifts of a residue class modulo half the modulus are roots whenever
one representative is a root. -/
theorem half_class_members {h : ℕ} {d y : ℤ}
    (hy : (2 : ℤ) ^ (h + 3) ∣ y ^ 2 - d) :
    y % (2 ^ (h + 2)) ∈ unitRoots h d ∧
      y % (2 ^ (h + 2)) + 2 ^ (h + 2) ∈ unitRoots h d := by
  let Q : ℤ := 2 ^ (h + 2)
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQeven : Even Q := by
    apply even_iff_two_dvd.mpr
    exact dvd_pow_self 2 (by omega)
  have hq : (2 : ℤ) ^ (h + 3) = 2 * Q := by
    dsimp [Q]
    rw [show h + 3 = (h + 2) + 1 by omega, pow_succ]
    ring
  have hdiv : Q ∣ y % Q - y := Int.modEq_iff_dvd.mp ((Int.mod_modEq y Q).symm)
  have hdiv' : Q ∣ (y % Q + Q) - y := by
    have hh := dvd_add hdiv (dvd_refl Q)
    have heq : y % Q - y + Q = y % Q + Q - y := by ring
    rwa [heq] at hh
  have hm0 : 0 ≤ y % Q := Int.emod_nonneg y (ne_of_gt hQpos)
  have hmQ : y % Q < Q := Int.emod_lt_of_pos y hQpos
  have hroot : ∀ x : ℤ, Q ∣ x - y → (2 : ℤ) ^ (h + 3) ∣ x ^ 2 - d := by
    intro x hx
    have hs := square_congruence_of_half hQeven hx
    rw [← hq] at hs
    have hh := dvd_add hs hy
    have heq : x ^ 2 - y ^ 2 + (y ^ 2 - d) = x ^ 2 - d := by ring
    rwa [heq] at hh
  constructor
  · apply (mem_unitRoots _ _ _).mpr
    refine ⟨hm0, ?_, hroot _ hdiv⟩
    rw [hq]
    omega
  · apply (mem_unitRoots _ _ _).mpr
    refine ⟨by omega, ?_, hroot _ hdiv'⟩
    rw [hq]
    omega

/-- The positive and negative half-modulus classes of an odd root are distinct. -/
theorem opposite_half_classes_ne {h : ℕ} {y : ℤ} (hy : Odd y) :
    y % (2 ^ (h + 2)) ≠ (-y) % (2 ^ (h + 2)) := by
  intro heq
  have hmod : y ≡ -y [ZMOD (2 ^ (h + 2))] := heq
  have hdiv := Int.modEq_iff_dvd.mp hmod
  have hfour : (4 : ℤ) ∣ 2 ^ (h + 2) := by
    have hh := pow_dvd_pow (2 : ℤ) (show 2 ≤ h + 2 by omega)
    norm_num at hh
    exact hh
  have h4 : (4 : ℤ) ∣ 2 * y := by
    have := dvd_neg.mpr (hfour.trans hdiv)
    have heq : -(-y - y) = 2 * y := by ring
    rwa [heq] at this
  have h2 : (2 : ℤ) ∣ y := by
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h4
  exact (Int.not_even_iff_odd.mpr hy) (even_iff_two_dvd.mpr h2)

/-- An existing root of an odd unit gives exactly four roots. -/
theorem unitRoots_card_eq_four_of_nonempty (h : ℕ) {d : ℤ} (hd : Odd d)
    (hs : (unitRoots h d).Nonempty) : (unitRoots h d).card = 4 := by
  obtain ⟨y, hy⟩ := hs
  have hydiv := ((mem_unitRoots _ _ _).mp hy).2.2
  have hyo : Odd y := root_odd (dvd_pow_self 2 (by omega)) hd hydiv
  have hm := half_class_members hydiv
  have hn := half_class_members (y := -y) (by simpa using hydiv)
  let Q : ℤ := 2 ^ (h + 2)
  let r : ℤ := y % Q
  let t : ℤ := (-y) % Q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hr0 : 0 ≤ r := Int.emod_nonneg y (ne_of_gt hQ)
  have hrQ : r < Q := Int.emod_lt_of_pos y hQ
  have ht0 : 0 ≤ t := Int.emod_nonneg (-y) (ne_of_gt hQ)
  have htQ : t < Q := Int.emod_lt_of_pos (-y) hQ
  have hrt : r ≠ t := opposite_half_classes_ne hyo
  have hset : unitRoots h d = {r, r + Q, t, t + Q} := by
    apply Finset.Subset.antisymm
    · intro x hx
      exact root_classification hd hx hy
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hm.1
      · exact hm.2
      · exact hn.1
      · exact hn.2
  rw [hset]
  have h1 : r ≠ r + Q := by omega
  have h2 : r ≠ t + Q := by omega
  have h3 : r + Q ≠ t := by omega
  have h4 : r + Q ≠ t + Q := by omega
  have h5 : t ≠ t + Q := by omega
  simp [h1, h2, h3, h4, h5, hrt]

/-- Complete odd-unit root count in the stable range. -/
theorem unitRoots_card (h : ℕ) {d : ℤ} (hd : Odd d) :
    (unitRoots h d).card = if 8 ∣ d - 1 then 4 else 0 := by
  split_ifs with h8
  · exact unitRoots_card_eq_four_of_nonempty h hd ((unitRoots_nonempty_iff h hd).mpr h8)
  · have hs : unitRoots h d = ∅ := Finset.not_nonempty_iff_eq_empty.mp
      (fun hn => h8 ((unitRoots_nonempty_iff h hd).mp hn))
    simp [hs]

/-- Actual odd-unit root counts stabilize from modulus eight onward. -/
theorem unitRoots_stable (h j : ℕ) {d : ℤ} (hd : Odd d) :
    (unitRoots h d).card = (unitRoots j d).card := by
  rw [unitRoots_card h hd, unitRoots_card j hd]

end DepthAspect.LocalRoots
