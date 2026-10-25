import DepthAspect.SquareDivisibility
import DepthAspect.PeriodicCounting
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Root counts with an arbitrary even valuation

The count is proved by a concrete finite bijection and exact counting over
complete periods. No root count or stabilization is assumed.
-/
namespace DepthAspect.GeneralRoots
open DepthAspect.SquareDivisibility
open DepthAspect.PeriodicCounting
open DepthAspect.LocalRoots

@[simp] theorem mem_squareRoots (j : ℕ) (d x : ℤ) :
    x ∈ squareRoots j d ↔ 0 ≤ x ∧ x < (2 : ℤ) ^ j ∧ (2 : ℤ) ^ j ∣ x ^ 2 - d := by
  simp only [squareRoots, Finset.mem_filter, Finset.mem_Ico]
  tauto

/-- Even valuation removes a square factor from a root congruence. -/
theorem square_factor_root_iff (a b : ℕ) (u x : ℤ) :
    (2 : ℤ) ^ (2 * a + b) ∣ x ^ 2 - (2 : ℤ) ^ (2 * a) * u ↔
      ∃ z : ℤ, x = 2 ^ a * z ∧ (2 : ℤ) ^ b ∣ z ^ 2 - u := by
  constructor
  · intro hx
    have hlow : (2 : ℤ) ^ (2 * a) ∣ x ^ 2 := by
      have h1 := (pow_dvd_pow (2 : ℤ) (show 2 * a ≤ 2 * a + b by omega)).trans hx
      have h2 : (2 : ℤ) ^ (2 * a) ∣ (2 : ℤ) ^ (2 * a) * u := dvd_mul_right _ _
      have hh := dvd_add h1 h2
      simpa only [sub_add_cancel] using hh
    obtain ⟨z, hz⟩ := (pow_two_even_dvd_square a x).mp hlow
    refine ⟨z, hz, ?_⟩
    rw [hz] at hx
    exact (scaled_square_divisibility a b u z).mp hx
  · rintro ⟨z, rfl, hz⟩
    exact (scaled_square_divisibility a b u z).mpr hz

/-- Concrete finite bijection for the even-valuation square-root reduction. -/
theorem squareRoots_even_valuation_card (a b : ℕ) (u : ℤ) :
    (squareRoots (2 * a + b) ((2 : ℤ) ^ (2 * a) * u)).card =
      2 ^ a * (squareRoots b u).card := by
  let s := (Finset.Ico 0 ((2 : ℤ) ^ (a + b))).filter
    (fun z => (2 : ℤ) ^ b ∣ z ^ 2 - u)
  let t := squareRoots (2 * a + b) ((2 : ℤ) ^ (2 * a) * u)
  have hpos : (0 : ℤ) < 2 ^ a := by positivity
  have hp : (2 : ℤ) ^ (2 * a + b) = 2 ^ a * 2 ^ (a + b) := by
    rw [← pow_add]
    congr 1
    omega
  have hbij : s.card = t.card := by
    apply Finset.card_bij (fun z _ => (2 : ℤ) ^ a * z)
    · intro z hz
      obtain ⟨hzI, hzdiv⟩ := Finset.mem_filter.mp hz
      obtain ⟨hz0, hzb⟩ := Finset.mem_Ico.mp hzI
      apply (mem_squareRoots _ _ _).mpr
      refine ⟨mul_nonneg hpos.le hz0, ?_, ?_⟩
      · rw [hp]
        exact mul_lt_mul_of_pos_left hzb hpos
      · exact (scaled_square_divisibility a b u z).mpr hzdiv
    · intro x _ y _ hxy
      exact mul_left_cancel₀ (ne_of_gt hpos) hxy
    · intro x hx
      obtain ⟨hx0, hxq, hxdiv⟩ := (mem_squareRoots _ _ _).mp hx
      obtain ⟨z, hz, hzdiv⟩ := (square_factor_root_iff a b u x).mp hxdiv
      refine ⟨z, ?_, hz.symm⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hzdiv⟩
      · rw [hz] at hx0
        by_contra hneg
        have hzneg : z ≤ -1 := by omega
        nlinarith
      · rw [hz, hp] at hxq
        by_contra hnot
        have hzge : 2 ^ (a + b) ≤ z := by omega
        nlinarith
  have hperiod : s.card = 2 ^ a * (squareRoots b u).card := by
    dsimp [s]
    rw [pow_add, repeated_roots_count _ _ _ (by positivity)]
    simp only [squareRoots]
    norm_cast
  exact hbij.symm.trans hperiod

/-- Exact stable-range root count for a discriminant of even valuation. -/
theorem squareRoots_even_valuation_stable_card (a h : ℕ) {u : ℤ} (hu : Odd u) :
    (squareRoots (2 * a + (h + 3)) ((2 : ℤ) ^ (2 * a) * u)).card =
      2 ^ a * (if 8 ∣ u - 1 then 4 else 0) := by
  rw [squareRoots_even_valuation_card]
  have huRoots : squareRoots (h + 3) u = unitRoots h u := rfl
  rw [huRoots, unitRoots_card h hu]

/-- Stabilization above the even valuation plus three. -/
theorem squareRoots_even_valuation_stable (a h j : ℕ) {u : ℤ} (hu : Odd u) :
    (squareRoots (2 * a + (h + 3)) ((2 : ℤ) ^ (2 * a) * u)).card =
      (squareRoots (2 * a + (j + 3)) ((2 : ℤ) ^ (2 * a) * u)).card := by
  rw [squareRoots_even_valuation_stable_card a h hu,
    squareRoots_even_valuation_stable_card a j hu]

/-- An odd unit has at most four square roots at every depth, including the
small moduli two and four. -/
theorem squareRoots_odd_card_le_four (b : ℕ) {u : ℤ} (hu : Odd u) :
    (squareRoots b u).card ≤ 4 := by
  by_cases hb : b ≤ 2
  · have hc : (squareRoots b u).card ≤ 2 ^ b := by
      calc
        _ ≤ (Finset.Ico (0 : ℤ) (2 ^ b)).card := Finset.card_filter_le _ _
        _ = 2 ^ b := by rw [Int.card_Ico]; simp only [sub_zero]; norm_cast
    have hp : (2 : ℕ) ^ b ≤ 4 := by
      have : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases this with rfl | rfl | rfl <;> norm_num
    exact hc.trans hp
  · have hb' : b = (b - 3) + 3 := by omega
    rw [hb']
    exact unitRoots_card_le_four (b - 3) hu

/-- The uniform square-root bound in (22), with an integer floor exponent.
This is slightly stronger than the stated real-valued exponent. -/
theorem squareRoots_card_bound_of_odd_part (v j : ℕ) {u : ℤ} (hu : Odd u) :
    (squareRoots j ((2 : ℤ) ^ v * u)).card ≤ 4 * 2 ^ (j / 2) := by
  by_cases hj : j ≤ v
  · have hd : (2 : ℤ) ^ j ∣ (2 : ℤ) ^ v * u :=
      dvd_mul_of_dvd_left (pow_dvd_pow (2 : ℤ) hj) u
    rw [squareRoots_card_of_dvd j _ hd]
    omega
  · rcases Nat.even_or_odd v with hv | hv
    · obtain ⟨a, ha⟩ := hv
      have hv' : v = 2 * a := by omega
      have hja : a ≤ j / 2 := by omega
      have hj' : j = 2 * a + (j - 2 * a) := by omega
      rw [hv', hj', squareRoots_even_valuation_card]
      have hc := squareRoots_odd_card_le_four (j - 2 * a) hu
      have hp : (2 : ℕ) ^ a ≤ 2 ^ (j / 2) := Nat.pow_le_pow_right (by decide) hja
      have hh : 2 ^ a * (squareRoots (j - 2 * a) u).card ≤ 4 * 2 ^ (j / 2) := by
        calc
          _ ≤ 2 ^ a * 4 := Nat.mul_le_mul_left _ hc
          _ = 4 * 2 ^ a := by omega
          _ ≤ 4 * 2 ^ (j / 2) := Nat.mul_le_mul_left _ hp
      simpa only [← hj'] using hh
    · obtain ⟨a, ha⟩ := hv
      have hv' : v = 2 * a + 1 := by omega
      rw [hv', squareRoots_card_of_odd_valuation a j u hu (by omega)]
      exact Nat.zero_le _

/-- Full square-root stabilization in terms of an explicit odd part.
This is the arithmetic stabilization assertion in (22), including both
parities of the valuation. -/
theorem squareRoots_stable_of_odd_part (v j l : ℕ) {u : ℤ} (hu : Odd u)
    (hj : v + 3 ≤ j) (hl : v + 3 ≤ l) :
    (squareRoots j ((2 : ℤ) ^ v * u)).card =
      (squareRoots l ((2 : ℤ) ^ v * u)).card := by
  rcases Nat.even_or_odd v with hv | hv
  · obtain ⟨a, ha⟩ := hv
    have hv' : v = 2 * a := by omega
    have hj' : j = 2 * a + ((j - (2 * a + 3)) + 3) := by omega
    have hl' : l = 2 * a + ((l - (2 * a + 3)) + 3) := by omega
    rw [hv', hj', hl']
    exact squareRoots_even_valuation_stable a _ _ hu
  · obtain ⟨a, ha⟩ := hv
    have hv' : v = 2 * a + 1 := by omega
    rw [hv', squareRoots_card_of_odd_valuation a j u hu (by omega),
      squareRoots_card_of_odd_valuation a l u hu (by omega)]

/-- The zero second difference of actual square-root counts in the stable range. -/
theorem squareRoots_second_difference (v j : ℕ) {u : ℤ} (hu : Odd u)
    (hj : v + 3 ≤ j) :
    ((squareRoots (j + 2) ((2 : ℤ) ^ v * u)).card : ℤ) -
      2 * ((squareRoots (j + 1) ((2 : ℤ) ^ v * u)).card : ℤ) +
      ((squareRoots j ((2 : ℤ) ^ v * u)).card : ℤ) = 0 := by
  rw [squareRoots_stable_of_odd_part v (j + 2) j hu (by omega) hj,
    squareRoots_stable_of_odd_part v (j + 1) j hu (by omega) hj]
  ring

/-- Every nonzero integer has an odd part, including a negative discriminant. -/
theorem exists_odd_part {d : ℤ} (hd : d ≠ 0) :
    ∃ v : ℕ, ∃ u : ℤ, Odd u ∧ d = (2 : ℤ) ^ v * u := by
  obtain ⟨v, m, hm, heq⟩ := Nat.exists_eq_two_pow_mul_odd
    (show d.natAbs ≠ 0 by simpa using hd)
  have hh : |d| = (2 : ℤ) ^ v * (m : ℤ) := by
    have hhcast : (d.natAbs : ℤ) = (2 : ℤ) ^ v * (m : ℤ) := by exact_mod_cast heq
    simpa only [Int.natCast_natAbs] using hhcast
  have hmo : Odd (m : ℤ) := by exact_mod_cast hm
  by_cases hd0 : 0 ≤ d
  · rw [abs_of_nonneg hd0] at hh
    exact ⟨v, m, hmo, hh⟩
  · rw [abs_of_neg (lt_of_not_ge hd0)] at hh
    exact ⟨v, - (m : ℤ), hmo.neg, by nlinarith [hh]⟩

/-- Unconditional stabilization for every nonzero integer discriminant. -/
theorem squareRoots_eventually_stable {d : ℤ} (hd : d ≠ 0) :
    ∃ v : ℕ, ∀ j l : ℕ, v + 3 ≤ j → v + 3 ≤ l →
      (squareRoots j d).card = (squareRoots l d).card := by
  obtain ⟨v, u, hu, rfl⟩ := exists_odd_part hd
  exact ⟨v, fun j l hj hl => squareRoots_stable_of_odd_part v j l hu hj hl⟩

/-- Uniform root-count bound for every integer discriminant and every depth. -/
theorem squareRoots_card_bound (j : ℕ) (d : ℤ) :
    (squareRoots j d).card ≤ 4 * 2 ^ (j / 2) := by
  by_cases hd : d = 0
  · subst d
    rw [squareRoots_card_of_dvd j 0 (dvd_zero _)]
    omega
  · obtain ⟨v, u, hu, rfl⟩ := exists_odd_part hd
    exact squareRoots_card_bound_of_odd_part v j hu

end DepthAspect.GeneralRoots
