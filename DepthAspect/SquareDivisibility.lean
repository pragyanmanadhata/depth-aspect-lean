import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Divisibility of squares and exact zero-root counts at powers of two

These theorems concern actual integers and finite sets of canonical residues.
They supply the zero-discriminant residue counts used in Section 3.
-/

namespace DepthAspect.SquareDivisibility

/-- A square is even exactly when its root is even. -/
theorem two_dvd_square_iff (x : ℤ) : (2 : ℤ) ∣ x ^ 2 ↔ (2 : ℤ) ∣ x := by
  constructor
  · intro h
    rcases Int.even_or_odd x with hx | hx
    · exact even_iff_two_dvd.mp hx
    · exact False.elim ((Int.not_even_iff_odd.mpr hx.pow) (even_iff_two_dvd.mpr h))
  · intro h
    exact h.trans (dvd_pow_self x (by decide : 2 ≠ 0))

/-- Exact square divisibility at an even exponent. -/
theorem pow_two_even_dvd_square (a : ℕ) (x : ℤ) :
    (2 : ℤ) ^ (2 * a) ∣ x ^ 2 ↔ (2 : ℤ) ^ a ∣ x := by
  rw [Nat.mul_comm 2 a, pow_mul]
  exact Int.pow_dvd_pow_iff (by decide : 2 ≠ 0)

/-- Exact square divisibility at an odd exponent. -/
theorem pow_two_odd_dvd_square (a : ℕ) (x : ℤ) :
    (2 : ℤ) ^ (2 * a + 1) ∣ x ^ 2 ↔ (2 : ℤ) ^ (a + 1) ∣ x := by
  constructor
  · intro h
    have hlow : (2 : ℤ) ^ (2 * a) ∣ x ^ 2 :=
      (pow_dvd_pow (2 : ℤ) (by omega : 2 * a ≤ 2 * a + 1)).trans h
    obtain ⟨y, rfl⟩ := (pow_two_even_dvd_square a x).mp hlow
    have heq : (2 : ℤ) ^ (2 * a + 1) = ((2 : ℤ) ^ a) ^ 2 * 2 := by
      rw [pow_succ, Nat.mul_comm 2 a, pow_mul]
    rw [heq, mul_pow, mul_dvd_mul_iff_left (by positivity : ((2 : ℤ) ^ a) ^ 2 ≠ 0)] at h
    obtain ⟨z, hz⟩ := (two_dvd_square_iff y).mp h
    refine ⟨z, ?_⟩
    rw [hz, pow_succ]
    ring
  · intro h
    have hsq := (pow_two_even_dvd_square (a + 1) x).mpr h
    exact (pow_dvd_pow (2 : ℤ) (by omega : 2 * a + 1 ≤ 2 * (a + 1))).trans hsq

/-- Uniform form: the root must be divisible by the ceiling of half the exponent. -/
theorem pow_two_dvd_square (j : ℕ) (x : ℤ) :
    (2 : ℤ) ^ j ∣ x ^ 2 ↔ (2 : ℤ) ^ ((j + 1) / 2) ∣ x := by
  rcases Nat.even_or_odd j with hj | hj
  · obtain ⟨a, ha⟩ := hj
    have hja : j = 2 * a := by omega
    rw [hja, pow_two_even_dvd_square, show (2 * a + 1) / 2 = a by omega]
  · obtain ⟨a, ha⟩ := hj
    have hja : j = 2 * a + 1 := by omega
    rw [hja, pow_two_odd_dvd_square, show (2 * a + 1 + 1) / 2 = a + 1 by omega]

/-- Multiples of a positive integer in a half-open interval have the expected
number of representatives. This is a concrete finite-set count, including zero. -/
theorem card_multiples_Ico (r m : ℤ) (hr : 0 < r) :
    ((Finset.Ico 0 (r * m)).filter (fun x => r ∣ x)).card = m.toNat := by
  have heq : (Finset.Ico 0 (r * m)).filter (fun x => r ∣ x) =
      (Finset.Ico 0 m).image (fun y => r * y) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx0, hxm⟩, ⟨y, rfl⟩⟩
      refine ⟨y, ⟨?_, ?_⟩, rfl⟩
      · exact (mul_nonneg_iff_of_pos_left hr).mp hx0
      · by_contra h
        have hmy : m ≤ y := by omega
        have hmul : r * m ≤ r * y := mul_le_mul_of_nonneg_left hmy hr.le
        omega
    · rintro ⟨y, ⟨hy0, hym⟩, rfl⟩
      exact ⟨⟨mul_nonneg hr.le hy0, mul_lt_mul_of_pos_left hym hr⟩, dvd_mul_right r y⟩
  rw [heq, Finset.card_image_of_injective _ (mul_right_injective₀ (ne_of_gt hr)), Int.card_Ico]
  simp

/-- Canonical residues whose squares vanish modulo `2^j`. -/
def zeroRoots (j : ℕ) : Finset ℤ :=
  (Finset.Ico 0 ((2 : ℤ) ^ j)).filter (fun x => (2 : ℤ) ^ j ∣ x ^ 2)

@[simp] theorem mem_zeroRoots (j : ℕ) (x : ℤ) :
    x ∈ zeroRoots j ↔ 0 ≤ x ∧ x < (2 : ℤ) ^ j ∧ (2 : ℤ) ^ ((j + 1) / 2) ∣ x := by
  simp only [zeroRoots, Finset.mem_filter, Finset.mem_Ico, pow_two_dvd_square]
  tauto

/-- At an even exponent, there are exactly `2^a` zero roots. -/
theorem zeroRoots_even_card (a : ℕ) : (zeroRoots (2 * a)).card = 2 ^ a := by
  have heq : (2 : ℤ) ^ (2 * a) = (2 : ℤ) ^ a * (2 : ℤ) ^ a := by
    rw [show 2 * a = a + a by omega, pow_add]
  unfold zeroRoots
  simp only [pow_two_even_dvd_square]
  rw [heq, card_multiples_Ico _ _ (by positivity)]
  norm_cast

/-- At an odd exponent, there are again exactly `2^a` zero roots. -/
theorem zeroRoots_odd_card (a : ℕ) : (zeroRoots (2 * a + 1)).card = 2 ^ a := by
  have heq : (2 : ℤ) ^ (2 * a + 1) = (2 : ℤ) ^ (a + 1) * (2 : ℤ) ^ a := by
    rw [show 2 * a + 1 = (a + 1) + a by omega, pow_add]
  unfold zeroRoots
  simp only [pow_two_odd_dvd_square]
  rw [heq, card_multiples_Ico _ _ (by positivity)]
  norm_cast

/-- The exact count `2^⌊j/2⌋` stated before (22), proved for actual residues. -/
theorem zeroRoots_card (j : ℕ) : (zeroRoots j).card = 2 ^ (j / 2) := by
  rcases Nat.even_or_odd j with hj | hj
  · obtain ⟨a, ha⟩ := hj
    have hja : j = 2 * a := by omega
    rw [hja, zeroRoots_even_card]
    congr 1
    omega
  · obtain ⟨a, ha⟩ := hj
    have hja : j = 2 * a + 1 := by omega
    rw [hja, zeroRoots_odd_card]
    congr 1
    omega

/-- All canonical square roots of an arbitrary integer modulo `2^j`. -/
def squareRoots (j : ℕ) (d : ℤ) : Finset ℤ :=
  (Finset.Ico 0 ((2 : ℤ) ^ j)).filter (fun x => (2 : ℤ) ^ j ∣ x ^ 2 - d)

/-- When the discriminant vanishes modulo the modulus, its root set is the zero-root set. -/
theorem squareRoots_eq_zeroRoots (j : ℕ) (d : ℤ) (hd : (2 : ℤ) ^ j ∣ d) :
    squareRoots j d = zeroRoots j := by
  ext x
  simp only [squareRoots, zeroRoots, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hinterval, hx⟩
    refine ⟨hinterval, ?_⟩
    have h := dvd_add hx hd
    simpa using h
  · rintro ⟨hinterval, hx⟩
    exact ⟨hinterval, dvd_sub hx hd⟩

/-- The first regime of the square-root formula in Section 3. -/
theorem squareRoots_card_of_dvd (j : ℕ) (d : ℤ) (hd : (2 : ℤ) ^ j ∣ d) :
    (squareRoots j d).card = 2 ^ (j / 2) := by
  rw [squareRoots_eq_zeroRoots j d hd, zeroRoots_card]

/-- A congruence to an integer divisible by `2^(2a)` forces the root to be
itself divisible by `2^a`. -/
theorem root_divisible_of_scaled_congruence (a j : ℕ) (d x : ℤ)
    (haj : 2 * a ≤ j) (h : (2 : ℤ) ^ j ∣ x ^ 2 - (2 : ℤ) ^ (2 * a) * d) :
    (2 : ℤ) ^ a ∣ x := by
  apply (pow_two_even_dvd_square a x).mp
  have hlow := (pow_dvd_pow (2 : ℤ) haj).trans h
  have hsum := dvd_add hlow (dvd_mul_right ((2 : ℤ) ^ (2 * a)) d)
  simpa using hsum

/-- Removing an even power of two from both the square and discriminant
reduces the modulus by the same even power. -/
theorem scaled_square_divisibility (a b : ℕ) (d z : ℤ) :
    (2 : ℤ) ^ (2 * a + b) ∣ ((2 : ℤ) ^ a * z) ^ 2 - (2 : ℤ) ^ (2 * a) * d ↔
      (2 : ℤ) ^ b ∣ z ^ 2 - d := by
  have hs : ((2 : ℤ) ^ a * z) ^ 2 - (2 : ℤ) ^ (2 * a) * d =
      (2 : ℤ) ^ (2 * a) * (z ^ 2 - d) := by
    rw [Nat.mul_comm 2 a, pow_mul]
    ring
  rw [hs, pow_add, mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ (2 * a) ≠ 0)]

/-- There are no roots above a discriminant of odd 2-adic valuation. -/
theorem no_root_of_odd_valuation (a j : ℕ) (u x : ℤ) (hu : Odd u)
    (haj : 2 * a + 2 ≤ j) :
    ¬ (2 : ℤ) ^ j ∣ x ^ 2 - (2 : ℤ) ^ (2 * a + 1) * u := by
  intro h
  have hlow := (pow_dvd_pow (2 : ℤ) (show 2 * a + 1 ≤ j by omega)).trans h
  have hsq : (2 : ℤ) ^ (2 * a + 1) ∣ x ^ 2 := by
    simpa using dvd_add hlow (dvd_mul_right ((2 : ℤ) ^ (2 * a + 1)) u)
  have hx := (pow_two_odd_dvd_square a x).mp hsq
  have hsq' := (pow_two_even_dvd_square (a + 1) x).mpr hx
  have hhigh := (pow_dvd_pow (2 : ℤ) haj).trans h
  have hd : (2 : ℤ) ^ (2 * a + 2) ∣ (2 : ℤ) ^ (2 * a + 1) * u := by
    have hsq'' : (2 : ℤ) ^ (2 * a + 2) ∣ x ^ 2 := by
      simpa [show 2 * (a + 1) = 2 * a + 2 by omega] using hsq'
    simpa using dvd_sub hsq'' hhigh
  have hp : (2 : ℤ) ^ (2 * a + 2) = (2 : ℤ) ^ (2 * a + 1) * 2 := by
    rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega, pow_succ]
  rw [hp, mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ (2 * a + 1) ≠ 0)] at hd
  exact (Int.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr hd)

/-- Cardinality form of the odd-valuation obstruction. -/
theorem squareRoots_card_of_odd_valuation (a j : ℕ) (u : ℤ) (hu : Odd u)
    (haj : 2 * a + 2 ≤ j) :
    (squareRoots j ((2 : ℤ) ^ (2 * a + 1) * u)).card = 0 := by
  have he : squareRoots j ((2 : ℤ) ^ (2 * a + 1) * u) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact no_root_of_odd_valuation a j u x hu haj (Finset.mem_filter.mp hx).2
  rw [he]
  rfl

end DepthAspect.SquareDivisibility
