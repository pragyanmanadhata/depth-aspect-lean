import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local arithmetic used in Sections 3 and 4

The statements below concern actual integer divisibility. They introduce no
axioms, and do not identify the paper's spectral quantities with new definitions.
The last stability lemma is explicitly a conditional algebraic implication;
it does not establish the projective root-count stabilization theorem.
-/

namespace DepthAspect.LocalArithmetic

/-- A positive integer strictly smaller than a positive modulus is not a
multiple of that modulus. -/
theorem not_dvd_of_pos_of_lt {q a : ℤ} (ha : 0 < a) (haq : a < q) : ¬ q ∣ a := by
  intro h
  have := Int.le_of_dvd ha h
  omega

/-- Lemma 4.2: below `q`, there are no surviving trace indices. Primality is
unnecessary for this implication. -/
theorem no_surviving_trace_index {q P r : ℤ} (hPq : P < q)
    (hrP : r ^ 2 < P) : ¬ q ∣ P - r ^ 2 := by
  apply not_dvd_of_pos_of_lt
  · omega
  · nlinarith [sq_nonneg r]

/-- Replacing the even trace `t = 2r` cancels the common factor four in
`4q ∣ 4P - t²`, as in (43). -/
theorem trace_congruence_iff (q P r : ℤ) :
    4 * q ∣ 4 * P - (2 * r) ^ 2 ↔ q ∣ P - r ^ 2 := by
  have heq : 4 * P - (2 * r) ^ 2 = 4 * (P - r ^ 2) := by ring
  rw [heq, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)]

/-- Divisibility by `4q` forces the trace to be even. -/
theorem trace_even_of_divisibility {q P t : ℤ}
    (h : 4 * q ∣ 4 * P - t ^ 2) : Even t := by
  rcases h with ⟨a, ha⟩
  have heven : Even (t ^ 2) := by
    refine ⟨2 * (P - q * a), ?_⟩
    nlinarith [ha]
  rcases Int.even_or_odd t with ht | ht
  · exact ht
  · exact False.elim ((Int.not_even_iff_odd.mpr ht.pow) heven)

/-- Exact reparametrization of the surviving trace condition in (43). -/
theorem surviving_trace_iff (q P t : ℤ) :
    (t ^ 2 < 4 * P ∧ 4 * q ∣ 4 * P - t ^ 2) ↔
      ∃ r : ℤ, t = 2 * r ∧ r ^ 2 < P ∧ q ∣ P - r ^ 2 := by
  constructor
  · rintro ⟨hlt, hdiv⟩
    obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp (trace_even_of_divisibility hdiv)
    refine ⟨r, hr, ?_, ?_⟩
    · rw [hr] at hlt
      nlinarith
    · rw [hr] at hdiv
      exact (trace_congruence_iff q P r).mp hdiv
  · rintro ⟨r, rfl, hlt, hdiv⟩
    constructor
    · nlinarith
    · exact (trace_congruence_iff q P r).mpr hdiv

/-- Every odd integer is coprime to two, including negative odd integers. -/
theorem two_isCoprime_odd {a : ℤ} (ha : Odd a) : IsCoprime (2 : ℤ) a := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨-b, 1, ?_⟩
  omega

/-- An odd factor can be cancelled from divisibility by an arbitrary power of two. -/
theorem pow_two_dvd_of_dvd_odd_mul {a b : ℤ} {h : ℕ} (ha : Odd a)
    (hdiv : (2 : ℤ) ^ h ∣ a * b) : (2 : ℤ) ^ h ∣ b := by
  exact ((two_isCoprime_odd ha).pow_left).dvd_of_dvd_mul_left hdiv

/-- The root congruence used in Proposition 3.4: two odd integers whose squares
agree modulo `2^(h+2)` agree up to sign modulo `2^(h+1)`.

The use of `h+2` avoids truncated natural subtraction. -/
theorem odd_square_congruence {x y : ℤ} {h : ℕ} (hx : Odd x) (hy : Odd y)
    (hdiv : (2 : ℤ) ^ (h + 2) ∣ x ^ 2 - y ^ 2) :
    (2 : ℤ) ^ (h + 1) ∣ x - y ∨ (2 : ℤ) ^ (h + 1) ∣ x + y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have hf : x ^ 2 - y ^ 2 = 4 * ((a - b) * (a + b + 1)) := by
    rw [ha, hb]
    ring
  have hp : (2 : ℤ) ^ (h + 2) = 4 * 2 ^ h := by rw [pow_add]; ring
  rw [hf, hp] at hdiv
  have hhalf : (2 : ℤ) ^ h ∣ (a - b) * (a + b + 1) :=
    (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp hdiv
  by_cases hab : Odd (a - b)
  · right
    obtain ⟨c, hc⟩ := pow_two_dvd_of_dvd_odd_mul hab hhalf
    refine ⟨c, ?_⟩
    rw [pow_succ]
    nlinarith [ha, hb, hc]
  · left
    have hab' : Odd (a + b + 1) := by
      rw [Int.odd_iff] at hab ⊢
      omega
    rw [mul_comm] at hhalf
    obtain ⟨c, hc⟩ := pow_two_dvd_of_dvd_odd_mul hab' hhalf
    refine ⟨c, ?_⟩
    rw [pow_succ]
    nlinarith [ha, hb, hc]

/-- Congruent squares modulo an even modulus preserve oddness. -/
theorem odd_of_square_congruence {x y q : ℤ} (hq : 2 ∣ q) (hy : Odd y)
    (h : q ∣ x ^ 2 - y ^ 2) : Odd x := by
  have heven : Even (x ^ 2 - y ^ 2) := even_iff_two_dvd.mpr (hq.trans h)
  have hodd : Odd (x ^ 2) := by
    have := (hy.pow (n := 2)).add_even heven
    convert this using 1
    ring
  rcases Int.even_or_odd x with hx | hx
  · exact False.elim ((Int.not_even_iff_odd.mpr hodd) (hx.pow_of_ne_zero (by decide : 2 ≠ 0)))
  · exact hx

/-- The prime-square exclusion in Proposition 3.4, in the stronger form valid
for every positive odd integer `P`. Here `q = 2^(h+2)` and `2P < q/2`.
-/
theorem no_interior_square_root {P r : ℤ} {h : ℕ} (_hP : 0 < P) (hodd : Odd P)
    (hsize : 2 * P < (2 : ℤ) ^ (h + 1)) (hleft : -P < r) (hright : r < P) :
    ¬ (2 : ℤ) ^ (h + 2) ∣ r ^ 2 - P ^ 2 := by
  intro hdiv
  have htwo : (2 : ℤ) ∣ (2 : ℤ) ^ (h + 2) := dvd_pow_self 2 (by omega)
  have hrodd := odd_of_square_congruence htwo hodd hdiv
  rcases odd_square_congruence hrodd hodd hdiv with hminus | hplus
  · have hminus' : (2 : ℤ) ^ (h + 1) ∣ P - r := by
      simpa only [neg_sub] using dvd_neg.mpr hminus
    exact not_dvd_of_pos_of_lt (by omega) (by omega) hminus'
  · exact not_dvd_of_pos_of_lt (by omega) (by omega) hplus

/-- An eventually constant sequence has zero second difference once all three
arguments lie in the stable range. This is the algebraic step in Lemma 3.1. -/
theorem second_difference_of_stable {R : ℕ → ℤ} {v n : ℕ}
    (hstable : ∀ j, v ≤ j → R (j + 1) = R j) (hvn : v ≤ n) :
    R (n + 2) - 2 * R (n + 1) + R n = 0 := by
  rw [show n + 2 = (n + 1) + 1 by omega, hstable (n + 1) (by omega), hstable n hvn]
  ring

/-- Multiplication by the content factor preserves zero second differences,
as required by (20). -/
theorem scaled_second_difference_of_stable {R : ℕ → ℤ} {v n : ℕ} (c : ℤ)
    (hstable : ∀ j, v ≤ j → R (j + 1) = R j) (hvn : v ≤ n) :
    c * R (n + 2) - 2 * (c * R (n + 1)) + c * R n = 0 := by
  have h := second_difference_of_stable hstable hvn
  calc
    _ = c * (R (n + 2) - 2 * R (n + 1) + R n) := by ring
    _ = 0 := by rw [h, mul_zero]

end DepthAspect.LocalArithmetic
