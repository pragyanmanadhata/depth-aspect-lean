import DepthAspect.Dimension
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# General Martin dimension factors and their dyadic specialization

The external theorem is Martin (2005), Theorem 1. Its arithmetic functions
are defined here from the complete prime-power tables in Definition 1′,
https://personal.math.ubc.ca/~gerg/papers/downloads/DSCFN.pdf, pp. 300–301.
Every specialization to powers of two below is proved from those definitions.
-/
namespace DepthAspect.MartinDimension
open scoped BigOperators

noncomputable def localExtension (f : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  N.factorization.prod f

theorem localExtension_prime_pow (f : ℕ → ℕ → ℝ) (hf : ∀ p, f p 0 = 1)
    (p a : ℕ) (hp : p.Prime) : localExtension f (p ^ a) = f p a := by
  unfold localExtension
  rw [hp.factorization_pow, Finsupp.prod_single_index (hf p)]

noncomputable def s0Local (p a : ℕ) : ℝ :=
  if a = 0 then 1 else if a = 1 then 1 - 1 / p else
    if a = 2 then 1 - 1 / p - 1 / (p : ℝ) ^ 2 else
      (1 - 1 / p) * (1 - 1 / (p : ℝ) ^ 2)

noncomputable def infinityLocal (p a : ℕ) : ℝ :=
  if a = 0 then 1 else if Odd a then 0 else if a = 2 then (p : ℝ) - 2 else
    (p : ℝ) ^ (a / 2 - 2) * ((p : ℝ) - 1) ^ 2

noncomputable def ellipticTwoLocal (p a : ℕ) : ℝ :=
  if a = 0 then 1 else if p = 2 then
    (if a = 1 ∨ a = 2 then -1 else if a = 3 then 1 else 0)
  else if p % 4 = 1 then (if a = 2 then -1 else 0)
  else (if a = 1 then -2 else if a = 2 then 1 else 0)

noncomputable def ellipticThreeLocal (p a : ℕ) : ℝ :=
  if a = 0 then 1 else if p = 3 then
    (if a = 1 ∨ a = 2 then -1 else if a = 3 then 1 else 0)
  else if p % 3 = 1 then (if a = 2 then -1 else 0)
  else (if a = 1 then -2 else if a = 2 then 1 else 0)

noncomputable def s0 (N : ℕ) : ℝ := localExtension s0Local N
noncomputable def nuInfinity (N : ℕ) : ℝ := localExtension infinityLocal N
noncomputable def nuTwo (N : ℕ) : ℝ := localExtension ellipticTwoLocal N
noncomputable def nuThree (N : ℕ) : ℝ := localExtension ellipticThreeLocal N

noncomputable def cTwo (k : ℕ) : ℝ := 1 / 4 + (k / 4 : ℕ) - (k : ℝ) / 4
noncomputable def cThree (k : ℕ) : ℝ := 1 / 3 + (k / 3 : ℕ) - (k : ℝ) / 3

/-- The full arithmetic expression in Martin's general theorem. -/
noncomputable def expression (k N : ℕ) : ℝ :=
  ((k : ℝ) - 1) / 12 * N * s0 N - nuInfinity N / 2 +
    cTwo k * nuTwo N + cThree k * nuThree N +
    if k = 2 then (ArithmeticFunction.moebius N : ℝ) else 0

@[simp] theorem s0_two_pow (n : ℕ) (hn : 3 ≤ n) : s0 (2 ^ n) = 3 / 8 := by
  unfold s0
  rw [localExtension_prime_pow s0Local (by intro p; simp [s0Local]) 2 n Nat.prime_two]
  norm_num [s0Local, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega]

@[simp] theorem nuTwo_two_pow (n : ℕ) (hn : 4 ≤ n) : nuTwo (2 ^ n) = 0 := by
  unfold nuTwo
  rw [localExtension_prime_pow ellipticTwoLocal (by intro p; simp [ellipticTwoLocal])
    2 n Nat.prime_two]
  simp [ellipticTwoLocal, show n ≠ 0 by omega, show n ≠ 1 by omega,
    show n ≠ 2 by omega, show n ≠ 3 by omega]

@[simp] theorem nuThree_two_pow (n : ℕ) (hn : 3 ≤ n) : nuThree (2 ^ n) = 0 := by
  unfold nuThree
  rw [localExtension_prime_pow ellipticThreeLocal (by intro p; simp [ellipticThreeLocal])
    2 n Nat.prime_two]
  norm_num [ellipticThreeLocal, show n ≠ 0 by omega, show n ≠ 1 by omega,
    show n ≠ 2 by omega]

@[simp] theorem moebius_two_pow (n : ℕ) (hn : 2 ≤ n) :
    ArithmeticFunction.moebius (2 ^ n) = 0 := by
  rw [ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by omega)]
  simp [show n ≠ 1 by omega]

@[simp] theorem nuInfinity_even (a : ℕ) (ha : 2 ≤ a) :
    nuInfinity (2 ^ (2 * a)) = (2 : ℝ) ^ (a - 2) := by
  unfold nuInfinity
  rw [localExtension_prime_pow infinityLocal (by intro p; simp [infinityLocal])
    2 (2 * a) Nat.prime_two]
  have hnot : ¬ Odd (2 * a) := Nat.not_odd_iff_even.mpr (even_two_mul a)
  simp [infinityLocal, show 2 * a ≠ 0 by omega, hnot,
    show 2 * a ≠ 2 by omega] <;> norm_num

@[simp] theorem nuInfinity_odd (a : ℕ) : nuInfinity (2 ^ (2 * a + 1)) = 0 := by
  unfold nuInfinity
  rw [localExtension_prime_pow infinityLocal (by intro p; simp [infinityLocal])
    2 (2 * a + 1) Nat.prime_two]
  have hodd : Odd (2 * a + 1) := ⟨a, by omega⟩
  simp [infinityLocal, show 2 * a + 1 ≠ 0 by omega, hodd]

/-- Lemma 2.5 at even depth, from the general formula's literal local factors. -/
theorem expression_even (k a : ℕ) (ha : 2 ≤ a) :
    expression k (2 ^ (2 * a)) = evenDimension (k : ℝ) ((2 : ℝ) ^ a) := by
  unfold expression
  rw [s0_two_pow _ (by omega), nuTwo_two_pow _ (by omega),
    nuThree_two_pow _ (by omega), nuInfinity_even a ha, moebius_two_pow _ (by omega)]
  simp only [Int.cast_zero, mul_zero, add_zero, ite_self]
  push_cast
  have hlevel : (2 : ℝ) ^ (2 * a) = ((2 : ℝ) ^ a) ^ 2 := by
    rw [mul_comm 2 a, pow_mul]
  have hhalf : (2 : ℝ) ^ (a - 2) / 2 = (2 : ℝ) ^ a / 8 := by
    have he : (2 : ℝ) ^ a = 2 ^ (a - 2) * 4 := by
      conv_lhs => rw [show a = (a - 2) + 2 by omega, pow_add]
      norm_num
    rw [he]
    ring
  rw [hlevel, hhalf]
  unfold evenDimension
  ring

/-- Lemma 2.5 at odd depth, from the general formula's literal local factors. -/
theorem expression_odd (k a : ℕ) (ha : 2 ≤ a) :
    expression k (2 ^ (2 * a + 1)) = oddDimension (k : ℝ) ((2 : ℝ) ^ a) := by
  unfold expression
  rw [s0_two_pow _ (by omega), nuTwo_two_pow _ (by omega),
    nuThree_two_pow _ (by omega), nuInfinity_odd a, moebius_two_pow _ (by omega)]
  simp only [Int.cast_zero, mul_zero, add_zero, sub_zero, zero_div, ite_self]
  push_cast
  have hlevel : (2 : ℝ) ^ (2 * a + 1) = 2 * ((2 : ℝ) ^ a) ^ 2 := by
    rw [pow_add, mul_comm 2 a, pow_mul]
    ring
  rw [hlevel]
  unfold oddDimension
  ring

/-- The external general dimension identity. No prime-power specialization
or dimension estimate is built into this predicate. -/
def SatisfiesMartinFormula (k : ℕ) (d : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 0 < N → d N = expression k N

/-- The general dimension identity yields the proved even-depth expression. -/
theorem dimension_even (k a : ℕ) (ha : 2 ≤ a) (d : ℕ → ℝ)
    (hformula : SatisfiesMartinFormula k d) :
    d (2 ^ (2 * a)) = evenDimension (k : ℝ) ((2 : ℝ) ^ a) := by
  rw [hformula _ (by positivity), expression_even k a ha]

/-- The general dimension identity yields the proved odd-depth expression. -/
theorem dimension_odd (k a : ℕ) (ha : 2 ≤ a) (d : ℕ → ℝ)
    (hformula : SatisfiesMartinFormula k d) :
    d (2 ^ (2 * a + 1)) = oddDimension (k : ℝ) ((2 : ℝ) ^ a) := by
  rw [hformula _ (by positivity), expression_odd k a ha]

/-- Uniform dimension bounds (15), derived from the general Martin identity. -/
theorem dimension_bounds (k n : ℕ) (hk : 2 ≤ k) (hn : 8 ≤ n)
    (d : ℕ → ℝ) (hformula : SatisfiesMartinFormula k d) :
    ((k : ℝ) - 1) * (2 : ℝ) ^ n / 64 ≤ d (2 ^ n) ∧
      d (2 ^ n) ≤ ((k : ℝ) - 1) * (2 : ℝ) ^ n / 32 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨a, ha⟩ := he
    have hn' : n = 2 * a := by omega
    rw [hn'] at hn ⊢
    rw [dimension_even k a (by omega) d hformula]
    have hq : (16 : ℝ) ≤ (2 : ℝ) ^ a := by
      have hh : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ a :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at hh ⊢
      exact hh
    have hb := even_dimension_bounds (k : ℝ) ((2 : ℝ) ^ a) hkR hq
    simpa only [mul_comm 2 a, pow_mul] using hb
  · obtain ⟨a, ha⟩ := ho
    have hn' : n = 2 * a + 1 := by omega
    rw [hn'] at hn ⊢
    rw [dimension_odd k a (by omega) d hformula]
    have hb := odd_dimension_bounds (k : ℝ) ((2 : ℝ) ^ a) hkR (by positivity)
    have hlevel : (2 : ℝ) ^ (2 * a + 1) = 2 * ((2 : ℝ) ^ a) ^ 2 := by
      rw [pow_add, mul_comm 2 a, pow_mul]
      ring
    rw [hlevel]
    exact ⟨hb.1, le_of_eq hb.2⟩

/-- The exact denominator premise used in the trace-bound modules, with the
weight written as polynomial degree plus two. -/
theorem polynomial_degree_dimension_lower (k n : ℕ) (hn : 8 ≤ n)
    (d : ℕ → ℝ) (hformula : SatisfiesMartinFormula (k + 2) d) :
    ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d (2 ^ n) := by
  have h := (dimension_bounds (k + 2) n (by omega) hn d hformula).1
  convert h using 1 <;> push_cast <;> ring

/-- A finite spectral family satisfying the general dimension identity is
nonempty at every depth in the paper's unsigned range. -/
theorem family_nonempty (F : ℕ → Type*) [∀ N, Fintype (F N)]
    (k n : ℕ) (hk : 2 ≤ k) (hn : 8 ≤ n)
    (hformula : SatisfiesMartinFormula k (fun N => (Fintype.card (F N) : ℝ))) :
    Nonempty (F (2 ^ n)) := by
  have hb := (dimension_bounds k n hk hn
    (fun N => (Fintype.card (F N) : ℝ)) hformula).1
  have hkR : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hc : (0 : ℝ) < (Fintype.card (F (2 ^ n)) : ℝ) :=
    lt_of_lt_of_le (by positivity) hb
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hc)

/-- The coefficient c_N in equation (15), with an arbitrary dimension function. -/
noncomputable def scalarCoefficient (k n : ℕ) (d : ℕ → ℝ) : ℝ :=
  ((k : ℝ) - 1) * (2 : ℝ) ^ n / (32 * d (2 ^ n))

theorem scalarCoefficient_bounds (k n : ℕ) (hk : 2 ≤ k) (hn : 8 ≤ n)
    (d : ℕ → ℝ) (hformula : SatisfiesMartinFormula k d) :
    1 ≤ scalarCoefficient k n d ∧ scalarCoefficient k n d ≤ 2 := by
  have hb := dimension_bounds k n hk hn d hformula
  have hkR : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hd : 0 < d (2 ^ n) := lt_of_lt_of_le (by positivity) hb.1
  unfold scalarCoefficient
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 32 * d (2 ^ n))).mpr
    linarith [hb.2]
  · apply (div_le_iff₀ (by positivity : 0 < 32 * d (2 ^ n))).mpr
    linarith [hb.1]

/-- The quantitative scalar error in (15) follows from the general Martin
formula and its proved local tables. -/
theorem scalarCoefficient_error (k n : ℕ) (hk : 2 ≤ k) (hn : 8 ≤ n)
    (d : ℕ → ℝ) (hformula : SatisfiesMartinFormula k d) :
    |scalarCoefficient k n d - 1| ≤
      8 / ((k : ℝ) - 1) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) - 1 := by linarith
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨a, ha⟩ := he
    have hn' : n = 2 * a := by omega
    rw [hn'] at hn ⊢
    have hq : (16 : ℝ) ≤ (2 : ℝ) ^ a := by
      have hh : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ a :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at hh ⊢
      exact hh
    have hlevel : (2 : ℝ) ^ (2 * a) = ((2 : ℝ) ^ a) ^ 2 := by
      rw [mul_comm 2 a, pow_mul]
    have hrpow : (((2 : ℝ) ^ a) ^ 2) ^ (-1 / 2 : ℝ) = ((2 : ℝ) ^ a)⁻¹ := by
      rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (2 : ℝ) ^ a)]
      norm_num [Real.rpow_neg_one]
    unfold scalarCoefficient
    rw [dimension_even k a (by omega) d hformula, hlevel, hrpow]
    have hb := even_scalar_coefficient_error (k : ℝ) ((2 : ℝ) ^ a) hkR hq
    convert hb using 1 <;> simp only [div_eq_mul_inv, mul_inv] <;> ring
  · obtain ⟨a, ha⟩ := ho
    have hn' : n = 2 * a + 1 := by omega
    rw [hn'] at hn ⊢
    have hlevel : (2 : ℝ) ^ (2 * a + 1) = 2 * ((2 : ℝ) ^ a) ^ 2 := by
      rw [pow_add, mul_comm 2 a, pow_mul]
      ring
    unfold scalarCoefficient
    rw [dimension_odd k a (by omega) d hformula, hlevel,
      odd_scalar_coefficient (k : ℝ) ((2 : ℝ) ^ a) hkR (by positivity)]
    simp only [sub_self, abs_zero]
    positivity

end DepthAspect.MartinDimension
