import DepthAspect.SurvivingTraces
import DepthAspect.PrimeSumBounds
import DepthAspect.FixedLines
import DepthAspect.TracePolynomial

/-!
# The absolute majorant and the two-root observation in Section 7

The root counts below use the canonical complete finite trace sets. The bound
for (136) is derived from the proved finite dyadic estimate, with its pointwise
trace estimate kept explicit so that it can be instantiated by `TraceBounds`.
-/
namespace DepthAspect.SectionSevenSupport

open SurvivingTraces
open scoped BigOperators

theorem odd_of_surviving {q m r : ℤ} (hq : 2 ∣ q) (hm : Odd m)
    (hr : r ∈ halvedTraces q m) : Odd r := by
  have he : Even (m - r ^ 2) :=
    even_iff_two_dvd.mpr (hq.trans ((mem_halvedTraces q m r).mp hr).2)
  have hs : Odd (r ^ 2) := by
    have hh := hm.sub_even he
    have hid : m - (m - r ^ 2) = r ^ 2 := by ring
    rwa [hid] at hh
  exact (Int.odd_pow' (by decide : (2 : ℕ) ≠ 0)).mp hs

/-- In an interval of radius `q/4`, two odd roots of the same square
congruence modulo `q=2^(h+2)` agree up to sign. -/
theorem two_roots_eq_or_neg (h : ℕ) {m r s : ℤ} (hm : Odd m)
    (hr : r ∈ halvedTraces ((2 : ℤ) ^ (h + 2)) m)
    (hs : s ∈ halvedTraces ((2 : ℤ) ^ (h + 2)) m)
    (hradius : |r| < (2 : ℤ) ^ h) (hsradius : |s| < (2 : ℤ) ^ h) :
    r = s ∨ r = -s := by
  have htwo : (2 : ℤ) ∣ (2 : ℤ) ^ (h + 2) := dvd_pow_self 2 (by omega)
  have hoddR := odd_of_surviving htwo hm hr
  have hoddS := odd_of_surviving htwo hm hs
  have hdiff : (2 : ℤ) ^ (h + 2) ∣ r ^ 2 - s ^ 2 := by
    have hh := ((mem_halvedTraces _ _ _).mp hs).2.sub
      ((mem_halvedTraces _ _ _).mp hr).2
    have hid : (m - s ^ 2) - (m - r ^ 2) = r ^ 2 - s ^ 2 := by ring
    rwa [hid] at hh
  have hhalf : (2 : ℤ) ^ (h + 1) = 2 * (2 : ℤ) ^ h := by rw [pow_succ]; ring
  have hrbounds := abs_lt.mp hradius
  have hsbounds := abs_lt.mp hsradius
  rcases LocalArithmetic.odd_square_congruence hoddR hoddS hdiff with hd | hd
  · left
    have hsmall : |r - s| < (2 : ℤ) ^ (h + 1) := by
      rw [hhalf, abs_lt]
      constructor <;> omega
    have hz := Int.eq_zero_of_abs_lt_dvd hd hsmall
    omega
  · right
    have hsmall : |r + s| < (2 : ℤ) ^ (h + 1) := by
      rw [hhalf, abs_lt]
      constructor <;> omega
    have hz := Int.eq_zero_of_abs_lt_dvd hd hsmall
    omega

/-- Equation (140), before converting the radius to the explicit depth
threshold (139). Primality is unnecessary; oddness is sufficient. -/
theorem surviving_count_le_two (h : ℕ) {m : ℤ} (hm : Odd m)
    (hsize : Real.sqrt (m : ℝ) ≤ (2 : ℝ) ^ h) :
    (survivingTraces ((2 : ℤ) ^ (h + 2)) m).card ≤ 2 := by
  rw [survivingTraces_card_eq]
  let S := halvedTraces ((2 : ℤ) ^ (h + 2)) m
  change S.card ≤ 2
  have hrad : ∀ r ∈ S, |r| < (2 : ℤ) ^ h := by
    intro r hr
    have hrsq : (r : ℝ) ^ 2 < (m : ℝ) := by
      exact_mod_cast ((mem_halvedTraces _ _ _).mp hr).1
    have hlt : |(r : ℝ)| < Real.sqrt (m : ℝ) := by
      exact (Real.lt_sqrt (abs_nonneg _)).mpr (by simpa only [sq_abs] using hrsq)
    have := hlt.trans_le hsize
    exact_mod_cast this
  by_cases he : S = ∅
  · simp [he]
  · obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hsub : S ⊆ {r, -r} := by
      intro s hs
      have heq := two_roots_eq_or_neg h hm hs hr (hrad s hs) (hrad r hr)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using heq
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- The explicit threshold (139), with `log₂ x` expanded as `log x / log 2`.
The natural ceiling agrees with the integer ceiling in the paper's range
`k≥2`, `0<a<2`, where the argument is positive. -/
noncomputable def depthThreshold (k a : ℝ) : ℕ :=
  max 8 (1 + ⌈(Real.log (64 * k ^ a) / Real.log 2) / (1 - a / 2)⌉₊)

theorem sqrt_endpoint_lt_quarter_modulus {k a : ℝ} (hk : 0 < k)
    (ha : a < 2) (n : ℕ) (hn : depthThreshold k a ≤ n) :
    Real.sqrt ((k ^ 2 * (2 : ℝ) ^ n) ^ a) < (2 : ℝ) ^ n / 64 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < 1 - a / 2 := by linarith
  have hceil : ⌈(Real.log (64 * k ^ a) / Real.log 2) / (1 - a / 2)⌉₊ < n := by
    have hh := (le_max_right 8 (1 + ⌈(Real.log (64 * k ^ a) / Real.log 2) /
      (1 - a / 2)⌉₊)).trans hn
    omega
  have hratio := Nat.lt_of_ceil_lt hceil
  have hprod := (div_lt_iff₀ hd).mp hratio
  have hmain := (div_lt_iff₀ hl2).mp hprod
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 6 using 1 <;> norm_num
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hk, h64] at hmain
  have hbase : 0 < k ^ 2 * (2 : ℝ) ^ n := by positivity
  have hleft : 0 < Real.sqrt ((k ^ 2 * (2 : ℝ) ^ n) ^ a) := by positivity
  have hright : 0 < (2 : ℝ) ^ n / 64 := by positivity
  apply (Real.log_lt_log_iff hleft hright).mp
  rw [Real.log_sqrt (by positivity), Real.log_rpow hbase,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div (by positivity) (by norm_num), Real.log_pow, h64]
  norm_num
  nlinarith

/-- Equations (139) and (140) combined, for every positive odd integer
index up to the paper's endpoint. -/
theorem surviving_count_le_two_at_depth {k a : ℝ} (hk : 0 < k)
    (ha : a < 2) (n : ℕ) (hn : depthThreshold k a ≤ n)
    {m : ℤ} (hm : Odd m) (hmX : (m : ℝ) ≤ (k ^ 2 * (2 : ℝ) ^ n) ^ a) :
    (survivingTraces ((2 : ℤ) ^ (n - 4)) m).card ≤ 2 := by
  have hn8 : 8 ≤ n := (le_max_left 8 _).trans hn
  have hpower : (2 : ℝ) ^ n / 64 = (2 : ℝ) ^ (n - 6) := by
    rw [show n = (n - 6) + 6 by omega, pow_add]
    norm_num
  have hsize := (Real.sqrt_le_sqrt hmX).trans_lt
    (sqrt_endpoint_lt_quarter_modulus hk ha n hn)
  rw [hpower] at hsize
  have hc := surviving_count_le_two (n - 6) hm hsize.le
  simpa only [show n - 6 + 2 = n - 4 by omega] using hc

/-- The complex sum in (136), with the actual logarithmic/square-root weight. -/
noncomputable def supportSum (L : ℝ) (M : Finset ℤ) (E : ℤ → ℂ)
    (g : ℝ → ℂ) : ℂ :=
  (1 / L : ℝ) • ∑ m ∈ M,
    ((Real.log (m : ℝ) / Real.sqrt (m : ℝ) : ℝ) : ℂ) * E m *
      g (Real.log (m : ℝ) / L)

/-- Equation (137), including the factor 48 rather than the factor 96 in
the explicit-formula estimate (45). No cancellation is presumed. -/
theorem supportSum_bound {X N L δ K H a : ℝ} {q : ℤ}
    (hX : 1 ≤ X) (hL : 0 < L) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hq : 0 < q) (hN : N = 16 * (q : ℝ))
    (hlogX : Real.log X ≤ a * L)
    (M : Finset ℤ) (E : ℤ → ℂ) (g : ℝ → ℂ)
    (hM : ∀ m ∈ M, 1 ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (htrace : ∀ m ∈ M, ‖E m‖ ≤ K * N ^ (-(1 / 2 : ℝ)) *
      (m : ℝ) ^ δ * ((survivingTraces q m).card : ℝ))
    (hg : ∀ m ∈ M, ‖g (Real.log (m : ℝ) / L)‖ ≤ H) :
    ‖supportSum L M E g‖ ≤
      (48 * a * K * Real.sqrt 2 / (1 - (2 : ℝ) ^ (-1 - δ))) *
        H * N ^ (-(3 / 2 : ℝ)) * X ^ (1 + δ) := by
  have hb := PrimeSumBounds.prime_sum_bound hX hL hδ ha hK hH hq hN hlogX
    M (survivingTraces q) E g hM
    (fun m _ t ht => (mem_survivingTraces q m t).mp ht) htrace hg
  have hn : ‖supportSum L M E g‖ ≤
      (1 / L) * ∑ m ∈ M, PrimeSumBounds.weightedTerm L E g m := by
    unfold supportSum
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / L)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ∑ m ∈ M, ‖((Real.log (m : ℝ) / Real.sqrt (m : ℝ) : ℝ) : ℂ) *
          E m * g (Real.log (m : ℝ) / L)‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        have hw : 0 ≤ Real.log (m : ℝ) / Real.sqrt (m : ℝ) :=
          div_nonneg (Real.log_nonneg (hM m hm).1) (Real.sqrt_nonneg _)
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hw, PrimeSumBounds.weightedTerm]
  have heq :
      (96 * a * K * Real.sqrt 2 / (1 - (2 : ℝ) ^ (-1 - δ))) *
        H * N ^ (-(3 / 2 : ℝ)) * X ^ (1 + δ) =
      2 * ((48 * a * K * Real.sqrt 2 / (1 - (2 : ℝ) ^ (-1 - δ))) *
        H * N ^ (-(3 / 2 : ℝ)) * X ^ (1 + δ)) := by ring
  rw [heq] at hb
  have hscale : (2 / L) * (∑ m ∈ M, PrimeSumBounds.weightedTerm L E g m) =
      2 * ((1 / L) * ∑ m ∈ M, PrimeSumBounds.weightedTerm L E g m) := by ring
  rw [hscale] at hb
  linarith

/-- The unconditional exponent is strictly negative in precisely the
stated open support range after choosing the paper's positive delta. -/
theorem unconditional_exponent_negative {a δ : ℝ} (ha : 0 < a)
    (hδ : δ < (3 / 2 - a) / a) : -3 / 2 + a * (1 + δ) < 0 := by
  have := (lt_div_iff₀ ha).mp hδ
  nlinarith

theorem unconditional_exponent_positive {a δ : ℝ} (ha : 3 / 2 ≤ a)
    (hδ : 0 < δ) : 0 < -3 / 2 + a * (1 + δ) := by
  have hprod : 0 < a * δ := mul_pos (by linarith) hδ
  nlinarith

/-- Negating a matrix does not change which primitive vectors span fixed
lines: the eigenvalue unit is simply negated. -/
theorem fixedPair_neg_iff {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (p : ProjectiveCharts.PrimitivePair R) :
    FixedLines.FixedPair (-M) p ↔ FixedLines.FixedPair M p := by
  constructor <;> rintro ⟨u, h1, h2⟩ <;> refine ⟨-u, ?_, ?_⟩
  · simpa only [Matrix.neg_apply, neg_mul, ← neg_add, Units.val_neg, neg_neg] using
      congrArg Neg.neg h1
  · simpa only [Matrix.neg_apply, neg_mul, ← neg_add, Units.val_neg, neg_neg] using
      congrArg Neg.neg h2
  · simpa only [Matrix.neg_apply, neg_mul, ← neg_add, Units.val_neg, neg_neg] using
      congrArg Neg.neg h1
  · simpa only [Matrix.neg_apply, neg_mul, ← neg_add, Units.val_neg, neg_neg] using
      congrArg Neg.neg h2

theorem isFixed_neg_iff {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (p : ProjectiveCharts.ProjectiveLine R) :
    FixedLines.IsFixed (-M) p ↔ FixedLines.IsFixed M p := by
  refine Quotient.inductionOn p ?_
  exact fixedPair_neg_iff M

/-- The trace polynomial has the parity of its degree. This proves the
absence of cancellation between the `t` and `-t` polynomial factors at even
weight, using the actual recurrence from the trace formula. -/
theorem tracePolynomial_neg (t m : ℂ) (n : ℕ) :
    tracePolynomial (-t) m n = (-1 : ℂ) ^ n * tracePolynomial t m n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [tracePolynomial]
  | one => simp [tracePolynomial]
  | more n ih₀ ih₁ =>
    change (-t) * tracePolynomial (-t) m (n + 1) - m * tracePolynomial (-t) m n =
      (-1 : ℂ) ^ (n + 2) *
        (t * tracePolynomial t m (n + 1) - m * tracePolynomial t m n)
    rw [ih₀, ih₁, pow_add, pow_add]
    norm_num
    ring

theorem tracePolynomial_neg_even (t m : ℂ) (n : ℕ) (hn : Even n) :
    tracePolynomial (-t) m n = tracePolynomial t m n := by
  rw [tracePolynomial_neg, hn.neg_one_pow, one_mul]

theorem tracePolynomial_weight_two (t m : ℂ) : tracePolynomial t m (2 - 2) = 1 := rfl

end DepthAspect.SectionSevenSupport
