import DepthAspect.OddAverageEuler
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Separating the actual dyadic series from the odd Euler product

The coefficient identity is a Dirichlet convolution with one surviving divisor
pair. Thus the twisted degree-zero dyadic coefficient may vanish; no false
multiplicativity assumption about the full averaged sequence is needed.
-/
noncomputable section
open scoped BigOperators LSeries.notation
namespace DepthAspect.DyadicOddSeries
open GlobalResidueMean GlobalResidueCoefficient

/-- The literal dyadic coefficients in (84). -/
def dyadicValue (t : ℤ) (χ : DirichletCharacter ℂ 8) (b : ℕ) : ℂ :=
  average (2 ^ b) t χ

/-- A coefficient sequence supported on powers of two. -/
def dyadicSequence (t : ℤ) (χ : DirichletCharacter ℂ 8) (n : ℕ) : ℂ :=
  if n = 2 ^ n.factorization 2 then dyadicValue t χ (n.factorization 2) else 0

 theorem oddMean_twoPower (t : ℤ) (b : ℕ) : OddMeanMajorant.oddMean (2 ^ b) t = 1 := by
  cases b with
  | zero => simp [OddMeanMajorant.oddMean]
  | succ b =>
    simp only [OddMeanMajorant.oddMean,
      Nat.primeFactors_prime_pow (Nat.succ_ne_zero b) Nat.prime_two,
      Finset.erase_singleton, Finset.prod_empty]

 theorem dyadicValue_eq_mean (t : ℤ) (χ : DirichletCharacter ℂ 8) (b : ℕ) :
    dyadicValue t χ b = dyadicMean (2 ^ b) t χ := by
  rw [dyadicValue, average_factorization, oddMean_twoPower]
  simp

 theorem dyadicMean_eq_value (m : ℕ) (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    dyadicMean m t χ = dyadicValue t χ (m.factorization 2) := by
  rw [dyadicValue_eq_mean]
  -- Abstract the exponent before rewriting it: it controls both the local
  -- coefficient and the type of the finite unit group being averaged.
  let F : ℕ → ℂ := fun b =>
    FiniteCharacterFourier.coefficient
      (fun x : (ZMod (2 ^ max 3 (2 * b)))ˣ =>
        χ (-1) *
          (χ.changeLevel (show 8 ∣ 2 ^ max 3 (2 * b) from
            pow_dvd_pow 2 (le_max_left 3 (2 * b)))) x *
          DyadicCoefficientFourier.localAtTwo (max 3 (2 * b)) b
            (le_max_right 3 (2 * b)) t x) 1
  have hb : (2 ^ m.factorization 2).factorization 2 = m.factorization 2 :=
    Nat.factorization_pow_self Nat.prime_two
  have hF := congrArg F hb
  -- Reduce only the wrappers on both sides. In particular, keep the finite
  -- Fourier coefficient opaque rather than asking `change` to discover this
  -- equality by unfolding its finite sum and all residue-group instances.
  dsimp only [F] at hF
  dsimp only [dyadicMean, dyadicFunction, twoExponent]
  exact hF.symm

 theorem norm_dyadicValue_le (t : ℤ) (χ : DirichletCharacter ℂ 8) (b : ℕ) :
    ‖dyadicValue t χ b‖ ≤ 1 := by
  rw [dyadicValue_eq_mean]
  exact norm_dyadicMean_le _ t χ

 theorem dyadicSequence_twoPower (t : ℤ) (χ : DirichletCharacter ℂ 8) (b : ℕ) :
    dyadicSequence t χ (2 ^ b) = dyadicValue t χ b := by
  unfold dyadicSequence
  rw [Nat.factorization_pow_self Nat.prime_two, if_pos rfl]

 theorem dyadicSequence_zero (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    dyadicSequence t χ 0 = 0 := by simp [dyadicSequence]

 theorem dyadicSequence_off_range (t : ℤ) (χ : DirichletCharacter ℂ 8) (n : ℕ)
    (hn : n ∉ Set.range (fun b : ℕ => 2 ^ b)) : dyadicSequence t χ n = 0 := by
  apply if_neg
  intro h
  exact hn ⟨n.factorization 2, h.symm⟩

private theorem factorization_two_odd {n : ℕ} (hn : Odd n) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd hn.not_two_dvd_nat

 theorem oddMean_ordCompl (m : ℕ) (t : ℤ) :
    OddMeanMajorant.oddMean (ordCompl[2] m) t = OddMeanMajorant.oddMean m t := by
  unfold OddMeanMajorant.oddMean
  rw [← Nat.support_factorization, Nat.factorization_ordCompl, Finsupp.support_erase,
    Finset.erase_idem]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Finsupp.erase_ne (Finset.mem_erase.mp hp).1]

 theorem sequence_decomposition (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {n : ℕ} (hn : n ≠ 0) :
    sequence t χ n = dyadicValue t χ (n.factorization 2) *
      OddAverageEuler.coefficient t (ordCompl[2] n) := by
  letI : NeZero n := ⟨hn⟩
  have ho : Odd (ordCompl[2] n) :=
    Nat.not_even_iff_odd.mp (fun h => Nat.not_dvd_ordCompl Nat.prime_two hn h.two_dvd)
  rw [sequence_eq, average_factorization, dyadicMean_eq_value,
    OddAverageEuler.coefficient_odd t ho, oddMean_ordCompl]

/-- Any nonzero convolution summand must be the canonical dyadic/odd pair. -/
theorem surviving_divisor_pair (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {n a b : ℕ} (hn : n ≠ 0) (hab : a * b = n)
    (ha : dyadicSequence t χ a ≠ 0) (hb : OddAverageEuler.coefficient t b ≠ 0) :
    a = 2 ^ n.factorization 2 ∧ b = ordCompl[2] n := by
  have ha0 : a ≠ 0 := by intro h; simp [h, dyadicSequence_zero] at ha
  have hb0 : b ≠ 0 := by intro h; simp [h] at hb
  have hapow : a = 2 ^ a.factorization 2 := by
    by_contra h
    exact ha (by simp [dyadicSequence, h])
  have hob : Odd b := by
    rcases Nat.even_or_odd b with he | ho
    · exact False.elim (hb (OddAverageEuler.coefficient_even t he))
    · exact ho
  have hv : n.factorization 2 = a.factorization 2 := by
    rw [← hab, Nat.factorization_mul ha0 hb0, Finsupp.add_apply,
      factorization_two_odd hob, add_zero]
  have heq : a = 2 ^ n.factorization 2 := by rw [hv]; exact hapow
  refine ⟨heq, ?_⟩
  change b = n / 2 ^ n.factorization 2
  rw [← heq, ← hab, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha0)]

/-- The full coefficient sequence is exactly the dyadic/odd convolution. -/
theorem sequence_eq_convolution (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    sequence t χ = dyadicSequence t χ ⍟ OddAverageEuler.coefficient t := by
  funext n
  rw [LSeries.convolution_def]
  dsimp only
  by_cases hn : n = 0
  · subst n
    simp [GlobalResidueMean.sequence]
  let c : ℕ × ℕ := (2 ^ n.factorization 2, ordCompl[2] n)
  have hc : c ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr
    ⟨Nat.ordProj_mul_ordCompl_eq_self n 2, hn⟩
  rw [Finset.sum_eq_single_of_mem c hc]
  · rw [sequence_decomposition t χ hn, dyadicSequence_twoPower]
  · rintro ⟨a,b⟩ hab hne
    by_cases ha : dyadicSequence t χ a = 0
    · simp [ha]
    by_cases hb : OddAverageEuler.coefficient t b = 0
    · simp [hb]
    have heq := surviving_divisor_pair t χ hn (Nat.mem_divisorsAntidiagonal.mp hab).1 ha hb
    exact False.elim (hne (Prod.ext heq.1 heq.2))

/-- The actual E2 series. -/
def dyadicSeries (t : ℤ) (χ : DirichletCharacter ℂ 8) (z : ℂ) : ℂ :=
  ∑' b : ℕ, dyadicValue t χ b * z ^ b

 theorem dyadicSeries_summable (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {z : ℂ} (hz : ‖z‖ < 1) : Summable (fun b : ℕ => dyadicValue t χ b * z ^ b) := by
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz)
  intro b
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg z) _) (norm_dyadicValue_le t χ b)

 theorem dyadic_LSeries (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {s : ℂ} (hs : 0 < s.re) :
    LSeriesHasSum (dyadicSequence t χ) s (dyadicSeries t χ ((2 : ℂ) ^ (-s))) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hz : ‖(2 : ℂ) ^ (-s)‖ < 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum := (dyadicSeries_summable t χ hz).hasSum
  apply (Nat.pow_right_injective (by omega : 1 < 2)).hasSum_iff
    (fun n hn => by simp [LSeries.term, dyadicSequence_off_range t χ n hn]) |>.mp
  convert! hsum using 1
  funext b
  rw [Function.comp_apply, LSeries.term_of_ne_zero (pow_ne_zero _ (by omega)),
    dyadicSequence_twoPower, div_eq_mul_inv, ← Complex.cpow_neg]
  congr 1
  exact map_pow (riemannZetaSummandHom hs0) 2 b

/-- The complete first equality of (84), with both series absolutely
convergent on the claimed half-plane. -/
theorem LSeries_factorization (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeries (sequence t χ) s = dyadicSeries t χ ((2 : ℂ) ^ (-s)) *
      LSeries (OddAverageEuler.coefficient t) s := by
  rw [sequence_eq_convolution,
    LSeries_convolution' (dyadic_LSeries t χ (by linarith : 0 < s.re)).LSeriesSummable
      (OddAverageEuler.summable_norm_terms t hs).of_norm,
    (dyadic_LSeries t χ (by linarith : 0 < s.re)).LSeries_eq]

end DepthAspect.DyadicOddSeries
