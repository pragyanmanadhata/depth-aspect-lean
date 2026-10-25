import DepthAspect.SignedPrimeExpression
import DepthAspect.SignedPrimeClassWeights
import DepthAspect.SignedPrimeNormalization
import DepthAspect.SignedArithmeticData

/-!
# The literal prime formulas (75) and (76)

The finite trace interval, the Ramanujan coefficient, the actual quadratic
L-value, and the common spectral family are all retained. The pointwise
class-number collapse is proved before applying the trace normalization.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators
open DyadicRamanujan QuadraticDiscriminantL QuadraticClassFormula

/-- The standard cosine in the prime formulas, for weight 2r+2. -/
noncomputable def primeCosine (r c P : ℕ) (t : ℤ) : ℝ :=
  Real.cos ((2 * (r : ℝ) + 1) *
    Real.arcsin ((t : ℝ) / (2 * Real.sqrt ((c : ℝ) * P))))

/-- Strict elliptic traces in the same canonical finite interval as the
general trace expression. -/
noncomputable def strictPrimeTraces (c P : ℕ) : Finset ℤ :=
  (closedTraces c P).filter (fun t => t ^ 2 < 4 * (c : ℤ) * P)

@[simp] theorem mem_strictPrimeTraces (c P : ℕ) (hc : 0 < c) (hP : 0 < P) (t : ℤ) :
    t ∈ strictPrimeTraces c P ↔ t ^ 2 < 4 * (c : ℤ) * P := by
  rw [strictPrimeTraces, Finset.mem_filter, mem_closedTraces c P hc hP]
  exact and_iff_right_of_imp le_of_lt

theorem strictPrimeTraces_eq_closed (b P : ℕ) (hP : P.Prime) (hodd : Odd P) :
    strictPrimeTraces (2 ^ b) P = closedTraces (2 ^ b) P := by
  classical
  ext t
  rw [mem_strictPrimeTraces _ _ (by positivity) hP.pos,
    mem_closedTraces _ _ (by positivity) hP.pos]
  constructor
  · exact le_of_lt
  · intro ht
    have he : (4 : ℤ) * (2 ^ b : ℕ) * P = (2 : ℤ) ^ (b + 2) * P := by
      push_cast
      rw [pow_add]
      ring
    rw [he] at ht ⊢
    exact prime_common_interval_strict (b + 2) P hP hodd t ht

theorem ramanujanTwoPow_eq_zero_of_not_eight_dvd (a : ℕ) (ha : 3 ≤ a)
    (t : ℤ) (ht : ¬ 8 ∣ t) : ramanujanTwoPow a t = 0 := by
  have hs : ¬ (2 : ℤ) ^ a ∣ t := by
    intro h
    apply ht
    exact dvd_trans (by simpa using (pow_dvd_pow (2 : ℤ) ha)) h
  have hl : ¬ (2 : ℤ) ^ (a + 1) ∣ t := by
    intro h
    exact hs (dvd_trans (pow_dvd_pow 2 (by omega : a ≤ a + 1)) h)
  rw [ramanujanTwoPow_formula, if_neg hs, if_neg hl]
  ring

/-- The finite stratum weight is already a Ramanujan coefficient times
the first class-number difference, before evaluating the local character. -/
theorem commonStratumWeight_collapse {H : ℤ → ℝ} (G : GeneralFormula H)
    (a b P : ℕ) (t : ℤ) (hD : IsNegativeDiscriminant (t ^ 2 - 4 * (2 ^ b : ℕ) * P)) :
    commonStratumWeight (2 ^ b) (2 ^ a) P H t =
      -ramanujanTwoPow (a + b + 1) t / (2 : ℂ) ^ (b + 1) *
        ((H (4 * (t ^ 2 - 4 * (2 ^ b : ℕ) * P)) -
          H (t ^ 2 - 4 * (2 ^ b : ℕ) * P) : ℝ) : ℂ) := by
  have hc1 : (((2 * 2 ^ b * 2 ^ a : ℕ) : ℤ)) = 2 ^ (a + b + 1) := by
    push_cast
    simp only [pow_add, pow_one]
    ring
  have hc2 : (((4 * 2 ^ b * 2 ^ a : ℕ) : ℤ)) = 2 ^ (a + b + 2) := by
    push_cast
    simp only [pow_add]
    ring
  have hs0 : ((2 ^ a : ℕ) : ℤ) ^ 2 = (4 : ℤ) ^ a := by
    push_cast
    rw [← pow_mul, mul_comm a 2, pow_mul]
    norm_num
  have hs1 : (((2 * 2 ^ a : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ (a + 1) := by
    calc
      _ = 4 * (((2 ^ a : ℕ) : ℤ)) ^ 2 := by push_cast; ring
      _ = _ := by rw [hs0, pow_succ]; ring
  have hs2 : (((4 * 2 ^ a : ℕ) : ℤ)) ^ 2 = (4 : ℤ) ^ (a + 2) := by
    calc
      _ = 16 * (((2 ^ a : ℕ) : ℤ)) ^ 2 := by push_cast; ring
      _ = _ := by rw [hs0, pow_add]; norm_num <;> ring
  simp only [commonStratumWeight, hc1, hc2, hs0, hs1, hs2]
  simp only [← Complex.ofReal_sub]
  rw [class_scaling G _ hD a,
    show a + 2 = (a + 1) + 1 by omega, class_scaling G _ hD (a + 1),
    ramanujanTwoPow_formula]
  simp only [show a + b + 1 + 1 = a + b + 2 by omega]
  split_ifs <;> push_cast <;> simp only [pow_add, pow_one, pow_succ]
    <;> field_simp <;> ring

/-- At even depth the actual class-number weight reduces to the residue
table w(P), with the true Ramanujan support enforcing 8 | t. -/
theorem commonStratumWeight_even {H : ℤ → ℝ} (G : GeneralFormula H)
    (a P : ℕ) (ha : 2 ≤ a) (hP : Odd P) (t : ℤ) (ht : t ^ 2 < 4 * (P : ℤ)) :
    commonStratumWeight 1 (2 ^ a) P H t =
      -2 * ramanujanTwoPow (a + 1) t * (primeWeight P : ℂ) *
        (H (t ^ 2 - 4 * P) : ℂ) := by
  have h := commonStratumWeight_collapse G a 0 P t
    (by simpa using elliptic_isNegativeDiscriminant t P ht)
  norm_num only [pow_zero, pow_one, Nat.cast_one, mul_one, add_zero] at h
  rw [h]
  by_cases h8 : (8 : ℤ) ∣ t
  · rw [even_prime_class_difference G t P h8 (by exact_mod_cast hP) ht]
    push_cast
    ring
  · rw [ramanujanTwoPow_eq_zero_of_not_eight_dvd (a + 1) (by omega) t h8]
    ring

/-- At odd depth the actual conductor is odd on the Ramanujan support,
so the first difference is twice H(D). -/
theorem commonStratumWeight_odd {H : ℤ → ℝ} (G : GeneralFormula H)
    (a P : ℕ) (ha : 1 ≤ a) (hP : Odd P) (t : ℤ) (ht : t ^ 2 < 8 * (P : ℤ)) :
    commonStratumWeight 2 (2 ^ a) P H t =
      -ramanujanTwoPow (a + 2) t / 2 * (H (t ^ 2 - 8 * P) : ℂ) := by
  have hD : IsNegativeDiscriminant (t ^ 2 - 4 * (2 ^ 1 : ℕ) * P) := by
    convert elliptic_isNegativeDiscriminant t (2 * P) (by nlinarith : t ^ 2 < 4 * (2 * P)) using 1 <;>
      norm_num <;> ring
  have h := commonStratumWeight_collapse G a 1 P t hD
  norm_num only [pow_one, Nat.cast_ofNat, show a + 1 + 1 = a + 2 by omega] at h
  norm_num at h
  rw [h]
  by_cases h8 : (8 : ℤ) ∣ t
  · rw [← Complex.ofReal_sub,
      odd_prime_class_difference G t P h8 (by exact_mod_cast hP) ht]
    push_cast
    ring
  · rw [ramanujanTwoPow_eq_zero_of_not_eight_dvd (a + 2) (by omega) t h8]
    ring

/-- The trace polynomial, the literal class-number identity, and the
individual Hecke normalization combine to the actual quadratic L-value. -/
theorem normalizedHurwitzTerm {H : ℤ → ℝ} (G : GeneralFormula H)
    (r c P : ℕ) (hc : 0 < c) (hP : 0 < P) (t : ℤ)
    (ht : t ^ 2 < 4 * (c : ℤ) * P) :
    (-1 : ℂ) ^ (r + 1) *
      tracePolynomial (((t : ℝ) / Real.sqrt c : ℝ) : ℂ) (P : ℂ) (2 * r) *
      (H (t ^ 2 - 4 * c * P) : ℂ) /
      (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
      -((2 * Real.sqrt c / Real.pi * primeCosine r c P t : ℝ) : ℂ) *
        LAtOne G (t ^ 2 - 4 * c * P) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have htR : (t : ℝ) ^ 2 < 4 * (c : ℝ) * P := by exact_mod_cast ht
  have hD : IsNegativeDiscriminant (t ^ 2 - 4 * c * P) := by
    convert elliptic_isNegativeDiscriminant t ((c : ℤ) * P) (by nlinarith) using 1 <;> ring
  have hsqrt : -((t ^ 2 - 4 * (c : ℤ) * P : ℤ) : ℝ) =
      4 * (c : ℝ) * P - (t : ℝ) ^ 2 := by push_cast; ring
  rw [hurwitz_eq G _ hD, hsqrt]
  push_cast
  rw [LAtOne_ofReal_re]
  have h := normalizedClassTerm r t c P hcR hPR htR (LAtOne G (t ^ 2 - 4 * c * P))
  simp only [primeCosine]
  push_cast at h ⊢
  simpa only [mul_assoc] using h

theorem normalized_even_prime_term {H : ℤ → ℝ} (G : GeneralFormula H)
    (r a P : ℕ) (ha : 2 ≤ a) (hP : 0 < P) (hodd : Odd P)
    (t : ℤ) (ht : t ^ 2 < 4 * (P : ℤ)) :
    (Real.sqrt P : ℂ) * (-1 : ℂ) ^ (r + 1) *
      (tracePolynomial (t : ℂ) (P : ℂ) (2 * r) *
        commonStratumWeight 1 (2 ^ a) P H t / 2) /
        (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((2 * Real.sqrt P / Real.pi * primeWeight P : ℝ) : ℂ) *
        (ramanujanTwoPow (a + 1) t * (primeCosine r 1 P t : ℂ) *
          LAtOne G (t ^ 2 - 4 * P)) := by
  rw [commonStratumWeight_even G a P ha hodd t ht]
  have hterm := normalizedHurwitzTerm G r 1 P (by decide) hP t
    (by simpa using ht)
  norm_num only [Nat.cast_one, mul_one, Real.sqrt_one, div_one,
    Complex.ofReal_intCast] at hterm
  calc
    _ = -((Real.sqrt P : ℂ) * ramanujanTwoPow (a + 1) t * (primeWeight P : ℂ)) *
        ((-1 : ℂ) ^ (r + 1) * tracePolynomial (t : ℂ) (P : ℂ) (2 * r) *
          (H (t ^ 2 - 4 * P) : ℂ) /
          (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hterm]; push_cast; ring

theorem normalized_odd_prime_term {H : ℤ → ℝ} (G : GeneralFormula H)
    (r a P : ℕ) (ha : 1 ≤ a) (hP : 0 < P) (hodd : Odd P)
    (t : ℤ) (ht : t ^ 2 < 8 * (P : ℤ)) :
    (Real.sqrt P : ℂ) * (-1 : ℂ) ^ (r + 1) *
      (tracePolynomial (((t : ℝ) / Real.sqrt 2 : ℝ) : ℂ) (P : ℂ) (2 * r) *
        commonStratumWeight 2 (2 ^ a) P H t / 2) /
        (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((Real.sqrt P / (Real.pi * Real.sqrt 2) : ℝ) : ℂ) *
        (ramanujanTwoPow (a + 2) t * (primeCosine r 2 P t : ℂ) *
          LAtOne G (t ^ 2 - 8 * P)) := by
  rw [commonStratumWeight_odd G a P ha hodd t ht]
  have hterm := normalizedHurwitzTerm G r 2 P (by decide) hP t
    (by norm_num; exact ht)
  norm_num only [Nat.cast_ofNat] at hterm
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
  calc
    _ = -((Real.sqrt P : ℂ) * ramanujanTwoPow (a + 2) t / 4) *
        ((-1 : ℂ) ^ (r + 1) *
          tracePolynomial (((t : ℝ) / Real.sqrt 2 : ℝ) : ℂ) (P : ℂ) (2 * r) *
          (H (t ^ 2 - 8 * P) : ℂ) /
          (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ)) := by ring
    _ = _ := by
      rw [hterm]
      push_cast
      have hs2C : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast hs2
      field_simp [hs2ne] <;> ring_nf <;> simp only [hs2C] <;> ring

/-- The auxiliary power is exactly P^(1-k/2), since k=2r+2. -/
theorem sqrt_div_hecke_power (r P : ℕ) (hP : 0 < P) :
    Real.sqrt P / (P : ℝ) ^ ((r : ℝ) + 1 / 2) = (P : ℝ) ^ (-(r : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (by exact_mod_cast hP : (0 : ℝ) < P)]
  congr 1
  ring

theorem normalized_prime_expression_even {H : ℤ → ℝ} (G : GeneralFormula H)
    (r a P : ℕ) (ha : 2 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    (Real.sqrt P : ℂ) * (-1 : ℂ) ^ (r + 1) *
      newSignedExpression (2 * r) (2 ^ (2 * a + 4)) P H /
        (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((2 * Real.sqrt P / Real.pi * primeWeight P : ℝ) : ℂ) *
        (∑ t ∈ strictPrimeTraces 1 P,
          ramanujanTwoPow (a + 1) t * (primeCosine r 1 P t : ℂ) *
            LAtOne G (t ^ 2 - 4 * P)) +
      (-1 : ℂ) ^ (r + 2) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
        (((P : ℝ) ^ (-(r : ℝ)) : ℝ) : ℂ) := by
  classical
  have hset := strictPrimeTraces_eq_closed 0 P hP hodd
  norm_num only [pow_zero] at hset
  rw [hset, newSignedExpression_prime_even (2 * r) a P hP H]
  have hterms : ∀ t ∈ closedTraces 1 P,
      (Real.sqrt P : ℂ) * (-1 : ℂ) ^ (r + 1) *
        (tracePolynomial (t : ℂ) (P : ℂ) (2 * r) *
          commonStratumWeight 1 (2 ^ a) P H t / 2) /
          (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((2 * Real.sqrt P / Real.pi * primeWeight P : ℝ) : ℂ) *
        (ramanujanTwoPow (a + 1) t * (primeCosine r 1 P t : ℂ) *
          LAtOne G (t ^ 2 - 4 * P)) := by
    intro t ht
    have hb := (mem_closedTraces 1 P (by decide) hP.pos t).mp ht
    norm_num only [Nat.cast_one, mul_one] at hb
    exact normalized_even_prime_term G r a P ha hP.pos hodd t
      (by simpa using prime_common_interval_strict 2 P hP hodd t (by simpa using hb))
  have hsum := Finset.sum_congr rfl hterms
  have haux : -(Real.sqrt P : ℂ) * (-1 : ℂ) ^ (r + 1) *
      ramanujanTwoPow (a + 1) (P + 1) / 2 /
        (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
      (-1 : ℂ) ^ (r + 2) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
        (((P : ℝ) ^ (-(r : ℝ)) : ℝ) : ℂ) := by
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    have hp := congrArg (fun x : ℝ => (x : ℂ)) (sqrt_div_hecke_power r P hP.pos)
    push_cast at hp
    calc
      _ = -(-1 : ℂ) ^ (r + 1) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
          ((Real.sqrt P : ℂ) / (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ)) := by ring
      _ = _ := by rw [hp]; ring
  simp only [← Finset.sum_div, ← Finset.mul_sum] at hsum
  rw [mul_sub, sub_div]
  push_cast at hsum haux ⊢
  linear_combination hsum + haux

theorem normalized_prime_expression_odd {H : ℤ → ℝ} (G : GeneralFormula H)
    (r a P : ℕ) (ha : 1 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    (Real.sqrt P : ℂ) * (-1 : ℂ) ^ (r + 1) *
      newSignedExpression (2 * r) (2 ^ (2 * a + 5)) P H /
        (((P : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((Real.sqrt P / (Real.pi * Real.sqrt 2) : ℝ) : ℂ) *
        ∑ t ∈ strictPrimeTraces 2 P,
          ramanujanTwoPow (a + 2) t * (primeCosine r 2 P t : ℂ) *
            LAtOne G (t ^ 2 - 8 * P) := by
  classical
  have hset := strictPrimeTraces_eq_closed 1 P hP hodd
  norm_num only [pow_one] at hset
  rw [hset, newSignedExpression_prime_odd (2 * r) a P hP H]
  have hterms := fun t ht => normalized_odd_prime_term G r a P ha hP.pos hodd t (by
    have hb := (mem_closedTraces 2 P (by decide) hP.pos t).mp ht
    norm_num only [Nat.cast_ofNat] at hb
    exact prime_common_interval_strict 3 P hP hodd t (by norm_num; exact hb))
  have hsum := Finset.sum_congr rfl hterms
  simpa only [← Finset.sum_div, ← Finset.mul_sum, div_div] using hsum

namespace SignedArithmeticData
variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- Equation (75) for the same finite family and Hecke eigenvalues used by
the unsigned density theorem. The only arithmetic inputs are general. -/
theorem primeSignedTrace_even (S : SignedArithmeticData r Family Full New)
    (a P : ℕ) (ha : 2 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    S.primeSignedTrace (2 ^ (2 * a + 4)) P =
      ((2 * Real.sqrt P / Real.pi * primeWeight P : ℝ) : ℂ) *
        (∑ t ∈ strictPrimeTraces 1 P,
          ramanujanTwoPow (a + 1) t * (primeCosine r 1 P t : ℂ) *
            LAtOne S.quadratic_class_formula (t ^ 2 - 4 * P)) +
      (-1 : ℂ) ^ (r + 2) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
        (((P : ℝ) ^ (-(r : ℝ)) : ℝ) : ℂ) := by
  rw [S.primeSignedTrace_eq_expression _ P hP.pos hodd]
  exact normalized_prime_expression_even S.quadratic_class_formula r a P ha hP hodd

/-- Equation (76), including the exact factor 1/(π√2) and absence of an
auxiliary term, for the common finite spectral family. -/
theorem primeSignedTrace_odd (S : SignedArithmeticData r Family Full New)
    (a P : ℕ) (ha : 1 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    S.primeSignedTrace (2 ^ (2 * a + 5)) P =
      ((Real.sqrt P / (Real.pi * Real.sqrt 2) : ℝ) : ℂ) *
        ∑ t ∈ strictPrimeTraces 2 P,
          ramanujanTwoPow (a + 2) t * (primeCosine r 2 P t : ℂ) *
            LAtOne S.quadratic_class_formula (t ^ 2 - 8 * P) := by
  rw [S.primeSignedTrace_eq_expression _ P hP.pos hodd]
  exact normalized_prime_expression_odd S.quadratic_class_formula r a P ha hP hodd

end SignedArithmeticData
end DepthAspect.SignedSieve

