import DepthAspect.SignedStratumReindex
import DepthAspect.TraceTrigonometry

/-!
# The literal rescaling of the surviving prime trace strata

For v=c*s², the integral change t=c*s*u gives the common interval t²≤4cm.
The choices c=1 and c=2 are the even- and odd-depth changes of variables in
Proposition 5.2. Divisibility and the even-u restriction are retained exactly.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators

/-- The integer change of variables used in both parity cases. -/
theorem sum_quotientTraces_scale (c s m : ℕ) (hc : 0 < c) (hs : 0 < s)
    (hm : 0 < m) (F : ℤ → ℂ) :
    (∑ u ∈ quotientTraces (c * s ^ 2) m, F (((c * s : ℕ) : ℤ) * u)) =
      ∑ t ∈ closedTraces c m,
        if ((c * s : ℕ) : ℤ) ∣ t then F t else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hcZ : (0 : ℤ) < c := by exact_mod_cast hc
  have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
  apply Finset.sum_bij (fun u _ => (((c * s : ℕ) : ℤ) * u))
  · intro u hu
    have hb := (mem_quotientTraces (c * s ^ 2) m (by positivity) hm u).mp hu
    refine Finset.mem_filter.mpr ⟨?_, dvd_mul_right _ _⟩
    rw [mem_closedTraces c m hc hm]
    push_cast at hb ⊢
    nlinarith [mul_le_mul_of_nonneg_left hb hcZ.le]
  · intro u hu w hw heq
    exact mul_left_cancel₀ (by positivity : (((c * s : ℕ) : ℤ)) ≠ 0) heq
  · intro t ht
    obtain ⟨ht, hdiv⟩ := Finset.mem_filter.mp ht
    obtain ⟨u, rfl⟩ := hdiv
    refine ⟨u, ?_, rfl⟩
    have hb := (mem_closedTraces c m hc hm _).mp ht
    rw [mem_quotientTraces (c * s ^ 2) m (by positivity) hm]
    apply (mul_le_mul_iff_right₀ hcZ).mp
    push_cast at hb ⊢
    nlinarith [hb]
  · intro u hu
    rfl

/-- The even-u subinterval becomes divisibility by twice the scale. -/
theorem sum_quotientTraces_scale_even (c s m : ℕ) (hc : 0 < c) (hs : 0 < s)
    (hm : 0 < m) (F : ℤ → ℂ) :
    (∑ u ∈ quotientTraces (c * s ^ 2) m,
      if Even u then F (((c * s : ℕ) : ℤ) * u) else 0) =
      ∑ t ∈ closedTraces c m,
        if (2 * ((c * s : ℕ) : ℤ)) ∣ t then F t else 0 := by
  classical
  have hscale : (((c * s : ℕ) : ℤ)) ≠ 0 := by positivity
  have heven (u : ℤ) : (2 * ((c * s : ℕ) : ℤ)) ∣ (((c * s : ℕ) : ℤ) * u) ↔
      Even u := by
    rw [mul_comm 2, mul_dvd_mul_iff_left hscale, even_iff_two_dvd]
  have hrepl :
      (∑ u ∈ quotientTraces (c * s ^ 2) m,
        if Even u then F (((c * s : ℕ) : ℤ) * u) else 0) =
      ∑ u ∈ quotientTraces (c * s ^ 2) m,
        if (2 * ((c * s : ℕ) : ℤ)) ∣ (((c * s : ℕ) : ℤ) * u)
        then F (((c * s : ℕ) : ℤ) * u) else 0 := by
    simp only [heven]
  rw [hrepl]
  rw [sum_quotientTraces_scale c s m hc hs hm
    (fun t => if 2 * ((c * s : ℕ) : ℤ) ∣ t then F t else 0)]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h2 : 2 * ((c * s : ℕ) : ℤ) ∣ t
  · have h1 : ((c * s : ℕ) : ℤ) ∣ t := dvd_trans (dvd_mul_left _ _) h2
    simp only [h2, h1, if_true]
  · simp only [h2, if_false, ite_self]

/-- The complex trace-polynomial arguments after the rescaling agree
literally. This proves the polynomial change in both parity cases. -/
theorem tracePolynomial_quotient_scale (r c s m : ℕ) (hc : 0 < c) (hs : 0 < s)
    (u : ℤ) :
    tracePolynomial
      ((((c * s ^ 2 : ℕ) : ℝ) * u / Real.sqrt (c * s ^ 2) : ℝ) : ℂ) (m : ℂ) r =
      tracePolynomial
        ((((c * s : ℕ) : ℝ) * u / Real.sqrt c : ℝ) : ℂ) (m : ℂ) r := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hroot : Real.sqrt (c * s ^ 2) = Real.sqrt c * s := by
    rw [Real.sqrt_mul hcR.le, Real.sqrt_sq hsR.le]
  congr 2
  push_cast
  rw [hroot]
  field_simp [ne_of_gt hsR, ne_of_gt (Real.sqrt_pos.mpr hcR)]

/-- The discriminant changes by the exact positive square scaling. -/
theorem discriminant_quotient_scale (c s m : ℕ) (u : ℤ) :
    (((c * s ^ 2 : ℕ) : ℤ) * u) ^ 2 - 4 * ((c * s ^ 2 : ℕ) : ℤ) * m =
      (s : ℤ) ^ 2 * ((((c * s : ℕ) : ℤ) * u) ^ 2 - 4 * c * m) := by
  push_cast
  ring


/-- Full class-number weighted rescaling of one actual surviving stratum. -/
theorem weighted_quotient_scale (r c s m : ℕ) (hc : 0 < c) (hs : 0 < s)
    (hm : 0 < m) (H : ℤ → ℝ) :
    (∑ u ∈ quotientTraces (c * s ^ 2) m,
      tracePolynomial
        ((((((c * s ^ 2 : ℕ) : ℤ) * u : ℤ) : ℝ) / Real.sqrt ((c * s ^ 2 : ℕ) : ℝ) : ℝ) : ℂ)
        (m : ℂ) r *
      (H ((((c * s ^ 2 : ℕ) : ℤ) * u) ^ 2 -
        4 * ((c * s ^ 2 : ℕ) : ℤ) * m) : ℂ)) =
    ∑ t ∈ closedTraces c m,
      if ((c * s : ℕ) : ℤ) ∣ t then
        tracePolynomial (((t : ℝ) / Real.sqrt c : ℝ) : ℂ) (m : ℂ) r *
          (H ((s : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ)
      else 0 := by
  have heq := sum_quotientTraces_scale c s m hc hs hm
    (fun t => tracePolynomial (((t : ℝ) / Real.sqrt c : ℝ) : ℂ) (m : ℂ) r *
      (H ((s : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ))
  rw [← heq]
  apply Finset.sum_congr rfl
  intro u hu
  rw [discriminant_quotient_scale]
  have hpoly := tracePolynomial_quotient_scale r c s m hc hs u
  push_cast at hpoly ⊢
  rw [hpoly]

/-- The same literal weighted rescaling on the even-u part of a stratum. -/
theorem weighted_quotient_scale_even (r c s m : ℕ) (hc : 0 < c) (hs : 0 < s)
    (hm : 0 < m) (H : ℤ → ℝ) :
    (∑ u ∈ quotientTraces (c * s ^ 2) m,
      if Even u then
        tracePolynomial
          ((((((c * s ^ 2 : ℕ) : ℤ) * u : ℤ) : ℝ) / Real.sqrt ((c * s ^ 2 : ℕ) : ℝ) : ℝ) : ℂ)
          (m : ℂ) r *
        (H ((((c * s ^ 2 : ℕ) : ℤ) * u) ^ 2 -
          4 * ((c * s ^ 2 : ℕ) : ℤ) * m) : ℂ)
      else 0) =
    ∑ t ∈ closedTraces c m,
      if (2 * ((c * s : ℕ) : ℤ)) ∣ t then
        tracePolynomial (((t : ℝ) / Real.sqrt c : ℝ) : ℂ) (m : ℂ) r *
          (H ((s : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ)
      else 0 := by
  have heq := sum_quotientTraces_scale_even c s m hc hs hm
    (fun t => tracePolynomial (((t : ℝ) / Real.sqrt c : ℝ) : ℂ) (m : ℂ) r *
      (H ((s : ℤ) ^ 2 * (t ^ 2 - 4 * c * m)) : ℂ))
  rw [← heq]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs
  · rw [discriminant_quotient_scale]
    have hpoly := tracePolynomial_quotient_scale r c s m hc hs u
    push_cast at hpoly ⊢
    rw [hpoly]
  · rfl


/-- An odd prime occurs to an odd exponent in 2^b*P, so there is no
integer zero-discriminant trace at a prime index. -/
theorem odd_prime_times_two_pow_not_square (b P : ℕ) (hP : P.Prime)
    (hodd : Odd P) (t : ℤ) : t ^ 2 ≠ (2 : ℤ) ^ b * P := by
  intro heq
  have hn : t.natAbs ^ 2 = 2 ^ b * P := by
    have h := congrArg Int.natAbs heq
    simpa only [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast,
      show Int.natAbs (2 : ℤ) = 2 by decide] using h
  have hdiv : P ∣ t.natAbs := hP.dvd_of_dvd_pow (by
    rw [hn]
    exact dvd_mul_left P (2 ^ b))
  obtain ⟨u, hu⟩ := hdiv
  have hcancel : P * (P * u ^ 2) = P * 2 ^ b := by
    rw [hu] at hn
    nlinarith [hn]
  have hpower : P * u ^ 2 = 2 ^ b := Nat.eq_of_mul_eq_mul_left hP.pos hcancel
  have hpdiv : P ∣ 2 ^ b := ⟨u ^ 2, hpower.symm⟩
  exact hP.ne_one ((hodd.coprime_two_right.pow_right b).eq_one_of_dvd hpdiv)

/-- At either common prime interval (c=1 or c=2), the closed trace condition
is already strict. The H(0) convention is therefore not silently discarded. -/
theorem prime_common_interval_strict (b P : ℕ) (hP : P.Prime) (hodd : Odd P) (t : ℤ)
    (ht : t ^ 2 ≤ (2 : ℤ) ^ b * P) : t ^ 2 < (2 : ℤ) ^ b * P :=
  lt_of_le_of_ne ht (odd_prime_times_two_pow_not_square b P hP hodd t)

end DepthAspect.SignedSieve
