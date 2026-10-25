import DepthAspect.ImprimitiveLSeries
import DepthAspect.EulerFactorBounds

open scoped BigOperators
namespace DepthAspect.HalfPlaneEulerBound

open ImprimitiveLSeries

noncomputable def primeFactor (p : ℝ) : ℝ := 1 + 2 / (Real.sqrt p - 1)
noncomputable def threshold (η : ℝ) : ℝ := max 4 ((3 : ℝ) ^ η⁻¹)
noncomputable def smallPrimes (η : ℝ) : Finset ℕ := ⌈threshold η⌉₊.primesBelow
noncomputable def boundConstant (η : ℝ) : ℝ :=
  ∏ p ∈ smallPrimes η, primeFactor (p : ℝ)

private theorem sqrt_gt_one {p : ℝ} (hp : 1 < p) : 1 < Real.sqrt p := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ p)
  have hn := Real.sqrt_nonneg p
  nlinarith

theorem primeFactor_one_le {p : ℝ} (hp : 1 < p) : 1 ≤ primeFactor p := by
  unfold primeFactor
  have hs := sqrt_gt_one hp
  have : 0 ≤ 2 / (Real.sqrt p - 1) := by positivity
  linarith

theorem mem_smallPrimes_iff (η : ℝ) (p : ℕ) :
    p ∈ smallPrimes η ↔ p.Prime ∧ (p : ℝ) < threshold η := by
  simp only [smallPrimes, Nat.mem_primesBelow, Nat.lt_ceil, and_comm]

theorem boundConstant_pos (η : ℝ) : 0 < boundConstant η := by
  apply Finset.prod_pos
  intro p hp
  exact zero_lt_one.trans_le (primeFactor_one_le (by
    exact_mod_cast ((mem_smallPrimes_iff η p).mp hp).1.one_lt))

/-- A geometric polynomial with an actual bounded ratio has the exact local
majorant used in (101). The conductor exponent is arbitrary. -/
theorem norm_polynomial_le (c x : ℂ) (hc : ‖c‖ ≤ 1) {r : ℝ} (hr : 1 < r)
    (hx : ‖x‖ ≤ r⁻¹) (e : ℕ) :
    ‖1 + (1 - c) * ∑ j ∈ Finset.range e, x ^ (j + 1)‖ ≤ 1 + 2 / (r - 1) := by
  have hn : ‖∑ j ∈ Finset.range e, x ^ (j + 1)‖ ≤ 1 / (r - 1) := by
    calc
      _ ≤ ∑ j ∈ Finset.range e, ‖x ^ (j + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range e, r⁻¹ ^ (j + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hx _
      _ ≤ _ := EulerFactorBounds.inverse_power_sum_le hr e
  have hsub : ‖1 - c‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ 2 := by norm_num only [norm_one]; linarith
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖(1 - c) * ∑ j ∈ Finset.range e, x ^ (j + 1)‖ := norm_add_le _ _
    _ ≤ 1 + 2 * (1 / (r - 1)) := by
      rw [norm_one, norm_mul]
      exact add_le_add (le_refl (1 : ℝ))
        (mul_le_mul hsub hn (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- The actual complex exponent in the Euler correction is controlled on
the closed half-plane Re(s)≥1/2, including its boundary. -/
theorem norm_correction_le {q p : ℕ} (χ : DirichletCharacter ℂ q) (f : ℕ)
    (hp : p.Prime) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖correction χ f p s‖ ≤ primeFactor (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hx : ‖(p : ℂ) ^ (-s)‖ ≤ (Real.sqrt (p : ℝ))⁻¹ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
    calc
      (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
      _ = _ := by rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow]
  exact norm_polynomial_le _ _ (χ.norm_le_one _) (sqrt_gt_one hp1) hx _

/-- A sufficient explicit cutoff: the local majorant is at most 3, while
p^η is at least 3. Thus no asymptotic size assertion is a premise. -/
theorem primeFactor_le_rpow {η p : ℝ} (hη : 0 < η) (hp : threshold η ≤ p) :
    primeFactor p ≤ p ^ η := by
  have hp4 : 4 ≤ p := (le_max_left _ _).trans hp
  have hp0 : 0 < p := by linarith
  have hs : 2 ≤ Real.sqrt p := by
    have hsq := Real.sq_sqrt hp0.le
    have hn := Real.sqrt_nonneg p
    nlinarith
  have hb : primeFactor p ≤ 3 := by
    unfold primeFactor
    have hden : 0 < Real.sqrt p - 1 := by linarith
    have hfrac : 2 / (Real.sqrt p - 1) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
    linarith
  have hpη : (3 : ℝ) ≤ p ^ η := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      ((le_max_right _ _).trans hp) hη.le
    simpa only [Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 3) hη.ne'] using h
  exact hb.trans hpη

/-- The finite Euler-product bound in equation (101), for the literal
correctionProduct and a constant depending only on η. -/
theorem correctionProduct_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) (hf : 0 < f) {s : ℂ} (hs : 1 / 2 ≤ s.re) {η : ℝ} (hη : 0 < η) :
    ‖correctionProduct χ f s‖ ≤ boundConstant η * (f : ℝ) ^ η := by
  classical
  let S := f.primeFactors.filter (fun p : ℕ => (p : ℝ) < threshold η)
  have hprime (p : ℕ) (hp : p ∈ f.primeFactors) : (1 : ℝ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hloc (p : ℕ) (hp : p ∈ f.primeFactors) :
      ‖correction χ f p s‖ ≤
        (if (p : ℝ) < threshold η then primeFactor (p : ℝ) else 1) * (p : ℝ) ^ η := by
    have hb := norm_correction_le χ f (Nat.prime_of_mem_primeFactors hp) hs
    split_ifs with hsmall
    · exact hb.trans (le_mul_of_one_le_right
        (zero_le_one.trans (primeFactor_one_le (hprime p hp)))
        (Real.one_le_rpow (hprime p hp).le hη.le))
    · simpa only [one_mul] using hb.trans (primeFactor_le_rpow hη (le_of_not_gt hsmall))
  have hS : S ⊆ smallPrimes η := by
    intro p hp
    obtain ⟨hpf, hpt⟩ := Finset.mem_filter.mp hp
    exact (mem_smallPrimes_iff η p).mpr ⟨Nat.prime_of_mem_primeFactors hpf, hpt⟩
  have hbA : (∏ p ∈ S, primeFactor (p : ℝ)) ≤ boundConstant η := by
    apply Finset.prod_le_prod_of_subset_of_one_le hS
    · intro p hp
      exact zero_le_one.trans (primeFactor_one_le (hprime p (Finset.mem_filter.mp hp).1))
    · intro p hp _
      exact primeFactor_one_le (by exact_mod_cast ((mem_smallPrimes_iff η p).mp hp).1.one_lt)
  have hrad : (∏ p ∈ f.primeFactors, (p : ℝ)) ≤ (f : ℝ) := by
    have hnat := Nat.le_of_dvd hf (Nat.prod_primeFactors_dvd f)
    have hcast : ((∏ p ∈ f.primeFactors, p : ℕ) : ℝ) ≤ (f : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_prod] using hcast
  have hrpow : (∏ p ∈ f.primeFactors, (p : ℝ) ^ η) ≤ (f : ℝ) ^ η := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
    exact Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) hrad hη.le
  unfold correctionProduct
  calc
    _ = ∏ p ∈ f.primeFactors, ‖correction χ f p s‖ := norm_prod _ _
    _ ≤ ∏ p ∈ f.primeFactors,
        (if (p : ℝ) < threshold η then primeFactor (p : ℝ) else 1) * (p : ℝ) ^ η :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) hloc
    _ = (∏ p ∈ S, primeFactor (p : ℝ)) * (∏ p ∈ f.primeFactors, (p : ℝ) ^ η) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
    _ ≤ boundConstant η * (f : ℝ) ^ η := mul_le_mul hbA hrpow
      (Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) η))
      (boundConstant_pos η).le

/-- Combining the proved finite correction with a supplied primitive
Dirichlet bound gives the discriminant form used in the contour shift.
`hprimitive` is precisely the cited GRH consequence (100), not an assumed
bound on the imprimitive function being studied. -/
theorem continuation_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (f : ℕ) (hf : 0 < f)
    {s : ℂ} (hs : 1 / 2 ≤ s.re) {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hprimitive : ‖DirichletCharacter.LFunction χ s‖ ≤
      C * ((q : ℝ) * (2 + |s.im|)) ^ η) :
    ‖continuationCandidate χ f s‖ ≤
      (C * boundConstant η) * ((q : ℝ) * (f : ℝ) ^ 2) ^ η *
        (2 + |s.im|) ^ η := by
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hT : 0 ≤ 2 + |s.im| := by positivity
  have hqf : (q : ℝ) * (f : ℝ) ≤ (q : ℝ) * (f : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hqR
  have hp : ((q : ℝ) * (f : ℝ)) ^ η ≤ ((q : ℝ) * (f : ℝ) ^ 2) ^ η :=
    Real.rpow_le_rpow (by positivity) hqf hη.le
  calc
    _ = ‖DirichletCharacter.LFunction χ s‖ * ‖correctionProduct χ f s‖ :=
      norm_mul _ _
    _ ≤ (C * ((q : ℝ) * (2 + |s.im|)) ^ η) *
        (boundConstant η * (f : ℝ) ^ η) :=
      mul_le_mul hprimitive (correctionProduct_bound χ f hf hs hη)
        (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (mul_nonneg hqR hT) _))
    _ = (C * boundConstant η) * ((q : ℝ) * (f : ℝ)) ^ η *
        (2 + |s.im|) ^ η := by
      rw [Real.mul_rpow hqR hT, Real.mul_rpow hqR (Nat.cast_nonneg f)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (boundConstant_pos η).le))
      (Real.rpow_nonneg hT _)

end DepthAspect.HalfPlaneEulerBound
