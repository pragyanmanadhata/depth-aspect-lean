import DepthAspect.SignedSpectralSummation
import DepthAspect.SignedHyperbolicBound

/-! The exact spectral decomposition and actual weighted (114). -/
namespace DepthAspect.SignedDensity
open SignedSieve UnsignedDensity PrimePowerApplications
open scoped BigOperators SchwartzMap

variable {k : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

noncomputable def hyperbolicPrimeSum (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (L s : ℝ) (h : 𝓢(ℝ, ℂ)) : ℂ :=
  ∑ P ∈ primeBases L s, ((Real.log (P : ℝ) / Real.sqrt P : ℝ) : ℂ) *
    ((-1 : ℂ) ^ (k + 1) * normalizedHyperbolic (2 * k) n
      (Fintype.card (Family (2 ^ n)) : ℝ) P) * h (Real.log (P : ℝ) / L)

/-- The actual prime-support set contains only the interval (2,exp(sL)]. -/
theorem primeBases_filter_full (L s : ℝ) :
    (primeBases L s).filter (fun P : ℕ => (2 : ℝ) < P ∧ (P : ℝ) ≤ Real.exp (s * L)) =
      primeBases L s := by
  classical
  apply Finset.filter_eq_self.mpr
  intro P hP
  obtain ⟨hPI, hprime, hne⟩ := Finset.mem_filter.mp hP
  have h3 : 3 ≤ P := by have := hprime.two_le; omega
  refine ⟨by exact_mod_cast (show 2 < P by omega), ?_⟩
  exact (Nat.le_floor_iff' hprime.ne_zero).mp (Finset.mem_Icc.mp hPI).2

theorem prime_hyperbolic_weight_identity (S : SignedArithmeticData k Family Full New)
    (n P : ℕ) (hP : 0 < P) :
    ((Real.log (P : ℝ) / P : ℝ) : ℂ) * primeHyperbolicTrace k n P /
        (Fintype.card (Family (2 ^ n)) : ℂ) =
      ((Real.log (P : ℝ) / Real.sqrt P : ℝ) : ℂ) *
        ((-1 : ℂ) ^ (k + 1) * normalizedHyperbolic (2 * k) n
          (Fintype.card (Family (2 ^ n)) : ℝ) P) := by
  have hpR : (0 : ℝ) < P := by exact_mod_cast hP
  have hs : (Real.sqrt P : ℂ) ^ 2 = (P : ℂ) := by exact_mod_cast Real.sq_sqrt hpR.le
  have hs0 : (Real.sqrt P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpR).ne'
  have he : (((2 * k : ℕ) : ℝ) + 1) / 2 = (k : ℝ) + 1 / 2 := by push_cast; ring
  unfold primeHyperbolicTrace normalizedHyperbolic
  rw [he]
  push_cast
  rw [← hs]
  field_simp [hs0] <;> ring

/-- The finite signed prime sum is exactly its elliptic block plus the
literal hyperbolic term, with no bound or trace identity assumed. -/
theorem signedPrimeContribution_eq_elliptic_add_hyperbolic
    (S : SignedArithmeticData k Family Full New) (n : ℕ) (L s : ℝ)
    (h : 𝓢(ℝ, ℂ)) :
    signedPrimeContribution (fun f => (S.rootNumber (2 ^ n) f : ℂ)) L h
      (S.unsigned.eigenvalues (2 ^ n)) (primeBases L s) =
      ellipticPrimeBlock S n L s 2 (Real.exp (s * L)) h + hyperbolicPrimeSum S n L s h := by
  rw [signedPrimeContribution_eq_traceSum S n L h (primeBases L s)
    (fun P hP => (Finset.mem_filter.mp hP).2.1.pos)]
  unfold ellipticPrimeBlock hyperbolicPrimeSum
  rw [primeBases_filter_full, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  rw [← prime_hyperbolic_weight_identity S n P (Finset.mem_filter.mp hP).2.1.pos]
  unfold ellipticPrimeTrace
  ring

/-- Actual equation (114), with an explicit constant independent of the
spectral family and the depth. -/
theorem hyperbolicPrimeSum_bound (S : SignedArithmeticData k Family Full New)
    (n : ℕ) (hn : 7 ≤ n) {L s : ℝ} (hL : 1 ≤ L) (hs : 0 ≤ s)
    (h : 𝓢(ℝ, ℂ)) :
    ‖((2 / L : ℝ) : ℂ) * hyperbolicPrimeSum S n L s h‖ ≤
      2 * (256 / (2 * (k : ℝ) + 1)) * ‖h.toBoundedContinuousFunction‖ *
        Real.log 4 * (1 + s) * ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hX : 1 ≤ Real.exp (s * L) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hs hL0.le)
  have hd := signed_dimension_lower S n hn
  have hb := normalizedHyperbolic_prime_sum_bound (2 * k) n (k + 1)
    hX hL (norm_nonneg _) hs (le_of_eq (Real.log_exp _))
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd)
    (primeBases L s) (primeBases_subset_primesLE L s)
    (fun P => h (Real.log (P : ℝ) / L))
    (fun P _ => h.toBoundedContinuousFunction.norm_coe_le_norm _)
  have hsum : ‖hyperbolicPrimeSum S n L s h‖ ≤
      weightedSum (primeBases L s) (-(1 / 2 : ℝ))
        (fun P => (-1 : ℂ) ^ (k + 1) * normalizedHyperbolic (2 * k) n
          (Fintype.card (Family (2 ^ n)) : ℝ) P)
        (fun P => h (Real.log (P : ℝ) / L)) := by
    rw [weightedSum_neg_half]
    unfold hyperbolicPrimeSum
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro P hP
    have hprime := (Finset.mem_filter.mp hP).2.1
    have hlog : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hlog (Real.sqrt_nonneg _))]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb)

end DepthAspect.SignedDensity
