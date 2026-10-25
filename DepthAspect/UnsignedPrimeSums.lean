import DepthAspect.UnsignedDensity
import DepthAspect.PrimePowerApplications
import DepthAspect.PrimeSumBounds

/-! Exact support truncations for the actual prime and prime-square sums. -/
namespace DepthAspect.UnsignedDensity

open scoped BigOperators

/-- The subset of the prime box compatible with a nonzero square test. -/
noncomputable def squareBases (L s : ℝ) : Finset ℕ :=
  (primeBases L s).filter (fun p => (p : ℝ) ^ 2 ≤ Real.exp (s * L))

theorem primeBases_subset_primesLE (L s : ℝ) :
    primeBases L s ⊆ Nat.primesLE ⌊Real.exp (s * L)⌋₊ := by
  intro p hp
  have hm := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hm.1).2, hm.2.1⟩

theorem squareBases_subset_primesLE (L s : ℝ) :
    squareBases L s ⊆ Nat.primesLE ⌊Real.sqrt (Real.exp (s * L))⌋₊ := by
  intro p hp
  obtain ⟨hp, hsq⟩ := Finset.mem_filter.mp hp
  exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (Real.le_sqrt_of_sq_le hsq),
    (Finset.mem_filter.mp hp).2.1⟩

/-- The actual weighted square sum over the full prime box equals the
square-root truncation, including at support endpoints. -/
theorem square_weightedSum_eq {L s : ℝ} (hL : 0 < L)
    {h : ℝ → ℂ} (hsupp : Function.support h ⊆ Set.Icc (-s) s) (E : ℕ → ℂ) :
    PrimePowerApplications.weightedSum (primeBases L s) (-1) E
        (fun p => h (2 * Real.log p / L)) =
      PrimePowerApplications.weightedSum (squareBases L s) (-1) E
        (fun p => h (2 * Real.log p / L)) := by
  unfold PrimePowerApplications.weightedSum squareBases
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hsq : (p : ℝ) ^ 2 ≤ Real.exp (s * L)
  · simp only [hsq, if_true]
  · have hz : h (2 * Real.log p / L) = 0 := by
      by_contra hn
      have hprime := (Finset.mem_filter.mp hp).2.1
      exact hsq (PrimePowerSupport.supported_prime_power_le hL hsupp
        hprime.pos (j := 2) (by simpa only [Nat.cast_ofNat] using hn))
    simp only [hsq, if_false, hz, norm_zero, mul_zero]

/-- The actual integer-index sum in the elliptic pair estimate is exactly
the natural-prime weighted sum after the injective cast of the index set. -/
theorem prime_weightedSum_eq_int (P : Finset ℕ) (L : ℝ) (E : ℤ → ℂ) (h : ℝ → ℂ) :
    (∑ m ∈ P.image (fun p : ℕ => (p : ℤ)), PrimeSumBounds.weightedTerm L E h m) =
      PrimePowerApplications.weightedSum P (-(1 / 2 : ℝ))
        (fun p => E (p : ℤ)) (fun p => h (Real.log p / L)) := by
  rw [Finset.sum_image (by
    intro p _ q _ hpq
    change (p : ℤ) = (q : ℤ) at hpq
    exact_mod_cast hpq), PrimePowerApplications.weightedSum_neg_half]
  apply Finset.sum_congr rfl
  intro p _
  simp only [PrimeSumBounds.weightedTerm, Int.cast_natCast]

/-- The literal trace decomposition passes to the actual nonnegative
weighted norms, so the elliptic and cusp estimates can be added directly. -/
theorem weightedSum_decomposition (P : Finset ℕ) (v : ℝ) (A E C w : ℕ → ℂ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hA : ∀ p ∈ P, A p = E p + C p) :
    PrimePowerApplications.weightedSum P v A w ≤
      PrimePowerApplications.weightedSum P v E w +
        PrimePowerApplications.weightedSum P v C w := by
  unfold PrimePowerApplications.weightedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ Real.log p * (p : ℝ) ^ v := by
    apply mul_nonneg (Real.log_nonneg (by exact_mod_cast hP p hp))
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ Real.log p * (p : ℝ) ^ v * (‖E p‖ + ‖C p‖) * ‖w p‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hw
      rw [hA p hp]
      exact norm_add_le _ _
    _ = _ := by ring

/-- The scalar, elliptic, and cusp pieces of a square-index trace are all
retained in the literal finite weighted sum. -/
theorem weightedSum_three_decomposition (P : Finset ℕ) (v : ℝ)
    (A S E C w : ℕ → ℂ) (hP : ∀ p ∈ P, 1 ≤ p)
    (hA : ∀ p ∈ P, A p = S p + E p + C p) :
    PrimePowerApplications.weightedSum P v A w ≤
      PrimePowerApplications.weightedSum P v S w +
        PrimePowerApplications.weightedSum P v E w +
          PrimePowerApplications.weightedSum P v C w := by
  have h₁ := weightedSum_decomposition P v A (fun p => S p + E p) C w hP hA
  have h₂ := weightedSum_decomposition P v (fun p => S p + E p) S E w hP (fun _ _ => rfl)
  exact h₁.trans (add_le_add h₂ le_rfl)

/-- The logarithmic endpoints used by (45), (46), (48), and (49) are exact. -/
theorem support_endpoint_log (L s : ℝ) :
    Real.log (Real.exp (s * L)) = s * L := Real.log_exp _

theorem square_endpoint_log (L s : ℝ) :
    Real.log (Real.sqrt (Real.exp (s * L))) = (s / 2) * L := by
  rw [Real.log_sqrt (Real.exp_pos _).le, Real.log_exp]
  ring

end DepthAspect.UnsignedDensity
