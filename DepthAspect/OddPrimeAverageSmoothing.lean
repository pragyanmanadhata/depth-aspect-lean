import DepthAspect.PrimeAverageSmoothing
import DepthAspect.OddSmoothedBounds

/-! The actual smoothing decomposition for the odd-depth discriminant
t²−8p. The coefficient sequence, its Fourier bound and its main value are
derived from the odd-modulus arithmetic; only general primitive-character
estimates enter as analytic inputs. -/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace DepthAspect.OddPrimeAverageSmoothing
open QuadraticClassFormula QuadraticDiscriminantL
open OddDepthCoefficientAverages OddSmoothedBounds
open GlobalSmoothedBounds (smoothed_summable weight_mul_eq_smoothedTerm)
open CoefficientPrimeAverages (prime_mem_interval norm_psi_le)
open PrimeAverageSmoothing (primeSet prime_log_sum_le integral_norm_le smoothingConstant_nonneg)

def primeWeight (Φ : ℝ → ℂ) (p : ℕ) : ℂ :=
  Φ p * (Real.log p : ℂ)

/-- The sum on the left side of (105), before subtracting its actual mean. -/
def primeLsum {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ p ∈ primeSet A B, primeWeight Φ p * LAtOne G (t ^ 2 - 8 * (p : ℤ))

/-- Under the printed lower endpoint restriction every counted prime is
odd, so the canonical odd-prime set is the complete prime interval. -/
theorem primeSet_eq_all_primes {A B : ℝ} (hA : 2 ≤ A) :
    primeSet A B = (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime := by
  ext p
  simp only [primeSet, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hpprime, _⟩
    exact ⟨hp, hpprime⟩
  · rintro ⟨hp, hpprime⟩
    refine ⟨hp, hpprime, ?_⟩
    have hAp := (prime_mem_interval (by linarith : 0 ≤ A) hp).1
    intro hp2
    subst p
    norm_num at hAp
    linarith

 theorem primeSet_discriminant {A B : ℝ} (hA : 0 ≤ A) {t : ℤ}
    (ht : (t : ℝ) ^ 2 ≤ 8 * A) {p : ℕ} (hp : p ∈ primeSet A B) :
    IsNegativeDiscriminant (t ^ 2 - 8 * (p : ℤ)) :=
  discriminant_negative hA ht (Finset.mem_filter.mp hp).1

 theorem coefficient_sum_eq {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (A B : ℝ) (Φ : ℝ → ℂ) (m : ℕ) :
    (∑ p ∈ primeSet A B, primeWeight Φ p * psi G (t ^ 2 - 8 * (p : ℤ)) m) =
      ResiduePrimeRestoration.weightedOdd (fun p => psi G (t ^ 2 - 8 * (p : ℤ)) m) A B Φ := by
  rw [primeSet, Finset.sum_filter, ResiduePrimeRestoration.weightedOdd]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp only [primeWeight] <;> ring

 theorem norm_primeWeight_le {A B M : ℝ} (hA : 0 ≤ A)
    (Φ : ℝ → ℂ) (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M)
    {p : ℕ} (hp : p ∈ primeSet A B) : ‖primeWeight Φ p‖ ≤ M * Real.log p := by
  obtain ⟨hpI, hp, _⟩ := Finset.mem_filter.mp hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  rw [primeWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact mul_le_mul_of_nonneg_right
    (hM p (Set.Ioc_subset_Icc_self (prime_mem_interval hA hpI))) hlog

 theorem discriminant_abs_le {A B : ℝ} (hA : 0 ≤ A) {t : ℤ}
    (ht : (t : ℝ) ^ 2 ≤ 8 * A) {p : ℕ} (hp : p ∈ primeSet A B) :
    ((t ^ 2 - 8 * (p : ℤ)).natAbs : ℝ) ≤ 8 * B := by
  have hD := primeSet_discriminant hA ht hp
  have habs : (((t ^ 2 - 8 * (p : ℤ)).natAbs : ℕ) : ℝ) =
      -((t ^ 2 - 8 * (p : ℤ) : ℤ) : ℝ) := by
    have hz : ((t ^ 2 - 8 * (p : ℤ)).natAbs : ℤ) =
        -(t ^ 2 - 8 * (p : ℤ)) := by
      rw [Int.natCast_natAbs, abs_of_neg hD.1]
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
    simpa only [Int.cast_natCast, Int.cast_neg] using hr
  rw [habs]
  push_cast
  have hpB := (prime_mem_interval hA (Finset.mem_filter.mp hp).1).2
  nlinarith [sq_nonneg (t : ℝ)]

/-- The first smoothing error, summed over the literal prime set using
Chebyshev's proved theta bound and |t²−8p|≤8B. -/
theorem L_smoothing_sum_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (t : ℤ)
    {A B M x η C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 8 * A) (hM0 : 0 ≤ M) (hx : 1 ≤ x)
    (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hC : 0 ≤ C)
    (Φ : ℝ → ℂ) (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    (∑ p ∈ primeSet A B, ‖primeWeight Φ p‖ *
      (NegativeDiscriminantSmoothing.constant η C *
        ((t ^ 2 - 8 * (p : ℤ)).natAbs : ℝ) ^ η * x ^ (-1 / 2 + η))) ≤
      (NegativeDiscriminantSmoothing.constant η C * 8 ^ η * Real.log 4) *
        M * B ^ (1 + η) * x ^ (-1 / 2 + η) := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hBzero : B = 0
  · have hAzero : A = 0 := by linarith
    subst A
    subst B
    simp [primeSet, Real.zero_rpow (by linarith : 1 + η ≠ 0)]
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
  have hK := smoothingConstant_nonneg (η := η) hC
  calc
    _ ≤ ∑ p ∈ primeSet A B, (M * Real.log p) *
        (NegativeDiscriminantSmoothing.constant η C * (8 * B) ^ η * x ^ (-1 / 2 + η)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg
        (by exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
      gcongr
      · exact norm_primeWeight_le hA Φ hM hp
      · exact discriminant_abs_le hA ht hp
    _ = (M * ∑ p ∈ primeSet A B, Real.log p) *
        (NegativeDiscriminantSmoothing.constant η C * (8 * B) ^ η * x ^ (-1 / 2 + η)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (M * (Real.log 4 * B)) *
        (NegativeDiscriminantSmoothing.constant η C * (8 * B) ^ η * x ^ (-1 / 2 + η)) := by
      gcongr
      exact prime_log_sum_le hB
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) hB, Real.rpow_add hBpos]
      simp only [Real.rpow_one]
      ring

/-- The complete three-error estimate behind (103), with explicit constants
and the lower-order omitted-prime/tail terms still displayed. The only
estimate premises are uniform, general primitive-character consequences. -/
theorem raw_smoothing_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (t : ℤ) (ht8 : 8 ∣ t)
    {A B M x η δ C₁ C₂ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 2 ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 8 * A) (hM0 : 0 ≤ M) (hx : 1 ≤ x)
    (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hprime : PrimitiveGRHTransport.PrimitiveVonMangoldtEstimate C₁)
    (hstrip : ImprimitiveSmoothing.PrimitiveStripEstimate η C₂)
    (Φ : ℝ → ℂ) (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    ‖primeLsum G t A B Φ - valueAtOne t * ∫ u in A..B, Φ u‖ ≤
      (NegativeDiscriminantSmoothing.constant η C₂ * 8 ^ η * Real.log 4) *
        M * B ^ (1 + η) * x ^ (-1 / 2 + η) +
      (CoefficientErrorMajorant.constant δ C₁ * ((4 / δ ^ 2) * 2 ^ δ *
        (1 + Real.Gamma (1 / 2 + δ + δ)))) *
          (M + ∫ u in A..B, ‖deriv Φ u‖) * Real.sqrt B * B ^ δ * x ^ (1 / 2 + δ + δ) +
      M * (Real.log (2 * x) ^ 2 + 1) +
      CoefficientTail.tailConstant / Real.sqrt x * (M * B) := by
  let V : ℝ := ∫ u in A..B, ‖deriv Φ u‖
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have hx0 : 0 < x := by linarith
  let a : ℕ → ℕ → ℂ := fun p => psi G (t ^ 2 - 8 * (p : ℤ))
  let U : ℕ → ℝ := fun p => NegativeDiscriminantSmoothing.constant η C₂ *
    ((t ^ 2 - 8 * (p : ℤ)).natAbs : ℝ) ^ η * x ^ (-1 / 2 + η)
  let R : ℕ → ℝ := fun n =>
    CoefficientErrorMajorant.constant δ C₁ * (M + V) * Real.sqrt B *
      ((n + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) * Real.log (2 * B * (n + 1 : ℕ)) ^ 2 +
        M * OmittedPrimeCost.primeCost (n + 1)
  have ha : ∀ p ∈ primeSet A B, Summable (fun n =>
      (FiniteSmoothedAssembly.weight x n : ℂ) * a p (n + 1)) := by
    intro p hp
    exact smoothed_summable _ (norm_psi_le G _) hx0
  have hb := average_smoothed_summable t hx0
  have hU : ∀ p ∈ primeSet A B,
      ‖LAtOne G (t ^ 2 - 8 * (p : ℤ)) - FiniteSmoothedAssembly.smoothed x (a p)‖ ≤ U p := by
    intro p hp
    have h := NegativeDiscriminantSmoothing.smoothing_bound G _
      (primeSet_discriminant hA ht hp) hx hη0 hη hC₂ hstrip
    simpa only [FiniteSmoothedAssembly.smoothed, weight_mul_eq_smoothedTerm, a, U] using h
  have hR : ∀ n, ‖FiniteSmoothedAssembly.coefficientError (primeSet A B)
      (primeWeight Φ) a (OddAverageEuler.coefficient t) (∫ u in A..B, Φ u) n‖ ≤ R n := by
    intro n
    letI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    have h := OddDepthCoefficientAverages.coefficient_error_bound G ht8 hA hAB hB ht hM0 hC₁ hprime Φ hΦ hdΦ hI hM
      (m := n + 1)
    have hmaj := CoefficientErrorMajorant.coefficient_majorant (Nat.succ_pos n)
      hδ0 hC₁ hB hM0 hV
    unfold FiniteSmoothedAssembly.coefficientError
    rw [show (∑ p ∈ primeSet A B, primeWeight Φ p * a p (n + 1)) =
      ResiduePrimeRestoration.weightedOdd (fun p => psi G (t ^ 2 - 8 * (p : ℤ)) (n + 1)) A B Φ from coefficient_sum_eq G t A B Φ (n + 1)]
    exact h.trans (add_le_add hmaj (le_refl _))
  have hRs : Summable (fun n => FiniteSmoothedAssembly.weight x n * R n) := by
    have h₁ := CoefficientErrorMajorant.term_summable (C := C₁) (M := M) (V := V) hδ0 hδ hB hx0
    have h₂ := (OmittedPrimeCost.omitted_prime_cost hx).1.mul_left M
    apply (h₁.add h₂).congr
    intro n
    unfold R CoefficientErrorMajorant.term FiniteSmoothedAssembly.weight
    push_cast
    ring
  have hmain := FiniteSmoothedAssembly.discrepancy_norm_le (primeSet A B)
    (primeWeight Φ) (fun p => LAtOne G (t ^ 2 - 8 * (p : ℤ))) a (OddAverageEuler.coefficient t)
    (∫ u in A..B, Φ u) x ha hb U hU R hR hRs
  have hfirst := L_smoothing_sum_bound G t hA hAB ht hM0 hx hη0 hη hC₂ Φ hM
  have hmiddle := CoefficientErrorMajorant.term_sum_bound hδ0 hδ hC₁ hB hM0 hV hx
  have hbad := mul_le_mul_of_nonneg_left (OmittedPrimeCost.omitted_prime_cost hx).2 hM0
  have htail := average_smoothed_tail t hx0
  have htail0 : 0 ≤ CoefficientTail.tailConstant / Real.sqrt x := (norm_nonneg _).trans htail
  have hlast := mul_le_mul htail (integral_norm_le hA hAB hM0 Φ hM)
    (norm_nonneg _) htail0
  have hsum : (∑' n, FiniteSmoothedAssembly.weight x n * R n) =
      (∑' n, CoefficientErrorMajorant.term δ C₁ B M V x n) +
      M * (∑' n : ℕ, Real.exp (-((n : ℝ) + 1) / x) /
        ((n : ℝ) + 1) * OmittedPrimeCost.primeCost (n + 1)) := by
    rw [← tsum_mul_left,
      ← (CoefficientErrorMajorant.term_summable hδ0 hδ hB hx0).tsum_add
        ((OmittedPrimeCost.omitted_prime_cost hx).1.mul_left M)]
    apply tsum_congr
    intro n
    unfold R CoefficientErrorMajorant.term FiniteSmoothedAssembly.weight
    push_cast
    ring
  rw [hsum] at hmain
  change ‖primeLsum G t A B Φ - valueAtOne t * ∫ u in A..B, Φ u‖ ≤ _ at hmain
  dsimp [U] at hmain
  dsimp [V] at hmiddle hlast
  exact hmain.trans ((add_le_add
    (add_le_add hfirst (add_le_add hmiddle hbad)) hlast).trans_eq (by ring))

end DepthAspect.OddPrimeAverageSmoothing
