import DepthAspect.CoefficientErrorMajorant
import DepthAspect.GlobalSmoothedBounds
import DepthAspect.NegativeDiscriminantSmoothing
import Mathlib.NumberTheory.Chebyshev

/-!
# The literal prime-average smoothing decomposition

This combines the actual negative-discriminant L-value estimate, the proved
residue/Fourier prime discrepancy, and the actual averaged coefficient tail.
No instance of (103) is an assumption. Constants in the two general primitive
character estimates are chosen before t, χ, the interval and the weight.
-/
noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace DepthAspect.PrimeAverageSmoothing
open QuadraticClassFormula QuadraticDiscriminantL GlobalResidueMean
open GlobalCoefficientTail GlobalSmoothedBounds CoefficientPrimeAverages

/-- The literal odd primes in the half-open interval in Theorem 5.5. -/
def primeSet (A B : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter (fun p => p.Prime ∧ p ≠ 2)

def primeWeight (χ : DirichletCharacter ℂ 8) (Φ : ℝ → ℂ) (p : ℕ) : ℂ :=
  Φ p * χ (-(p : ℤ)) * (Real.log p : ℂ)

/-- The sum on the left side of (104), before subtracting its actual mean. -/
def primeLsum {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) (A B : ℝ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ p ∈ primeSet A B, primeWeight χ Φ p * LAtOne G (t ^ 2 - 4 * (p : ℤ))

/-- Every character modulo eight vanishes at the excluded prime two. -/
 theorem character_neg_two (χ : DirichletCharacter ℂ 8) : χ (-(2 : ℤ)) = 0 := by
  apply (χ.apply_eq_zero_iff (-(2 : ℤ))).mpr
  rintro ⟨a, b, h⟩
  omega

/-- With characters represented at the common modulus eight, the canonical
odd-prime sum equals its all-prime extension. This statement uses the principal
character modulo eight, which vanishes at two. The paper already restricts P
to odd primes in Section 1.3; this equality is an additional presentation.
TheoremFiveFiveAllPrimes separately proves a stronger primitive-twist variant. -/
theorem primeLsum_eq_all_primes {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) (A B : ℝ) (Φ : ℝ → ℂ) :
    primeLsum G t χ A B Φ =
      ∑ p ∈ (Finset.Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime,
        Φ p * χ (-(p : ℤ)) * LAtOne G (t ^ 2 - 4 * (p : ℤ)) * (Real.log p : ℂ) := by
  unfold primeLsum primeSet
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hpI
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      have hguard : ¬ ((2 : ℕ).Prime ∧ (2 : ℕ) ≠ 2) := fun h => h.2 rfl
      rw [if_neg hguard, if_pos Nat.prime_two]
      rw [show χ (-((2 : ℕ) : ℤ)) = 0 from character_neg_two χ]
      simp only [mul_zero, zero_mul]
    · rw [if_pos ⟨hp, hp2⟩, if_pos hp]
      unfold primeWeight
      ring
  · rw [if_neg (fun h : p.Prime ∧ p ≠ 2 => hp h.1), if_neg hp]

 theorem primeSet_discriminant {A B : ℝ} (hA : 0 ≤ A) {t : ℤ}
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) {p : ℕ} (hp : p ∈ primeSet A B) :
    IsNegativeDiscriminant (t ^ 2 - 4 * (p : ℤ)) :=
  discriminant_negative hA ht (Finset.mem_filter.mp hp).1

 theorem coefficient_sum_eq {H : ℤ → ℝ} (G : GeneralFormula H) (t : ℤ)
    (χ : DirichletCharacter ℂ 8) (A B : ℝ) (Φ : ℝ → ℂ) (m : ℕ) :
    (∑ p ∈ primeSet A B, primeWeight χ Φ p * psi G (t ^ 2 - 4 * (p : ℤ)) m) =
      weightedPsi G t χ m A B Φ := by
  rw [primeSet, Finset.sum_filter, weightedPsi]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp only [primeWeight] <;> ring

 theorem prime_log_sum_le {A B : ℝ} (hB : 0 ≤ B) :
    (∑ p ∈ primeSet A B, Real.log p) ≤ Real.log 4 * B := by
  apply le_trans _ (Chebyshev.theta_le_log4_mul_x hB)
  rw [Chebyshev.theta_eq_sum_Icc]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hp, _⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le p, (Finset.mem_Ioc.mp hpI).2⟩, hp⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)

 theorem norm_primeWeight_le {A B M : ℝ} (hA : 0 ≤ A) (χ : DirichletCharacter ℂ 8)
    (Φ : ℝ → ℂ) (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M)
    {p : ℕ} (hp : p ∈ primeSet A B) : ‖primeWeight χ Φ p‖ ≤ M * Real.log p := by
  obtain ⟨hpI, hp, hp2⟩ := Finset.mem_filter.mp hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  rw [primeWeight, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog]
  calc
    _ ≤ M * 1 * Real.log p := by
      have hPhi := hM p (Set.Ioc_subset_Icc_self (prime_mem_interval hA hpI))
      have hM0 : 0 ≤ M := (norm_nonneg _).trans hPhi
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hPhi (χ.norm_le_one _) (norm_nonneg _) hM0) hlog
    _ = _ := by ring

 theorem discriminant_abs_le {A B : ℝ} (hA : 0 ≤ A) {t : ℤ}
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) {p : ℕ} (hp : p ∈ primeSet A B) :
    ((t ^ 2 - 4 * (p : ℤ)).natAbs : ℝ) ≤ 4 * B := by
  have hD := primeSet_discriminant hA ht hp
  have habs : (((t ^ 2 - 4 * (p : ℤ)).natAbs : ℕ) : ℝ) =
      -((t ^ 2 - 4 * (p : ℤ) : ℤ) : ℝ) := by
    have hz : ((t ^ 2 - 4 * (p : ℤ)).natAbs : ℤ) =
        -(t ^ 2 - 4 * (p : ℤ)) := by
      rw [Int.natCast_natAbs, abs_of_neg hD.1]
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hz
    simpa only [Int.cast_natCast, Int.cast_neg] using hr
  rw [habs]
  push_cast
  have hpB := (prime_mem_interval hA (Finset.mem_filter.mp hp).1).2
  nlinarith [sq_nonneg (t : ℝ)]

 theorem integral_norm_le {A B M : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hM0 : 0 ≤ M)
    (Φ : ℝ → ℂ) (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    ‖∫ u in A..B, Φ u‖ ≤ M * B := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := A) (b := B) (f := Φ) (C := M)
    (fun u hu => by
      have hu' : u ∈ Set.Ioc A B := by
        simpa only [Set.uIoc_of_le hAB] using hu
      exact hM u ⟨hu'.1.le, hu'.2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hAB)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hM0)

 theorem smoothingConstant_nonneg {η C : ℝ} (hC : 0 ≤ C) :
    0 ≤ NegativeDiscriminantSmoothing.constant η C := by
  unfold NegativeDiscriminantSmoothing.constant
  have := MellinContour.gammaMoment_nonneg (-1 / 2 + η) η
  have := HalfPlaneEulerBound.boundConstant_pos η
  positivity

/-- The first smoothing error, summed over the literal prime set using
Chebyshev's proved theta bound and |t²−4p|≤4B. -/
theorem L_smoothing_sum_bound {H : ℤ → ℝ} (G : GeneralFormula H)
    (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {A B M x η C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) (hM0 : 0 ≤ M) (hx : 1 ≤ x)
    (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hC : 0 ≤ C)
    (Φ : ℝ → ℂ) (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    (∑ p ∈ primeSet A B, ‖primeWeight χ Φ p‖ *
      (NegativeDiscriminantSmoothing.constant η C *
        ((t ^ 2 - 4 * (p : ℤ)).natAbs : ℝ) ^ η * x ^ (-1 / 2 + η))) ≤
      (NegativeDiscriminantSmoothing.constant η C * 4 ^ η * Real.log 4) *
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
        (NegativeDiscriminantSmoothing.constant η C * (4 * B) ^ η * x ^ (-1 / 2 + η)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
        exact_mod_cast (Finset.mem_filter.mp hp).2.1.one_le)
      gcongr
      · exact norm_primeWeight_le hA χ Φ hM hp
      · exact discriminant_abs_le hA ht hp
    _ = (M * ∑ p ∈ primeSet A B, Real.log p) *
        (NegativeDiscriminantSmoothing.constant η C * (4 * B) ^ η * x ^ (-1 / 2 + η)) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (M * (Real.log 4 * B)) *
        (NegativeDiscriminantSmoothing.constant η C * (4 * B) ^ η * x ^ (-1 / 2 + η)) := by
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
    (t : ℤ) (χ : DirichletCharacter ℂ 8)
    {A B M x η δ C₁ C₂ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hB : 2 ≤ B)
    (ht : (t : ℝ) ^ 2 ≤ 4 * A) (hM0 : 0 ≤ M) (hx : 1 ≤ x)
    (hη0 : 0 < η) (hη : η ≤ 1 / 4) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 4)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hprime : PrimitiveGRHTransport.PrimitiveVonMangoldtEstimate C₁)
    (hstrip : ImprimitiveSmoothing.PrimitiveStripEstimate η C₂)
    (Φ : ℝ → ℂ) (hΦ : ContinuousOn Φ (Set.Icc A B))
    (hdΦ : ∀ u ∈ Set.Ioo A B, DifferentiableAt ℝ Φ u)
    (hI : IntegrableOn (deriv Φ) (Set.Icc A B))
    (hM : ∀ u ∈ Set.Icc A B, ‖Φ u‖ ≤ M) :
    ‖primeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u‖ ≤
      (NegativeDiscriminantSmoothing.constant η C₂ * 4 ^ η * Real.log 4) *
        M * B ^ (1 + η) * x ^ (-1 / 2 + η) +
      (CoefficientErrorMajorant.constant δ C₁ * ((4 / δ ^ 2) * 2 ^ δ *
        (1 + Real.Gamma (1 / 2 + δ + δ)))) *
          (M + ∫ u in A..B, ‖deriv Φ u‖) * Real.sqrt B * B ^ δ * x ^ (1 / 2 + δ + δ) +
      M * (Real.log (2 * x) ^ 2 + 1) +
      CoefficientTail.tailConstant / Real.sqrt x * (M * B) := by
  let V : ℝ := ∫ u in A..B, ‖deriv Φ u‖
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg hAB (fun _ _ => norm_nonneg _)
  have hx0 : 0 < x := by linarith
  let a : ℕ → ℕ → ℂ := fun p => psi G (t ^ 2 - 4 * (p : ℤ))
  let U : ℕ → ℝ := fun p => NegativeDiscriminantSmoothing.constant η C₂ *
    ((t ^ 2 - 4 * (p : ℤ)).natAbs : ℝ) ^ η * x ^ (-1 / 2 + η)
  let R : ℕ → ℝ := fun n =>
    CoefficientErrorMajorant.constant δ C₁ * (M + V) * Real.sqrt B *
      ((n + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) * Real.log (2 * B * (n + 1 : ℕ)) ^ 2 +
        M * OmittedPrimeCost.primeCost (n + 1)
  have ha : ∀ p ∈ primeSet A B, Summable (fun n =>
      (FiniteSmoothedAssembly.weight x n : ℂ) * a p (n + 1)) := by
    intro p hp
    exact smoothed_summable _ (norm_psi_le G _) hx0
  have hb := average_smoothed_summable t χ hx0
  have hU : ∀ p ∈ primeSet A B,
      ‖LAtOne G (t ^ 2 - 4 * (p : ℤ)) - FiniteSmoothedAssembly.smoothed x (a p)‖ ≤ U p := by
    intro p hp
    have h := NegativeDiscriminantSmoothing.smoothing_bound G _
      (primeSet_discriminant hA ht hp) hx hη0 hη hC₂ hstrip
    simpa only [FiniteSmoothedAssembly.smoothed, weight_mul_eq_smoothedTerm, a, U] using h
  have hR : ∀ n, ‖FiniteSmoothedAssembly.coefficientError (primeSet A B)
      (primeWeight χ Φ) a (sequence t χ) (∫ u in A..B, Φ u) n‖ ≤ R n := by
    intro n
    letI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    have h := coefficient_error_bound G t χ hA hAB hB ht hM0 hC₁ hprime Φ hΦ hdΦ hI hM
      (m := n + 1)
    have hmaj := CoefficientErrorMajorant.coefficient_majorant (Nat.succ_pos n)
      hδ0 hC₁ hB hM0 hV
    unfold FiniteSmoothedAssembly.coefficientError
    rw [show (∑ p ∈ primeSet A B, primeWeight χ Φ p * a p (n + 1)) =
      weightedPsi G t χ (n + 1) A B Φ from coefficient_sum_eq G t χ A B Φ (n + 1), sequence_eq]
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
    (primeWeight χ Φ) (fun p => LAtOne G (t ^ 2 - 4 * (p : ℤ))) a (sequence t χ)
    (∫ u in A..B, Φ u) x ha hb U hU R hR hRs
  have hfirst := L_smoothing_sum_bound G t χ hA hAB ht hM0 hx hη0 hη hC₂ Φ hM
  have hmiddle := CoefficientErrorMajorant.term_sum_bound hδ0 hδ hC₁ hB hM0 hV hx
  have hbad := mul_le_mul_of_nonneg_left (OmittedPrimeCost.omitted_prime_cost hx).2 hM0
  have htail := average_smoothed_tail t χ hx0
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
  change ‖primeLsum G t χ A B Φ - valueAtOne t χ * ∫ u in A..B, Φ u‖ ≤ _ at hmain
  dsimp [U] at hmain
  dsimp [V] at hmiddle hlast
  exact hmain.trans ((add_le_add
    (add_le_add hfirst (add_le_add hmiddle hbad)) hlast).trans_eq (by ring))

end DepthAspect.PrimeAverageSmoothing
