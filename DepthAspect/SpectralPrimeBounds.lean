import DepthAspect.UnsignedPrimeSums
import DepthAspect.TracePrimeApplications
import DepthAspect.TraceSquareApplications
import DepthAspect.CuspPrimeApplications
import DepthAspect.PopaTrace

/-!
# Actual spectral Hecke sums from the proved literal trace estimates

The exact mean-trace identity is an explicitly named intermediate, derived
by `PopaTrace.heckeAverage_canonical_from_general_inputs`. This module supplies
no pointwise Hecke or prime-average size estimate as an input.
-/
namespace DepthAspect.UnsignedDensity

open SpectralFamily TraceBounds TracePrimeApplications PrimePowerApplications
open scoped BigOperators

theorem spectral_prime_sum_bound {ι : Type*} [Fintype ι]
    (eigenvalues : ι → ℕ → ℂ) (k n : ℕ) (hn : 4 ≤ n)
    {L s δ Ccl H : ℝ} (hL : 1 ≤ L) (hs : 0 ≤ s) (hδ : 0 < δ)
    (hC : 0 ≤ Ccl) (hH : 0 ≤ H)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ (Fintype.card ι : ℝ))
    (h₀ Hurwitz : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      Hurwitz D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hHgrowth : ∀ D : ℤ, D < 0 → Hurwitz D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (F : ℤ → ℤ → ℕ → ContentDatum) (h : ℝ → ℂ)
    (hF : ∀ p ∈ primeBases L s, ∀ t : ℤ, t ^ 2 < 4 * (p : ℤ) →
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * (p : ℤ)),
        h₀ ((t ^ 2 - 4 * (p : ℤ)) / (u : ℤ) ^ 2) ≠ 0 →
        IsPrimitiveContentMatrix u (t ^ 2 - 4 * (p : ℤ)) (F p t u))
    (hh : ∀ x, ‖h x‖ ≤ H)
    (htrace : ∀ p ∈ primeBases L s, heckeAverage eigenvalues p =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card ι : ℝ)) *
        (p : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator p : ℝ) : ℂ) +
      literalElliptic k n (Fintype.card ι : ℝ) (p : ℤ) h₀ (F p) +
      (normalizedCusp k n (Fintype.card ι : ℝ) (p : ℝ) p.divisorsAntidiagonal : ℂ)) :
    (2 / L) * weightedSum (primeBases L s) (-(1 / 2 : ℝ)) (heckeAverage eigenvalues)
        (fun p => h (Real.log p / L)) ≤
      (96 * s * ellipticConstant Ccl δ * Real.sqrt 2 /
        (1 - (2 : ℝ) ^ (-1 - δ))) * H *
        ((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 + δ) +
      2 * (576 / ((k : ℝ) + 1)) * H * Real.log 4 * (1 + s) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  let P := primeBases L s
  let E : ℤ → ℂ := fun m => literalElliptic k n (Fintype.card ι : ℝ) m h₀ (F m)
  let C : ℕ → ℂ := fun p =>
    (normalizedCusp k n (Fintype.card ι : ℝ) p p.divisorsAntidiagonal : ℂ)
  let w : ℕ → ℂ := fun p => h (Real.log p / L)
  have hL0 : 0 < L := by linarith
  have hX : 1 ≤ Real.exp (s * L) := Real.one_le_exp_iff.mpr (mul_nonneg hs hL0.le)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (Finset.mem_filter.mp hp).2.1
  have hdec : ∀ p ∈ P, heckeAverage eigenvalues p = E p + C p := by
    intro p hp
    have ht := htrace p hp
    simpa only [PopaTrace.squareIndicator_prime (hP p hp), mul_zero,
      Complex.ofReal_zero, zero_add, E, C] using ht
  have hsum := weightedSum_decomposition P (-(1 / 2 : ℝ))
    (heckeAverage eigenvalues) (fun p => E p) C w
    (fun p hp => (hP p hp).one_le) hdec
  have hEI := literalElliptic_prime_sum_bound k n hn hX hL0 hδ hC hs hH
    (le_of_eq (Real.log_exp _)) hd h₀ Hurwitz h₀nonneg hidentity hHgrowth
    (P.image (fun p : ℕ => (p : ℤ))) F h
    (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      have hupper := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      constructor
      · exact_mod_cast (hP p hp).one_le
      · simpa only [Int.cast_natCast] using (Nat.le_floor_iff (Real.exp_pos _).le).mp hupper)
    (by
      intro m hm
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      exact hF p hp)
    (fun _ _ => hh _)
  rw [prime_weightedSum_eq_int] at hEI
  have hCI := normalizedCusp_prime_sum_bound k n hX hL hH hs
    (le_of_eq (Real.log_exp _)) hd P (primeBases_subset_primesLE L s) w
    (fun _ _ => hh _)
  have ht := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 / L)
  rw [mul_add] at ht
  exact ht.trans (add_le_add hEI hCI)

/-- The actual prime-square Hecke sum, including its scalar, elliptic, and
cusp components, after the proved support truncation to `p ≤ sqrt(X)`. -/
theorem spectral_square_sum_bound {ι : Type*} [Fintype ι]
    (eigenvalues : ι → ℕ → ℂ) (k n : ℕ) (hn : 4 ≤ n)
    {L s δ Ccl H : ℝ} (hL : 1 ≤ L) (hs : 0 ≤ s) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hC : 0 ≤ Ccl) (hH : 0 ≤ H)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ (Fintype.card ι : ℝ))
    (h₀ Hurwitz : ℤ → ℝ) (h₀nonneg : ∀ D : ℤ, D < 0 → 0 ≤ h₀ D)
    (hidentity : ∀ D : ℤ, D < 0 →
      Hurwitz D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (hHgrowth : ∀ D : ℤ, D < 0 → Hurwitz D ≤ Ccl * |(D : ℝ)| ^ (1 / 2 + δ))
    (F : ℕ → ℤ → ℕ → ContentDatum) (h : ℝ → ℂ)
    (hsupp : Function.support h ⊆ Set.Icc (-s) s)
    (hF : ∀ p ∈ squareBases L s, ∀ t : ℤ, t ^ 2 < 4 * (p : ℤ) ^ 2 →
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * (p : ℤ) ^ 2),
        h₀ ((t ^ 2 - 4 * (p : ℤ) ^ 2) / (u : ℤ) ^ 2) ≠ 0 →
        IsPrimitiveContentMatrix u (t ^ 2 - 4 * (p : ℤ) ^ 2) (F p t u))
    (hh : ∀ x, ‖h x‖ ≤ H)
    (htrace : ∀ p ∈ squareBases L s, heckeAverage eigenvalues (p ^ 2) =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card ι : ℝ)) *
        ((p ^ 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator (p ^ 2) : ℝ) : ℂ) +
      literalElliptic k n (Fintype.card ι : ℝ) ((p ^ 2 : ℕ) : ℤ) h₀ (F p) +
      (normalizedCusp k n (Fintype.card ι : ℝ) ((p ^ 2 : ℕ) : ℝ)
        (p ^ 2).divisorsAntidiagonal : ℂ)) :
    (2 / L) * weightedSum (primeBases L s) (-1)
        (fun p => heckeAverage eigenvalues (p ^ 2)) (fun p => h (2 * Real.log p / L)) ≤
      8 * H * Real.log 4 / L +
      squareConstant (ellipticConstant Ccl δ) δ * H / L *
        (((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * (Real.exp (s * L)) ^ (1 / 2 + δ) +
          ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) * (Real.exp (s * L)) ^ δ) +
      2 * (576 / ((k : ℝ) + 1)) * H * Real.log 4 * (1 + s / 2) *
        ((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ)) := by
  let Q := squareBases L s
  let d : ℝ := Fintype.card ι
  let c : ℝ := ((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * d)
  let S : ℕ → ℂ := fun p => ((c / (p : ℝ) : ℝ) : ℂ)
  let E : ℕ → ℂ := fun p => literalElliptic k n d ((p : ℤ) ^ 2) h₀ (F p)
  let C : ℕ → ℂ := fun p => (normalizedCusp k n d ((p ^ 2 : ℕ) : ℝ)
    (p ^ 2).divisorsAntidiagonal : ℂ)
  let w : ℕ → ℂ := fun p => h (2 * Real.log p / L)
  have hL0 : 0 < L := by linarith
  have hX : 1 ≤ Real.exp (s * L) := Real.one_le_exp_iff.mpr (mul_nonneg hs hL0.le)
  have hZ := Real.one_le_sqrt.mpr hX
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc2 : c ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 32 * d)).mpr
    dsimp [d] at *
    nlinarith
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ p ≠ 2 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hdec : ∀ p ∈ Q, heckeAverage eigenvalues (p ^ 2) = S p + E p + C p := by
    intro p hp
    have ht := htrace p hp
    rw [PopaTrace.squareIndicator_square, PopaTrace.square_inverse_sqrt] at ht
    simpa only [mul_one, Nat.cast_pow, S, E, C, c, d, div_eq_mul_inv] using ht
  rw [square_weightedSum_eq hL0 hsupp]
  have hsum := weightedSum_three_decomposition Q (-1)
    (fun p => heckeAverage eigenvalues (p ^ 2)) S E C w
    (fun p hp => (hQ p hp).1.one_le) hdec
  have hSI := scalarCoefficient_square_sum_bound hZ hL0 hH hc0 hc2 Q
    (squareBases_subset_primesLE L s) w (fun _ _ => hh _)
  have hEI := literalElliptic_square_sum_bound k n hn hX hL0 hδ hδhalf hC hH hd
    h₀ Hurwitz h₀nonneg hidentity hHgrowth Q (squareBases_subset_primesLE L s)
    (fun p hp => (hQ p hp).2) F w hF (fun _ _ => hh _)
  have hCI := normalizedCusp_square_sum_bound k n hZ hL hH (div_nonneg hs (by norm_num))
    (le_of_eq (square_endpoint_log L s)) hd Q (squareBases_subset_primesLE L s) w
    (fun _ _ => hh _)
  have ht := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 / L)
  simp only [mul_add] at ht
  exact ht.trans (add_le_add (add_le_add hSI hEI) hCI)

end DepthAspect.UnsignedDensity
