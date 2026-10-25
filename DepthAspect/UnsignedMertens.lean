import DepthAspect.UnsignedDensity
import DepthAspect.MertensFourier

/-!
# The actual prime-square constant term in the finite density formula

This identifies the finite `-1` coefficient in the averaged square term
with the complete Mertens-weighted prime sum, including the support argument
that makes the two sums equal.
-/
namespace DepthAspect.UnsignedDensity

open SpectralFamily
open scoped BigOperators FourierTransform SchwartzMap

noncomputable def mertensContribution (L : ℝ) (h : ℝ → ℂ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
    h (2 * Real.log (p : ℝ) / L)

noncomputable def squareHeckeContribution {ι : Type*} [Fintype ι]
    (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
    heckeAverage a (p ^ 2) * h (2 * Real.log (p : ℝ) / L)

theorem squareContribution_decompose {ι : Type*} [Fintype ι]
    (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ) :
    squareContribution L h a P = squareHeckeContribution L h a P - mertensContribution L h P := by
  unfold squareContribution squareHeckeContribution mertensContribution
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The canonical finite prime box contains every nonzero Mertens summand.
This holds even when the support is so small that the box is empty. -/
theorem mertensContribution_eq_total {L s : ℝ} (hL : 0 < L)
    {h : ℝ → ℂ} (hsupp : Function.support h ⊆ Set.Icc (-s) s) :
    mertensContribution L h (primeBases L s) = MertensWeights.weightedTotal (2 / L) h := by
  have hsum : MertensWeights.weightedTotal (2 / L) h =
      ∑ p ∈ primeBases L s,
        MertensWeights.logWeight (2 / L) h p * (MertensWeights.oddPrimeWeight p : ℂ) := by
    unfold MertensWeights.weightedTotal
    apply tsum_eq_sum
    intro p hp
    by_cases hprime : p.Prime ∧ Odd p
    · have hp2 : p ≠ 2 := by
        intro he
        obtain ⟨i, hi⟩ := hprime.2
        omega
      by_cases hh : h (2 * Real.log (p : ℝ) / L) = 0
      · have he : (2 / L) * Real.log (p : ℝ) = 2 * Real.log (p : ℝ) / L := by ring
        simp only [MertensWeights.logWeight, he, hh, zero_mul]
      · have hsquare := PrimePowerSupport.supported_prime_power_le hL hsupp hprime.1.pos
          (j := 2) (by simpa only [Nat.cast_ofNat] using hh)
        have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hprime.1.two_le
        have hpSquare : (p : ℝ) ≤ (p : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((p : ℝ) - 1)]
        have hple : (p : ℝ) ≤ Real.exp (s * L) := hpSquare.trans hsquare
        exact (hp (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨hprime.1.two_le, Nat.le_floor hple⟩, hprime.1, hp2⟩)).elim
    · simp only [MertensWeights.oddPrimeWeight, if_neg hprime, Complex.ofReal_zero, mul_zero]
  rw [hsum]
  unfold mertensContribution
  apply Finset.sum_congr rfl
  intro p hp
  have hc := (Finset.mem_filter.mp hp).2
  have hprime : p.Prime ∧ Odd p := ⟨hc.1, hc.1.odd_of_ne_two hc.2⟩
  simp only [MertensWeights.oddPrimeWeight, if_pos hprime, MertensWeights.logWeight]
  rw [show (2 / L) * Real.log (p : ℝ) = 2 * Real.log (p : ℝ) / L by ring, mul_comm]

/-- The main term in (61) is the actual finite prime-square constant term,
with the explicit error proved from the cited Mertens cumulative estimate. -/
theorem finite_mertens_main_term {L C s : ℝ}
    (hL : 0 < L) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s) :
    ‖((2 / L : ℝ) : ℂ) * mertensContribution L (𝓕 φ : 𝓢(ℝ, ℂ)) (primeBases L s) - φ 0 / 2‖ ≤
      (4 * Real.log 2 + 2 * C) *
        (‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖ +
          ∫ u : ℝ, ‖deriv (𝓕 φ : 𝓢(ℝ, ℂ)) u‖) / L := by
  rw [mertensContribution_eq_total hL hsupp]
  simpa only [Complex.real_smul] using
    MertensFourier.fourier_mertens_main_term hL hC hM φ heven hsupp

end DepthAspect.UnsignedDensity
