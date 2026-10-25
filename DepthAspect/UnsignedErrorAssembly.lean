import DepthAspect.UnsignedRemainder
import DepthAspect.UnsignedMertens
import DepthAspect.UnsignedExponents
import DepthAspect.PrimePowerApplications

/-!
# The unsigned density main term and finite trace-error assembly

The actual finite zero average, actual prime sums, actual higher-power
remainder, and the Mertens prime-square term are combined here. The named
individual trace-sum bounds are intermediate obligations, supplied by the
pointwise trace estimates and `PrimeSumBounds` / `PrimePowerApplications`.
-/
namespace DepthAspect.UnsignedDensity

open SpectralFamily
open scoped BigOperators FourierTransform SchwartzMap

/-- Triangle inequality for the literal prime contribution, with exactly
the nonnegative prime weight used by the arithmetic prime-sum estimates. -/
theorem primeContribution_norm_le {ι : Type*} [Fintype ι]
    (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    ‖primeContribution L h a P‖ ≤
      PrimePowerApplications.weightedSum P (-(1 / 2 : ℝ)) (heckeAverage a)
        (fun p => h (Real.log p / L)) := by
  rw [PrimePowerApplications.weightedSum_neg_half]
  unfold primeContribution
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hP p hp))
      (Real.sqrt_nonneg _))]

/-- The analogous bound for the Hecke part of the prime-square term. -/
theorem squareHeckeContribution_norm_le {ι : Type*} [Fintype ι]
    (L : ℝ) (h : ℝ → ℂ) (a : ι → ℕ → ℂ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 1 ≤ p) :
    ‖squareHeckeContribution L h a P‖ ≤
      PrimePowerApplications.weightedSum P (-1) (fun p => heckeAverage a (p ^ 2))
        (fun p => h (2 * Real.log p / L)) := by
  rw [PrimePowerApplications.weightedSum_neg_one]
  unfold squareHeckeContribution
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hP p hp))
      (Nat.cast_nonneg _))]

/-- The constant `+ φ(0)/2` is obtained from the actual Mertens prime sum,
not imposed as part of a density hypothesis. The only per-form formula input
is the named equation (56), discharged by its analytic specialization. -/
theorem density_error_from_trace_sums {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : ι → Type*} {L s EA H C EP EQ : ℝ}
    (hL : 0 < L) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hM : ∀ x : ℝ, 2 ≤ x → |MertensWeights.mertensSum x - Real.log x| ≤ C)
    (φ : 𝓢(ℝ, ℂ)) (heven : Function.Even φ)
    (hsupp : Function.support (𝓕 φ : 𝓢(ℝ, ℂ)) ⊆ Set.Icc (-s) s)
    (γ : ∀ f, κ f → ℂ) (α β : ι → ℕ → ℂ) (a : ι → ℕ → ℂ) (A : ℂ)
    (hfirst : ∀ p ∈ primeBases L s, ∀ f, α f p + β f p = a f p)
    (hprod : ∀ p ∈ primeBases L s, ∀ f, α f p * β f p = 1)
    (hsquare : ∀ p ∈ primeBases L s, ∀ f,
      tracePolynomial (α f p + β f p) 1 2 = a f (p ^ 2))
    (hα : ∀ p ∈ primeBases L s, ∀ f, ‖α f p‖ = 1)
    (hβ : ∀ p ∈ primeBases L s, ∀ f, ‖β f p‖ = 1)
    (hh : ∀ x, ‖(𝓕 φ : 𝓢(ℝ, ℂ)) x‖ ≤ H)
    (hArch : ‖A - (𝓕 φ : 𝓢(ℝ, ℂ)) 0‖ ≤ EA)
    (h56 : ∀ f, ExplicitFormula.density s L φ (γ f) =
      A - ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (α f) (β f))
    (hPrime : (2 / L) * PrimePowerApplications.weightedSum (primeBases L s)
      (-(1 / 2 : ℝ)) (heckeAverage a)
      (fun p => (𝓕 φ : 𝓢(ℝ, ℂ)) (Real.log p / L)) ≤ EP)
    (hSquare : (2 / L) * PrimePowerApplications.weightedSum (primeBases L s)
      (-1) (fun p => heckeAverage a (p ^ 2))
      (fun p => (𝓕 φ : 𝓢(ℝ, ℂ)) (2 * Real.log p / L)) ≤ EQ) :
    ‖meanDensity s L φ γ - ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 + φ 0 / 2)‖ ≤
      EA + 192 * H / L +
        (4 * Real.log 2 + 2 * C) *
          (‖(𝓕 φ : 𝓢(ℝ, ℂ)).toBoundedContinuousFunction‖ +
            ∫ u : ℝ, ‖deriv (𝓕 φ : 𝓢(ℝ, ℂ)) u‖) / L + EP + EQ := by
  let h : ℝ → ℂ := (𝓕 φ : 𝓢(ℝ, ℂ))
  let P := primeBases L s
  let c : ℂ := ((2 / L : ℝ) : ℂ)
  have hP : ∀ p ∈ P, 1 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1.one_le
  have hp := primeContribution_norm_le L h a P hP
  have hq := squareHeckeContribution_norm_le L h a P hP
  have hpn : ‖c * primeContribution L h a P‖ ≤ EP := by
    change ‖((2 / L : ℝ) : ℂ) * primeContribution L h a P‖ ≤ EP
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans hPrime
  have hqn : ‖c * squareHeckeContribution L h a P‖ ≤ EQ := by
    change ‖((2 / L : ℝ) : ℂ) * squareHeckeContribution L h a P‖ ≤ EQ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
    exact (mul_le_mul_of_nonneg_left hq (by positivity)).trans hSquare
  have hr := averaged_low_power_error hL hH φ hsupp γ α β a A hfirst hprod hsquare
    hα hβ hh hArch h56
  have hm := finite_mertens_main_term hL hC hM φ heven hsupp
  let R := meanDensity s L φ γ - (h 0 - c * primeContribution L h a P -
    c * squareContribution L h a P)
  have heq : meanDensity s L φ γ - (h 0 + φ 0 / 2) =
      R + (c * mertensContribution L h P - φ 0 / 2) -
        c * primeContribution L h a P - c * squareHeckeContribution L h a P := by
    dsimp [R]
    rw [squareContribution_decompose]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add hr hm)) hpn)) hqn)

end DepthAspect.UnsignedDensity
