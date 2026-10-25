import DepthAspect.UnsignedDensity
import DepthAspect.FinitePrimePowerTail
import DepthAspect.ArchimedeanBound

/-! The actual higher-power remainder in the finite spectral average (61). -/
namespace DepthAspect.UnsignedDensity

open SpectralFamily
open scoped BigOperators FourierTransform SchwartzMap

theorem higherContribution_norm_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (L s : ℝ) (h : ℝ → ℂ) (α β : ι → ℕ → ℂ)
    (hα : ∀ p ∈ primeBases L s, ∀ f, ‖α f p‖ = 1)
    (hβ : ∀ p ∈ primeBases L s, ∀ f, ‖β f p‖ = 1)
    (H : ℝ) (hH : 0 ≤ H) (hh : ∀ x, ‖h x‖ ≤ H) :
    ‖higherContribution L s h α β‖ ≤ 96 * H := by
  let S := primeBases L s ×ˢ Finset.Icc 3 (powerCap L s)
  have hS : ∀ pj ∈ S, pj.1.Prime ∧ 3 ≤ pj.1 ∧ 3 ≤ pj.2 := by
    intro pj hpj
    obtain ⟨hp, hj⟩ := Finset.mem_product.mp hpj
    have hc := (Finset.mem_filter.mp hp).2
    have hp2 := hc.1.two_le
    exact ⟨hc.1, by omega, (Finset.mem_Icc.mp hj).1⟩
  have ha : ∀ pj ∈ S, ‖meanPowerCoefficient α β pj.1 pj.2‖ ≤ 2 := by
    intro pj hpj
    apply norm_average_le
    intro f
    have hp := (Finset.mem_product.mp hpj).1
    exact SatakeCoefficients.norm_powerCoefficient_le_two _ _ (hα _ hp f) (hβ _ hp f) _
  have hb := FinitePrimePowerTail.finite_primePowerTerm_tail_bound S hS
    (meanPowerCoefficient α β) ha h H hH hh L
  simpa only [higherContribution, meanPrimePowerTerm, PrimePowerSupport.primePowerTerm] using hb

/-- A fixed-test, fixed-weight constant for the actual archimedean term. -/
noncomputable def archimedeanConstant (a : ℕ) (φ : 𝓢(ℝ, ℂ)) : ℝ :=
  Real.log (4 * Real.pi ^ 2 * (2 * a) ^ 2) * ‖(𝓕 φ : 𝓢(ℝ, ℂ)) 0‖ +
    2 * ArchimedeanBound.harmonicConstant a * (∫ x : ℝ, ‖φ x‖) +
      8 * Real.pi * (∫ x : ℝ, ‖x • φ x‖)

theorem archimedeanConstant_nonneg (a : ℕ) (ha : 1 ≤ a) (φ : 𝓢(ℝ, ℂ)) :
    0 ≤ archimedeanConstant a φ := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hlog := ArchimedeanBound.conductor_log_nonneg (2 * a) (by linarith)
  have hI : 0 ≤ ∫ x : ℝ, ‖φ x‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have hJ : 0 ≤ ∫ x : ℝ, ‖x • φ x‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  unfold archimedeanConstant ArchimedeanBound.harmonicConstant
  positivity

/-- The actual digamma integral contributes a uniform inverse-log error;
the first-moment integrability is supplied by the Schwartz class. -/
theorem actual_archimedean_error (hDLMF : DigammaBound.DLMFSeriesIdentity)
    (N : ℝ) (hN : 1 ≤ N) (a : ℕ) (ha : 1 ≤ a) (φ : 𝓢(ℝ, ℂ))
    (hL : 1 ≤ Real.log ((2 * (a : ℝ)) ^ 2 * N)) :
    ‖ArchimedeanBound.archimedeanTerm N (2 * a) a φ ((𝓕 φ : 𝓢(ℝ, ℂ)) 0) -
      (𝓕 φ : 𝓢(ℝ, ℂ)) 0‖ ≤
      archimedeanConstant a φ / Real.log ((2 * (a : ℝ)) ^ 2 * N) := by
  let L := Real.log ((2 * (a : ℝ)) ^ 2 * N)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hLsq : L ≤ L ^ 2 := by dsimp [L]; nlinarith
  have hI : 0 ≤ ∫ x : ℝ, ‖x • φ x‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have htail : (8 * Real.pi / L ^ 2) * (∫ x : ℝ, ‖x • φ x‖) ≤
      (8 * Real.pi * (∫ x : ℝ, ‖x • φ x‖)) / L := by
    calc
      _ = (8 * Real.pi * (∫ x : ℝ, ‖x • φ x‖)) / L ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hL0 hLsq
  have hb := ArchimedeanBound.schwartz_even_weight_remainder_bound hDLMF N hN a ha φ
    ((𝓕 φ : 𝓢(ℝ, ℂ)) 0)
  apply hb.trans
  calc
    _ ≤ (Real.log (4 * Real.pi ^ 2 * (2 * a) ^ 2) * ‖(𝓕 φ : 𝓢(ℝ, ℂ)) 0‖ +
        2 * ArchimedeanBound.harmonicConstant a * (∫ x : ℝ, ‖φ x‖)) / L +
          (8 * Real.pi * (∫ x : ℝ, ‖x • φ x‖)) / L := add_le_add le_rfl htail
    _ = _ := by dsimp [archimedeanConstant, L]; ring

/-- Quantitative version of the `O(L⁻¹)` in (61). The tail estimate is
proved for the literal finite prime-power sum; `hArch` is the separately
proved estimate (59), to be instantiated with the actual digamma integral. -/
theorem averaged_low_power_error {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ : ι → Type*} {L s EA H : ℝ} (hL : 0 < L) (hH : 0 ≤ H) (φ : 𝓢(ℝ, ℂ))
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
      A - ((2 / L : ℝ) : ℂ) * ExplicitFormula.primePowerSum L φ (α f) (β f)) :
    ‖meanDensity s L φ γ - ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 -
      ((2 / L : ℝ) : ℂ) * primeContribution L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * squareContribution L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s))‖ ≤
      EA + 192 * H / L := by
  have hid := averaged_low_power_formula hL φ hsupp γ α β a A hfirst hprod hsquare h56
  have ht := higherContribution_norm_bound L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β hα hβ H hH hh
  have htail : ‖((2 / L : ℝ) : ℂ) * higherContribution L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β‖ ≤
      192 * H / L := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 2 / L)]
    calc
      _ ≤ (2 / L) * (96 * H) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have heq : meanDensity s L φ γ - ((𝓕 φ : 𝓢(ℝ, ℂ)) 0 -
      ((2 / L : ℝ) : ℂ) * primeContribution L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s) -
      ((2 / L : ℝ) : ℂ) * squareContribution L (𝓕 φ : 𝓢(ℝ, ℂ)) a (primeBases L s)) =
      (A - (𝓕 φ : 𝓢(ℝ, ℂ)) 0) -
        ((2 / L : ℝ) : ℂ) * higherContribution L s (𝓕 φ : 𝓢(ℝ, ℂ)) α β := by
    rw [hid]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hArch htail)

end DepthAspect.UnsignedDensity
