import DepthAspect.SignedSpectralBlock
import DepthAspect.SectionSevenConditionalSupport

/-! The actual normalized signed block in (141). Every internal
prime-average, variation, trace-count and dimension estimate is supplied
by the two parity cases of the spectral theorem. The parameter k here
corresponds to the paper's even modular weight 2k+2. -/
namespace DepthAspect.SectionSevenSigned
open MeasureTheory SignedDensity SignedSieve DirichletRH GRHConsequences
open scoped SchwartzMap

variable {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- The elliptic prime block with the literal explicit-formula factor 2/L,
minus the same normalization of its actual murmuration integral. -/
noncomputable def normalizedEllipticBlockError {k : ℕ}
    (S : SignedArithmeticData k Family Full New) (n : ℕ)
    (L s X Y : ℝ) (h : 𝓢(ℝ, ℂ)) : ℂ :=
  (2 / L : ℝ) • (ellipticPrimeBlock S n L s X Y h -
    (∫ u in X..Y, (traceDimensionScale k ((2 : ℝ) ^ n)
      (Fintype.card (Family (2 ^ n)) : ℝ) *
      MurmurationArithmetic.M k 2 (u / ((2 : ℝ) ^ n)) / u) •
        h (Real.log u / L)))

/-- Equation (141), for the actual spectral block at either parity and
also on the truncated final interval. Its only analytic number-theory
assumptions are primitive Dirichlet RH and its cited general implications. -/
theorem conditional_block_error (k : ℕ) (h : 𝓢(ℝ, ℂ))
    (hRH : PrimitiveDirichletRH) (cited : CitedGeneralTheorems)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : SignedArithmeticData k Family Full New)
      (n : ℕ), 7 ≤ n → ∀ X Y L s : ℝ,
      2 ≤ X → X ≤ Y → Y ≤ 2 * X → 3 ≤ Y → 1 ≤ L → Y ≤ Real.exp (s * L) →
      ‖normalizedEllipticBlockError S n L s X Y h‖ ≤
        (C / L) * ((((2 : ℝ) ^ n) ^ (-(1 / 2 : ℝ))) * X ^ (1 / 4 + ε) +
          (((2 : ℝ) ^ n) ^ (-1 : ℝ)) * X ^ (3 / 4 + ε)) := by
  obtain ⟨C, hC, hb⟩ := signed_prime_elliptic_block_bound
    (Family := Family) (Full := Full) (New := New) k h hRH cited hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro S n hn X Y L s hX hXY hY hY3 hL hYs
  have he := hb S n hn X Y L s hX hXY hY hY3 hL hYs
  have hscale : 0 ≤ 2 / L := div_nonneg (by norm_num) (by linarith)
  unfold normalizedEllipticBlockError
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  exact (mul_le_mul_of_nonneg_left he hscale).trans_eq (by ring)

end DepthAspect.SectionSevenSigned
