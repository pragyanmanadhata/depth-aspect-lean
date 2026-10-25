import DepthAspect.SignedTraceIndices
import DepthAspect.SignedDensityModel

/-! Literal spectral prime traces on the shared active-index lattice. -/
namespace DepthAspect.SignedDensity
open SignedSieve DyadicRamanujan QuadraticDiscriminantL SpectralFamily
open scoped BigOperators

variable {r : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- Equation (75) on precisely the r-indices counted in (111). -/
theorem primeSignedTrace_even_lattice
    (S : SignedArithmeticData r Family Full New)
    (a P : ℕ) (ha : 2 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    S.primeSignedTrace (2 ^ (2 * a + 4)) P =
      ((2 * Real.sqrt P / Real.pi * primeWeight P : ℝ) : ℂ) * (2 : ℂ) ^ (a + 1) *
        (∑ j ∈ activeIndices ((2 : ℝ) ^ (2 * a + 4)) P,
          (-1 : ℂ) ^ j *
            (Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin
              ((j : ℝ) / (4 * Real.sqrt ((P : ℝ) / (2 : ℝ) ^ (2 * a + 4))))) : ℂ) *
            LAtOne S.quadratic_class_formula (((2 : ℤ) ^ (a + 1) * j) ^ 2 - 4 * P)) +
      (-1 : ℂ) ^ (r + 2) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
        (((P : ℝ) ^ (-(r : ℝ)) : ℝ) : ℂ) := by
  rw [S.primeSignedTrace_even a P ha hP hodd]
  have he : (∑ t ∈ strictPrimeTraces 1 P,
      ramanujanTwoPow (a + 1) t * (primeCosine r 1 P t : ℂ) *
        LAtOne S.quadratic_class_formula (t ^ 2 - 4 * P)) =
      (2 : ℂ) ^ (a + 1) *
        ∑ j ∈ activeIndices ((2 : ℝ) ^ (2 * a + 4)) P,
          (-1 : ℂ) ^ j *
            (Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin
              ((j : ℝ) / (4 * Real.sqrt ((P : ℝ) / (2 : ℝ) ^ (2 * a + 4))))) : ℂ) *
            LAtOne S.quadratic_class_formula (((2 : ℤ) ^ (a + 1) * j) ^ 2 - 4 * P) := by
    simp_rw [mul_assoc]
    rw [ramanujan_trace_reindex, scaledPrimeTraces_even a P hP.pos]
    simp_rw [primeCosine_even_scaled r a P hP.pos]
  rw [he]
  ring

/-- Equation (76) uses the identical active r-set after its different
half-modulus scale and base discriminant are retained. -/
theorem primeSignedTrace_odd_lattice
    (S : SignedArithmeticData r Family Full New)
    (a P : ℕ) (ha : 1 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    S.primeSignedTrace (2 ^ (2 * a + 5)) P =
      ((Real.sqrt P / (Real.pi * Real.sqrt 2) : ℝ) : ℂ) * (2 : ℂ) ^ (a + 2) *
        (∑ j ∈ activeIndices ((2 : ℝ) ^ (2 * a + 5)) P,
          (-1 : ℂ) ^ j *
            (Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin
              ((j : ℝ) / (4 * Real.sqrt ((P : ℝ) / (2 : ℝ) ^ (2 * a + 5))))) : ℂ) *
            LAtOne S.quadratic_class_formula (((2 : ℤ) ^ (a + 2) * j) ^ 2 - 8 * P)) := by
  rw [S.primeSignedTrace_odd a P ha hP hodd]
  have he : (∑ t ∈ strictPrimeTraces 2 P,
      ramanujanTwoPow (a + 2) t * (primeCosine r 2 P t : ℂ) *
        LAtOne S.quadratic_class_formula (t ^ 2 - 8 * P)) =
      (2 : ℂ) ^ (a + 2) *
        ∑ j ∈ activeIndices ((2 : ℝ) ^ (2 * a + 5)) P,
          (-1 : ℂ) ^ j *
            (Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin
              ((j : ℝ) / (4 * Real.sqrt ((P : ℝ) / (2 : ℝ) ^ (2 * a + 5))))) : ℂ) *
            LAtOne S.quadratic_class_formula (((2 : ℤ) ^ (a + 2) * j) ^ 2 - 8 * P) := by
    simp_rw [mul_assoc]
    rw [ramanujan_trace_reindex, scaledPrimeTraces_odd a P hP.pos]
    simp_rw [primeCosine_odd_scaled r a P hP.pos]
  rw [he]
  ring

/-- The j=1 contribution of the literal signed explicit formula is the
paper's sum of log(P)/P times A_P, divided by the actual family cardinality. -/
theorem signedPrimeContribution_eq_traceSum
    (S : SignedArithmeticData r Family Full New) (n : ℕ) (L : ℝ)
    (h : ℝ → ℂ) (T : Finset ℕ) (hT : ∀ p ∈ T, 0 < p) :
    signedPrimeContribution (fun f => (S.rootNumber (2 ^ n) f : ℂ)) L h
      (S.unsigned.eigenvalues (2 ^ n)) T =
        ∑ p ∈ T, ((Real.log (p : ℝ) / p : ℝ) : ℂ) *
          S.primeSignedTrace (2 ^ n) p / (Fintype.card (Family (2 ^ n)) : ℂ) *
            h (Real.log (p : ℝ) / L) := by
  apply Finset.sum_congr rfl
  intro p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hT p hp
  have hs : (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hpR.le
  have hs0 : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpR).ne'
  have hw : (Real.log (p : ℝ) : ℂ) / (Real.sqrt (p : ℝ) : ℂ) =
      ((Real.log (p : ℝ) : ℂ) / (p : ℂ)) * (Real.sqrt (p : ℝ) : ℂ) := by
    rw [← hs]
    field_simp [hs0] <;> ring
  unfold signedHeckeAverage average SignedArithmeticData.primeSignedTrace signedHeckeSum
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  rw [hw]
  ring

end DepthAspect.SignedDensity
