import DepthAspect.SignedPrimeLattice
import DepthAspect.EvenTraceError
import DepthAspect.SignedBalance

/-!
# The spectral meaning of the finite block model

The arithmetic block is identified with the literal elliptic part of the
actual signed prime trace. Both parity constants and the log(P)/P spectral
normalization are retained exactly.
-/
namespace DepthAspect.SignedDensity
open SignedSieve DyadicRamanujan QuadraticDiscriminantL TraceWeightVariation
open scoped BigOperators SchwartzMap

noncomputable def oddLValue {H : ℤ → ℝ} (G : QuadraticClassFormula.GeneralFormula H)
    (a : ℕ) (j : ℤ) (P : ℕ) : ℂ :=
  LAtOne G (((2 : ℤ) ^ (a + 2) * j) ^ 2 - 8 * (P : ℤ))

noncomputable def latticeEllipticTrace (k : ℕ) (N : ℝ) (V : ℤ → ℕ → ℂ) (P : ℕ) : ℂ :=
  ((Real.sqrt (N * P) / (2 * Real.pi) : ℝ) : ℂ) *
    ∑ j ∈ activeIndices N P, (-1 : ℂ) ^ j *
      (Real.cos ((2 * (k : ℝ) + 1) * Real.arcsin
        ((j : ℝ) / (4 * Real.sqrt ((P : ℝ) / N)))) : ℂ) * V j P

/-- The actual log(P)/P sum of lattice traces is exactly the finite block
model whose arithmetic discrepancy was bounded in (112). -/
theorem primeTraceBlock_eq_latticeTraceSum (k : ℕ) {N d : ℝ}
    (hN : 0 < N) (hd : 0 < d) (L X Y : ℝ) (h : 𝓢(ℝ, ℂ))
    (T : Finset ℕ) (hT : ∀ P ∈ T, 0 < P) (V : ℤ → ℕ → ℂ) :
    primeTraceBlock k N d L X Y h T V =
      ∑ P ∈ T.filter (fun P : ℕ => X < (P : ℝ) ∧ (P : ℝ) ≤ Y),
        ((Real.log (P : ℝ) / P : ℝ) : ℂ) * latticeEllipticTrace k N V P /
          (d : ℂ) * h (Real.log (P : ℝ) / L) := by
  classical
  unfold primeTraceBlock
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hT P (Finset.mem_filter.mp hP).1
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP0.ne'
  have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold latticeEllipticTrace
  simp only [Finset.smul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [traceWeight, cosineTrace, traceAngle, traceAmplitude, smul_smul,
    traceAngle_main_argument hN hP0, inverse_sqrt_eq_sqrt_div hP0,
    Real.sqrt_mul hN.le, traceMainScale, Complex.real_smul]
  push_cast
  field_simp [hdC, hPC, hπC] <;> ring

variable {k : ℕ} {Family Full New : ℕ → Type*}
  [∀ N, Fintype (Family N)]
  [∀ N, AddCommGroup (Full N)] [∀ N, Module ℂ (Full N)]
  [∀ N, AddCommGroup (New N)] [∀ N, Module ℂ (New N)]

/-- The elliptic portion of (75) has precisely the doubled w(P) used in
the actual even prime-average theorem. The remaining term is displayed. -/
theorem primeSignedTrace_even_model (S : SignedArithmeticData k Family Full New)
    (a P : ℕ) (ha : 2 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    S.primeSignedTrace (2 ^ (2 * a + 4)) P =
      latticeEllipticTrace k ((2 : ℝ) ^ (2 * a + 4))
        (evenLValue S.quadratic_class_formula a) P +
      (-1 : ℂ) ^ (k + 2) / 2 * ramanujanTwoPow (a + 1) (P + 1) *
        (((P : ℝ) ^ (-(k : ℝ)) : ℝ) : ℂ) := by
  rw [primeSignedTrace_even_lattice S a P ha hP hodd]
  congr 1
  have hN : Real.sqrt ((2 : ℝ) ^ (2 * a + 4)) = (2 : ℝ) ^ (a + 2) := by
    rw [show 2 * a + 4 = 2 * (a + 2) by omega, sqrt_two_even_power]
  unfold latticeEllipticTrace evenLValue
  rw [Real.sqrt_mul (by positivity), hN]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  rw [show a + 2 = (a + 1) + 1 by omega, pow_succ]
  ring

/-- At odd depth the √2 factor produces the same common lattice scale,
and the actual hyperbolic contribution is zero. -/
theorem primeSignedTrace_odd_model (S : SignedArithmeticData k Family Full New)
    (a P : ℕ) (ha : 1 ≤ a) (hP : P.Prime) (hodd : Odd P) :
    S.primeSignedTrace (2 ^ (2 * a + 5)) P =
      latticeEllipticTrace k ((2 : ℝ) ^ (2 * a + 5))
        (oddLValue S.quadratic_class_formula a) P := by
  rw [primeSignedTrace_odd_lattice S a P ha hP hodd]
  have hN : Real.sqrt ((2 : ℝ) ^ (2 * a + 5)) = Real.sqrt 2 * (2 : ℝ) ^ (a + 2) := by
    rw [show 2 * a + 5 = 2 * (a + 2) + 1 by omega, sqrt_two_odd_power]
  unfold latticeEllipticTrace oddLValue
  rw [Real.sqrt_mul (by positivity), hN]
  congr 1
  push_cast
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hs0, hπ]
  ring_nf
  simp only [hs] <;> ring

end DepthAspect.SignedDensity
