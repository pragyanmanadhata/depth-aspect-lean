import DepthAspect.TracePolynomial
import DepthAspect.MurmurationKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Exact Chebyshev and trigonometric forms of the trace polynomial

The Chebyshev expression is the same expression used by MurmurationKernel.
The arcsine identity includes the repeated-root endpoints.
-/
namespace DepthAspect.TraceTrigonometry
open Polynomial Polynomial.Chebyshev

/-- The coefficient recurrence is exactly the scaled Chebyshev-U recurrence. -/
theorem tracePolynomial_scaled_chebyshev (r x : ℂ) (n : ℕ) :
    tracePolynomial (2 * r * x) (r ^ 2) n =
      r ^ n * (U ℂ (n : ℤ)).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [tracePolynomial, U_zero]
  | one => simp [tracePolynomial, U_one]; ring
  | more n ih₀ ih₁ =>
    rw [tracePolynomial, ih₀, ih₁]
    have hU := congrArg (fun p : Polynomial ℂ => p.eval x) (U_add_two ℂ (n : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hU
    rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega, hU]
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega]
    rw [pow_succ r (n + 1), pow_succ r n]
    ring

/-- The repeated-root endpoint value used in the closed signed trace formula. -/
theorem tracePolynomial_repeated_root (s : ℂ) (n : ℕ) :
    tracePolynomial (2 * s) (s ^ 2) n = ((n : ℂ) + 1) * s ^ n := by
  have h := tracePolynomial_scaled_chebyshev s 1 n
  simpa only [mul_one, one_mul, U_eval_one, Int.cast_natCast, mul_comm] using h

/-- The paper's cosine kernel is exactly Chebyshev-U times the semicircle
factor. This formulation includes u=±1 and uses the shared kernel expression. -/
theorem chebyshev_even_arcsin (r : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
    (U ℝ ((2 * r : ℕ) : ℤ)).eval u * Real.sqrt (1 - u ^ 2) =
      (-1 : ℝ) ^ r * Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin u) := by
  obtain ⟨hul, hur⟩ := abs_le.mp hu
  let θ := Real.pi / 2 - Real.arcsin u
  have hc : Real.cos θ = u := by
    rw [show θ = Real.pi / 2 - Real.arcsin u from rfl, Real.cos_pi_div_two_sub,
      Real.sin_arcsin hul hur]
  have hs : Real.sin θ = Real.sqrt (1 - u ^ 2) := by
    rw [show θ = Real.pi / 2 - Real.arcsin u from rfl, Real.sin_pi_div_two_sub,
      Real.cos_arcsin]
  have hU := U_real_cos θ ((2 * r : ℕ) : ℤ)
  rw [hc, hs] at hU
  calc
    _ = Real.sin (((((2 * r : ℕ) : ℤ) : ℝ) + 1) * θ) := hU
    _ = Real.sin ((Real.pi / 2 - (2 * (r : ℝ) + 1) * Real.arcsin u) +
        (r : ℝ) * Real.pi) := by
      congr 1
      dsimp [θ]
      push_cast
      ring
    _ = _ := by rw [Real.sin_add_nat_mul_pi, Real.sin_pi_div_two_sub]

/-- Chebyshev evaluation commutes with the real embedding into the complex field. -/
theorem chebyshev_ofReal (n : ℤ) (u : ℝ) :
    (U ℂ n).eval (u : ℂ) = (((U ℝ n).eval u : ℝ) : ℂ) := by
  rw [← map_U Complex.ofRealHom n]
  exact Polynomial.eval_map_apply Complex.ofRealHom u

/-- The exact trace-polynomial cosine quotient in the strict elliptic range.
Writing s=√m and u=t/(2√(vm)) gives equation (65); the endpoint-free kernel
identity above remains valid at the repeated-root endpoints. -/
theorem tracePolynomial_even_arcsin (r : ℕ) (s u : ℝ) (hu : |u| < 1) :
    tracePolynomial ((2 * s * u : ℝ) : ℂ) ((s ^ 2 : ℝ) : ℂ) (2 * r) =
      ((s ^ (2 * r) * (-1 : ℝ) ^ r *
        Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin u) / Real.sqrt (1 - u ^ 2) : ℝ) : ℂ) := by
  have hsq : 0 < 1 - u ^ 2 := by
    have hab := (sq_lt_one_iff_abs_lt_one u).mpr hu
    linarith
  have hroot : Real.sqrt (1 - u ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hsq).ne'
  have heval : (U ℝ ((2 * r : ℕ) : ℤ)).eval u =
      (-1 : ℝ) ^ r * Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin u) /
        Real.sqrt (1 - u ^ 2) :=
    (eq_div_iff hroot).mpr (chebyshev_even_arcsin r u hu.le)
  push_cast
  rw [tracePolynomial_scaled_chebyshev, chebyshev_ofReal, heval]
  push_cast
  ring

/-- Equation (65) with its literal variables and normalization. The weight is
2r+2, so the degree is 2r and the cosine-polynomial sign equals (-1)^r. -/
theorem tracePolynomial_signed_formula (r : ℕ) (t v m : ℝ)
    (hv : 0 < v) (hm : 0 < m) (ht : t ^ 2 < 4 * v * m) :
    tracePolynomial ((t / Real.sqrt v : ℝ) : ℂ) (m : ℂ) (2 * r) =
      ((2 * (-1 : ℝ) ^ r * m ^ ((r : ℝ) + 1 / 2) * Real.sqrt v *
        Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin (t / (2 * Real.sqrt (v * m)))) /
        Real.sqrt (4 * v * m - t ^ 2) : ℝ) : ℂ) := by
  have hvroot : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hmroot : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hvm : 0 < v * m := mul_pos hv hm
  have hvmroot : 0 < Real.sqrt (v * m) := Real.sqrt_pos.mpr hvm
  have hden : 0 < 4 * v * m - t ^ 2 := by linarith
  have hsprod : Real.sqrt (v * m) = Real.sqrt v * Real.sqrt m :=
    Real.sqrt_mul hv.le m
  have hsq : (2 * Real.sqrt (v * m)) ^ 2 = 4 * v * m := by
    nlinarith [Real.sq_sqrt hvm.le]
  have hu : |t / (2 * Real.sqrt (v * m))| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (v * m)),
      div_lt_one (by positivity : 0 < 2 * Real.sqrt (v * m))]
    apply (sq_lt_sq₀ (abs_nonneg t) (by positivity : 0 ≤ 2 * Real.sqrt (v * m))).mp
    simpa only [sq_abs, hsq] using ht
  have hinner : 1 - (t / (2 * Real.sqrt (v * m))) ^ 2 =
      (4 * v * m - t ^ 2) / (2 * Real.sqrt (v * m)) ^ 2 := by
    field_simp [ne_of_gt hvmroot]
    nlinarith [hsq]
  have hs : Real.sqrt (1 - (t / (2 * Real.sqrt (v * m))) ^ 2) =
      Real.sqrt (4 * v * m - t ^ 2) / (2 * Real.sqrt (v * m)) := by
    rw [hinner, Real.sqrt_div hden.le, Real.sqrt_sq (by positivity)]
  have hx : 2 * Real.sqrt m * (t / (2 * Real.sqrt (v * m))) = t / Real.sqrt v := by
    rw [hsprod]
    field_simp [ne_of_gt hvroot, ne_of_gt hmroot]
  have hp : Real.sqrt m ^ (2 * r) = m ^ r := by
    rw [pow_mul, Real.sq_sqrt hm.le]
  have hpower : m ^ ((r : ℝ) + 1 / 2) = m ^ r * Real.sqrt m := by
    rw [Real.rpow_add hm, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have h := tracePolynomial_even_arcsin r (Real.sqrt m)
    (t / (2 * Real.sqrt (v * m))) hu
  rw [hx, Real.sq_sqrt hm.le, hp, hs, hsprod] at h
  rw [h, hpower, hsprod]
  push_cast
  simp only [div_div, div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- The zero-trace polynomial value in (68), with even degree 2r. -/
theorem tracePolynomial_even_zero (r : ℕ) :
    tracePolynomial 0 1 (2 * r) = (-1 : ℂ) ^ r := by
  simpa using tracePolynomial_even_arcsin r 1 0 (by norm_num)

/-- The paper's cosine expression is the actual shared compactly supported
kernel on its entire closed support. -/
theorem kernel_even_arcsin (r : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
    MurmurationKernel.kernel (2 * r + 2) u =
      (-1 : ℝ) ^ r * Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin u) := by
  unfold MurmurationKernel.kernel
  rw [show ((2 * r + 2 : ℕ) : ℤ) - 2 = ((2 * r : ℕ) : ℤ) by omega]
  exact chebyshev_even_arcsin r u hu

end DepthAspect.TraceTrigonometry
