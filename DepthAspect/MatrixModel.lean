import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Matrix conjugation and the integral representative in equations (18)–(19)

The discriminant identity implies the required parity of the diagonal
numerators. The displayed matrix has trace t, determinant m, and associated
binary quadratic form u[A,B,C]. The explicit determinant-one inverse also gives
the conjugated lower-left entry used in (18). These are identities of actual
integer matrices.
-/

namespace DepthAspect

def matrixQuadratic (M : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ) : ℤ :=
  M 1 0 * x ^ 2 + (M 1 1 - M 0 0) * x * y - M 0 1 * y ^ 2

def integerRepresentative (t u A B C : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(t - u * B) / 2, -u * C; u * A, (t + u * B) / 2]

/-- The explicit adjugate; for determinant one this is the integral inverse. -/
def adjugateTwo (X : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![X 1 1, -X 0 1; -X 1 0, X 0 0]

theorem adjugateTwo_inverse (X : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : Matrix.det X = 1) :
    X * adjugateTwo X = 1 ∧ adjugateTwo X * X = 1 := by
  rw [Matrix.det_fin_two] at hdet
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [adjugateTwo, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hdet]

/-- The lower-left entry of the determinant-one change of basis, as used
immediately before (19). -/
theorem conjugated_lower_left (X M : Matrix (Fin 2) (Fin 2) ℤ) :
    (X * M * adjugateTwo X) 1 0 = matrixQuadratic M (X 1 1) (-X 1 0) := by
  simp [adjugateTwo, matrixQuadratic, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem matrixQuadratic_discriminant (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (M 1 1 - M 0 0) ^ 2 - 4 * M 1 0 * (-M 0 1) =
      (Matrix.trace M) ^ 2 - 4 * Matrix.det M := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring

/-- Vanishing of the quadratic is the determinant condition for a vector
and its image to be collinear. -/
theorem matrixQuadratic_eq_vector_det (M : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℤ) :
    matrixQuadratic M x y =
      x * (M 1 0 * x + M 1 1 * y) - y * (M 0 0 * x + M 0 1 * y) := by
  unfold matrixQuadratic
  ring

theorem representative_parity {t m u A B C : ℤ}
    (hD : t ^ 2 - 4 * m = u ^ 2 * (B ^ 2 - 4 * A * C)) :
    Even (t - u * B) ∧ Even (t + u * B) := by
  have hsq : Even (t ^ 2 - (u * B) ^ 2) := by
    refine ⟨2 * (m - u ^ 2 * A * C), ?_⟩
    nlinarith [hD]
  have hpar : Even t ↔ Even (u * B) := by
    simpa only [Int.even_sub, Int.even_pow, OfNat.ofNat_ne_zero,
      ne_eq, not_false_eq_true, and_true] using hsq
  exact ⟨Int.even_sub.mpr hpar, Int.even_add.mpr hpar⟩

theorem representative_diagonal {t m u A B C : ℤ}
    (hD : t ^ 2 - 4 * m = u ^ 2 * (B ^ 2 - 4 * A * C)) :
    2 * ((t - u * B) / 2) = t - u * B ∧
    2 * ((t + u * B) / 2) = t + u * B := by
  obtain ⟨hminus, hplus⟩ := representative_parity hD
  constructor
  · simpa only [mul_comm] using Int.ediv_mul_cancel hminus.two_dvd
  · simpa only [mul_comm] using Int.ediv_mul_cancel hplus.two_dvd

theorem integerRepresentative_trace {t m u A B C : ℤ}
    (hD : t ^ 2 - 4 * m = u ^ 2 * (B ^ 2 - 4 * A * C)) :
    Matrix.trace (integerRepresentative t u A B C) = t := by
  obtain ⟨ha, hd⟩ := representative_diagonal hD
  rw [integerRepresentative, Matrix.trace_fin_two_of]
  omega

theorem integerRepresentative_det {t m u A B C : ℤ}
    (hD : t ^ 2 - 4 * m = u ^ 2 * (B ^ 2 - 4 * A * C)) :
    Matrix.det (integerRepresentative t u A B C) = m := by
  obtain ⟨ha, hd⟩ := representative_diagonal hD
  rw [integerRepresentative, Matrix.det_fin_two_of]
  have hprod : 4 * (((t - u * B) / 2) * ((t + u * B) / 2)) =
      (t - u * B) * (t + u * B) := by
    calc
      _ = (2 * ((t - u * B) / 2)) * (2 * ((t + u * B) / 2)) := by ring
      _ = _ := by rw [ha, hd]
  nlinarith [hD]

theorem integerRepresentative_form {t m u A B C : ℤ}
    (hD : t ^ 2 - 4 * m = u ^ 2 * (B ^ 2 - 4 * A * C)) (x y : ℤ) :
    matrixQuadratic (integerRepresentative t u A B C) x y =
      u * (A * x ^ 2 + B * x * y + C * y ^ 2) := by
  obtain ⟨ha, hd⟩ := representative_diagonal hD
  have hdiff : (t + u * B) / 2 - (t - u * B) / 2 = u * B := by omega
  simp only [matrixQuadratic, integerRepresentative, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hdiff]
  ring

end DepthAspect
