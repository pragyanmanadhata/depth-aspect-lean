import DepthAspect.FixedLines
import DepthAspect.MatrixModel
import DepthAspect.QuadraticForms

/-!
# Local cancellation for actual fixed projective lines

An integer matrix of odd determinant acts invertibly on the dyadic residue
ring. Its fixed lines are counted in the actual unit-orbit quotient, and the
count agrees with the quadratic-form count used in the local proof.
-/
namespace DepthAspect.DyadicFixedLines

open ProjectiveCharts FixedLines
open scoped Classical

/-- Reduce every entry of an integer matrix modulo the dyadic level. -/
def residueMatrix (h : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) (ZMod (2 ^ h)) :=
  fun i j => (M i j : ZMod (2 ^ h))

/-- The determinant commutes with reduction modulo the level. -/
theorem residueMatrix_det (h : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix.det (residueMatrix h M) = ((Matrix.det M : ℤ) : ZMod (2 ^ h)) := by
  simp only [Matrix.det_fin_two, residueMatrix, Int.cast_sub, Int.cast_mul]

/-- Odd determinant supplies the unit determinant needed by the fixed-line theorem. -/
theorem residueMatrix_det_unit (h : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : Odd (Matrix.det M)) : IsUnit (Matrix.det (residueMatrix h M)) := by
  rw [residueMatrix_det]
  exact QuadraticForms.odd_isUnit_dyadic hdet h

/-- Count the lines actually fixed by the reduced matrix. -/
noncomputable def fixedLineCount (h : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Fintype.card {p : ProjectiveLine (ZMod (2 ^ h)) // IsFixed (residueMatrix h M) p}

/-- Fixed lines and roots of the associated matrix quadratic have the same count. -/
theorem fixedLineCount_eq_rootCount (h : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : Odd (Matrix.det M)) :
    fixedLineCount h M = dyadicRootCount h (M 1 0) (M 1 1 - M 0 0) (-M 0 1) := by
  unfold fixedLineCount dyadicRootCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro p
  simpa only [Equiv.refl_apply, residueMatrix, Int.cast_sub, Int.cast_neg] using
    isFixed_iff_isRoot (residueMatrix h M) (residueMatrix_det_unit h M hdet) p

/-- The fixed-line count is the two-chart count appearing in Section 3. -/
theorem fixedLineCount_eq_rho (h : ℕ) (hh : 1 ≤ h)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : Odd (Matrix.det M)) :
    fixedLineCount h M = ContentReduction.rho h (M 1 0) (M 1 1 - M 0 0) (-M 0 1) := by
  rw [fixedLineCount_eq_rootCount h M hdet]
  exact dyadic_projective_root_card h hh _ _ _

/-- Lemma 3.1 for actual fixed projective lines of a matrix. The discriminant
hypothesis is stated directly using the matrix trace and determinant. -/
theorem fixedLineCount_local_cancellation (n e : ℕ) (hn : 3 ≤ n)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : Odd (Matrix.det M))
    (A B C : ℤ) (hprim : Odd A ∨ Odd B ∨ Odd C)
    (hA : M 1 0 = 2 ^ e * A)
    (hB : M 1 1 - M 0 0 = 2 ^ e * B)
    (hC : -M 0 1 = 2 ^ e * C)
    (hbad : ¬ (2 : ℤ) ^ (n + e - 2) ∣
      (Matrix.trace M) ^ 2 - 4 * Matrix.det M) :
    (fixedLineCount n M : ℤ) - 2 * (fixedLineCount (n - 1) M : ℤ) +
      (fixedLineCount (n - 2) M : ℤ) = 0 := by
  rw [fixedLineCount_eq_rho n (by omega) M hdet,
    fixedLineCount_eq_rho (n - 1) (by omega) M hdet,
    fixedLineCount_eq_rho (n - 2) (by omega) M hdet, hA, hB, hC]
  have hdisc : ((2 : ℤ) ^ e * B) ^ 2 -
      4 * ((2 : ℤ) ^ e * A) * ((2 : ℤ) ^ e * C) =
      (Matrix.trace M) ^ 2 - 4 * Matrix.det M := by
    rw [← hA, ← hB, ← hC]
    exact matrixQuadratic_discriminant M
  exact LocalCancellation.local_cancellation n e (by omega) A B C hprim
    (by rwa [hdisc])

/-- Extract the exact common power of two from three coefficients. A
nondivisible discriminant ensures that the coefficients are not all zero;
the least failed divisibility exponent supplies the primitive residual triple. -/
theorem exists_primitive_two_content (r : ℕ) (a b c : ℤ)
    (hbad : ¬ (2 : ℤ) ^ r ∣ b ^ 2 - 4 * a * c) :
    ∃ e : ℕ, ∃ A B C : ℤ, (Odd A ∨ Odd B ∨ Odd C) ∧
      a = 2 ^ e * A ∧ b = 2 ^ e * B ∧ c = 2 ^ e * C := by
  let P : ℕ → Prop := fun j =>
    (2 : ℤ) ^ j ∣ a ∧ (2 : ℤ) ^ j ∣ b ∧ (2 : ℤ) ^ j ∣ c
  have h0 : P 0 := by simp [P]
  have hex : ∃ j, ¬ P j := by
    refine ⟨r, ?_⟩
    rintro ⟨ha, hb, _⟩
    apply hbad
    have hpoly : b ^ 2 - 4 * a * c = b * b - (4 * c) * a := by ring
    rw [hpoly]
    exact dvd_sub (dvd_mul_of_dvd_left hb b) (dvd_mul_of_dvd_right ha (4 * c))
  let k := Nat.find hex
  have hspec : ¬ P k := Nat.find_spec hex
  have hk : 0 < k := by
    by_contra h
    have heq : k = 0 := by omega
    exact hspec (by simpa only [heq] using h0)
  let e := k - 1
  have hek : e < k := by dsimp [e]; omega
  have he : P e := by
    by_contra h
    exact Nat.find_min hex hek h
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩⟩ := he
  refine ⟨e, A, B, C, ?_, hA, hB, hC⟩
  by_contra hprim
  push Not at hprim
  obtain ⟨a', ha'⟩ := (Int.not_odd_iff_even.mp hprim.1).two_dvd
  obtain ⟨b', hb'⟩ := (Int.not_odd_iff_even.mp hprim.2.1).two_dvd
  obtain ⟨c', hc'⟩ := (Int.not_odd_iff_even.mp hprim.2.2).two_dvd
  apply hspec
  have hke : k = e + 1 := by dsimp [e]; omega
  change (2 : ℤ) ^ k ∣ a ∧ (2 : ℤ) ^ k ∣ b ∧ (2 : ℤ) ^ k ∣ c
  rw [hke, pow_succ]
  refine ⟨⟨a', ?_⟩, ⟨b', ?_⟩, ⟨c', ?_⟩⟩
  · rw [hA, ha']; ring
  · rw [hB, hb']; ring
  · rw [hC, hc']; ring

/-- The fixed-line second difference is supported on the original matrix
discriminant congruence. There are no content or primitive-coefficient
hypotheses: their witnesses are constructed inside the proof. -/
theorem fixedLineCount_discriminant_support (n : ℕ) (hn : 3 ≤ n)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : Odd (Matrix.det M))
    (hbad : ¬ (2 : ℤ) ^ (n - 2) ∣
      (Matrix.trace M) ^ 2 - 4 * Matrix.det M) :
    (fixedLineCount n M : ℤ) - 2 * (fixedLineCount (n - 1) M : ℤ) +
      (fixedLineCount (n - 2) M : ℤ) = 0 := by
  obtain ⟨e, A, B, C, hprim, hA, hB, hC⟩ :=
    exists_primitive_two_content (n - 2) (M 1 0) (M 1 1 - M 0 0) (-M 0 1)
      (by rwa [matrixQuadratic_discriminant])
  apply fixedLineCount_local_cancellation n e hn M hdet A B C hprim hA hB hC
  intro h
  exact hbad ((pow_dvd_pow (2 : ℤ) (by omega : n - 2 ≤ n + e - 2)).trans h)

/-- Any finite weighted class sum of these actual fixed-line terms has the
same discriminant support. This statement imposes no content decomposition. -/
theorem weighted_fixedLineCount_support {ι R : Type*} [CommRing R]
    (s : Finset ι) (w : ι → R) (M : ι → Matrix (Fin 2) (Fin 2) ℤ)
    (n : ℕ) (hn : 3 ≤ n) (D : ℤ)
    (hdet : ∀ i ∈ s, Odd (Matrix.det (M i)))
    (hD : ∀ i ∈ s, (Matrix.trace (M i)) ^ 2 - 4 * Matrix.det (M i) = D)
    (hbad : ¬ (2 : ℤ) ^ (n - 2) ∣ D) :
    (s.sum fun i => w i * (((fixedLineCount n (M i) : ℤ) -
      2 * (fixedLineCount (n - 1) (M i) : ℤ) +
      (fixedLineCount (n - 2) (M i) : ℤ) : ℤ) : R)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hz := fixedLineCount_discriminant_support n hn (M i) (hdet i hi)
    (by rwa [hD i hi])
  rw [hz, Int.cast_zero, mul_zero]

end DepthAspect.DyadicFixedLines
