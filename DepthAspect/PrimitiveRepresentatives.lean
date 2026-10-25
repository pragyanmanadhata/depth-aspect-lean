import DepthAspect.ContentReindex
import DepthAspect.MatrixModel

/-!
# Canonical integral matrices from actual primitive quadratic forms

The forms carry their actual integer coefficients, primitive gcd, positivity,
and discriminant. Equation (19) constructs the matrix; all parity, determinant,
and content assertions needed by the trace bounds are proved from that data.
-/
namespace DepthAspect.TraceBounds
open scoped BigOperators

/-- A primitive positive-definite binary quadratic form of negative discriminant D.
For negative D, positivity of A implies positive definiteness. -/
structure PrimitiveForm (D : ℤ) where
  A : ℤ
  B : ℤ
  C : ℤ
  positive : 0 < A
  negative : D < 0
  primitive : Nat.gcd A.natAbs (Nat.gcd B.natAbs C.natAbs) = 1
  discriminant : B ^ 2 - 4 * A * C = D

theorem PrimitiveForm.primitive_at_two {D : ℤ} (f : PrimitiveForm D) :
    Odd f.A ∨ Odd f.B ∨ Odd f.C := by
  by_contra h
  simp only [not_or] at h
  obtain ⟨ha, hb, hc⟩ := h
  have ha2 : 2 ∣ f.A.natAbs := Int.natCast_dvd.mp (Int.not_odd_iff_even.mp ha).two_dvd
  have hb2 : 2 ∣ f.B.natAbs := Int.natCast_dvd.mp (Int.not_odd_iff_even.mp hb).two_dvd
  have hc2 : 2 ∣ f.C.natAbs := Int.natCast_dvd.mp (Int.not_odd_iff_even.mp hc).two_dvd
  have hdiv := Nat.dvd_gcd ha2 (Nat.dvd_gcd hb2 hc2)
  rw [f.primitive] at hdiv
  norm_num at hdiv

def representativeDatum {D : ℤ} (t : ℤ) (u : ℕ) (f : PrimitiveForm D) : ContentDatum where
  matrix := integerRepresentative t (u : ℤ) f.A f.B f.C
  weight := 0
  A := f.A
  B := f.B
  C := f.C

/-- Every actual primitive form at D/u² supplies the matrix premises in the
literal content trace. None of these internal matrix conclusions is assumed. -/
theorem representativeDatum_valid (t m : ℤ) (hm : Odd m) (u : ℕ)
    (hu : (u : ℤ) ^ 2 ∣ t ^ 2 - 4 * m)
    (f : PrimitiveForm ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2)) :
    IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (representativeDatum t u f) := by
  have hD : t ^ 2 - 4 * m = (u : ℤ) ^ 2 * (f.B ^ 2 - 4 * f.A * f.C) := by
    rw [f.discriminant, mul_comm ((u : ℤ) ^ 2), Int.ediv_mul_cancel hu]
  obtain ⟨hminus, hplus⟩ := representative_diagonal hD
  refine ⟨?_, f.primitive_at_two, ?_, ?_, ?_, ?_⟩
  · change Odd (Matrix.det (integerRepresentative t (u : ℤ) f.A f.B f.C))
    rwa [integerRepresentative_det hD]
  · simp [representativeDatum, integerRepresentative]
  · change (t + (u : ℤ) * f.B) / 2 - (t - (u : ℤ) * f.B) / 2 = (u : ℤ) * f.B
    omega
  · simp [representativeDatum, integerRepresentative]
  · change (Matrix.trace (integerRepresentative t (u : ℤ) f.A f.B f.C)) ^ 2 -
      4 * Matrix.det (integerRepresentative t (u : ℤ) f.A f.B f.C) = t ^ 2 - 4 * m
    rw [integerRepresentative_trace hD, integerRepresentative_det hD]

/-- The actual representative has the prescribed trace and determinant. -/
theorem representativeDatum_trace_det (t m : ℤ) (u : ℕ)
    (hu : (u : ℤ) ^ 2 ∣ t ^ 2 - 4 * m)
    (f : PrimitiveForm ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2)) :
    Matrix.trace (representativeDatum t u f).matrix = t ∧
      Matrix.det (representativeDatum t u f).matrix = m := by
  have hD : t ^ 2 - 4 * m = (u : ℤ) ^ 2 * (f.B ^ 2 - 4 * f.A * f.C) := by
    rw [f.discriminant, mul_comm ((u : ℤ) ^ 2), Int.ediv_mul_cancel hu]
  exact ⟨integerRepresentative_trace hD, integerRepresentative_det hD⟩

/-- A nonzero sum over a finite class family has a primitive representative.
This is the only existence fact needed from the weighted-class definition of h₀. -/
theorem primitiveForm_exists_of_nonzero_class_sum {D : ℤ} {ι : Type*} [Fintype ι]
    (form : ι → PrimitiveForm D) (weight : ι → ℝ) (h : (∑ i, weight i) ≠ 0) :
    Nonempty (PrimitiveForm D) := by
  classical
  obtain ⟨i, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨form i⟩

/-- The literal primitive class weight 2h(D)/w(D), for a supplied finite
class family with its automorphism count. -/
noncomputable def primitiveClassWeight (ι : Type*) [Fintype ι] (w : ℕ) : ℝ :=
  2 * (Fintype.card ι : ℝ) / (w : ℝ)

theorem primitiveClassWeight_nonneg (ι : Type*) [Fintype ι] (w : ℕ) :
    0 ≤ primitiveClassWeight ι w := by
  unfold primitiveClassWeight
  positivity

/-- The representative-existence input used below follows directly from the
literal finite-class definition when its primitive weight is nonzero. -/
theorem primitiveForm_of_nonzero_class_weight {D : ℤ} (ι : Type*) [Fintype ι]
    (w : ℕ) (form : ι → PrimitiveForm D) (h : primitiveClassWeight ι w ≠ 0) :
    Nonempty (PrimitiveForm D) := by
  classical
  have hi : Nonempty ι := by
    by_contra he
    haveI : IsEmpty ι := not_nonempty_iff.mp he
    simp [primitiveClassWeight] at h
  exact ⟨form (Classical.choice hi)⟩

/-- Select an actual primitive form only at a nonzero admissible class weight.
All inactive slots are harmless zero data. -/
noncomputable def selectedRepresentative (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m t : ℤ) (u : ℕ) : ContentDatum :=
  if h : t ^ 2 < 4 * m ∧ u ∈ positiveSquareContents (t ^ 2 - 4 * m) ∧
      h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0 then
    let hD : t ^ 2 - 4 * m < 0 := by omega
    let hu := (mem_positiveSquareContents (t ^ 2 - 4 * m) hD.ne u).mp h.2.1
    representativeDatum t u (Classical.choice (hforms _
      (negative_discriminant_quotient _ hD u hu.1 hu.2) h.2.2))
  else ⟨0, 0, 0, 0, 0⟩

/-- The representative condition in the full literal trace bound is therefore
proved from actual primitive forms, rather than requiring the local matrix
identities as additional assumptions. -/
theorem selectedRepresentative_valid (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m : ℤ) (hm : Odd m) (t : ℤ) (ht : t ^ 2 < 4 * m) (u : ℕ)
    (hu : u ∈ positiveSquareContents (t ^ 2 - 4 * m))
    (hw : h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0) :
    IsPrimitiveContentMatrix u (t ^ 2 - 4 * m) (selectedRepresentative h₀ hforms m t u) := by
  unfold selectedRepresentative
  rw [dif_pos ⟨ht, hu, hw⟩]
  apply representativeDatum_valid t m hm u
  exact ((mem_positiveSquareContents _ (by omega) u).mp hu).2

/-- The matrix/discriminant hypotheses of the general local interpretation
are derived for the selected primitive representative. -/
theorem selectedRepresentative_trace_det (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (m t : ℤ) (ht : t ^ 2 < 4 * m) (u : ℕ)
    (hu : u ∈ positiveSquareContents (t ^ 2 - 4 * m))
    (hw : h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0) :
    Matrix.trace (selectedRepresentative h₀ hforms m t u).matrix = t ∧
      Matrix.det (selectedRepresentative h₀ hforms m t u).matrix = m := by
  unfold selectedRepresentative
  rw [dif_pos ⟨ht, hu, hw⟩]
  apply representativeDatum_trace_det t m u
  exact ((mem_positiveSquareContents _ (by omega) u).mp hu).2

end DepthAspect.TraceBounds
