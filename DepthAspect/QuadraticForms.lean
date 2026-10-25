import DepthAspect.LocalArithmetic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-!
# Completing the square in the primitive even-middle-coefficient case

The root equivalence below is an actual equivalence of solution sets over
ZMod, not a postulated equality of counts. The even-y projective chart is
also excluded by parity, as in the paragraph preceding (21).
-/

namespace DepthAspect.QuadraticForms

section Ring
variable {R : Type*} [CommRing R]

theorem complete_square (a b c x : R) :
    a * (a * x ^ 2 + 2 * b * x + c) =
      (a * x + b) ^ 2 - (b ^ 2 - a * c) := by ring

theorem complete_square_root_iff (a : Rˣ) (b c x : R) :
    (a : R) * x ^ 2 + 2 * b * x + c = 0 ↔
      ((a : R) * x + b) ^ 2 - (b ^ 2 - (a : R) * c) = 0 := by
  rw [← complete_square]
  exact a.mul_right_eq_zero.symm

def affineEquiv (a : Rˣ) (b : R) : R ≃ R where
  toFun x := (a : R) * x + b
  invFun y := (↑(a⁻¹) : R) * (y - b)
  left_inv x := by simp
  right_inv y := by simp

/-- The change of variables x ↦ a*x+b is a bijection between the
quadratic-form roots and the square roots of its quarter-discriminant. -/
def squareCompletionEquiv (a : Rˣ) (b c : R) :
    {x : R // (a : R) * x ^ 2 + 2 * b * x + c = 0} ≃
      {y : R // y ^ 2 - (b ^ 2 - (a : R) * c) = 0} where
  toFun x := ⟨affineEquiv a b x, (complete_square_root_iff a b c x).mp x.property⟩
  invFun y := ⟨(affineEquiv a b).symm y, (complete_square_root_iff a b c _).mpr (by
    change (affineEquiv a b ((affineEquiv a b).symm y)) ^ 2 -
      (b ^ 2 - (a : R) * c) = 0
    rw [(affineEquiv a b).apply_symm_apply]
    exact y.property)⟩
  left_inv x := Subtype.ext ((affineEquiv a b).symm_apply_apply x)
  right_inv y := Subtype.ext ((affineEquiv a b).apply_symm_apply y)

end Ring

theorem odd_isUnit_dyadic {A : ℤ} (hA : Odd A) (j : ℕ) :
    IsUnit (A : ZMod (2 ^ j)) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime A (2 ^ j)).mpr
  have h := (LocalArithmetic.two_isCoprime_odd hA).pow_left (m := j)
  simpa using h

/-- For odd A the two actual finite root sets have the same cardinality.
Here B=2b and the quarter-discriminant is b²-A*C. -/
theorem dyadic_quadratic_root_card {A : ℤ} (hA : Odd A) (b C : ℤ) (j : ℕ) :
    Fintype.card {x : ZMod (2 ^ j) //
      (A : ZMod (2 ^ j)) * x ^ 2 + 2 * (b : ZMod (2 ^ j)) * x + C = 0} =
    Fintype.card {y : ZMod (2 ^ j) //
      y ^ 2 - ((b : ZMod (2 ^ j)) ^ 2 - (A : ZMod (2 ^ j)) * C) = 0} := by
  classical
  obtain ⟨a, ha⟩ := odd_isUnit_dyadic hA j
  have hc := Fintype.card_congr (squareCompletionEquiv a (b : ZMod (2 ^ j)) (C : ZMod (2 ^ j)))
  simpa only [ha] using hc

/-- If A is odd and B=2b, the chart (1,y) with y even has no roots
at any positive dyadic level. -/
theorem no_even_chart_root {A y : ℤ} (hA : Odd A) (hy : Even y)
    (b C : ℤ) (j : ℕ) :
    ¬ (2 : ℤ) ^ (j + 1) ∣ A + 2 * b * y + C * y ^ 2 := by
  have he : Even (2 * b * y + C * y ^ 2) := by
    obtain ⟨v, hv⟩ := hy
    refine ⟨b * y + 2 * C * v ^ 2, ?_⟩
    rw [hv]
    ring
  have ho : Odd (A + 2 * b * y + C * y ^ 2) := by
    simpa [add_assoc] using hA.add_even he
  intro hdiv
  have htwo : (2 : ℤ) ∣ 2 ^ (j + 1) := dvd_pow_self 2 (by omega)
  exact (Int.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (htwo.trans hdiv))

end DepthAspect.QuadraticForms
