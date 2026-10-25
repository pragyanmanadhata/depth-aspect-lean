import DepthAspect.DyadicClassScaling
import DepthAspect.DyadicRamanujan

/-!
# Class-number collapse of the four prime trace strata

The input is the cited general class-number identity, together with the
actual fundamental character and positive conductor. The geometric class
number differences and the Ramanujan sums are proved in imported modules.
Thus these are conclusions (78) and (80), not additional trace assumptions.
-/
namespace DepthAspect.SignedSieve
open DyadicClassScaling DyadicRamanujan

/-- Equation (78), with n=2a+4 and q=2^(a+2). -/
theorem even_class_strata_collapse {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-(q : ℤ) * (f : ℤ) ^ 2) = classValue χ hχ hq f hf)
    (f : ℕ) (hf : 0 < f) (a : ℕ) (t : ℤ) (α : ℝ)
    (hα : χ (2 : ZMod q) = (α : ℂ)) :
    (if (2 : ℤ) ^ (a + 1) ∣ t then
      ((H ((4 : ℤ) ^ (a + 1) * (-(q : ℤ) * (f : ℤ) ^ 2)) -
        H ((4 : ℤ) ^ a * (-(q : ℤ) * (f : ℤ) ^ 2)) : ℝ) : ℂ) else 0) -
    (if (2 : ℤ) ^ (a + 2) ∣ t then
      ((H ((4 : ℤ) ^ (a + 2) * (-(q : ℤ) * (f : ℤ) ^ 2)) -
        H ((4 : ℤ) ^ (a + 1) * (-(q : ℤ) * (f : ℤ) ^ 2)) : ℝ) : ℂ) else 0) =
      -ramanujanTwoPow (a + 1) t / 2 *
        ((H (4 * (-(q : ℤ) * (f : ℤ) ^ 2)) -
          H (-(q : ℤ) * (f : ℤ) ^ 2) : ℝ) : ℂ) := by
  rw [hurwitz_four_pow_difference χ hχ hq H hformula f hf a α hα,
    show a + 2 = (a + 1) + 1 by omega,
    hurwitz_four_pow_difference χ hχ hq H hformula f hf (a + 1) α hα,
    ramanujanTwoPow_formula]
  split_ifs <;> push_cast <;> simp only [pow_succ] <;> ring

/-- Equation (80)'s first class-number equality, with n=2a+5 and
Q=2^(a+3). The extra factor 1/2 comes from the actual odd-depth scale. -/
theorem odd_class_strata_collapse {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-(q : ℤ) * (f : ℤ) ^ 2) = classValue χ hχ hq f hf)
    (f : ℕ) (hf : 0 < f) (a : ℕ) (t : ℤ) (α : ℝ)
    (hα : χ (2 : ZMod q) = (α : ℂ)) :
    (if (2 : ℤ) ^ (a + 2) ∣ t then
      ((H ((4 : ℤ) ^ (a + 1) * (-(q : ℤ) * (f : ℤ) ^ 2)) -
        H ((4 : ℤ) ^ a * (-(q : ℤ) * (f : ℤ) ^ 2)) : ℝ) : ℂ) else 0) -
    (if (2 : ℤ) ^ (a + 3) ∣ t then
      ((H ((4 : ℤ) ^ (a + 2) * (-(q : ℤ) * (f : ℤ) ^ 2)) -
        H ((4 : ℤ) ^ (a + 1) * (-(q : ℤ) * (f : ℤ) ^ 2)) : ℝ) : ℂ) else 0) =
      -ramanujanTwoPow (a + 2) t / 4 *
        ((H (4 * (-(q : ℤ) * (f : ℤ) ^ 2)) -
          H (-(q : ℤ) * (f : ℤ) ^ 2) : ℝ) : ℂ) := by
  rw [hurwitz_four_pow_difference χ hχ hq H hformula f hf a α hα,
    show a + 2 = (a + 1) + 1 by omega,
    hurwitz_four_pow_difference χ hχ hq H hformula f hf (a + 1) α hα,
    ramanujanTwoPow_formula]
  simp only [show a + 1 + 1 + 1 = a + 3 by omega]
  split_ifs <;> push_cast <;> simp only [pow_succ] <;> ring

end DepthAspect.SignedSieve
