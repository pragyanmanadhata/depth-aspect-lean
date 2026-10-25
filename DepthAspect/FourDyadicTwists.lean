import DepthAspect.DyadicLocalMeans
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-! The four actual modulus-eight characters used throughout Section 5. -/
noncomputable section
namespace DepthAspect.FourDyadicTwists

/-- The order is principal, χ−4 inflated to eight, χ8, χ−8. -/
def character (i : Fin 4) : DirichletCharacter ℂ 8 :=
  ![1, DirichletCharacter.changeLevel (by norm_num : 4 ∣ 8)
      (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 4),
    ZMod.χ₈.ringHomComp (Int.castRingHom ℂ),
    ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)] i

/-- Identification with the actual finite character table used to compute
(91). This is restricted to units, as the principal character is zero off units. -/
theorem character_apply_unit (i : Fin 4) (x : (ZMod 8)ˣ) :
    character i x = (DyadicLocalMeans.twistValue i x : ℂ) := by
  fin_cases i
  · simp [character, DyadicLocalMeans.twistValue]
  · change (DirichletCharacter.changeLevel (by norm_num : 4 ∣ 8)
        (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ 4)) x =
      (ZMod.χ₄ (ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) (x : ZMod 8)) : ℂ)
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    rfl
  · rfl
  · rfl

@[simp] theorem character_zero : character 0 = 1 := rfl

 theorem character_norm_le (i : Fin 4) (x : ZMod 8) : ‖character i x‖ ≤ 1 :=
  (character i).norm_le_one x

end DepthAspect.FourDyadicTwists
