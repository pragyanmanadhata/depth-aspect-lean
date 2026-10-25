import DepthAspect.OddDiscriminantValues
import DepthAspect.ClassNumberGrowth
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Reality of the actual quadratic imprimitive L-value

The defining prime-symbol identities imply reality at every natural
argument by multiplicative induction. The ordered-series limit preserves
reality, so the prime trace formulas can use the actual complex L-value
rather than silently replacing it by its real part.
-/
namespace DepthAspect.OddDiscriminantValues
open ImprimitiveCharacter ClassNumberGrowth OrderedDirichlet
open scoped BigOperators Topology

theorem QuadraticCharacterData.nat_value_im {d : ℤ} (χ : QuadraticCharacterData d)
    (n : ℕ) : (χ.character (n : ZMod d.natAbs)).im = 0 := by
  induction n using Nat.recOnMul with
  | zero =>
    have hs : χ.character (0 : ZMod d.natAbs) * χ.character 0 = χ.character 0 := by
      rw [← map_mul, mul_zero]
    have hp : χ.character (0 : ZMod d.natAbs) * (χ.character 0 - 1) = 0 := by
      calc
        _ = χ.character (0 : ZMod d.natAbs) * χ.character 0 - χ.character 0 := by ring
        _ = 0 := by rw [hs]; ring
    rcases mul_eq_zero.mp hp with hz | hz
    · simp [hz]
    · have hone : χ.character (0 : ZMod d.natAbs) = 1 := sub_eq_zero.mp hz
      simp [hone]
  | one => simp
  | prime p hp =>
    by_cases hp2 : p = 2
    · subst p
      simp only [Nat.cast_ofNat]
      rw [χ.two_value]
      simp
    · rw [χ.odd_prime_value p hp hp2]
      simp
  | mul a b ha hb =>
    simp only [Nat.cast_mul, map_mul, Complex.mul_im, ha, hb, mul_zero, zero_mul, add_zero]

theorem QuadraticCharacterData.psiNat_im {d : ℤ} (χ : QuadraticCharacterData d)
    (f n : ℕ) : (psiNat χ.character f n).im = 0 := by
  rw [psiNat_eq]
  exact χ.nat_value_im _

theorem QuadraticCharacterData.partialL_im {d : ℤ} (χ : QuadraticCharacterData d)
    (f n : ℕ) : (partialL (psiNat χ.character f) n).im = 0 := by
  unfold partialL
  change Complex.imAddGroupHom
    (∑ j ∈ Finset.range n, psiNat χ.character f (j + 1) / ((j : ℂ) + 1)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  change (psiNat χ.character f (j + 1) / ((j : ℂ) + 1)).im = 0
  rw [Complex.div_im]
  simp [χ.psiNat_im]

/-- The actual ordered limit at one is real; no class-number identity is
used in proving this fact. -/
theorem QuadraticCharacterData.LAtOne_im {d : ℤ} (χ : QuadraticCharacterData d)
    (hχ : χ.character.Odd) (hq : 0 < d.natAbs) (f : ℕ) (hf : 0 < f) :
    (imprimitiveLAtOne χ.character hχ hq f hf).im = 0 := by
  have hlim := (Complex.continuous_im.tendsto
    (imprimitiveLAtOne χ.character hχ hq f hf)).comp
      (imprimitiveLAtOne_limit χ.character hχ hq f hf)
  have heq : (fun n => (partialL (psiNat χ.character f) n).im) =
      (fun _ : ℕ => (0 : ℝ)) := funext (χ.partialL_im f)
  change Filter.Tendsto (fun n => (partialL (psiNat χ.character f) n).im)
    Filter.atTop _ at hlim
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem QuadraticCharacterData.LAtOne_ofReal_re {d : ℤ} (χ : QuadraticCharacterData d)
    (hχ : χ.character.Odd) (hq : 0 < d.natAbs) (f : ℕ) (hf : 0 < f) :
    ((imprimitiveLAtOne χ.character hχ hq f hf).re : ℂ) =
      imprimitiveLAtOne χ.character hχ hq f hf := by
  apply Complex.ext
  · simp
  · simp [χ.LAtOne_im hχ hq f hf]

end DepthAspect.OddDiscriminantValues
