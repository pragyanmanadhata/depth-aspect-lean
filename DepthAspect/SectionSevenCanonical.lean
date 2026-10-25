import DepthAspect.SectionSevenSupport
import DepthAspect.UniformSpectralPrimeBounds
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The actual canonical spectral elliptic term in (136)--(137), with the
internal pointwise trace estimate discharged by the general arithmetic data. -/
namespace DepthAspect.SectionSevenSupport

open TraceBounds UnsignedDensity
open scoped BigOperators BoundedContinuousFunction

/-- Equation (136), using the complete odd-prime set and the literal
canonical primitive-class elliptic expression. -/
noncomputable def canonicalSupportSum {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (n : ℕ) (L a : ℝ) (g : ℝ → ℂ) : ℂ :=
  supportSum L ((primeBases L a).image (fun p : ℕ => (p : ℤ)))
    (fun m => canonicalLiteralElliptic k n (Fintype.card (Family (2 ^ n)) : ℝ)
      m D.primitiveClass D.primitive_forms) g

/-- Equation (137) for the actual elliptic trace, with no internal growth,
pointwise trace, pair count, or prime-average estimate among its inputs. -/
theorem canonicalSupportSum_bound {k : ℕ} {Family V : ℕ → Type*}
    [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]
    (D : ArithmeticSpectralData k Family V) (n : ℕ) (hn : 8 ≤ n)
    {L a δ : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (hδ : 0 < δ) (g : ℝ →ᵇ ℂ) :
    ‖canonicalSupportSum D n L a g‖ ≤
      (48 * a * uniformEllipticConstant δ * Real.sqrt 2 /
        (1 - (2 : ℝ) ^ (-1 - δ))) * ‖g‖ *
          ((2 : ℝ) ^ n) ^ (-(3 / 2 : ℝ)) * (Real.exp (a * L)) ^ (1 + δ) := by
  have hX : 1 ≤ Real.exp (a * L) := Real.one_le_exp_iff.mpr (mul_nonneg ha hL.le)
  have hN : (2 : ℝ) ^ n = 16 * (((2 : ℤ) ^ (n - 4) : ℤ) : ℝ) := by
    push_cast
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 4) + 4) := by congr 1; omega
      _ = 16 * (2 : ℝ) ^ (n - 4) := by rw [pow_add]; norm_num; ring
  unfold canonicalSupportSum
  apply supportSum_bound (q := (2 : ℤ) ^ (n - 4)) hX hL hδ.le ha (uniformEllipticConstant_pos hδ).le
    (norm_nonneg _) (by positivity) hN (le_of_eq (Real.log_exp _))
    ((primeBases L a).image (fun p : ℕ => (p : ℤ))) _ _
  · intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have hmem := Finset.mem_filter.mp hp
    have hupper := (Finset.mem_Icc.mp hmem.1).2
    constructor
    · exact_mod_cast hmem.2.1.one_le
    · simpa only [Int.cast_natCast] using (Nat.le_floor_iff (Real.exp_pos _).le).mp hupper
  · intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp'.1.pos
    have hpodd : Odd (p : ℤ) := by exact_mod_cast hp'.1.odd_of_ne_two hp'.2
    simpa only [neg_div] using canonicalLiteralElliptic_bound k n hn (p : ℤ) hp0 hpodd
      (fun M => (Fintype.card (Family M) : ℝ)) D.dimension_formula D.primitiveClass
      D.hurwitzClass D.primitive_nonneg D.primitive_decomposition
      D.ordered_class_number_formula D.primitive_forms δ hδ
  · intro m _
    exact g.norm_coe_le_norm _

end DepthAspect.SectionSevenSupport
