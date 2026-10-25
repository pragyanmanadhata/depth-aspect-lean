import DepthAspect.FiniteCharacterTranslation
import Mathlib.Algebra.Group.Subgroup.Defs

/-! The arbitrary subgroup-coset assertion following (93). The proof uses
the actual coefficient transform, its translation identity and inversion.
No identification of an arbitrary quotient with a residue unit group is used. -/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace DepthAspect.FourierCosets
open FiniteCharacterFourier FiniteCharacterTranslation
variable {q : ℕ} [NeZero q]

def subgroupIndicator (H : Subgroup (ZMod q)ˣ) (x : (ZMod q)ˣ) : ℂ :=
  if x ∈ H then 1 else 0

theorem subgroupIndicator_translate (H : Subgroup (ZMod q)ˣ)
    {u : (ZMod q)ˣ} (hu : u ∈ H) :
    (fun x => subgroupIndicator H (u * x)) = subgroupIndicator H := by
  funext x
  simp only [subgroupIndicator, H.mul_mem_cancel_left hu]

theorem coefficient_subgroup_zero (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) {u : (ZMod q)ˣ}
    (hu : u ∈ H) (hχ : χ u ≠ 1) : coefficient (subgroupIndicator H) χ = 0 := by
  have h := coefficient_translate_relation (subgroupIndicator H) u χ
  rw [subgroupIndicator_translate H hu] at h
  have hc : conj (χ u) ≠ 1 := by
    intro he
    apply hχ
    simpa using congrArg conj he
  have hz : (conj (χ u) - 1) * coefficient (subgroupIndicator H) χ = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)

/-- A subgroup indicator has nonnegative real Fourier coefficients. -/
theorem norm_coefficient_subgroup_eq_re (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) :
    ‖coefficient (subgroupIndicator H) χ‖ =
      (coefficient (subgroupIndicator H) χ).re := by
  by_cases h : ∀ u ∈ H, χ u = 1
  · have he : coefficient (subgroupIndicator H) χ =
        (((Finset.univ.filter (fun x : (ZMod q)ˣ => x ∈ H)).card : ℂ) /
          (Fintype.card (ZMod q)ˣ : ℂ)) := by
      unfold coefficient
      congr 1
      calc
        _ = ∑ x : (ZMod q)ˣ, if x ∈ H then (1 : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxH : x ∈ H
          · simp [subgroupIndicator, hxH, h x hxH]
          · simp [subgroupIndicator, hxH]
        _ = _ := by simp
    have hr : coefficient (subgroupIndicator H) χ =
        (((Finset.univ.filter (fun x : (ZMod q)ˣ => x ∈ H)).card : ℝ) /
          (Fintype.card (ZMod q)ˣ : ℝ) : ℝ) := by
      rw [he]
      push_cast <;> rfl
    rw [hr, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re,
      abs_of_nonneg (by positivity)]
  · push_neg at h
    obtain ⟨u, hu, hχ⟩ := h
    rw [coefficient_subgroup_zero H χ hu hχ]
    simp

theorem beta_subgroup (H : Subgroup (ZMod q)ˣ) :
    beta (subgroupIndicator H) = 1 := by
  have hsum : (∑ χ : DirichletCharacter ℂ q,
      coefficient (subgroupIndicator H) χ) = 1 := by
    simpa [subgroupIndicator] using inversion (subgroupIndicator H) 1
  calc
    beta (subgroupIndicator H) =
        (∑ χ : DirichletCharacter ℂ q, coefficient (subgroupIndicator H) χ).re := by
      simp only [beta, norm_coefficient_subgroup_eq_re, Complex.re_sum]
    _ = 1 := by rw [hsum]; rfl

/-- The indicator of any left coset of any subgroup has coefficient norm one. -/
theorem beta_coset (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) :
    beta (fun x : (ZMod q)ˣ => if a⁻¹ * x ∈ H then (1 : ℂ) else 0) = 1 := by
  change beta (fun x => subgroupIndicator H (a⁻¹ * x)) = 1
  rw [beta_translate, beta_subgroup]

end DepthAspect.FourierCosets
