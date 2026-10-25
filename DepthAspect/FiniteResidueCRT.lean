import DepthAspect.FiniteCharacterFourier
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Actual reduced-residue averages and the Chinese remainder theorem

The principal coefficient of a product of local functions is computed by the
canonical Chinese remainder equivalence of unit groups. No local mean or
factorization of an average is assumed.
-/
noncomputable section
open scoped BigOperators
namespace DepthAspect.FiniteResidueCRT

variable {ι : Type*} [Fintype ι] (a : ι → ℕ)
variable [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]

/-- The literal CRT equivalence on the groups of reduced residue classes. -/
def unitsCRT (hc : Pairwise fun i j => Nat.Coprime (a i) (a j)) :
    (ZMod (∏ i, a i))ˣ ≃* ∀ i, (ZMod (a i))ˣ :=
  (Units.mapEquiv (ZMod.prodEquivPi a hc).toMulEquiv).trans MulEquiv.piUnits

 theorem unitsCRT_apply (hc : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (x : (ZMod (∏ i, a i))ˣ) (i : ι) :
    unitsCRT a hc x i = ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x := by
  apply Units.ext
  change ZMod.prodEquivPi a hc (x : ZMod (∏ i, a i)) i =
    ZMod.castHom (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
      (ZMod (a i)) (x : ZMod (∏ i, a i))
  exact ZMod.prodEquivPi_apply a hc (x : ZMod (∏ i, a i)) i

 theorem sum_product (hc : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (g : ∀ i, (ZMod (a i))ˣ → ℂ) :
    (∑ x : (ZMod (∏ i, a i))ˣ,
      ∏ i, g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x)) =
      ∏ i, ∑ x : (ZMod (a i))ˣ, g i x := by
  classical
  calc
    _ = ∑ x : (ZMod (∏ i, a i))ˣ, ∏ i, g i (unitsCRT a hc x i) := by
      simp only [unitsCRT_apply]
    _ = ∑ x : ∀ i, (ZMod (a i))ˣ, ∏ i, g i (x i) :=
      Equiv.sum_comp (unitsCRT a hc).toEquiv (fun x : ∀ i, (ZMod (a i))ˣ => ∏ i, g i (x i))
    _ = _ := (Fintype.prod_sum g).symm

 theorem card_units_product (hc : Pairwise fun i j => Nat.Coprime (a i) (a j)) :
    Fintype.card (ZMod (∏ i, a i))ˣ = ∏ i, Fintype.card (ZMod (a i))ˣ := by
  classical
  rw [Fintype.card_congr (unitsCRT a hc).toEquiv, Fintype.card_pi]

/-- The exact principal-coefficient factorization used in (81)–(84), including
local factors whose degree-zero average is not one. -/
theorem principal_product (hc : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (g : ∀ i, (ZMod (a i))ˣ → ℂ) :
    FiniteCharacterFourier.coefficient
      (fun x : (ZMod (∏ i, a i))ˣ =>
        ∏ i, g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x)) 1 =
      ∏ i, FiniteCharacterFourier.coefficient (g i) 1 := by
  classical
  simp only [FiniteCharacterFourier.coefficient_principal]
  rw [sum_product a hc, card_units_product a hc, Nat.cast_prod, Finset.prod_div_distrib]

/-- The actual product coefficient norm has the upper bound needed for (97).
The local functions are inflated by the canonical reduction maps. -/
theorem beta_product_le (g : ∀ i, (ZMod (a i))ˣ → ℂ) :
    FiniteCharacterFourier.beta
      (fun x : (ZMod (∏ i, a i))ˣ =>
        ∏ i, g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x)) ≤
      ∏ i, FiniteCharacterFourier.beta (g i) := by
  classical
  have h := FiniteCharacterFourier.beta_prod Finset.univ
    (fun i x => g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x))
  simpa only [FiniteCharacterFourier.beta_inflation] using h

end DepthAspect.FiniteResidueCRT

noncomputable section
open scoped BigOperators
namespace DepthAspect.FiniteResidueCRT

variable {ι : Type*} [Fintype ι] (a : ι → ℕ)
variable [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]

/-- The actual product of the local characters, inflated by reduction. -/
def tensorCharacter (χ : ∀ i, DirichletCharacter ℂ (a i)) :
    DirichletCharacter ℂ (∏ i, a i) :=
  ∏ i, (χ i).changeLevel (Finset.dvd_prod_of_mem a (Finset.mem_univ i))

private theorem character_prod_apply {q : ℕ} {κ : Type*} (s : Finset κ)
    (χ : κ → DirichletCharacter ℂ q) (x : (ZMod q)ˣ) :
    (∏ i ∈ s, χ i) (x : ZMod q) = ∏ i ∈ s, χ i (x : ZMod q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, MulChar.mul_apply, ih]

theorem tensorCharacter_apply (χ : ∀ i, DirichletCharacter ℂ (a i))
    (x : (ZMod (∏ i, a i))ˣ) :
    tensorCharacter a χ x =
      ∏ i, χ i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x) := by
  rw [tensorCharacter, character_prod_apply]
  apply Finset.prod_congr rfl
  intro i hi
  simp [DirichletCharacter.changeLevel_def]

theorem tensorCharacter_apply_crt (hc : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (χ : ∀ i, DirichletCharacter ℂ (a i)) (x : ∀ i, (ZMod (a i))ˣ) :
    tensorCharacter a χ ((unitsCRT a hc).symm x) = ∏ i, χ i (x i) := by
  rw [tensorCharacter_apply]
  simp only [← unitsCRT_apply a hc, MulEquiv.apply_symm_apply]

/-- CRT makes the products of local characters distinct. -/
theorem tensorCharacter_injective (hc : Pairwise fun i j => Nat.Coprime (a i) (a j)) :
    Function.Injective (tensorCharacter a) := by
  classical
  intro χ ν heq
  funext i
  apply MulChar.ext
  intro x
  have h := congrArg (fun ξ : DirichletCharacter ℂ (∏ i, a i) =>
    ξ ((unitsCRT a hc).symm (Pi.mulSingle i x))) heq
  have heval (θ : ∀ j, DirichletCharacter ℂ (a j)) :
      (∏ j, θ j (↑(Pi.mulSingle (M := fun k => (ZMod (a k))ˣ) i x j) : ZMod (a j))) = θ i x := by
    calc
      _ = ∏ j, if j = i then θ i x else 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j; simp
        · simp [Pi.mulSingle, hji, Ne.symm hji]
      _ = _ := by simp
  simpa only [tensorCharacter_apply_crt, heval] using h

/-- The Fourier coefficient itself factors across the actual CRT factors. -/
theorem coefficient_product (hc : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (g : ∀ i, (ZMod (a i))ˣ → ℂ) (χ : ∀ i, DirichletCharacter ℂ (a i)) :
    FiniteCharacterFourier.coefficient
      (fun x : (ZMod (∏ i, a i))ˣ =>
        ∏ i, g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x))
      (tensorCharacter a χ) =
        ∏ i, FiniteCharacterFourier.coefficient (g i) (χ i) := by
  classical
  unfold FiniteCharacterFourier.coefficient
  simp only [tensorCharacter_apply, map_prod, ← Finset.prod_mul_distrib]
  rw [sum_product a hc (fun i x => g i x * (starRingEnd ℂ) (χ i x)),
    card_units_product a hc, Nat.cast_prod, Finset.prod_div_distrib]

/-- The exact norm factorization asserted after (93), not merely its upper bound. -/
theorem beta_product (hc : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (g : ∀ i, (ZMod (a i))ˣ → ℂ) :
    FiniteCharacterFourier.beta
      (fun x : (ZMod (∏ i, a i))ˣ =>
        ∏ i, g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x)) =
      ∏ i, FiniteCharacterFourier.beta (g i) := by
  classical
  apply le_antisymm (beta_product_le a g)
  let G : (ZMod (∏ i, a i))ˣ → ℂ := fun x =>
    ∏ i, g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x)
  calc
    _ = ∑ χ : ∀ i, DirichletCharacter ℂ (a i),
        ∏ i, ‖FiniteCharacterFourier.coefficient (g i) (χ i)‖ := by
      exact Fintype.prod_sum _
    _ = ∑ χ : ∀ i, DirichletCharacter ℂ (a i),
        ‖FiniteCharacterFourier.coefficient G (tensorCharacter a χ)‖ := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [show G = (fun x : (ZMod (∏ i, a i))ˣ =>
        ∏ i, g i (ZMod.unitsMap (Finset.dvd_prod_of_mem a (Finset.mem_univ i)) x)) from rfl,
        coefficient_product a hc, norm_prod]
    _ = ∑ ν ∈ Finset.univ.image (tensorCharacter a),
        ‖FiniteCharacterFourier.coefficient G ν‖ := by
      rw [Finset.sum_image]
      exact fun x hx y hy h => tensorCharacter_injective a hc h
    _ ≤ ∑ ν : DirichletCharacter ℂ (∏ i, a i),
        ‖FiniteCharacterFourier.coefficient G ν‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => norm_nonneg _)
    _ = _ := rfl

end DepthAspect.FiniteResidueCRT

noncomputable section
open scoped BigOperators
namespace DepthAspect.FiniteResidueCRT

/-- Transport the actual CRT product average to an equal named modulus. The
reduction proofs are immaterial; no new average identity is assumed. -/
theorem principal_product_at_modulus {ι : Type*} [Fintype ι] (a : ι → ℕ)
    [∀ i, NeZero (a i)] [NeZero (∏ i, a i)]
    (hc : Pairwise fun i j => Nat.Coprime (a i) (a j))
    (Q : ℕ) [NeZero Q] (heq : (∏ i, a i) = Q) (hdiv : ∀ i, a i ∣ Q)
    (g : ∀ i, (ZMod (a i))ˣ → ℂ) :
    FiniteCharacterFourier.coefficient
      (fun x : (ZMod Q)ˣ => ∏ i, g i (ZMod.unitsMap (hdiv i) x)) 1 =
        ∏ i, FiniteCharacterFourier.coefficient (g i) 1 := by
  subst Q
  simpa using principal_product a hc g

end DepthAspect.FiniteResidueCRT
