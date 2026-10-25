import DepthAspect.CoefficientBounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Actual Fourier expansion on the reduced residue classes

All coefficients below are defined by their finite sums. Orthogonality,
inversion, Parseval and the support bound are proved from Mathlib's character
orthogonality. No Fourier identity or coefficient estimate is an input.
-/

open scoped BigOperators ComplexConjugate Classical
open Finset

namespace DepthAspect.FiniteCharacterFourier

noncomputable section

variable {q : ℕ} [NeZero q]

private instance complexRootsOfUnity (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity ℂ n where
  prim := ⟨Complex.exp (2 * Real.pi * Complex.I / n),
    Complex.isPrimitiveRoot_exp n (NeZero.ne n)⟩
  cyc := rootsOfUnity.isCyclic ℂ n

/-- The literal normalized coefficient in (93). -/
def coefficient (g : (ZMod q)ˣ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ x, g x * conj (χ x)) / Fintype.card (ZMod q)ˣ

/-- The coefficient norm of the actual character expansion. -/
def beta (g : (ZMod q)ˣ → ℂ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, ‖coefficient g χ‖

private def asAddChar (χ : DirichletCharacter ℂ q) : AddChar (Additive (ZMod q)ˣ) ℂ where
  toFun x := χ x.toMul
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [map_mul]

private theorem asAddChar_injective :
    Function.Injective (asAddChar (q := q)) := by
  intro χ ν h
  apply MulChar.ext
  intro x
  exact congrArg (fun f : AddChar (Additive (ZMod q)ˣ) ℂ => f (Additive.ofMul x)) h

/-- The transform of a character is its one-point coefficient array. -/
theorem coefficient_character (χ ν : DirichletCharacter ℂ q) :
    coefficient (fun x : (ZMod q)ˣ => χ x) ν = if χ = ν then 1 else 0 := by
  classical
  have h := AddChar.wInner_cWeight_eq_boole (asAddChar ν) (asAddChar χ)
  simp only [asAddChar_injective.eq_iff] at h
  have h' : (∑ x : Additive (ZMod q)ˣ,
      χ x.toMul * conj (ν x.toMul)) / Fintype.card (ZMod q)ˣ =
        if ν = χ then (1 : ℂ) else 0 := by
    simpa only [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
      RCLike.inner_apply, asAddChar, AddChar.coe_mk, Fintype.card_additive] using h
  have he : (∑ x : Additive (ZMod q)ˣ, χ x.toMul * conj (ν x.toMul)) =
      ∑ x : (ZMod q)ˣ, χ x * conj (ν x) :=
    Equiv.sum_comp Additive.toMul (fun x : (ZMod q)ˣ => χ x * conj (ν x))
  rw [he] at h'
  simpa only [coefficient, eq_comm] using h'

private theorem conj_character_unit_inv (χ : DirichletCharacter ℂ q) (x : (ZMod q)ˣ) :
    conj (χ x) = χ ((x⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  rw [← Complex.inv_eq_conj (χ.unit_norm_eq_one x)]
  have h := congrArg (fun z : ℂˣ => (z : ℂ)) (map_inv χ.toUnitHom x)
  simpa only [Units.val_inv_eq_inv_val, MulChar.coe_toUnitHom] using h.symm

private theorem kernel (x y : (ZMod q)ˣ) :
    (∑ χ : DirichletCharacter ℂ q, conj (χ x) * χ y) =
      if x = y then (Fintype.card (ZMod q)ˣ : ℂ) else 0 := by
  classical
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ x.isUnit (y : ZMod q)
  simpa only [conj_character_unit_inv, ZMod.inv_coe_unit,
    Units.val_inj, ZMod.card_units_eq_totient] using h

/-- Fourier inversion on the actual unit group modulo `q`. -/
theorem inversion (g : (ZMod q)ˣ → ℂ) (y : (ZMod q)ˣ) :
    ∑ χ : DirichletCharacter ℂ q, coefficient g χ * χ y = g y := by
  classical
  have hcard : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [coefficient, div_mul_eq_mul_div, ← Finset.sum_div]
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, kernel]
  simp [hcard]

/-- Transforming a finite linear combination can be done term by term. -/
theorem coefficient_sum {ι : Type*} (s : Finset ι)
    (g : ι → (ZMod q)ˣ → ℂ) (χ : DirichletCharacter ℂ q) :
    coefficient (fun x => ∑ i ∈ s, g i x) χ = ∑ i ∈ s, coefficient (g i) χ := by
  classical
  simp only [coefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

 theorem coefficient_mul (c : ℂ) (g : (ZMod q)ˣ → ℂ) (χ : DirichletCharacter ℂ q) :
    coefficient (fun x => c * g x) χ = c * coefficient g χ := by
  simp only [coefficient, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

/-- The coefficients of any character expansion are uniquely determined by the
actual finite average. -/
theorem coefficient_expansion (a : DirichletCharacter ℂ q → ℂ)
    (ν : DirichletCharacter ℂ q) :
    coefficient (fun x => ∑ χ, a χ * χ x) ν = a ν := by
  classical
  rw [coefficient_sum]
  simp only [coefficient_mul, coefficient_character]
  simp

 theorem coefficient_injective : Function.Injective (coefficient (q := q)) := by
  intro g h heq
  funext x
  rw [← inversion g x, ← inversion h x, heq]

/-- Complex-valued Parseval, before taking real parts. -/
theorem parseval_complex (g : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, coefficient g χ * conj (coefficient g χ)) =
      (∑ x : (ZMod q)ˣ, g x * conj (g x)) / Fintype.card (ZMod q)ˣ := by
  classical
  have hconj (χ : DirichletCharacter ℂ q) : conj (coefficient g χ) =
      (∑ x : (ZMod q)ˣ, conj (g x) * χ x) / Fintype.card (ZMod q)ˣ := by
    simp only [coefficient, map_div₀, map_sum, map_mul, Complex.conj_conj, map_natCast]
  calc
    _ = (∑ χ : DirichletCharacter ℂ q,
        ∑ x : (ZMod q)ˣ, conj (g x) * (coefficient g χ * χ x)) /
        Fintype.card (ZMod q)ˣ := by
      simp_rw [hconj]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [← mul_div_assoc, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x : (ZMod q)ˣ, conj (g x) *
        ∑ χ : DirichletCharacter ℂ q, coefficient g χ * χ x) /
        Fintype.card (ZMod q)ˣ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by simp only [inversion, mul_comm]

/-- Normalized Parseval for the coefficients defined above. -/
theorem parseval (g : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖coefficient g χ‖ ^ 2) =
      (∑ x : (ZMod q)ˣ, ‖g x‖ ^ 2) / Fintype.card (ZMod q)ˣ := by
  have h := parseval_complex g
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_div] at h
  exact Complex.ofReal_injective h

/-- Equation (93), with the actual Fourier expansion and Parseval proved. -/
theorem beta_le_sqrt_support (g : (ZMod q)ˣ → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1) :
    beta g ≤ Real.sqrt ((Finset.univ.filter fun x => g x ≠ 0).card : ℝ) := by
  classical
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Fintype.card (ZMod q)ˣ := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  exact CoefficientBounds.l1_le_sqrt_support_of_parseval
    (coefficient g) g hcard (parseval g) hg

 theorem beta_character (χ : DirichletCharacter ℂ q) :
    beta (fun x : (ZMod q)ˣ => χ x) = 1 := by
  classical
  simp only [beta, coefficient_character]
  calc
    _ = ∑ ν : DirichletCharacter ℂ q, if χ = ν then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro ν hν
      split_ifs <;> norm_num
    _ = 1 := by simp [eq_comm]

/-- The principal coefficient is precisely the average over reduced residues. -/
theorem coefficient_principal (g : (ZMod q)ˣ → ℂ) :
    coefficient g 1 = (∑ x, g x) / Fintype.card (ZMod q)ˣ := by
  simp [coefficient]

/-- A point mass on the unit group has coefficient norm one. -/
theorem beta_point (a : (ZMod q)ˣ) :
    beta (fun x => if x = a then (1 : ℂ) else 0) = 1 := by
  classical
  have hn : (0 : ℝ) < Fintype.card (ZMod q)ˣ := by exact_mod_cast Fintype.card_pos
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Fintype.card (ZMod q)ˣ := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  simp [beta, coefficient, norm_div, hcard, hn.ne']

 theorem beta_add (g h : (ZMod q)ˣ → ℂ) : beta (g + h) ≤ beta g + beta h := by
  classical
  unfold beta
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro χ hχ
  have hcoeff : coefficient (g + h) χ = coefficient g χ + coefficient h χ := by
    simp [coefficient, add_mul, Finset.sum_add_distrib, add_div]
  rw [hcoeff]
  exact norm_add_le _ _

 theorem beta_sum {ι : Type*} (s : Finset ι) (g : ι → (ZMod q)ˣ → ℂ) :
    beta (fun x => ∑ i ∈ s, g i x) ≤ ∑ i ∈ s, beta (g i) := by
  classical
  unfold beta
  simp_rw [coefficient_sum]
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q, ∑ i ∈ s, ‖coefficient (g i) χ‖ :=
      Finset.sum_le_sum fun χ _ => norm_sum_le _ _
    _ = _ := Finset.sum_comm

/-- Multiplication by a character permutes the actual Fourier coefficients. -/
theorem coefficient_twist (g : (ZMod q)ˣ → ℂ) (ξ χ : DirichletCharacter ℂ q) :
    coefficient (fun x => ξ x * g x) χ = coefficient g (χ * ξ⁻¹) := by
  have hξ (x : (ZMod q)ˣ) : conj (ξ⁻¹ x) = ξ x := by
    rw [← MulChar.star_apply']
    simp only [RCLike.star_def, Complex.conj_conj]
  unfold coefficient
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  simp only [MulChar.mul_apply, map_mul, hξ]
  ring

 theorem beta_twist (g : (ZMod q)ˣ → ℂ) (ξ : DirichletCharacter ℂ q) :
    beta (fun x => ξ x * g x) = beta g := by
  unfold beta
  simp_rw [coefficient_twist]
  exact Fintype.sum_bijective (fun χ : DirichletCharacter ℂ q => χ * ξ⁻¹)
    (Group.mulRight_bijective ξ⁻¹) _ _ (fun χ => rfl)

 theorem beta_const_mul (c : ℂ) (g : (ZMod q)ˣ → ℂ) :
    beta (fun x => c * g x) = ‖c‖ * beta g := by
  simp only [beta, coefficient_mul, norm_mul, Finset.mul_sum]

/-- The coefficient norm is submultiplicative for arbitrary products. This
already supplies the upper bound needed after the CRT factorization, without
assuming any tensor-product coefficient identity. -/
theorem beta_mul (f g : (ZMod q)ˣ → ℂ) :
    beta (fun x => f x * g x) ≤ beta f * beta g := by
  classical
  have heq : (fun x => f x * g x) =
      (fun x : (ZMod q)ˣ => ∑ χ : DirichletCharacter ℂ q,
        coefficient f χ * (χ x * g x)) := by
    funext x
    rw [← inversion f x, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro χ hχ
    ring
  rw [heq]
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ q,
        beta (fun x => coefficient f χ * (χ x * g x)) := beta_sum Finset.univ _
    _ = ∑ χ : DirichletCharacter ℂ q, ‖coefficient f χ‖ * beta g := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [beta_const_mul, beta_twist]
    _ = _ := by rw [← Finset.sum_mul]; rfl

 theorem beta_nonneg (g : (ZMod q)ˣ → ℂ) : 0 ≤ beta g :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

 theorem beta_prod {ι : Type*} (s : Finset ι) (g : ι → (ZMod q)ˣ → ℂ) :
    beta (fun x => ∏ i ∈ s, g i x) ≤ ∏ i ∈ s, beta (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (beta_character (1 : DirichletCharacter ℂ q)).le
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (beta_mul (g i) (fun x => ∏ j ∈ s, g j x)).trans
      (mul_le_mul_of_nonneg_left ih (beta_nonneg (g i)))

/-- Inflation from a divisor modulus has exactly the old coefficients at the
inflated characters and zero coefficients at all remaining characters. -/
theorem coefficient_inflation {Q : ℕ} [NeZero Q] (hdiv : q ∣ Q)
    (g : (ZMod q)ˣ → ℂ) (ν : DirichletCharacter ℂ Q) :
    coefficient (fun x => g (ZMod.unitsMap hdiv x)) ν =
      ∑ χ : DirichletCharacter ℂ q,
        if χ.changeLevel hdiv = ν then coefficient g χ else 0 := by
  classical
  have heq : (fun x => g (ZMod.unitsMap hdiv x)) =
      (fun x : (ZMod Q)ˣ => ∑ χ : DirichletCharacter ℂ q,
        coefficient g χ * χ.changeLevel hdiv x) := by
    funext x
    rw [← inversion g (ZMod.unitsMap hdiv x)]
    apply Finset.sum_congr rfl
    intro χ hχ
    congr 1
    simp [DirichletCharacter.changeLevel_def]
  rw [heq, coefficient_sum]
  simp only [coefficient_mul, coefficient_character]
  apply Finset.sum_congr rfl
  intro χ hχ
  split_ifs <;> simp

/-- The normalized reduced-residue mean is unchanged by inflation. -/
theorem coefficient_principal_inflation {Q : ℕ} [NeZero Q] (hdiv : q ∣ Q)
    (g : (ZMod q)ˣ → ℂ) :
    coefficient (fun x => g (ZMod.unitsMap hdiv x)) 1 = coefficient g 1 := by
  rw [coefficient_inflation]
  simp only [DirichletCharacter.changeLevel_eq_one_iff hdiv]
  simp

/-- Inflation preserves the actual coefficient norm, as asserted after (93). -/
theorem beta_inflation {Q : ℕ} [NeZero Q] (hdiv : q ∣ Q)
    (g : (ZMod q)ˣ → ℂ) :
    beta (fun x => g (ZMod.unitsMap hdiv x)) = beta g := by
  classical
  let e : DirichletCharacter ℂ q ↪ DirichletCharacter ℂ Q :=
    ⟨DirichletCharacter.changeLevel hdiv,
      DirichletCharacter.changeLevel_injective hdiv⟩
  apply CoefficientBounds.coefficientL1_zero_extension e (coefficient g)
    (coefficient (fun x => g (ZMod.unitsMap hdiv x)))
  · intro χ
    rw [coefficient_inflation]
    simp only [e, Function.Embedding.coeFn_mk,
      (DirichletCharacter.changeLevel_injective hdiv).eq_iff]
    simp
  · intro ν hν
    rw [coefficient_inflation]
    apply Finset.sum_eq_zero
    intro χ hχ
    exact if_neg (hν χ)

/-- The inverse image of one residue class under reduction is a coset of the
kernel; its indicator has norm one, with no subgroup-character formula assumed. -/
theorem beta_residue_coset {Q : ℕ} [NeZero Q] (hdiv : q ∣ Q)
    (a : (ZMod q)ˣ) :
    beta (fun x : (ZMod Q)ˣ => if ZMod.unitsMap hdiv x = a then (1 : ℂ) else 0) = 1 := by
  rw [beta_inflation hdiv (fun x => if x = a then (1 : ℂ) else 0), beta_point]

end
end DepthAspect.FiniteCharacterFourier
