import DepthAspect.ImprimitiveBoundary
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.LinearCombination

/-!
# Actual conductor-two class-number scaling

The finite factors are the actual Euler corrections for the ordered value
of the imprimitive character. The only class-number input in the final
transfer is the cited analytic class-number identity, not a growth or a
conductor-scaling assertion.
-/
namespace DepthAspect.DyadicClassScaling
open scoped BigOperators
open ClassNumberGrowth ImprimitiveBoundary

/-- The literal finite correction polynomial at s=1. -/
noncomputable def localCorrection (c : ℂ) (p : ℝ) (e : ℕ) : ℂ :=
  1 + (1 - c) * ∑ j ∈ Finset.range e, ((p : ℂ)⁻¹) ^ (j + 1)

/-- This polynomial is the actual global Euler product's correction at one. -/
theorem correction_at_one {q : ℕ} (χ : DirichletCharacter ℂ q) (f p : ℕ) :
    ImprimitiveLSeries.correction χ f p 1 =
      localCorrection (χ (p : ZMod q)) p (f.factorization p) := by
  simp only [ImprimitiveLSeries.correction, localCorrection,
    Complex.cpow_neg_one, Complex.ofReal_natCast]

noncomputable def localClassFactor (α : ℝ) (e : ℕ) : ℝ :=
  1 + (2 - α) * ((2 : ℝ) ^ e - 1)

theorem localClassFactor_difference (α : ℝ) (e : ℕ) :
    localClassFactor α (e + 1) - localClassFactor α e = (2 - α) * (2 : ℝ) ^ e := by
  simp only [localClassFactor, pow_succ]
  ring

theorem localClassFactor_scaled_difference (α : ℝ) (e j : ℕ) :
    localClassFactor α (e + j + 1) - localClassFactor α (e + j) =
      (2 : ℝ) ^ j * (localClassFactor α (e + 1) - localClassFactor α e) := by
  rw [localClassFactor_difference, localClassFactor_difference, pow_add]
  ring

theorem localClassFactor_pos (α : ℝ) (e : ℕ) (hα : α ≤ 1) :
    0 < localClassFactor α e := by
  have hp : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  have hc : 0 ≤ 2 - α := by linarith
  have hprod := mul_nonneg hc (sub_nonneg.mpr hp)
  unfold localClassFactor
  linarith

/-- The complete finite Euler correction at two, including exponent zero. -/
theorem correction_two_scaled (c : ℂ) (e : ℕ) :
    (2 : ℂ) ^ e * localCorrection c 2 e =
      1 + (2 - c) * ((2 : ℂ) ^ e - 1) := by
  induction e with
  | zero => simp [localCorrection]
  | succ e ih =>
    have hp : (2 : ℂ) ^ (e + 1) * (2 : ℂ)⁻¹ ^ (e + 1) = 1 := by
      rw [← mul_pow]
      norm_num
    unfold localCorrection at ih ⊢
    simp only [Complex.ofReal_ofNat, Finset.sum_range_succ] at ih ⊢
    simp only [pow_succ] at hp ih ⊢
    linear_combination 2 * ih + (1 - c) * hp

/-- Splitting off the actual prime-two factor from a conductor with odd part
`f₀`. This is an equality of the literal finite products in equation (7). -/
theorem correction_product_two_part {q : ℕ} (χ : DirichletCharacter ℂ q)
    (e f₀ : ℕ) (hf₀ : 0 < f₀) (hodd : Odd f₀) :
    (∏ p ∈ (2 ^ e * f₀).primeFactors,
      localCorrection (χ (p : ZMod q)) p ((2 ^ e * f₀).factorization p)) =
    localCorrection (χ (2 : ZMod q)) 2 e *
      ∏ p ∈ f₀.primeFactors,
        localCorrection (χ (p : ZMod q)) p (f₀.factorization p) := by
  classical
  have hnot : ¬ 2 ∣ f₀ := hodd.not_two_dvd_nat
  have hf2 : f₀.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hnot
  have hnotmem : 2 ∉ f₀.primeFactors := by
    intro h
    exact hnot (Nat.mem_primeFactors.mp h).2.1
  cases e with
  | zero => simp [localCorrection]
  | succ e =>
    rw [Nat.primeFactors_mul (by positivity) (ne_of_gt hf₀),
      Nat.primeFactors_pow_succ, Nat.prime_two.primeFactors, Finset.singleton_union,
      Finset.prod_insert hnotmem]
    have hfact (p : ℕ) :
        (2 ^ (e + 1) * f₀).factorization p =
          (Finsupp.single 2 (e + 1)) p + f₀.factorization p := by
      rw [Nat.factorization_mul (by positivity) (ne_of_gt hf₀),
        Nat.prime_two.factorization_pow]
      rfl
    rw [hfact 2]
    simp only [Finsupp.single_eq_same, hf2, add_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hnotmem hp
    rw [hfact p, Finsupp.single_eq_of_ne hp2, zero_add]

/-- Equation (77)'s finite conductor-two ratio for the actual ordered
imprimitive L-value, before invoking the class-number identity. -/
theorem imprimitive_two_part {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (e f₀ : ℕ) (hf₀ : 0 < f₀) (hodd : Odd f₀) :
    imprimitiveLAtOne χ hχ hq (2 ^ e * f₀) (by positivity) =
      localCorrection (χ (2 : ZMod q)) 2 e *
        imprimitiveLAtOne χ hχ hq f₀ hf₀ := by
  rw [imprimitive_one_eq_correctionProduct, imprimitive_one_eq_correctionProduct]
  unfold ImprimitiveLSeries.correctionProduct
  simp only [correction_at_one]
  rw [correction_product_two_part χ e f₀ hf₀ hodd]
  ring

/-- The factor `T_e` is obtained from the actual finite Euler correction,
with no ratio of possibly zero L-values used. -/
theorem imprimitive_two_part_scaled {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (e f₀ : ℕ) (hf₀ : 0 < f₀) (hodd : Odd f₀)
    (α : ℝ) (hα : χ (2 : ZMod q) = (α : ℂ)) :
    (2 : ℂ) ^ e * imprimitiveLAtOne χ hχ hq (2 ^ e * f₀) (by positivity) =
      (localClassFactor α e : ℂ) * imprimitiveLAtOne χ hχ hq f₀ hf₀ := by
  rw [imprimitive_two_part χ hχ hq e f₀ hf₀ hodd, ← mul_assoc,
    correction_two_scaled, hα]
  simp only [localClassFactor]
  push_cast
  rfl

/-- The actual analytic class-number expression for fixed fundamental
character and variable conductor. Its identification with Hurwitz numbers
is the standard external class-number identity. -/
noncomputable def classValue {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.Odd) (hq : 0 < q) (f : ℕ) (hf : 0 < f) : ℝ :=
  Real.sqrt ((q : ℝ) * (f : ℝ) ^ 2) / Real.pi *
    (imprimitiveLAtOne χ hχ hq f hf).re

/-- The first equality in (77), derived from the actual ordered L-value. -/
theorem classValue_two_part {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (e f₀ : ℕ) (hf₀ : 0 < f₀) (hodd : Odd f₀)
    (α : ℝ) (hα : χ (2 : ZMod q) = (α : ℂ)) :
    classValue χ hχ hq (2 ^ e * f₀) (by positivity) =
      localClassFactor α e * classValue χ hχ hq f₀ hf₀ := by
  have hL := congrArg Complex.re
    (imprimitive_two_part_scaled χ hχ hq e f₀ hf₀ hodd α hα)
  rw [show (2 : ℂ) ^ e = (((2 : ℝ) ^ e : ℝ) : ℂ) by norm_cast] at hL
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hL
  have hs : Real.sqrt ((q : ℝ) * ((2 ^ e * f₀ : ℕ) : ℝ) ^ 2) =
      (2 : ℝ) ^ e * Real.sqrt ((q : ℝ) * (f₀ : ℝ) ^ 2) := by
    push_cast
    rw [show (q : ℝ) * ((2 : ℝ) ^ e * f₀) ^ 2 =
      ((2 : ℝ) ^ e) ^ 2 * ((q : ℝ) * (f₀ : ℝ) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  unfold classValue
  rw [hs]
  calc
    _ = Real.sqrt ((q : ℝ) * (f₀ : ℝ) ^ 2) / Real.pi *
      ((2 : ℝ) ^ e * (imprimitiveLAtOne χ hχ hq (2 ^ e * f₀) (by positivity)).re) := by ring
    _ = _ := by rw [hL]; ring

/-- The actual class-number expressions have the geometric difference
relation used to collapse the four dyadic trace strata. -/
theorem classValue_scaled_difference {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (e j f₀ : ℕ) (hf₀ : 0 < f₀) (hodd : Odd f₀)
    (α : ℝ) (hα : χ (2 : ZMod q) = (α : ℂ)) :
    classValue χ hχ hq (2 ^ (e + j + 1) * f₀) (by positivity) -
      classValue χ hχ hq (2 ^ (e + j) * f₀) (by positivity) =
      (2 : ℝ) ^ j * (classValue χ hχ hq (2 ^ (e + 1) * f₀) (by positivity) -
        classValue χ hχ hq (2 ^ e * f₀) (by positivity)) := by
  simp only [classValue_two_part χ hχ hq _ f₀ hf₀ hodd α hα]
  rw [← sub_mul, localClassFactor_scaled_difference]
  ring

/-- The ratio in (77) is legitimate because the elementary factor `T_e`
is positive; no nonvanishing of the underlying L-value is required. -/
theorem classValue_difference_ratio {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (e f₀ : ℕ) (hf₀ : 0 < f₀) (hodd : Odd f₀)
    (α : ℝ) (hα : χ (2 : ZMod q) = (α : ℂ)) (hαle : α ≤ 1) :
    classValue χ hχ hq (2 ^ (e + 1) * f₀) (by positivity) -
      classValue χ hχ hq (2 ^ e * f₀) (by positivity) =
      ((2 - α) * (2 : ℝ) ^ e / localClassFactor α e) *
        classValue χ hχ hq (2 ^ e * f₀) (by positivity) := by
  simp only [classValue_two_part χ hχ hq _ f₀ hf₀ hodd α hα]
  rw [← sub_mul, localClassFactor_difference]
  field_simp [ne_of_gt (localClassFactor_pos α e hαle)]

/-- General cited class-number identity specialized only after proving all
conductor-two arithmetic internally. -/
theorem hurwitz_two_part {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-(q : ℤ) * (f : ℤ) ^ 2) = classValue χ hχ hq f hf)
    (e f₀ : ℕ) (hf₀ : 0 < f₀) (hodd : Odd f₀)
    (α : ℝ) (hα : χ (2 : ZMod q) = (α : ℂ)) :
    H (-(q : ℤ) * ((2 ^ e * f₀ : ℕ) : ℤ) ^ 2) =
      localClassFactor α e * H (-(q : ℤ) * (f₀ : ℤ) ^ 2) := by
  rw [hformula _ (by positivity), hformula _ hf₀,
    classValue_two_part χ hχ hq e f₀ hf₀ hodd α hα]


/-- The actual discriminant scaling agrees with multiplying the conductor. -/
theorem four_pow_discriminant (q f j : ℕ) :
    (4 : ℤ) ^ j * (-(q : ℤ) * (f : ℤ) ^ 2) =
      -(q : ℤ) * ((2 ^ j * f : ℕ) : ℤ) ^ 2 := by
  have hp : (4 : ℤ) ^ j = ((2 : ℤ) ^ j) ^ 2 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm 2 j, pow_mul]
  rw [hp]
  push_cast
  ring

/-- The full difference relation in (77), for every positive conductor,
obtained by splitting off its actual dyadic factorization. -/
theorem hurwitz_four_pow_difference {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-(q : ℤ) * (f : ℤ) ^ 2) = classValue χ hχ hq f hf)
    (f : ℕ) (hf : 0 < f) (j : ℕ) (α : ℝ)
    (hα : χ (2 : ZMod q) = (α : ℂ)) :
    H ((4 : ℤ) ^ (j + 1) * (-(q : ℤ) * (f : ℤ) ^ 2)) -
      H ((4 : ℤ) ^ j * (-(q : ℤ) * (f : ℤ) ^ 2)) =
      (2 : ℝ) ^ j * (H (4 * (-(q : ℤ) * (f : ℤ) ^ 2)) -
        H (-(q : ℤ) * (f : ℤ) ^ 2)) := by
  let e := f.factorization 2
  let f₀ := f / 2 ^ e
  have hf₀ : 0 < f₀ := Nat.ordCompl_pos 2 hf.ne'
  have hodd : Odd f₀ := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact Nat.not_dvd_ordCompl Nat.prime_two hf.ne' he.two_dvd
  have hsplit : f = 2 ^ e * f₀ := (Nat.ordProj_mul_ordCompl_eq_self f 2).symm
  have hscaled (a : ℕ) : 2 ^ a * f = 2 ^ (e + a) * f₀ := by
    rw [hsplit, pow_add]
    ring
  have hfour : 4 * (-(q : ℤ) * (f : ℤ) ^ 2) =
      -(q : ℤ) * ((2 * f : ℕ) : ℤ) ^ 2 := by
    simpa only [pow_one] using four_pow_discriminant q f 1
  rw [four_pow_discriminant, four_pow_discriminant, hfour]
  rw [hformula _ (by positivity), hformula _ (by positivity),
    hformula _ (by positivity), hformula _ hf]
  simp only [hscaled (j + 1), hscaled j,
    show 2 * f = 2 ^ (e + 1) * f₀ by simpa only [pow_one] using hscaled 1]
  simp only [hsplit]
  simpa only [Nat.add_assoc] using
    classValue_scaled_difference χ hχ hq e j f₀ hf₀ hodd α hα

/-- The ratio in (77) for an arbitrary positive conductor, using its
actual dyadic valuation rather than a supplied valuation parameter. -/
theorem hurwitz_difference_ratio {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (hq : 0 < q)
    (H : ℤ → ℝ)
    (hformula : ∀ f : ℕ, ∀ hf : 0 < f,
      H (-(q : ℤ) * (f : ℤ) ^ 2) = classValue χ hχ hq f hf)
    (f : ℕ) (hf : 0 < f) (α : ℝ)
    (hα : χ (2 : ZMod q) = (α : ℂ)) (hαle : α ≤ 1) :
    H (4 * (-(q : ℤ) * (f : ℤ) ^ 2)) - H (-(q : ℤ) * (f : ℤ) ^ 2) =
      ((2 - α) * (2 : ℝ) ^ (f.factorization 2) /
        localClassFactor α (f.factorization 2)) * H (-(q : ℤ) * (f : ℤ) ^ 2) := by
  let e := f.factorization 2
  let f₀ := f / 2 ^ e
  have hf₀ : 0 < f₀ := Nat.ordCompl_pos 2 hf.ne'
  have hodd : Odd f₀ := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact Nat.not_dvd_ordCompl Nat.prime_two hf.ne' he.two_dvd
  have hsplit : f = 2 ^ e * f₀ := (Nat.ordProj_mul_ordCompl_eq_self f 2).symm
  have hscaled : 2 * f = 2 ^ (e + 1) * f₀ := by rw [hsplit, pow_succ]; ring
  have hfour : 4 * (-(q : ℤ) * (f : ℤ) ^ 2) =
      -(q : ℤ) * ((2 * f : ℕ) : ℤ) ^ 2 := by
    simpa only [pow_one] using four_pow_discriminant q f 1
  rw [hfour, hformula _ (by positivity), hformula _ hf]
  change classValue χ hχ hq (2 * f) _ - classValue χ hχ hq f hf =
    ((2 - α) * (2 : ℝ) ^ e / localClassFactor α e) * classValue χ hχ hq f hf
  simp only [hscaled]
  simp only [hsplit]
  exact classValue_difference_ratio χ hχ hq e f₀ hf₀ hodd α hα hαle

end DepthAspect.DyadicClassScaling
