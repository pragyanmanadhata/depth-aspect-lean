import DepthAspect.PeriodicCounting

/-!
# Actual projective two-chart root counts and content reduction

The two affine charts are `(x,1)` for every residue `x`, and `(1,y)` for
even residues `y`. All cardinalities below are counts of explicit finite sets
of integer representatives. In particular equation (20) is not an assumption.
-/
namespace DepthAspect.ContentReduction

@[simp] theorem pow_two_toNat (e : ℕ) : ((2 : ℤ) ^ e).toNat = 2 ^ e := by
  rw [Int.toNat_pow_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]
  rfl

/-- Roots in the projective chart `(x,1)`. -/
def firstChart (h : ℕ) (A B C : ℤ) : Finset ℤ :=
  (Finset.Ico 0 ((2 : ℤ) ^ h)).filter
    (fun x => (2 : ℤ) ^ h ∣ A * x ^ 2 + B * x + C)

/-- Roots in the projective chart `(1,y)`, where `y` is even. -/
def secondChart (h : ℕ) (A B C : ℤ) : Finset ℤ :=
  (Finset.Ico 0 ((2 : ℤ) ^ h)).filter
    (fun y => Even y ∧ (2 : ℤ) ^ h ∣ A + B * y + C * y ^ 2)

/-- The actual two-chart projective root count. -/
def rho (h : ℕ) (A B C : ℤ) : ℕ :=
  (firstChart h A B C).card + (secondChart h A B C).card

 theorem quadratic_periodic (q A B C x : ℤ) :
    (q ∣ A * x ^ 2 + B * x + C) ↔
      q ∣ A * (x % q) ^ 2 + B * (x % q) + C := by
  have hx := Int.mod_modEq x q
  have h := ((Int.ModEq.mul_left A (hx.pow 2)).add
    (Int.ModEq.mul_left B hx)).add (Int.ModEq.refl C)
  exact h.dvd_iff.symm

 theorem reverse_quadratic_periodic (q A B C x : ℤ) :
    (q ∣ A + B * x + C * x ^ 2) ↔
      q ∣ A + B * (x % q) + C * (x % q) ^ 2 := by
  have hx := Int.mod_modEq x q
  have h := ((Int.ModEq.refl A).add (Int.ModEq.mul_left B hx)).add
    (Int.ModEq.mul_left C (hx.pow 2))
  exact h.dvd_iff.symm

 theorem even_periodic (q x : ℤ) (hq : 2 ∣ q) :
    Even x ↔ Even (x % q) := by
  have h := (Int.mod_modEq x q).of_dvd hq
  simpa only [even_iff_two_dvd] using h.dvd_iff.symm

 theorem scaled_quadratic_dvd (e j : ℕ) (A B C x : ℤ) :
    (2 : ℤ) ^ (e + j) ∣
      (2 ^ e * A) * x ^ 2 + (2 ^ e * B) * x + 2 ^ e * C ↔
      (2 : ℤ) ^ j ∣ A * x ^ 2 + B * x + C := by
  have heq : (2 ^ e * A) * x ^ 2 + (2 ^ e * B) * x + 2 ^ e * C =
      (2 : ℤ) ^ e * (A * x ^ 2 + B * x + C) := by ring
  rw [heq, pow_add, mul_dvd_mul_iff_left (pow_ne_zero e (by norm_num : (2 : ℤ) ≠ 0))]

 theorem scaled_reverse_quadratic_dvd (e j : ℕ) (A B C x : ℤ) :
    (2 : ℤ) ^ (e + j) ∣
      2 ^ e * A + (2 ^ e * B) * x + (2 ^ e * C) * x ^ 2 ↔
      (2 : ℤ) ^ j ∣ A + B * x + C * x ^ 2 := by
  have heq : 2 ^ e * A + (2 ^ e * B) * x + (2 ^ e * C) * x ^ 2 =
      (2 : ℤ) ^ e * (A + B * x + C * x ^ 2) := by ring
  rw [heq, pow_add, mul_dvd_mul_iff_left (pow_ne_zero e (by norm_num : (2 : ℤ) ≠ 0))]

 theorem firstChart_content_reduction (e j : ℕ) (A B C : ℤ) :
    (firstChart (e + j) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C)).card =
      2 ^ e * (firstChart j A B C).card := by
  have hs : firstChart (e + j) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) =
      (Finset.Ico 0 ((2 : ℤ) ^ e * 2 ^ j)).filter
        (fun x => (2 : ℤ) ^ j ∣ A * x ^ 2 + B * x + C) := by
    ext x
    simp only [firstChart, Finset.mem_filter, Finset.mem_Ico]
    rw [scaled_quadratic_dvd, pow_add]
  rw [hs]
  have hc := PeriodicCounting.periodic_count ((2 : ℤ) ^ e) ((2 : ℤ) ^ j)
    (by positivity) (fun x => (2 : ℤ) ^ j ∣ A * x ^ 2 + B * x + C)
    (quadratic_periodic _ A B C)
  simpa [firstChart] using hc

 theorem secondChart_content_reduction (e j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) :
    (secondChart (e + j) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C)).card =
      2 ^ e * (secondChart j A B C).card := by
  have ht : (2 : ℤ) ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  have hs : secondChart (e + j) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) =
      (Finset.Ico 0 ((2 : ℤ) ^ e * 2 ^ j)).filter
        (fun y => Even y ∧ (2 : ℤ) ^ j ∣ A + B * y + C * y ^ 2) := by
    ext x
    simp only [secondChart, Finset.mem_filter, Finset.mem_Ico]
    rw [scaled_reverse_quadratic_dvd, pow_add]
  rw [hs]
  have hc := PeriodicCounting.periodic_count ((2 : ℤ) ^ e) ((2 : ℤ) ^ j)
    (by positivity) (fun y => Even y ∧ (2 : ℤ) ^ j ∣ A + B * y + C * y ^ 2)
    (fun y => and_congr (even_periodic _ y ht) (reverse_quadratic_periodic _ A B C y))
  simpa [secondChart] using hc

/-- The non-scalar branch of (20), for arbitrary integer coefficients. -/
theorem rho_content_reduction (e j : ℕ) (A B C : ℤ) (hj : 1 ≤ j) :
    rho (e + j) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) =
      2 ^ e * rho j A B C := by
  unfold rho
  rw [firstChart_content_reduction, secondChart_content_reduction e j A B C hj]
  exact (Nat.mul_add _ _ _).symm

/-- Exactly half the representatives at positive dyadic level are even. -/
theorem even_representatives_card (a : ℕ) :
    ((Finset.Ico 0 ((2 : ℤ) ^ (a + 1))).filter Even).card = 2 ^ a := by
  have hc := PeriodicCounting.periodic_count ((2 : ℤ) ^ a) 2 (by norm_num)
    Even (fun x => even_periodic 2 x dvd_rfl)
  have hb : ((Finset.Ico (0 : ℤ) 2).filter Even).card = 1 := by decide
  simpa [pow_succ, hb] using hc

 theorem scalar_firstChart (h e : ℕ) (A B C : ℤ) (he : h ≤ e) :
    firstChart h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) =
      Finset.Ico 0 ((2 : ℤ) ^ h) := by
  have hdiv : (2 : ℤ) ^ h ∣ 2 ^ e := pow_dvd_pow 2 he
  ext x
  simp only [firstChart, Finset.mem_filter]
  apply and_iff_left_of_imp
  intro hx
  have hh : (2 : ℤ) ^ h ∣ 2 ^ e * (A * x ^ 2 + B * x + C) :=
    hdiv.trans (dvd_mul_right _ _)
  convert hh using 1
  ring

 theorem scalar_secondChart (h e : ℕ) (A B C : ℤ) (he : h ≤ e) :
    secondChart h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) =
      (Finset.Ico 0 ((2 : ℤ) ^ h)).filter Even := by
  have hdiv : (2 : ℤ) ^ h ∣ 2 ^ e := pow_dvd_pow 2 he
  ext x
  simp only [secondChart, Finset.mem_filter]
  have hh : (2 : ℤ) ^ h ∣ 2 ^ e * (A + B * x + C * x ^ 2) :=
    hdiv.trans (dvd_mul_right _ _)
  have ht : (2 : ℤ) ^ h ∣ 2 ^ e * A + (2 ^ e * B) * x + (2 ^ e * C) * x ^ 2 := by
    convert hh using 1
    ring
  simp [ht]

/-- The all-scalar branch of (20), including the exact factor 3. -/
theorem rho_all_scalar (h e : ℕ) (A B C : ℤ) (hh : 1 ≤ h) (he : h ≤ e) :
    rho h (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) = 3 * 2 ^ (h - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, h = a + 1 := ⟨h - 1, by omega⟩
  unfold rho
  rw [scalar_firstChart (a + 1) e A B C he, scalar_secondChart (a + 1) e A B C he,
    even_representatives_card]
  simp only [Int.card_Ico, sub_zero, pow_two_toNat, Nat.add_sub_cancel]
  rw [pow_succ]
  omega

/-- Odd content has no effect on a dyadic root congruence. -/
theorem cancel_odd_content (h : ℕ) (u z : ℤ) (hu : Odd u) :
    (2 : ℤ) ^ h ∣ u * z ↔ (2 : ℤ) ^ h ∣ z := by
  constructor
  · exact LocalArithmetic.pow_two_dvd_of_dvd_odd_mul hu
  · rintro ⟨a, ha⟩
    refine ⟨u * a, ?_⟩
    rw [ha]
    ring

 theorem firstChart_odd_content (h : ℕ) (u A B C : ℤ) (hu : Odd u) :
    firstChart h (u * A) (u * B) (u * C) = firstChart h A B C := by
  ext x
  simp only [firstChart, Finset.mem_filter]
  have heq : (u * A) * x ^ 2 + (u * B) * x + u * C =
      u * (A * x ^ 2 + B * x + C) := by ring
  rw [heq, cancel_odd_content h u _ hu]

 theorem secondChart_odd_content (h : ℕ) (u A B C : ℤ) (hu : Odd u) :
    secondChart h (u * A) (u * B) (u * C) = secondChart h A B C := by
  ext x
  simp only [secondChart, Finset.mem_filter]
  have heq : u * A + (u * B) * x + (u * C) * x ^ 2 =
      u * (A + B * x + C * x ^ 2) := by ring
  rw [heq, cancel_odd_content h u _ hu]

/-- Removing the odd part of the content preserves the actual root count. -/
theorem rho_odd_content (h : ℕ) (u A B C : ℤ) (hu : Odd u) :
    rho h (u * A) (u * B) (u * C) = rho h A B C := by
  simp only [rho, firstChart_odd_content h u A B C hu,
    secondChart_odd_content h u A B C hu]

end DepthAspect.ContentReduction
