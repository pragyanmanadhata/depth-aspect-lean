import DepthAspect.LocalResidueIdentification
import DepthAspect.OddCoefficientPeriodicity
import DepthAspect.FiniteCharacterFourier
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Units.Equiv

/-!
# The actual reduced-residue mean in the odd Euler factor

The affine map x ↦ t²−4x is a permutation of the residue ring at an odd prime.
Its restriction sends units exactly to discriminants outside the class t² mod p.
This proves that the computed paired-digit average is the principal Fourier
coefficient of the literal local ψ function; no local-mean identity is assumed.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.AffineResidueMean
open LocalResidueAverages LocalResidueIdentification OddDiscriminantValues

variable {p : ℕ} [Fact p.Prime]

/-- Reduction from a positive prime-power modulus to the prime field. -/
def reduction (k : ℕ) (hk : 0 < k) : ZMod (p ^ k) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hk.ne') _

theorem reduction_val (k : ℕ) (hk : 0 < k) (x : ZMod (p ^ k)) :
    reduction k hk x = (x.val : ZMod p) := by
  simp only [reduction, ZMod.castHom_apply, ZMod.cast_eq_val]

theorem coprime_iff_reduction_ne_zero (k : ℕ) (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    Nat.Coprime x.val (p ^ k) ↔ reduction k hk x ≠ 0 := by
  rw [Nat.coprime_pow_right_iff hk, Nat.coprime_comm,
    (Fact.out : p.Prime).coprime_iff_not_dvd, reduction_val]
  exact not_congr (ZMod.natCast_eq_zero_iff x.val p).symm

private theorem four_isUnit (hp2 : p ≠ 2) (k : ℕ) (hk : 0 < k) :
    IsUnit (4 : ZMod (p ^ k)) := by
  change IsUnit ((4 : ℕ) : ZMod (p ^ k))
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) hk]
  intro h
  have h2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
    (show p ∣ 2 ^ 2 by norm_num at h ⊢; exact h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h2)

/-- The affine discriminant map on the complete residue ring. -/
def affine (hp2 : p ≠ 2) (k : ℕ) (hk : 0 < k) (t : ℤ) :
    Equiv.Perm (ZMod (p ^ k)) where
  toFun x := (t : ZMod (p ^ k)) ^ 2 - 4 * x
  invFun D := (4 : ZMod (p ^ k))⁻¹ * ((t : ZMod (p ^ k)) ^ 2 - D)
  left_inv x := by
    have h4 := ZMod.inv_mul_of_unit (4 : ZMod (p ^ k)) (four_isUnit hp2 k hk)
    calc
      _ = ((4 : ZMod (p ^ k))⁻¹ * 4) * x := by ring
      _ = x := by rw [h4, one_mul]
  right_inv D := by
    have h4 := ZMod.mul_inv_of_unit (4 : ZMod (p ^ k)) (four_isUnit hp2 k hk)
    calc
      _ = (t : ZMod (p ^ k)) ^ 2 -
          (4 * (4 : ZMod (p ^ k))⁻¹) * ((t : ZMod (p ^ k)) ^ 2 - D) := by ring
      _ = D := by rw [h4]; ring

 theorem affine_reduction_iff (hp2 : p ≠ 2) (k : ℕ) (hk : 0 < k)
    (t : ℤ) (x : ZMod (p ^ k)) :
    Nat.Coprime x.val (p ^ k) ↔
      reduction k hk (affine hp2 k hk t x) ≠ (t : ZMod p) ^ 2 := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro hz
    have hp4 : p ∣ (4 : ℕ) :=
      (ZMod.natCast_eq_zero_iff 4 p).mp (by simpa using hz)
    have hp2div : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
      (show p ∣ 2 ^ 2 by norm_num; exact hp4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hp2div)
  rw [coprime_iff_reduction_ne_zero]
  change reduction k hk x ≠ 0 ↔
    reduction k hk ((t : ZMod (p ^ k)) ^ 2 - 4 * x) ≠ (t : ZMod p) ^ 2
  simp only [map_sub, map_pow, map_mul, map_intCast, map_ofNat]
  constructor
  · intro hx heq
    apply hx
    exact (mul_eq_zero.mp (sub_eq_self.mp heq)).resolve_left h4
  · intro hx hz
    apply hx
    simp [hz]

/-- The affine map restricted to units is a genuine bijection onto the
allowed discriminant residues. -/
def unitsAffine (hp2 : p ≠ 2) (k : ℕ) (hk : 0 < k) (t : ℤ) :
    (ZMod (p ^ k))ˣ ≃
      {D : ZMod (p ^ k) // reduction k hk D ≠ (t : ZMod p) ^ 2} :=
  ZMod.unitsEquivCoprime.trans
    ((affine hp2 k hk t).subtypeEquiv (affine_reduction_iff hp2 k hk t))

 theorem sum_units_affine (hp2 : p ≠ 2) (k : ℕ) (hk : 0 < k) (t : ℤ)
    (F : ZMod (p ^ k) → ℝ) :
    (∑ x : (ZMod (p ^ k))ˣ, F ((t : ZMod (p ^ k)) ^ 2 - 4 * x)) =
      ∑ D : ZMod (p ^ k), if reduction k hk D ≠ (t : ZMod p) ^ 2 then F D else 0 := by
  calc
    _ = ∑ D : {D : ZMod (p ^ k) // reduction k hk D ≠ (t : ZMod p) ^ 2}, F D :=
      Equiv.sum_comp (unitsAffine hp2 k hk t) (fun D => F D)
    _ = ∑ D ∈ Finset.univ.filter (fun D : ZMod (p ^ k) =>
          reduction k hk D ≠ (t : ZMod p) ^ 2), F D :=
      (Finset.sum_subtype _ (by simp) F).symm
    _ = _ := Finset.sum_filter _ _

 theorem reduction_digit (b : ℕ) (lo hi : ZMod p) (D : Digits p b) :
    reduction (2 * (b + 1)) (by omega) (residueEquiv (b + 1) (lo, hi, D)) = lo := by
  rw [reduction_val, residueEquiv_succ_val]
  simp

/-- The numerator of the actual unit average is the numerator that was
computed in the recurrence proof, with no unspecified bijection. -/
theorem residueValue_sum_units (hp2 : p ≠ 2) (b : ℕ) (t : ℤ) :
    (∑ x : (ZMod (p ^ (2 * (b + 1))))ˣ,
      residueValue (p := p) (b + 1) ((t : ZMod (p ^ (2 * (b + 1)))) ^ 2 -
        4 * (x : ZMod (p ^ (2 * (b + 1)))))) =
      ∑ lo : ZMod p, ∑ hi : ZMod p, ∑ D : Digits p b,
        if lo ≠ (t : ZMod p) ^ 2 then value (b + 1) (lo, hi, D) else 0 := by
  rw [sum_units_affine hp2 _ (by omega)]
  rw [← Equiv.sum_comp (residueEquiv (b + 1))]
  change (∑ D : ZMod p × ZMod p × Digits p b, _) = _
  simp only [Fintype.sum_prod_type, reduction_digit, residueValue,
    Equiv.symm_apply_apply]

 theorem card_units_succ (b : ℕ) :
    (Fintype.card (ZMod (p ^ (2 * (b + 1))))ˣ : ℝ) =
      ((p : ℝ) - 1) * p * (p : ℝ) ^ (2 * b) := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow (Fact.out : p.Prime) (by omega)]
  rw [show 2 * (b + 1) - 1 = 2 * b + 1 by omega]
  push_cast [Nat.cast_sub (Fact.out : p.Prime).one_le]
  ring

/-- The computed unitMean is the normalized sum of the literal residue
coefficient over units. -/
theorem unitMean_eq_residue_average (hp2 : p ≠ 2) (b : ℕ) (t : ℤ) :
    unitMean (p := p) b (t : ZMod p) =
      (∑ x : (ZMod (p ^ (2 * b)))ˣ,
        residueValue (p := p) b ((t : ZMod (p ^ (2 * b))) ^ 2 -
        4 * (x : ZMod (p ^ (2 * b))))) /
        Fintype.card (ZMod (p ^ (2 * b)))ˣ := by
  cases b with
  | zero => simp [unitMean, residueValue, value]
  | succ b => rw [unitMean, residueValue_sum_units hp2 b t, card_units_succ]

/-- Literal normalized-coefficient version of the odd local mean. -/
theorem unitMean_eq_local_average (hp2 : p ≠ 2) (b : ℕ) (t : ℤ) :
    (unitMean (p := p) b (t : ZMod p) : ℂ) =
      (∑ x : (ZMod (p ^ (2 * b)))ˣ,
        localCoefficient p (t ^ 2 - 4 * ((x : ZMod (p ^ (2 * b))).val : ℤ)) b) /
        Fintype.card (ZMod (p ^ (2 * b)))ˣ := by
  rw [unitMean_eq_residue_average hp2]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [residueValue_eq_localCoefficient]
  have hD : ((t : ZMod (p ^ (2 * b))) ^ 2 - 4 * x) =
      ((t ^ 2 - 4 * ((x : ZMod (p ^ (2 * b))).val : ℤ) : ℤ) :
        ZMod (p ^ (2 * b))) := by
    simp
  rw [hD]
  exact OddCoefficientPeriodicity.localCoefficient_residue b _

/-- Equation (83) really computes the principal Fourier coefficient of the
actual local coefficient function on reduced residues. -/
theorem principal_local_mean (hp2 : p ≠ 2) (b : ℕ) (t : ℤ) :
    FiniteCharacterFourier.coefficient
      (fun x : (ZMod (p ^ (2 * b)))ˣ =>
        localCoefficient p (t ^ 2 - 4 * ((x : ZMod (p ^ (2 * b))).val : ℤ)) b) 1 =
      (unitMean (p := p) b (t : ZMod p) : ℂ) := by
  rw [FiniteCharacterFourier.coefficient_principal]
  exact (unitMean_eq_local_average hp2 b t).symm

end DepthAspect.AffineResidueMean
