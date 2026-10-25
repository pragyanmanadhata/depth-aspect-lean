import DepthAspect.DyadicFourClassBridge
import DepthAspect.SmoothingKernel
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! Short literal corollaries for the prose surrounding (81)–(105): the empty
initial dyadic stratum, failure of multiplicativity for a nonprincipal twist,
and the strict numerical inequality ζ(2)<2. -/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.CoefficientProse
open DyadicResidueFourier DyadicFourClassBridge

/-- For odd u and unit x, u²-x is even. Consequently the a=0 stratum in
(96) is empty. The result covers both digit counts two and three. -/
theorem stratum_zero_of_odd {r : ℕ} (hr : 1 ≤ r) {u : ℤ} (hu : Odd u)
    (b : ℕ) : ∀ x : (ZMod (2 ^ (2 * 0 + r)))ˣ, stratum 0 r b u x = 0 := by
  intro x
  let X : ℤ := (x : ZMod (2 ^ (2 * 0 + r))).val
  have hX : Odd X := units_odd_representative (by omega : 1 ≤ 2 * 0 + r) x
  have hx : (X : ZMod (2 ^ (2 * 0 + r))) = x := by simp [X]
  have hEven : Even (u ^ 2 - X) := (hu.pow (n := 2)).sub_odd hX
  have hmod : (2 : ℕ) ∣ ((u ^ 2 - X : ℤ) : ZMod (2 ^ (2 * 0 + r))).val := by
    apply (ResidueNormalization.divides_val_iff (a := 2) (N := 2 ^ (2 * 0 + r))
      (show 2 ∣ 2 ^ (2 * 0 + r) from by
        simpa only [pow_one] using pow_dvd_pow (2 : ℕ) (by omega : 1 ≤ 2 * 0 + r))
      (u ^ 2 - X)).mpr
    simpa only [Nat.cast_ofNat] using hEven.two_dvd
  have hres : DyadicResidueFourier.residual (2 * 0 + r) u x =
      ((u ^ 2 - X : ℤ) : ZMod (2 ^ (2 * 0 + r))) := by
    simp only [DyadicResidueFourier.residual, Int.cast_sub, Int.cast_pow, hx]
  have hnot : ¬ (DyadicResidueFourier.residual (2 * 0 + r) u x).val % 4 = 1 := by
    rw [hres]
    omega
  unfold stratum
  rw [if_neg]
  intro h
  apply hnot
  have hz := h.2
  change (DyadicResidueFourier.residual (2 * 0 + r) u x).val / 1 % 4 = 1 at hz
  simpa only [Nat.div_one] using hz

def twistedArithmeticFunction (t : ℤ) (χ : DirichletCharacter ℂ 8) :
    ArithmeticFunction ℂ :=
  ⟨GlobalResidueMean.sequence t χ, by simp [GlobalResidueMean.sequence]⟩

/-- The degree-zero exception is an actual value of the global sequence. -/
theorem nonprincipal_value_at_one :
    GlobalResidueMean.sequence 0 (FourDyadicTwists.character 1) 1 = 0 := by
  have h := dyadicValue_eq_four_class (t := 0) (by norm_num) (1 : Fin 4) 0
  simpa [GlobalResidueMean.sequence, DyadicOddSeries.dyadicValue,
    DyadicLocalMeans.average_zero] using h

/-- The full twisted sequence really need not be multiplicative. -/
theorem twisted_sequence_not_multiplicative :
    ¬ (twistedArithmeticFunction 0 (FourDyadicTwists.character 1)).IsMultiplicative := by
  intro h
  have h1 := h.map_one
  change GlobalResidueMean.sequence 0 (FourDyadicTwists.character 1) 1 = 1 at h1
  rw [nonprincipal_value_at_one] at h1
  exact zero_ne_one h1

theorem inverse_square_sum_le_seven_quarters :
    (∑' n : ℕ, DigammaBound.inverseSquare n) ≤ 7 / 4 := by
  have htail := SmoothingKernel.inverseSquare_tail (N := 2) (by norm_num)
  have hsplit := DigammaBound.inverseSquare_summable.sum_add_tsum_nat_add 2
  have hhead : (∑ n ∈ Finset.range 2, DigammaBound.inverseSquare n) = 5 / 4 := by
    norm_num [Finset.sum_range_succ, DigammaBound.inverseSquare]
  rw [hhead] at hsplit
  norm_num at htail
  linarith

theorem inverse_square_sum_lt_two :
    (∑' n : ℕ, DigammaBound.inverseSquare n) < 2 :=
  inverse_square_sum_le_seven_quarters.trans_lt (by norm_num)

/-- The actual ζ(2) value satisfies the strict inequality used below (88). -/
theorem zeta_two_lt_two : (riemannZeta 2).re < 2 := by
  have hshift := hasSum_zeta_two.summable.tsum_eq_zero_add
  have heq : (∑' n : ℕ, DigammaBound.inverseSquare n) = Real.pi ^ 2 / 6 := by
    rw [hasSum_zeta_two.tsum_eq] at hshift
    simpa only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero,
      zero_add, Nat.cast_add, Nat.cast_one, DigammaBound.inverseSquare] using hshift.symm
  rw [riemannZeta_two]
  have hr : (((Real.pi : ℂ) ^ 2 / 6).re) = Real.pi ^ 2 / 6 := by
    norm_cast
  rw [hr, ← heq]
  exact inverse_square_sum_lt_two

end DepthAspect.CoefficientProse
