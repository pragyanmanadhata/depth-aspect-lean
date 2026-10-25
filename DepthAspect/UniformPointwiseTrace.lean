import DepthAspect.UniformSpectralPrimeBounds
import DepthAspect.TraceZeta

/-!
# The complete unsigned pointwise trace estimates

The final statements concern the same actual finite spectral averages as the
density theorems. Their only arithmetic inputs are the cited general identities
in ArithmeticSpectralData. No dyadic size estimate is a final premise.
Here k is the polynomial degree, so the modular weight is k+2.
-/
namespace DepthAspect.UnsignedDensity

open scoped BigOperators
open TraceBounds SpectralFamily

private theorem level_inverse_sqrt (n : ℕ) :
    (Real.sqrt ((2 : ℝ) ^ n))⁻¹ = ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
    Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ) ^ n), ← Real.sqrt_eq_rpow]

noncomputable def divisorWeightSum (k m : ℕ) : ℝ :=
  ∑ p ∈ m.divisorsAntidiagonal,
    ((min p.1 p.2 : ℕ) / Real.sqrt (m : ℝ) : ℝ) ^ (k + 1)

noncomputable def divisorRatioSum (k m : ℕ) : ℝ :=
  ∑ p ∈ m.divisorsAntidiagonal,
    (((min p.1 p.2 : ℕ) : ℝ) / ((max p.1 p.2 : ℕ) : ℝ)) ^ (((k : ℝ) + 1) / 2)

theorem divisorWeightSum_nonneg (k m : ℕ) : 0 ≤ divisorWeightSum k m := by
  unfold divisorWeightSum
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem divisorWeightSum_eq_ratio (k m : ℕ) (hm : 0 < m) :
    divisorWeightSum k m = divisorRatioSum k m := by
  unfold divisorWeightSum divisorRatioSum
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hA : (0 : ℝ) ≤ (min p.1 p.2 : ℕ) := by positivity
  have hB : (0 : ℝ) < (max p.1 p.2 : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp))
      (le_max_left p.1 p.2))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hAB : (((min p.1 p.2 : ℕ) : ℝ) * ((max p.1 p.2 : ℕ) : ℝ)) = m := by
    exact_mod_cast ((min_mul_max p.1 p.2).trans hprod)
  have hsq : (((min p.1 p.2 : ℕ) : ℝ) / Real.sqrt (m : ℝ)) ^ 2 =
      (((min p.1 p.2 : ℕ) : ℝ) / ((max p.1 p.2 : ℕ) : ℝ)) := by
    rw [div_pow, Real.sq_sqrt hmR.le]
    apply (div_eq_div_iff hmR.ne' hB.ne').mpr
    calc
      _ = (((min p.1 p.2 : ℕ) : ℝ)) *
          ((((min p.1 p.2 : ℕ) : ℝ)) * ((max p.1 p.2 : ℕ) : ℝ)) := by ring
      _ = _ := by rw [hAB]
  rw [← hsq, ← Real.rpow_natCast_mul (by positivity) 2]
  norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * (((k : ℝ) + 1) / 2) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

theorem square_scalar_weight_le_divisorWeightSum (k m : ℕ) (hm : 0 < m) :
    (m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m ≤ divisorWeightSum k m := by
  classical
  by_cases hs : IsSquare m
  · obtain ⟨a, rfl⟩ := hs
    have ha : 0 < a := Nat.pos_of_mul_pos_left hm
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hp : (a, a) ∈ (a * a).divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, ne_of_gt hm⟩
    have hterm : (((min a a : ℕ) : ℝ) / Real.sqrt ((a * a : ℕ) : ℝ)) ^ (k + 1) = 1 := by
      simp only [min_self, Nat.cast_mul, Real.sqrt_mul_self (Nat.cast_nonneg a),
        div_self haR.ne', one_pow]
    have hsum : 1 ≤ divisorWeightSum k (a * a) := by
      have hsingle := Finset.single_le_sum
        (s := (a * a).divisorsAntidiagonal) (a := (a, a))
        (f := fun p : ℕ × ℕ =>
          (((min p.1 p.2 : ℕ) : ℝ) / Real.sqrt ((a * a : ℕ) : ℝ)) ^ (k + 1))
        (fun p _ => pow_nonneg
          (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) _) hp
      exact hterm.symm.le.trans hsingle
    have hpow : ((a * a : ℕ) : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ a * a from hm)) (by norm_num)
    have hsquare : IsSquare (a * a) := ⟨a, rfl⟩
    simpa only [PopaTrace.squareIndicator, if_pos hsquare, mul_one] using hpow.trans hsum
  · simpa only [PopaTrace.squareIndicator, if_neg hs, mul_zero] using divisorWeightSum_nonneg k m

namespace ArithmeticSpectralData

variable {k : ℕ} {Family V : ℕ → Type*}
  [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)] [∀ Q, Module ℂ (V Q)]

noncomputable def ellipticTerm (D : ArithmeticSpectralData k Family V) (n m : ℕ) : ℂ :=
  canonicalLiteralElliptic k n (Fintype.card (Family (2 ^ n)) : ℝ) (m : ℤ)
    D.primitiveClass D.primitive_forms

noncomputable def cuspTerm (D : ArithmeticSpectralData k Family V) (n m : ℕ) : ℂ :=
  (normalizedCusp k n (Fintype.card (Family (2 ^ n)) : ℝ) (m : ℝ) m.divisorsAntidiagonal : ℂ)

noncomputable def scalarFactor (D : ArithmeticSpectralData k Family V) (n : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card (Family (2 ^ n)) : ℝ))

theorem mean_trace_parts (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (hm : 0 < m) (hodd : Odd m) :
    heckeAverage (D.eigenvalues (2 ^ n)) m =
      ((D.scalarFactor n * (m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m : ℝ) : ℂ) +
        D.ellipticTerm n m + D.cuspTerm n m := by
  exact D.mean_trace n hn m hm hodd

theorem scalarFactor_error (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 8 ≤ n) :
    |D.scalarFactor n - 1| ≤ 8 / ((k : ℝ) + 1) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by
  have h := MartinDimension.scalarCoefficient_error (k + 2) n (by omega) hn
    (fun M => (Fintype.card (Family M) : ℝ)) D.dimension_formula
  simpa only [MartinDimension.scalarCoefficient, scalarFactor, Nat.cast_add, Nat.cast_ofNat,
    show (k : ℝ) + 2 - 1 = (k : ℝ) + 1 by ring] using h

theorem ellipticTerm_bound (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 8 ≤ n) (m : ℕ) (hm : 0 < m) (hodd : Odd m)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖D.ellipticTerm n m‖ ≤ uniformEllipticConstant δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
      (m : ℝ) ^ δ * ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) (m : ℤ)).card : ℝ) := by
  simpa only [ellipticTerm, Int.cast_natCast] using canonicalLiteralElliptic_bound k n hn
    (m : ℤ) (by exact_mod_cast hm) (by exact_mod_cast hodd)
    (fun M => (Fintype.card (Family M) : ℝ)) D.dimension_formula D.primitiveClass
    D.hurwitzClass D.primitive_nonneg D.primitive_decomposition D.ordered_class_number_formula
    D.primitive_forms δ hδ

theorem cuspTerm_bound (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 8 ≤ n) (m : ℕ) (hm : 0 < m) :
    ‖D.cuspTerm n m‖ ≤ 192 / ((k : ℝ) + 1) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
      divisorWeightSum k m := by
  have h := normalizedCusp_bound k n (Fintype.card (Family (2 ^ n)) : ℝ)
    (m : ℝ) (by exact_mod_cast hm)
    (MartinDimension.polynomial_degree_dimension_lower k n hn _ D.dimension_formula)
    m.divisorsAntidiagonal
  rw [cuspTerm, Complex.norm_real, Real.norm_eq_abs]
  simpa only [divisorWeightSum, div_eq_mul_inv, level_inverse_sqrt, mul_assoc] using h

theorem uniform_unsigned_trace_bound (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 8 ≤ n) (m : ℕ) (hm : 0 < m) (hodd : Odd m)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖heckeAverage (D.eigenvalues (2 ^ n)) m -
        (((m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m : ℝ) : ℂ)‖ ≤
      (uniformEllipticConstant δ + 576 / ((k : ℝ) + 1)) *
        ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
        ((m : ℝ) ^ δ *
          ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) (m : ℤ)).card : ℝ) +
          divisorRatioSum k m) := by
  have hE := D.ellipticTerm_bound n hn m hm hodd δ hδ
  have hC := D.cuspTerm_bound n hn m hm
  have hS := D.scalarFactor_error n hn
  have hW := square_scalar_weight_le_divisorWeightSum k m hm
  have hi : 0 ≤ PopaTrace.squareIndicator m := by unfold PopaTrace.squareIndicator; split_ifs <;> norm_num
  have hbase : 0 ≤ (m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m := by positivity
  have hScalar : ‖((((D.scalarFactor n - 1) *
      ((m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m)) : ℝ) : ℂ)‖ ≤
      (8 / ((k : ℝ) + 1) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ)) * divisorWeightSum k m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hbase]
    exact (mul_le_mul_of_nonneg_right hS hbase).trans
      (mul_le_mul_of_nonneg_left hW (by positivity))
  have hEq : heckeAverage (D.eigenvalues (2 ^ n)) m -
      (((m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m : ℝ) : ℂ) =
      (((D.scalarFactor n - 1) *
        ((m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m) : ℝ) : ℂ) +
        D.ellipticTerm n m + D.cuspTerm n m := by
    rw [D.mean_trace_parts n (by omega) m hm hodd]
    push_cast
    ring
  rw [hEq, ← divisorWeightSum_eq_ratio k m hm]
  have hM : 0 ≤ (m : ℝ) ^ δ *
      ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) (m : ℤ)).card : ℝ) := by positivity
  have hR := divisorWeightSum_nonneg k m
  have hK := (uniformEllipticConstant_pos hδ).le
  have hN : 0 ≤ ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by positivity
  have hden : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
  calc
    _ ≤ ‖((((D.scalarFactor n - 1) *
        ((m : ℝ) ^ (-1 / 2 : ℝ) * PopaTrace.squareIndicator m)) : ℝ) : ℂ)‖ +
        ‖D.ellipticTerm n m‖ + ‖D.cuspTerm n m‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ _ := by
      simp only [div_eq_mul_inv, one_mul] at hScalar hC hden ⊢
      nlinarith [mul_nonneg hK (mul_nonneg hN hR),
        mul_nonneg hden (mul_nonneg hN hM), mul_nonneg hden (mul_nonneg hN hR)]

theorem uniform_prime_trace_bound (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 8 ≤ n) (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖heckeAverage (D.eigenvalues (2 ^ n)) p‖ ≤
      (uniformEllipticConstant δ + 576 / ((k : ℝ) + 1)) *
        ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
        ((p : ℝ) ^ δ *
          ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) (p : ℤ)).card : ℝ) +
          (p : ℝ) ^ (-((k : ℝ) + 1) / 2)) := by
  have hE := D.ellipticTerm_bound n hn p hp.pos hodd δ hδ
  have hC := normalizedCusp_prime_bound k n p hp (Fintype.card (Family (2 ^ n)) : ℝ)
    (MartinDimension.polynomial_degree_dimension_lower k n hn _ D.dimension_formula)
  have hC' : ‖D.cuspTerm n p‖ ≤ (576 / ((k : ℝ) + 1)) *
      ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (p : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
    rw [cuspTerm, Complex.norm_real, Real.norm_eq_abs]
    simpa only [div_eq_mul_inv, level_inverse_sqrt, mul_assoc] using hC
  rw [D.mean_trace_parts n (by omega) p hp.pos hodd, PopaTrace.squareIndicator_prime hp]
  simp only [mul_zero, Complex.ofReal_zero, zero_add]
  have hK := (uniformEllipticConstant_pos hδ).le
  have hx : 0 ≤ uniformEllipticConstant δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
      (p : ℝ) ^ (-((k : ℝ) + 1) / 2) := by positivity
  have hy : 0 ≤ (576 / ((k : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
      ((p : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) (p : ℤ)).card : ℝ)) := by positivity
  exact (norm_add_le _ _).trans (by nlinarith)

theorem square_mean_trace (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 3 ≤ n) (p : ℕ) (hp : 0 < p) (hodd : Odd p) :
    heckeAverage (D.eigenvalues (2 ^ n)) (p ^ 2) =
      ((D.scalarFactor n / (p : ℝ) : ℝ) : ℂ) +
        D.ellipticTerm n (p ^ 2) + D.cuspTerm n (p ^ 2) := by
  rw [D.mean_trace_parts n hn (p ^ 2) (by positivity) (show Odd (p ^ 2) from hodd.pow),
    PopaTrace.squareIndicator_square, PopaTrace.square_inverse_sqrt, mul_one, div_eq_mul_inv]

theorem square_elliptic_bound (D : ArithmeticSpectralData k Family V)
    (n : ℕ) (hn : 8 ≤ n) (p : ℕ) (hp : 0 < p) (hodd : Odd p)
    (δ : ℝ) (hδ : 0 < δ) :
    ‖D.ellipticTerm n (p ^ 2)‖ ≤ uniformEllipticConstant δ *
      ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (p : ℝ) ^ (2 * δ) *
        (128 * (p : ℝ) / (2 : ℝ) ^ n + 4) := by
  have hE := D.ellipticTerm_bound n hn (p ^ 2) (by positivity)
    (show Odd (p ^ 2) from hodd.pow) δ hδ
  have hlevel : (2 : ℝ) ^ n = 16 * (((2 : ℤ) ^ (n - 4) : ℤ) : ℝ) := by
    push_cast
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 4) + 4) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hc := PrimeSquareCount.canonical_square_count_level (n - 4)
    (show (0 : ℤ) < p by exact_mod_cast hp) (show Odd (p : ℤ) by exact_mod_cast hodd) hlevel
  have hpow : (((p ^ 2 : ℕ) : ℝ)) ^ δ = (p : ℝ) ^ (2 * δ) := by
    push_cast
    exact (Real.rpow_natCast_mul (by positivity) 2 δ).symm
  rw [hpow] at hE
  push_cast at hE hc
  apply hE.trans
  exact mul_le_mul_of_nonneg_left hc (by have := (uniformEllipticConstant_pos hδ).le; positivity)

theorem small_square_surviving_empty (n p : ℕ) (hn : 8 ≤ n) (hp : 0 < p) (hodd : Odd p)
    (hsize : (p : ℝ) < (2 : ℝ) ^ n / 64) :
    SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) ((p ^ 2 : ℕ) : ℤ) = ∅ := by
  have hscale : (2 : ℝ) ^ n = 32 * (2 : ℝ) ^ (n - 5) := by
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 5) + 5) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hsizeR : 2 * (p : ℝ) < (2 : ℝ) ^ (n - 5) := by rw [hscale] at hsize; linarith
  have hsizeZ : 2 * (p : ℤ) < (2 : ℤ) ^ ((n - 4) - 1) := by
    rw [show (n - 4) - 1 = n - 5 by omega]
    exact_mod_cast hsizeR
  simpa only [Nat.cast_pow] using PrimeSquareCount.canonical_square_count_zero (n - 4)
    (by omega) (show (0 : ℤ) < p by exact_mod_cast hp)
    (show Odd (p : ℤ) by exact_mod_cast hodd) hsizeZ

theorem small_square_elliptic_zero (D : ArithmeticSpectralData k Family V)
    (n p : ℕ) (hn : 8 ≤ n) (hp : 0 < p) (hodd : Odd p)
    (hsize : (p : ℝ) < (2 : ℝ) ^ n / 64) : D.ellipticTerm n (p ^ 2) = 0 := by
  have h := D.ellipticTerm_bound n hn (p ^ 2) (by positivity)
    (show Odd (p ^ 2) from hodd.pow) 1 (by norm_num)
  rw [small_square_surviving_empty n p hn hp hodd hsize, Finset.card_empty,
    Nat.cast_zero, mul_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

theorem small_prime_square_trace_bound (D : ArithmeticSpectralData k Family V)
    (n p : ℕ) (hn : 8 ≤ n) (hp : p.Prime) (hodd : Odd p)
    (hsize : (p : ℝ) < (2 : ℝ) ^ n / 64) :
    SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) ((p ^ 2 : ℕ) : ℤ) = ∅ ∧
    ‖heckeAverage (D.eigenvalues (2 ^ n)) (p ^ 2) - ((1 / (p : ℝ) : ℝ) : ℂ)‖ ≤
      (584 / ((k : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by
  refine ⟨small_square_surviving_empty n p hn hp.pos hodd hsize, ?_⟩
  have hS := D.scalarFactor_error n hn
  have hC := normalizedCusp_prime_square_bound k n p hp (Fintype.card (Family (2 ^ n)) : ℝ)
    (MartinDimension.polynomial_degree_dimension_lower k n hn _ D.dimension_formula)
  have hC' : ‖D.cuspTerm n (p ^ 2)‖ ≤ (576 / ((k : ℝ) + 1)) *
      ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by
    rw [cuspTerm, Complex.norm_real, Real.norm_eq_abs]
    simpa only [div_eq_mul_inv, level_inverse_sqrt, mul_assoc] using hC
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hS' : ‖(((D.scalarFactor n - 1) / (p : ℝ) : ℝ) : ℂ)‖ ≤
      (8 / ((k : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hpR]
    exact (div_le_self (abs_nonneg _) hp1).trans hS
  have heq : heckeAverage (D.eigenvalues (2 ^ n)) (p ^ 2) - ((1 / (p : ℝ) : ℝ) : ℂ) =
      (((D.scalarFactor n - 1) / (p : ℝ) : ℝ) : ℂ) + D.cuspTerm n (p ^ 2) := by
    rw [D.square_mean_trace n (by omega) p hp.pos hodd,
      D.small_square_elliptic_zero n p hn hp.pos hodd hsize]
    push_cast
    ring
  rw [heq]
  calc
    _ ≤ ‖(((D.scalarFactor n - 1) / (p : ℝ) : ℝ) : ℂ)‖ +
        ‖D.cuspTerm n (p ^ 2)‖ := norm_add_le _ _
    _ ≤ (8 / ((k : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) +
        (576 / ((k : ℝ) + 1)) * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) := add_le_add hS' hC'
    _ = _ := by ring

end ArithmeticSpectralData
end DepthAspect.UnsignedDensity
