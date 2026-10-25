import DepthAspect.CoefficientHalfPlane
import DepthAspect.LocalGeneratingFunctions
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Nat.Prime.Int

/-!
# The actual odd Euler series in (84)

The multiplicative sequence here is only the odd factor. The full twisted
average is not asserted to be multiplicative. Its positive odd coefficients
are exactly the previously computed odd residue means, and all positive even
coefficients vanish.
-/
noncomputable section
open scoped BigOperators Classical
namespace DepthAspect.OddAverageEuler
open OddMeanMajorant

/-- Local coefficients at two encode restriction to odd integers. -/
def localValue (t : ℤ) (p e : ℕ) : ℂ :=
  if p = 2 then if e = 0 then 1 else 0 else (primeMean p t e : ℂ)

/-- The actual multiplicative extension of the odd local means. -/
def coefficient (t : ℤ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod (localValue t)

 theorem localValue_zero (t : ℤ) {p : ℕ} (hp : p.Prime) : localValue t p 0 = 1 := by
  by_cases hp2 : p = 2
  · simp [localValue, hp2]
  · simp [localValue, hp2, primeMean, hp, LocalResidueAverages.unitMean]

@[simp] theorem coefficient_zero (t : ℤ) : coefficient t 0 = 0 := by simp [coefficient]
@[simp] theorem coefficient_one (t : ℤ) : coefficient t 1 = 1 := by simp [coefficient]

/-- Multiplicativity follows from the disjoint actual prime factorizations. -/
theorem coefficient_mul (t : ℤ) {m n : ℕ} (h : m.Coprime n) :
    coefficient t (m * n) = coefficient t m * coefficient t n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [coefficient, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)]
  rw [Nat.factorization_mul hm hn,
    Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors]

 theorem coefficient_prime_power (t : ℤ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    coefficient t (p ^ e) = localValue t p e := by
  rw [coefficient, if_neg (pow_ne_zero _ hp.ne_zero), hp.factorization_pow]
  exact Finsupp.prod_single_index (localValue_zero t hp)

/-- At an odd positive index this is exactly the literal odd mean product. -/
theorem coefficient_odd (t : ℤ) {n : ℕ} (hn : Odd n) :
    coefficient t n = (oddMean n t : ℂ) := by
  have hn0 : n ≠ 0 := by intro h; simp [h] at hn
  have htwo : 2 ∉ n.primeFactors := by
    intro h
    exact hn.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors h)
  rw [coefficient, if_neg hn0, Nat.prod_factorization_eq_prod_primeFactors]
  unfold oddMean
  rw [Finset.erase_eq_of_notMem htwo]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  have hp2 : p ≠ 2 := by intro h; exact htwo (h ▸ hp)
  simp only [localValue, hp2, ↓reduceIte]

 theorem coefficient_even (t : ℤ) {n : ℕ} (hn : Even n) : coefficient t n = 0 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have htwo : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, even_iff_two_dvd.mp hn, hn0⟩
  have hv : n.factorization 2 ≠ 0 := by
    exact Finsupp.mem_support_iff.mp htwo
  rw [coefficient, if_neg hn0, Nat.prod_factorization_eq_prod_primeFactors]
  exact Finset.prod_eq_zero htwo (by simp [localValue, hv])

/-- Its actual squarefree majorant, derived from the local finite means. -/
theorem coefficient_majorant (t : ℤ) (b : ℕ)
    (u : CoefficientDecomposition.SquarefreeOdd) (v : ℕ) (hv : 0 < v) (_ho : Odd v) :
    ‖coefficient t (2 ^ b * (u : ℕ) * v ^ 2)‖ ≤ 1 / ((u : ℕ).totient : ℝ) := by
  rcases Nat.even_or_odd (2 ^ b * (u : ℕ) * v ^ 2) with he | ho
  · rw [coefficient_even t he, norm_zero]
    positivity
  · rw [coefficient_odd t ho, Complex.norm_real, Real.norm_eq_abs]
    exact abs_oddMean_le u.property.1 u.property.2 hv.ne' b t

 theorem summable_norm_terms (t : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun n : ℕ => ‖LSeries.term (coefficient t) s n‖) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [LSeries.term_of_ne_zero (Nat.succ_ne_zero _), norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.succ_pos _) s] using
      (CoefficientHalfPlane.absolute_sum_of_majorant (coefficient t)
        (coefficient_majorant t) hs).1

 theorem weighted_multiplicative (t : ℤ) {s : ℂ} (hs : s ≠ 0)
    {m n : ℕ} (hmn : m.Coprime n) :
    LSeries.term (coefficient t) s (m * n) =
      LSeries.term (coefficient t) s m * LSeries.term (coefficient t) s n := by
  have heq (n : ℕ) : LSeries.term (coefficient t) s n =
      coefficient t n * riemannZetaSummandHom hs n := by
    simp only [LSeries.term_of_ne_zero' hs, riemannZetaSummandHom,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.cpow_neg, div_eq_mul_inv]
  simp only [heq, coefficient_mul t hmn, map_mul]
  ring

/-- The Euler product is a theorem about the actual odd coefficient sequence. -/
theorem euler_hasProd (t : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term (coefficient t) s (p.val ^ e))
      (LSeries (coefficient t) s) := by
  have hs0 : s ≠ 0 := by intro hz; norm_num [hz] at hs
  apply EulerProduct.eulerProduct_hasProd
  · simp
  · exact fun {m n} h => weighted_multiplicative t hs0 h
  · exact summable_norm_terms t hs
  · simp [LSeries.term]

/-- The literal local generating function, with the factor at two equal to one. -/
def localFactor (t : ℤ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if hp2 : p.val = 2 then 1 else
    if (t : ZMod p.val) = 0 then (1 - ((p.val : ℂ) ^ (-s)) ^ 2)⁻¹ else
      ((p.val : ℂ) ^ 2 - ((p.val : ℂ) + 1) * (p.val : ℂ) ^ (-s) -
        ((p.val : ℂ) + 1) * ((p.val : ℂ) ^ (-s)) ^ 2) /
        ((1 - ((p.val : ℂ) ^ (-s)) ^ 2) * ((p.val : ℂ) ^ 2 - (p.val : ℂ) ^ (-s)))

 theorem localFactor_eq_series (t : ℤ) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    localFactor t p s = ∑' e : ℕ, LSeries.term (coefficient t) s (p.val ^ e) := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  have hs0 : s ≠ 0 := by intro hz; norm_num [hz] at hs
  have hw : ‖(p.val : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.property.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (by linarith)
  have heq (e : ℕ) : LSeries.term (coefficient t) s (p.val ^ e) =
      localValue t p.val e * ((p.val : ℂ) ^ (-s)) ^ e := by
    rw [LSeries.term_of_ne_zero' hs0, coefficient_prime_power t p.property,
      div_eq_mul_inv, ← Complex.cpow_neg]
    congr 1
    exact map_pow (riemannZetaSummandHom hs0) p.val e
  simp_rw [heq]
  by_cases hp2 : p.val = 2
  · simp [localFactor, hp2, localValue, tsum_ite_eq]
  · simp only [localFactor, hp2, ↓reduceDIte, localValue, ↓reduceIte,
      primeMean, dif_pos p.property]
    by_cases ht : (t : ZMod p.val) = 0
    · rw [if_pos ht, ht]
      exact (LocalGeneratingFunctions.unitMean_zero_hasSum hp2 hw).tsum_eq.symm
    · rw [if_neg ht]
      exact (LocalGeneratingFunctions.unitMean_nonzero_hasSum hp2 ht hw).tsum_eq.symm

/-- Absolute Euler-product convergence and its equality to the actual series. -/
theorem localFactor_hasProd (t : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasProd (fun p : Nat.Primes => localFactor t p s) (LSeries (coefficient t) s) := by
  simpa only [localFactor_eq_series t _ (by linarith : 0 < s.re)] using euler_hasProd t hs

/-- Distinct positive prime powers give distinct natural indices. -/
theorem positive_prime_power_injective :
    Function.Injective (fun i : Nat.Primes × ℕ => i.1.val ^ (i.2 + 1)) := by
  rintro ⟨p, a⟩ ⟨q, b⟩ h
  obtain ⟨hpq, hab⟩ := p.property.pow_inj q.property h
  exact Prod.ext (Subtype.ext hpq) hab

/-- Restricting the absolutely convergent series to powers of one prime. -/
private theorem primePower_norm_summable (t : ℤ) (p : Nat.Primes)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun e : ℕ => ‖LSeries.term (coefficient t) s (p.val ^ e)‖) :=
  (summable_norm_terms t hs).comp_injective
    (show Function.Injective (fun e : ℕ => p.val ^ e) from
      Nat.pow_right_injective p.property.one_lt)

private theorem localFactor_sub_one_eq (t : ℤ) (p : Nat.Primes)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    localFactor t p s - 1 =
      ∑' e : ℕ, LSeries.term (coefficient t) s (p.val ^ (e + 1)) := by
  have hpowers : Summable (fun e : ℕ => LSeries.term (coefficient t) s (p.val ^ e)) :=
    (primePower_norm_summable t p hs).of_norm
  rw [localFactor_eq_series t p (by linarith : 0 < s.re), hpowers.tsum_eq_zero_add]
  have hzero : LSeries.term (coefficient t) s (p.val ^ 0) = 1 := by
    simp only [pow_zero, LSeries.term, one_ne_zero, ↓reduceIte,
      coefficient_one, Nat.cast_one, Complex.one_cpow, div_one]
  rw [hzero]
  ring

private theorem primePower_tail_norm_summable (t : ℤ)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes =>
      ∑' e : ℕ, ‖LSeries.term (coefficient t) s (p.val ^ (e + 1))‖) := by
  have hpair : Summable (fun i : Nat.Primes × ℕ =>
      ‖LSeries.term (coefficient t) s (i.1.val ^ (i.2 + 1))‖) :=
    (summable_norm_terms t hs).comp_injective positive_prime_power_injective
  exact ((summable_prod_of_nonneg (fun i : Nat.Primes × ℕ =>
    norm_nonneg (LSeries.term (coefficient t) s (i.1.val ^ (i.2 + 1))))).mp hpair).2

/-- Absolute convergence of the Euler product in its usual analytic sense:
the deviations of the local factors from one are norm-summable. -/
theorem localFactor_deviation_summable (t : ℤ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes => ‖localFactor t p s - 1‖) := by
  apply (primePower_tail_norm_summable t hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  rw [localFactor_sub_one_eq t p hs]
  have hshift : Summable (fun e : ℕ =>
      ‖LSeries.term (coefficient t) s (p.val ^ (e + 1))‖) :=
    (summable_nat_add_iff 1
      (f := fun e : ℕ => ‖LSeries.term (coefficient t) s (p.val ^ e)‖)).mpr
        (primePower_norm_summable t p hs)
  exact norm_tsum_le_tsum_norm
    (f := fun e : ℕ => LSeries.term (coefficient t) s (p.val ^ (e + 1))) hshift

end DepthAspect.OddAverageEuler
