import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Finite coefficient-norm bounds used in (93)

The main theorem takes normalized Parseval as an explicit premise and proves
its Cauchy–Schwarz consequence. No assertion here constructs a Dirichlet
character expansion. Product, permutation, and zero-extension identities are
proved for the coefficient arrays themselves.
-/

open scoped BigOperators

namespace DepthAspect.CoefficientBounds

noncomputable def coefficientL1 {ι : Type*} [Fintype ι] (c : ι → ℂ) : ℝ :=
  ∑ i, ‖c i‖

/-- Values bounded in modulus by one have squared norm at most their finite
support size. -/
theorem square_sum_le_support_card {κ : Type*} [Fintype κ]
    (g : κ → ℂ) (hg : ∀ j, ‖g j‖ ≤ 1) :
    ∑ j, ‖g j‖ ^ 2 ≤ ((Finset.univ.filter fun j => g j ≠ 0).card : ℝ) := by
  classical
  have heq : (∑ j, ‖g j‖ ^ 2) =
      ∑ j ∈ Finset.univ.filter (fun j => g j ≠ 0), ‖g j‖ ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : g j = 0 <;> simp [h]
  rw [heq]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => g j ≠ 0), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonneg := norm_nonneg (g j)
      have hbound := hg j
      nlinarith
    _ = _ := by simp

/-- The normalized Parseval identity implies the square-root-of-support bound
in (93). The two finite index types have equal cardinality, as the group and
its character group do. -/
theorem l1_le_sqrt_support_of_parseval
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (c : ι → ℂ) (g : κ → ℂ)
    (hcard : Fintype.card ι = Fintype.card κ)
    (hparseval : (∑ i, ‖c i‖ ^ 2) = (∑ j, ‖g j‖ ^ 2) / (Fintype.card κ : ℝ))
    (hg : ∀ j, ‖g j‖ ≤ 1) :
    coefficientL1 c ≤ Real.sqrt ((Finset.univ.filter fun j => g j ≠ 0).card : ℝ) := by
  classical
  have hn : (Fintype.card κ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : ι => ‖c i‖) (fun _ : ι => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcauchy
  rw [hcard, hparseval, div_mul_cancel₀ _ hn] at hcauchy
  exact Real.le_sqrt_of_sq_le (hcauchy.trans (square_sum_le_support_card g hg))

/-- A permutation of coefficients preserves their total absolute value. In a
Fourier application, multiplication by a character permutes the coefficients. -/
theorem coefficientL1_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (c : κ → ℂ) :
    coefficientL1 (fun i => c (e i)) = coefficientL1 c := by
  unfold coefficientL1
  exact Equiv.sum_comp e (fun j => ‖c j‖)

/-- The coefficient norm of a tensor product factors. This is the finite
coefficient identity used with Chinese-remainder decompositions. -/
theorem coefficientL1_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (d : κ → ℂ) :
    coefficientL1 (fun p : ι × κ => c p.1 * d p.2) =
      coefficientL1 c * coefficientL1 d := by
  simp only [coefficientL1, Fintype.sum_prod_type, norm_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Adding zero coefficients preserves the total absolute value. In an
inflation application, the old characters are embedded among the new ones;
identifying the inflated Fourier coefficients with these values is a separate
Fourier-algebra step. -/
theorem coefficientL1_zero_extension {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ↪ κ) (c : ι → ℂ) (d : κ → ℂ)
    (himage : ∀ i, d (e i) = c i)
    (hzero : ∀ j, (∀ i, e i ≠ j) → d j = 0) :
    coefficientL1 d = coefficientL1 c := by
  classical
  unfold coefficientL1
  calc
    (∑ j, ‖d j‖) = ∑ j ∈ Finset.univ.image e, ‖d j‖ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnot
      have hout : ∀ i, e i ≠ j := by
        intro i he
        exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
      simp [hzero j hout]
    _ = ∑ i, ‖c i‖ := by
      rw [Finset.sum_image]
      · simp only [himage]
      · intro i hi j hj he
        exact e.injective he

/-- The even-degree coefficient in (86), as a function of the preceding
unrestricted local average `U`. -/
noncomputable def evenLocalCoefficient (p U : ℝ) : ℝ :=
  (p - 2) / (p - 1) + U / (p * (p - 1))

/-- The odd-degree coefficient in (86). -/
noncomputable def oddLocalCoefficient (p U : ℝ) : ℝ :=
  -(1 / (p - 1)) + U / (p * (p - 1))

/-- The even-degree coefficient is in `[0,1]` whenever the prior average is.
The real inequality `p≥2` suffices; primality is unnecessary for this step. -/
theorem evenLocalCoefficient_bounds (p U : ℝ) (hp : 2 ≤ p)
    (hU0 : 0 ≤ U) (hU1 : U ≤ 1) :
    0 ≤ evenLocalCoefficient p U ∧ evenLocalCoefficient p U ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - 1 := by linarith
  have hD : 0 < p * (p - 1) := mul_pos hp0 hd
  constructor
  · unfold evenLocalCoefficient
    exact add_nonneg (div_nonneg (by linarith) hd.le) (div_nonneg hU0 hD.le)
  · have heq : evenLocalCoefficient p U = (p * (p - 2) + U) / (p * (p - 1)) := by
      unfold evenLocalCoefficient
      field_simp
    rw [heq, div_le_iff₀ hD]
    nlinarith

/-- The odd-degree coefficient lies between `−1/(p−1)` and zero. -/
theorem oddLocalCoefficient_bounds (p U : ℝ) (hp : 2 ≤ p)
    (hU0 : 0 ≤ U) (hU1 : U ≤ 1) :
    -(1 / (p - 1)) ≤ oddLocalCoefficient p U ∧ oddLocalCoefficient p U ≤ 0 := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - 1 := by linarith
  have hD : 0 < p * (p - 1) := mul_pos hp0 hd
  have hterm0 : 0 ≤ U / (p * (p - 1)) := div_nonneg hU0 hD.le
  have hterm1 : U / (p * (p - 1)) ≤ 1 / (p - 1) := by
    have heq : p / (p * (p - 1)) = 1 / (p - 1) := by field_simp
    rw [← heq]
    exact div_le_div_of_nonneg_right (by linarith) hD.le
  unfold oddLocalCoefficient
  constructor <;> linarith

/-- The exact odd coefficient majorant used below (86). -/
theorem oddLocalCoefficient_abs_le (p U : ℝ) (hp : 2 ≤ p)
    (hU0 : 0 ≤ U) (hU1 : U ≤ 1) :
    |oddLocalCoefficient p U| ≤ 1 / (p - 1) := by
  have h := oddLocalCoefficient_bounds p U hp hU0 hU1
  rw [abs_of_nonpos h.2]
  linarith [h.1]

/-- The exact even coefficient majorant used below (86). -/
theorem evenLocalCoefficient_abs_le (p U : ℝ) (hp : 2 ≤ p)
    (hU0 : 0 ≤ U) (hU1 : U ≤ 1) :
    |evenLocalCoefficient p U| ≤ 1 := by
  have h := evenLocalCoefficient_bounds p U hp hU0 hU1
  rw [abs_of_nonneg h.1]
  exact h.2

/-- The recurrence step for the unrestricted local average in (86). -/
noncomputable def localMeanStep (p U : ℝ) (evenDegree : Bool) : ℝ :=
  (if evenDegree then 1 - 1 / p else 0) + U / p ^ 2

/-- The recurrence preserves `[0,1]`. -/
theorem localMeanStep_bounds (p U : ℝ) (evenDegree : Bool) (hp : 2 ≤ p)
    (hU0 : 0 ≤ U) (hU1 : U ≤ 1) :
    0 ≤ localMeanStep p U evenDegree ∧ localMeanStep p U evenDegree ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp0
  have hrecip0 : 0 ≤ 1 / p := div_nonneg (by norm_num) hp0.le
  have hrecip1 : 1 / p ≤ 1 := by
    rw [div_le_iff₀ hp0]
    linarith
  have hterm0 : 0 ≤ U / p ^ 2 := div_nonneg hU0 hp2.le
  have hterm1 : U / p ^ 2 ≤ 1 / p := by
    have heq : p / p ^ 2 = 1 / p := by field_simp
    rw [← heq]
    exact div_le_div_of_nonneg_right (by linarith) hp2.le
  cases evenDegree <;> simp only [localMeanStep, Bool.false_eq_true, ↓reduceIte,
    zero_add] <;> constructor <;> linarith

/-- The sequence `U_b` defined by the recurrence displayed in (86). Its
identification with an average over discriminant residue classes is separate. -/
noncomputable def unrestrictedLocalAverage (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | b + 1 => localMeanStep p (unrestrictedLocalAverage p b) (decide (Even (b + 1)))

 theorem unrestrictedLocalAverage_bounds (p : ℝ) (hp : 2 ≤ p) (b : ℕ) :
    0 ≤ unrestrictedLocalAverage p b ∧ unrestrictedLocalAverage p b ≤ 1 := by
  induction b with
  | zero => norm_num [unrestrictedLocalAverage]
  | succ b hb =>
      exact localMeanStep_bounds p (unrestrictedLocalAverage p b)
        (decide (Even (b + 1))) hp hb.1 hb.2

/-- The coefficient sequence specified by (86) for `p ∤ t`. -/
noncomputable def localCoefficient (p : ℝ) (b : ℕ) : ℝ :=
  if b = 0 then 1
  else if Even b then evenLocalCoefficient p (unrestrictedLocalAverage p (b - 1))
  else oddLocalCoefficient p (unrestrictedLocalAverage p (b - 1))

 theorem localCoefficient_even_bound (p : ℝ) (hp : 2 ≤ p) (j : ℕ) :
    |localCoefficient p (2 * j)| ≤ 1 := by
  by_cases hj : j = 0
  · simp [localCoefficient, hj]
  · have hne : 2 * j ≠ 0 := by omega
    have heven : Even (2 * j) := ⟨j, by omega⟩
    have hU := unrestrictedLocalAverage_bounds p hp (2 * j - 1)
    simpa [localCoefficient, hne, heven] using
      evenLocalCoefficient_abs_le p (unrestrictedLocalAverage p (2 * j - 1)) hp hU.1 hU.2

 theorem localCoefficient_odd_bound (p : ℝ) (hp : 2 ≤ p) (j : ℕ) :
    |localCoefficient p (2 * j + 1)| ≤ 1 / (p - 1) := by
  have hne : 2 * j + 1 ≠ 0 := by omega
  have hodd : ¬ Even (2 * j + 1) := by
    rintro ⟨a, ha⟩
    omega
  have hU := unrestrictedLocalAverage_bounds p hp (2 * j + 1 - 1)
  simpa [localCoefficient, hne, hodd] using
    oddLocalCoefficient_abs_le p (unrestrictedLocalAverage p (2 * j + 1 - 1)) hp hU.1 hU.2

end DepthAspect.CoefficientBounds
