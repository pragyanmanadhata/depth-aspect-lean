import DepthAspect.DyadicFixedLines
import DepthAspect.LocalBounds
import DepthAspect.TracePolynomial
import DepthAspect.Dimension
import DepthAspect.CuspBounds
import DepthAspect.SurvivingTraces
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Conditional uniform bounds for actual finite trace models

The matrix-root and totient terms are concrete. Class-number growth and the
identification of these finite models with spectral traces are separate inputs.
Class-number growth is an intermediate obligation to be discharged by the
internal proof of Lemma 2.2; only the cited spectral trace formula is an external
input. The local bounds and their summation are proved here, rather than assumed.
The parameter `k` below is the trace-polynomial degree, i.e. weight minus two.
-/
open scoped BigOperators
namespace DepthAspect.TraceBounds
open DyadicFixedLines ContentReduction

noncomputable def decayRatio (δ : ℝ) : ℝ := (2 : ℝ) ^ (-(1 / 2 + 2 * δ))
noncomputable def contentMajorant (δ : ℝ) (p : ℕ × ℕ) : ℝ :=
  decayRatio δ ^ p.1 * ((p.2 : ℝ) + 1) ^ (-1 - 2 * δ)
/-- The ordinary positive p-series, equal to ζ(1+2δ) in its convergence domain. -/
noncomputable def zetaMajorant (δ : ℝ) : ℝ :=
  ∑' v : ℕ, ((v : ℝ) + 1) ^ (-1 - 2 * δ)

theorem decayRatio_nonneg (δ : ℝ) : 0 ≤ decayRatio δ := by
  exact Real.rpow_nonneg (by norm_num) _

theorem decayRatio_lt_one {δ : ℝ} (hδ : 0 < δ) : decayRatio δ < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  linarith

theorem content_pseries_summable {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun v : ℕ => ((v : ℝ) + 1) ^ (-1 - 2 * δ)) := by
  have h := (Real.summable_nat_rpow.mpr (by linarith : -1 - 2 * δ < -1)).comp_injective
    (show Function.Injective (fun v : ℕ => v + 1) from fun _ _ h => Nat.add_right_cancel h)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

theorem zetaMajorant_nonneg (δ : ℝ) : 0 ≤ zetaMajorant δ := by
  apply tsum_nonneg
  intro v
  positivity

/-- Both extended sums in (28) converge; their product bounds every finite
set of content pairs. The second coordinate represents the positive odd part
minus one; allowing even positive parts only enlarges the majorant. -/
theorem content_majorant_sum_bound {δ : ℝ} (hδ : 0 < δ) (s : Finset (ℕ × ℕ)) :
    ∑ p ∈ s, contentMajorant δ p ≤ zetaMajorant δ / (1 - decayRatio δ) := by
  have hq := decayRatio_lt_one hδ
  let E := s.image Prod.fst
  let V := s.image Prod.snd
  have hs : s ⊆ E ×ˢ V := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  have he : (∑ e ∈ E, decayRatio δ ^ e) ≤ (1 - decayRatio δ)⁻¹ := by
    have hz := (summable_geometric_of_lt_one (decayRatio_nonneg δ) (decayRatio_lt_one hδ)).sum_le_tsum
      E (fun _ _ => pow_nonneg (decayRatio_nonneg δ) _)
    rwa [tsum_geometric_of_lt_one (decayRatio_nonneg δ) (decayRatio_lt_one hδ)] at hz
  have hv : (∑ v ∈ V, ((v : ℝ) + 1) ^ (-1 - 2 * δ)) ≤ zetaMajorant δ :=
    (content_pseries_summable hδ).sum_le_tsum V (fun _ _ => by positivity)
  calc
    _ ≤ ∑ p ∈ E ×ˢ V, contentMajorant δ p :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by
        unfold contentMajorant; exact mul_nonneg (pow_nonneg (decayRatio_nonneg δ) _) (by positivity))
    _ = (∑ e ∈ E, decayRatio δ ^ e) *
        (∑ v ∈ V, ((v : ℝ) + 1) ^ (-1 - 2 * δ)) := by
      simp only [contentMajorant, Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ (1 - decayRatio δ)⁻¹ * zetaMajorant δ :=
      mul_le_mul he hv (by positivity) (by positivity)
    _ = zetaMajorant δ / (1 - decayRatio δ) := by ring

/-- Actual fixed-line second difference, viewed as a real scalar. -/
noncomputable def matrixDifference (n : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  (fixedLineCount n M : ℝ) - 2 * (fixedLineCount (n - 1) M : ℝ) +
    (fixedLineCount (n - 2) M : ℝ)

theorem matrixDifference_zero (n : ℕ) (hn : 3 ≤ n)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : Odd (Matrix.det M))
    (hbad : ¬ (2 : ℤ) ^ (n - 2) ∣ (Matrix.trace M) ^ 2 - 4 * Matrix.det M) :
    matrixDifference n M = 0 := by
  have hz := fixedLineCount_discriminant_support n hn M hdet hbad
  unfold matrixDifference
  exact_mod_cast hz

/-- The exact dyadic content controls the actual matrix difference. -/
theorem matrixDifference_bound (n e : ℕ) (hn : 3 ≤ n)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : Odd (Matrix.det M))
    (v A B C : ℤ) (hv : Odd v) (hprim : Odd A ∨ Odd B ∨ Odd C)
    (hA : M 1 0 = v * (2 ^ e * A))
    (hB : M 1 1 - M 0 0 = v * (2 ^ e * B))
    (hC : -M 0 1 = v * (2 ^ e * C)) :
    |matrixDifference n M| ≤ 16 * (2 : ℝ) ^ (((n : ℝ) + e) / 2) := by
  unfold matrixDifference
  rw [fixedLineCount_eq_rho n (by omega) M hdet,
    fixedLineCount_eq_rho (n - 1) (by omega) M hdet,
    fixedLineCount_eq_rho (n - 2) (by omega) M hdet, hA, hB, hC,
    rho_odd_content n v _ _ _ hv, rho_odd_content (n - 1) v _ _ _ hv,
    rho_odd_content (n - 2) v _ _ _ hv]
  exact LocalBounds.second_difference_bound_real n e A B C hprim

/-- Exact real-power algebra in (27), with `R=|D|` and positive content part v. -/
theorem content_weight_identity (n e : ℕ) (R v δ : ℝ) (hR : 0 < R) (hv : 0 < v) :
    (R / ((2 : ℝ) ^ e * v) ^ 2) ^ (1 / 2 + δ) *
        (2 : ℝ) ^ (((n : ℝ) + e) / 2) =
      (2 : ℝ) ^ ((n : ℝ) / 2) * R ^ (1 / 2 + δ) *
        decayRatio δ ^ e * v ^ (-1 - 2 * δ) := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  rw [Real.div_rpow hR.le (sq_nonneg _),
    ← Real.rpow_natCast_mul (by positivity : 0 ≤ (2 : ℝ) ^ e * v) 2 (1 / 2 + δ),
    Real.mul_rpow (by positivity) hv.le]
  norm_num only [Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul htwo.le e (2 * (1 / 2 + δ)),
    div_eq_mul_inv, mul_inv,
    ← Real.rpow_neg htwo.le, ← Real.rpow_neg hv.le]
  have hp : (2 : ℝ) ^ (-((e : ℝ) * (2 * (1 / 2 + δ)))) *
        (2 : ℝ) ^ (((n : ℝ) + e) / 2) =
      (2 : ℝ) ^ ((n : ℝ) / 2) * decayRatio δ ^ e := by
    unfold decayRatio
    rw [← Real.rpow_mul_natCast htwo.le,
      ← Real.rpow_add htwo, ← Real.rpow_add htwo]
    congr 1
    ring
  rw [show -(2 * (1 / 2 + δ)) = -1 - 2 * δ by ring]
  calc
    _ = ((2 : ℝ) ^ (-((e : ℝ) * (2 * (1 / 2 + δ)))) *
          (2 : ℝ) ^ (((n : ℝ) + e) / 2)) *
        R ^ (1 / 2 + δ) * v ^ (-1 - 2 * δ) := by ring
    _ = _ := by rw [hp]; ring

/-- A weighted matrix term for one positive content. The primitive residual
coefficients are data; their arithmetic properties occur in `IsContentDatum`. -/
structure ContentDatum where
  matrix : Matrix (Fin 2) (Fin 2) ℤ
  weight : ℝ
  A : ℤ
  B : ℤ
  C : ℤ

/-- Faithful hypotheses for a content term. The only size input is the explicit
class-number growth bound. No root-count or trace estimate is a field. -/
structure IsContentDatum (p : ℕ × ℕ) (D : ℤ) (Ccl δ : ℝ) (F : ContentDatum) : Prop where
  oddDet : Odd (Matrix.det F.matrix)
  oddPart : Odd ((p.2 : ℤ) + 1)
  primitive : Odd F.A ∨ Odd F.B ∨ Odd F.C
  coeffA : F.matrix 1 0 = ((p.2 : ℤ) + 1) * (2 ^ p.1 * F.A)
  coeffB : F.matrix 1 1 - F.matrix 0 0 = ((p.2 : ℤ) + 1) * (2 ^ p.1 * F.B)
  coeffC : -F.matrix 0 1 = ((p.2 : ℤ) + 1) * (2 ^ p.1 * F.C)
  discriminant : (Matrix.trace F.matrix) ^ 2 - 4 * Matrix.det F.matrix = D
  weight_nonneg : 0 ≤ F.weight
  class_number_growth : F.weight ≤
    Ccl * (|(D : ℝ)| / ((2 : ℝ) ^ p.1 * ((p.2 : ℝ) + 1)) ^ 2) ^ (1 / 2 + δ)

/-- Equation (27), without its optional zero-support indicator, for an actual
weighted fixed-line term. -/
theorem content_term_bound (n : ℕ) (hn : 3 ≤ n) (p : ℕ × ℕ)
    (D : ℤ) (hD : D < 0) (Ccl δ : ℝ) (hC : 0 ≤ Ccl)
    (F : ContentDatum) (hF : IsContentDatum p D Ccl δ F) :
    |F.weight * matrixDifference n F.matrix| ≤
      16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * |(D : ℝ)| ^ (1 / 2 + δ) *
        contentMajorant δ p := by
  have hR : 0 < |(D : ℝ)| := abs_pos.mpr (by exact_mod_cast ne_of_lt hD)
  have hm := matrixDifference_bound n p.1 hn F.matrix hF.oddDet
    ((p.2 : ℤ) + 1) F.A F.B F.C hF.oddPart hF.primitive hF.coeffA hF.coeffB hF.coeffC
  rw [abs_mul, abs_of_nonneg hF.weight_nonneg]
  calc
    _ ≤ (Ccl * (|(D : ℝ)| / ((2 : ℝ) ^ p.1 * ((p.2 : ℝ) + 1)) ^ 2) ^
        (1 / 2 + δ)) * (16 * (2 : ℝ) ^ (((n : ℝ) + p.1) / 2)) :=
      mul_le_mul hF.class_number_growth hm (abs_nonneg _) (by positivity)
    _ = 16 * Ccl * ((|(D : ℝ)| / ((2 : ℝ) ^ p.1 * ((p.2 : ℝ) + 1)) ^ 2) ^
        (1 / 2 + δ) * (2 : ℝ) ^ (((n : ℝ) + p.1) / 2)) := by ring
    _ = _ := by
      rw [content_weight_identity n p.1 |(D : ℝ)| ((p.2 : ℝ) + 1) δ hR (by positivity)]
      unfold contentMajorant
      ring

/-- The finite weighted class-number model indexed by distinct contents. -/
noncomputable def contentTrace (n : ℕ) (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → ContentDatum) : ℝ :=
  ∑ p ∈ s, (F p).weight * matrixDifference n (F p).matrix

/-- Equation (28): sum the proved term bound over actual content indices and
majorize by the two convergent extended sums. -/
theorem contentTrace_bound (n : ℕ) (hn : 3 ≤ n) (s : Finset (ℕ × ℕ))
    (F : ℕ × ℕ → ContentDatum) (D : ℤ) (hD : D < 0)
    (Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hF : ∀ p ∈ s, IsContentDatum p D Ccl δ (F p)) :
    |contentTrace n s F| ≤
      16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * |(D : ℝ)| ^ (1 / 2 + δ) *
        zetaMajorant δ / (1 - decayRatio δ) := by
  unfold contentTrace
  calc
    _ ≤ ∑ p ∈ s, |(F p).weight * matrixDifference n (F p).matrix| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ s, 16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) *
        |(D : ℝ)| ^ (1 / 2 + δ) * contentMajorant δ p := by
      apply Finset.sum_le_sum
      intro p hp
      exact content_term_bound n hn p D hD Ccl δ hC (F p) (hF p hp)
    _ = (16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * |(D : ℝ)| ^ (1 / 2 + δ)) *
        (∑ p ∈ s, contentMajorant δ p) := by rw [Finset.mul_sum]
    _ ≤ (16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * |(D : ℝ)| ^ (1 / 2 + δ)) *
        (zetaMajorant δ / (1 - decayRatio δ)) :=
      mul_le_mul_of_nonneg_left (content_majorant_sum_bound hδ s) (by positivity)
    _ = _ := by ring

/-- The class-number model vanishes off the proved matrix-discriminant support. -/
theorem contentTrace_zero (n : ℕ) (hn : 3 ≤ n) (s : Finset (ℕ × ℕ))
    (F : ℕ × ℕ → ContentDatum) (D : ℤ) (Ccl δ : ℝ)
    (hF : ∀ p ∈ s, IsContentDatum p D Ccl δ (F p))
    (hbad : ¬ (2 : ℤ) ^ (n - 2) ∣ D) : contentTrace n s F = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  rw [matrixDifference_zero n hn (F p).matrix (hF p hp).oddDet
    (by rwa [(hF p hp).discriminant]), mul_zero]

/-- The lower dimension bound converts an actual normalization denominator
into its explicit reciprocal majorant. -/
theorem dimension_division_bound (k : ℕ) (d N x : ℝ) (hN : 0 < N)
    (hd : ((k : ℝ) + 1) * N / 64 ≤ d) (hx : 0 ≤ x) :
    x / (2 * d) ≤ 32 * x / (((k : ℝ) + 1) * N) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * d) (by positivity)).mpr
  calc
    x * (((k : ℝ) + 1) * N) ≤ x * (64 * d) :=
      mul_le_mul_of_nonneg_left (by linarith) hx
    _ = (32 * x) * (2 * d) := by ring

theorem sqrt_div_self {N : ℝ} (hN : 0 < N) :
    Real.sqrt N / N = 1 / Real.sqrt N := by
  have hS := Real.sqrt_pos.mpr hN
  field_simp [ne_of_gt hN, ne_of_gt hS]
  nlinarith [Real.sq_sqrt hN.le]

/-- The dyadic version of the restricted totient definition of Φ in (2).
No bound is built into this definition. -/
noncomputable def cuspPhi (h a d : ℕ) : ℕ :=
  CuspBounds.restrictedCuspSum h
    (fun j => (2 : ℤ) ^ min j (h - j) ∣ (a : ℤ) - d)

/-- The actual cusp second difference from this restricted totient sum. -/
noncomputable def cuspDifference (n a d : ℕ) : ℝ :=
  (cuspPhi n a d : ℝ) - 2 * (cuspPhi (n - 1) a d : ℝ) +
    (cuspPhi (n - 2) a d : ℝ)

theorem cuspDifference_bound (n a d : ℕ) :
    |cuspDifference n a d| ≤ 6 * Real.sqrt ((2 : ℝ) ^ n) := by
  apply CuspBounds.cusp_second_difference_bound_six (fun h => (cuspPhi h a d : ℝ))
  intro h
  constructor
  · positivity
  · dsimp [cuspPhi]
    exact_mod_cast CuspBounds.restrictedCuspSum_le h
      (fun j => (2 : ℤ) ^ min j (h - j) ∣ (a : ℤ) - d)

/-- The normalized cusp contribution for an actual finite divisor-pair set.
In applications the pairs satisfy a*d=m; the bound itself does not need this. -/
noncomputable def normalizedCusp (k n : ℕ) (d m : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  -(∑ p ∈ s, ((min p.1 p.2 : ℕ) / Real.sqrt m : ℝ) ^ (k + 1) *
    cuspDifference n p.1 p.2) / (2 * d)

/-- Equation (31) for the concrete restricted-totient model, with degree k
corresponding to weight k+2. The dimension bound is the explicit input (15). -/
theorem normalizedCusp_bound (k n : ℕ) (d m : ℝ) (hm : 0 < m)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d) (s : Finset (ℕ × ℕ)) :
    |normalizedCusp k n d m s| ≤
      (192 / ((k : ℝ) + 1) / Real.sqrt ((2 : ℝ) ^ n)) *
        ∑ p ∈ s, ((min p.1 p.2 : ℕ) / Real.sqrt m : ℝ) ^ (k + 1) := by
  let W : ℕ × ℕ → ℝ := fun p => ((min p.1 p.2 : ℕ) / Real.sqrt m : ℝ) ^ (k + 1)
  have hW : ∀ p, 0 ≤ W p := by intro p; dsimp [W]; positivity
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hs : |∑ p ∈ s, W p * cuspDifference n p.1 p.2| ≤
      6 * Real.sqrt ((2 : ℝ) ^ n) * ∑ p ∈ s, W p := by
    calc
      _ ≤ ∑ p ∈ s, |W p * cuspDifference n p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ s, W p * (6 * Real.sqrt ((2 : ℝ) ^ n)) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, abs_of_nonneg (hW p)]
        exact mul_le_mul_of_nonneg_left (cuspDifference_bound n p.1 p.2) (hW p)
      _ = _ := by rw [← Finset.sum_mul]; ring
  change |-(∑ p ∈ s, W p * cuspDifference n p.1 p.2) / (2 * d)| ≤ _
  rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * d)]
  calc
    _ ≤ (6 * Real.sqrt ((2 : ℝ) ^ n) * ∑ p ∈ s, W p) / (2 * d) :=
      div_le_div_of_nonneg_right hs (by positivity)
    _ ≤ 32 * (6 * Real.sqrt ((2 : ℝ) ^ n) * ∑ p ∈ s, W p) /
        (((k : ℝ) + 1) * (2 : ℝ) ^ n) :=
      dimension_division_bound k d ((2 : ℝ) ^ n) _ (by positivity) hd (by positivity)
    _ = (192 / ((k : ℝ) + 1)) *
        (Real.sqrt ((2 : ℝ) ^ n) / (2 : ℝ) ^ n) * (∑ p ∈ s, W p) := by
      simp only [div_eq_mul_inv, mul_inv]
      ring
    _ = _ := by rw [sqrt_div_self (by positivity)]; ring

/-- The actual finite polynomial-weighted normalized elliptic expression.
The degree k is weight minus two, so the normalizing power is k+1. -/
noncomputable def normalizedElliptic (k : ℕ) (d m : ℝ) (T : Finset ℤ) (H : ℤ → ℝ) : ℂ :=
  -(∑ t ∈ T, tracePolynomial (t : ℂ) (m : ℂ) k * (H t : ℂ)) /
    ((2 * d * (Real.sqrt m) ^ (k + 1) : ℝ) : ℂ)

/-- Normalize the finite trace-polynomial estimate using the dimension bound.
This helper is subsequently applied to the proved actual content bound. -/
theorem normalizedElliptic_bound_of_uniform (k : ℕ) (d m N B : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hB : 0 ≤ B)
    (hd : ((k : ℝ) + 1) * N / 64 ≤ d) (T : Finset ℤ) (H : ℤ → ℝ)
    (hT : ∀ t ∈ T, (t : ℝ) ^ 2 ≤ 4 * m)
    (hH : ∀ t ∈ T, |H t| ≤ B) :
    ‖normalizedElliptic k d m T H‖ ≤ 32 * B / (N * Real.sqrt m) * (T.card : ℝ) := by
  have hP : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hraw : ‖∑ t ∈ T, tracePolynomial (t : ℂ) (m : ℂ) k * (H t : ℂ)‖ ≤
      (T.card : ℝ) * (((k : ℝ) + 1) * (Real.sqrt m) ^ k * B) := by
    calc
      _ ≤ ∑ t ∈ T, ‖tracePolynomial (t : ℂ) (m : ℂ) k * (H t : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ T, ((k : ℝ) + 1) * (Real.sqrt m) ^ k * B := by
        apply Finset.sum_le_sum
        intro t ht
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (norm_tracePolynomial_le (t : ℝ) m k (hT t ht)) (hH t ht)
          (abs_nonneg _) (by positivity)
      _ = _ := by simp
  unfold normalizedElliptic
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * d * (Real.sqrt m) ^ (k + 1))]
  calc
    _ ≤ ((T.card : ℝ) * (((k : ℝ) + 1) * (Real.sqrt m) ^ k * B)) /
        (2 * d * (Real.sqrt m) ^ (k + 1)) := div_le_div_of_nonneg_right hraw (by positivity)
    _ = (((k : ℝ) + 1) * (B * (T.card : ℝ) / Real.sqrt m)) / (2 * d) := by
      rw [pow_succ]
      field_simp [ne_of_gt hdpos, ne_of_gt hP]
    _ ≤ 32 * (B * (T.card : ℝ) / Real.sqrt m) / N := by
      have hz := dimension_division_bound k d N
        (((k : ℝ) + 1) * (B * (T.card : ℝ) / Real.sqrt m)) hN hd (by positivity)
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      convert hz using 1 <;> field_simp <;> ring
    _ = _ := by ring

/-- The local uniform majorant derived from (28), before polynomial normalization. -/
noncomputable def ellipticLocalMajorant (n : ℕ) (m Ccl δ : ℝ) : ℝ :=
  16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * (4 * m) ^ (1 / 2 + δ) *
    zetaMajorant δ / (1 - decayRatio δ)

/-- The constant in (34), with the convergent p-series defining its zeta value. -/
noncomputable def ellipticConstant (Ccl δ : ℝ) : ℝ :=
  512 * (4 : ℝ) ^ (1 / 2 + δ) * Ccl * zetaMajorant δ / (1 - decayRatio δ)

theorem ellipticLocalMajorant_nonneg (n : ℕ) (m Ccl δ : ℝ)
    (hm : 0 ≤ m) (hC : 0 ≤ Ccl) (hδ : 0 < δ) : 0 ≤ ellipticLocalMajorant n m Ccl δ := by
  have hz := zetaMajorant_nonneg δ
  have hq := decayRatio_lt_one hδ
  unfold ellipticLocalMajorant
  positivity

/-- The discriminant has magnitude at most 4m throughout the actual interior
trace range. This upgrades (28) to a trace-index independent majorant. -/
theorem contentTrace_uniform_bound (n : ℕ) (hn : 3 ≤ n) (m t : ℤ)
    (ht : t ^ 2 < 4 * m) (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → ContentDatum)
    (Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hF : ∀ p ∈ s, IsContentDatum p (t ^ 2 - 4 * m) Ccl δ (F p)) :
    |contentTrace n s F| ≤ ellipticLocalMajorant n (m : ℝ) Ccl δ := by
  have hD : t ^ 2 - 4 * m < 0 := by omega
  have hbound := contentTrace_bound n hn s F (t ^ 2 - 4 * m) hD Ccl δ hC hδ hF
  have htreal : (t : ℝ) ^ 2 < 4 * (m : ℝ) := by exact_mod_cast ht
  have hR : |((t ^ 2 - 4 * m : ℤ) : ℝ)| ≤ 4 * (m : ℝ) := by
    push_cast
    rw [abs_of_neg (by linarith : (t : ℝ) ^ 2 - 4 * (m : ℝ) < 0)]
    nlinarith [sq_nonneg (t : ℝ)]
  have hp := Real.rpow_le_rpow (abs_nonneg _) hR (by linarith : 0 ≤ 1 / 2 + δ)
  have hz := zetaMajorant_nonneg δ
  have hq := decayRatio_lt_one hδ
  have hconst : 0 ≤ 16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) *
      zetaMajorant δ / (1 - decayRatio δ) := by positivity
  calc
    _ ≤ (16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * zetaMajorant δ /
        (1 - decayRatio δ)) * |((t ^ 2 - 4 * m : ℤ) : ℝ)| ^ (1 / 2 + δ) := by
      convert hbound using 1; ring
    _ ≤ (16 * Ccl * (2 : ℝ) ^ ((n : ℝ) / 2) * zetaMajorant δ /
        (1 - decayRatio δ)) * (4 * (m : ℝ)) ^ (1 / 2 + δ) :=
      mul_le_mul_of_nonneg_left hp hconst
    _ = _ := by unfold ellipticLocalMajorant; ring

/-- Exact cancellation of the square-root scales after dimension normalization. -/
theorem elliptic_majorant_normalization (n : ℕ) (m Ccl δ : ℝ)
    (hm : 0 < m) (hδ : 0 < δ) :
    32 * ellipticLocalMajorant n m Ccl δ / ((2 : ℝ) ^ n * Real.sqrt m) =
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * m ^ δ := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hhalf : (2 : ℝ) ^ ((n : ℝ) / 2) = Real.sqrt ((2 : ℝ) ^ n) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul htwo.le n (1 / 2)]
    congr 1
    ring
  have hmhalf : (4 * m) ^ (1 / 2 + δ) =
      (4 : ℝ) ^ (1 / 2 + δ) * Real.sqrt m * m ^ δ := by
    rw [Real.mul_rpow (by norm_num) hm.le, Real.rpow_add hm, ← Real.sqrt_eq_rpow]
    ring
  have hnneg : ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) = 1 / Real.sqrt ((2 : ℝ) ^ n) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow]
    simp only [one_div]
  have hq := decayRatio_lt_one hδ
  have hP : Real.sqrt m ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm)
  unfold ellipticLocalMajorant ellipticConstant
  rw [hhalf, hmhalf, hnneg]
  calc
    _ = (512 * (4 : ℝ) ^ (1 / 2 + δ) * Ccl * zetaMajorant δ / (1 - decayRatio δ)) *
        (Real.sqrt ((2 : ℝ) ^ n) / (2 : ℝ) ^ n) * m ^ δ := by
      field_simp [hP]
      ring
    _ = _ := by rw [sqrt_div_self (by positivity)]

/-- The actual finite polynomial/content model satisfies a uniform bound over
any finite set of interior traces. Its size estimate is derived, not supplied as a hypothesis. -/
theorem normalizedElliptic_actual_bound (k n : ℕ) (hn : 3 ≤ n) (m : ℤ)
    (hm : 0 < m) (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (T : Finset ℤ) (s : ℤ → Finset (ℕ × ℕ)) (F : ℤ → ℕ × ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * m)
    (hF : ∀ t ∈ T, ∀ p ∈ s t,
      IsContentDatum p (t ^ 2 - 4 * m) Ccl δ (F t p)) :
    ‖normalizedElliptic k d (m : ℝ) T (fun t => contentTrace n (s t) (F t))‖ ≤
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) *
        (m : ℝ) ^ δ * (T.card : ℝ) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := normalizedElliptic_bound_of_uniform k d (m : ℝ) ((2 : ℝ) ^ n)
    (ellipticLocalMajorant n (m : ℝ) Ccl δ) hmreal (by positivity)
    (ellipticLocalMajorant_nonneg n (m : ℝ) Ccl δ hmreal.le hC hδ) hd T
    (fun t => contentTrace n (s t) (F t))
    (fun t ht => by exact_mod_cast (hT t ht).le)
    (fun t ht => contentTrace_uniform_bound n hn m t (hT t ht) (s t) (F t)
      Ccl δ hC hδ (hF t ht))
  rwa [elliptic_majorant_normalization n (m : ℝ) Ccl δ hmreal hδ] at hb

/-- Removing zero terms from the actual normalized elliptic sum. -/
theorem normalizedElliptic_filter (k : ℕ) (d m : ℝ) (T : Finset ℤ)
    (H : ℤ → ℝ) (P : ℤ → Prop) [DecidablePred P]
    (hz : ∀ t ∈ T, ¬ P t → H t = 0) :
    normalizedElliptic k d m T H = normalizedElliptic k d m (T.filter P) H := by
  have hs : (∑ t ∈ T, tracePolynomial (t : ℂ) (m : ℂ) k * (H t : ℂ)) =
      ∑ t ∈ T.filter P, tracePolynomial (t : ℂ) (m : ℂ) k * (H t : ℂ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs with h
    · rfl
    · rw [hz t ht h]
      simp
  unfold normalizedElliptic
  rw [hs]

theorem ellipticConstant_nonneg (Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ) :
    0 ≤ ellipticConstant Ccl δ := by
  have hz := zetaMajorant_nonneg δ
  have hq := decayRatio_lt_one hδ
  unfold ellipticConstant
  positivity

/-- Equation (35) with the actual canonical surviving-trace cardinality.
All matrix-root, content, polynomial and normalization estimates are derived
inside the proof chain. The remaining size premise is class-number growth. -/
theorem normalizedElliptic_bound_surviving (k n : ℕ) (hn : 4 ≤ n) (m : ℤ)
    (hm : 0 < m) (d Ccl δ : ℝ) (hC : 0 ≤ Ccl) (hδ : 0 < δ)
    (hd : ((k : ℝ) + 1) * (2 : ℝ) ^ n / 64 ≤ d)
    (T : Finset ℤ) (s : ℤ → Finset (ℕ × ℕ)) (F : ℤ → ℕ × ℕ → ContentDatum)
    (hT : ∀ t ∈ T, t ^ 2 < 4 * m)
    (hF : ∀ t ∈ T, ∀ p ∈ s t,
      IsContentDatum p (t ^ 2 - 4 * m) Ccl δ (F t p)) :
    ‖normalizedElliptic k d (m : ℝ) T (fun t => contentTrace n (s t) (F t))‖ ≤
      ellipticConstant Ccl δ * ((2 : ℝ) ^ n) ^ (-1 / 2 : ℝ) * (m : ℝ) ^ δ *
        ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) := by
  let G := T.filter (fun t => (2 : ℤ) ^ (n - 2) ∣ t ^ 2 - 4 * m)
  have hsub : G ⊆ SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m := by
    intro t ht
    obtain ⟨htT, htD⟩ := Finset.mem_filter.mp ht
    apply (SurvivingTraces.mem_survivingTraces _ _ _).mpr
    refine ⟨hT t htT, ?_⟩
    have hq : 4 * (2 : ℤ) ^ (n - 4) = 2 ^ (n - 2) := by
      rw [show n - 2 = (n - 4) + 2 by omega, pow_add]
      ring
    rw [hq]
    have hneg : (2 : ℤ) ^ (n - 2) ∣ -(t ^ 2 - 4 * m) := dvd_neg.mpr htD
    simpa only [neg_sub] using hneg
  have heq := normalizedElliptic_filter k d (m : ℝ) T
    (fun t => contentTrace n (s t) (F t))
    (fun t => (2 : ℤ) ^ (n - 2) ∣ t ^ 2 - 4 * m)
    (fun t ht hbad => contentTrace_zero n (by omega) (s t) (F t)
      (t ^ 2 - 4 * m) Ccl δ (hF t ht) hbad)
  rw [heq]
  have hb := normalizedElliptic_actual_bound k n (by omega) m hm d Ccl δ hC hδ hd
    G s F (fun t ht => hT t (Finset.mem_filter.mp ht).1)
    (fun t ht => hF t (Finset.mem_filter.mp ht).1)
  apply hb.trans
  have hc : (G.card : ℝ) ≤
      ((SurvivingTraces.survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hK := ellipticConstant_nonneg Ccl δ hC hδ
  exact mul_le_mul_of_nonneg_left hc (by positivity)

end DepthAspect.TraceBounds
