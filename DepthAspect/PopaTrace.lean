import DepthAspect.ClassNumberWeights
import DepthAspect.CuspReindex
import DepthAspect.OldformTrace
import DepthAspect.PopaLocalInterpretation
import DepthAspect.PrimitiveRepresentatives
import DepthAspect.Algebra
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Dyadic specialization of the general primitive-weight trace formula

`generalTraceExpression` is the cited general Popa formula with its scalar
endpoint separated and its strict elliptic part written with primitive class
weights. Its local kernel is an explicit parameter. The interpretation of
that general kernel as the fixed-line count at prime-power level is the
cited external input from Popa (2.17), Lemma 4.1. All dyadic subtraction and
normalization below use the actual checked finite matrix-root model.
-/
namespace DepthAspect.PopaTrace
open scoped BigOperators
open TraceBounds Module

noncomputable def indexPsi (Q : ℕ) : ℝ :=
  Q * ∏ p ∈ Q.primeFactors, (1 + (p : ℝ)⁻¹)

noncomputable def restrictedSigma (Q m : ℕ) : ℝ :=
  ∑ d ∈ m.divisors.filter (fun d => Nat.Coprime d Q), ((m / d : ℕ) : ℝ)

noncomputable def squareIndicator (m : ℕ) : ℝ := if IsSquare m then 1 else 0

@[simp] theorem squareIndicator_prime {p : ℕ} (hp : Nat.Prime p) : squareIndicator p = 0 := by
  simp [squareIndicator, hp.not_isSquare]

@[simp] theorem squareIndicator_square (a : ℕ) : squareIndicator (a ^ 2) = 1 := by
  simp [squareIndicator, IsSquare.sq]

/-- At a square prime index the scalar factor is exactly 1/p. -/
theorem square_inverse_sqrt (p : ℕ) :
    ((p ^ 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ) = (p : ℝ)⁻¹ := by
  push_cast
  rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (p : ℝ))]
  norm_num [Real.rpow_neg_one]

noncomputable def generalElliptic (k Q m : ℕ) (h₀ : ℤ → ℝ)
    (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ) (F : ℤ → ℕ → ContentDatum) : ℂ :=
  -(∑ t ∈ ellipticTraces (m : ℤ), tracePolynomial (t : ℂ) (m : ℂ) k *
    ((∑ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
      h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) * κ Q (F t u).matrix : ℝ) : ℂ)) / 2

noncomputable def generalCusp (k Q m : ℕ) : ℝ :=
  -(∑ p ∈ m.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) *
    (divisorCuspPhi Q p.1 p.2 : ℝ)) / 2

/-- Polynomial degree is k, so the modular-form weight is k+2. -/
noncomputable def generalTraceExpression (k Q m : ℕ) (h₀ : ℤ → ℝ)
    (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ) (F : ℤ → ℕ → ContentDatum) : ℂ :=
  ((((k : ℝ) + 1) / 12 * indexPsi Q * (m : ℝ) ^ ((k : ℝ) / 2) *
      squareIndicator m : ℝ) : ℂ) + generalElliptic k Q m h₀ κ F +
    (generalCusp k Q m : ℂ) + (if k = 0 then (restrictedSigma Q m : ℂ) else 0)

theorem indexPsi_two_pow (h : ℕ) (hh : 0 < h) :
    indexPsi (2 ^ h) = 3 * (2 : ℝ) ^ h / 2 := by
  unfold indexPsi
  rw [Nat.primeFactors_prime_pow (by omega) Nat.prime_two]
  simp only [Finset.prod_singleton, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- For an odd Hecke index the correction term is independent of dyadic depth. -/
theorem restrictedSigma_two_pow (h m : ℕ) (hm : Odd m) :
    restrictedSigma (2 ^ h) m = ∑ d ∈ m.divisors, ((m / d : ℕ) : ℝ) := by
  unfold restrictedSigma
  congr 1
  apply Finset.filter_eq_self.mpr
  intro d hd
  have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
  exact (hm.coprime_two_right.of_dvd_left hdvd).pow_right h

/-- The elementary finite-sum difference, used for the literal content sum. -/
theorem sum_second_difference {ι : Type*} (s : Finset ι) (f g h : ι → ℝ) :
    (∑ i ∈ s, f i) - 2 * (∑ i ∈ s, g i) + (∑ i ∈ s, h i) =
      ∑ i ∈ s, (f i - 2 * g i + h i) := by
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem generalCusp_second_difference (k n m : ℕ) :
    generalCusp k (2 ^ n) m - 2 * generalCusp k (2 ^ (n - 1)) m +
      generalCusp k (2 ^ (n - 2)) m =
      -(∑ p ∈ m.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) *
        cuspDifference n p.1 p.2) / 2 := by
  unfold generalCusp cuspDifference
  simp only [divisorCuspPhi_two_pow]
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [show ∀ x y : ℝ, x * (2 * y) = 2 * (x * y) by intros; ring]
  rw [← Finset.mul_sum]
  ring

/-- The primitive elliptic expression specializes to the exact matrix-root
second difference. The kernel identification is required only at active
primitive weights, so no representative of an inadmissible discriminant is
silently demanded. -/
theorem generalElliptic_second_difference (k n m : ℕ) (hn : 3 ≤ n)
    (h₀ : ℤ → ℝ) (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ)
    (F : ℤ → ℕ → ContentDatum)
    (hlocal : ∀ h : ℕ, 0 < h → ∀ t ∈ ellipticTraces (m : ℤ),
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
      h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) ≠ 0 →
      κ (2 ^ h) (F t u).matrix =
        (DyadicFixedLines.fixedLineCount h (F t u).matrix : ℝ)) :
    generalElliptic k (2 ^ n) m h₀ κ F -
      2 * generalElliptic k (2 ^ (n - 1)) m h₀ κ F +
      generalElliptic k (2 ^ (n - 2)) m h₀ κ F =
      -(∑ t ∈ ellipticTraces (m : ℤ), tracePolynomial (t : ℂ) (m : ℂ) k *
        (literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * (m : ℤ)))
          (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * (m : ℤ)) u (F t u)) : ℂ)) / 2 := by
  have hweight (h : ℕ) (hh : 0 < h) (t : ℤ) (ht : t ∈ ellipticTraces (m : ℤ))
      (u : ℕ) (hu : u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ))) :
      h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) * κ (2 ^ h) (F t u).matrix =
      h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) *
        (DyadicFixedLines.fixedLineCount h (F t u).matrix : ℝ) := by
    by_cases hz : h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [hlocal h hh t ht u hu hz]
  have hinner (t : ℤ) (ht : t ∈ ellipticTraces (m : ℤ)) :
      literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * (m : ℤ)))
          (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * (m : ℤ)) u (F t u)) =
      (∑ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
        h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) * κ (2 ^ n) (F t u).matrix) -
      2 * (∑ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
        h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) * κ (2 ^ (n - 1)) (F t u).matrix) +
      (∑ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
        h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) * κ (2 ^ (n - 2)) (F t u).matrix) := by
    rw [sum_second_difference]
    unfold literalContentTrace
    apply Finset.sum_congr rfl
    intro u hu
    rw [hweight n (by omega) t ht u hu, hweight (n - 1) (by omega) t ht u hu,
      hweight (n - 2) (by omega) t ht u hu]
    simp only [classWeightedDatum, matrixDifference]
    ring
  unfold generalElliptic
  have hs := Finset.sum_congr rfl (fun (t : ℤ) ht => congrArg
    (fun x : ℝ => tracePolynomial (t : ℂ) (m : ℂ) k * (x : ℂ)) (hinner t ht))
  rw [hs]
  push_cast
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [show ∀ x y : ℂ, x * (2 * y) = 2 * (x * y) by intros; ring]
  rw [← Finset.mul_sum]
  ring

/-- The unnormalized dyadic newspace expression, with the complete literal
primitive elliptic sum and the actual divisor-pair cusp sum. -/
noncomputable def newTraceExpression (k n m : ℕ) (h₀ : ℤ → ℝ)
    (F : ℤ → ℕ → ContentDatum) : ℂ :=
  ((((k : ℝ) + 1) * (2 : ℝ) ^ n / 32 * (m : ℝ) ^ ((k : ℝ) / 2) *
      squareIndicator m : ℝ) : ℂ) -
    (∑ t ∈ ellipticTraces (m : ℤ), tracePolynomial (t : ℂ) (m : ℂ) k *
      (literalContentTrace n (positiveSquareContents (t ^ 2 - 4 * (m : ℤ)))
        (fun u => classWeightedDatum h₀ (t ^ 2 - 4 * (m : ℤ)) u (F t u)) : ℂ)) / 2 -
    (((∑ p ∈ m.divisorsAntidiagonal, ((min p.1 p.2 : ℕ) : ℝ) ^ (k + 1) *
      cuspDifference n p.1 p.2) / 2 : ℝ) : ℂ)

/-- Actual ψ-values give the scalar coefficient of (14). -/
theorem scalar_second_difference (k n m : ℕ) (hn : 3 ≤ n) :
    ((k : ℝ) + 1) / 12 * indexPsi (2 ^ n) * (m : ℝ) ^ ((k : ℝ) / 2) * squareIndicator m -
    2 * (((k : ℝ) + 1) / 12 * indexPsi (2 ^ (n - 1)) *
      (m : ℝ) ^ ((k : ℝ) / 2) * squareIndicator m) +
    ((k : ℝ) + 1) / 12 * indexPsi (2 ^ (n - 2)) * (m : ℝ) ^ ((k : ℝ) / 2) * squareIndicator m =
    ((k : ℝ) + 1) * (2 : ℝ) ^ n / 32 * (m : ℝ) ^ ((k : ℝ) / 2) * squareIndicator m := by
  rw [indexPsi_two_pow n (by omega), indexPsi_two_pow (n - 1) (by omega),
    indexPsi_two_pow (n - 2) (by omega)]
  have hp : (2 : ℝ) ^ n = 4 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega, pow_add]
    ring
  have hq : (2 : ℝ) ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega, pow_add]
    ring
  rw [hp, hq]
  ring

/-- Proposition 2.4 as an identity of the literal general trace expressions.
It proves the specialization, including the weight-two cancellation, rather
than assuming the newspace trace expression as a premise. -/
theorem generalTrace_second_difference (k n m : ℕ) (hn : 3 ≤ n) (hm : Odd m)
    (h₀ : ℤ → ℝ) (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ)
    (F : ℤ → ℕ → ContentDatum)
    (hlocal : ∀ h : ℕ, 0 < h → ∀ t ∈ ellipticTraces (m : ℤ),
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
      h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) ≠ 0 →
      κ (2 ^ h) (F t u).matrix =
        (DyadicFixedLines.fixedLineCount h (F t u).matrix : ℝ)) :
    generalTraceExpression k (2 ^ n) m h₀ κ F -
      2 * generalTraceExpression k (2 ^ (n - 1)) m h₀ κ F +
      generalTraceExpression k (2 ^ (n - 2)) m h₀ κ F =
      newTraceExpression k n m h₀ F := by
  have hE := generalElliptic_second_difference k n m hn h₀ κ F hlocal
  have hC := congrArg (fun x : ℝ => (x : ℂ)) (generalCusp_second_difference k n m)
  have hI := congrArg (fun x : ℝ => (x : ℂ)) (scalar_second_difference k n m hn)
  push_cast at hC hI
  unfold generalTraceExpression newTraceExpression
  rw [restrictedSigma_two_pow n m hm, restrictedSigma_two_pow (n - 1) m hm,
    restrictedSigma_two_pow (n - 2) m hm]
  push_cast
  linear_combination hE + hC + hI

/-- A reusable derived local identity for the actual selected representatives.
Its only semantic premise is the named general Popa interpretation. -/
theorem selectedRepresentative_local_interpretation
    (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ)
    (hκ : PopaLocalInterpretation.GeneralPopaLocalFormula κ)
    (m : ℤ) (hm : 0 < m) (hodd : Odd m)
    (h : ℕ) (hh : 0 < h) (t : ℤ) (ht : t ∈ ellipticTraces m)
    (u : ℕ) (hu : u ∈ positiveSquareContents (t ^ 2 - 4 * m))
    (hw : h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) ≠ 0) :
    κ (2 ^ h) (selectedRepresentative h₀ hforms m t u).matrix =
      (DyadicFixedLines.fixedLineCount h (selectedRepresentative h₀ hforms m t u).matrix : ℝ) := by
  have ht' := (mem_ellipticTraces m t).mp ht
  obtain ⟨htr, hdet⟩ := selectedRepresentative_trace_det h₀ hforms m t ht' u hu hw
  apply hκ.dyadic h hh _
  · rwa [hdet]
  · rwa [hdet]
  · rwa [htr, hdet]

/-- Applying the cited general full-space formula to genuine linear traces
and the cited general oldform eigenbasis proves the newform eigenvalue sum.
The only trace formula input is at general positive, coprime level. -/
theorem newform_sum_from_general_trace
    (Family V : ℕ → Type*) [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)]
    [∀ Q, Module ℂ (V Q)] (k n m : ℕ) (hn : 3 ≤ n) (hm : Odd m)
    (eig : ∀ M, Family M → ℂ) (T : ∀ Q, V Q →ₗ[ℂ] V Q)
    (b : ∀ Q, 0 < Q → Basis (OldformTrace.OldIndex Family Q) ℂ (V Q))
    (heigen : ∀ Q (hQ : 0 < Q), Nat.Coprime m Q → ∀ i,
      T Q (b Q hQ i) = OldformTrace.copyEigenvalue eig i • b Q hQ i)
    (h₀ : ℤ → ℝ) (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ)
    (F : ℤ → ℕ → ContentDatum)
    (htrace : ∀ Q : ℕ, 0 < Q → Nat.Coprime m Q →
      LinearMap.trace ℂ (V Q) (T Q) = generalTraceExpression k Q m h₀ κ F)
    (hlocal : ∀ h : ℕ, 0 < h → ∀ t ∈ ellipticTraces (m : ℤ),
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
      h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) ≠ 0 →
      κ (2 ^ h) (F t u).matrix =
        (DyadicFixedLines.fixedLineCount h (F t u).matrix : ℝ)) :
    (∑ f : Family (2 ^ n), eig (2 ^ n) f) = newTraceExpression k n m h₀ F := by
  rw [OldformTrace.new_trace_second_difference_odd_index Family V m hm eig T b heigen n (by omega)]
  rw [htrace (2 ^ n) (by positivity) (hm.coprime_two_right.pow_right n),
    htrace (2 ^ (n - 1)) (by positivity) (hm.coprime_two_right.pow_right (n - 1)),
    htrace (2 ^ (n - 2)) (by positivity) (hm.coprime_two_right.pow_right (n - 2))]
  exact generalTrace_second_difference k n m hn hm h₀ κ F hlocal

/-- Exact normalization of the derived newspace expression, equation (16). -/
theorem newTraceExpression_normalized (k n m : ℕ) (hm : 0 < m) (d : ℝ)
    (h₀ : ℤ → ℝ) (F : ℤ → ℕ → ContentDatum) :
    newTraceExpression k n m h₀ F /
        ((d * (m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * d) *
        (m : ℝ) ^ (-1 / 2 : ℝ) * squareIndicator m : ℝ) : ℂ) +
      literalElliptic k n d (m : ℤ) h₀ F +
      (normalizedCusp k n d (m : ℝ) m.divisorsAntidiagonal : ℂ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs := DepthAspect.scalar_trace_normalization ((k : ℝ) + 2) ((2 : ℝ) ^ n)
    d (m : ℝ) (squareIndicator m) hmR
  have he1 : (k : ℝ) + 2 - 1 = (k : ℝ) + 1 := by ring
  have he2 : ((k : ℝ) + 2) / 2 - 1 = (k : ℝ) / 2 := by ring
  rw [he1, he2] at hs
  have hsC := congrArg (fun x : ℝ => (x : ℂ)) hs
  unfold newTraceExpression literalElliptic
  simp only [Int.cast_natCast]
  rw [normalizedElliptic_eq_original_power k d (m : ℝ) hmR.le,
    normalizedCusp_eq_original_power k n d (m : ℝ) hmR.le]
  simp only [originalCuspDifference_eq]
  push_cast at hsC ⊢
  simp only [div_eq_mul_inv, mul_inv, neg_mul, neg_add_rev] at hsC ⊢
  linear_combination hsC

/-- The finite Hecke average of the actual newform labels is the derived
scalar term plus the actual literal elliptic and cusp terms. -/
theorem heckeAverage_from_newform_sum {ι : Type*} [Fintype ι]
    (a : ι → ℕ → ℂ) (k n m : ℕ) (hm : 0 < m)
    (h₀ : ℤ → ℝ) (F : ℤ → ℕ → ContentDatum)
    (htrace : (∑ f : ι, ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * a f m)) =
      newTraceExpression k n m h₀ F) :
    SpectralFamily.heckeAverage a m =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card ι : ℝ)) *
        (m : ℝ) ^ (-1 / 2 : ℝ) * squareIndicator m : ℝ) : ℂ) +
      literalElliptic k n (Fintype.card ι : ℝ) (m : ℤ) h₀ F +
      (normalizedCusp k n (Fintype.card ι : ℝ) (m : ℝ) m.divisorsAntidiagonal : ℂ) := by
  rw [← newTraceExpression_normalized k n m hm (Fintype.card ι : ℝ) h₀ F, ← htrace,
    ← Finset.mul_sum]
  unfold SpectralFamily.heckeAverage SpectralFamily.average
  have hpR : (m : ℝ) ^ (((k : ℝ) + 1) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
  have hpC : ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hpR
  push_cast
  rw [mul_comm (Fintype.card ι : ℂ)]
  exact (mul_div_mul_left _ _ hpC).symm

/-- A single interface from the general cited oldform basis, classical Hecke
normalization, general full-space trace identity, and general local-kernel
interpretation to the actual finite newform Hecke average. Every dyadic
specialization and normalization in the conclusion has been proved above. -/
theorem heckeAverage_from_general_inputs
    (Family V : ℕ → Type*) [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)]
    [∀ Q, Module ℂ (V Q)] (k n m : ℕ) (hn : 3 ≤ n) (hm : Odd m) (hmpos : 0 < m)
    (a : ∀ M, Family M → ℕ → ℂ) (T : ∀ Q, V Q →ₗ[ℂ] V Q)
    (b : ∀ Q, 0 < Q → Basis (OldformTrace.OldIndex Family Q) ℂ (V Q))
    (heigen : ∀ Q (hQ : 0 < Q), Nat.Coprime m Q → ∀ i,
      T Q (b Q hQ i) = OldformTrace.copyEigenvalue
        (fun M f => ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * a M f m)) i • b Q hQ i)
    (h₀ : ℤ → ℝ) (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ)
    (F : ℤ → ℕ → ContentDatum)
    (htrace : ∀ Q : ℕ, 0 < Q → Nat.Coprime m Q →
      LinearMap.trace ℂ (V Q) (T Q) = generalTraceExpression k Q m h₀ κ F)
    (hκ : PopaLocalInterpretation.GeneralPopaLocalFormula κ)
    (hmatrix : ∀ t ∈ ellipticTraces (m : ℤ),
      ∀ u ∈ positiveSquareContents (t ^ 2 - 4 * (m : ℤ)),
      h₀ ((t ^ 2 - 4 * (m : ℤ)) / (u : ℤ) ^ 2) ≠ 0 →
      Matrix.trace (F t u).matrix = t ∧ Matrix.det (F t u).matrix = (m : ℤ)) :
    SpectralFamily.heckeAverage (a (2 ^ n)) m =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card (Family (2 ^ n)) : ℝ)) *
        (m : ℝ) ^ (-1 / 2 : ℝ) * squareIndicator m : ℝ) : ℂ) +
      literalElliptic k n (Fintype.card (Family (2 ^ n)) : ℝ) (m : ℤ) h₀ F +
      (normalizedCusp k n (Fintype.card (Family (2 ^ n)) : ℝ)
        (m : ℝ) m.divisorsAntidiagonal : ℂ) := by
  apply heckeAverage_from_newform_sum (a (2 ^ n)) k n m hmpos h₀ F
  exact newform_sum_from_general_trace Family V k n m hn hm
    (fun M f => ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * a M f m))
    T b heigen h₀ κ F htrace (by
      intro h hh t ht u hu hw
      obtain ⟨htr, hdet⟩ := hmatrix t ht u hu hw
      apply hκ.dyadic h hh (F t u).matrix
      · rw [hdet]
        exact_mod_cast hm
      · rw [hdet]
        exact_mod_cast hmpos
      · rw [htr, hdet]
        exact (mem_ellipticTraces (m : ℤ) t).mp ht)

/-- The final canonical average decomposition consumes only the cited general
trace/local identities and actual primitive-class data. Matrix conditions,
coprimality at dyadic level, and the local fixed-line specialization are all
proved; no independent dyadic local identity remains as an assumption. -/
theorem heckeAverage_canonical_from_general_inputs
    (Family V : ℕ → Type*) [∀ M, Fintype (Family M)] [∀ Q, AddCommGroup (V Q)]
    [∀ Q, Module ℂ (V Q)] (k n m : ℕ) (hn : 3 ≤ n) (hm : Odd m) (hmpos : 0 < m)
    (a : ∀ M, Family M → ℕ → ℂ) (T : ∀ Q, V Q →ₗ[ℂ] V Q)
    (b : ∀ Q, 0 < Q → Basis (OldformTrace.OldIndex Family Q) ℂ (V Q))
    (heigen : ∀ Q (hQ : 0 < Q), Nat.Coprime m Q → ∀ i,
      T Q (b Q hQ i) = OldformTrace.copyEigenvalue
        (fun M f => ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * a M f m)) i • b Q hQ i)
    (h₀ : ℤ → ℝ)
    (hforms : ∀ D : ℤ, D < 0 → h₀ D ≠ 0 → Nonempty (PrimitiveForm D))
    (κ : ℕ → Matrix (Fin 2) (Fin 2) ℤ → ℝ)
    (hκ : PopaLocalInterpretation.GeneralPopaLocalFormula κ)
    (htrace : ∀ Q : ℕ, 0 < Q → Nat.Coprime m Q →
      LinearMap.trace ℂ (V Q) (T Q) = generalTraceExpression k Q m h₀ κ
        (selectedRepresentative h₀ hforms (m : ℤ))) :
    SpectralFamily.heckeAverage (a (2 ^ n)) m =
      ((((k : ℝ) + 1) * (2 : ℝ) ^ n / (32 * (Fintype.card (Family (2 ^ n)) : ℝ)) *
        (m : ℝ) ^ (-1 / 2 : ℝ) * squareIndicator m : ℝ) : ℂ) +
      literalElliptic k n (Fintype.card (Family (2 ^ n)) : ℝ) (m : ℤ) h₀
        (selectedRepresentative h₀ hforms (m : ℤ)) +
      (normalizedCusp k n (Fintype.card (Family (2 ^ n)) : ℝ)
        (m : ℝ) m.divisorsAntidiagonal : ℂ) := by
  apply heckeAverage_from_general_inputs Family V k n m hn hm hmpos a T b heigen
    h₀ κ (selectedRepresentative h₀ hforms (m : ℤ)) htrace hκ
  intro t ht u hu hw
  exact selectedRepresentative_trace_det h₀ hforms (m : ℤ) t
    ((mem_ellipticTraces (m : ℤ) t).mp ht) u hu hw

end DepthAspect.PopaTrace
