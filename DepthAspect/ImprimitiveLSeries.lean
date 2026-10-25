import DepthAspect.ImprimitiveEuler
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.FunProp

/-!
# The global imprimitive Euler-factor identity

The initial half-plane identity is derived from the actual multiplicative
sequence, its proven local sums, absolute convergence, and finite-prime-product
limits. The analytic continuation is then characterized by its defining
agreement with that series. No size bound or Euler-factor identity is a premise.
-/

open Filter
open scoped BigOperators Topology
namespace DepthAspect.ImprimitiveLSeries

open ImprimitiveCharacter ImprimitiveEuler

noncomputable def correction {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f p : ℕ) (s : ℂ) : ℂ :=
  1 + (1 - χ (p : ZMod q)) *
    ∑ j ∈ Finset.range (f.factorization p), ((p : ℂ) ^ (-s)) ^ (j + 1)

noncomputable def correctionProduct {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) (s : ℂ) : ℂ := ∏ p ∈ f.primeFactors, correction χ f p s

theorem correction_eq_one_of_not_dvd {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f p : ℕ) (hpf : ¬ p ∣ f) (s : ℂ) : correction χ f p s = 1 := by
  simp [correction, Nat.factorization_eq_zero_of_not_dvd hpf]

theorem psi_LSeries_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (psiNat χ f) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => psiNat_norm_le_one χ f n) hs

private theorem term_eq_weighted {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (psiNat χ f) s n = psiNat χ f n * riemannZetaSummandHom hs n := by
  simp only [LSeries.term_of_ne_zero' hs, riemannZetaSummandHom,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Complex.cpow_neg, div_eq_mul_inv]

theorem weighted_psi_multiplicative {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) {s : ℂ} (hs : s ≠ 0) {m n : ℕ} (hmn : Nat.Coprime m n) :
    LSeries.term (psiNat χ f) s (m * n) =
      LSeries.term (psiNat χ f) s m * LSeries.term (psiNat χ f) s n := by
  simp only [term_eq_weighted χ f hs, psiNat_mul_of_coprime χ f m n hmn, map_mul]
  ring

theorem local_twist_norm_lt_one {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) {s : ℂ} (hs : 1 < s.re) :
    ‖χ (p : ZMod q) * (p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_right (χ.norm_le_one (p : ZMod q))
    (norm_nonneg ((p : ℂ) ^ (-s)))
  have hpw := Complex.norm_prime_cpow_le_one_half ⟨p, hp⟩ hs
  simp only [one_mul] at h
  linarith

theorem local_weighted_psi_tsum {q p f : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (hf : f ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    (∑' b : ℕ, LSeries.term (psiNat χ f) s (p ^ b)) =
      correction χ f p s * (1 - χ (p : ZMod q) * (p : ℂ) ^ (-s))⁻¹ := by
  have hlocal := psiNat_localFactor_hasSum χ hp hf ((p : ℂ) ^ (-s))
    (local_twist_norm_lt_one χ hp hs)
  have hterm : (fun b : ℕ => LSeries.term (psiNat χ f) s (p ^ b)) =
      (fun b : ℕ => psiNat χ f (p ^ b) * ((p : ℂ) ^ (-s)) ^ b) := by
    funext b
    rw [term_eq_weighted χ f (Complex.ne_zero_of_one_lt_re hs), map_pow]
    rfl
  rw [hterm]
  simpa only [correction, div_eq_mul_inv] using hlocal.tsum_eq

/-- The correction factor stabilizes once the finite product includes every
prime dividing the conductor. -/
theorem correction_partial_product {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) (hf : f ≠ 0) (s : ℂ) {n : ℕ} (hn : f < n) :
    (∏ p ∈ n.primesBelow, correction χ f p s) = correctionProduct χ f s := by
  classical
  unfold correctionProduct
  symm
  apply Finset.prod_subset
  · intro p hp
    obtain ⟨hpp, hpf, _⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesBelow.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hf) hpf).trans_lt hn, hpp⟩
  · intro p hp hnot
    apply correction_eq_one_of_not_dvd
    intro hpf
    exact hnot (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesBelow.mp hp).2, hpf, hf⟩)

/-- Equation (7) on its initial absolutely convergent half-plane, for the
actual imprimitive coefficients. This is proved by Euler products. -/
theorem LSeries_eq_product {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ℕ) (hf : f ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (psiNat χ f) s = LSeries (fun n : ℕ => χ (n : ZMod q)) s *
      correctionProduct χ f s := by
  have hs0 := Complex.ne_zero_of_one_lt_re hs
  have hone : LSeries.term (psiNat χ f) s 1 = 1 := by simp
  have hmul := fun {m n : ℕ} (hmn : Nat.Coprime m n) =>
    weighted_psi_multiplicative χ f hs0 hmn
  have hE := EulerProduct.eulerProduct hone hmul
    (psi_LSeries_summable χ f hs).norm (LSeries.term_zero _ _)
  have hχ := (χ.LSeries_eulerProduct hs).mul_const (correctionProduct χ f s)
  have hevent : (fun n : ℕ => ∏ p ∈ n.primesBelow,
      ∑' b : ℕ, LSeries.term (psiNat χ f) s (p ^ b)) =ᶠ[atTop]
      (fun n : ℕ => (∏ p ∈ n.primesBelow,
        (1 - χ (p : ZMod q) * (p : ℂ) ^ (-s))⁻¹) * correctionProduct χ f s) := by
    filter_upwards [eventually_gt_atTop f] with n hn
    calc
      _ = ∏ p ∈ n.primesBelow, correction χ f p s *
          (1 - χ (p : ZMod q) * (p : ℂ) ^ (-s))⁻¹ := by
        apply Finset.prod_congr rfl
        intro p hp
        exact local_weighted_psi_tsum χ (Nat.mem_primesBelow.mp hp).2 hf hs
      _ = (∏ p ∈ n.primesBelow, correction χ f p s) *
          ∏ p ∈ n.primesBelow, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-s))⁻¹ :=
        Finset.prod_mul_distrib
      _ = _ := by rw [correction_partial_product χ f hf s hn]; ring
  exact tendsto_nhds_unique hE (hχ.congr' hevent.symm)


/-- Odd characters are nonprincipal, including small-modulus edge cases. -/
theorem odd_character_ne_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) :
    χ ≠ 1 := by
  intro h
  have he : χ (-1) = 1 := by
    rw [h]
    exact MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod q))
  have ho : χ (-1) = -1 := hχ
  have : (1 : ℂ) = -1 := he.symm.trans ho
  norm_num at this

noncomputable def continuationCandidate {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (f : ℕ) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ s * correctionProduct χ f s

/-- The finite Euler-correction expression is an entire continuation of the
actual ψ series. Its existence is proved, not assumed. -/
theorem continuationCandidate_differentiable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (f : ℕ) :
    Differentiable ℂ (continuationCandidate χ f) := by
  apply (DirichletCharacter.differentiable_LFunction (odd_character_ne_one χ hχ)).mul
  intro s
  unfold correctionProduct
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  letI : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  unfold correction
  fun_prop

theorem continuationCandidate_agrees {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (f : ℕ) (hf : f ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    continuationCandidate χ f s = LSeries (psiNat χ f) s := by
  unfold continuationCandidate
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact (LSeries_eq_product χ f hf hs).symm

/-- Equation (7) by analytic continuation. The hypotheses characterize a
continuation by analyticity and agreement with the actual defining series on
its convergence half-plane; they contain no Euler-factor conclusion. -/
theorem continuation_eq_product {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (f : ℕ) (hf : f ≠ 0)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hseries : ∀ s : ℂ, 1 < s.re → G s = LSeries (psiNat χ f) s) :
    G = continuationCandidate χ f := by
  apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (continuationCandidate_differentiable χ hχ f))
  filter_upwards [show ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re from
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)] with s hs
  rw [hseries s hs, continuationCandidate_agrees χ f hf hs]

/-- Existence and uniqueness of the entire continuation of the actual
imprimitive series, without invoking an unordered sum at the boundary. -/
theorem entire_continuation_exists_unique {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) (f : ℕ) (hf : f ≠ 0) :
    ∃! G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, 1 < s.re → G s = LSeries (psiNat χ f) s := by
  refine ⟨continuationCandidate χ f,
    ⟨continuationCandidate_differentiable χ hχ f, fun s hs =>
      continuationCandidate_agrees χ f hf hs⟩, ?_⟩
  intro G hG
  exact continuation_eq_product χ hχ f hf G hG.1 hG.2

end DepthAspect.ImprimitiveLSeries
