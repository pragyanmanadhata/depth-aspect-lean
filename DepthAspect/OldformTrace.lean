import DepthAspect.CuspReindex
import DepthAspect.SpectralFamily
import Mathlib.LinearAlgebra.Trace

/-!
# Linear trace from the general oldform eigenbasis

The supplied basis is the general oldform basis indexed by M*L=N, a newform
at level M, and a positive divisor of L. Only this cited decomposition and
the cited Hecke eigenvector relation are external inputs. The trace sum,
dyadic multiplicity, and second-difference conclusions are proved here.
-/
namespace DepthAspect.OldformTrace
open scoped BigOperators
open TraceBounds Module

/-- The literal general oldform labels from (10). -/
abbrev OldIndex (F : ℕ → Type*) (N : ℕ) :=
  Σ p : N.divisorsAntidiagonal, F p.1.1 × p.1.2.divisors

/-- The oldform copy has the eigenvalue of its underlying newform. -/
def copyEigenvalue {F : ℕ → Type*} (eig : ∀ M, F M → ℂ) {N : ℕ} (i : OldIndex F N) : ℂ :=
  eig i.1.1.1 i.2.1

/-- Actual linear trace is the sum of eigenvalues for a supplied eigenbasis. -/
theorem trace_of_eigenbasis {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (b : Basis ι ℂ V) (T : V →ₗ[ℂ] V) (eig : ι → ℂ)
    (heigen : ∀ i, T (b i) = eig i • b i) : LinearMap.trace ℂ V T = ∑ i, eig i := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i hi
  change LinearMap.toMatrix b b T i i = eig i
  rw [LinearMap.toMatrix_apply, heigen i]
  simp

/-- Counting the actual divisor copies in the general eigenbasis. -/
theorem old_index_sum (F : ℕ → Type*) [∀ M, Fintype (F M)]
    (N : ℕ) (eig : ∀ M, F M → ℂ) :
    (∑ i : OldIndex F N, copyEigenvalue eig i) =
      ∑ p ∈ N.divisorsAntidiagonal, (p.2.divisors.card : ℂ) * ∑ f : F p.1, eig p.1 f := by
  classical
  unfold OldIndex copyEigenvalue
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  exact Finset.sum_coe_sort N.divisorsAntidiagonal
    (fun p : ℕ × ℕ => (p.2.divisors.card : ℂ) * ∑ f : F p.1, eig p.1 f)

/-- Divisor multiplicity at a prime power, proved from the actual divisor set. -/
theorem two_pow_divisors_card (a : ℕ) : (2 ^ a).divisors.card = a + 1 := by
  have h := Nat.sum_divisors_prime_pow (f := fun _ : ℕ => (1 : ℕ)) (k := a) Nat.prime_two
  simpa using h

/-- Exact oldform multiplicities at dyadic level, as an actual linear trace. -/
theorem full_trace_dyadic (F : ℕ → Type*) [∀ M, Fintype (F M)]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (eig : ∀ M, F M → ℂ) (b : Basis (OldIndex F (2 ^ n)) ℂ V)
    (T : V →ₗ[ℂ] V) (heigen : ∀ i, T (b i) = copyEigenvalue eig i • b i) :
    LinearMap.trace ℂ V T =
      ∑ a ∈ Finset.range (n + 1), ((n - a + 1 : ℕ) : ℂ) * ∑ f : F (2 ^ a), eig (2 ^ a) f := by
  rw [trace_of_eigenbasis b T _ heigen, old_index_sum F (2 ^ n) eig,
    sum_divisorsAntidiagonal_two_pow]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [two_pow_divisors_card]

/-- Complex-valued oldform convolution, with subtraction in the coefficient field. -/
def oldTraceComplex (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ Finset.range (n + 1), ((n + 1 : ℕ) - (a : ℂ)) * f a

theorem oldTraceComplex_eq (f : ℕ → ℂ) (n : ℕ) :
    oldTraceComplex f n =
      ∑ a ∈ Finset.range (n + 1), ((n - a + 1 : ℕ) : ℂ) * f a := by
  apply Finset.sum_congr rfl
  intro a ha
  have han : a ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub han]
  ring

theorem oldTraceComplex_succ (f : ℕ → ℂ) (n : ℕ) :
    oldTraceComplex f (n + 1) = oldTraceComplex f n + ∑ a ∈ Finset.range (n + 2), f a := by
  have hs : (∑ a ∈ Finset.range (n + 1), ((n + 2 : ℕ) - (a : ℂ)) * f a) =
      (∑ a ∈ Finset.range (n + 1), ((n + 1 : ℕ) - (a : ℂ)) * f a) +
        ∑ a ∈ Finset.range (n + 1), f a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    push_cast
    ring
  calc
    oldTraceComplex f (n + 1) =
        (∑ a ∈ Finset.range (n + 1), ((n + 2 : ℕ) - (a : ℂ)) * f a) + f (n + 1) := by
      unfold oldTraceComplex
      rw [Finset.sum_range_succ]
      apply congrArg₂ (fun x y : ℂ => x + y)
      · apply Finset.sum_congr rfl
        intro a ha
        push_cast
        ring
      · push_cast
        ring
    _ = oldTraceComplex f n + ∑ a ∈ Finset.range (n + 2), f a := by
      rw [hs, Finset.sum_range_succ f (n + 1)]
      unfold oldTraceComplex
      ring

theorem oldTraceComplex_second_difference (f : ℕ → ℂ) (n : ℕ) (hn : 2 ≤ n) :
    f n = oldTraceComplex f n - 2 * oldTraceComplex f (n - 1) + oldTraceComplex f (n - 2) := by
  have htwo := oldTraceComplex_succ f (n - 1)
  have hone := oldTraceComplex_succ f (n - 2)
  have hs := Finset.sum_range_succ f n
  rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega] at htwo
  rw [show n - 2 + 1 = n - 1 by omega, show n - 2 + 2 = n by omega] at hone
  rw [htwo, hone, hs]
  ring

/-- Lemma 2.3 for genuine linear traces, derived from the cited general
oldform eigenbases rather than taking the multiplicity identity as an input. -/
theorem new_trace_second_difference
    (F V : ℕ → Type*) [∀ M, Fintype (F M)] [∀ N, AddCommGroup (V N)]
    [∀ N, Module ℂ (V N)] (eig : ∀ M, F M → ℂ)
    (T : ∀ N, V N →ₗ[ℂ] V N)
    (b : ∀ N, 0 < N → Basis (OldIndex F N) ℂ (V N))
    (heigen : ∀ N (hN : 0 < N) i,
      T N (b N hN i) = copyEigenvalue eig i • b N hN i)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ f : F (2 ^ n), eig (2 ^ n) f) =
      LinearMap.trace ℂ (V (2 ^ n)) (T (2 ^ n)) -
      2 * LinearMap.trace ℂ (V (2 ^ (n - 1))) (T (2 ^ (n - 1))) +
      LinearMap.trace ℂ (V (2 ^ (n - 2))) (T (2 ^ (n - 2))) := by
  let f := fun a => ∑ g : F (2 ^ a), eig (2 ^ a) g
  have hfull : ∀ a,
      LinearMap.trace ℂ (V (2 ^ a)) (T (2 ^ a)) = oldTraceComplex f a := by
    intro a
    rw [oldTraceComplex_eq]
    exact full_trace_dyadic F a eig (b (2 ^ a) (by positivity)) (T (2 ^ a))
      (heigen (2 ^ a) (by positivity))
  rw [hfull n, hfull (n - 1), hfull (n - 2)]
  exact oldTraceComplex_second_difference f n hn

/-- The Hecke-compatible version asks for the cited eigenvector relation only
at levels coprime to the odd Hecke index. It does not incorrectly impose an
oldform eigenbasis for the bad-prime Hecke operator. -/
theorem new_trace_second_difference_odd_index
    (F V : ℕ → Type*) [∀ M, Fintype (F M)] [∀ N, AddCommGroup (V N)]
    [∀ N, Module ℂ (V N)] (m : ℕ) (hm : Odd m) (eig : ∀ M, F M → ℂ)
    (T : ∀ N, V N →ₗ[ℂ] V N)
    (b : ∀ N, 0 < N → Basis (OldIndex F N) ℂ (V N))
    (heigen : ∀ N (hN : 0 < N), Nat.Coprime m N → ∀ i,
      T N (b N hN i) = copyEigenvalue eig i • b N hN i)
    (n : ℕ) (hn : 2 ≤ n) :
    (∑ f : F (2 ^ n), eig (2 ^ n) f) =
      LinearMap.trace ℂ (V (2 ^ n)) (T (2 ^ n)) -
      2 * LinearMap.trace ℂ (V (2 ^ (n - 1))) (T (2 ^ (n - 1))) +
      LinearMap.trace ℂ (V (2 ^ (n - 2))) (T (2 ^ (n - 2))) := by
  let f := fun a => ∑ g : F (2 ^ a), eig (2 ^ a) g
  have hfull : ∀ a,
      LinearMap.trace ℂ (V (2 ^ a)) (T (2 ^ a)) = oldTraceComplex f a := by
    intro a
    rw [oldTraceComplex_eq]
    exact full_trace_dyadic F a eig (b (2 ^ a) (by positivity)) (T (2 ^ a))
      (heigen (2 ^ a) (by positivity) (hm.coprime_two_right.pow_right a))
  rw [hfull n, hfull (n - 1), hfull (n - 2)]
  exact oldTraceComplex_second_difference f n hn

/-- Normalized Hecke averages are actual linear traces divided by the
classical eigenvalue normalization and the finite family size. The relation
in `heigen` is the standard normalization, not a trace or average assumption. -/
theorem heckeAverage_eq_normalized_trace {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (b : Basis ι ℂ V) (T : V →ₗ[ℂ] V)
    (a : ι → ℕ → ℂ) (k m : ℕ) (hm : 0 < m)
    (heigen : ∀ f, T (b f) =
      ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ) * a f m) • b f) :
    SpectralFamily.heckeAverage a m = LinearMap.trace ℂ V T /
      ((Fintype.card ι : ℂ) * (((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ)) := by
  have hpR : (m : ℝ) ^ (((k : ℝ) + 1) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
  have hpC : ((((m : ℝ) ^ (((k : ℝ) + 1) / 2) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hpR
  rw [trace_of_eigenbasis b T _ heigen, ← Finset.mul_sum]
  unfold SpectralFamily.heckeAverage SpectralFamily.average
  rw [mul_comm (Fintype.card ι : ℂ)]
  exact (mul_div_mul_left _ _ hpC).symm

end DepthAspect.OldformTrace
