import DepthAspect.OldformTrace
import DepthAspect.SignedSieve

/-!
# Signed Hecke normalization from the cited general trace formula

The external inputs are the simultaneous Hecke/Fricke eigenbasis and the
Skoruppa–Zagier trace identity at arbitrary coprime level and index. The
signed finite-family sum, its normalization, and the dyadic four-level sieve
are proved here. The parameter r gives modular weight 2r+2.
-/
namespace DepthAspect.SignedSieve
open scoped BigOperators
open Module

noncomputable def signedHeckeSum {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (a : ι → ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ f, ε f * a f m

/-- The composition has the product of the two actual eigenvalues. -/
theorem trace_hecke_fricke {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (b : Basis ι ℂ V) (T W : V →ₗ[ℂ] V) (eigenvalue w : ι → ℂ)
    (hT : ∀ f, T (b f) = eigenvalue f • b f)
    (hW : ∀ f, W (b f) = w f • b f) :
    LinearMap.trace ℂ V (T.comp W) = ∑ f, w f * eigenvalue f := by
  apply OldformTrace.trace_of_eigenbasis b (T.comp W)
  intro f
  simp only [LinearMap.comp_apply, hW, map_smul, hT, smul_smul]

/-- Exact spectral normalization (67), derived from the individual cited
Hecke and Fricke eigenvalue normalizations. No signed-trace equality is
assumed as a substitute for the eigenbasis. -/
theorem signedHeckeSum_eq_trace {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V] (r m : ℕ) (hm : 0 < m)
    (b : Basis ι ℂ V) (T W : V →ₗ[ℂ] V) (ε : ι → ℂ) (a : ι → ℕ → ℂ)
    (hT : ∀ f, T (b f) =
      ((((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * a f m) • b f)
    (hW : ∀ f, W (b f) = ((-1 : ℂ) ^ (r + 1) * ε f) • b f) :
    signedHeckeSum ε a m =
      (-1 : ℂ) ^ (r + 1) * LinearMap.trace ℂ V (T.comp W) /
        (((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) := by
  have ht := trace_hecke_fricke b T W _ _ hT hW
  have hp : (((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
  have hs : ((-1 : ℂ) ^ (r + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (r + 1) 2, pow_mul]
    norm_num
  rw [ht]
  unfold signedHeckeSum
  have hsum : (∑ f, ((-1 : ℂ) ^ (r + 1) * ε f) *
      ((((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * a f m)) =
      (-1 : ℂ) ^ (r + 1) * (((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) *
        ∑ f, ε f * a f m := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    ring
  rw [hsum]
  have heq : (-1 : ℂ) ^ (r + 1) *
      ((-1 : ℂ) ^ (r + 1) * (((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) *
        ∑ f, ε f * a f m) =
      (((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * ∑ f, ε f * a f m := by
    calc
      _ = ((-1 : ℂ) ^ (r + 1)) ^ 2 *
          ((((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * ∑ f, ε f * a f m) := by ring
      _ = _ := by rw [hs, one_mul]
  rw [heq, mul_div_cancel_left₀ _ hp]

/-- Named general external formula: arbitrary level and coprime index,
with the full literal elliptic, hyperbolic, and weight-two expression. -/
structure GeneralSignedTraceFormula (r : ℕ) (H : ℤ → ℝ)
    (V : ℕ → Type*) [∀ N, AddCommGroup (V N)] [∀ N, Module ℂ (V N)]
    (T : ∀ N, ℕ → V N →ₗ[ℂ] V N) (W : ∀ N, V N →ₗ[ℂ] V N) : Prop where
  trace_formula : ∀ N m : ℕ, 0 < N → 0 < m → Nat.Coprime m N →
    LinearMap.trace ℂ (V N) ((T N m).comp (W N)) =
      newSignedExpression (2 * r) N m H

/-- The actual signed spectral sum is the proved four-level dyadic sieve
of the general cited expression. This is the precise starting point for
(68), (72), and the subsequent prime-index specializations. -/
theorem signedHeckeSum_dyadic_from_general_formula
    (Family V : ℕ → Type*) [∀ N, Fintype (Family N)]
    [∀ N, AddCommGroup (V N)] [∀ N, Module ℂ (V N)]
    (r n m : ℕ) (hn : 3 ≤ n) (hm : 0 < m) (hodd : Odd m)
    (ε : ∀ N, Family N → ℂ) (a : ∀ N, Family N → ℕ → ℂ)
    (T : ∀ N, ℕ → V N →ₗ[ℂ] V N) (W : ∀ N, V N →ₗ[ℂ] V N)
    (b : ∀ N, 0 < N → Basis (Family N) ℂ (V N)) (H : ℤ → ℝ)
    (hSZ : GeneralSignedTraceFormula r H V T W)
    (hT : ∀ N (hN : 0 < N), Nat.Coprime m N → ∀ f,
      T N m (b N hN f) =
        ((((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) * a N f m) • b N hN f)
    (hW : ∀ N (hN : 0 < N), ∀ f, W N (b N hN f) =
      ((-1 : ℂ) ^ (r + 1) * ε N f) • b N hN f) :
    signedHeckeSum (ε (2 ^ n)) (a (2 ^ n)) m =
      (-1 : ℂ) ^ (r + 1) *
        (∑ j ∈ Finset.range 4, (Dyadic.alpha j : ℂ) *
          fullSignedExpression (2 * r) (2 ^ (n - j)) m H) /
        (((m : ℝ) ^ ((r : ℝ) + 1 / 2) : ℝ) : ℂ) := by
  have hN : 0 < 2 ^ n := by positivity
  have hcop : Nat.Coprime m (2 ^ n) := hodd.coprime_two_right.pow_right n
  rw [signedHeckeSum_eq_trace r m hm (b (2 ^ n) hN) (T (2 ^ n) m) (W (2 ^ n))
    (ε (2 ^ n)) (a (2 ^ n)) (hT (2 ^ n) hN hcop) (hW (2 ^ n) hN),
    hSZ.trace_formula (2 ^ n) m hN hm hcop, newSignedExpression_two_pow (2 * r) n m hn]

end DepthAspect.SignedSieve
