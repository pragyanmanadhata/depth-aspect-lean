import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Exact algebra used by the depth-aspect paper

This file proves algebraic consequences of explicitly supplied trace or sign data.
It does not assert the modular-form trace formula, an explicit formula, or any
analytic estimate. In particular no analytic conclusion of the paper is made
an axiom here.
-/

open scoped BigOperators

namespace DepthAspect

/-- The oldform trace sum in Lemma 2.3. Subtraction is in `ℝ`; on this
summation range it agrees with the natural-number multiplicity. -/
def oldTrace (newTrace : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (n + 1), ((n + 1 : ℕ) - (a : ℝ)) * newTrace a

/-- The displayed definition has exactly the multiplicities from (11). -/
theorem oldTrace_eq_multiplicity_sum (f : ℕ → ℝ) (n : ℕ) :
    oldTrace f n = ∑ a ∈ Finset.range (n + 1), ((n - a + 1 : ℕ) : ℝ) * f a := by
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub ha']
  ring

/-- A single difference removes one copy of each lower-level contribution. -/
theorem oldTrace_succ (f : ℕ → ℝ) (n : ℕ) :
    oldTrace f (n + 1) = oldTrace f n + ∑ a ∈ Finset.range (n + 2), f a := by
  have h : (∑ a ∈ Finset.range (n + 1), ((n + 2 : ℕ) - (a : ℝ)) * f a) =
      (∑ a ∈ Finset.range (n + 1), ((n + 1 : ℕ) - (a : ℝ)) * f a) +
      ∑ a ∈ Finset.range (n + 1), f a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    push_cast
    ring
  calc
    oldTrace f (n + 1) =
        (∑ a ∈ Finset.range (n + 1), ((n + 2 : ℕ) - (a : ℝ)) * f a) +
          f (n + 1) := by
      unfold oldTrace
      rw [Finset.sum_range_succ]
      push_cast
      ring_nf
    _ = oldTrace f n + ∑ a ∈ Finset.range (n + 2), f a := by
      rw [h, Finset.sum_range_succ f (n + 1)]
      unfold oldTrace
      ring

/-- Lemma 2.3, with indices shifted to avoid truncated natural subtraction. -/
theorem oldTrace_second_difference (f : ℕ → ℝ) (n : ℕ) :
    oldTrace f (n + 2) - 2 * oldTrace f (n + 1) + oldTrace f n = f (n + 2) := by
  have h2 := oldTrace_succ f (n + 1)
  have h1 := oldTrace_succ f n
  have hs := Finset.sum_range_succ f (n + 2)
  rw [h2, h1, hs]
  ring

/-- The unshifted second-difference identity exactly as in (11). -/
theorem oldTrace_second_difference_of_two_le (f : ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    f n = oldTrace f n - 2 * oldTrace f (n - 1) + oldTrace f (n - 2) := by
  have h := oldTrace_second_difference f (n - 2)
  have h1 : n - 2 + 2 = n := by omega
  have h2 : n - 2 + 1 = n - 1 := by omega
  rw [h1, h2] at h
  exact h.symm

/-- Applying oldform inversion to an externally supplied oldform decomposition. -/
theorem newTrace_of_oldform_decomposition (full newTrace : ℕ → ℝ)
    (hdecomp : ∀ n, full n = oldTrace newTrace n) (n : ℕ) (hn : 2 ≤ n) :
    newTrace n = full n - 2 * full (n - 1) + full (n - 2) := by
  simp only [hdecomp]
  exact oldTrace_second_difference_of_two_le newTrace n hn

/-- The constant weight-two term cancels in a second difference. -/
theorem constant_second_difference (c : ℝ) : c - 2 * c + c = 0 := by ring

/-- Scalar coefficient in Proposition 2.4. The three levels have
`ψ(N)=3N/2`, `ψ(N/2)=3N/4`, `ψ(N/4)=3N/8`. -/
theorem scalar_second_difference (k N : ℝ) :
    (k - 1) / 12 * (3 * N / 2) - 2 * ((k - 1) / 12 * (3 * N / 4)) +
      (k - 1) / 12 * (3 * N / 8) = (k - 1) * N / 32 := by
  ring

/-- The real-power exponent cancellation in (16). -/
theorem scalar_power_normalization (k m : ℝ) (hm : 0 < m) :
    m ^ (k / 2 - 1) / m ^ ((k - 1) / 2) = m ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_sub hm]
  congr 1
  ring

/-- The scalar term of (14), divided by `d m^((k-1)/2)`, is the
scalar term of (16). The indicator `q` can be `0` or `1`, but the algebra
holds for any value. -/
theorem scalar_trace_normalization (k N d m q : ℝ) (hm : 0 < m) :
    (q * ((k - 1) * N / 32) * m ^ (k / 2 - 1)) /
        (d * m ^ ((k - 1) / 2)) =
      ((k - 1) * N / (32 * d)) * m ^ (-(1 / 2 : ℝ)) * q := by
  rw [show q * ((k - 1) * N / 32) * m ^ (k / 2 - 1) =
      (((k - 1) * N / 32) * q) * m ^ (k / 2 - 1) by ring]
  rw [mul_div_mul_comm, scalar_power_normalization k m hm]
  ring

/-- Normalization distributes over all three terms of (14). -/
theorem normalized_trace_decomposition (k N d m q E C T : ℝ) (hm : 0 < m)
    (htrace : T = q * ((k - 1) * N / 32) * m ^ (k / 2 - 1) + E + C) :
    T / (d * m ^ ((k - 1) / 2)) =
      ((k - 1) * N / (32 * d)) * m ^ (-(1 / 2 : ℝ)) * q +
      E / (d * m ^ ((k - 1) / 2)) + C / (d * m ^ ((k - 1) / 2)) := by
  rw [htrace, add_div, add_div, scalar_trace_normalization k N d m q hm]

section RootNumberProjection

variable {ι : Type*}

/-- The sign indicator `(1 + σ ε)/2`, summed over an arbitrary finite
family, gives the numerator of (119). -/
theorem twice_sign_sum (s : Finset ι) (ε X : ι → ℝ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1) :
    2 * (∑ i ∈ s.filter (fun i => ε i = σ), X i) =
      (∑ i ∈ s, X i) + σ * (∑ i ∈ s, ε i * X i) := by
  classical
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hσ with hσ | hσ <;> rcases hε i hi with hiε | hiε <;>
    norm_num [hσ, hiε] <;> ring

/-- The same indicator gives the exact size of each sign family. -/
theorem twice_sign_card (s : Finset ι) (ε : ι → ℝ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1) :
    2 * ((s.filter (fun i => ε i = σ)).card : ℝ) =
      (s.card : ℝ) + σ * (∑ i ∈ s, ε i) := by
  simpa using twice_sign_sum s ε (fun _ => 1) σ hσ hε

/-- Division step in the sign projection. Nonzero family sizes are
explicit hypotheses; division by an empty family is not justified. -/
theorem projection_quotient (a b u v d r σ : ℝ) (hd : d ≠ 0) (hb : b ≠ 0)
    (ha : 2 * a = u + σ * v) (hcount : 2 * b = d + σ * r) :
    a / b = (u / d + σ * (v / d)) / (1 + σ * (r / d)) := by
  have hden : d + σ * r ≠ 0 := by rw [← hcount]; exact mul_ne_zero (by norm_num) hb
  have heq : (u / d + σ * (v / d)) / (1 + σ * (r / d)) =
      (u + σ * v) / (d + σ * r) := by
    field_simp
  rw [heq, ← ha, ← hcount]
  field_simp

/-- Formula (119) for any finite family with root numbers in `{1,-1}`. -/
theorem sign_family_average (s : Finset ι) (ε X : ι → ℝ) (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1) (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1)
    (hs : s.Nonempty) (hsign : (s.filter (fun i => ε i = σ)).Nonempty) :
    (∑ i ∈ s.filter (fun i => ε i = σ), X i) /
        ((s.filter (fun i => ε i = σ)).card : ℝ) =
      ((∑ i ∈ s, X i) / (s.card : ℝ) +
        σ * ((∑ i ∈ s, ε i * X i) / (s.card : ℝ))) /
      (1 + σ * ((∑ i ∈ s, ε i) / (s.card : ℝ))) := by
  classical
  apply projection_quotient
  · exact_mod_cast ne_of_gt (Finset.card_pos.mpr hs)
  · exact_mod_cast ne_of_gt (Finset.card_pos.mpr hsign)
  · exact twice_sign_sum s ε X σ hσ hε
  · exact twice_sign_card s ε σ hσ hε

end RootNumberProjection

/-- Complex-valued version of the root-number numerator identity. This does
not require zero sums or test functions to be real-valued. -/
theorem twice_complex_sign_sum {ι : Type*} (s : Finset ι) (ε X : ι → ℂ) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1) (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1) :
    2 * (∑ i ∈ s.filter (fun i => ε i = σ), X i) =
      (∑ i ∈ s, X i) + σ * (∑ i ∈ s, ε i * X i) := by
  classical
  rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hσ with hσ | hσ <;> rcases hε i hi with hiε | hiε <;>
    norm_num [hσ, hiε] <;> ring

/-- Exact sign-class cardinality, with its value embedded in `ℂ`. -/
theorem twice_complex_sign_card {ι : Type*} (s : Finset ι) (ε : ι → ℂ) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1) (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1) :
    2 * ((s.filter (fun i => ε i = σ)).card : ℂ) =
      (s.card : ℂ) + σ * (∑ i ∈ s, ε i) := by
  simpa using twice_complex_sign_sum s ε (fun _ => 1) σ hσ hε

/-- The projection division identity over `ℂ`. -/
theorem complex_projection_quotient (a b u v d r σ : ℂ) (hd : d ≠ 0) (hb : b ≠ 0)
    (ha : 2 * a = u + σ * v) (hcount : 2 * b = d + σ * r) :
    a / b = (u / d + σ * (v / d)) / (1 + σ * (r / d)) := by
  have hden : d + σ * r ≠ 0 := by rw [← hcount]; exact mul_ne_zero (by norm_num) hb
  have heq : (u / d + σ * (v / d)) / (1 + σ * (r / d)) =
      (u + σ * v) / (d + σ * r) := by
    field_simp
  rw [heq, ← ha, ← hcount]
  field_simp

/-- Formula (119) for arbitrary complex-valued data, appropriate also for
complex test functions. Actual newforms and their zero sums still need to
be instantiated in this finite-family theorem. -/
theorem complex_sign_family_average {ι : Type*} (s : Finset ι) (ε X : ι → ℂ) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1) (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1)
    (hs : s.Nonempty) (hsign : (s.filter (fun i => ε i = σ)).Nonempty) :
    (∑ i ∈ s.filter (fun i => ε i = σ), X i) /
        ((s.filter (fun i => ε i = σ)).card : ℂ) =
      ((∑ i ∈ s, X i) / (s.card : ℂ) +
        σ * ((∑ i ∈ s, ε i * X i) / (s.card : ℂ))) /
      (1 + σ * ((∑ i ∈ s, ε i) / (s.card : ℂ))) := by
  classical
  apply complex_projection_quotient
  · exact_mod_cast ne_of_gt (Finset.card_pos.mpr hs)
  · exact_mod_cast ne_of_gt (Finset.card_pos.mpr hsign)
  · exact twice_complex_sign_sum s ε X σ hσ hε
  · exact twice_complex_sign_card s ε σ hσ hε

end DepthAspect
