import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Literal natural averages over a finite spectral family

This common interface contains no trace-formula or density assumptions.
-/
namespace DepthAspect.SpectralFamily

open scoped BigOperators

noncomputable def average {ι : Type*} [Fintype ι] (X : ι → ℂ) : ℂ :=
  (∑ f, X f) / (Fintype.card ι : ℂ)

noncomputable def heckeAverage {ι : Type*} [Fintype ι] (a : ι → ℕ → ℂ) (m : ℕ) : ℂ :=
  average (fun f => a f m)

theorem average_add {ι : Type*} [Fintype ι] (X Y : ι → ℂ) :
    average (fun f => X f + Y f) = average X + average Y := by
  simp only [average, Finset.sum_add_distrib, add_div]

theorem average_sub {ι : Type*} [Fintype ι] (X Y : ι → ℂ) :
    average (fun f => X f - Y f) = average X - average Y := by
  simp only [average, Finset.sum_sub_distrib, sub_div]

theorem average_mul_left {ι : Type*} [Fintype ι] (c : ℂ) (X : ι → ℂ) :
    average (fun f => c * X f) = c * average X := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_mul_right {ι : Type*} [Fintype ι] (X : ι → ℂ) (c : ℂ) :
    average (fun f => X f * c) = average X * c := by
  simp only [average, ← Finset.sum_mul]
  ring

theorem average_const {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℂ) :
    average (fun _ : ι => c) = c := by
  have hc : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [average, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hc

theorem average_finset_sum {ι κ : Type*} [Fintype ι]
    (S : Finset κ) (X : ι → κ → ℂ) :
    average (fun f => ∑ p ∈ S, X f p) = ∑ p ∈ S, average (fun f => X f p) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem norm_average_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → ℂ) (C : ℝ) (hX : ∀ f, ‖X f‖ ≤ C) : ‖average X‖ ≤ C := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : ‖∑ f, X f‖ ≤ (Fintype.card ι : ℝ) * C := by
    calc
      _ ≤ ∑ f, ‖X f‖ := norm_sum_le _ _
      _ ≤ ∑ _f : ι, C := Finset.sum_le_sum (fun f _ => hX f)
      _ = _ := by simp
  rw [average, norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hs)

end DepthAspect.SpectralFamily
