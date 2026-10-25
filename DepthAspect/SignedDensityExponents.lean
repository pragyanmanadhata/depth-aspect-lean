import DepthAspect.UnsignedExponents
import Mathlib.Topology.Order.Real
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Uniformity in the signed-density depth

The four power savings of (118) are quantitatively absorbed into the
inverse logarithm. The finite-prefix argument includes depth seven and
arbitrarily small positive Fourier support: its constant is a single finite
sum of the actual errors, not a depth-dependent bound or an added premise.
-/
namespace DepthAspect.SignedDensity
open Filter
open scoped BigOperators

noncomputable def errorExponents (s η : ℝ) : Fin 4 → ℝ :=
  ![-1 + 3 * s / 4 + η, -(1 / 2 : ℝ) + s / 4 + η,
    -1 + s / 2 + η, -(1 / 2 : ℝ) + η]

theorem errorExponents_negative {s η : ℝ} (hs : 0 < s)
    (hη : η < min (1 - 3 * s / 4) (1 / 2 - s / 4)) :
    ∀ i : Fin 4, errorExponents s η i < 0 := by
  have h := signed_exponents_negative hs (lt_min_iff.mp hη).1 (lt_min_iff.mp hη).2
  intro i
  fin_cases i <;> norm_num [errorExponents] <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- The exact exponent expression in (118). -/
theorem four_term_to_inverse_log {k N s η C E : ℝ}
    (hk : 1 ≤ k ^ 2) (hN : 1 < N) (hC : 0 ≤ C) (hs : 0 < s)
    (hη : η < min (1 - 3 * s / 4) (1 / 2 - s / 4))
    (hE : E ≤ C * (1 / Real.log (k ^ 2 * N) +
      N ^ (-1 + 3 * s / 4 + η) + N ^ (-(1 / 2 : ℝ) + s / 4 + η) +
      N ^ (-1 + s / 2 + η) + N ^ (-(1 / 2 : ℝ) + η))) :
    E ≤ C * (1 + ∑ i : Fin 4, (Real.log (k ^ 2) + 1 / (-errorExponents s η i))) /
      Real.log (k ^ 2 * N) := by
  apply absorb_power_errors Finset.univ (errorExponents s η) hN hk hC
    (fun i _ => errorExponents_negative hs hη i)
  simpa [errorExponents, Fin.sum_univ_succ, add_assoc] using hE

/-- One fixed finite sum extends an eventual inverse-log estimate to every
allowed depth. In particular it can include n=7 and all depths with X_s<2. -/
theorem extend_finite_prefix (L : ℕ → ℝ) (E : ℕ → ℂ) (start cutoff : ℕ)
    (hL : ∀ n, start ≤ n → 0 < L n)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n, start ≤ n → cutoff ≤ n → ‖E n‖ ≤ K / L n) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ n, start ≤ n → ‖E n‖ ≤ K' / L n := by
  let C := ∑ j ∈ Finset.range cutoff, max 0 (L j) * ‖E j‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg (le_max_left _ _) (norm_nonneg _))
  refine ⟨K + C, add_nonneg hK hC, ?_⟩
  intro n hn
  by_cases hcut : cutoff ≤ n
  · exact (hbound n hn hcut).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right hC) (hL n hn).le)
  · have hnmem : n ∈ Finset.range cutoff := Finset.mem_range.mpr (by omega)
    have hsingle : max 0 (L n) * ‖E n‖ ≤ C :=
      Finset.single_le_sum (fun j _ => mul_nonneg (le_max_left _ _) (norm_nonneg _)) hnmem
    rw [max_eq_right (hL n hn).le] at hsingle
    exact (le_div_iff₀ (hL n hn)).mpr (by nlinarith)

/-- For each fixed positive support radius, the endpoint eventually exceeds
two. The threshold may depend on the radius but is a finite natural number. -/
theorem support_endpoint_eventually_large {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    ∃ cutoff : ℕ, ∀ n : ℕ, cutoff ≤ n →
      2 ≤ Real.exp (s * Real.log (k ^ 2 * (2 : ℝ) ^ n)) := by
  have hlevel : Tendsto (fun n : ℕ => k ^ 2 * (2 : ℝ) ^ n) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) dyadic_level_tendsto
  have hlog := Real.tendsto_log_atTop.comp hlevel
  have hscale : Tendsto (fun n : ℕ => s * Real.log (k ^ 2 * (2 : ℝ) ^ n)) atTop atTop :=
    Tendsto.const_mul_atTop hs hlog
  have hexp := Real.tendsto_exp_atTop.comp hscale
  exact eventually_atTop.mp (hexp.eventually (eventually_ge_atTop (2 : ℝ)))

/-- No uniform lower bound on the support radius is needed to extend an
estimate proved on the dyadic-block range to all depths. -/
theorem extend_support_range {k s : ℝ} (hk : 0 < k) (hs : 0 < s)
    (E : ℕ → ℂ) (start : ℕ)
    (hL : ∀ n, start ≤ n → 0 < Real.log (k ^ 2 * (2 : ℝ) ^ n))
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n, start ≤ n →
      2 ≤ Real.exp (s * Real.log (k ^ 2 * (2 : ℝ) ^ n)) →
      ‖E n‖ ≤ K / Real.log (k ^ 2 * (2 : ℝ) ^ n)) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ n, start ≤ n →
      ‖E n‖ ≤ K' / Real.log (k ^ 2 * (2 : ℝ) ^ n) := by
  obtain ⟨cutoff, hcutoff⟩ := support_endpoint_eventually_large hk hs
  exact extend_finite_prefix (fun n => Real.log (k ^ 2 * (2 : ℝ) ^ n))
    E start cutoff hL K hK (fun n hn hc => hbound n hn (hcutoff n hc))

end DepthAspect.SignedDensity
