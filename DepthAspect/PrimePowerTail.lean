import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual higher prime-power tail

Equation (60) is proved by differentiating an explicit antiderivative, applying
the integral comparison to log(x)/x^(3/2), and then evaluating the actual
geometric series at each odd prime. No analytic estimate is supplied as a premise.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DepthAspect.PrimePowerTail

noncomputable def logWeight (x : ℝ) : ℝ := Real.log x * x ^ (-(3 / 2 : ℝ))

noncomputable def logPrimitive (x : ℝ) : ℝ :=
  -(2 * Real.log x + 4) * x ^ (-(1 / 2 : ℝ))

theorem logWeight_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logWeight x :=
  mul_nonneg (Real.log_nonneg hx) (Real.rpow_nonneg (by linarith) _)

theorem logWeight_nat_nonneg (n : ℕ) : 0 ≤ logWeight (n : ℝ) := by
  cases n with
  | zero => simp [logWeight]
  | succ n => exact logWeight_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

theorem hasDerivAt_logPrimitive {x : ℝ} (hx : 0 < x) :
    HasDerivAt logPrimitive (logWeight x) x := by
  have hd := (((Real.hasDerivAt_log (ne_of_gt hx)).const_mul 2).add_const 4).neg.fun_mul
    (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (ne_of_gt hx)))
  refine hd.congr_deriv ?_
  simp only [Pi.neg_apply]
  have hp : x ^ (-(3 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) / x := by
    rw [← Real.rpow_sub_one (ne_of_gt hx)]
    norm_num
  norm_num only [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]
  rw [show logWeight x = Real.log x * x ^ (-(3 / 2 : ℝ)) by rfl, hp]
  ring

theorem logPrimitive_tendsto : Tendsto logPrimitive atTop (𝓝 0) := by
  have hl := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero
  have hp := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlimit : Tendsto (fun x : ℝ =>
      -2 * (Real.log x / x ^ (1 / 2 : ℝ)) + -4 * x ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (hl.const_mul (-2)).add (hp.const_mul (-4))
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold logPrimitive
  simp only [Real.rpow_neg hx.le, div_eq_mul_inv]
  ring

theorem hasDerivAt_logWeight {x : ℝ} (hx : 0 < x) :
    HasDerivAt logWeight ((1 - 3 / 2 * Real.log x) * x ^ (-(5 / 2 : ℝ))) x := by
  have hd := (Real.hasDerivAt_log (ne_of_gt hx)).fun_mul
    (Real.hasDerivAt_rpow_const (p := -(3 / 2 : ℝ)) (Or.inl (ne_of_gt hx)))
  refine hd.congr_deriv ?_
  have hp : x ^ (-(5 / 2 : ℝ)) = x ^ (-(3 / 2 : ℝ)) / x := by
    rw [← Real.rpow_sub_one (ne_of_gt hx)]
    norm_num
  norm_num only [show -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) by norm_num]
  rw [hp]
  ring

theorem logWeight_antitone : AntitoneOn logWeight (Ici 2) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 2)
  · intro x hx
    exact (hasDerivAt_logWeight (by linarith [hx.out])).continuousAt.continuousWithinAt
  · intro x hx
    have hx2 : 2 ≤ x := (interior_subset hx).out
    exact (hasDerivAt_logWeight (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx2 : 2 ≤ x := (interior_subset hx).out
    have hx0 : 0 < x := by linarith
    rw [(hasDerivAt_logWeight hx0).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg
    · have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx2
      have htwo := Real.log_two_gt_d9
      linarith
    · exact Real.rpow_nonneg hx0.le _

theorem logWeight_integrable : IntegrableOn logWeight (Ioi 2) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => hasDerivAt_logPrimitive (by linarith [hx.out]))
    (fun x hx => logWeight_nonneg (by linarith [hx.out])) logPrimitive_tendsto

theorem logWeight_integral : (∫ x in Ioi (2 : ℝ), logWeight x) =
    (2 * Real.log 2 + 4) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x (hx : x ∈ Ici (2 : ℝ)) => hasDerivAt_logPrimitive (by linarith [hx.out]))
    (fun x (hx : x ∈ Ioi (2 : ℝ)) => logWeight_nonneg (by linarith [hx.out]))
    logPrimitive_tendsto
  rw [h]
  unfold logPrimitive
  ring

theorem logWeight_nat_summable : Summable (fun n : ℕ => logWeight (n : ℝ)) :=
  logWeight_antitone.summable_of_integrableOn_Ioi (N := 2) logWeight_integrable
    (fun x hx => logWeight_nonneg (by norm_num only [Nat.cast_ofNat, Set.mem_Ioi] at hx; linarith))

theorem logWeight_tail_le_integral :
    (∑' n : ℕ, logWeight ((n + 3 : ℕ) : ℝ)) ≤
      (2 * Real.log 2 + 4) * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have h := logWeight_antitone.tsum_comp_add_le_integral 2 logWeight_integrable
    (fun x hx => logWeight_nonneg (by norm_num only [Nat.cast_ofNat, Set.mem_Ioi] at hx; linarith))
  norm_num only [Nat.cast_ofNat] at h
  rw [logWeight_integral] at h
  simpa only [Nat.add_assoc] using h

theorem logWeight_nat_tsum_le_six : (∑' n : ℕ, logWeight (n : ℝ)) ≤ 6 := by
  have htail := logWeight_tail_le_integral
  have hsplit := logWeight_nat_summable.sum_add_tsum_nat_add 3
  have hsmall : (∑ n ∈ Finset.range 3, logWeight (n : ℝ)) = logWeight 2 := by
    norm_num [Finset.sum_range_succ, logWeight]
  rw [hsmall] at hsplit
  rw [← hsplit]
  have hlog : 0 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
    constructor
    · exact Real.log_nonneg (by norm_num)
    · linarith [Real.log_two_lt_d9]
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hp : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 3) hs
    norm_num at h
    simpa only [one_div] using h
  have hp0 : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hLP : Real.log 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    simpa only [one_mul] using mul_le_mul hlog.2 hp hp0 (by norm_num : (0 : ℝ) ≤ 1)
  have heq : logWeight 2 = Real.log 2 / 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    unfold logWeight
    have hpow : (2 : ℝ) ^ (-(3 / 2 : ℝ)) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) / 2 := by
      rw [← Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    rw [hpow]
    ring
  rw [heq]
  nlinarith

/-- Actual prime-power summand with exponent `nu = j + 3`. -/
noncomputable def higherPowerTerm (p : ℝ) (j : ℕ) : ℝ :=
  Real.log p / p ^ (((j : ℝ) + 3) / 2)

theorem higherPowerTerm_geometric {p : ℝ} (hp : 0 < p) (j : ℕ) :
    higherPowerTerm p j = logWeight p * (p ^ (-(1 / 2 : ℝ))) ^ j := by
  unfold higherPowerTerm logWeight
  rw [div_eq_mul_inv, ← Real.rpow_neg hp.le,
    ← Real.rpow_mul_natCast hp.le, mul_assoc, ← Real.rpow_add hp]
  congr 2
  ring

theorem inverse_sqrt_lt_one {p : ℝ} (hp : 3 ≤ p) :
    p ^ (-(1 / 2 : ℝ)) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)

theorem higherPowerTerm_hasSum {p : ℝ} (hp : 3 ≤ p) :
    HasSum (higherPowerTerm p)
      (logWeight p / (1 - p ^ (-(1 / 2 : ℝ)))) := by
  have hgeom := (hasSum_geometric_of_lt_one
    (Real.rpow_nonneg (by linarith : 0 ≤ p) _) (inverse_sqrt_lt_one hp)).mul_left
      (logWeight p)
  change HasSum (fun j => higherPowerTerm p j) _
  simpa only [higherPowerTerm_geometric (by linarith : 0 < p), div_eq_mul_inv] using hgeom

theorem higherPowerTerm_tsum_le {p : ℝ} (hp : 3 ≤ p) :
    (∑' j : ℕ, higherPowerTerm p j) ≤
      logWeight p / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rw [(higherPowerTerm_hasSum hp).tsum_eq]
  have hr := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 3) hp
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  exact div_le_div_of_nonneg_left (logWeight_nonneg (by linarith))
    (sub_pos.mpr (inverse_sqrt_lt_one (show (3 : ℝ) ≤ 3 by rfl))) (by linarith)

/-- The odd primes actually used by the paper. -/
def OddPrime := {p : ℕ // p.Prime ∧ 3 ≤ p}

theorem oddPrime_logWeight_summable : Summable (fun p : OddPrime => logWeight (p.val : ℝ)) :=
  logWeight_nat_summable.subtype _

theorem oddPrime_logWeight_tsum_le_six :
    (∑' p : OddPrime, logWeight (p.val : ℝ)) ≤ 6 := by
  exact (Summable.tsum_subtype_le (fun n : ℕ => logWeight (n : ℝ))
    {p : ℕ | p.Prime ∧ 3 ≤ p} logWeight_nat_nonneg logWeight_nat_summable).trans
      logWeight_nat_tsum_le_six

theorem oddPrime_higherPower_summable :
    Summable (fun p : OddPrime => ∑' j : ℕ, higherPowerTerm (p.val : ℝ) j) := by
  refine (oddPrime_logWeight_summable.div_const
    (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ)))).of_nonneg_of_le ?_ ?_
  · intro p
    apply tsum_nonneg
    intro j
    unfold higherPowerTerm
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 3) p.property.2)))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · intro p
    exact higherPowerTerm_tsum_le (by exact_mod_cast p.property.2)

/-- Equation (60), with convergence of both nested series proved from the
actual logarithmic prime-power terms. -/
theorem oddPrime_higherPower_tsum_le :
    (∑' p : OddPrime, ∑' j : ℕ, higherPowerTerm (p.val : ℝ) j) ≤
      6 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  calc
    _ ≤ ∑' p : OddPrime,
        logWeight (p.val : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) :=
      oddPrime_higherPower_summable.tsum_le_tsum
        (fun p => higherPowerTerm_tsum_le (by exact_mod_cast p.property.2))
        (oddPrime_logWeight_summable.div_const _)
    _ = (∑' p : OddPrime, logWeight (p.val : ℝ)) /
        (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) := tsum_div_const
    _ ≤ _ := div_le_div_of_nonneg_right oddPrime_logWeight_tsum_le_six
      (sub_nonneg.mpr (le_of_lt (inverse_sqrt_lt_one (show (3 : ℝ) ≤ 3 by rfl))))

theorem inverse_sqrt_three_le_three_quarters :
    (3 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
  rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt 3 := Real.le_sqrt_of_sq_le (by norm_num)
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 3) hs
  norm_num at h
  simpa only [one_div] using h

/-- The numerical majorant invoked in the higher-prime-power part of (117). -/
theorem oddPrime_higherPower_tsum_le_forty_eight :
    (∑' p : OddPrime, ∑' j : ℕ, higherPowerTerm (p.val : ℝ) j) ≤ 48 := by
  apply oddPrime_higherPower_tsum_le.trans
  apply (div_le_iff₀ (sub_pos.mpr (inverse_sqrt_lt_one (show (3 : ℝ) ≤ 3 by rfl)))).2
  nlinarith [inverse_sqrt_three_le_three_quarters]

end DepthAspect.PrimePowerTail
