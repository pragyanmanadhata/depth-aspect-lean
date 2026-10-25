import DepthAspect.PrimePairBound

/-! The actual finite trace-index set common to both depth parities. -/
namespace DepthAspect.SignedDensity
open scoped BigOperators

noncomputable def activeIndices (N u : ℝ) : Finset ℤ :=
  let R : ℕ := ⌊4 * Real.sqrt (u / N)⌋₊
  (Finset.Icc (-(R : ℤ)) (R : ℤ)).filter (fun r : ℤ => N * (r : ℝ) ^ 2 / 16 < u)

theorem mem_activeIndices {N u : ℝ} (hN : 0 < N) (hu : 0 < u) (r : ℤ) :
    r ∈ activeIndices N u ↔ N * (r : ℝ) ^ 2 / 16 < u := by
  classical
  rw [activeIndices, Finset.mem_filter]
  refine and_iff_right_of_imp ?_
  intro ht
  have hs := Real.sq_sqrt (by positivity : 0 ≤ u / N)
  have hsq : (r : ℝ) ^ 2 ≤ (4 * Real.sqrt (u / N)) ^ 2 := by
    have hdiv : (r : ℝ) ^ 2 ≤ 16 * u / N :=
      (le_div_iff₀ hN).mpr (by nlinarith)
    calc
      (r : ℝ) ^ 2 ≤ 16 * (u / N) := by simpa only [mul_div_assoc] using hdiv
      _ = (4 * Real.sqrt (u / N)) ^ 2 := by rw [mul_pow, hs]; norm_num
  have habs : |(r : ℝ)| ≤ 4 * Real.sqrt (u / N) :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)
  have hn : r.natAbs ≤ ⌊4 * Real.sqrt (u / N)⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_natAbs, Int.cast_abs] using habs
  have hi : (r.natAbs : ℤ) ≤ (⌊4 * Real.sqrt (u / N)⌋₊ : ℤ) := by exact_mod_cast hn
  rw [Int.natCast_natAbs] at hi
  exact Finset.mem_Icc.mpr (abs_le.mp hi)

theorem active_argument_bound {N u : ℝ} (hN : 0 < N) (hu : 0 < u)
    {r : ℤ} (hr : r ∈ activeIndices N u) :
    |(r : ℝ) / (4 * Real.sqrt (u / N))| < 1 := by
  have ht := (mem_activeIndices hN hu r).mp hr
  have hs := Real.sq_sqrt (by positivity : 0 ≤ u / N)
  have hR : 0 < 4 * Real.sqrt (u / N) := by positivity
  rw [abs_div, abs_of_pos hR]
  apply (div_lt_one hR).mpr
  have hdiv : (r : ℝ) ^ 2 < 16 * u / N :=
    (lt_div_iff₀ hN).mpr (by nlinarith)
  apply (sq_lt_sq₀ (abs_nonneg _) hR.le).mp
  rw [sq_abs, mul_pow, hs]
  norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num]
  simpa only [mul_div_assoc] using hdiv

end DepthAspect.SignedDensity
