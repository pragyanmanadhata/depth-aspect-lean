import DepthAspect.MurmurationDecay
import DepthAspect.MurmurationLattice

/-! Actual lattice reindexing and zero-frequency cancellation in (128). -/
open scoped BigOperators FourierTransform
namespace DepthAspect.MurmurationPoisson
open MurmurationFourier MurmurationDecay MurmurationLattice

/-- The positive-frequency contribution on a rescaled lattice is the
actual Bessel series, with every factor of two and lattice scale retained. -/
theorem positive_fourier_sum_eq_bessel (hDLMF : BesselFirstKind.DLMFIdentities)
    (a : ℕ) {c : ℝ} (hc : 0 < c) :
    2 * (c⁻¹ : ℂ) *
      (∑' ν : ℕ+, 𝓕 (complexKernel (2 * a + 2)) ((ν : ℝ) / c)) =
    ((((2 * a + 1 : ℕ) : ℝ) * (-1 : ℝ) ^ a : ℝ) : ℂ) *
      ∑' ν : ℕ+, ((BesselFirstKind.J (2 * a + 1)
        (2 * Real.pi * ν / c) / (ν : ℝ) : ℝ) : ℂ) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro ν
  have hν : (0 : ℝ) < ν := by exact_mod_cast ν.pos
  rw [fourier_eq_bessel hDLMF a (ne_of_gt (div_pos hν hc))]
  have he : 2 * Real.pi * ((ν : ℝ) / c) = 2 * Real.pi * ν / c := by ring
  rw [he]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hc),
    Complex.ofReal_ne_zero.mpr (ne_of_gt hν)]
  <;> ring

/-- One rescaled lattice splits into its zero mode and the actual Bessel
series. This identity precedes the arithmetic divisor reindexing. -/
theorem lattice_sum_eq_bessel (hDLMF : BesselFirstKind.DLMFIdentities)
    (a : ℕ) {c : ℝ} (hc : 0 < c) :
    (∑' n : ℤ, complexKernel (2 * a + 2) (c * n)) =
      (c⁻¹ : ℂ) * 𝓕 (complexKernel (2 * a + 2)) 0 +
      ((((2 * a + 1 : ℕ) : ℝ) * (-1 : ℝ) ^ a : ℝ) : ℂ) *
        ∑' ν : ℕ+, ((BesselFirstKind.J (2 * a + 1)
          (2 * Real.pi * ν / c) / (ν : ℝ) : ℝ) : ℂ) := by
  rw [poisson_scaled_positive hDLMF a hc, positive_fourier_sum_eq_bessel hDLMF a hc]

/-- The divisible residue classes form exactly the multiplied lattice. -/
theorem divisible_lattice_sum (f : ℤ → ℂ) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    (∑' r : ℤ, if ℓ ∣ r then f r else 0) = ∑' n : ℤ, f (ℓ * n) := by
  have hi : Function.Injective (fun n : ℤ => ℓ * n) := by
    intro x y h
    exact mul_left_cancel₀ hℓ h
  have hs : Function.support (fun r : ℤ => if ℓ ∣ r then f r else 0) ⊆
      Set.range (fun n : ℤ => ℓ * n) := by
    intro r hr
    by_cases hd : ℓ ∣ r
    · obtain ⟨n, rfl⟩ := hd
      exact ⟨n, rfl⟩
    · exact (hr (if_neg hd)).elim
  have h := hi.tsum_eq hs
  simpa using h.symm

/-- The residue weight in (106) is exactly the difference of the full
lattice and its sublattice; all series are summable by compact support. -/
theorem residue_lattice_difference (a : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {c : ℝ} (hc : 0 < c) :
    (∑' r : ℤ, (residueWeight ℓ r : ℂ) *
      complexKernel (2 * a + 2) ((c / (ℓ : ℝ)) * r)) =
      (∑' n : ℤ, complexKernel (2 * a + 2) (c * n)) -
        ((ℓ : ℝ)⁻¹ : ℂ) *
          ∑' n : ℤ, complexKernel (2 * a + 2) ((c / (ℓ : ℝ)) * n) := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  let f : ℤ → ℂ := fun r => complexKernel (2 * a + 2) ((c / (ℓ : ℝ)) * r)
  have hf : Summable f := scaled_lattice_summable _ (div_pos hc hℓR)
  have hi : Summable (fun r : ℤ => if (ℓ : ℤ) ∣ r then f r else 0) := by
    apply (hf.indicator {r : ℤ | (ℓ : ℤ) ∣ r}).congr
    intro r
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have he : (fun r : ℤ => (residueWeight ℓ r : ℂ) * f r) =
      (fun r => (if (ℓ : ℤ) ∣ r then f r else 0) - ((ℓ : ℝ)⁻¹ : ℂ) * f r) := by
    funext r
    unfold residueWeight
    split_ifs <;> push_cast <;> ring
  change (∑' r : ℤ, (residueWeight ℓ r : ℂ) * f r) = _
  rw [he, hi.tsum_sub (hf.mul_left _), tsum_mul_left,
    divisible_lattice_sum f (by exact_mod_cast Nat.ne_of_gt hℓ)]
  have harg (n : ℤ) : (c / (ℓ : ℝ)) * (((ℓ : ℤ) * n : ℤ) : ℝ) = c * n := by
    push_cast
    field_simp [ne_of_gt hℓR]
    <;> ring
  simp only [f, harg]

/-- The two zero modes cancel with exactly the coefficients appearing in
the paper; the remaining positive-frequency sums are absolutely convergent. -/
theorem zero_frequency_cancellation (hDLMF : BesselFirstKind.DLMFIdentities)
    (a : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) {c : ℝ} (hc : 0 < c) :
    (∑' r : ℤ, (residueWeight ℓ r : ℂ) *
      complexKernel (2 * a + 2) ((c / (ℓ : ℝ)) * r)) =
      2 * (c⁻¹ : ℂ) *
        ((∑' ν : ℕ+, 𝓕 (complexKernel (2 * a + 2)) ((ν : ℝ) / c)) -
          ∑' ν : ℕ+, 𝓕 (complexKernel (2 * a + 2)) ((ℓ : ℝ) * ν / c)) := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  rw [residue_lattice_difference a hℓ hc, poisson_scaled_positive hDLMF a hc,
    poisson_scaled_positive hDLMF a (div_pos hc hℓR)]
  have harg (ν : ℕ+) : (ν : ℝ) / (c / (ℓ : ℝ)) = (ℓ : ℝ) * ν / c := by
    field_simp [ne_of_gt hc, ne_of_gt hℓR]
    <;> ring
  simp only [harg]
  let z : ℂ := 𝓕 (complexKernel (2 * a + 2)) 0
  let S : ℂ := ∑' ν : ℕ+, 𝓕 (complexKernel (2 * a + 2)) ((ν : ℝ) / c)
  let T : ℂ := ∑' ν : ℕ+, 𝓕 (complexKernel (2 * a + 2)) ((ℓ : ℝ) * ν / c)
  let ci : ℂ := (c : ℂ)⁻¹
  let li : ℂ := ((ℓ : ℝ) : ℂ)⁻¹
  let di : ℂ := ((c / (ℓ : ℝ) : ℝ) : ℂ)⁻¹
  change ci * z + 2 * ci * S - li * (di * z + 2 * di * T) = 2 * ci * (S - T)
  have hscale : li * di = ci := by
    dsimp [li, di, ci]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hc),
      (by exact_mod_cast Nat.ne_of_gt hℓ : (ℓ : ℂ) ≠ 0)]
    <;> ring
  calc
    _ = ci * z + 2 * ci * S - (li * di) * z - 2 * (li * di) * T := by ring
    _ = _ := by rw [hscale]; ring

end DepthAspect.MurmurationPoisson
