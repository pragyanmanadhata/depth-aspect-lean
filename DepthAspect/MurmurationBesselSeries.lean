import DepthAspect.MurmurationPoisson

/-! The actual first identity in (128), obtained by Poisson summation on
both lattices. The Bessel series is proved summable, not merely assigned a
formal value. -/
open scoped BigOperators FourierTransform
namespace DepthAspect.MurmurationBesselSeries
open MurmurationKernel MurmurationFourier MurmurationDecay
open MurmurationLattice MurmurationPoisson BesselFirstKind

noncomputable def g (a ℓ : ℕ) (y : ℝ) : ℝ :=
  weightedDensity a ℓ (fun _ => 1) y

/-- The Fourier decay already proved for the literal compact kernel
implies absolute summability of each Bessel series occurring in Poisson. -/
theorem bessel_series_summable (hDLMF : DLMFIdentities) (a : ℕ)
    {c : ℝ} (hc : 0 < c) :
    Summable (fun ν : ℕ+ => J (2 * a + 1) (2 * Real.pi * ν / c) / (ν : ℝ)) := by
  have hinj : Function.Injective (fun ν : ℕ+ => ((ν : ℕ) : ℤ)) := by
    intro x y h
    apply Subtype.ext
    change ((x : ℕ) : ℤ) = ((y : ℕ) : ℤ) at h
    exact Int.ofNat.inj h
  have hs := (scaled_fourier_integer_summable hDLMF a hc).comp_injective hinj
  let m : ℂ := (((2 * a + 1 : ℕ) : ℝ) : ℂ)
  let s : ℂ := (((-1 : ℝ) ^ a) : ℂ)
  have hm : m ≠ 0 := by
    dsimp [m]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hsign : s ≠ 0 := by dsimp [s]; exact_mod_cast pow_ne_zero a (by norm_num : (-1 : ℝ) ≠ 0)
  apply Complex.summable_ofReal.mp
  apply (hs.mul_left (2 / (m * s))).congr
  intro ν
  have hν : (0 : ℝ) < ν := by exact_mod_cast ν.pos
  simp only [Function.comp_apply, Int.cast_natCast]
  rw [fourier_eq_bessel hDLMF a (ne_of_gt (div_pos hν hc))]
  have he : 2 * Real.pi * ((ν : ℝ) / c) = 2 * Real.pi * ν / c := by ring
  rw [he]
  dsimp [m, s] at *
  push_cast at hm hsign ⊢
  field_simp [hm, hsign, Complex.ofReal_ne_zero.mpr (ne_of_gt hc),
    Complex.ofReal_ne_zero.mpr (ne_of_gt hν)]
  <;> ring

/-- Both zero modes cancel in the actual residue lattice. -/
theorem residue_lattice_eq_bessel (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) {c : ℝ} (hc : 0 < c) :
    (∑' r : ℤ, residueWeight ℓ r *
      kernel (2 * a + 2) ((c / (ℓ : ℝ)) * r)) =
      (((2 * a + 1 : ℕ) : ℝ) * (-1 : ℝ) ^ a) *
        ((∑' ν : ℕ+, J (2 * a + 1) (2 * Real.pi * ν / c) / (ν : ℝ)) -
          (ℓ : ℝ)⁻¹ * ∑' ν : ℕ+,
            J (2 * a + 1) (2 * Real.pi * ℓ * ν / c) / (ν : ℝ)) := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have h := residue_lattice_difference a hℓ hc
  rw [lattice_sum_eq_bessel hDLMF a hc,
    lattice_sum_eq_bessel hDLMF a (div_pos hc hℓR)] at h
  have harg (ν : ℕ+) : 2 * Real.pi * (ν : ℝ) / (c / (ℓ : ℝ)) =
      2 * Real.pi * ℓ * ν / c := by field_simp [ne_of_gt hc, ne_of_gt hℓR] <;> ring
  simp only [harg, complexKernel, ← Complex.ofReal_mul, ← Complex.ofReal_tsum] at h
  have hscale : ((ℓ : ℝ) : ℂ)⁻¹ * ((c / (ℓ : ℝ) : ℝ) : ℂ)⁻¹ = (c : ℂ)⁻¹ := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hc),
      (by exact_mod_cast Nat.ne_of_gt hℓ : (ℓ : ℂ) ≠ 0)] <;> ring
  apply Complex.ofReal_injective
  rw [h]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv]
  rw [mul_add, ← mul_assoc, hscale]
  ring

/-- The two Bessel sequences in the literal formula (128) are summable
for every positive y, including the small-y range. -/
theorem g_bessel_series_summable (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 0 < ℓ) {y : ℝ} (hy : 0 < y) :
    Summable (fun ν : ℕ+ =>
      J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
        J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)) := by
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have h1 := bessel_series_summable hDLMF a
    (by positivity : 0 < 1 / (2 * Real.sqrt y))
  have h2 := (bessel_series_summable hDLMF a
    (by positivity : 0 < 1 / (2 * (ℓ : ℝ) * Real.sqrt y))).div_const (ℓ : ℝ)
  have he1 (ν : ℕ+) : 2 * Real.pi * (ν : ℝ) / (1 / (2 * Real.sqrt y)) =
      4 * Real.pi * ν * Real.sqrt y := by field_simp; ring
  have he2 (ν : ℕ+) : 2 * Real.pi * (ν : ℝ) / (1 / (2 * (ℓ : ℝ) * Real.sqrt y)) =
      4 * Real.pi * ℓ * ν * Real.sqrt y := by field_simp; ring
  simp only [he1] at h1
  simp only [he2, div_div] at h2
  exact h1.sub (h2.congr (fun ν => by rw [mul_comm (ν : ℝ) (ℓ : ℝ)]))

/-- The first identity of (128), with the actual unweighted density on
the left and an absolutely convergent series on the right. -/
theorem g_eq_bessel (hDLMF : DLMFIdentities) (a : ℕ)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {y : ℝ} (hy : 0 < y) :
    g a ℓ y = (2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹)) *
      ∑' ν : ℕ+, (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
        J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)) := by
  have hℓR : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  let c : ℝ := 1 / (2 * Real.sqrt y)
  have hc : 0 < c := by dsimp [c]; positivity
  have hlat := residue_lattice_eq_bessel hDLMF a (by omega : 0 < ℓ) hc
  have harg (r : ℤ) : (c / (ℓ : ℝ)) * r =
      (r : ℝ) / (2 * (ℓ : ℝ) * Real.sqrt y) := by dsimp [c]; ring
  have he1 (ν : ℕ+) : 2 * Real.pi * (ν : ℝ) / c =
      4 * Real.pi * ν * Real.sqrt y := by dsimp [c]; field_simp; ring
  have he2 (ν : ℕ+) : 2 * Real.pi * ℓ * (ν : ℝ) / c =
      4 * Real.pi * ℓ * ν * Real.sqrt y := by dsimp [c]; field_simp; ring
  simp only [harg, he1, he2] at hlat
  have h1 := bessel_series_summable hDLMF a hc
  have h2 := (bessel_series_summable hDLMF a
    (by positivity : 0 < c / (ℓ : ℝ))).mul_left ((ℓ : ℝ)⁻¹)
  simp only [he1] at h1
  have he3 (ν : ℕ+) : 2 * Real.pi * (ν : ℝ) / (c / (ℓ : ℝ)) =
      4 * Real.pi * ℓ * ν * Real.sqrt y := by dsimp [c]; field_simp; ring
  simp only [he3] at h2
  have hseries : (∑' ν : ℕ+, J (2 * a + 1)
      (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ)) -
      (ℓ : ℝ)⁻¹ * ∑' ν : ℕ+, J (2 * a + 1)
        (4 * Real.pi * ℓ * ν * Real.sqrt y) / (ν : ℝ) =
      ∑' ν : ℕ+, (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
        J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν)) := by
    rw [← tsum_mul_left, ← h1.tsum_sub h2]
    apply tsum_congr
    intro ν
    congr 1
    ring
  have hm : (((2 * a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hz : 1 - (ℓ : ℝ)⁻¹ ≠ 0 := by
    have := inv_lt_one_of_one_lt₀ hℓR
    linarith
  have hsign : ((-1 : ℝ) ^ a) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm a 2, pow_mul]
    norm_num
  unfold g weightedDensity
  simp only [mul_one]
  rw [hlat, hseries]
  calc
    _ = ((2 * Real.pi * Real.sqrt y / (1 - (ℓ : ℝ)⁻¹)) *
        ∑' ν : ℕ+, (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
          J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) / ((ℓ : ℝ) * ν))) *
        ((-1 : ℝ) ^ a) ^ 2 := by
          generalize hsum : (∑' ν : ℕ+,
            (J (2 * a + 1) (4 * Real.pi * ν * Real.sqrt y) / (ν : ℝ) -
              J (2 * a + 1) (4 * Real.pi * ℓ * ν * Real.sqrt y) /
                ((ℓ : ℝ) * ν))) = S
          generalize hzv : 1 - (ℓ : ℝ)⁻¹ = z at hz ⊢
          field_simp [hm, hz]
          <;> ring
    _ = _ := by rw [hsign, mul_one]

theorem g_small (a : ℕ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {y : ℝ}
    (hy : 0 < y) (hymax : y ≤ 1 / (4 * (ℓ : ℝ) ^ 2)) :
    g a ℓ y = (2 * Real.pi / ((2 * a + 1 : ℕ) : ℝ)) * Real.sqrt y :=
  weightedDensity_small a hℓ (fun _ => 1) rfl hy hymax

end DepthAspect.MurmurationBesselSeries
