import DepthAspect.MurmurationOscillationSeries
import DepthAspect.CosineMeans

/-! The actual mean and nonzero coefficient (134) of the series (131).
The second possible resonance is excluded by the proved arithmetic support. -/
open Filter
open scoped BigOperators Topology
namespace DepthAspect.MurmurationBohrCoefficient
open ArithmeticWeights MurmurationOscillationSeries OscillatoryMean CosineMeans

noncomputable def frequency (i : ℕ+ × ℕ+) : ℝ := 4 * Real.pi * i.2 / i.1
noncomputable def secondFrequency (ℓ : ℕ) (i : ℕ+ × ℕ+) : ℝ :=
  4 * Real.pi * ℓ * i.2 / i.1
noncomputable def amplitude (ℓ : ℕ) (i : ℕ+ × ℕ+) : ℝ :=
  K ℓ * (b ℓ i.1 * Real.sqrt i.1) * (i.2 : ℝ) ^ (-(3 / 2 : ℝ))

theorem frequency_pos (i : ℕ+ × ℕ+) : 0 < frequency i := by
  unfold frequency
  positivity

theorem secondFrequency_pos {ℓ : ℕ} (hℓ : 0 < ℓ) (i : ℕ+ × ℕ+) :
    0 < secondFrequency ℓ i := by
  unfold secondFrequency
  positivity

theorem frequency_resonance (i : ℕ+ × ℕ+) : frequency i = 4 * Real.pi ↔ i.2 = i.1 := by
  have hd : (i.1 : ℝ) ≠ 0 := by positivity
  have hp : 4 * Real.pi ≠ 0 := by positivity
  rw [frequency, div_eq_iff hd, mul_right_inj' hp]
  constructor
  · intro h
    apply Subtype.ext
    exact Nat.cast_injective h
  · intro h
    rw [h]

/-- The forbidden second resonance forces the omitted prime to divide d. -/
theorem secondFrequency_ne {ℓ : ℕ} (hℓ : ℓ.Prime) (i : ℕ+ × ℕ+)
    (hb : b ℓ i.1 ≠ 0) : secondFrequency ℓ i ≠ 4 * Real.pi := by
  intro h
  have hd : (i.1 : ℝ) ≠ 0 := by positivity
  have hp : 4 * Real.pi ≠ 0 := by positivity
  have he : (ℓ : ℝ) * (i.2 : ℝ) = (i.1 : ℝ) := by
    apply mul_left_cancel₀ hp
    have he := (div_eq_iff hd).mp h
    nlinarith [he]
  have heN : ℓ * (i.2 : ℕ) = (i.1 : ℕ) := by exact_mod_cast he
  exact (hℓ.coprime_iff_not_dvd.mp (b_ne_zero_coprime hℓ hb).symm)
    ⟨i.2, heN.symm⟩

theorem oscillationTerm_eq (a ℓ : ℕ) (i : ℕ+ × ℕ+) (x : ℝ) :
    oscillationTerm a ℓ i x = amplitude ℓ i *
      (Real.cos (frequency i * x - phase a) - (ℓ : ℝ) ^ (-(3 / 2 : ℝ)) *
        Real.cos (secondFrequency ℓ i * x - phase a)) := by
  unfold oscillationTerm amplitude frequency secondFrequency
  congr 2 <;> congr 1 <;> ring

theorem diagonal_amplitude (ℓ : ℕ) (d : ℕ+) :
    amplitude ℓ (d, d) = K ℓ * (b ℓ d / (d : ℝ)) := by
  have hd : (0 : ℝ) < d := by positivity
  have he : Real.sqrt (d : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) = (d : ℝ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hd]
    norm_num [Real.rpow_neg_one]
  dsimp [amplitude]
  calc
    _ = K ℓ * b ℓ d * (Real.sqrt d * (d : ℝ) ^ (-(3 / 2 : ℝ))) := by ring
    _ = _ := by rw [he]; ring

theorem oscillationTerm_mean_zero (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (i : ℕ+ × ℕ+) :
    Tendsto (average (fun x => (oscillationTerm a ℓ i x : ℂ))) atTop (𝓝 0) := by
  have h₁ := frequency_pos i
  have h₂ := secondFrequency_pos hℓ.pos i
  have h := cosine_difference_mean (amplitude ℓ i) ((ℓ : ℝ) ^ (-(3 / 2 : ℝ)))
    (frequency i) (secondFrequency ℓ i) 0 (phase a)
  simpa only [← oscillationTerm_eq, neg_zero, wave_zero, mul_one, if_neg (ne_of_gt h₁),
    if_neg (neg_ne_zero.mpr (ne_of_gt h₁)), if_neg (ne_of_gt h₂),
    if_neg (neg_ne_zero.mpr (ne_of_gt h₂)), mul_zero, add_zero, sub_zero]
    using h

noncomputable def coefficient (a ℓ : ℕ) (i : ℕ+ × ℕ+) : ℂ :=
  if i.2 = i.1 then ((K ℓ * (b ℓ i.1 / (i.1 : ℝ)) / 2 : ℝ) : ℂ) *
    wave (-(phase a)) 1 else 0

/-- The coefficient is supported exactly on the first diagonal, with no
contribution from the second cosine on the arithmetic support. -/
theorem oscillationTerm_coefficient (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (i : ℕ+ × ℕ+) :
    Tendsto (average (fun x => (oscillationTerm a ℓ i x : ℂ) *
      wave (-(4 * Real.pi)) x)) atTop (𝓝 (coefficient a ℓ i)) := by
  by_cases hb : b ℓ i.1 = 0
  · have hz : (fun x => (oscillationTerm a ℓ i x : ℂ) * wave (-(4 * Real.pi)) x) =
        fun _ => 0 := by funext x; simp [oscillationTerm, hb]
    rw [hz]
    have haz : OscillatoryMean.average (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by
      funext T
      simp [OscillatoryMean.average]
    rw [haz]
    have hc : coefficient a ℓ i = 0 := by simp [coefficient, hb]
    rw [hc]
    exact tendsto_const_nhds
  · have h₁ := frequency_pos i
    have h₂ := secondFrequency_pos hℓ.pos i
    have hπ : 0 < 4 * Real.pi := by positivity
    have hn₁ : -frequency i ≠ 4 * Real.pi := by linarith
    have hn₂ : -secondFrequency ℓ i ≠ 4 * Real.pi := by linarith
    have h := cosine_difference_mean (amplitude ℓ i) ((ℓ : ℝ) ^ (-(3 / 2 : ℝ)))
      (frequency i) (secondFrequency ℓ i) (4 * Real.pi) (phase a)
    simp only [← oscillationTerm_eq, if_neg hn₁, if_neg hn₂,
      if_neg (secondFrequency_ne hℓ i hb), mul_zero, add_zero, sub_zero] at h
    by_cases hi : i.2 = i.1
    · rw [if_pos ((frequency_resonance i).mpr hi), mul_one] at h
      have ha : amplitude ℓ i = K ℓ * (b ℓ i.1 / (i.1 : ℝ)) := by
        have he : i = (i.1, i.1) := Prod.ext rfl hi
        rw [he, diagonal_amplitude]
      convert h using 1
      simp only [coefficient, if_pos hi, ha, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    · simpa only [if_neg (mt (frequency_resonance i).mp hi), mul_zero,
        coefficient, if_neg hi] using h

theorem coefficient_bound (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) (i : ℕ+ × ℕ+) :
    ‖coefficient a ℓ i‖ ≤ majorant ℓ i := by
  apply le_of_tendsto (oscillationTerm_coefficient a hℓ i).norm
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
  apply average_norm_bound hU
  intro x
  simpa only [norm_mul, wave_norm, mul_one, Complex.norm_real]
    using oscillationTerm_bound a hℓ i x

theorem coefficient_summable (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Summable (coefficient a ℓ) :=
  (majorant_summable ℓ).of_norm_bounded (coefficient_bound a hℓ)

theorem coefficient_tsum (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    (∑' i, coefficient a ℓ i) = (q ℓ : ℂ) * wave (-(phase a)) 1 := by
  rw [(coefficient_summable a hℓ).tsum_prod]
  have hi : ∀ d : ℕ+, (∑' ν : ℕ+, coefficient a ℓ (d, ν)) =
      ((K ℓ * (b ℓ d / (d : ℝ)) / 2 : ℝ) : ℂ) * wave (-(phase a)) 1 := by
    intro d
    rw [tsum_eq_single d]
    · simp [coefficient]
    · intro ν hν
      simp [coefficient, hν]
  simp_rw [hi]
  rw [tsum_mul_right, ← Complex.ofReal_tsum]
  congr 2
  simp only [q, S, div_eq_mul_inv, tsum_mul_right, tsum_mul_left]

/-- The actual uniformly convergent series has zero ordinary mean. -/
theorem A_mean_zero (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Tendsto (average (fun x => (A a ℓ x : ℂ))) atTop (𝓝 0) := by
  have h := average_tsum_tendsto
    (fun i x => (oscillationTerm a ℓ i x : ℂ))
    (fun i => by unfold oscillationTerm; fun_prop)
    (majorant_summable ℓ)
    (fun i x => by simpa only [Complex.norm_real] using oscillationTerm_bound a hℓ i x)
    (fun _ => 0) (oscillationTerm_mean_zero a hℓ)
  simpa only [tsum_zero, A, Complex.ofReal_tsum] using h

/-- The literal nonzero Bohr coefficient displayed in (134). -/
theorem A_coefficient (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Tendsto (average (fun x => (A a ℓ x : ℂ) * wave (-(4 * Real.pi)) x))
      atTop (𝓝 ((q ℓ : ℂ) * wave (-(phase a)) 1)) := by
  have h := average_tsum_tendsto
    (fun i x => (oscillationTerm a ℓ i x : ℂ) * wave (-(4 * Real.pi)) x)
    (fun i => by unfold oscillationTerm wave; fun_prop)
    (majorant_summable ℓ)
    (fun i x => by simpa only [norm_mul, wave_norm, mul_one, Complex.norm_real]
      using oscillationTerm_bound a hℓ i x)
    (coefficient a ℓ) (oscillationTerm_coefficient a hℓ)
  rw [coefficient_tsum a hℓ] at h
  simpa only [A, Complex.ofReal_tsum, tsum_mul_right] using h

theorem A_coefficient_norm (a : ℕ) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ‖(q ℓ : ℂ) * wave (-(phase a)) 1‖ = q ℓ := by
  simp only [norm_mul, wave_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (q_pos hℓ)]

end DepthAspect.MurmurationBohrCoefficient
