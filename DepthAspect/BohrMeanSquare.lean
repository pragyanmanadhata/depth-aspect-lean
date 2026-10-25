import DepthAspect.UniformPeriodicMean

/-! A finite two-frequency mean-square inequality, proved by subtracting
the matching real cosine and averaging a nonnegative square. -/
open MeasureTheory Filter
open scoped Topology
namespace DepthAspect.BohrMeanSquare
open OscillatoryMean CosineMeans UniformPeriodicMean

theorem realAverage_re {f : ℝ → ℂ} (hf : Continuous f) (T : ℝ) :
    realAverage (fun x => (f x).re) T = (average f T).re := by
  have hi := Complex.reCLM.intervalIntegral_comp_comm
    (hf.intervalIntegrable (μ := volume) (a := 0) (b := T))
  change (∫ x : ℝ in (0)..T, (f x).re) = (∫ x : ℝ in (0)..T, f x).re at hi
  unfold realAverage OscillatoryMean.average
  rw [hi, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem cosine_projection (f : ℝ → ℝ) (ω δ x : ℝ) :
    (wave δ 1 * ((f x : ℂ) * wave (-ω) x)).re = f x * Real.cos (ω * x - δ) := by
  have he : wave δ 1 * wave (-ω) x = wave (δ - ω * x) 1 := by
    unfold wave
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ((f x : ℂ) * (wave δ 1 * wave (-ω) x)).re := by congr 1; ring
    _ = f x * Real.cos (δ - ω * x) := by
      rw [he]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, wave, mul_one, Complex.exp_ofReal_mul_I_re]
    _ = _ := by rw [show δ - ω * x = -(ω * x - δ) by ring, Real.cos_neg]

theorem cosine_projection_mean {f : ℝ → ℝ} (hf : Continuous f) {ω δ q : ℝ}
    (hcoef : Tendsto (average (fun x => (f x : ℂ) * wave (-ω) x))
      atTop (𝓝 ((q : ℂ) * wave (-δ) 1))) :
    Tendsto (realAverage (fun x => f x * Real.cos (ω * x - δ))) atTop (𝓝 q) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (hcoef.const_mul (wave δ 1))
  have hc : (wave δ 1 * ((q : ℂ) * wave (-δ) 1)).re = q := by
    have hw : wave δ 1 * wave (-δ) 1 = 1 := by rw [wave_mul]; simp
    calc
      _ = ((q : ℂ) * (wave δ 1 * wave (-δ) 1)).re := by congr 1; ring
      _ = _ := by rw [hw, mul_one, Complex.ofReal_re]
  rw [hc] at h
  apply h.congr'
  filter_upwards [] with T
  have he : (fun x => f x * Real.cos (ω * x - δ)) =
      fun x => (wave δ 1 * ((f x : ℂ) * wave (-ω) x)).re :=
    funext (fun x => (cosine_projection f ω δ x).symm)
  change (wave δ 1 * average (fun x => (f x : ℂ) * wave (-ω) x) T).re = _
  rw [he, realAverage_re
    (f := fun x => wave δ 1 * ((f x : ℂ) * wave (-ω) x))
    (continuous_const.mul ((Complex.continuous_ofReal.comp hf).mul (wave_continuous _))),
    average_const_mul]

theorem real_cosine_mean_zero {ω : ℝ} (hω : ω ≠ 0) (δ : ℝ) :
    Tendsto (realAverage (fun x => Real.cos (ω * x - δ))) atTop (𝓝 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (cosine_mean_zero hω δ)
  simpa only [Function.comp_def, ← realAverage_cast, Complex.ofReal_re, Complex.zero_re] using h

theorem real_cosine_square_mean {ω : ℝ} (hω : ω ≠ 0) (δ : ℝ) :
    Tendsto (realAverage (fun x => (Real.cos (ω * x - δ)) ^ 2))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hz : 2 * ω ≠ 0 := mul_ne_zero (by norm_num) hω
  have h := ((real_cosine_mean_zero hz (2 * δ)).add
    (tendsto_const_nhds (x := (1 : ℝ)))).const_mul (1 / 2 : ℝ)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have he : (fun x => (Real.cos (ω * x - δ)) ^ 2) =
      fun x => (1 / 2 : ℝ) * (Real.cos ((2 * ω) * x - 2 * δ) + 1) := by
    funext x
    have hc := Real.cos_two_mul (ω * x - δ)
    rw [show 2 * (ω * x - δ) = (2 * ω) * x - 2 * δ by ring] at hc
    linarith
  rw [he, realAverage_const_mul, realAverage_add (by fun_prop) continuous_const]
  simp [realAverage, ne_of_gt hT]

theorem realAverage_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) {T : ℝ} (hT : 0 < T) : 0 ≤ realAverage f T := by
  have h := realAverage_mono continuous_const hf hn hT
  simpa [realAverage] using h

/-- Two conjugate coefficients of magnitude q force the mean square to be
at least 2q². This does not require other frequencies to be distinct. -/
theorem mean_square_lower_bound {f : ℝ → ℝ} (hf : Continuous f)
    {ω δ q E : ℝ} (hω : ω ≠ 0)
    (hcoef : Tendsto (average (fun x => (f x : ℂ) * wave (-ω) x))
      atTop (𝓝 ((q : ℂ) * wave (-δ) 1)))
    (hE : Tendsto (realAverage (fun x => (f x) ^ 2)) atTop (𝓝 E)) :
    2 * q ^ 2 ≤ E := by
  have hcross := (cosine_projection_mean hf hcoef).const_mul (4 * q)
  have hcos := (real_cosine_square_mean hω δ).const_mul (4 * q ^ 2)
  have h := (hE.sub hcross).add hcos
  have he (T : ℝ) : realAverage
      (fun x => (f x - 2 * q * Real.cos (ω * x - δ)) ^ 2) T =
      realAverage (fun x => (f x) ^ 2) T -
        4 * q * realAverage (fun x => f x * Real.cos (ω * x - δ)) T +
          4 * q ^ 2 * realAverage (fun x => (Real.cos (ω * x - δ)) ^ 2) T := by
    have hfcn : (fun x => (f x - 2 * q * Real.cos (ω * x - δ)) ^ 2) =
        fun x => ((f x) ^ 2 - (4 * q) * (f x * Real.cos (ω * x - δ))) +
          (4 * q ^ 2) * (Real.cos (ω * x - δ)) ^ 2 := by funext x; ring
    rw [hfcn, realAverage_add
      (f := fun x => (f x) ^ 2 - (4 * q) * (f x * Real.cos (ω * x - δ)))
      (g := fun x => (4 * q ^ 2) * (Real.cos (ω * x - δ)) ^ 2)
      (by fun_prop) (by fun_prop),
      realAverage_sub (f := fun x => (f x) ^ 2)
        (g := fun x => (4 * q) * (f x * Real.cos (ω * x - δ)))
        (by fun_prop) (by fun_prop), realAverage_const_mul, realAverage_const_mul]
  have hnonneg : 0 ≤ E - 4 * q * q + 4 * q ^ 2 * (1 / 2) := by
    apply ge_of_tendsto h
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← he T]
    exact realAverage_nonneg (by fun_prop) (fun x => sq_nonneg _) hT
  nlinarith

end DepthAspect.BohrMeanSquare
