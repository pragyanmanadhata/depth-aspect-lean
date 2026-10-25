import DepthAspect.OscillatoryMean

/-! Actual exponential coefficients of a cosine, including its phase and
the two possible resonances. No independence of frequencies is presumed. -/
open MeasureTheory Filter
open scoped Topology
namespace DepthAspect.CosineMeans
open OscillatoryMean

theorem wave_mul (ω η x : ℝ) : wave ω x * wave η x = wave (ω + η) x := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) (T : ℝ) :
    average (fun x => c * f x) T = c * average f T := by
  unfold OscillatoryMean.average
  rw [intervalIntegral.integral_const_mul]
  ring

theorem average_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (T : ℝ) :
    average (fun x => f x + g x) T = average f T + average g T := by
  unfold OscillatoryMean.average
  rw [intervalIntegral.integral_add (hf.intervalIntegrable 0 T) (hg.intervalIntegrable 0 T), mul_add]

theorem average_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (T : ℝ) :
    average (fun x => f x - g x) T = average f T - average g T := by
  unfold OscillatoryMean.average
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable 0 T) (hg.intervalIntegrable 0 T), mul_sub]

theorem cosine_waves (ω δ x : ℝ) :
    (Real.cos (ω * x - δ) : ℂ) =
      (wave (-δ) 1 * wave ω x + wave δ 1 * wave (-ω) x) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  congr 1
  congr 1 <;> unfold wave <;> rw [← Complex.exp_add] <;> congr 1 <;> push_cast <;> ring

theorem cosine_modulated_waves (ω η δ x : ℝ) :
    (Real.cos (ω * x - δ) : ℂ) * wave (-η) x =
      (wave (-δ) 1 / 2) * wave (ω - η) x +
        (wave δ 1 / 2) * wave (-ω - η) x := by
  rw [cosine_waves]
  have h₁ := wave_mul ω (-η) x
  have h₂ := wave_mul (-ω) (-η) x
  simp only [← sub_eq_add_neg] at h₁ h₂
  calc
    _ = (wave (-δ) 1 / 2) * (wave ω x * wave (-η) x) +
        (wave δ 1 / 2) * (wave (-ω) x * wave (-η) x) := by ring
    _ = _ := by rw [h₁, h₂]

/-- The actual finite-average coefficient of any real cosine. -/
theorem cosine_modulated_mean (ω η δ : ℝ) :
    Tendsto (average (fun x => (Real.cos (ω * x - δ) : ℂ) * wave (-η) x))
      atTop (𝓝 ((wave (-δ) 1 / 2) * (if ω = η then 1 else 0) +
        (wave δ 1 / 2) * (if -ω = η then 1 else 0))) := by
  have h := ((average_wave_tendsto (ω - η)).const_mul (wave (-δ) 1 / 2)).add
    ((average_wave_tendsto (-ω - η)).const_mul (wave δ 1 / 2))
  simp only [sub_eq_zero] at h
  apply h.congr'
  filter_upwards [] with T
  have he : (fun x => (Real.cos (ω * x - δ) : ℂ) * wave (-η) x) =
      fun x => (wave (-δ) 1 / 2) * wave (ω - η) x +
        (wave δ 1 / 2) * wave (-ω - η) x := funext (cosine_modulated_waves ω η δ)
  rw [he, average_add
    (f := fun x => (wave (-δ) 1 / 2) * wave (ω - η) x)
    (g := fun x => (wave δ 1 / 2) * wave (-ω - η) x)
    (continuous_const.mul (wave_continuous _))
    (continuous_const.mul (wave_continuous _)), average_const_mul, average_const_mul]

theorem cosine_mean_zero {ω : ℝ} (hω : ω ≠ 0) (δ : ℝ) :
    Tendsto (average (fun x => (Real.cos (ω * x - δ) : ℂ))) atTop (𝓝 0) := by
  simpa only [neg_zero, wave_zero, mul_one, if_neg hω, if_neg (neg_ne_zero.mpr hω),
    mul_zero, add_zero] using cosine_modulated_mean ω 0 δ

/-- At a positive matching frequency only the positive exponential remains. -/
theorem cosine_resonant_mean {ω : ℝ} (hω : 0 < ω) (δ : ℝ) :
    Tendsto (average (fun x => (Real.cos (ω * x - δ) : ℂ) * wave (-ω) x))
      atTop (𝓝 (wave (-δ) 1 / 2)) := by
  have hn : -ω ≠ ω := by linarith
  simpa [hn] using cosine_modulated_mean ω ω δ

/-- Linearity is applied to the literal product with the testing wave. -/
theorem cosine_difference_mean (c e ω₁ ω₂ η δ : ℝ) :
    Tendsto (average (fun x =>
      ((c * (Real.cos (ω₁ * x - δ) - e * Real.cos (ω₂ * x - δ)) : ℝ) : ℂ) *
        wave (-η) x)) atTop
      (𝓝 ((c : ℂ) * (((wave (-δ) 1 / 2) * (if ω₁ = η then 1 else 0) +
          (wave δ 1 / 2) * (if -ω₁ = η then 1 else 0)) -
        (e : ℂ) * ((wave (-δ) 1 / 2) * (if ω₂ = η then 1 else 0) +
          (wave δ 1 / 2) * (if -ω₂ = η then 1 else 0))))) := by
  have h := ((cosine_modulated_mean ω₁ η δ).sub
    ((cosine_modulated_mean ω₂ η δ).const_mul (e : ℂ))).const_mul (c : ℂ)
  apply h.congr'
  filter_upwards [] with T
  have he : (fun x =>
      ((c * (Real.cos (ω₁ * x - δ) - e * Real.cos (ω₂ * x - δ)) : ℝ) : ℂ) *
        wave (-η) x) = fun x => (c : ℂ) *
      ((Real.cos (ω₁ * x - δ) : ℂ) * wave (-η) x -
        (e : ℂ) * ((Real.cos (ω₂ * x - δ) : ℂ) * wave (-η) x)) := by
    funext x
    push_cast
    ring
  rw [he, average_const_mul,
    average_sub
      (f := fun x => (Real.cos (ω₁ * x - δ) : ℂ) * wave (-η) x)
      (g := fun x => (e : ℂ) * ((Real.cos (ω₂ * x - δ) : ℂ) * wave (-η) x))
      (by unfold wave; fun_prop) (by unfold wave; fun_prop),
    average_const_mul]

end DepthAspect.CosineMeans
