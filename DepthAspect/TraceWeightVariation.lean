import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.Ext
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic.NthRewrite

/-!
# The actual endpoint variation in (111)

The angle is monotone, including at a zero-discriminant endpoint. Its
actual derivative is integrable and its integral is controlled by the
angle's range. No variation or endpoint integrability estimate is an input.
-/
namespace DepthAspect.TraceWeightVariation

open MeasureTheory Set
open scoped Topology SchwartzMap

/-- An antitone real angle has an integrable derivative, and its total
integrated derivative is at most its endpoint displacement. -/
theorem antitone_derivative_variation {q : ℝ → ℝ} {A B : ℝ} (hAB : A ≤ B)
    (hq : AntitoneOn q (Icc A B)) :
    IntervalIntegrable (deriv q) volume A B ∧
      (∫ u in A..B, ‖deriv q u‖) ≤ q A - q B := by
  have hm : MonotoneOn (fun u => -q u) (Set.uIcc A B) := by
    simpa only [Set.uIcc_of_le hAB] using hq.neg
  have hi := hm.intervalIntegrable_deriv
  have hqi : IntervalIntegrable (deriv q) volume A B := by
    have hneg : -(deriv (fun u => -q u)) = deriv q := by
      funext u
      change -deriv (fun x => -q x) u = deriv q u
      rw [deriv.fun_neg, neg_neg]
    have hi' := hi.neg
    rwa [hneg] at hi'
  refine ⟨hqi, ?_⟩
  have hend : q B ≤ q A := hq ⟨le_rfl, hAB⟩ ⟨hAB, le_rfl⟩ hAB
  have hb := hm.intervalIntegral_deriv_mem_uIcc
  rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ -q B - -q A)] at hb
  have heq : (∫ u in A..B, ‖deriv q u‖) =
      ∫ u in A..B, deriv (fun x => -q x) u := by
    apply intervalIntegral.integral_congr_uIoo
    rw [Set.uIoo_of_le hAB]
    intro u hu
    have hd : deriv q u ≤ 0 := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
      exact hq.derivWithin_nonpos
    change ‖deriv q u‖ = deriv (fun x => -q x) u
    rw [Real.norm_eq_abs, abs_of_nonpos hd, deriv.fun_neg]
  rw [heq]
  linarith [hb.2]

/-- The angle occurring at either parity of depth, after incorporating
its denominator into the real parameter c. -/
noncomputable def traceAngle (c u : ℝ) : ℝ := Real.arcsin (c / Real.sqrt u)

theorem traceAngle_antitone {c A B : ℝ} (hc : 0 ≤ c) (hA : 0 < A) :
    AntitoneOn (traceAngle c) (Icc A B) := by
  intro u hu v hv huv
  apply Real.monotone_arcsin
  exact div_le_div_of_nonneg_left hc (Real.sqrt_pos.mpr (hA.trans_le hu.1))
    (Real.sqrt_le_sqrt huv)

/-- The singular derivative at the lower discriminant endpoint is
integrable, with the exact uniform angular bound π/2. -/
theorem traceAngle_variation {c A B : ℝ} (hc : 0 ≤ c) (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (deriv (traceAngle c)) volume A B ∧
      (∫ u in A..B, ‖deriv (traceAngle c) u‖) ≤ Real.pi / 2 := by
  obtain ⟨hi, hb⟩ := antitone_derivative_variation hAB (traceAngle_antitone hc hA)
  refine ⟨hi, hb.trans ?_⟩
  have hupper := Real.arcsin_le_pi_div_two (c / Real.sqrt A)
  have hlower : 0 ≤ Real.arcsin (c / Real.sqrt B) :=
    Real.arcsin_nonneg.mpr (div_nonneg hc (Real.sqrt_nonneg _))
  dsimp [traceAngle]
  linarith

/-- Composition with cosine costs at most its frequency in integrated
variation. Differentiability is needed only in the open interval. -/
theorem cosine_variation {q : ℝ → ℝ} {A B m V : ℝ} (hAB : A ≤ B)
    (hm : 0 ≤ m) (hq : ∀ u ∈ Ioo A B, DifferentiableAt ℝ q u)
    (hi : IntervalIntegrable (deriv q) volume A B)
    (hV : (∫ u in A..B, ‖deriv q u‖) ≤ V) :
    IntervalIntegrable (deriv (fun u => Real.cos (m * q u))) volume A B ∧
      (∫ u in A..B, ‖deriv (fun u => Real.cos (m * q u)) u‖) ≤ m * V := by
  let f : ℝ → ℝ := fun u => Real.cos (m * q u)
  have hpoint (u : ℝ) (hu : u ∈ Ioo A B) : ‖deriv f u‖ ≤ m * ‖deriv q u‖ := by
    have hd := ((hq u hu).hasDerivAt.const_mul m).cos
    rw [hd.deriv]
    simp only [norm_mul, norm_neg, Real.norm_eq_abs m, abs_of_nonneg hm]
    have hsin : ‖Real.sin (m * q u)‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (m * q u)
    calc
      _ ≤ 1 * (m * ‖deriv q u‖) :=
        mul_le_mul_of_nonneg_right hsin (mul_nonneg hm (norm_nonneg _))
      _ = _ := one_mul _
  have hmajor : IntervalIntegrable (fun u => m * ‖deriv q u‖) volume A B :=
    hi.norm.const_mul m
  have hfi : IntervalIntegrable (deriv f) volume A B := by
    apply hmajor.mono_fun' (aestronglyMeasurable_deriv _ _)
    rw [Set.uIoc_of_le hAB, ← restrict_Ioo_eq_restrict_Ioc]
    exact (ae_restrict_mem measurableSet_Ioo).mono (fun u hu => hpoint u hu)
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ u in A..B, m * ‖deriv q u‖ :=
      intervalIntegral.integral_mono_on_of_le_Ioo hAB hfi.norm hmajor hpoint
    _ = m * ∫ u in A..B, ‖deriv q u‖ := intervalIntegral.integral_const_mul _ _
    _ ≤ m * V := mul_le_mul_of_nonneg_left hV hm

theorem traceAngle_differentiableAt {c u : ℝ} (hc : 0 ≤ c) (hu : c ^ 2 < u) :
    DifferentiableAt ℝ (traceAngle c) u := by
  have hu0 : 0 < u := (sq_nonneg c).trans_lt hu
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hratio : c / Real.sqrt u < 1 :=
    (div_lt_one hsqrt).mpr ((Real.lt_sqrt hc).mpr hu)
  have hratio0 : 0 ≤ c / Real.sqrt u := div_nonneg hc hsqrt.le
  exact (Real.differentiableAt_arcsin.mpr
    ⟨by linarith, hratio.ne⟩).comp u
      ((differentiableAt_const c).div (Real.hasDerivAt_sqrt hu0.ne').differentiableAt hsqrt.ne')

noncomputable def cosineTrace (m c u : ℝ) : ℝ := Real.cos (m * traceAngle c u)

theorem cosineTrace_abs (m c : ℝ) : cosineTrace m c = cosineTrace m |c| := by
  funext u
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
  · simp only [cosineTrace, traceAngle, abs_of_neg (lt_of_not_ge hc), neg_div,
      Real.arcsin_neg, mul_neg, Real.cos_neg]

/-- Actual cosine factor variation, uniform in the trace parameter and
valid at a zero-discriminant endpoint A=c². -/
theorem cosineTrace_variation {m c A B : ℝ} (hm : 0 ≤ m)
    (hA : 0 < A) (hAB : A ≤ B) (hcA : c ^ 2 ≤ A) :
    IntervalIntegrable (deriv (cosineTrace m c)) volume A B ∧
      (∫ u in A..B, ‖deriv (cosineTrace m c) u‖) ≤ m * (Real.pi / 2) := by
  rw [cosineTrace_abs m c]
  obtain ⟨hi, hv⟩ := traceAngle_variation (abs_nonneg c) hA hAB
  apply cosine_variation hAB hm ?_ hi hv
  intro u hu
  apply traceAngle_differentiableAt (abs_nonneg c)
  simpa only [sq_abs] using hcA.trans_lt hu.1

/-- A bounded smooth amplitude times a bounded real oscillating factor.
All derivatives and integrals in the conclusion are literal. -/
theorem smul_weight_variation {f : ℝ → ℂ} {g : ℝ → ℝ} {A B H₀ H₁ V : ℝ}
    (hAB : A ≤ B) (hH₀ : 0 ≤ H₀) (hH₁ : 0 ≤ H₁)
    (hf : ∀ u ∈ Ioo A B, DifferentiableAt ℝ f u)
    (hg : ∀ u ∈ Ioo A B, DifferentiableAt ℝ g u)
    (hfBound : ∀ u ∈ Icc A B, ‖f u‖ ≤ H₀)
    (hdfBound : ∀ u ∈ Ioo A B, ‖deriv f u‖ ≤ H₁)
    (hgBound : ∀ u ∈ Icc A B, ‖g u‖ ≤ 1)
    (hgi : IntervalIntegrable (deriv g) volume A B)
    (hV : (∫ u in A..B, ‖deriv g u‖) ≤ V) :
    IntervalIntegrable (deriv (fun u => g u • f u)) volume A B ∧
      (∀ u ∈ Icc A B, ‖g u • f u‖ ≤ H₀) ∧
      (∫ u in A..B, ‖deriv (fun u => g u • f u) u‖) ≤
        H₀ * V + (B - A) * H₁ := by
  let w : ℝ → ℂ := fun u => g u • f u
  have hpoint (u : ℝ) (hu : u ∈ Ioo A B) :
      ‖deriv w u‖ ≤ H₀ * ‖deriv g u‖ + H₁ := by
    change ‖deriv (fun x => g x • f x) u‖ ≤ H₀ * ‖deriv g u‖ + H₁
    rw [deriv_fun_smul (hg u hu) (hf u hu)]
    calc
      _ ≤ ‖g u • deriv f u‖ + ‖deriv g u • f u‖ := norm_add_le _ _
      _ = ‖g u‖ * ‖deriv f u‖ + ‖deriv g u‖ * ‖f u‖ := by rw [norm_smul, norm_smul]
      _ ≤ 1 * H₁ + ‖deriv g u‖ * H₀ := by
        exact add_le_add
          (mul_le_mul (hgBound u ⟨hu.1.le, hu.2.le⟩) (hdfBound u hu) (norm_nonneg _) zero_le_one)
          (mul_le_mul_of_nonneg_left (hfBound u ⟨hu.1.le, hu.2.le⟩) (norm_nonneg _))
      _ = _ := by ring
  have hmajor : IntervalIntegrable (fun u => H₀ * ‖deriv g u‖ + H₁) volume A B :=
    (hgi.norm.const_mul H₀).add intervalIntegrable_const
  have hwi : IntervalIntegrable (deriv w) volume A B := by
    apply hmajor.mono_fun' (aestronglyMeasurable_deriv _ _)
    rw [Set.uIoc_of_le hAB, ← restrict_Ioo_eq_restrict_Ioc]
    exact (ae_restrict_mem measurableSet_Ioo).mono (fun u hu => hpoint u hu)
  refine ⟨hwi, ?_, ?_⟩
  · intro u hu
    rw [norm_smul]
    exact (mul_le_mul (hgBound u hu) (hfBound u hu) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul H₀)
  · calc
      _ ≤ ∫ u in A..B, (H₀ * ‖deriv g u‖ + H₁) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hAB hwi.norm hmajor hpoint
      _ = H₀ * (∫ u in A..B, ‖deriv g u‖) + (B - A) * H₁ := by
        rw [intervalIntegral.integral_add (hgi.norm.const_mul H₀) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hV hH₀) le_rfl

noncomputable def traceAmplitude (L : ℝ) (h : 𝓢(ℝ, ℂ)) (u : ℝ) : ℂ :=
  u ^ (-(1 / 2 : ℝ)) • h (Real.log u / L)

theorem traceAmplitude_hasDerivAt (L : ℝ) (h : 𝓢(ℝ, ℂ)) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (traceAmplitude L h)
      (u ^ (-(1 / 2 : ℝ)) • ((u⁻¹ / L) • deriv h (Real.log u / L)) +
        (-(1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) • h (Real.log u / L)) u := by
  have hp := Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hu.ne')
  have hh : HasDerivAt (fun x : ℝ => h (Real.log x / L))
      ((u⁻¹ / L) • deriv h (Real.log u / L)) u :=
    (h.hasDerivAt _).scomp u ((Real.hasDerivAt_log hu.ne').div_const L)
  have hd := hp.smul hh
  convert hd using 1 <;> first
    | exact AddCommGroup.ext rfl
    | rfl
    | norm_num

/-- Actual amplitude bound, with no t-dependent constant. -/
theorem traceAmplitude_norm_le (L : ℝ) (h : 𝓢(ℝ, ℂ)) {X u H : ℝ}
    (hX : 0 < X) (hu : X ≤ u) (hH : 0 ≤ H) (hh : ∀ x, ‖h x‖ ≤ H) :
    ‖traceAmplitude L h u‖ ≤ H * X ^ (-(1 / 2 : ℝ)) := by
  have hu0 : 0 < u := hX.trans_le hu
  rw [traceAmplitude, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (hX.le.trans hu) _)]
  calc
    _ ≤ u ^ (-(1 / 2 : ℝ)) * H :=
      mul_le_mul_of_nonneg_left (hh _) (by positivity)
    _ ≤ X ^ (-(1 / 2 : ℝ)) * H :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hX hu (by norm_num)) hH
    _ = _ := mul_comm _ _

/-- Differentiating the nonoscillating amplitude gives a uniform bound on
any subinterval of [X,2X]. -/
theorem traceAmplitude_deriv_norm_le (h : 𝓢(ℝ, ℂ)) {L X u H H' : ℝ}
    (hL : 1 ≤ L) (hX : 0 < X) (hu : X ≤ u) (hH : 0 ≤ H) (hH' : 0 ≤ H')
    (hh : ∀ x, ‖h x‖ ≤ H) (hh' : ∀ x, ‖deriv h x‖ ≤ H') :
    ‖deriv (traceAmplitude L h) u‖ ≤ (H / 2 + H') * X ^ (-(3 / 2 : ℝ)) := by
  have hu0 := hX.trans_le hu
  have hL0 : 0 < L := by linarith
  have hpow : u ^ (-(1 / 2 : ℝ)) * u⁻¹ = u ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hu0]
    norm_num
  have hi : u⁻¹ / L ≤ u⁻¹ := (div_le_iff₀ hL0).mpr
    (by nlinarith [inv_nonneg.mpr hu0.le])
  have hb : ‖deriv (traceAmplitude L h) u‖ ≤
      u ^ (-(1 / 2 : ℝ)) * ((u⁻¹ / L) * H') +
        ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) * H := by
    rw [(traceAmplitude_hasDerivAt L h hu0).deriv]
    calc
      _ ≤ ‖u ^ (-(1 / 2 : ℝ)) • ((u⁻¹ / L) • deriv h (Real.log u / L))‖ +
          ‖(-(1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) • h (Real.log u / L)‖ := norm_add_le _ _
      _ = u ^ (-(1 / 2 : ℝ)) * ((u⁻¹ / L) * ‖deriv h (Real.log u / L)‖) +
          ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) * ‖h (Real.log u / L)‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (by positivity : 0 ≤ u ^ (-(1 / 2 : ℝ))),
          abs_of_nonneg (by positivity : 0 ≤ u⁻¹ / L),
          abs_of_nonneg (by positivity : 0 ≤ u ^ (-(3 / 2 : ℝ)))]
        norm_num
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hh' _) (by positivity)) (by positivity))
        (mul_le_mul_of_nonneg_left (hh _) (by positivity))
  calc
    _ ≤ u ^ (-(1 / 2 : ℝ)) * ((u⁻¹ / L) * H') +
        ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) * H := hb
    _ ≤ u ^ (-(1 / 2 : ℝ)) * (u⁻¹ * H') +
        ((1 / 2 : ℝ) * u ^ (-(3 / 2 : ℝ))) * H :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hi hH') (by positivity)) le_rfl
    _ = (H / 2 + H') * u ^ (-(3 / 2 : ℝ)) := by rw [← mul_assoc, hpow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hX hu (by norm_num)) (by positivity)

/-- The literal weight (110), with c=t/2 or c=t/(2√2). -/
noncomputable def traceWeight (m c L : ℝ) (h : 𝓢(ℝ, ℂ)) (u : ℝ) : ℂ :=
  cosineTrace m c u • traceAmplitude L h u

theorem cosineTrace_differentiableAt {m c u : ℝ} (hu : c ^ 2 < u) :
    DifferentiableAt ℝ (cosineTrace m c) u := by
  rw [cosineTrace_abs m c]
  exact ((traceAngle_differentiableAt (abs_nonneg c)
    (by simpa only [sq_abs] using hu)).const_mul m).cos

theorem traceWeight_continuousOn (m c L : ℝ) (h : 𝓢(ℝ, ℂ)) {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (traceWeight m c L h) (Icc A B) := by
  intro u hu
  have hu0 := hA.trans_le hu.1
  have hr : ContinuousAt (fun x : ℝ => c / Real.sqrt x) u :=
    continuousAt_const.div Real.continuous_sqrt.continuousAt
      (Real.sqrt_pos.mpr hu0).ne'
  have ha : ContinuousAt (traceAngle c) u :=
    Real.continuous_arcsin.continuousAt.comp hr
  have hc : ContinuousAt (cosineTrace m c) u :=
    Real.continuous_cos.continuousAt.comp (ha.const_mul m)
  exact (hc.smul (traceAmplitude_hasDerivAt L h hu0).continuousAt).continuousWithinAt

theorem traceWeight_differentiableAt (m c L : ℝ) (h : 𝓢(ℝ, ℂ)) {u : ℝ}
    (hu : c ^ 2 < u) : DifferentiableAt ℝ (traceWeight m c L h) u :=
  (cosineTrace_differentiableAt hu).smul
    (traceAmplitude_hasDerivAt L h ((sq_nonneg c).trans_lt hu)).differentiableAt

/-- Equation (111), uniformly on every truncated dyadic interval and even
when A=c². This proves integrability of the actual endpoint-singular
derivative and the actual supremum-plus-variation bound. -/
theorem traceWeight_variation (h : 𝓢(ℝ, ℂ)) {m c L X A B H H' : ℝ}
    (hm : 0 ≤ m) (hL : 1 ≤ L) (hX : 0 < X) (hXA : X ≤ A)
    (hAB : A ≤ B) (hB : B ≤ 2 * X) (hcA : c ^ 2 ≤ A)
    (hH : 0 ≤ H) (hH' : 0 ≤ H') (hh : ∀ x, ‖h x‖ ≤ H)
    (hh' : ∀ x, ‖deriv h x‖ ≤ H') :
    IntegrableOn (deriv (traceWeight m c L h)) (Icc A B) ∧
      (∀ u ∈ Icc A B, ‖traceWeight m c L h u‖ ≤ H * X ^ (-(1 / 2 : ℝ))) ∧
      H * X ^ (-(1 / 2 : ℝ)) +
        (∫ v in A..B, ‖deriv (traceWeight m c L h) v‖) ≤
          (2 + m * (Real.pi / 2)) * (H + H') * X ^ (-(1 / 2 : ℝ)) := by
  have hA := hX.trans_le hXA
  obtain ⟨hgi, hgv⟩ := cosineTrace_variation hm hA hAB hcA
  obtain ⟨hwi, hwb, hwv⟩ := smul_weight_variation
    (f := traceAmplitude L h) (g := cosineTrace m c) hAB
    (show 0 ≤ H * X ^ (-(1 / 2 : ℝ)) by positivity)
    (show 0 ≤ (H / 2 + H') * X ^ (-(3 / 2 : ℝ)) by positivity)
    (fun u hu => (traceAmplitude_hasDerivAt L h (hA.trans hu.1)).differentiableAt)
    (fun u hu => cosineTrace_differentiableAt (hcA.trans_lt hu.1))
    (fun u hu => traceAmplitude_norm_le L h hX (hXA.trans hu.1) hH hh)
    (fun u hu => traceAmplitude_deriv_norm_le h hL hX (hXA.trans hu.1.le) hH hH' hh hh')
    (fun u _ => by simpa only [cosineTrace, Real.norm_eq_abs] using
      Real.abs_cos_le_one (m * traceAngle c u)) hgi hgv
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mp hwi, hwb, ?_⟩
  have hlen : B - A ≤ X := by linarith
  have hpow : X * X ^ (-(3 / 2 : ℝ)) = X ^ (-(1 / 2 : ℝ)) := by
    nth_rw 1 [← Real.rpow_one X]
    rw [← Real.rpow_add hX]
    norm_num
  have hV : (∫ v in A..B, ‖deriv (traceWeight m c L h) v‖) ≤
      (H * (m * (Real.pi / 2)) + (H / 2 + H')) * X ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ (H * X ^ (-(1 / 2 : ℝ))) * (m * (Real.pi / 2)) +
          (B - A) * ((H / 2 + H') * X ^ (-(3 / 2 : ℝ))) := hwv
      _ ≤ (H * X ^ (-(1 / 2 : ℝ))) * (m * (Real.pi / 2)) +
          X * ((H / 2 + H') * X ^ (-(3 / 2 : ℝ))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hlen (by positivity))
      _ = _ := by rw [show X * ((H / 2 + H') * X ^ (-(3 / 2 : ℝ))) =
          (H / 2 + H') * (X * X ^ (-(3 / 2 : ℝ))) by ring, hpow]; ring
  have hcoef : H + (H * (m * (Real.pi / 2)) + (H / 2 + H')) ≤
      (2 + m * (Real.pi / 2)) * (H + H') := by
    have hpi := Real.pi_pos
    nlinarith [mul_nonneg hm (mul_nonneg hpi.le hH')]
  have hc := mul_le_mul_of_nonneg_right hcoef
    (Real.rpow_nonneg hX.le (-(1 / 2 : ℝ)))
  nlinarith

/-- The actual fixed Schwartz seminorm combination used in the bound. -/
noncomputable def schwartzSize (h : 𝓢(ℝ, ℂ)) : ℝ :=
  ‖h.toBoundedContinuousFunction‖ +
    ‖(SchwartzMap.derivCLM ℝ ℂ h).toBoundedContinuousFunction‖

theorem schwartz_traceWeight_variation (h : 𝓢(ℝ, ℂ)) {m c L X A B : ℝ}
    (hm : 0 ≤ m) (hL : 1 ≤ L) (hX : 0 < X) (hXA : X ≤ A)
    (hAB : A ≤ B) (hB : B ≤ 2 * X) (hcA : c ^ 2 ≤ A) :
    IntegrableOn (deriv (traceWeight m c L h)) (Icc A B) ∧
      (∀ u ∈ Icc A B, ‖traceWeight m c L h u‖ ≤
        ‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ))) ∧
      ‖h.toBoundedContinuousFunction‖ * X ^ (-(1 / 2 : ℝ)) +
        (∫ v in A..B, ‖deriv (traceWeight m c L h) v‖) ≤
          (2 + m * (Real.pi / 2)) * schwartzSize h * X ^ (-(1 / 2 : ℝ)) := by
  apply traceWeight_variation h hm hL hX hXA hAB hB hcA
    (norm_nonneg _) (norm_nonneg _) (fun x => h.toBoundedContinuousFunction.norm_coe_le_norm x)
  intro x
  simpa only [SchwartzMap.toBoundedContinuousFunction_apply, SchwartzMap.derivCLM_apply] using
    (SchwartzMap.derivCLM ℝ ℂ h).toBoundedContinuousFunction.norm_coe_le_norm x

end DepthAspect.TraceWeightVariation
