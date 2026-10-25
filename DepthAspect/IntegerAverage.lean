import DepthAspect.SurvivingTraces
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The integer average in equation (138)

All sets below are complete finite integer sets. The lower bound constructs
actual odd indices and actual surviving roots, rather than postulating a
positive density of roots. Evenness of the modulus is essential to the
construction of odd indices and is included explicitly.
-/
namespace DepthAspect.IntegerAverage

open SurvivingTraces
open scoped BigOperators

noncomputable def oddBlock (B : ℝ) : Finset ℤ :=
  (Finset.Ioc ⌊B⌋ ⌊2 * B⌋).filter Odd

@[simp] theorem mem_oddBlock (B : ℝ) (m : ℤ) :
    m ∈ oddBlock B ↔ B < (m : ℝ) ∧ (m : ℝ) ≤ 2 * B ∧ Odd m := by
  simp only [oddBlock, Finset.mem_filter, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]
  tauto

/-- The exact integer multiples that place `r²+qv` in `(B,2B]`. -/
noncomputable def multipleWindow (B : ℝ) (q r : ℤ) : Finset ℤ :=
  Finset.Ioc ⌊(B - (r : ℝ) ^ 2) / (q : ℝ)⌋
    ⌊(2 * B - (r : ℝ) ^ 2) / (q : ℝ)⌋

theorem mem_multipleWindow {B : ℝ} {q r v : ℤ} (hq : 0 < q) :
    v ∈ multipleWindow B q r ↔
      B < (r : ℝ) ^ 2 + (q : ℝ) * (v : ℝ) ∧
        (r : ℝ) ^ 2 + (q : ℝ) * (v : ℝ) ≤ 2 * B := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  simp only [multipleWindow, Finset.mem_Ioc, Int.floor_lt, Int.le_floor,
    div_lt_iff₀ hqR, le_div_iff₀ hqR]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- Uniform floor-error estimate for the number of multiples in an interval. -/
theorem multipleWindow_card {B : ℝ} {q r : ℤ} (hB : 0 ≤ B) (hq : 0 < q) :
    B / (q : ℝ) - 1 ≤ ((multipleWindow B q r).card : ℝ) ∧
      ((multipleWindow B q r).card : ℝ) ≤ B / (q : ℝ) + 1 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let l := (B - (r : ℝ) ^ 2) / (q : ℝ)
  let u := (2 * B - (r : ℝ) ^ 2) / (q : ℝ)
  have hlu : l ≤ u := by
    dsimp [l, u]
    exact div_le_div_of_nonneg_right (by linarith) hqR.le
  have hfl : (⌊l⌋ : ℤ) ≤ ⌊u⌋ := Int.floor_mono hlu
  have hc : ((multipleWindow B q r).card : ℝ) = (⌊u⌋ : ℤ) - (⌊l⌋ : ℤ) := by
    change ((Finset.Ioc (⌊l⌋ : ℤ) ⌊u⌋).card : ℝ) = (⌊u⌋ : ℤ) - (⌊l⌋ : ℤ)
    exact_mod_cast Int.card_Ioc_of_le (⌊l⌋ : ℤ) ⌊u⌋ hfl
  have hd : u - l = B / (q : ℝ) := by dsimp [l, u]; ring
  have hl₀ := Int.floor_le l
  have hl₁ := Int.lt_floor_add_one l
  have hu₀ := Int.floor_le u
  have hu₁ := Int.lt_floor_add_one u
  rw [hc]
  constructor <;> linarith

/-- A concrete collection of positive and negative odd integers in the
small square-root interval used in the lower bound. -/
noncomputable def smallOddRoots (B : ℝ) : Finset ℤ :=
  let R : ℕ := ⌊Real.sqrt B / 4⌋₊
  (Finset.Icc (-(R : ℤ)) ((R : ℤ) - 1)).image (fun i => 2 * i + 1)

theorem smallOddRoots_card (B : ℝ) :
    (smallOddRoots B).card = 2 * ⌊Real.sqrt B / 4⌋₊ := by
  unfold smallOddRoots
  rw [Finset.card_image_of_injective]
  · rw [Int.card_Icc]
    omega
  · intro a b h
    change 2 * a + 1 = 2 * b + 1 at h
    omega

theorem smallOddRoots_properties {B : ℝ} (hB : 64 ≤ B) {r : ℤ}
    (hr : r ∈ smallOddRoots B) : Odd r ∧ (r : ℝ) ^ 2 ≤ B / 4 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
  have hi' := Finset.mem_Icc.mp hi
  have hiL : -(⌊Real.sqrt B / 4⌋₊ : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi'.1
  have hiR : (i : ℝ) ≤ (⌊Real.sqrt B / 4⌋₊ : ℝ) - 1 := by exact_mod_cast hi'.2
  have hfloor := Nat.floor_le (show 0 ≤ Real.sqrt B / 4 by positivity)
  have hsqrt := Real.sq_sqrt (by linarith : 0 ≤ B)
  constructor
  · exact ⟨i, rfl⟩
  · push_cast
    have habs : |2 * (i : ℝ) + 1| ≤ Real.sqrt B / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hs := sq_le_sq₀ (abs_nonneg (2 * (i : ℝ) + 1)) (by positivity : 0 ≤ Real.sqrt B / 2)
    have hh := hs.mpr habs
    rw [sq_abs] at hh
    nlinarith

theorem smallOddRoots_card_lower {B : ℝ} (hB : 64 ≤ B) :
    Real.sqrt B / 4 ≤ ((smallOddRoots B).card : ℝ) := by
  rw [smallOddRoots_card]
  push_cast
  have hs : 8 ≤ Real.sqrt B := by
    exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 8) (by linarith : 0 ≤ B)).mpr
      (by norm_num; exact hB)
  have hf := Nat.lt_floor_add_one (Real.sqrt B / 4)
  nlinarith

/-- The construction `(r,v) ↦ (m=r²+qv,r)` counts actual surviving roots. -/
theorem lower_count {B : ℝ} {q : ℤ} (hB : 64 ≤ B) (hq : 0 < q)
    (hqEven : Even q) (hBq : 2 * (q : ℝ) ≤ B) :
    Real.sqrt B * B / (8 * (q : ℝ)) ≤
      ((∑ m ∈ oddBlock B, (survivingTraces q m).card : ℕ) : ℝ) := by
  let R := smallOddRoots B
  let V : ℤ → Finset ℤ := multipleWindow B q
  let D := R.sigma V
  let T := (oddBlock B).sigma (halvedTraces q)
  let f : (Σ _ : ℤ, ℤ) → (Σ _ : ℤ, ℤ) := fun p => ⟨p.1 ^ 2 + q * p.2, p.1⟩
  have hf : Function.Injective f := by
    rintro ⟨r, v⟩ ⟨s, w⟩ h
    have h1 : r ^ 2 + q * v = s ^ 2 + q * w := congrArg Sigma.fst h
    have h2 : r = s := congrArg (fun p : (Σ _ : ℤ, ℤ) => p.2) h
    subst s
    have hv : v = w := by
      apply mul_left_cancel₀ (ne_of_gt hq)
      linarith
    subst w
    rfl
  have hmem : ∀ p ∈ D, f p ∈ T := by
    rintro ⟨r, v⟩ hp
    obtain ⟨hr, hv⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hodd, hrsq⟩ := smallOddRoots_properties hB hr
    obtain ⟨hmlo, hmhi⟩ := (mem_multipleWindow hq).mp hv
    apply Finset.mem_sigma.mpr
    constructor
    · apply (mem_oddBlock B _).mpr
      refine ⟨?_, ?_, hodd.pow.add_even (hqEven.mul_right v)⟩
      · simpa only [f, Int.cast_add, Int.cast_pow, Int.cast_mul] using hmlo
      · simpa only [f, Int.cast_add, Int.cast_pow, Int.cast_mul] using hmhi
    · apply (mem_halvedTraces _ _ _).mpr
      constructor
      · have hlt : (r : ℝ) ^ 2 < (r : ℝ) ^ 2 + (q : ℝ) * v := by linarith
        exact_mod_cast hlt
      · refine ⟨v, ?_⟩
        ring
  have hc : D.card ≤ T.card := Finset.card_le_card_of_injOn f hmem hf.injOn
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hratio : 2 ≤ B / (q : ℝ) := (le_div_iff₀ hqR).mpr (by linarith)
  have hw : ∀ r ∈ R, B / (2 * (q : ℝ)) ≤ ((V r).card : ℝ) := by
    intro r _
    have h := (multipleWindow_card (by linarith : 0 ≤ B) hq (r := r)).1
    change B / (2 * (q : ℝ)) ≤ ((multipleWindow B q r).card : ℝ)
    have he : B / (2 * (q : ℝ)) = (B / (q : ℝ)) / 2 := by ring
    rw [he]
    linarith
  have hD : ((R.card : ℝ) * (B / (2 * (q : ℝ)))) ≤ (D.card : ℝ) := by
    dsimp [D]
    rw [Finset.card_sigma, Nat.cast_sum]
    calc
      _ = ∑ _r ∈ R, B / (2 * (q : ℝ)) := by simp
      _ ≤ _ := Finset.sum_le_sum hw
  have hR := smallOddRoots_card_lower hB
  have htotal : Real.sqrt B * B / (8 * (q : ℝ)) ≤ (T.card : ℝ) := by
    calc
      _ = (Real.sqrt B / 4) * (B / (2 * (q : ℝ))) := by ring
      _ ≤ (R.card : ℝ) * (B / (2 * (q : ℝ))) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
      _ ≤ (D.card : ℝ) := hD
      _ ≤ _ := by exact_mod_cast hc
  have heq : T.card = ∑ m ∈ oddBlock B, (survivingTraces q m).card := by
    dsimp [T]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro m _
    exact (survivingTraces_card_eq q m).symm
  rwa [heq] at htotal

/-- The lower half of equation (138), for a real endpoint `B`. -/
theorem lower_count_level {B N : ℝ} {q : ℤ} (hB : 64 ≤ B) (hq : 0 < q)
    (hqEven : Even q) (hBq : 2 * (q : ℝ) ≤ B) (hN : N = 16 * (q : ℝ)) :
    2 * B ^ (3 / 2 : ℝ) / N ≤
      ((∑ m ∈ oddBlock B, (survivingTraces q m).card : ℕ) : ℝ) := by
  have h := lower_count hB hq hqEven hBq
  have he : 2 * B ^ (3 / 2 : ℝ) / N = Real.sqrt B * B / (8 * (q : ℝ)) := by
    rw [hN, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith : 0 < B), Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring
  rwa [he]

/-- The upper bound counts every integer root in the square-root interval,
and every multiple in its corresponding interval. -/
theorem upper_count {B : ℝ} {q : ℤ} (hB : 1 ≤ B) (hq : 0 < q)
    (hBq : 2 * (q : ℝ) ≤ B) :
    ((∑ m ∈ oddBlock B, (survivingTraces q m).card : ℕ) : ℝ) ≤
      6 * Real.sqrt B * B / (q : ℝ) := by
  let R : ℕ := ⌊Real.sqrt (2 * B)⌋₊
  let S := Finset.Icc (-(R : ℤ)) (R : ℤ)
  let V : ℤ → Finset ℤ := multipleWindow B q
  let D := S.sigma V
  let T := (oddBlock B).sigma (halvedTraces q)
  let f : (Σ _ : ℤ, ℤ) → (Σ _ : ℤ, ℤ) := fun p => ⟨p.2, (p.1 - p.2 ^ 2) / q⟩
  have hmem : ∀ p ∈ T, f p ∈ D := by
    rintro ⟨m, r⟩ hp
    obtain ⟨hm, hr⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hmlo, hmhi, _⟩ := (mem_oddBlock B m).mp hm
    obtain ⟨hrsq, hrdiv⟩ := (mem_halvedTraces q m r).mp hr
    have hquot := Int.ediv_mul_cancel hrdiv
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr (PrimePairBound.radius_bound hrsq hmhi)
    · apply (mem_multipleWindow hq).mpr
      have heq : (r : ℝ) ^ 2 + (q : ℝ) * (((m - r ^ 2) / q : ℤ) : ℝ) = (m : ℝ) := by
        have hh : ((m - r ^ 2) / q : ℤ) * q = m - r ^ 2 := hquot
        have hhR : (((m - r ^ 2) / q : ℤ) : ℝ) * (q : ℝ) = (m : ℝ) - (r : ℝ) ^ 2 := by
          exact_mod_cast hh
        nlinarith
      rw [heq]
      exact ⟨hmlo, hmhi⟩
  have hf : Set.InjOn f T := by
    rintro ⟨m, r⟩ hp ⟨n, s⟩ ht he
    have hr : r = s := congrArg Sigma.fst he
    have hv : (m - r ^ 2) / q = (n - s ^ 2) / q :=
      congrArg (fun p : (Σ _ : ℤ, ℤ) => p.2) he
    have hm := Int.ediv_mul_cancel
      ((mem_halvedTraces _ _ _).mp (Finset.mem_sigma.mp hp).2).2
    have hn := Int.ediv_mul_cancel
      ((mem_halvedTraces _ _ _).mp (Finset.mem_sigma.mp ht).2).2
    subst s
    rw [hv] at hm
    have hmn : m = n := by linarith
    subst n
    rfl
  have hc : T.card ≤ D.card := Finset.card_le_card_of_injOn f hmem hf
  have hD : (D.card : ℝ) ≤ (S.card : ℝ) * (B / (q : ℝ) + 1) := by
    dsimp [D]
    rw [Finset.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _r ∈ S, (B / (q : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro r _
        exact (multipleWindow_card (by linarith : 0 ≤ B) hq (r := r)).2
      _ = _ := by simp [mul_add]
  have hcard : S.card = 2 * R + 1 := by
    dsimp [S]
    rw [Int.card_Icc]
    omega
  have hR : (R : ℝ) ≤ Real.sqrt (2 * B) := Nat.floor_le (Real.sqrt_nonneg _)
  have hs1 : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hsB := Real.sq_sqrt (by linarith : 0 ≤ B)
  have hs2B := Real.sq_sqrt (by linarith : 0 ≤ 2 * B)
  have hsqrt : Real.sqrt (2 * B) ≤ (3 / 2 : ℝ) * Real.sqrt B := by
    nlinarith [Real.sqrt_nonneg (2 * B), Real.sqrt_nonneg B]
  have hS : (S.card : ℝ) ≤ 4 * Real.sqrt B := by
    rw [hcard]
    push_cast
    linarith
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hratio : 2 ≤ B / (q : ℝ) := (le_div_iff₀ hqR).mpr (by linarith)
  have hquot : B / (q : ℝ) + 1 ≤ 3 * B / (2 * (q : ℝ)) := by
    have he : 3 * B / (2 * (q : ℝ)) = (3 / 2 : ℝ) * (B / (q : ℝ)) := by ring
    rw [he]
    linarith
  have htotal : (T.card : ℝ) ≤ 6 * Real.sqrt B * B / (q : ℝ) := by
    calc
      _ ≤ (D.card : ℝ) := by exact_mod_cast hc
      _ ≤ (S.card : ℝ) * (B / (q : ℝ) + 1) := hD
      _ ≤ (4 * Real.sqrt B) * (3 * B / (2 * (q : ℝ))) :=
        mul_le_mul hS hquot (by positivity) (by positivity)
      _ = _ := by ring
  have heq : T.card = ∑ m ∈ oddBlock B, (survivingTraces q m).card := by
    dsimp [T]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro m _
    exact (survivingTraces_card_eq q m).symm
  rwa [heq] at htotal

/-- The sharper constant 96 stated in the proof of (138). -/
theorem upper_count_level {B N : ℝ} {q : ℤ} (hB : 1 ≤ B) (hq : 0 < q)
    (hBq : 2 * (q : ℝ) ≤ B) (hN : N = 16 * (q : ℝ)) :
    ((∑ m ∈ oddBlock B, (survivingTraces q m).card : ℕ) : ℝ) ≤
      96 * B ^ (3 / 2 : ℝ) / N := by
  have h := upper_count hB hq hBq
  have he : 96 * B ^ (3 / 2 : ℝ) / N = 6 * Real.sqrt B * B / (q : ℝ) := by
    rw [hN, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by linarith : 0 < B), Real.rpow_one, ← Real.sqrt_eq_rpow]
    ring
  rwa [he]

/-- Both sides of equation (138), over the complete set of odd integers in
the displayed interval and with no primality restriction. -/
theorem integer_average {B N : ℝ} {q : ℤ} (hB : 64 ≤ B) (hq : 0 < q)
    (hqEven : Even q) (hBq : 2 * (q : ℝ) ≤ B) (hN : N = 16 * (q : ℝ)) :
    2 * B ^ (3 / 2 : ℝ) / N ≤
      ((∑ m ∈ oddBlock B, (survivingTraces q m).card : ℕ) : ℝ) ∧
    ((∑ m ∈ oddBlock B, (survivingTraces q m).card : ℕ) : ℝ) ≤
      128 * B ^ (3 / 2 : ℝ) / N := by
  refine ⟨lower_count_level hB hq hqEven hBq hN, ?_⟩
  have hb := upper_count_level (by linarith : 1 ≤ B) hq hBq hN
  have hN0 : 0 < N := by rw [hN]; positivity
  exact hb.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (96 : ℝ) ≤ 128) (by positivity)) hN0.le)

/-- Equation (138) specialized to the paper's actual dyadic level. The
positivity and evenness of q=N/16 are derived from n≥8. -/
theorem integer_average_dyadic (n : ℕ) (hn : 8 ≤ n) {B : ℝ}
    (hB : max (2 * (2 : ℝ) ^ (n - 4)) 64 ≤ B) :
    2 * B ^ (3 / 2 : ℝ) / (2 : ℝ) ^ n ≤
      ((∑ m ∈ oddBlock B, (survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℕ) : ℝ) ∧
    ((∑ m ∈ oddBlock B, (survivingTraces ((2 : ℤ) ^ (n - 4)) m).card : ℕ) : ℝ) ≤
      128 * B ^ (3 / 2 : ℝ) / (2 : ℝ) ^ n := by
  have hq : Even ((2 : ℤ) ^ (n - 4)) :=
    even_iff_two_dvd.mpr (dvd_pow_self (2 : ℤ) (by omega))
  have hN : (2 : ℝ) ^ n = 16 * (((2 : ℤ) ^ (n - 4) : ℤ) : ℝ) := by
    push_cast
    calc
      (2 : ℝ) ^ n = 2 ^ ((n - 4) + 4) := by congr 1; omega
      _ = 16 * (2 : ℝ) ^ (n - 4) := by rw [pow_add]; norm_num; ring
  apply integer_average ((le_max_right _ _).trans hB) (by positivity) hq _ hN
  simpa only [Int.cast_pow, Int.cast_ofNat] using (le_max_left _ _).trans hB

end DepthAspect.IntegerAverage
