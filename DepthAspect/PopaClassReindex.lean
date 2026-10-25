import DepthAspect.PopaLiteralFunctions

/-!
# Substituting the primitive class decomposition into the literal Popa sum

The only class-number premise is the general identity H(D)=sum h0(D/u²).
The finite change of variables u=v*w and Möbius inversion are proved here.
In particular, no equality involving a dyadic Xi or K is an input.
-/
namespace DepthAspect.PopaLiteralFunctions

open scoped BigOperators
open TraceBounds

theorem squareContents_of_dvd {D : ℤ} (hD : D ≠ 0) {u v : ℕ}
    (hu : u ∈ positiveSquareContents D) (hv : 0 < v) (hvu : v ∣ u) :
    v ∈ positiveSquareContents D := by
  apply (mem_positiveSquareContents D hD v).mpr
  refine ⟨hv, ?_⟩
  exact dvd_trans (pow_dvd_pow_of_dvd (by exact_mod_cast hvu) 2)
    ((mem_positiveSquareContents D hD u).mp hu).2

theorem squareContents_quotient (D : ℤ) (hD : D < 0) (v : ℕ) (hv : 0 < v)
    (hdiv : (v : ℤ) ^ 2 ∣ D) :
    positiveSquareContents (D / (v : ℤ) ^ 2) =
      (positiveSquareContents D).filter (fun w => v * w ∈ positiveSquareContents D) := by
  ext w
  have hquot := negative_discriminant_quotient D hD v hv hdiv
  rw [mem_positiveSquareContents _ hquot.ne w, Finset.mem_filter,
    mem_positiveSquareContents D hD.ne w,
    mem_positiveSquareContents D hD.ne (v * w)]
  have hmul : ((v * w : ℕ) : ℤ) ^ 2 = (v : ℤ) ^ 2 * (w : ℤ) ^ 2 := by
    push_cast
    ring
  rw [hmul, Int.dvd_div_iff_mul_dvd hdiv]
  constructor
  · rintro ⟨hw, hd⟩
    refine ⟨⟨hw, ?_⟩, Nat.mul_pos hv hw, hd⟩
    exact dvd_trans (dvd_mul_left ((w : ℤ) ^ 2) ((v : ℤ) ^ 2)) hd
  · rintro ⟨⟨hw, _⟩, _, hd⟩
    exact ⟨hw, hd⟩

theorem sum_multiply_squareContents (D : ℤ) (hD : D < 0)
    (v : ℕ) (hv : 0 < v) (F : ℕ → ℝ) :
    (∑ w ∈ (positiveSquareContents D).filter (fun w => v * w ∈ positiveSquareContents D),
      F (v * w)) =
    ∑ u ∈ (positiveSquareContents D).filter (fun u => v ∣ u), F u := by
  classical
  apply Finset.sum_bij (fun w _ => v * w)
  · intro w hw
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).2, dvd_mul_right v w⟩
  · intro w hw z hz heq
    exact Nat.eq_of_mul_eq_mul_left hv heq
  · intro u hu
    obtain ⟨hu, hvu⟩ := Finset.mem_filter.mp hu
    obtain ⟨w, rfl⟩ := hvu
    have hw : 0 < w := Nat.pos_of_mul_pos_left (positiveSquareContents_positive D _ hu)
    refine ⟨w, Finset.mem_filter.mpr ⟨?_, hu⟩, rfl⟩
    exact squareContents_of_dvd hD.ne hu hw (dvd_mul_left w v)
  · intro w hw
    rfl

theorem square_quotient_quotient (D : ℤ) (v w : ℕ) :
    D / (v : ℤ) ^ 2 / (w : ℤ) ^ 2 = D / ((v * w : ℕ) : ℤ) ^ 2 := by
  rw [Int.ediv_ediv_of_nonneg (sq_nonneg _)]
  congr 1
  push_cast
  ring

theorem divisors_filter_dvd (Q u : ℕ) (hQ : 0 < Q) :
    Q.divisors.filter (fun v => v ∣ u) = (Nat.gcd Q u).divisors := by
  ext v
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · intro h
    exact ⟨⟨h.1.1, h.2⟩, Nat.ne_of_gt (Nat.gcd_pos_of_pos_left u hQ)⟩
  · intro h
    exact ⟨⟨h.1.1, Nat.ne_of_gt hQ⟩, h.1.2⟩

/-- The finite substitution preceding (9), at every positive level. -/
theorem classCoefficient_eq_primitive (Q : ℕ) (hQ : 0 < Q)
    (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (t m : ℤ) (hD : t ^ 2 - 4 * m < 0) :
    classCoefficient Q hQ H t m =
      ∑ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
        h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) * B Q hQ (Nat.gcd Q u) t m := by
  classical
  let D := t ^ 2 - 4 * m
  have hD' : D < 0 := hD
  have hinner (v : ℕ) (hvQ : v ∈ Q.divisors) :
      (if (v : ℤ) ^ 2 ∣ D then H (D / (v : ℤ) ^ 2) * C Q hQ v t m else 0) =
        ∑ u ∈ (positiveSquareContents D).filter (fun u => v ∣ u),
          h₀ (D / (u : ℤ) ^ 2) * C Q hQ v t m := by
    have hv := Nat.pos_of_mem_divisors hvQ
    by_cases hdiv : (v : ℤ) ^ 2 ∣ D
    · rw [if_pos hdiv, hclasses _ (negative_discriminant_quotient D hD' v hv hdiv),
        Finset.sum_mul, squareContents_quotient D hD' v hv hdiv]
      simp_rw [square_quotient_quotient]
      exact sum_multiply_squareContents D hD' v hv
        (fun u => h₀ (D / (u : ℤ) ^ 2) * C Q hQ v t m)
    · rw [if_neg hdiv]
      symm
      apply Finset.sum_eq_zero
      intro u hu
      obtain ⟨hu, hvu⟩ := Finset.mem_filter.mp hu
      exact False.elim (hdiv ((mem_positiveSquareContents D hD'.ne v).mp
        (squareContents_of_dvd hD'.ne hu hv hvu)).2)
  unfold classCoefficient
  change (∑ v ∈ Q.divisors,
      if (v : ℤ) ^ 2 ∣ D then H (D / (v : ℤ) ^ 2) * C Q hQ v t m else 0) = _
  rw [Finset.sum_congr rfl hinner]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.sum_filter, divisors_filter_dvd Q u hQ, ← Finset.mul_sum,
    sum_C_eq_B Q hQ (Nat.gcd Q u) (Nat.gcd_pos_of_pos_left u hQ) t m]

noncomputable def primitiveCoefficient (Q : ℕ) (hQ : 0 < Q)
    (h₀ : ℤ → ℝ) (t m : ℤ) : ℝ :=
  ∑ u ∈ positiveSquareContents (t ^ 2 - 4 * m),
    h₀ ((t ^ 2 - 4 * m) / (u : ℤ) ^ 2) * B Q hQ (Nat.gcd Q u) t m

theorem Xi_eq_primitive (h : ℕ) (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (t m : ℤ) (hD : t ^ 2 - 4 * m < 0) :
    Xi h H t m = primitiveCoefficient (2 ^ h) (by positivity) h₀ t m :=
  classCoefficient_eq_primitive (2 ^ h) (by positivity) H h₀ hclasses t m hD

theorem K_eq_primitive_second_difference (n : ℕ) (H h₀ : ℤ → ℝ)
    (hclasses : ∀ D : ℤ, D < 0 →
      H D = ∑ u ∈ positiveSquareContents D, h₀ (D / (u : ℤ) ^ 2))
    (t m : ℤ) (hD : t ^ 2 - 4 * m < 0) :
    K n H t m =
      primitiveCoefficient (2 ^ n) (by positivity) h₀ t m -
        2 * primitiveCoefficient (2 ^ (n - 1)) (by positivity) h₀ t m +
        primitiveCoefficient (2 ^ (n - 2)) (by positivity) h₀ t m := by
  simp only [K, Xi_eq_primitive _ H h₀ hclasses t m hD]

end DepthAspect.PopaLiteralFunctions
