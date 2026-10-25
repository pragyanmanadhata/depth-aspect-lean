import DepthAspect.ArithmeticDyadicMass
import DepthAspect.DyadicMassBounds

/-! The four actual weighted estimates in (125), with explicit ℓ-dependent constants. -/
namespace DepthAspect.ArithmeticWeights

open scoped BigOperators

/-- The real cast of a nonnegative integer agrees with its natural index. -/
theorem toNat_real {n : ℤ} (hn : 0 ≤ n) : (n.toNat : ℝ) = (n : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg hn

/-- The actual finite interval mass estimate also applies to integer sets;
all indices in the positive interval are converted injectively. -/
theorem integer_interval_mass (ℓ : ℕ) (S : Finset ℤ) {X : ℝ} (hX : 0 < X) :
    (∑ n ∈ S.filter (fun n : ℤ => X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X), c ℓ n.toNat) ≤
      dyadicMassConstant ℓ := by
  let T := S.filter (fun n : ℤ => X < (n : ℝ) ∧ (n : ℝ) ≤ 2 * X)
  have hpos (n : ℤ) (hn : n ∈ T) : 0 ≤ n := by
    have ht : (0 : ℝ) < n := hX.trans (Finset.mem_filter.mp hn).2.1
    exact_mod_cast ht.le
  have hinj : Set.InjOn Int.toNat (↑T : Set ℤ) := by
    intro m hm n hn he
    have hi := congrArg (fun k : ℕ => (k : ℤ)) he
    simpa only [Int.toNat_of_nonneg (hpos m hm), Int.toNat_of_nonneg (hpos n hn)] using hi
  have hsub : T.image Int.toNat ⊆ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    have hbounds := (Finset.mem_filter.mp hm).2
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hX.le).mpr
      (by simpa only [toNat_real (hpos m hm)] using hbounds.1),
      Nat.le_floor (by simpa only [toNat_real (hpos m hm)] using hbounds.2)⟩
  calc
    _ = ∑ n ∈ T.image Int.toNat, c ℓ n := (Finset.sum_image hinj).symm
    _ ≤ dyadicMass ℓ X := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => c_nonneg ℓ n)
    _ ≤ _ := dyadicMass_bound ℓ hX

/-- The finite positive-moment version of (125), for any actual subset. -/
theorem finite_prefix_moment (ℓ : ℕ) {X a : ℝ} (hX : 0 < X) (ha : 0 < a)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) :
    (∑ n ∈ S, c ℓ n * (n : ℝ) ^ a) ≤
      dyadicMassConstant ℓ * X ^ a / (1 - (2 : ℝ) ^ (-a)) := by
  have hb := DyadicMassBounds.prefix_bound hX ha
    (zero_le_one.trans (dyadicMassConstant_ge_one ℓ))
    (S.image (fun n : ℕ => (n : ℤ))) (fun n => c ℓ n.toNat)
    (by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      simpa only [Int.cast_natCast] using hS n hn)
    (fun n _ => c_nonneg ℓ n.toNat)
    (fun x hx => integer_interval_mass ℓ _ hx)
  rw [Finset.sum_image (by
    intro m _ n _ hmn
    change (m : ℤ) = (n : ℤ) at hmn
    exact_mod_cast hmn)] at hb
  simpa only [Int.toNat_natCast, Int.cast_natCast] using hb

/-- The finite negative-moment version, uniform over arbitrary finite tails. -/
theorem finite_tail_moment (ℓ : ℕ) {X a : ℝ} (hX : 0 < X) (ha : 0 < a)
    (S : Finset ℕ) (hS : ∀ n ∈ S, X < (n : ℝ)) :
    (∑ n ∈ S, c ℓ n * (n : ℝ) ^ (-a)) ≤
      dyadicMassConstant ℓ * X ^ (-a) / (1 - (2 : ℝ) ^ (-a)) := by
  have hb := DyadicMassBounds.tail_bound hX ha
    (zero_le_one.trans (dyadicMassConstant_ge_one ℓ))
    (S.image (fun n : ℕ => (n : ℤ))) (fun n => c ℓ n.toNat)
    (by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
      simpa only [Int.cast_natCast] using hS n hn)
    (fun n _ => c_nonneg ℓ n.toNat)
    (fun x hx => integer_interval_mass ℓ _ (hX.trans_le hx))
  rw [Finset.sum_image (by
    intro m _ n _ hmn
    change (m : ℤ) = (n : ℤ) at hmn
    exact_mod_cast hmn)] at hb
  simpa only [Int.toNat_natCast, Int.cast_natCast] using hb

noncomputable def tailWeight (ℓ : ℕ) (a X : ℝ) (n : ℕ) : ℝ :=
  if X < (n : ℝ) then c ℓ n * (n : ℝ) ^ (-a) else 0

theorem tailWeight_nonneg (ℓ : ℕ) (a X : ℝ) (n : ℕ) : 0 ≤ tailWeight ℓ a X n := by
  unfold tailWeight
  split_ifs
  · exact mul_nonneg (c_nonneg ℓ n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_rfl

/-- The actual infinite weighted tail is summable and has the claimed power
bound. Neither its summability nor its dyadic interval masses are assumed. -/
theorem tail_moment (ℓ : ℕ) {X a : ℝ} (hX : 0 < X) (ha : 0 < a) :
    Summable (tailWeight ℓ a X) ∧
      (∑' n : ℕ, tailWeight ℓ a X n) ≤
        dyadicMassConstant ℓ * X ^ (-a) / (1 - (2 : ℝ) ^ (-a)) := by
  have hb (S : Finset ℕ) : (∑ n ∈ S, tailWeight ℓ a X n) ≤
      dyadicMassConstant ℓ * X ^ (-a) / (1 - (2 : ℝ) ^ (-a)) := by
    unfold tailWeight
    rw [← Finset.sum_filter]
    exact finite_tail_moment ℓ hX ha _ (fun n hn => (Finset.mem_filter.mp hn).2)
  exact ⟨summable_of_sum_le (tailWeight_nonneg ℓ a X) hb,
    Real.tsum_le_of_sum_le (tailWeight_nonneg ℓ a X) hb⟩

/-- The first bound in (125), with its literal real cutoff. -/
theorem prefix_half_moment (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, c ℓ n * Real.sqrt n) ≤
      dyadicMassConstant ℓ * Real.sqrt X / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  simpa only [Real.sqrt_eq_rpow] using finite_prefix_moment ℓ hX0
    (by norm_num : (0 : ℝ) < 1 / 2) (Finset.Ioc 0 ⌊X⌋₊) (by
      intro n hn
      obtain ⟨hn0, hnX⟩ := Finset.mem_Ioc.mp hn
      constructor
      · exact_mod_cast (show 1 ≤ n by omega)
      · exact (by exact_mod_cast hnX : (n : ℝ) ≤ ⌊X⌋₊).trans (Nat.floor_le hX0.le))

/-- The second bound in (125). -/
theorem tail_half_moment (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    (∑' n : ℕ, tailWeight ℓ (1 / 2) X n) ≤
      dyadicMassConstant ℓ * X ^ (-(1 / 2 : ℝ)) / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) :=
  (tail_moment ℓ (lt_of_lt_of_le zero_lt_one hX) (by norm_num)).2

/-- The third bound in (125). -/
theorem tail_inverse_moment (ℓ : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    (∑' n : ℕ, tailWeight ℓ 1 X n) ≤ 2 * dyadicMassConstant ℓ / X := by
  have ht := (tail_moment ℓ (lt_of_lt_of_le zero_lt_one hX) (by norm_num : (0 : ℝ) < 1)).2
  norm_num only [Real.rpow_neg_one] at ht
  convert ht using 1 <;> ring

/-- The square-root b-weight is exactly the half inverse c-weight. -/
theorem b_sqrt_eq (ℓ n : ℕ) : b ℓ n * Real.sqrt n = c ℓ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have he : (n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      nth_rw 1 [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hn0]
      norm_num
    rw [c_apply, Real.sqrt_eq_rpow]
    calc
      _ = b ℓ n * ((n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by rw [he]
      _ = _ := by ring

/-- The final global convergent series in (125), with a displayed bound. -/
theorem b_sqrt_summable_and_bound (ℓ : ℕ) :
    Summable (fun n : ℕ => b ℓ n * Real.sqrt n) ∧
      (∑' n : ℕ, b ℓ n * Real.sqrt n) ≤
        1 + dyadicMassConstant ℓ / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have ht := tail_moment ℓ (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he (n : ℕ) : b ℓ n * Real.sqrt n =
      (if n = 1 then 1 else 0) + tailWeight ℓ (1 / 2) 1 n := by
    rw [b_sqrt_eq]
    by_cases hn0 : n = 0
    · subst n
      simp [tailWeight]
    · by_cases hn1 : n = 1
      · subst n
        simp [tailWeight, c_one]
      · have hn : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
        simp [tailWeight, hn1, hn]
  have hi : Summable (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq 1 (1 : ℝ)).summable
  constructor
  · exact (hi.add ht.1).congr (fun n => (he n).symm)
  · simp_rw [he]
    rw [hi.tsum_add ht.1, tsum_ite_eq]
    simpa only [Real.one_rpow, mul_one] using add_le_add le_rfl ht.2

end DepthAspect.ArithmeticWeights
