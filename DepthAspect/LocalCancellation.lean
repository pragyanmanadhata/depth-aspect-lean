import DepthAspect.GeneralRoots
import DepthAspect.ContentReduction
import DepthAspect.OddMiddleRoots
import DepthAspect.ResidueBridge
import DepthAspect.QuadraticForms

/-!
# Stabilization of primitive projective roots and local cancellation

All root counts in this file are the actual two-chart counts `rho`.
-/
namespace DepthAspect.LocalCancellation
open ContentReduction SquareDivisibility GeneralRoots

/-- With odd leading coefficient and even middle coefficient, the second
projective chart has no roots. -/
theorem secondChart_empty_of_odd_leading {A : ℤ} (hA : Odd A) (b C : ℤ)
    (j : ℕ) (hj : 1 ≤ j) : secondChart j A (2 * b) C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨_, hyeven, hydiv⟩ := Finset.mem_filter.mp hy
  have h := QuadraticForms.no_even_chart_root hA hyeven b C (j - 1)
  have hj' : j - 1 + 1 = j := by omega
  rw [hj'] at h
  exact h hydiv

/-- The even-leading/odd-constant affine chart has no roots modulo an even modulus. -/
theorem firstChart_empty_of_even_leading {A C : ℤ} (hA : Even A) (hC : Odd C)
    (b : ℤ) (j : ℕ) (hj : 1 ≤ j) : firstChart j A (2 * b) C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have ht : (2 : ℤ) ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  have he : Even (A * x ^ 2 + 2 * b * x) := by
    obtain ⟨a, ha⟩ := hA
    refine ⟨a * x ^ 2 + b * x, ?_⟩
    rw [ha]
    ring
  have ho : Odd (A * x ^ 2 + 2 * b * x + C) := by
    simpa [add_comm] using hC.add_even he
  exact (Int.not_even_iff_odd.mpr ho)
    (even_iff_two_dvd.mpr (ht.trans (Finset.mem_filter.mp hx).2))

/-- In the remaining even-middle case, every reverse affine root is even. -/
theorem reverse_root_even {A C y : ℤ} (hA : Even A) (hC : Odd C) (b : ℤ)
    (j : ℕ) (hj : 1 ≤ j) (hy : (2 : ℤ) ^ j ∣ A + 2 * b * y + C * y ^ 2) : Even y := by
  rcases Int.even_or_odd y with he | ho
  · exact he
  · have hlow : Even (A + 2 * b * y + C * y ^ 2) :=
      even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega : j ≠ 0)).trans hy)
    have he : Even (A + 2 * b * y) := by
      obtain ⟨a, ha⟩ := hA
      refine ⟨a + b * y, ?_⟩
      rw [ha]
      ring
    have hodd : Odd (A + 2 * b * y + C * y ^ 2) := by
      simpa [add_comm] using (hC.mul (ho.pow (n := 2))).add_even he
    exact False.elim ((Int.not_even_iff_odd.mpr hodd) hlow)

/-- The reversed chart's even restriction is automatic in the
remaining even-middle case. -/
theorem secondChart_eq_reverse_first {A C : ℤ} (hA : Even A) (hC : Odd C)
    (b : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    secondChart j A (2 * b) C = firstChart j C (2 * b) A := by
  ext y
  have heq : A + 2 * b * y + C * y ^ 2 = C * y ^ 2 + 2 * b * y + A := by ring
  simp only [secondChart, firstChart, Finset.mem_filter]
  constructor
  · rintro ⟨hI, _, hdiv⟩
    exact ⟨hI, by rwa [← heq]⟩
  · rintro ⟨hI, hdiv⟩
    have hdiv' : (2 : ℤ) ^ j ∣ A + 2 * b * y + C * y ^ 2 := by rwa [heq]
    exact ⟨hI, reverse_root_even hA hC b j hj hdiv', hdiv'⟩

/-- Completion of the square expressed directly in the canonical integer chart. -/
theorem firstChart_square_card {A : ℤ} (hA : Odd A) (b C : ℤ) (j : ℕ) :
    (firstChart j A (2 * b) C).card = (squareRoots j (b ^ 2 - A * C)).card := by
  have hbridge := ResidueBridge.integer_quadratic_card j A (2 * b) C
  change (firstChart j A (2 * b) C).card = _ at hbridge
  rw [hbridge]
  have hquad := QuadraticForms.dyadic_quadratic_root_card hA b C j
  simp only [Int.cast_mul, Int.cast_ofNat] at *
  rw [hquad]
  have hcard := ResidueBridge.zmod_square_card j (b ^ 2 - A * C)
  push_cast at hcard
  exact hcard

/-- The actual primitive projective count in the even-middle case is exactly
the square-root count of the quarter-discriminant. -/
theorem rho_even_middle_eq_squareRoots (A b C : ℤ) (hprim : Odd A ∨ Odd C)
    (j : ℕ) (hj : 1 ≤ j) :
    rho j A (2 * b) C = (squareRoots j (b ^ 2 - A * C)).card := by
  by_cases hA : Odd A
  · unfold rho
    rw [secondChart_empty_of_odd_leading hA b C j hj, Finset.card_empty, Nat.add_zero,
      firstChart_square_card hA b C j]
  · have heA : Even A := Int.not_odd_iff_even.mp hA
    have hC : Odd C := hprim.resolve_left hA
    unfold rho
    rw [firstChart_empty_of_even_leading heA hC b j hj, Finset.card_empty, Nat.zero_add,
      secondChart_eq_reverse_first heA hC b j hj, firstChart_square_card hC b A j]
    rw [mul_comm C A]

/-- Actual projective stabilization in the odd-middle case. -/
theorem rho_odd_middle_stable (A B C : ℤ) (hB : Odd B) (j l : ℕ)
    (hj : 1 ≤ j) (hl : 1 ≤ l) : rho j A B C = rho l A B C := by
  have hfirst (r : ℕ) : firstChart r A B C = OddMiddleRoots.roots r A B C := rfl
  have hsecond (r : ℕ) : secondChart r A B C = OddMiddleRoots.evenRoots r C B A := by
    ext x
    simp only [secondChart, OddMiddleRoots.evenRoots, OddMiddleRoots.evenRootsMod, OddMiddleRoots.rootsMod,
      OddMiddleRoots.quadratic, Finset.mem_filter]
    have heq : A + B * x + C * x ^ 2 = C * x ^ 2 + B * x + A := by ring
    rw [heq]
    tauto
  unfold rho
  rw [hfirst j, hfirst l, hsecond j, hsecond l,
    OddMiddleRoots.roots_stable j l A B C hj hl hB,
    OddMiddleRoots.evenRoots_stable j l C B A hj hl hB]

/-- Actual projective stabilization in the even-middle case. -/
theorem rho_even_middle_stable (A b C : ℤ) (hprim : Odd A ∨ Odd C)
    (v j l : ℕ) {u : ℤ} (hu : Odd u) (hD : b ^ 2 - A * C = (2 : ℤ) ^ v * u)
    (hj : v + 3 ≤ j) (hl : v + 3 ≤ l) : rho j A (2 * b) C = rho l A (2 * b) C := by
  rw [rho_even_middle_eq_squareRoots A b C hprim j (by omega),
    rho_even_middle_eq_squareRoots A b C hprim l (by omega), hD]
  exact squareRoots_stable_of_odd_part v j l hu hj hl

/-- The stable primitive count gives a zero second difference after content
scaling; every count here is the concrete projective `rho`. -/
theorem scaled_rho_second_difference (e j : ℕ) (A B C : ℤ) (hj : 1 ≤ j)
    (h1 : rho (j + 1) A B C = rho j A B C)
    (h2 : rho (j + 2) A B C = rho j A B C) :
    (rho (e + j + 2) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) -
      2 * (rho (e + j + 1) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) +
      (rho (e + j) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) = 0 := by
  rw [show e + j + 2 = e + (j + 2) by omega,
    show e + j + 1 = e + (j + 1) by omega,
    rho_content_reduction e (j + 2) A B C (by omega),
    rho_content_reduction e (j + 1) A B C (by omega),
    rho_content_reduction e j A B C hj, h1, h2]
  ring

/-- The discriminant scales by the square of the content. -/
theorem scaled_discriminant (e : ℕ) (A B C : ℤ) :
    (2 ^ e * B) ^ 2 - 4 * (2 ^ e * A) * (2 ^ e * C) =
      (2 : ℤ) ^ (2 * e) * (B ^ 2 - 4 * A * C) := by
  rw [Nat.mul_comm 2 e, pow_mul]
  ring

/-- Lemma 3.1 for actual projective root counts: the second difference vanishes
unless the discriminant has the stated extra power-of-two divisibility.
Primitivity at two is exactly the hypothesis that at least one coefficient is odd.
No root-count stabilization is assumed. -/
theorem local_cancellation (n e : ℕ) (hn : 2 ≤ n) (A B C : ℤ)
    (hprim : Odd A ∨ Odd B ∨ Odd C)
    (hbad : ¬ (2 : ℤ) ^ (n + e - 2) ∣
      (2 ^ e * B) ^ 2 - 4 * (2 ^ e * A) * (2 ^ e * C)) :
    (rho n (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) -
      2 * (rho (n - 1) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) +
      (rho (n - 2) (2 ^ e * A) (2 ^ e * B) (2 ^ e * C) : ℤ) = 0 := by
  have he : e < n - 2 := by
    by_contra h
    apply hbad
    rw [scaled_discriminant]
    exact dvd_mul_of_dvd_left (pow_dvd_pow (2 : ℤ) (by omega)) _
  let j := n - 2 - e
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hn0 : n = e + j + 2 := by dsimp [j]; omega
  have hn1 : n - 1 = e + j + 1 := by omega
  have hn2 : n - 2 = e + j := by omega
  have hstable : ∀ l : ℕ, j ≤ l → rho l A B C = rho j A B C := by
    rcases Int.even_or_odd B with hBe | hBo
    · obtain ⟨b, hb⟩ := hBe
      have hB : B = 2 * b := by omega
      have hnBo : ¬ Odd B := by
        rw [hB, Int.odd_iff]
        omega
      have hAC : Odd A ∨ Odd C := by tauto
      have hdisc :
          (2 ^ e * B) ^ 2 - 4 * (2 ^ e * A) * (2 ^ e * C) =
            (2 : ℤ) ^ (2 * e + 2) * (b ^ 2 - A * C) := by
        rw [scaled_discriminant, hB, pow_add]
        ring
      have hDne : b ^ 2 - A * C ≠ 0 := by
        intro hzero
        apply hbad
        rw [hdisc, hzero, mul_zero]
        exact dvd_zero _
      obtain ⟨v, u, hu, hD⟩ := exists_odd_part hDne
      have hfactor :
          (2 ^ e * B) ^ 2 - 4 * (2 ^ e * A) * (2 ^ e * C) =
            (2 : ℤ) ^ (2 * e + v + 2) * u := by
        rw [hdisc, hD, ← mul_assoc, ← pow_add]
        congr 2
        omega
      have hvj : v + 3 ≤ j := by
        by_contra h
        apply hbad
        rw [hfactor]
        exact dvd_mul_of_dvd_left (pow_dvd_pow (2 : ℤ) (by omega)) _
      intro l hl
      rw [hB]
      exact rho_even_middle_stable A b C hAC v l j hu hD (by omega) hvj
    · intro l hl
      exact rho_odd_middle_stable A B C hBo l j (by omega) hj
  rw [hn1, hn2, hn0]
  exact scaled_rho_second_difference e j A B C hj
    (hstable (j + 1) (by omega)) (hstable (j + 2) (by omega))

/-- The common-discriminant weighted form of Corollary 3.2. Arbitrary weights
are allowed, so the result applies in particular to the finite class-number sum.
The vanishing of each root-count second difference is proved above. -/
theorem weighted_local_cancellation {ι R : Type*} [CommRing R]
    (s : Finset ι) (w : ι → R) (e : ι → ℕ) (A B C : ι → ℤ)
    (n : ℕ) (hn : 2 ≤ n) (D : ℤ)
    (hprim : ∀ i ∈ s, Odd (A i) ∨ Odd (B i) ∨ Odd (C i))
    (hdisc : ∀ i ∈ s,
      (2 ^ e i * B i) ^ 2 - 4 * (2 ^ e i * A i) * (2 ^ e i * C i) = D)
    (hbad : ¬ (2 : ℤ) ^ (n - 2) ∣ D) :
    (∑ i ∈ s, w i * (((rho n (2 ^ e i * A i) (2 ^ e i * B i) (2 ^ e i * C i) : ℤ) -
      2 * (rho (n - 1) (2 ^ e i * A i) (2 ^ e i * B i) (2 ^ e i * C i) : ℤ) +
      (rho (n - 2) (2 ^ e i * A i) (2 ^ e i * B i) (2 ^ e i * C i) : ℤ) : ℤ) : R)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hbad' : ¬ (2 : ℤ) ^ (n + e i - 2) ∣
      (2 ^ e i * B i) ^ 2 - 4 * (2 ^ e i * A i) * (2 ^ e i * C i) := by
    intro h
    apply hbad
    rw [← hdisc i hi]
    exact (pow_dvd_pow (2 : ℤ) (by omega)).trans h
  rw [local_cancellation n (e i) hn (A i) (B i) (C i) (hprim i hi) hbad',
    Int.cast_zero, mul_zero]

end DepthAspect.LocalCancellation
